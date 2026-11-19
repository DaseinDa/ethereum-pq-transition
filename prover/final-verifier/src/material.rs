//! F's verifier-key material (pq-final-verifier, 2026-11-01): the data that fixes F's verifier besides the code, read
//! from `key/f-key-material.json` and `key/f-periodic.rle`, and the recomputation of the three identity digests that
//! chain F to B and B to L0' v2.
//!
//! The same file is compiled into two programs, byte for byte:
//! - the export process (code/pq-proof-pipeline-20261101, mode `f-export-key` of the recorded F2 binary), which writes
//!   the material from F's recorded schedule and checks, in that process, that this module rebuilds F's AIR equal to
//!   the schedule's and recomputes F's, B's and L0' v2's digests equal to the recorded functions' values
//!   (`fmodes::f_vk_digest`, `b2_vk_digest`, `l0p2::vk_digest`);
//! - the standalone verifier (`src/key.rs`), which loads the material, rebuilds F's AIR and recomputes the digests at
//!   start-up and compares them with its pinned `TrustedParams`.
//!
//! Each digest function follows its recorded original word for word (the original's file and function are named on
//! each). The periodic columns are stored run-length encoded (`encode_periodic`), and their SHA-256 (u32
//! little-endian, column-major, as `fmodes::periodic_sha256` computes it) is checked after decoding.
//! research packaging; loop-internal self-review; not independently reviewed.
use p3_air::BaseAir;
use p3_batch_stark_c3np::NextRowColumns;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};
use tiny_keccak::{Hasher, Keccak};

use crate::fkernel::{self, KernelAir, P2Air, PIdx};

/// The schema of `f-key-material.json`.
pub const SCHEMA: &str = "pq-final-verifier/key-material/v1";
/// The first bytes of `f-periodic.rle`.
pub const PERIODIC_MAGIC: &[u8; 8] = b"PQFPRLE1";

/// The bytes of the source files that the digests cover (each recorded original hashes its own sources with
/// `include_bytes!`): F's kernel, schedule compiler, constraint compiler, child module and modes; B's kernel, schedule
/// compiler and constraint compiler (the same `compiler.rs`).
pub struct DigestSources<'a> {
    pub fkernel: &'a [u8],
    pub fschedule: &'a [u8],
    pub compiler: &'a [u8],
    pub fchild: &'a [u8],
    pub fmodes: &'a [u8],
    pub kernel: &'a [u8],
    pub schedule: &'a [u8],
}

/// A material file that is malformed or does not fit the code that reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterialError(pub String);

impl core::fmt::Display for MaterialError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.0)
    }
}

fn err<T>(msg: impl Into<String>) -> Result<T, MaterialError> {
    Err(MaterialError(msg.into()))
}

// ---------- JSON accessors (no derive: every field read by name, unknown fields ignored) ----------

pub fn get<'a>(v: &'a Value, key: &str) -> Result<&'a Value, MaterialError> {
    v.get(key).ok_or_else(|| MaterialError(format!("missing field {key}")))
}
pub fn num(v: &Value, key: &str) -> Result<usize, MaterialError> {
    get(v, key)?.as_u64().map(|x| x as usize).ok_or_else(|| MaterialError(format!("field {key} is not an unsigned integer")))
}
pub fn text<'a>(v: &'a Value, key: &str) -> Result<&'a str, MaterialError> {
    get(v, key)?.as_str().ok_or_else(|| MaterialError(format!("field {key} is not a string")))
}
fn usizes(v: &Value) -> Result<Vec<usize>, MaterialError> {
    v.as_array()
        .ok_or_else(|| MaterialError("expected an array".into()))?
        .iter()
        .map(|x| x.as_u64().map(|y| y as usize).ok_or_else(|| MaterialError("expected an unsigned integer".into())))
        .collect()
}
pub fn list(v: &Value, key: &str) -> Result<Vec<usize>, MaterialError> {
    usizes(get(v, key)?).map_err(|e| MaterialError(format!("{key}: {e}")))
}
fn fixed<const N: usize>(v: &Value, key: &str) -> Result<[usize; N], MaterialError> {
    list(v, key)?.try_into().map_err(|_| MaterialError(format!("field {key} must have {N} entries")))
}
pub fn unhex(s: &str) -> Result<Vec<u8>, MaterialError> {
    if s.len() % 2 != 0 || !s.bytes().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()) {
        return err("hex must be lower-case and of even length");
    }
    Ok((0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect())
}
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn digest32(v: &Value, key: &str) -> Result<[u8; 32], MaterialError> {
    unhex(text(v, key)?)?.try_into().map_err(|_| MaterialError(format!("field {key} must hold 32 bytes")))
}
/// A Merkle cap: a list of digests of 8 canonical KoalaBear elements.
fn cap(v: &Value, key: &str) -> Result<Vec<[u32; 8]>, MaterialError> {
    get(v, key)?
        .as_array()
        .ok_or_else(|| MaterialError(format!("{key} is not an array")))?
        .iter()
        .map(|d| {
            let w = usizes(d)?;
            let w: [usize; 8] = w.try_into().map_err(|_| MaterialError(format!("{key}: a digest has 8 elements")))?;
            if w.iter().any(|&x| x >= F::ORDER_U32 as usize) {
                return err(format!("{key}: an element is not canonical"));
            }
            Ok(w.map(|x| x as u32))
        })
        .collect()
}

// ---------- the periodic columns ----------

fn put_varint(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push((x as u8 & 0x7f) | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

/// A canonical LEB128 varint of at most 10 bytes (an overlong encoding is rejected).
fn take_varint(bytes: &[u8], pos: &mut usize) -> Result<u64, MaterialError> {
    let mut x: u64 = 0;
    for i in 0..10 {
        let b = *bytes.get(*pos).ok_or_else(|| MaterialError("periodic data truncated".into()))?;
        *pos += 1;
        if i == 9 && b > 1 {
            return err("periodic data: varint overflows u64");
        }
        x |= u64::from(b & 0x7f) << (7 * i);
        if b & 0x80 == 0 {
            if i > 0 && b == 0 {
                return err("periodic data: overlong varint");
            }
            return Ok(x);
        }
    }
    err("periodic data: varint longer than 10 bytes")
}

/// `PERIODIC_MAGIC`, the column count and the row count, then per column its runs: the run count, then each run's
/// canonical value and length (LEB128 varints).
pub fn encode_periodic(cols: &[Vec<F>]) -> Vec<u8> {
    let mut out = PERIODIC_MAGIC.to_vec();
    put_varint(&mut out, cols.len() as u64);
    put_varint(&mut out, cols.first().map_or(0, Vec::len) as u64);
    for col in cols {
        let mut runs: Vec<(u32, u64)> = vec![];
        for v in col {
            let v = v.as_canonical_u32();
            match runs.last_mut() {
                Some((last, n)) if *last == v => *n += 1,
                _ => runs.push((v, 1)),
            }
        }
        put_varint(&mut out, runs.len() as u64);
        for (v, n) in runs {
            put_varint(&mut out, u64::from(v));
            put_varint(&mut out, n);
        }
    }
    out
}

/// The inverse of `encode_periodic`, strict: the magic, the expected shape, runs of length at least one that fill each
/// column exactly, canonical values, adjacent runs with different values, no trailing byte.
pub fn decode_periodic(bytes: &[u8], ncols: usize, nrows: usize) -> Result<Vec<Vec<F>>, MaterialError> {
    if bytes.len() < PERIODIC_MAGIC.len() || &bytes[..PERIODIC_MAGIC.len()] != PERIODIC_MAGIC {
        return err("periodic data: wrong magic");
    }
    let mut pos = PERIODIC_MAGIC.len();
    let (c, r) = (take_varint(bytes, &mut pos)?, take_varint(bytes, &mut pos)?);
    if c != ncols as u64 || r != nrows as u64 {
        return err(format!("periodic data: shape {c} x {r}, expected {ncols} x {nrows}"));
    }
    let mut cols = Vec::with_capacity(ncols);
    for k in 0..ncols {
        let runs = take_varint(bytes, &mut pos)?;
        let mut col: Vec<F> = Vec::with_capacity(nrows);
        let mut last: Option<u64> = None;
        for _ in 0..runs {
            let v = take_varint(bytes, &mut pos)?;
            let n = take_varint(bytes, &mut pos)?;
            if v >= u64::from(F::ORDER_U32) || n == 0 || last == Some(v) || col.len() as u64 + n > nrows as u64 {
                return err(format!("periodic data: column {k} has an invalid run"));
            }
            col.extend(std::iter::repeat_n(F::from_u32(v as u32), n as usize));
            last = Some(v);
        }
        if col.len() != nrows {
            return err(format!("periodic data: column {k} has {} rows", col.len()));
        }
        cols.push(col);
    }
    if pos != bytes.len() {
        return err("periodic data: trailing bytes");
    }
    Ok(cols)
}

/// SHA-256 of the periodic columns, u32 little-endian, column-major (`fmodes::periodic_sha256`).
pub fn periodic_sha256(cols: &[Vec<F>]) -> [u8; 32] {
    let mut h = Sha256::new();
    for col in cols {
        for v in col {
            h.update(v.as_canonical_u32().to_le_bytes());
        }
    }
    h.finalize().into()
}

// ---------- F's AIR ----------

pub fn pidx_to_json(p: &PIdx) -> Value {
    json!({"cf": p.cf, "cv": p.cv, "kc": p.kc, "tag": p.tag, "kr": p.kr, "ivf": p.ivf, "lnk": p.lnk, "cons": p.cons,
        "path_t": p.path_t, "start": p.start, "pend": p.pend, "pend_canon": p.pend_canon, "lsel": p.lsel, "xs": p.xs,
        "x0": p.x0, "xp": p.xp, "xc": p.xc, "vs": p.vs, "xce": p.xce, "vacc": p.vacc, "vsig": p.vsig, "op": p.op,
        "kappa": p.kappa, "kx": p.kx, "unp": p.unp, "ctrl": p.ctrl, "dv": p.dv, "dc": p.dc, "dl": p.dl, "dp": p.dp,
        "dw": p.dw, "cs": p.cs, "bind": p.bind, "inj": p.inj, "capr": p.capr, "capw": p.capw, "hiw": p.hiw})
}

pub fn pidx_from_json(v: &Value) -> Result<PIdx, MaterialError> {
    Ok(PIdx {
        cf: fixed(v, "cf")?,
        cv: fixed(v, "cv")?,
        kc: num(v, "kc")?,
        tag: num(v, "tag")?,
        kr: fixed(v, "kr")?,
        ivf: num(v, "ivf")?,
        lnk: num(v, "lnk")?,
        cons: num(v, "cons")?,
        path_t: num(v, "path_t")?,
        start: num(v, "start")?,
        pend: num(v, "pend")?,
        pend_canon: num(v, "pend_canon")?,
        lsel: fixed(v, "lsel")?,
        xs: num(v, "xs")?,
        x0: num(v, "x0")?,
        xp: num(v, "xp")?,
        xc: num(v, "xc")?,
        vs: num(v, "vs")?,
        xce: num(v, "xce")?,
        vacc: num(v, "vacc")?,
        vsig: num(v, "vsig")?,
        op: fixed(v, "op")?,
        kappa: num(v, "kappa")?,
        kx: num(v, "kx")?,
        unp: fixed(v, "unp")?,
        ctrl: fixed(v, "ctrl")?,
        dv: num(v, "dv")?,
        dc: num(v, "dc")?,
        dl: fixed(v, "dl")?,
        dp: num(v, "dp")?,
        dw: num(v, "dw")?,
        cs: fixed(v, "cs")?,
        bind: fixed(v, "bind")?,
        inj: num(v, "inj")?,
        capr: num(v, "capr")?,
        capw: num(v, "capw")?,
        hiw: num(v, "hiw")?,
    })
}

/// F's AIR from the material's `f.air` and the decoded periodic columns: `KernelAir` as `fschedule::Schedule::build`
/// constructs it (`P2Air::new(constants())`, the schedule's columns and names, the periodic-column indices, the
/// public-value binding map and the first transcript row's absorbed count).
pub fn air_from_material(f_air: &Value, periodic: Vec<Vec<F>>) -> Result<KernelAir, MaterialError> {
    let periodic_names: Vec<String> = get(f_air, "periodic_names")?
        .as_array()
        .ok_or_else(|| MaterialError("periodic_names is not an array".into()))?
        .iter()
        .map(|x| x.as_str().map(str::to_string).ok_or_else(|| MaterialError("a periodic name is not a string".into())))
        .collect::<Result<_, _>>()?;
    if periodic_names.len() != periodic.len() {
        return err("periodic names and columns differ in count");
    }
    let width = periodic.len();
    let pidx = pidx_from_json(get(f_air, "pidx")?)?;
    let pub_terms: Vec<Vec<(usize, usize)>> = get(f_air, "pub_terms")?
        .as_array()
        .ok_or_else(|| MaterialError("pub_terms is not an array".into()))?
        .iter()
        .map(|lane| {
            lane.as_array()
                .ok_or_else(|| MaterialError("a pub_terms lane is not an array".into()))?
                .iter()
                .map(|t| {
                    let p = usizes(t)?;
                    if p.len() != 2 || p[0] >= width {
                        return err("a pub_terms entry is not (periodic selector, public value)");
                    }
                    Ok((p[0], p[1]))
                })
                .collect()
        })
        .collect::<Result<_, _>>()?;
    let air = KernelAir {
        p2: P2Air::new(fkernel::constants()),
        log_n: num(f_air, "log_n")?,
        num_public: num(f_air, "num_public")?,
        periodic,
        periodic_names,
        pidx,
        pub_terms,
        k0: num(f_air, "k0")?,
    };
    if air.pub_terms.iter().flatten().any(|&(_, j)| j >= air.num_public) {
        return err("a pub_terms entry names a public value outside the statement");
    }
    Ok(air)
}

/// The material's `f.air` for an AIR (the periodic columns are written apart: shape, encoding and SHA-256 only).
pub fn air_to_json(air: &KernelAir) -> Value {
    json!({"log_n": air.log_n, "num_public": air.num_public, "k0": air.k0, "main_width": fkernel::WIDTH,
        "nctrl_main": fkernel::NCTRL_MAIN, "pidx": pidx_to_json(&air.pidx),
        "pub_terms": air.pub_terms.iter().map(|lane| lane.iter().map(|&(s, j)| json!([s, j])).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "periodic_names": air.periodic_names,
        "periodic": {"columns": air.periodic.len(), "rows": air.periodic.first().map_or(0, Vec::len), "file": "f-periodic.rle",
            "encoding": "PQFPRLE1: magic, then LEB128 varints: column count, row count, per column the run count and each run's canonical value and length",
            "sha256_u32le_column_major": hex(&periodic_sha256(&air.periodic))}})
}

// ---------- next-row sets ----------

pub fn next_rows_to_json(n: &NextRowColumns) -> Value {
    json!({"main_width": n.main_width, "main": n.main, "preprocessed_width": n.preprocessed_width, "preprocessed": n.preprocessed,
        "permutation_width": n.permutation_width, "permutation": n.permutation})
}
pub fn next_rows_from_json(v: &Value) -> Result<NextRowColumns, MaterialError> {
    let n = NextRowColumns {
        main_width: num(v, "main_width")?,
        main: list(v, "main")?,
        preprocessed_width: num(v, "preprocessed_width")?,
        preprocessed: list(v, "preprocessed")?,
        permutation_width: num(v, "permutation_width")?,
        permutation: list(v, "permutation")?,
    };
    if !n.is_well_formed() {
        return err("a next-row set is not strictly increasing inside its width");
    }
    Ok(n)
}

/// The length of a postcard varint (`fmodes::vlen`).
fn vlen(n: usize) -> i64 {
    let mut len = 1;
    let mut v = n >> 7;
    while v > 0 {
        len += 1;
        v >>= 7;
    }
    len
}

/// The byte change of splitting a hiding trace's next-row subset (`fmodes::split_delta_bytes`, F's parameters).
pub fn split_delta_bytes(width: usize, next: usize, queries: usize, random_codewords: usize, salt_elems: usize) -> i64 {
    assert!(0 < next && next < width, "only a proper, non-empty next-row subset can be split");
    let (q, cw, salt, efb, fb) = (queries as i64, random_codewords, salt_elems as i64, 32i64, 4i64);
    let ood = (vlen(next) + efb * next as i64) - (vlen(width) + efb * width as i64);
    let codewords = vlen(1) + vlen(cw) + efb * cw as i64;
    let rows = q * (vlen(next + cw) + vlen(width - next + cw) - vlen(width + cw) + fb * cw as i64);
    let salts = q * (vlen(salt_elems) + fb * salt);
    let framing = vlen(2) - vlen(1);
    ood + codewords + rows + salts + q * 2 * framing + framing
}

/// F's opened next-row sets from the derived ones by the break-even rule (`fmodes::f_next_rows`): a trace whose
/// derived set is a proper subset is split only where the split saves bytes; otherwise it is opened in full.
pub fn opened_from_derived(derived: &NextRowColumns, queries: usize, random_codewords: usize, salt_elems: usize) -> NextRowColumns {
    let mut opened = derived.clone();
    let main_delta = derived.main_split().is_split().then(|| split_delta_bytes(derived.main_width, derived.main.len(), queries, random_codewords, salt_elems));
    let pw = 8 * derived.permutation_width;
    let perm_delta = derived.permutation_split(8).is_split().then(|| split_delta_bytes(pw, 8 * derived.permutation.len(), queries, random_codewords, salt_elems));
    if main_delta.is_some_and(|d| d >= 0) {
        opened.main = (0..derived.main_width).collect();
    }
    if perm_delta.is_some_and(|d| d >= 0) {
        opened.permutation = (0..derived.permutation_width).collect();
    }
    opened
}

// ---------- the three identity digests ----------

/// One table of a child as the kernel's verifier-key digests list it (`TableSpec`'s fields, in the digests' order).
struct TableWords(Vec<u64>);

fn table_words(t: &Value) -> Result<TableWords, MaterialError> {
    let mut d: Vec<u64> = ["log_trace", "width", "pre_width", "perm_width", "chunks", "log_qd"]
        .iter()
        .map(|k| num(t, k).map(|x| x as u64))
        .collect::<Result<_, _>>()?;
    for key in ["public", "next_main", "next_pre", "next_perm", "lookup_bus"] {
        d.extend(list(t, key)?.into_iter().map(|x| x as u64));
    }
    Ok(TableWords(d))
}

/// A prefix item's field elements (`fschedule::prefix_elements` / `schedule::prefix_elements` with an all-zero
/// statement): bytes as their length then each byte, fields as they are, a statement part as its length then zeros.
pub fn prefix_elements(items: &Value) -> Result<Vec<F>, MaterialError> {
    let mut v = vec![];
    for item in items.as_array().ok_or_else(|| MaterialError("prefix is not an array".into()))? {
        match text(item, "kind")? {
            "bytes" => {
                let b = unhex(text(item, "hex")?)?;
                v.push(F::from_usize(b.len()));
                v.extend(b.iter().map(|&x| F::from_u8(x)));
            }
            "fields" => {
                for x in list(item, "values")? {
                    if x >= F::ORDER_U32 as usize {
                        return err("a prefix field is not canonical");
                    }
                    v.push(F::from_usize(x));
                }
            }
            "statement" => {
                let len = num(item, "len")?;
                v.push(F::from_usize(len));
                v.extend(std::iter::repeat_n(F::ZERO, len));
            }
            other => return err(format!("unknown prefix item kind {other}")),
        }
    }
    Ok(v)
}

fn update_words(h: &mut Keccak, words: &[u64]) {
    for v in words {
        h.update(&v.to_le_bytes());
    }
}

/// The child part of a kernel digest's word list: index bits, queries, final polynomial, blowup, the child's cap
/// height, the FRI arities and every table.
fn child_words(c: &Value) -> Result<Vec<u64>, MaterialError> {
    let mut d: Vec<u64> = ["index_bits", "num_queries", "log_final_poly_len", "log_blowup", "cap_height"]
        .iter()
        .map(|k| num(c, k).map(|x| x as u64))
        .collect::<Result<_, _>>()?;
    d.extend(list(c, "fri_log_arities")?.into_iter().map(|x| x as u64));
    for t in get(c, "tables")?.as_array().ok_or_else(|| MaterialError("tables is not an array".into()))? {
        d.extend(table_words(t)?.0);
    }
    Ok(d)
}

/// L0' v2's identity digest as B pins it (code/l5-layer-f2-20261031/f2/l0p2.rs `vk_digest`): label, domain, AIR digest
/// and program digest each with its length, the descriptor and the degree bits, every preprocessed cap entry, and the
/// four tables' next-row sets.
pub fn l0p2_vk_digest(l: &Value) -> Result<[u8; 32], MaterialError> {
    let mut h = Keccak::v256();
    h.update(text(l, "vk_label")?.as_bytes());
    let domain = text(l, "domain")?.as_bytes().to_vec();
    for part in [domain, digest32(l, "air_digest")?.to_vec(), digest32(l, "program_digest")?.to_vec()] {
        h.update(&(part.len() as u64).to_le_bytes());
        h.update(&part);
    }
    let words: Vec<u64> = list(l, "descriptor")?.into_iter().chain(list(l, "degree_bits")?).map(|x| x as u64).collect();
    update_words(&mut h, &words);
    for d in cap(l, "preprocessed_cap")? {
        for v in d {
            h.update(&v.to_le_bytes());
        }
    }
    for n in get(l, "next_rows")?.as_array().ok_or_else(|| MaterialError("next_rows is not an array".into()))? {
        for key in ["main", "preprocessed", "permutation"] {
            let set = list(n, key)?;
            h.update(&(set.len() as u64).to_le_bytes());
            for c in set {
                h.update(&(c as u64).to_le_bytes());
            }
        }
    }
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    Ok(out)
}

/// L0' v2's transcript prefix as B's schedule absorbs it (F2's l0p2.rs `prefix`): the domain, the AIR digest, the
/// descriptor (its length, then its entries) and the program digest.
pub fn l0p2_prefix_json(l: &Value) -> Result<Value, MaterialError> {
    let d = list(l, "descriptor")?;
    let mut fields = vec![d.len()];
    fields.extend(d);
    Ok(json!([
        {"kind": "bytes", "name": "domain_separator", "hex": hex(text(l, "domain")?.as_bytes())},
        {"kind": "bytes", "name": "air_digest", "hex": text(l, "air_digest")?},
        {"kind": "fields", "name": "descriptor", "values": fields},
        {"kind": "bytes", "name": "program_digest", "hex": text(l, "program_digest")?},
    ]))
}

/// B's verifier-key digest (code/l5-layer-f2-20261031/f2/main.rs `b2_vk_digest`), with the child's identity digest
/// and prefix taken from the L0' v2 section.
pub fn b_vk_digest(b: &Value, l0p2: &Value, l0p2_vk: &[u8; 32], src: &DigestSources<'_>) -> Result<[u8; 32], MaterialError> {
    let mut h = Keccak::v256();
    h.update(text(b, "vk_label")?.as_bytes());
    let s = get(b, "schedule")?;
    let p = get(b, "params")?;
    let c = get(b, "child")?;
    let mut d: Vec<u64> = vec![
        num(s, "n")? as u64,
        num(s, "main_width")? as u64,
        num(s, "pre_width")? as u64,
        0,
        num(s, "q")? as u64,
        num(s, "num_public")? as u64,
        num(s, "t_rows")? as u64,
        num(s, "block_rows")? as u64,
        num(s, "program_len")? as u64,
    ];
    for k in ["log_blowup", "log_final_poly_len", "max_log_arity", "num_queries", "random_codewords", "salt_elems", "digest_elems", "cap_height"] {
        d.push(num(p, k)? as u64);
    }
    d.extend(child_words(c)?);
    update_words(&mut h, &d);
    h.update(&digest32(b, "air_digest")?);
    h.update(&digest32(b, "program_digest")?);
    h.update(&digest32(b, "salt_seed")?);
    for root in cap(b, "preprocessed_cap")? {
        for v in root {
            h.update(&v.to_le_bytes());
        }
    }
    h.update(text(b, "bus")?.as_bytes());
    h.update(l0p2_vk);
    for v in prefix_elements(&l0p2_prefix_json(l0p2)?)? {
        h.update(&v.as_canonical_u32().to_le_bytes());
    }
    h.update(&digest32(c, "program_sha256")?);
    h.update(src.kernel);
    h.update(src.schedule);
    h.update(src.compiler);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    Ok(out)
}

/// The next-row sets' words for F's verifier-key digest (`fmodes::next_rows_digest_words`).
fn next_rows_words(n: &NextRowColumns) -> Vec<u64> {
    let mut d = vec![n.main_width as u64, n.main.len() as u64];
    d.extend(n.main.iter().map(|&c| c as u64));
    d.extend([n.preprocessed_width as u64, n.preprocessed.len() as u64]);
    d.extend(n.preprocessed.iter().map(|&c| c as u64));
    d.extend([n.permutation_width as u64, n.permutation.len() as u64]);
    d.extend(n.permutation.iter().map(|&c| c as u64));
    d
}

/// B's transcript prefix as F's schedule absorbs it (fchild.rs `b_child`): B's domain and B's verifier-key digest as
/// bytes, then the statement (its length, then the public values).
pub fn b_prefix_json(b_domain: &str, b_vk: &[u8; 32], num_public: usize) -> Value {
    json!([
        {"kind": "bytes", "name": "b_domain", "hex": hex(b_domain.as_bytes())},
        {"kind": "bytes", "name": "b_vk_digest", "hex": hex(b_vk)},
        {"kind": "statement", "name": "statement", "first": 0, "len": num_public},
    ])
}

/// F's verifier-key digest (code/l5-layer-f2-20261031/f2/fmodes.rs `f_vk_digest`): F's bus-control width, the opened
/// and derived next-row sets, F's shape and FRI parameters, the child B's shape, FRI tail and tables, every periodic
/// column (`periodic_statement`), the first transcript row's absorbed count, the public-value binding map, the bus name,
/// B's verifier-key digest, B's prefix, B's compiled program's SHA-256 and F's five sources.
pub fn f_vk_digest(f: &Value, air: &KernelAir, derived: &NextRowColumns, opened: &NextRowColumns, b_vk: &[u8; 32],
                   src: &DigestSources<'_>) -> Result<[u8; 32], MaterialError> {
    let mut h = Keccak::v256();
    h.update(text(f, "vk_label")?.as_bytes());
    let s = get(f, "schedule")?;
    let p = get(f, "params")?;
    let c = get(f, "child")?;
    let mut d: Vec<u64> = vec![fkernel::NCTRL_MAIN as u64];
    d.extend(next_rows_words(opened));
    d.extend(next_rows_words(derived));
    d.extend([
        num(s, "n")? as u64,
        fkernel::WIDTH as u64,
        num(s, "q")? as u64,
        num(s, "num_public")? as u64,
        air.periodic.len() as u64,
        num(s, "t_rows")? as u64,
        num(s, "block_rows")? as u64,
        num(s, "program_len")? as u64,
    ]);
    for k in ["log_blowup", "log_final_poly_len", "max_log_arity", "num_queries", "random_codewords", "salt_elems", "digest_elems", "cap_height"] {
        d.push(num(p, k)? as u64);
    }
    d.extend(child_words(c)?);
    update_words(&mut h, &d);
    h.update(&BaseAir::<F>::periodic_statement(air));
    h.update(&(air.k0 as u64).to_le_bytes());
    for lane in &air.pub_terms {
        h.update(&(lane.len() as u64).to_le_bytes());
        for &(sel, j) in lane {
            h.update(&(sel as u64).to_le_bytes());
            h.update(&(j as u64).to_le_bytes());
        }
    }
    h.update(text(f, "bus")?.as_bytes());
    h.update(b_vk);
    for v in prefix_elements(&b_prefix_json(text(c, "domain")?, b_vk, num(c, "num_public")?))? {
        h.update(&v.as_canonical_u32().to_le_bytes());
    }
    h.update(&digest32(c, "program_sha256")?);
    h.update(src.fkernel);
    h.update(src.fschedule);
    h.update(src.compiler);
    h.update(src.fchild);
    h.update(src.fmodes);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    Ok(out)
}

/// SHA-256 of a byte string, in hex.
pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

/// The sources' SHA-256 as the material records them.
pub fn sources_json(src: &DigestSources<'_>) -> Value {
    json!({"fkernel.rs": sha256_hex(src.fkernel), "fschedule.rs": sha256_hex(src.fschedule), "compiler.rs": sha256_hex(src.compiler),
        "fchild.rs": sha256_hex(src.fchild), "fmodes.rs": sha256_hex(src.fmodes), "kernel.rs": sha256_hex(src.kernel),
        "schedule.rs": sha256_hex(src.schedule)})
}

/// The F section's integer parameters as `TrustedParams` states them (FRI and PCS).
pub fn f_params(f: &Value) -> Result<[usize; 8], MaterialError> {
    let p = get(f, "params")?;
    Ok([
        num(p, "log_blowup")?,
        num(p, "log_final_poly_len")?,
        num(p, "max_log_arity")?,
        num(p, "num_queries")?,
        num(p, "random_codewords")?,
        num(p, "salt_elems")?,
        num(p, "digest_elems")?,
        num(p, "cap_height")?,
    ])
}

/// The whole chain from a material document: L0' v2's digest from its section, B's from its section with L0' v2's,
/// F's from its section with B's; each section's recorded digest must equal the recomputed one, and each parent's
/// child digest must equal the child's. Returns (F's, B's, L0' v2's).
pub fn digest_chain(m: &Value, air: &KernelAir, derived: &NextRowColumns, opened: &NextRowColumns, src: &DigestSources<'_>)
    -> Result<([u8; 32], [u8; 32], [u8; 32]), MaterialError> {
    if text(m, "schema")? != SCHEMA {
        return err("unknown key-material schema");
    }
    let (f, b, l) = (get(m, "f")?, get(m, "b")?, get(m, "l0p2")?);
    let l_vk = l0p2_vk_digest(l)?;
    if l_vk != digest32(l, "vk_digest")? || l_vk != digest32(get(b, "child")?, "vk_digest")? {
        return err("L0' v2's identity digest does not reproduce");
    }
    let b_vk = b_vk_digest(b, l, &l_vk, src)?;
    if b_vk != digest32(b, "vk_digest")? || b_vk != digest32(get(f, "child")?, "vk_digest")? {
        return err("B's verifier-key digest does not reproduce");
    }
    let f_vk = f_vk_digest(f, air, derived, opened, &b_vk, src)?;
    if f_vk != digest32(f, "vk_digest")? {
        return err("F's verifier-key digest does not reproduce");
    }
    Ok((f_vk, b_vk, l_vk))
}
