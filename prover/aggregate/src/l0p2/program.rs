//! The straight-line program of the three fixed-base scalar multiplications of the §16.3 relation
//! (the parent keys of the two non-hardened CKD steps and the final key) over the secp256k1 base
//! field, the BIP-32 key arithmetic modulo the group order n (stage S2b), and the tie of the
//! multiplications' scalar bits to the derived keys (stage S4a), with its witness. One row is one
//! operation r = a*b + sigma*c (mod p, or mod n on rows with the modulus selector) on 256-bit values
//! held as 32 byte limbs; operands are read from a write-once memory (ids), results written to it.
//!
//! Scalar multiplication k*G = sum_i k_i * 2^i * G, with the public points 2^i * G as constants:
//! acc starts at a public offset point H (so no step meets the point at infinity), each step adds
//! 2^i * G and keeps the sum when k_i = 1, and a last addition of -H gives k*G. Each addition checks
//! dx * dx^-1 = 1, so dx != 0.
//!
//! Key arithmetic (§16.3, l. 229-232): k0 = I_L of the master HMAC, invalid if k0 = 0 or k0 >= n; each
//! CKDpriv step k = I_L + k_par mod n, invalid if I_L >= n or k = 0. A value x is shown below n by
//! x + d = n - 1 with q = 0 and d a 32-byte witness; a key is shown non-zero by k * k^-1 = 1 mod n.
//!
//! Tie (S4a): each scalar bit is an integer 0 or 1 (its limbs 1..31 are zero and b*b - b = 0 mod p), so
//! the bit means the same under p and under n; the bits are recomposed mod n by Horner's rule
//! (acc = 2*acc + b) and the result must equal the derived key mod n. The keys are private.
//!
//! Keccak input (S4b): the point of k5 is private; its coordinates are shown canonical (x, y <= p - 1)
//! and one row reads both, so that the row's operand limbs give the 64-byte message x || y (big-endian)
//! as 32 little-endian byte pairs to the Keccak table's bus.
//!
//! HMAC buses (S4c): the I_L input rows read their values from the SHA table, and one data row per CKD
//! step gives the step's message to it: the parent key (hardened steps), or the parent point's x with
//! the parity of y as the prefix (non-hardened steps; x canonical, y = 2h + b exactly). No public value
//! remains in this table. Since S4e the index's first byte on a data row is a private witness (column
//! IDX0, range-checked as a byte); the SHA table checks the index's shape.
//! Witness generation is variable-time (spec §12 item 14 (e) not met here).
use num_bigint::BigUint;
use num_traits::{One, Zero};
use tiny_keccak::{Hasher, Keccak};

pub const LIMBS: usize = 32;
pub const CKD_INPUTS: usize = 6; // I_L of the master HMAC and of the five CKDpriv HMACs
/// Public blocks of the field-operation table: none since S4c (the I_L values come from the SHA table
/// over the `il` bus, the points of k3 and k4 go to it over the `data` bus, k5's to the Keccak table).
pub const PUBLIC_BLOCKS: usize = 0;
pub const HEIGHT: usize = 1 << 14;
pub const PAIR_HEIGHT: usize = 1 << 16;
pub const CARRIES: usize = 2 * LIMBS - 2; // carries of convolution columns 0..61; column 62's carry is zero
pub const CARRY_OFFSET: i64 = 1 << 15;

pub fn p() -> BigUint { BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16).unwrap() }
pub fn n() -> BigUint { BigUint::parse_bytes(b"fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16).unwrap() }
pub fn g() -> (BigUint, BigUint) {
    (BigUint::parse_bytes(b"79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16).unwrap(),
     BigUint::parse_bytes(b"483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16).unwrap())
}

pub fn limbs(x: &BigUint) -> [u64; LIMBS] {
    let bytes = x.to_bytes_le();
    assert!(bytes.len() <= LIMBS, "value exceeds 256 bits");
    std::array::from_fn(|i| *bytes.get(i).unwrap_or(&0) as u64)
}

pub fn p_limbs() -> [u64; LIMBS] { limbs(&p()) }
pub fn n_limbs() -> [u64; LIMBS] { limbs(&n()) }

fn inv(x: &BigUint) -> BigUint { let p = p(); x.modpow(&(&p - 2u8), &p) }

pub type Point = (BigUint, BigUint);

pub fn add_points(a: &Point, b: &Point) -> Point {
    let p = p();
    assert!(a.0 != b.0, "addition needs distinct x");
    let lam = ((&b.1 + &p - &a.1) % &p) * inv(&((&b.0 + &p - &a.0) % &p)) % &p;
    let x3 = (&lam * &lam + &p * 2u8 - &a.0 - &b.0) % &p;
    let y3 = (&lam * ((&a.0 + &p - &x3) % &p) + &p - &a.1) % &p;
    (x3, y3)
}

pub fn double_point(a: &Point) -> Point {
    let p = p();
    let lam = (BigUint::from(3u8) * &a.0 * &a.0) % &p * inv(&((BigUint::from(2u8) * &a.1) % &p)) % &p;
    let x3 = (&lam * &lam + &p * 2u8 - &a.0 - &a.0) % &p;
    let y3 = (&lam * ((&a.0 + &p - &x3) % &p) + &p - &a.1) % &p;
    (x3, y3)
}

/// Reference scalar multiplication (double-and-add), independent of the program.
pub fn mul_point(k: &BigUint) -> Point {
    let mut acc: Option<Point> = None;
    let mut addend = g();
    for i in 0..k.bits() {
        if k.bit(i) {
            acc = Some(match acc { None => addend.clone(), Some(a) if a.0 == addend.0 => double_point(&a), Some(a) => add_points(&a, &addend) });
        }
        addend = double_point(&addend);
    }
    acc.expect("non-zero scalar")
}

/// The public offset point H: the first x >= keccak256(label) mod p on the curve, even y.
pub fn offset_point() -> Point {
    let p = p();
    let mut h = Keccak::v256();
    h.update(b"PQ-MIGRATE-AG1-NARROW-SECP256K1-OFFSET-v1");
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    let mut x = BigUint::from_bytes_be(&out) % &p;
    let exp = (&p + 1u8) / 4u8;
    loop {
        let rhs = (&x * &x * &x + 7u8) % &p;
        let y = rhs.modpow(&exp, &p);
        if (&y * &y) % &p == rhs {
            let y = if y.bit(0) { &p - &y } else { y };
            return (x, y);
        }
        x = (x + 1u8) % &p;
    }
}

/// The key-arithmetic statement: the six I_L values (public), and optionally a child key witness
/// that replaces the reduced one (a non-canonical key, for a malicious-prover control).
#[derive(Clone, Debug)]
pub struct Ckd {
    pub il: [BigUint; CKD_INPUTS],
    pub force_key: Option<(usize, BigUint)>,
}

/// A replaced scalar-multiplication witness (malicious-prover controls): multiplication `slot` uses
/// `scalar`, and each bit input becomes bit_i(scalar) + p * bit_i(shift).
#[derive(Clone, Debug)]
pub struct EcOverride {
    pub slot: usize,
    pub scalar: BigUint,
    pub shift: BigUint,
}

/// The keys k0..k5 that the key-arithmetic rows compute (a forced witness stays unreduced).
pub fn derive_keys(ckd: &Ckd) -> Vec<BigUint> {
    let n = n();
    let mut keys = vec![ckd.il[0].clone()];
    for j in 1..CKD_INPUTS {
        let reduced = (&ckd.il[j] + &keys[j - 1]) % &n;
        keys.push(match &ckd.force_key { Some((step, v)) if *step == j => v.clone(), _ => reduced });
    }
    keys
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind { Const, Input, Arith }

#[derive(Clone, Debug)]
pub struct Row {
    pub kind: Kind,
    pub id_r: u64,
    pub ids: [u64; 3],
    pub sub: bool,
    pub modn: bool,
    pub qzero: bool,
    pub bit: bool,
    pub kec: bool,
    pub kil: bool,
    pub kd: bool,
    pub nh: bool,
    pub step: u64,
    pub check: Option<u8>,
    pub out: Option<usize>,
    pub const_value: Option<BigUint>,
}

/// Rows by role, for the controls.
#[derive(Clone, Debug, Default)]
pub struct CkdRows {
    pub start: usize,
    pub slack_il: Vec<usize>,
    pub slack_key: Vec<usize>,
    pub inverse: Vec<usize>,
    pub add: Vec<usize>,
    pub tie_start: usize,
    pub horner: Vec<usize>,
    pub tie_check: Vec<usize>,
    pub keccak_start: usize,
    pub slack_coord: Vec<usize>,
    pub kec_row: usize,
    pub il_rows: Vec<usize>,
    pub data_start: usize,
    pub data_rows: Vec<usize>,
    pub parity_bit: Vec<usize>,
}

/// Program and witness together: `values[id]` is the value of memory cell `id` (id 0 unused).
/// `lenient` builds a best-effort witness for a statement that may be false (negative controls).
pub struct Program {
    pub rows: Vec<Row>,
    pub values: Vec<BigUint>,
    pub ckd_rows: CkdRows,
    pub lenient: bool,
    /// The point of k5 as the program computes it: the Keccak message.
    pub pubkey: Point,
    /// The first byte of each CKD step's index, by step (entry 0 unused): the witness of the data rows'
    /// IDX0 column (S4e). The caller sets it from the path; the program does not depend on it.
    pub index_first: [u64; 6],
    zero: u64,
    one: u64,
}

impl Program {
    fn new(lenient: bool) -> Self {
        let mut prog = Self { rows: vec![], values: vec![BigUint::zero()], ckd_rows: CkdRows::default(), lenient,
            pubkey: (BigUint::zero(), BigUint::zero()), index_first: [0; 6], zero: 0, one: 0 };
        prog.zero = prog.konst(BigUint::zero());
        prog.one = prog.konst(BigUint::one());
        prog
    }
    fn fresh(&mut self, v: BigUint) -> u64 { self.values.push(v); (self.values.len() - 1) as u64 }
    fn push(&mut self, row: Row) -> usize { self.rows.push(row); self.rows.len() - 1 }
    fn row(kind: Kind, id_r: u64) -> Row {
        Row { kind, id_r, ids: [0; 3], sub: false, modn: false, qzero: false, bit: false, kec: false, kil: false, kd: false, nh: false,
              step: 0, check: None, out: None, const_value: None }
    }
    fn konst(&mut self, v: BigUint) -> u64 {
        let id = self.fresh(v.clone());
        self.push(Row { const_value: Some(v), ..Self::row(Kind::Const, id) });
        id
    }
    /// An input row; `out` binds its value to a public block, `bit` marks a scalar bit.
    fn input_at(&mut self, v: BigUint, out: Option<usize>, bit: bool) -> (u64, usize) {
        let id = self.fresh(v);
        let row = self.push(Row { out, bit, ..Self::row(Kind::Input, id) });
        (id, row)
    }
    fn input(&mut self, v: BigUint) -> u64 { self.input_at(v, None, false).0 }
    /// r = a*b + c (sub = false) or a*b - c (sub = true), mod p; stored unless it is a check.
    fn arith(&mut self, a: u64, b: u64, c: u64, sub: bool, check: Option<u8>, out: Option<usize>) -> u64 {
        self.arith_full(a, b, c, sub, false, check, out, None).0
    }
    /// The same mod p or mod n; `forced` replaces the reduced result (malicious-prover controls).
    #[allow(clippy::too_many_arguments)]
    fn arith_full(&mut self, a: u64, b: u64, c: u64, sub: bool, modn: bool, check: Option<u8>, out: Option<usize>,
                  forced: Option<BigUint>) -> (u64, usize) {
        let m = if modn { n() } else { p() };
        let prod = &self.values[a as usize] * &self.values[b as usize];
        let cv = &self.values[c as usize];
        let reduced = if !sub {
            (prod + cv) % &m
        } else if &prod + &m >= *cv {
            (prod + &m - cv) % &m
        } else {
            assert!(self.lenient, "subtrahend exceeds a*b + m for the honest witness");
            BigUint::zero()
        };
        if let Some(expect) = check {
            assert!(self.lenient || reduced == BigUint::from(expect), "check row does not hold for the honest witness");
        }
        let v = forced.unwrap_or(reduced);
        let id = if check.is_none() { self.fresh(v) } else { 0 };
        let row = self.push(Row { ids: [a, b, c], sub, modn, check, out, ..Self::row(Kind::Arith, id) });
        (id, row)
    }
    fn add(&mut self, a: u64, b: u64) -> u64 { let one = self.one; self.arith(a, one, b, false, None, None) }
    fn sub(&mut self, a: u64, b: u64) -> u64 { let one = self.one; self.arith(a, one, b, true, None, None) }
    fn mul(&mut self, a: u64, b: u64) -> u64 { let zero = self.zero; self.arith(a, b, zero, false, None, None) }
    fn fma(&mut self, a: u64, b: u64, c: u64) -> u64 { self.arith(a, b, c, false, None, None) }

    /// acc + Q (affine, dx != 0 checked); returns (x3, y3) ids.
    fn add_affine(&mut self, ax: u64, ay: u64, qx: u64, qy: u64) -> (u64, u64) {
        let p = p();
        let dx = self.sub(qx, ax);
        let dy = self.sub(qy, ay);
        let dxv = self.values[dx as usize].clone();
        assert!(!dxv.is_zero(), "honest witness meets dx = 0");
        let inv_id = self.input(dxv.modpow(&(&p - 2u8), &p));
        let zero = self.zero;
        self.arith(dx, inv_id, zero, false, Some(1), None);
        let lam = self.mul(dy, inv_id);
        let t1 = self.mul(lam, lam);
        let t2 = self.add(ax, qx);
        let x3 = self.sub(t1, t2);
        let t3 = self.sub(ax, x3);
        let t4 = self.mul(lam, t3);
        let y3 = self.sub(t4, ay);
        (x3, y3)
    }

    /// x <= bound (the constant cell `bound`, n - 1 or p - 1): x + d = bound exactly (q = 0, r the
    /// constant), d a 32-byte witness. Returns the row of d. A false claim gets d = bound - x mod 2^256.
    fn below(&mut self, x: u64, bound: u64) -> usize {
        let xv = self.values[x as usize].clone();
        let bv = self.values[bound as usize].clone();
        assert!(self.lenient || xv <= bv, "honest witness has a value above its bound");
        let d = ((BigUint::one() << 256) + &bv - &xv) % (BigUint::one() << 256);
        let (d_id, d_row) = self.input_at(d, None, false);
        let one = self.one;
        self.push(Row { ids: [x, one, d_id], modn: true, qzero: true, const_value: Some(bv), ..Self::row(Kind::Arith, 0) });
        d_row
    }

    /// k != 0 mod n: k * k^-1 = 1 (mod n). A false claim gets the inverse 0. Returns the row of k^-1.
    fn nonzero_mod_n(&mut self, k: u64) -> usize {
        let n = n();
        let kv = &self.values[k as usize] % &n;
        assert!(self.lenient || !kv.is_zero(), "honest witness has a zero key");
        let inverse = if kv.is_zero() { BigUint::zero() } else { kv.modpow(&(&n - 2u8), &n) };
        let (inv_id, inv_row) = self.input_at(inverse, None, false);
        let zero = self.zero;
        self.arith_full(k, inv_id, zero, false, true, Some(1), None, None);
        inv_row
    }
}

/// The program: the three scalar multiplications of k3, k4, k5 (the points of k3 and k4 as public blocks
/// 0..4), the key arithmetic with the six I_L values as blocks 4..10, the tie of the scalar bits to the
/// keys, and the Keccak input row for k5's point. `ec` replaces one multiplication's witness
/// (malicious-prover controls).
pub fn build(ckd: &Ckd, ec: Option<&EcOverride>, lenient: bool) -> Program {
    let p = p();
    let n = n();
    let keys = derive_keys(ckd);
    let mut prog = Program::new(lenient);
    let mut table = Vec::with_capacity(256);
    let mut pt = g();
    for _ in 0..256 {
        let x = prog.konst(pt.0.clone());
        let y = prog.konst(pt.1.clone());
        table.push((x, y));
        pt = double_point(&pt);
    }
    let h = offset_point();
    let hx = prog.konst(h.0.clone());
    let hy = prog.konst(h.1.clone());
    let nhx = prog.konst(h.0.clone());
    let nhy = prog.konst((&p - &h.1) % &p);
    let mut bit_ids = vec![vec![0u64; 256]; 3];
    let mut pt_ids = vec![(0u64, 0u64); 3];
    for j in 0..3 {
        let (k, shift) = match ec {
            Some(o) if o.slot == j => (o.scalar.clone(), o.shift.clone()),
            _ => (&keys[3 + j] % &n, BigUint::zero()),
        };
        let (mut ax, mut ay) = (hx, hy);
        for (i, &(px, py)) in table.iter().enumerate() {
            let value = BigUint::from(k.bit(i as u64) as u8) + if shift.bit(i as u64) { p.clone() } else { BigUint::zero() };
            let (bit, _) = prog.input_at(value, None, true);
            bit_ids[j][i] = bit;
            prog.arith(bit, bit, bit, true, Some(0), None); // bit * bit - bit = 0
            let (x3, y3) = prog.add_affine(ax, ay, px, py);
            let d1 = prog.sub(x3, ax);
            let nx = prog.fma(bit, d1, ax);
            let d2 = prog.sub(y3, ay);
            let ny = prog.fma(bit, d2, ay);
            ax = nx;
            ay = ny;
        }
        let (rx, ry) = prog.add_affine(ax, ay, nhx, nhy);
        let expect = mul_point(&k);
        assert_eq!((prog.values[rx as usize].clone(), prog.values[ry as usize].clone()), expect, "program result differs from k*G");
        pt_ids[j] = (rx, ry);
        if j == 2 { prog.pubkey = expect; }
    }

    // Key arithmetic modulo n; the keys are private. Each I_L input row reads its value from the SHA
    // table's `il` bus (S4c).
    prog.ckd_rows.start = prog.rows.len();
    let nm1 = prog.konst(&n - 1u8);
    let (k0, row) = prog.input_at(ckd.il[0].clone(), None, false);
    prog.rows[row].kil = true;
    prog.ckd_rows.il_rows.push(row);
    let row = prog.below(k0, nm1);
    prog.ckd_rows.slack_key.push(row);
    let row = prog.nonzero_mod_n(k0);
    prog.ckd_rows.inverse.push(row);
    let mut key_ids = vec![k0];
    for j in 1..CKD_INPUTS {
        let (il, row) = prog.input_at(ckd.il[j].clone(), None, false);
        prog.rows[row].kil = true;
        prog.rows[row].step = j as u64;
        prog.ckd_rows.il_rows.push(row);
        let row = prog.below(il, nm1);
        prog.ckd_rows.slack_il.push(row);
        let forced = ckd.force_key.as_ref().filter(|(step, _)| *step == j).map(|(_, v)| v.clone());
        let one = prog.one;
        let (child, row) = prog.arith_full(il, one, key_ids[j - 1], false, true, None, None, forced);
        assert_eq!(prog.values[child as usize], keys[j], "key arithmetic differs from derive_keys");
        prog.ckd_rows.add.push(row);
        let row = prog.below(child, nm1);
        prog.ckd_rows.slack_key.push(row);
        let row = prog.nonzero_mod_n(child);
        prog.ckd_rows.inverse.push(row);
        key_ids.push(child);
    }

    // Tie: sum_i b_i * 2^i = k (mod n) for each multiplication, by Horner's rule from the top bit.
    prog.ckd_rows.tie_start = prog.rows.len();
    let two = prog.konst(BigUint::from(2u8));
    for j in 0..3 {
        let mut acc = prog.zero;
        for i in (0..256).rev() {
            let (next, row) = prog.arith_full(acc, two, bit_ids[j][i], false, true, None, None, None);
            prog.ckd_rows.horner.push(row);
            acc = next;
        }
        let one = prog.one;
        let (_, row) = prog.arith_full(acc, one, key_ids[3 + j], true, true, Some(0), None, None); // acc - k = 0 mod n
        prog.ckd_rows.tie_check.push(row);
    }

    // Keccak input (S4b): k5's point shown canonical, then one row whose operands a and c are x and y; its
    // result x + y mod p is not used. The row's flag puts (a, c) on the Keccak bus.
    prog.ckd_rows.keccak_start = prog.rows.len();
    let pm1 = prog.konst(&p - 1u8);
    for c in [pt_ids[2].0, pt_ids[2].1] {
        let row = prog.below(c, pm1);
        prog.ckd_rows.slack_coord.push(row);
    }
    let one = prog.one;
    let (_, row) = prog.arith_full(pt_ids[2].0, one, pt_ids[2].1, false, false, None, None, None);
    prog.rows[row].kec = true;
    prog.ckd_rows.kec_row = row;

    // HMAC data (S4c): one row per CKD step whose operand a is the parent key (steps 1..3, hardened) or
    // the parent point's x (steps 4 and 5) and whose operand c is 0 or the parity of y; its flags put
    // the message's first 33 bytes, with the prefix and the index's first byte (column IDX0, a private
    // witness since S4e), on the `data` bus. For a point: x <= p - 1, and y = 2h + b exactly with
    // h <= (p - 1) / 2 and b a bit, so b is y's parity.
    prog.ckd_rows.data_start = prog.rows.len();
    let half = prog.konst((&p - 1u8) / 2u8);
    let zero = prog.zero;
    for step in 1..4 {
        let (_, row) = prog.arith_full(key_ids[step - 1], one, zero, false, false, None, None, None);
        prog.rows[row].kd = true;
        prog.rows[row].step = step as u64;
        prog.ckd_rows.data_rows.push(row);
    }
    for (step, slot) in [(4usize, 0usize), (5, 1)] {
        let (x, y) = pt_ids[slot];
        let row = prog.below(x, pm1);
        prog.ckd_rows.slack_coord.push(row);
        let yv = prog.values[y as usize].clone();
        let (hid, _) = prog.input_at(&yv >> 1, None, false);
        let (bid, brow) = prog.input_at(BigUint::from(yv.bit(0) as u8), None, false);
        prog.ckd_rows.parity_bit.push(brow);
        prog.arith(bid, bid, bid, true, Some(0), None); // b * b - b = 0
        let (r, row) = prog.arith_full(hid, two, bid, false, false, None, None, None); // r = 2h + b, exactly:
        prog.rows[row].qzero = true;
        prog.arith_full(r, one, y, true, false, Some(0), None, None); // r - y = 0 mod p
        prog.below(hid, half);
        let (_, row) = prog.arith_full(x, one, bid, false, false, None, None, None);
        prog.rows[row].kd = true;
        prog.rows[row].nh = true;
        prog.rows[row].step = step as u64;
        prog.ckd_rows.data_rows.push(row);
    }
    assert!(prog.rows.len() <= HEIGHT, "program exceeds the table height");
    prog
}

/// Main-trace columns of the field-operation table.
pub mod col {
    use super::{CARRIES, LIMBS};
    pub const A: usize = 0;
    pub const B: usize = A + LIMBS;
    pub const C: usize = B + LIMBS;
    pub const Q: usize = C + LIMBS;
    pub const R: usize = Q + LIMBS;
    pub const CL: usize = R + LIMBS;
    pub const CH: usize = CL + CARRIES;
    pub const MULT: usize = CH + CARRIES;
    // Copies of the program values the buses use, each constrained equal to its periodic column
    // (Plonky3 0.9.0-rc.1 does not supply periodic values when it builds the lookup trace).
    pub const ID_A: usize = MULT + 1;
    pub const ID_B: usize = ID_A + 1;
    pub const ID_C: usize = ID_B + 1;
    pub const ID_R: usize = ID_C + 1;
    pub const ARITH: usize = ID_R + 1;
    pub const KEC: usize = ARITH + 1; // the Keccak input row (S4b)
    pub const KIL: usize = KEC + 1; // an I_L input row (S4c)
    pub const KD: usize = KIL + 1; // an HMAC data row (S4c)
    pub const NH: usize = KD + 1; // a non-hardened data row (S4c)
    pub const STEP: usize = NH + 1; // the CKD step of an I_L or data row (S4c)
    pub const IDX0: usize = STEP + 1; // the index's first byte on a data row, a private witness (S4e)
    pub const WIDTH: usize = IDX0 + 1;
}

/// Byte-pair table columns: multiplicity, and copies of the periodic (lo, hi) entry.
pub mod pair_col {
    pub const MULT: usize = 0;
    pub const LO: usize = 1;
    pub const HI: usize = 2;
    pub const WIDTH: usize = 3;
}

/// Periodic (public, verifier-computed) columns of the field-operation table: the program.
/// CONST_LIMB holds the constant of a constant row and the fixed result of a below-n row (RCONST).
pub mod per {
    use super::{LIMBS, PUBLIC_BLOCKS};
    pub const ID_A: usize = 0;
    pub const ID_B: usize = 1;
    pub const ID_C: usize = 2;
    pub const ID_R: usize = 3;
    pub const ARITH: usize = 4;
    pub const SUB: usize = 5;
    pub const CONST: usize = 6;
    pub const INPUT: usize = 7;
    pub const CHECK1: usize = 8;
    pub const CHECK0: usize = 9;
    pub const MODN: usize = 10;
    pub const QZERO: usize = 11;
    pub const RCONST: usize = 12;
    pub const BIT: usize = 13;
    pub const KEC: usize = 14;
    pub const KIL: usize = 15;
    pub const KD: usize = 16;
    pub const NH: usize = 17;
    pub const STEP: usize = 18;
    pub const CONST_LIMB: usize = 19;
    pub const PUB: usize = CONST_LIMB + LIMBS;
    pub const NUM: usize = PUB + PUBLIC_BLOCKS;
}

pub fn periodic(prog: &Program) -> Vec<Vec<u64>> {
    let mut cols = vec![vec![0u64; HEIGHT]; per::NUM];
    for (r, row) in prog.rows.iter().enumerate() {
        cols[per::ID_R][r] = row.id_r;
        cols[per::STEP][r] = row.step;
        if let Some(t) = row.out { cols[per::PUB + t][r] = 1; }
        match row.kind {
            Kind::Const => {
                cols[per::CONST][r] = 1;
                for (i, l) in limbs(row.const_value.as_ref().unwrap()).iter().enumerate() { cols[per::CONST_LIMB + i][r] = *l; }
            }
            Kind::Input => {
                cols[per::INPUT][r] = 1;
                cols[per::BIT][r] = row.bit as u64;
                cols[per::KIL][r] = row.kil as u64;
            }
            Kind::Arith => {
                cols[per::ARITH][r] = 1;
                cols[per::ID_A][r] = row.ids[0];
                cols[per::ID_B][r] = row.ids[1];
                cols[per::ID_C][r] = row.ids[2];
                cols[per::SUB][r] = row.sub as u64;
                cols[per::MODN][r] = row.modn as u64;
                cols[per::QZERO][r] = row.qzero as u64;
                cols[per::KEC][r] = row.kec as u64;
                cols[per::KD][r] = row.kd as u64;
                cols[per::NH][r] = row.nh as u64;
                match row.check { Some(1) => cols[per::CHECK1][r] = 1, Some(0) => cols[per::CHECK0][r] = 1, _ => {} }
                if let Some(v) = &row.const_value {
                    cols[per::RCONST][r] = 1;
                    for (i, l) in limbs(v).iter().enumerate() { cols[per::CONST_LIMB + i][r] = *l; }
                }
            }
        }
    }
    cols
}

pub fn pair_periodic() -> Vec<Vec<u64>> {
    vec![(0..PAIR_HEIGHT as u64).map(|r| r & 255).collect(), (0..PAIR_HEIGHT as u64).map(|r| r >> 8).collect()]
}


/// Both traces (field-operation table, byte-pair table), row-major as u64.
/// `fault` flips one cell (row, column) of the field-operation trace, for malicious-prover controls.
/// For a lenient program the identities are not asserted: a false statement gets its best-effort trace.
pub fn traces(prog: &Program, fault: Option<(usize, usize)>) -> (Vec<u64>, Vec<u64>) {
    let (p, n) = (p(), n());
    let (pl, nl) = (p_limbs(), n_limbs());
    let two256 = BigUint::one() << 256;
    let mut reads = vec![0u64; prog.values.len()];
    for row in &prog.rows { if row.kind == Kind::Arith { for id in row.ids { reads[id as usize] += 1; } } }
    let mut t = vec![0u64; HEIGHT * col::WIDTH];
    for (r, row) in prog.rows.iter().enumerate() {
        let w = &mut t[r * col::WIDTH..(r + 1) * col::WIDTH];
        let rv = match row.kind {
            Kind::Arith => {
                let (m, ml) = if row.modn { (&n, &nl) } else { (&p, &pl) };
                let [a, b, c] = row.ids.map(|id| prog.values[id as usize].clone());
                let prod = &a * &b;
                let total = if !row.sub {
                    prod + &c
                } else if &prod + m >= c {
                    prod + m - &c
                } else {
                    assert!(prog.lenient, "row {r}: subtrahend exceeds a*b + m for the honest witness");
                    BigUint::zero()
                };
                let rr = match (row.check, &row.const_value) {
                    (Some(v), _) => BigUint::from(v),
                    (None, Some(k)) => k.clone(),
                    (None, None) => prog.values[row.id_r as usize].clone(),
                };
                let q = if row.qzero {
                    BigUint::zero()
                } else if total >= rr && ((&total - &rr) % m).is_zero() {
                    (&total - &rr) / m
                } else {
                    assert!(prog.lenient, "row {r}: identity does not hold for the honest witness");
                    if total >= rr { ((&total - &rr) / m) % &two256 } else { BigUint::zero() }
                };
                let (al, bl, cl, ql, rl) = (limbs(&a), limbs(&b), limbs(&c), limbs(&q), limbs(&rr));
                w[col::A..col::A + LIMBS].copy_from_slice(&al);
                w[col::B..col::B + LIMBS].copy_from_slice(&bl);
                w[col::C..col::C + LIMBS].copy_from_slice(&cl);
                w[col::Q..col::Q + LIMBS].copy_from_slice(&ql);
                let mut carry: i64 = 0;
                for k in 0..2 * LIMBS - 1 {
                    let mut s: i64 = 0;
                    for i in k.saturating_sub(LIMBS - 1)..=k.min(LIMBS - 1) {
                        let j = k - i;
                        s += (al[i] * bl[j]) as i64 - (ql[i] * ml[j]) as i64;
                    }
                    if k < LIMBS {
                        let sigma_c = if row.sub { -(cl[k] as i64) } else { cl[k] as i64 };
                        s += sigma_c + if row.sub { ml[k] as i64 } else { 0 } - rl[k] as i64;
                    }
                    let tk = s + carry;
                    assert!(prog.lenient || tk.rem_euclid(256) == 0, "row {r}: convolution column {k} not divisible");
                    carry = tk.div_euclid(256);
                    if k < CARRIES {
                        let enc = carry + CARRY_OFFSET;
                        assert!(prog.lenient || (0..1 << 16).contains(&enc), "row {r}: carry out of range");
                        let enc = enc.rem_euclid(1 << 16) as u64;
                        w[col::CL + k] = enc & 255;
                        w[col::CH + k] = enc >> 8;
                    }
                }
                assert!(prog.lenient || carry == 0, "row {r}: final carry must vanish");
                rr
            }
            _ => prog.values[row.id_r as usize].clone(),
        };
        w[col::R..col::R + LIMBS].copy_from_slice(&limbs(&rv));
        w[col::MULT] = if row.id_r == 0 { 0 } else { reads[row.id_r as usize] };
        w[col::ID_R] = row.id_r;
        w[col::STEP] = row.step;
        w[col::KIL] = row.kil as u64;
        if row.kind == Kind::Arith {
            w[col::ID_A] = row.ids[0];
            w[col::ID_B] = row.ids[1];
            w[col::ID_C] = row.ids[2];
            w[col::ARITH] = 1;
            w[col::KEC] = row.kec as u64;
            w[col::KD] = row.kd as u64;
            w[col::NH] = row.nh as u64;
            if row.kd { w[col::IDX0] = prog.index_first[row.step as usize]; }
        }
    }
    if let Some((r, c)) = fault { t[r * col::WIDTH + c] ^= 1; }
    let mut mult = vec![0u64; PAIR_HEIGHT];
    for r in 0..HEIGHT {
        let w = &t[r * col::WIDTH..(r + 1) * col::WIDTH];
        for i in 0..LIMBS / 2 {
            for base in [col::Q, col::R] { mult[(w[base + 2 * i] + 256 * w[base + 2 * i + 1]) as usize] += 1; }
        }
        for k in 0..CARRIES { mult[(w[col::CL + k] + 256 * w[col::CH + k]) as usize] += 1; }
        if w[col::KD] == 1 { mult[w[col::IDX0] as usize] += 1; } // (IDX0, 0) on a data row (S4e)
    }
    let pair = (0..PAIR_HEIGHT).flat_map(|r| [mult[r], (r & 255) as u64, (r >> 8) as u64]).collect();
    (t, pair)
}
