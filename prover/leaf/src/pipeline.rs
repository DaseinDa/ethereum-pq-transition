//! Pipeline modes of code/pq-proof-pipeline-20261101 (2026-11-01), added to L0' v2's binary
//! (code/l5-leaf-l0p2-20261031) as one new module. L0' v2's relation, AIR sources, program, key generation, prover
//! and verifier are the recorded ones: this module only chooses the witness (a public test seed64 and a path of the
//! five-level shape) and the 198-byte PI (layout 2) of one statement, and calls the recorded functions.
//! - `prove-statement --input - --vk VK.json --out DIR`: the honest proof of L0' v2 for the statement supplied on stdin
//!   (`seed64_hex`, `path`, `pi198_hex`). The witness's derived address must equal the PI's `legacy_address` field (the
//!   relation's only constraint on the PI; every other field is bound by the transcript). L0' v2's key is recomputed
//!   and compared with the recorded vk.json (the fields `checked_key` compares); the program digest must be S5's. The
//!   proof is verified in the proving process. Writes `l0p2.postcard`, `vk.json`, `metrics.json`, `statement.json`.
//! - `verify-statement --dir DIR --vk VK.json --pi PI.hex --out OUT.json`: a fresh process recomputes the key (from the
//!   research fixture's AIRs, which carry no witness), compares it with VK.json, decodes `DIR/l0p2.postcard` strictly
//!   and verifies it for the PI in PI.hex. Exit code 2 on rejection.
//! research packaging; loop-internal self-review; not independently reviewed.
use crate::memory_io as fs;
use std::path::Path;
use std::time::Instant;

use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};

use crate::{Binding, Built, Witness};

const SCHEMA: &str = "pq-proof-pipeline/l0p2/v1";
const TIER: &str = "research packaging; loop-internal self-review; not independently reviewed";

fn unhex(s: &str) -> Vec<u8> {
    let t = s.trim().trim_start_matches("0x");
    assert!(t.len() % 2 == 0, "hex of odd length");
    (0..t.len() / 2).map(|i| u8::from_str_radix(&t[2 * i..2 * i + 2], 16).expect("hex digit")).collect()
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).expect("JSON")
}

/// One statement: the witness (seed64, the five path indices) and the PI.
struct Input {
    seed: [u8; 64],
    path: [u32; 5],
    pi: [u8; 198],
}

fn read_input(path: &Path) -> Input {
    assert_eq!(path, Path::new("-"), "the witness must be supplied on stdin (--input -)");
    let v: Value = serde_json::from_reader(std::io::stdin().lock()).expect("witness JSON on stdin");
    let seed: [u8; 64] = unhex(v["seed64_hex"].as_str().expect("seed64_hex")).try_into().expect("seed64 has 64 bytes");
    let p: Vec<u32> = v["path"].as_array().expect("path").iter().map(|x| u32::try_from(x.as_u64().expect("path index")).expect("u32")).collect();
    let path: [u32; 5] = p.try_into().expect("five path indices");
    let pi: [u8; 198] = unhex(v["pi198_hex"].as_str().expect("pi198_hex")).try_into().expect("PI has 198 bytes");
    Input { seed, path, pi }
}

/// The statement's public values: the Keccak table's 198 values are PI198 (S4d), the other tables have none.
fn set_pi(b: &mut Built, pi: &[u8; 198]) {
    b.pi = *pi;
    b.public = vec![vec![], vec![], pi.iter().map(|&v| F::from_u8(v)).collect(), vec![]];
}

/// The prover's statement: the recorded `build_with` for the witness (not lenient: every assertion of S5 kept), then
/// PI198 in place of the research fixture's. The program is witness-independent and must be S5's.
fn built_for(input: &Input) -> (Built, [u8; 20]) {
    assert!(crate::sha::fits_shape(&input.path), "the path must have the five-level shape of spec section 16.3");
    let mut b = crate::build_with(&Witness { seed: Some(input.seed), path: Some(input.path), ..Default::default() }, false);
    assert_eq!(crate::hex(&b.digest), crate::S5_PROGRAM_DIGEST, "the program differs from S5's");
    let derived = crate::keccak::address(&b.message);
    let reference = crate::instance::derive_with(&input.seed, &input.path).address;
    assert_eq!(derived, reference, "the program's address differs from the reference derivation");
    assert_eq!(&input.pi[64..84], &derived[..], "PI198's legacy_address is not the address that the witness derives");
    set_pi(&mut b, &input.pi);
    (b, derived)
}

/// The verifier's statement: the research fixture's AIRs (`build`, every assertion kept; no witness is needed to
/// verify) with PI198 as the public values.
fn verifier_built(pi: &[u8; 198]) -> Built {
    let mut b = crate::build();
    set_pi(&mut b, pi);
    b
}

/// The recomputed key against a recorded vk.json, on the fields that `checked_key` compares.
fn key_check(b: &Built, common: &p3_batch_stark_c3n::CommonData<crate::Config>, vk_path: &Path) -> Value {
    let pinned = read_json(vk_path);
    let ours = crate::vk_record(b, common);
    let fields = ["preprocessed", "air_digest", "program_digest", "descriptor", "next_row_columns"];
    let rows: Vec<Value> = fields.iter().map(|f| json!({"field": f, "equal": pinned[*f] == ours[*f]})).collect();
    let all = rows.iter().all(|r| r["equal"] == json!(true));
    json!({"all_equal": all, "fields": rows, "vk_path": vk_path.display().to_string(),
        "commitment_keccak256": ours["preprocessed"]["commitment_keccak256"]})
}

fn prove_statement(input_path: &Path, vk_path: &Path, out: &Path) {
    fs::create_dir(out).expect("fresh output directory required");
    let input = read_input(input_path);
    let t = Instant::now();
    let (b, address) = built_for(&input);
    let build_ms = t.elapsed().as_secs_f64() * 1e3;
    let t = Instant::now();
    let data = crate::keygen(&b);
    let keygen_ms = t.elapsed().as_secs_f64() * 1e3;
    let check = key_check(&b, &data.common, vk_path);
    assert_eq!(check["all_equal"], json!(true), "L0' v2's recomputed key differs from the recorded vk.json: {check}");
    let layout = crate::next_rows(&b, &data.common);
    let rss_before = crate::peak_rss_kib();
    let (proof, gen_ms, prove_ms) = crate::prove_with(&b, None, Binding::Expected, &data);
    let rss_after = crate::peak_rss_kib();
    let t = Instant::now();
    let in_process = crate::verify_proof(&b, Binding::Expected, &proof, &b.public, &data.common);
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;
    assert!(in_process.is_ok(), "the honest proof must verify: {in_process:?}");
    let encoded = postcard::to_allocvec(&proof).unwrap();
    let decoded = crate::decode_strict(&encoded).expect("strict decoding of the proof just made");
    assert_eq!(postcard::to_allocvec(&decoded).unwrap(), encoded, "re-encoding is byte-identical");
    crate::save(out, "l0p2.postcard", &encoded);
    let vk = crate::vk_record(&b, &data.common);
    crate::save(out, "vk.json", &serde_json::to_vec_pretty(&vk).unwrap());
    let mut params = crate::params(&b);
    // The recorded `params` names the research fixture's version; this run's PI names its own (bytes 125..129).
    params["research_verifier_version"] = json!(format!("{:#010x}", u32::from_be_bytes(input.pi[125..129].try_into().unwrap())));
    let metrics = json!({"schema": SCHEMA, "review": crate::REVIEW, "tier": TIER, "n": 1, "params": params,
        "configuration": crate::config_record(), "proof_bytes": encoded.len(), "proof_sha256": crate::sha256_hex(&encoded),
        "proof_keccak256": crate::hex(&crate::keccak256(&[&encoded])),
        "vk_preprocessed_commitment_keccak256": vk["preprocessed"]["commitment_keccak256"],
        "key_recomputed_against_recorded_vk_json": check, "next_row_columns": crate::next_rows_record(&layout),
        "claims_ef8": crate::claims(&proof), "program_and_witness_ms": build_ms, "keygen_ms": keygen_ms, "trace_ms": gen_ms,
        "prove_ms": prove_ms, "verify_in_process_ms": verify_ms, "degree_bits": proof.degree_bits,
        "peak_rss_kib_before_prove": rss_before, "peak_rss_kib_after_prove": rss_after,
        "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok(), "breakdown": crate::breakdown(&proof)});
    crate::save(out, "metrics.json", &serde_json::to_vec_pretty(&metrics).unwrap());
    let statement = json!({"schema": SCHEMA, "pi198_hex": crate::hex(&input.pi), "legacy_address": crate::hex(&address),
        "public_values": input.pi.iter().map(|&v| v as u32).collect::<Vec<_>>(), "proof_sha256": crate::sha256_hex(&encoded),
        "program_digest": crate::hex(&b.digest), "witness": "a public test seed64 and a five-level path (not recorded here; see the fixture)"});
    crate::save(out, "statement.json", &serde_json::to_vec_pretty(&statement).unwrap());
    crate::event(json!({"phase": "pipeline_l0p2_prove_done", "proof_bytes": encoded.len(), "proof_sha256": crate::sha256_hex(&encoded),
        "prove_ms": prove_ms, "peak_rss_kib": rss_after, "key_check": check["all_equal"], "accepted_in_process": true}));
}

fn verify_statement(dir: &Path, vk_path: &Path, pi_path: &Path, out: &Path) {
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let pi: [u8; 198] = unhex(&fs::read_to_string(pi_path).expect("PI file")).try_into().expect("PI has 198 bytes");
    let t = Instant::now();
    let b = verifier_built(&pi);
    let build_ms = t.elapsed().as_secs_f64() * 1e3;
    let t = Instant::now();
    let data = crate::keygen(&b);
    let keygen_ms = t.elapsed().as_secs_f64() * 1e3;
    let check = key_check(&b, &data.common, vk_path);
    let encoded = fs::read(dir.join("l0p2.postcard")).expect("l0p2.postcard");
    let t = Instant::now();
    let decoded = crate::decode_strict(&encoded);
    let decode_ms = t.elapsed().as_secs_f64() * 1e3;
    let t = Instant::now();
    let r = decoded.and_then(|p| crate::verify_proof(&b, Binding::Expected, &p, &b.public, &data.common));
    let verify_ms = t.elapsed().as_secs_f64() * 1e3;
    let accepted = r.is_ok() && check["all_equal"] == json!(true);
    let doc = json!({"schema": SCHEMA, "review": crate::REVIEW, "phase": "pipeline_l0p2_fresh_verify",
        "verdict": if accepted { "ACCEPTED" } else { "REJECTED" }, "stark_verifier_error": r.as_ref().err(),
        "key_recomputed_against_recorded_vk_json": check, "pi198_hex": crate::hex(&pi),
        "proof_bytes": encoded.len(), "proof_sha256": crate::sha256_hex(&encoded),
        "timings_ms": {"program": build_ms, "keygen": keygen_ms, "decode": decode_ms, "verify": verify_ms},
        "peak_rss_kib": crate::peak_rss_kib(), "rayon_threads": std::env::var("RAYON_NUM_THREADS").ok()});
    let parent = out.parent().unwrap_or(Path::new("."));
    crate::save(parent, out.file_name().unwrap().to_str().unwrap(), &serde_json::to_vec_pretty(&doc).unwrap());
    crate::event(doc);
    if !accepted {
        std::process::exit(2);
    }
}

pub fn cli(args: &[&str]) {
    match args {
        ["prove-statement", "--input", input, "--vk", vk, "--out", out] => prove_statement(Path::new(input), Path::new(vk), Path::new(out)),
        ["verify-statement", "--dir", dir, "--vk", vk, "--pi", pi, "--out", out] => {
            verify_statement(Path::new(dir), Path::new(vk), Path::new(pi), Path::new(out))
        }
        _ => panic!("usage: prove-statement --input - --vk VK.json --out DIR | verify-statement --dir DIR --vk VK.json --pi PI.hex --out OUT.json"),
    }
}
