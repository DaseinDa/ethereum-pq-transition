//! `pq-final-verify`: the command-line front of pq-final-verifier (research packaging; loop-internal self-review; not
//! independently reviewed).
//!
//! ```text
//! pq-final-verify --proof PROOF.postcard --pi PI198.hex [--repeat N]
//! pq-final-verify --self-check
//! ```
//! `--pi` is a file holding the 198 PI bytes as lower-case hex (whitespace ignored). Prints one JSON object. Exit code:
//! 0 accepted, 1 rejected (invalid input or invalid proof), 2 local fault (not a verdict), 64 usage. `--repeat N`
//! verifies N times in this process after the first verification and reports the times (the key is built once).
use std::time::Instant;

use pq_final_verifier::{ErrorClass, PI_BYTES, Pi198, TRUSTED_PARAMS, verifier_ready, verify};

fn usage() -> ! {
    eprintln!("usage: pq-final-verify --proof PROOF.postcard --pi PI198.hex [--repeat N] | pq-final-verify --self-check");
    std::process::exit(64);
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    let t: String = s.split_whitespace().collect();
    let t = t.strip_prefix("0x").unwrap_or(&t);
    if t.len() % 2 != 0 {
        return None;
    }
    (0..t.len() / 2).map(|i| u8::from_str_radix(&t[2 * i..2 * i + 2], 16).ok()).collect()
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned();
    let p = &TRUSTED_PARAMS;
    if args.iter().any(|a| a == "--self-check") {
        let t = Instant::now();
        let r = verifier_ready(p);
        let ms = t.elapsed().as_secs_f64() * 1e3;
        match r {
            Ok(build_ms) => {
                println!("{{\"verifier_key\":\"ok\",\"build_ms\":{build_ms:.3},\"wall_ms\":{ms:.3},\"f_vk_digest\":\"{}\",\"b_vk_digest\":\"{}\",\"l0p2_vk_digest\":\"{}\",\"max_proof_bytes\":{},\"f_domain\":{},\"num_queries\":{},\"log_blowup\":{}}}",
                    hex(p.f_vk_digest()), hex(p.b_vk_digest()), hex(p.l0p2_vk_digest()), p.max_proof_bytes(), json_str(p.f_domain()),
                    p.fri().num_queries, p.fri().log_blowup);
                std::process::exit(0);
            }
            Err(e) => {
                println!("{{\"verifier_key\":\"fault\",\"error\":{}}}", json_str(&e.to_string()));
                std::process::exit(2);
            }
        }
    }
    let (Some(proof_path), Some(pi_path)) = (get("--proof"), get("--pi")) else { usage() };
    let repeat: usize = get("--repeat").map(|r| r.parse().unwrap_or_else(|_| usage())).unwrap_or(0);
    let proof = std::fs::read(&proof_path).unwrap_or_else(|e| {
        eprintln!("{proof_path}: {e}");
        std::process::exit(64)
    });
    let pi_text = std::fs::read_to_string(&pi_path).unwrap_or_else(|e| {
        eprintln!("{pi_path}: {e}");
        std::process::exit(64)
    });
    let Some(pi_vec) = unhex(&pi_text) else { usage() };
    let Ok(pi) = <[u8; PI_BYTES]>::try_from(pi_vec.as_slice()) else {
        eprintln!("the PI file must hold exactly 198 bytes of hex");
        std::process::exit(64)
    };
    let t = Instant::now();
    let r = verify(&proof, &pi, p);
    let first_ms = t.elapsed().as_secs_f64() * 1e3;
    let mut times = vec![];
    for _ in 0..repeat {
        let t = Instant::now();
        let again = verify(&proof, &pi, p);
        times.push(t.elapsed().as_secs_f64() * 1e3);
        assert_eq!(again.is_ok(), r.is_ok(), "the verdict changed between repetitions");
    }
    times.sort_by(f64::total_cmp);
    let stats = if times.is_empty() {
        String::new()
    } else {
        format!(",\"repeat\":{},\"verify_ms_min\":{:.3},\"verify_ms_median\":{:.3},\"verify_ms_max\":{:.3}", times.len(), times[0], times[times.len() / 2], times[times.len() - 1])
    };
    let fields = Pi198::decode(&pi);
    let head = format!("\"proof_bytes\":{},\"chain_id\":{},\"verifier_version\":\"{:#010x}\",\"first_call_ms\":{first_ms:.3}{stats}",
        proof.len(), fields.chain_id_u64().map_or("null".to_string(), |c| c.to_string()), fields.verifier_version);
    match r {
        Ok(()) => {
            println!("{{\"verdict\":\"ACCEPTED\",{head}}}");
            std::process::exit(0);
        }
        Err(e) => {
            let class = match e.class() {
                ErrorClass::InvalidInput => "invalid_input",
                ErrorClass::InvalidProof => "invalid_proof",
                ErrorClass::LocalFault => "local_fault",
            };
            println!("{{\"verdict\":\"{}\",\"class\":\"{class}\",\"kind\":\"{}\",\"error\":{},{head}}}",
                if e.is_rejection() { "REJECTED" } else { "LOCAL_FAULT" }, e.kind(), json_str(&e.to_string()));
            std::process::exit(if e.is_rejection() { 1 } else { 2 });
        }
    }
}
