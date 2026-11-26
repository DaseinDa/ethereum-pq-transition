//! Client for the Solana enrollment run.
//!
//! `pqsol bench-verify N`
//!     times ML-DSA-44 and Ed25519 verification on this machine (one thread).
//! `pqsol run RPC_URL FUNDER_KEYPAIR.json PROGRAM_ID N_WALLETS SEED OUT_DIR`
//!     funds N wallets, checks the registry program's rules on the first seventeen wallets, then sends every
//!     remaining wallet's enrollment and activation as fast as the node takes them, and writes per-transaction
//!     and per-block statistics read back from the node (blocks.csv lists the slots that have a block).
//! `pqsol verify-in-vm RPC_URL FUNDER_KEYPAIR.json PROGRAM_ID N COMPUTE_UNIT_LIMIT`
//!     simulates N proofs of possession, and N with one bit flipped, against the program of `../program-verify`,
//!     which verifies ML-DSA-44 inside the virtual machine, and prints the compute units the node reports.
//! `pqsol simulate-transfer RPC_URL FUNDER_KEYPAIR.json`
//!     simulates one v1 transfer and prints the node's answer; a quick test of the transaction format.
//!
//! The environment variable PQSOL_SEND_THREADS sets the number of connections that send the bulk phases.
//! Every wallet, ML-DSA-44 key and signature derives from SEED and the wallet's index, so a run can be repeated.
//! Transactions use the v1 format (4,096 bytes at most), written out by hand below; the layout follows
//! `solana-message` 6.0.0, `src/versions/v1/message.rs`.

use base64::Engine as _;
use ed25519_dalek::{Signer as _, SigningKey};
use fips204::ml_dsa_44;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

const PK_LEN: usize = 1312;
const SIG_LEN: usize = 2420;
const RECORD_SEED: &[u8] = b"pq-enroll";
const SYSTEM_PROGRAM: [u8; 32] = [0u8; 32];
const MAX_TX: usize = 4096;
const IX_ENROLL: u8 = 0;
const IX_ACTIVATE: u8 = 1;
const RECORD_LEN_ENROLLED: usize = 42;
const RECORD_LEN_ACTIVATED: usize = 42 + PK_LEN;

const KIND_FUND: u8 = 0;
const KIND_ENROLL: u8 = 1;
const KIND_ACTIVATE: u8 = 2;
const KIND_CHECK: u8 = 3;

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}

fn b58(bytes: &[u8]) -> String {
    bs58::encode(bytes).into_string()
}

fn b58_32(s: &str) -> [u8; 32] {
    let v = bs58::decode(s).into_vec().expect("base58");
    v.try_into().expect("32 bytes")
}

fn b64(bytes: &[u8]) -> String {
    base64::engine::general_purpose::STANDARD.encode(bytes)
}

fn unb64(s: &str) -> Vec<u8> {
    base64::engine::general_purpose::STANDARD.decode(s).expect("base64")
}

/// The record address of a wallet: the address that the system program derives from the wallet's address, the
/// seed and the program id (`create_with_seed`). A wallet has exactly one.
fn record_address(wallet: &[u8; 32], program: &[u8; 32]) -> [u8; 32] {
    sha256(&[wallet, RECORD_SEED, program])
}

struct Wallet {
    ed: SigningKey,
    addr: [u8; 32],
    pq_pk: [u8; PK_LEN],
    pq_sk: ml_dsa_44::PrivateKey,
    record: [u8; 32],
    sign_seed: [u8; 32],
}

fn make_wallet(seed: &str, index: u32, program: &[u8; 32]) -> Wallet {
    let tag = |label: &str| sha256(&[b"pqsol-run", seed.as_bytes(), &index.to_le_bytes(), label.as_bytes()]);
    let ed = SigningKey::from_bytes(&tag("ed25519"));
    let addr = ed.verifying_key().to_bytes();
    let (pk, sk) = ml_dsa_44::KG::keygen_from_seed(&tag("ml-dsa-44"));
    let record = record_address(&addr, program);
    Wallet { ed, addr, pq_pk: pk.into_bytes(), pq_sk: sk, record, sign_seed: tag("ml-dsa-44-sign") }
}

fn pop_message(genesis: &[u8; 32], program: &[u8; 32], w: &Wallet) -> Vec<u8> {
    [b"pq-enroll-v1".as_slice(), genesis, program, &w.addr, &w.pq_pk].concat()
}

fn activation_message(genesis: &[u8; 32], program: &[u8; 32], w: &Wallet) -> Vec<u8> {
    [b"pq-activate-v1".as_slice(), genesis, program, &w.addr, &w.record].concat()
}

fn pq_sign(w: &Wallet, msg: &[u8]) -> [u8; SIG_LEN] {
    w.pq_sk.try_sign_with_seed(&w.sign_seed, msg, &[]).expect("ml-dsa sign")
}

fn pq_verify(pk: &[u8; PK_LEN], msg: &[u8], sig: &[u8; SIG_LEN]) -> bool {
    match ml_dsa_44::PublicKey::try_from_bytes(*pk) {
        Ok(key) => key.verify(msg, sig, &[]),
        Err(_) => false,
    }
}

struct Ix {
    program: u8,
    accounts: Vec<u8>,
    data: Vec<u8>,
}

#[derive(Clone, Copy)]
struct Cfg {
    priority_fee: Option<u64>,
    cu_limit: Option<u32>,
    loaded_limit: Option<u32>,
}

/// A v1 transaction with one signer, the fee payer `keys[0]`. `ro_unsigned` counts the read-only keys at the
/// end of `keys`. Returns the wire bytes; the signature is the last 64 bytes.
fn build_v1(payer: &SigningKey, keys: &[[u8; 32]], ro_unsigned: u8, blockhash: &[u8; 32], cfg: &Cfg, ixs: &[Ix]) -> Vec<u8> {
    let mut m = Vec::with_capacity(MAX_TX);
    m.push(0x81);
    m.extend_from_slice(&[1, 0, ro_unsigned]);
    let mut mask = 0u32;
    if cfg.priority_fee.is_some() {
        mask |= 0b11;
    }
    if cfg.cu_limit.is_some() {
        mask |= 0b100;
    }
    if cfg.loaded_limit.is_some() {
        mask |= 0b1000;
    }
    m.extend_from_slice(&mask.to_le_bytes());
    m.extend_from_slice(blockhash);
    m.push(ixs.len() as u8);
    m.push(keys.len() as u8);
    for k in keys {
        m.extend_from_slice(k);
    }
    if let Some(v) = cfg.priority_fee {
        m.extend_from_slice(&v.to_le_bytes());
    }
    if let Some(v) = cfg.cu_limit {
        m.extend_from_slice(&v.to_le_bytes());
    }
    if let Some(v) = cfg.loaded_limit {
        m.extend_from_slice(&v.to_le_bytes());
    }
    for ix in ixs {
        m.push(ix.program);
        m.push(ix.accounts.len() as u8);
        m.extend_from_slice(&(ix.data.len() as u16).to_le_bytes());
    }
    for ix in ixs {
        m.extend_from_slice(&ix.accounts);
        m.extend_from_slice(&ix.data);
    }
    let sig = payer.sign(&m);
    m.extend_from_slice(&sig.to_bytes());
    assert!(m.len() <= MAX_TX, "transaction of {} bytes", m.len());
    m
}

fn tx_sig(tx: &[u8]) -> [u8; 64] {
    tx[tx.len() - 64..].try_into().unwrap()
}

fn enroll_tx(w: &Wallet, program: &[u8; 32], genesis: &[u8; 32], blockhash: &[u8; 32], cfg: &Cfg) -> Vec<u8> {
    let pop = pq_sign(w, &pop_message(genesis, program, w));
    let mut data = Vec::with_capacity(1 + PK_LEN + SIG_LEN);
    data.push(IX_ENROLL);
    data.extend_from_slice(&w.pq_pk);
    data.extend_from_slice(&pop);
    let keys = [w.addr, w.record, SYSTEM_PROGRAM, *program];
    build_v1(&w.ed, &keys, 2, blockhash, cfg, &[Ix { program: 3, accounts: vec![0, 1, 2], data }])
}

fn activate_tx(w: &Wallet, program: &[u8; 32], genesis: &[u8; 32], blockhash: &[u8; 32], cfg: &Cfg) -> Vec<u8> {
    let sig = pq_sign(w, &activation_message(genesis, program, w));
    let mut data = Vec::with_capacity(1 + PK_LEN + SIG_LEN);
    data.push(IX_ACTIVATE);
    data.extend_from_slice(&w.pq_pk);
    data.extend_from_slice(&sig);
    let keys = [w.addr, w.record, SYSTEM_PROGRAM, *program];
    build_v1(&w.ed, &keys, 2, blockhash, cfg, &[Ix { program: 3, accounts: vec![0, 1, 2], data }])
}

fn rpc(agent: &ureq::Agent, url: &str, method: &str, params: Value) -> Result<Value, String> {
    let body = json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params});
    let mut last = String::new();
    for _ in 0..6 {
        match agent.post(url).send_json(&body) {
            Ok(resp) => {
                let v: Value = resp.into_json().map_err(|e| e.to_string())?;
                if let Some(e) = v.get("error") {
                    return Err(e.to_string());
                }
                return Ok(v["result"].clone());
            }
            Err(e) => {
                last = e.to_string();
                std::thread::sleep(Duration::from_millis(250));
            }
        }
    }
    Err(last)
}

fn agent() -> ureq::Agent {
    ureq::AgentBuilder::new().timeout(Duration::from_secs(60)).build()
}

fn latest_blockhash(a: &ureq::Agent, url: &str) -> ([u8; 32], u64) {
    let v = rpc(a, url, "getLatestBlockhash", json!([{"commitment": "confirmed"}])).expect("blockhash");
    (b58_32(v["value"]["blockhash"].as_str().unwrap()), v["value"]["lastValidBlockHeight"].as_u64().unwrap())
}

fn current_slot(a: &ureq::Agent, url: &str) -> u64 {
    rpc(a, url, "getSlot", json!([{"commitment": "confirmed"}])).expect("slot").as_u64().unwrap()
}

fn send_one(a: &ureq::Agent, url: &str, tx: &[u8]) -> Result<String, String> {
    let r = rpc(a, url, "sendTransaction", json!([b64(tx), {"encoding": "base64", "skipPreflight": true}]))?;
    Ok(r.as_str().unwrap_or("").to_string())
}

/// Sends all transactions over `threads` connections, several to a request (a JSON-RPC batch whose body stays
/// under the 50 KB that the node's RPC accepts). Returns the number the node refused.
fn send_all(url: &str, txs: &[Vec<u8>], threads: usize) -> usize {
    const PER_REQUEST: usize = 8;
    let chunk = txs.len().div_ceil(threads.max(1)).max(1);
    let refused = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|s| {
        for part in txs.chunks(chunk) {
            let refused = &refused;
            s.spawn(move || {
                let a = agent();
                for group in part.chunks(PER_REQUEST) {
                    let calls: Vec<Value> = group
                        .iter()
                        .enumerate()
                        .map(|(i, tx)| {
                            json!({"jsonrpc": "2.0", "id": i, "method": "sendTransaction",
                                   "params": [b64(tx), {"encoding": "base64", "skipPreflight": true}]})
                        })
                        .collect();
                    let accepted = match a.post(url).send_json(&Value::Array(calls)) {
                        Ok(resp) => resp
                            .into_json::<Value>()
                            .ok()
                            .and_then(|v| v.as_array().map(|answers| answers.iter().filter(|x| x["result"].is_string()).count()))
                            .unwrap_or(0),
                        Err(_) => 0,
                    };
                    refused.fetch_add(group.len() - accepted, std::sync::atomic::Ordering::Relaxed);
                }
            });
        }
    });
    refused.into_inner()
}

/// Polls until every signature has a status or the blockhash has expired. Returns signature -> error (None = ok).
fn wait_statuses(a: &ureq::Agent, url: &str, sigs: &[[u8; 64]], last_valid: u64, max_wait: Duration) -> HashMap<[u8; 64], Option<String>> {
    let mut done: HashMap<[u8; 64], Option<String>> = HashMap::new();
    let start = Instant::now();
    loop {
        let pending: Vec<&[u8; 64]> = sigs.iter().filter(|s| !done.contains_key(*s)).collect();
        if pending.is_empty() {
            break;
        }
        for part in pending.chunks(256) {
            let list: Vec<String> = part.iter().map(|s| b58(&s[..])).collect();
            if let Ok(v) = rpc(a, url, "getSignatureStatuses", json!([list])) {
                for (sig, st) in part.iter().zip(v["value"].as_array().cloned().unwrap_or_default()) {
                    if !st.is_null() {
                        let err = if st["err"].is_null() { None } else { Some(st["err"].to_string()) };
                        done.insert(**sig, err);
                    }
                }
            }
        }
        let height = rpc(a, url, "getBlockHeight", json!([{"commitment": "confirmed"}])).ok().and_then(|v| v.as_u64()).unwrap_or(0);
        if height > last_valid + 5 || start.elapsed() > max_wait {
            break;
        }
        std::thread::sleep(Duration::from_millis(300));
    }
    done
}

struct TxRow {
    slot: u64,
    kind: u8,
    bytes: usize,
    cu: u64,
    cost: u64,
    fee: u64,
    failed: bool,
}

struct BlockRow {
    slot: u64,
    time: i64,
    txs: usize,
    by_kind: [usize; 5],
    bytes: usize,
    cost: u64,
    cu: u64,
}

fn first_signature(raw: &[u8]) -> Option<[u8; 64]> {
    if raw.is_empty() {
        return None;
    }
    if raw[0] == 0x81 {
        let n = raw[1] as usize;
        let at = raw.len().checked_sub(64 * n)?;
        return raw.get(at..at + 64)?.try_into().ok();
    }
    raw.get(1..65)?.try_into().ok()
}

fn scan_blocks(a: &ureq::Agent, url: &str, from: u64, to: u64, kinds: &HashMap<[u8; 64], u8>) -> (Vec<BlockRow>, Vec<TxRow>) {
    let mut blocks = Vec::new();
    let mut rows = Vec::new();
    for slot in from..=to {
        let opts = json!({"encoding": "base64", "transactionDetails": "full", "rewards": false,
                          "maxSupportedTransactionVersion": 1, "commitment": "confirmed"});
        let b = match rpc(a, url, "getBlock", json!([slot, opts])) {
            Ok(b) if !b.is_null() => b,
            Ok(_) => panic!("getBlock returned nothing for slot {slot}"),
            // -32007 and -32009: the slot was skipped, it has no block
            Err(e) if e.contains("-32007") || e.contains("-32009") => continue,
            Err(e) => panic!("getBlock failed for slot {slot}: {e}"),
        };
        let mut row = BlockRow { slot, time: b["blockTime"].as_i64().unwrap_or(0), txs: 0, by_kind: [0; 5], bytes: 0, cost: 0, cu: 0 };
        for t in b["transactions"].as_array().cloned().unwrap_or_default() {
            let raw = unb64(t["transaction"][0].as_str().unwrap_or(""));
            let kind = first_signature(&raw).and_then(|s| kinds.get(&s).copied()).unwrap_or(4);
            let meta = &t["meta"];
            let cu = meta["computeUnitsConsumed"].as_u64().unwrap_or(0);
            let cost = meta["costUnits"].as_u64().unwrap_or(0);
            row.txs += 1;
            row.by_kind[kind as usize] += 1;
            row.bytes += raw.len();
            row.cost += cost;
            row.cu += cu;
            rows.push(TxRow { slot, kind, bytes: raw.len(), cu, cost, fee: meta["fee"].as_u64().unwrap_or(0), failed: !meta["err"].is_null() });
        }
        blocks.push(row);
    }
    (blocks, rows)
}

fn summary(values: &mut Vec<u64>) -> Value {
    if values.is_empty() {
        return json!(null);
    }
    values.sort_unstable();
    let n = values.len();
    let sum: u128 = values.iter().map(|v| *v as u128).sum();
    // the median of an even number of values is the mean of the two middle ones
    let median = if n % 2 == 1 {
        json!(values[n / 2])
    } else {
        let two = values[n / 2 - 1] as u128 + values[n / 2] as u128;
        if two % 2 == 0 {
            json!((two / 2) as u64)
        } else {
            json!(two as f64 / 2.0)
        }
    };
    json!({"n": n, "min": values[0], "median": median, "p90": values[((n * 9) / 10).min(n - 1)], "max": values[n - 1],
           "mean": (sum as f64) / (n as f64)})
}

fn bench_verify(n: usize) {
    let program = [7u8; 32];
    let genesis = [9u8; 32];
    let wallets: Vec<Wallet> = (0..n as u32).map(|i| make_wallet("bench", i, &program)).collect();
    let msgs: Vec<Vec<u8>> = wallets.iter().map(|w| pop_message(&genesis, &program, w)).collect();
    let sigs: Vec<[u8; SIG_LEN]> = wallets.iter().zip(&msgs).map(|(w, m)| pq_sign(w, m)).collect();
    let ed_sigs: Vec<ed25519_dalek::Signature> = wallets.iter().zip(&msgs).map(|(w, m)| w.ed.sign(m)).collect();
    let mut rounds = Vec::new();
    for round in 0..5 {
        let mut pq_ns = Vec::with_capacity(n);
        let mut ed_ns = Vec::with_capacity(n);
        for i in 0..n {
            let t = Instant::now();
            let ok = pq_verify(&wallets[i].pq_pk, &msgs[i], &sigs[i]);
            pq_ns.push(t.elapsed().as_nanos() as u64);
            assert!(ok);
            let vk = wallets[i].ed.verifying_key();
            let t = Instant::now();
            let ok = vk.verify_strict(&msgs[i], &ed_sigs[i]).is_ok();
            ed_ns.push(t.elapsed().as_nanos() as u64);
            assert!(ok);
        }
        rounds.push(json!({"round": round, "ml_dsa_44_verify_ns": summary(&mut pq_ns), "ed25519_verify_ns": summary(&mut ed_ns)}));
    }
    // a forged signature must fail
    let mut bad = sigs[0];
    bad[10] ^= 1;
    assert!(!pq_verify(&wallets[0].pq_pk, &msgs[0], &bad));
    let out = json!({"library": "fips204 0.5.0 (ML-DSA-44, public key decoded for every verification), ed25519-dalek 2 (verify_strict)",
                     "threads": 1, "samples_per_round": n, "message_bytes": msgs[0].len(), "rounds": rounds});
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}

fn read_keypair(path: &str) -> SigningKey {
    let v: Vec<u8> = serde_json::from_str(&std::fs::read_to_string(path).expect("keypair file")).expect("keypair json");
    SigningKey::from_bytes(&v[..32].try_into().unwrap())
}

fn get_tx(a: &ureq::Agent, url: &str, sig: &[u8; 64]) -> Value {
    for _ in 0..40 {
        let opts = json!({"encoding": "json", "maxSupportedTransactionVersion": 1, "commitment": "confirmed"});
        if let Ok(v) = rpc(a, url, "getTransaction", json!([b58(&sig[..]), opts])) {
            if !v.is_null() {
                return v;
            }
        }
        std::thread::sleep(Duration::from_millis(250));
    }
    json!(null)
}

fn account_data(a: &ureq::Agent, url: &str, addr: &[u8; 32]) -> Option<(Vec<u8>, u64, String)> {
    let v = rpc(a, url, "getAccountInfo", json!([b58(addr), {"encoding": "base64", "commitment": "confirmed"}])).ok()?;
    let val = &v["value"];
    if val.is_null() {
        return None;
    }
    Some((unb64(val["data"][0].as_str()?), val["lamports"].as_u64()?, val["owner"].as_str()?.to_string()))
}

/// Sends one transaction and waits for it. Returns (meta of the transaction, signature).
fn send_and_get(a: &ureq::Agent, url: &str, tx: &[u8]) -> (Value, [u8; 64]) {
    let sig = tx_sig(tx);
    send_one(a, url, tx).expect("send");
    (get_tx(a, url, &sig), sig)
}

/// True if the node returned the transaction and it ran without error.
fn landed_ok(t: &Value) -> bool {
    !t.is_null() && t["meta"]["err"].is_null()
}

fn meta_brief(t: &Value, bytes: usize) -> Value {
    let m = &t["meta"];
    json!({"slot": t["slot"], "bytes": bytes, "computeUnitsConsumed": m["computeUnitsConsumed"], "costUnits": m["costUnits"],
           "fee": m["fee"], "err": m["err"]})
}

fn run(url: &str, funder_path: &str, program_b58: &str, n: u32, seed: &str, out_dir: &str) {
    let a = agent();
    let program = b58_32(program_b58);
    let funder = read_keypair(funder_path);
    let funder_addr = funder.verifying_key().to_bytes();
    let genesis = b58_32(rpc(&a, url, "getGenesisHash", json!([])).expect("genesis").as_str().unwrap());
    let version = rpc(&a, url, "getVersion", json!([])).expect("version");
    let rent_enrolled = rpc(&a, url, "getMinimumBalanceForRentExemption", json!([RECORD_LEN_ENROLLED])).unwrap().as_u64().unwrap();
    let rent_activated = rpc(&a, url, "getMinimumBalanceForRentExemption", json!([RECORD_LEN_ACTIVATED])).unwrap().as_u64().unwrap();
    std::fs::create_dir_all(out_dir).unwrap();
    assert!(n >= 18, "N_WALLETS must be at least 18: seventeen wallets are used by the checks");
    let t_run = Instant::now();
    let slot_start = current_slot(&a, url);
    // Connections used to send the bulk phases (environment variable PQSOL_SEND_THREADS, 16 if unset).
    let send_threads: usize = std::env::var("PQSOL_SEND_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(16);

    eprintln!("generating {n} wallets");
    let threads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(8).min(16);
    let mut wallets: Vec<Wallet> = Vec::with_capacity(n as usize);
    std::thread::scope(|s| {
        let per = (n as usize).div_ceil(threads);
        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let program = &program;
                s.spawn(move || {
                    let lo = (t * per).min(n as usize) as u32;
                    let hi = ((t + 1) * per).min(n as usize) as u32;
                    (lo..hi).map(|i| make_wallet(seed, i, program)).collect::<Vec<_>>()
                })
            })
            .collect();
        for h in handles {
            wallets.extend(h.join().unwrap());
        }
    });

    let mut kinds: HashMap<[u8; 64], u8> = HashMap::new();
    // A v1 transaction has no default limits: without them it fails with MaxLoadedAccountsDataSizeExceeded.
    let fund_cfg = Cfg { priority_fee: None, cu_limit: Some(12_000), loaded_limit: Some(65_536) };

    // ---- funding: 40 transfers per transaction
    let fund_lamports: u64 = rent_activated + 5_000_000;
    let mut unfunded: Vec<usize> = (0..wallets.len()).collect();
    let mut fund_rounds = 0;
    while !unfunded.is_empty() && fund_rounds < 8 {
        fund_rounds += 1;
        let (bh, last_valid) = latest_blockhash(&a, url);
        let mut txs = Vec::new();
        let mut groups = Vec::new();
        for group in unfunded.chunks(40) {
            let mut keys = vec![funder_addr];
            keys.extend(group.iter().map(|i| wallets[*i].addr));
            keys.push(SYSTEM_PROGRAM);
            let prog_idx = (keys.len() - 1) as u8;
            let ixs: Vec<Ix> = (0..group.len())
                .map(|j| {
                    let mut data = 2u32.to_le_bytes().to_vec();
                    data.extend_from_slice(&fund_lamports.to_le_bytes());
                    Ix { program: prog_idx, accounts: vec![0, (j + 1) as u8], data }
                })
                .collect();
            let tx = build_v1(&funder, &keys, 1, &bh, &fund_cfg, &ixs);
            kinds.insert(tx_sig(&tx), KIND_FUND);
            groups.push(group.to_vec());
            txs.push(tx);
        }
        send_all(url, &txs, 8);
        let sigs: Vec<[u8; 64]> = txs.iter().map(|t| tx_sig(t)).collect();
        let st = wait_statuses(&a, url, &sigs, last_valid, Duration::from_secs(120));
        let mut still = Vec::new();
        for (sig, group) in sigs.iter().zip(groups) {
            if !matches!(st.get(sig), Some(None)) {
                still.extend(group);
            }
        }
        unfunded = still;
    }
    assert!(unfunded.is_empty(), "funding incomplete");
    eprintln!("funded in {fund_rounds} round(s)");

    // ---- checks of the program's rules on the first wallets, one transaction at a time
    let mut checks = Vec::new();
    let mut probes = Vec::new();
    let roomy = Cfg { priority_fee: None, cu_limit: Some(60_000), loaded_limit: Some(1 << 20) };
    let simulate = |tx: &[u8]| -> Value {
        rpc(&a, url, "simulateTransaction", json!([b64(tx), {"encoding": "base64", "sigVerify": true, "commitment": "confirmed"}]))
            .map(|v| v["value"].clone())
            .unwrap_or(json!(null))
    };
    // Tight limits from a simulation: compute units plus 15 %, loaded data rounded up to 32 KiB pages.
    let tight_from = |sim: &Value| -> Cfg {
        let cu = sim["unitsConsumed"].as_u64().unwrap_or(40_000);
        let size = sim["loadedAccountsDataSize"].as_u64().unwrap_or(1 << 20);
        Cfg {
            priority_fee: None,
            cu_limit: Some((((cu as f64) * 1.15 / 100.0).ceil() as u32) * 100),
            loaded_limit: Some((size.div_ceil(32_768) * 32_768) as u32),
        }
    };
    let mut tight_enroll = roomy;
    let mut tight_activate = roomy;
    let mut simulations = Vec::new();
    let n_probe = 8usize;
    for i in 0..n_probe {
        let w = &wallets[i];
        let use_tight = i >= n_probe / 2;
        let (bh, _) = latest_blockhash(&a, url);
        if i == 0 {
            let s = simulate(&enroll_tx(w, &program, &genesis, &bh, &roomy));
            tight_enroll = tight_from(&s);
            simulations.push(json!({"step": "enroll", "unitsConsumed": s["unitsConsumed"],
                                    "loadedAccountsDataSize": s["loadedAccountsDataSize"], "err": s["err"]}));
        }
        let cfg_e = if use_tight { tight_enroll } else { roomy };
        let tx = enroll_tx(w, &program, &genesis, &bh, &cfg_e);
        let (t, sig) = send_and_get(&a, url, &tx);
        kinds.insert(sig, KIND_CHECK);
        let rec = account_data(&a, url, &w.record);
        let ok_enroll = landed_ok(&t)
            && rec.as_ref().map_or(false, |(d, _, owner)| {
                d.len() == RECORD_LEN_ENROLLED && d[0] == 1 && d[1] == 1 && d[10..42] == sha256(&[&w.pq_pk]) && owner == program_b58
            });
        let enroll_meta = meta_brief(&t, tx.len());
        let (bh, _) = latest_blockhash(&a, url);
        if i == 0 {
            let s = simulate(&activate_tx(w, &program, &genesis, &bh, &roomy));
            tight_activate = tight_from(&s);
            simulations.push(json!({"step": "activate", "unitsConsumed": s["unitsConsumed"],
                                    "loadedAccountsDataSize": s["loadedAccountsDataSize"], "err": s["err"]}));
        }
        let cfg_a = if use_tight { tight_activate } else { roomy };
        let tx2 = activate_tx(w, &program, &genesis, &bh, &cfg_a);
        let (t2, sig2) = send_and_get(&a, url, &tx2);
        kinds.insert(sig2, KIND_CHECK);
        let rec2 = account_data(&a, url, &w.record);
        let ok_activate = landed_ok(&t2)
            && rec2.as_ref().map_or(false, |(d, lamports, _)| {
                d.len() == RECORD_LEN_ACTIVATED && d[0] == 2 && d[42..] == w.pq_pk[..] && *lamports >= rent_activated
            });
        probes.push(json!({"wallet": i, "limits": if use_tight { "tight" } else { "roomy" },
                           "enroll_limits": {"compute_units": cfg_e.cu_limit, "loaded_accounts_data_size": cfg_e.loaded_limit},
                           "activate_limits": {"compute_units": cfg_a.cu_limit, "loaded_accounts_data_size": cfg_a.loaded_limit},
                           "enroll": enroll_meta, "activate": meta_brief(&t2, tx2.len()),
                           "record_after_enroll_ok": ok_enroll, "record_after_activate_ok": ok_activate}));
    }
    checks.push(json!({"check": "enroll then activate: record holds the commitment, then the key", "wallets": n_probe,
                       "pass": probes.iter().all(|p| p["record_after_enroll_ok"] == true && p["record_after_activate_ok"] == true)}));

    let expect_fail = |name: &str, expected: &str, t: &Value, checks: &mut Vec<Value>| {
        let err = t["meta"]["err"].clone();
        let pass = !t.is_null() && err == json!({"InstructionError": [0, expected]});
        checks.push(json!({"check": name, "expected": format!("the transaction fails with {expected}"), "err": err, "pass": pass}));
    };
    {
        let base = n_probe;
        // 1. activation before enrollment
        let w = &wallets[base];
        let (bh, _) = latest_blockhash(&a, url);
        let (t, s) = send_and_get(&a, url, &activate_tx(w, &program, &genesis, &bh, &roomy));
        kinds.insert(s, KIND_CHECK);
        expect_fail("activation before enrollment", "IllegalOwner", &t, &mut checks);
        // 2. a second enrollment of the same wallet
        let w = &wallets[base + 1];
        let (bh, _) = latest_blockhash(&a, url);
        let (t, s) = send_and_get(&a, url, &enroll_tx(w, &program, &genesis, &bh, &roomy));
        kinds.insert(s, KIND_CHECK);
        checks.push(json!({"check": "first enrollment of the wallet used for the duplicate test", "pass": landed_ok(&t)}));
        let (bh2, _) = loop {
            let x = latest_blockhash(&a, url);
            if x.0 != bh {
                break x;
            }
            std::thread::sleep(Duration::from_millis(200));
        };
        let (t, s) = send_and_get(&a, url, &enroll_tx(w, &program, &genesis, &bh2, &roomy));
        kinds.insert(s, KIND_CHECK);
        expect_fail("second enrollment of an enrolled wallet", "AccountAlreadyInitialized", &t, &mut checks);
        // 3. activation with another public key than the committed one
        let other = &wallets[base + 2];
        let (bh, _) = latest_blockhash(&a, url);
        let sig = pq_sign(w, &activation_message(&genesis, &program, w));
        let mut data = vec![IX_ACTIVATE];
        data.extend_from_slice(&other.pq_pk);
        data.extend_from_slice(&sig);
        let tx = build_v1(&w.ed, &[w.addr, w.record, SYSTEM_PROGRAM, program], 2, &bh, &roomy, &[Ix { program: 3, accounts: vec![0, 1, 2], data }]);
        let (t, s) = send_and_get(&a, url, &tx);
        kinds.insert(s, KIND_CHECK);
        expect_fail("activation with a public key that does not match the commitment", "InvalidArgument", &t, &mut checks);
        // 4. enrollment into another wallet's record
        let w3 = &wallets[base + 3];
        let w4 = &wallets[base + 4];
        let (bh, _) = latest_blockhash(&a, url);
        let pop = pq_sign(w3, &pop_message(&genesis, &program, w3));
        let mut data = vec![IX_ENROLL];
        data.extend_from_slice(&w3.pq_pk);
        data.extend_from_slice(&pop);
        let tx = build_v1(&w3.ed, &[w3.addr, w4.record, SYSTEM_PROGRAM, program], 2, &bh, &roomy, &[Ix { program: 3, accounts: vec![0, 1, 2], data }]);
        let (t, s) = send_and_get(&a, url, &tx);
        kinds.insert(s, KIND_CHECK);
        expect_fail("enrollment into another wallet's record", "InvalidSeeds", &t, &mut checks);
        // 5. enrollment for a wallet that did not sign (another wallet pays)
        let w5 = &wallets[base + 5];
        let (bh, _) = latest_blockhash(&a, url);
        let pop = pq_sign(w5, &pop_message(&genesis, &program, w5));
        let mut data = vec![IX_ENROLL];
        data.extend_from_slice(&w5.pq_pk);
        data.extend_from_slice(&pop);
        let tx = build_v1(&w3.ed, &[w3.addr, w5.addr, w5.record, SYSTEM_PROGRAM, program], 2, &bh, &roomy, &[Ix { program: 4, accounts: vec![1, 2, 3], data }]);
        let (t, s) = send_and_get(&a, url, &tx);
        kinds.insert(s, KIND_CHECK);
        expect_fail("enrollment of a wallet that did not sign", "MissingRequiredSignature", &t, &mut checks);
        // 6. to 8. someone sends lamports to a record address before its wallet enrolls: the enrollment must
        // still succeed (it tops the address up if needed and allocates it), and so must the activation, which
        // in the third case finds the record already funded and transfers nothing
        let rent_empty = rpc(&a, url, "getMinimumBalanceForRentExemption", json!([0])).unwrap().as_u64().unwrap();
        for (k, sent, label) in [
            (base + 6, (rent_empty + rent_enrolled) / 2, "less than the enrolled record needs"),
            (base + 7, 2 * rent_enrolled, "more than the enrolled record needs"),
            (base + 8, rent_activated, "as much as the activated record needs"),
        ] {
            let w = &wallets[k];
            let (bh, _) = latest_blockhash(&a, url);
            let mut data = 2u32.to_le_bytes().to_vec();
            data.extend_from_slice(&sent.to_le_bytes());
            let tx = build_v1(&funder, &[funder_addr, w.record, SYSTEM_PROGRAM], 1, &bh, &fund_cfg, &[Ix { program: 2, accounts: vec![0, 1], data }]);
            let (t0, s) = send_and_get(&a, url, &tx);
            kinds.insert(s, KIND_CHECK);
            let (bh, _) = latest_blockhash(&a, url);
            let (t1, s) = send_and_get(&a, url, &enroll_tx(w, &program, &genesis, &bh, &roomy));
            kinds.insert(s, KIND_CHECK);
            let (bh, _) = latest_blockhash(&a, url);
            let (t2, s) = send_and_get(&a, url, &activate_tx(w, &program, &genesis, &bh, &roomy));
            kinds.insert(s, KIND_CHECK);
            let rec = account_data(&a, url, &w.record);
            let ok = landed_ok(&t0)
                && landed_ok(&t1)
                && landed_ok(&t2)
                && rec.as_ref().map_or(false, |(d, lamports, owner)| {
                    d.len() == RECORD_LEN_ACTIVATED && d[0] == 2 && d[42..] == w.pq_pk[..] && *lamports >= rent_activated && owner == program_b58
                });
            checks.push(json!({"check": format!("enrollment and activation after someone sent the record address {label}"),
                               "lamports_sent_first": sent, "enroll_compute_units": t1["meta"]["computeUnitsConsumed"],
                               "enroll_cost_units": t1["meta"]["costUnits"], "enroll_err": t1["meta"]["err"],
                               "activate_compute_units": t2["meta"]["computeUnitsConsumed"],
                               "activate_err": t2["meta"]["err"], "pass": ok}));
        }
    }

    // compute-unit limits for the bulk phases: the largest probe value plus a tenth, rounded up to a hundred
    let limit_of = |field: &str| -> u32 {
        let top = probes.iter().filter_map(|p| p[field]["computeUnitsConsumed"].as_u64()).max().unwrap_or(40_000);
        (((top as f64) * 1.1 / 100.0).ceil() as u32) * 100
    };
    let enroll_cfg = Cfg { cu_limit: Some(limit_of("enroll")), ..tight_enroll };
    let activate_cfg = Cfg { cu_limit: Some(limit_of("activate")), ..tight_activate };

    // ---- bulk phases: every remaining wallet enrolls, then activates
    let first_bulk = n_probe + 9;
    let bulk: Vec<usize> = (first_bulk.min(wallets.len())..wallets.len()).collect();
    let mut phases = Vec::new();
    for (name, kind) in [("enroll", KIND_ENROLL), ("activate", KIND_ACTIVATE)] {
        let mut pending: Vec<usize> = bulk.clone();
        let phase_slot = current_slot(&a, url);
        let t0 = Instant::now();
        let mut waves = Vec::new();
        while !pending.is_empty() && waves.len() < 12 {
            let (bh, last_valid) = latest_blockhash(&a, url);
            let t_sign = Instant::now();
            let mut txs: Vec<Vec<u8>> = Vec::with_capacity(pending.len());
            std::thread::scope(|s| {
                let per = pending.len().div_ceil(threads).max(1);
                let handles: Vec<_> = pending
                    .chunks(per)
                    .map(|part| {
                        let (wallets, program, genesis, bh) = (&wallets, &program, &genesis, &bh);
                        let cfg = if kind == KIND_ENROLL { enroll_cfg } else { activate_cfg };
                        s.spawn(move || {
                            part.iter()
                                .map(|i| {
                                    if kind == KIND_ENROLL {
                                        enroll_tx(&wallets[*i], program, genesis, bh, &cfg)
                                    } else {
                                        activate_tx(&wallets[*i], program, genesis, bh, &cfg)
                                    }
                                })
                                .collect::<Vec<_>>()
                        })
                    })
                    .collect();
                for h in handles {
                    txs.extend(h.join().unwrap());
                }
            });
            let sign_s = t_sign.elapsed().as_secs_f64();
            for tx in &txs {
                kinds.insert(tx_sig(tx), kind);
            }
            let t_send = Instant::now();
            let refused = send_all(url, &txs, send_threads);
            let send_s = t_send.elapsed().as_secs_f64();
            let sigs: Vec<[u8; 64]> = txs.iter().map(|t| tx_sig(t)).collect();
            let st = wait_statuses(&a, url, &sigs, last_valid, Duration::from_secs(240));
            let mut still = Vec::new();
            let mut failed = 0;
            for (sig, i) in sigs.iter().zip(&pending) {
                match st.get(sig) {
                    Some(None) => {}
                    Some(Some(_)) => failed += 1,
                    None => still.push(*i),
                }
            }
            waves.push(json!({"sent": txs.len(), "refused_by_rpc": refused, "sign_seconds": sign_s, "send_seconds": send_s,
                              "landed_ok": txs.len() - still.len() - failed, "landed_failed": failed, "not_landed": still.len()}));
            eprintln!("{name}: wave {} sent {} left {}", waves.len(), txs.len(), still.len());
            pending = still;
        }
        phases.push(json!({"phase": name, "wallets": bulk.len(), "first_slot": phase_slot, "last_slot": current_slot(&a, url),
                           "seconds": t0.elapsed().as_secs_f64(), "waves": waves, "not_landed": pending.len(),
                           "compute_unit_limit": if kind == KIND_ENROLL { enroll_cfg.cu_limit } else { activate_cfg.cu_limit },
                           "loaded_accounts_data_size_limit": if kind == KIND_ENROLL { enroll_cfg.loaded_limit } else { activate_cfg.loaded_limit }}));
    }

    // every bulk wallet must now hold an activated record with its own key
    let mut good = 0usize;
    for part in bulk.chunks(100) {
        let keys: Vec<String> = part.iter().map(|i| b58(&wallets[*i].record)).collect();
        let v = rpc(&a, url, "getMultipleAccounts", json!([keys, {"encoding": "base64", "commitment": "confirmed"}])).unwrap_or(json!(null));
        for (i, acc) in part.iter().zip(v["value"].as_array().cloned().unwrap_or_default()) {
            let d = acc["data"][0].as_str().map(unb64).unwrap_or_default();
            if d.len() == RECORD_LEN_ACTIVATED && d[0] == 2 && d[42..] == wallets[*i].pq_pk[..] && acc["owner"].as_str() == Some(program_b58) {
                good += 1;
            }
        }
    }
    checks.push(json!({"check": "every bulk wallet holds an activated record with its own key", "wallets": bulk.len(), "good": good,
                       "pass": good == bulk.len()}));

    // ---- read every block of the run back from the node
    std::thread::sleep(Duration::from_secs(2));
    let slot_end = current_slot(&a, url);
    let (blocks, rows) = scan_blocks(&a, url, slot_start, slot_end, &kinds);
    let names = ["fund", "enroll", "activate", "check", "other"];
    let mut csv = String::from("slot,block_time,txs,fund,enroll,activate,check,other,tx_bytes,cost_units,compute_units\n");
    for b in &blocks {
        csv.push_str(&format!("{},{},{},{},{},{},{},{},{},{},{}\n", b.slot, b.time, b.txs, b.by_kind[0], b.by_kind[1], b.by_kind[2],
                              b.by_kind[3], b.by_kind[4], b.bytes, b.cost, b.cu));
    }
    std::fs::write(format!("{out_dir}/blocks.csv"), csv).unwrap();
    let mut per_kind = serde_json::Map::new();
    for (k, name) in names.iter().enumerate() {
        let sel: Vec<&TxRow> = rows.iter().filter(|r| r.kind as usize == k && !r.failed).collect();
        if sel.is_empty() {
            continue;
        }
        per_kind.insert(name.to_string(), json!({
            "landed_ok": sel.len(),
            "failed": rows.iter().filter(|r| r.kind as usize == k && r.failed).count(),
            "bytes": summary(&mut sel.iter().map(|r| r.bytes as u64).collect()),
            "compute_units": summary(&mut sel.iter().map(|r| r.cu).collect()),
            "cost_units": summary(&mut sel.iter().map(|r| r.cost).collect()),
            "fee_lamports": summary(&mut sel.iter().map(|r| r.fee).collect()),
            "slots": summary(&mut sel.iter().map(|r| r.slot).collect::<HashSet<_>>().into_iter().collect()),
        }));
    }
    let out = json!({
        "rpc": url, "send_threads": send_threads, "node_version": version, "genesis_hash": b58(&genesis), "program_id": program_b58, "seed": seed, "wallets": n,
        "rent_exempt_lamports": {"record_enrolled_42_bytes": rent_enrolled, "record_activated_1354_bytes": rent_activated},
        "funded_lamports_per_wallet": fund_lamports, "first_slot": slot_start, "last_slot": slot_end, "blocks_read": blocks.len(),
        "seconds": t_run.elapsed().as_secs_f64(), "checks": checks, "simulations": simulations, "probes": probes, "phases": phases, "transactions": per_kind,
    });
    std::fs::write(format!("{out_dir}/run.json"), serde_json::to_string_pretty(&out).unwrap()).unwrap();
    println!("{}", serde_json::to_string_pretty(&json!({"checks": out["checks"], "simulations": out["simulations"], "transactions": out["transactions"], "phases": out["phases"]})).unwrap());
}

/// Simulates one v1 transfer of 1 SOL from the funder, without and with a compute-unit limit, and prints the
/// node's answers. Both fail with MaxLoadedAccountsDataSizeExceeded: a v1 transaction has no default limits.
fn simulate_transfer(url: &str, funder_path: &str) {
    let a = agent();
    let funder = read_keypair(funder_path);
    let dest = sha256(&[b"pqsol-debug-destination"]);
    let (bh, _) = latest_blockhash(&a, url);
    let mut data = 2u32.to_le_bytes().to_vec();
    data.extend_from_slice(&1_000_000_000u64.to_le_bytes());
    let keys = [funder.verifying_key().to_bytes(), dest, SYSTEM_PROGRAM];
    for (label, cfg) in [
        ("no config", Cfg { priority_fee: None, cu_limit: None, loaded_limit: None }),
        ("compute-unit limit 10,000", Cfg { priority_fee: None, cu_limit: Some(10_000), loaded_limit: None }),
    ] {
        let tx = build_v1(&funder, &keys, 1, &bh, &cfg, &[Ix { program: 2, accounts: vec![0, 1], data: data.clone() }]);
        let r = rpc(&a, url, "simulateTransaction", json!([b64(&tx), {"encoding": "base64", "sigVerify": true, "commitment": "confirmed"}]));
        println!("{label}: {} bytes -> {}", tx.len(), match r {
            Ok(v) => v["value"].to_string(),
            Err(e) => format!("RPC error {e}"),
        });
    }
}

/// One ML-DSA-44 verification inside the virtual machine: the program of `../program-verify`, by simulation.
fn verify_in_vm(url: &str, funder_path: &str, program_b58: &str, n: u32, cu_limit: u32) {
    let a = agent();
    let program = b58_32(program_b58);
    let funder = read_keypair(funder_path);
    let payer = funder.verifying_key().to_bytes();
    let cfg = Cfg { priority_fee: None, cu_limit: Some(cu_limit), loaded_limit: Some(1 << 20) };
    let mut rows = Vec::new();
    for i in 0..n {
        let w = make_wallet("verify-in-vm", i, &program);
        let msg = [b"pq-enroll-v1".as_slice(), &payer, &w.pq_pk].concat();
        let sig = pq_sign(&w, &msg);
        assert!(pq_verify(&w.pq_pk, &msg, &sig));
        for tamper in [false, true] {
            let mut data = Vec::with_capacity(PK_LEN + SIG_LEN);
            data.extend_from_slice(&w.pq_pk);
            data.extend_from_slice(&sig);
            if tamper {
                data[PK_LEN + 100] ^= 1;
            }
            let (bh, _) = latest_blockhash(&a, url);
            let tx = build_v1(&funder, &[payer, program], 1, &bh, &cfg, &[Ix { program: 1, accounts: vec![0], data }]);
            let opts = json!({"encoding": "base64", "sigVerify": true, "commitment": "confirmed"});
            let v = rpc(&a, url, "simulateTransaction", json!([b64(&tx), opts])).map(|v| v["value"].clone()).unwrap_or(json!(null));
            let logs: Vec<Value> = v["logs"].as_array().cloned().unwrap_or_default();
            let tail: Vec<Value> = logs.iter().skip(logs.len().saturating_sub(3)).cloned().collect();
            rows.push(json!({"key": i, "signature": if tamper { "one bit flipped" } else { "valid" }, "bytes": tx.len(),
                             "err": v["err"], "unitsConsumed": v["unitsConsumed"], "last_logs": tail}));
        }
    }
    let out = json!({"program_id": program_b58, "compute_unit_limit_requested": cu_limit,
                     "node_version": rpc(&a, url, "getVersion", json!([])).ok(), "simulations": rows});
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("simulate-transfer") if args.len() == 4 => simulate_transfer(&args[2], &args[3]),
        Some("verify-in-vm") if args.len() == 7 => {
            verify_in_vm(&args[2], &args[3], &args[4], args[5].parse().expect("N"), args[6].parse().expect("COMPUTE_UNIT_LIMIT"))
        }
        Some("bench-verify") => bench_verify(args.get(2).and_then(|s| s.parse().ok()).unwrap_or(500)),
        Some("run") if args.len() == 8 => run(&args[2], &args[3], &args[4], args[5].parse().expect("N_WALLETS"), &args[6], &args[7]),
        _ => {
            eprintln!("usage: pqsol bench-verify N");
            eprintln!("       pqsol run RPC_URL FUNDER_KEYPAIR.json PROGRAM_ID N_WALLETS SEED OUT_DIR");
            eprintln!("       pqsol verify-in-vm RPC_URL FUNDER_KEYPAIR.json PROGRAM_ID N COMPUTE_UNIT_LIMIT");
            eprintln!("       pqsol simulate-transfer RPC_URL FUNDER_KEYPAIR.json");
            std::process::exit(2);
        }
    }
}
