//! Agave's own cost model applied to transaction bytes.
//!
//! Reads lines from standard input:
//!   I <feature id>                     a feature that is inactive (every other feature this version knows is active)
//!   T <slot> <index> <base64 bytes>    a transaction as it is on the wire
//! and writes one CSV row per transaction: the limits Agave reads from it, its cost at those limits, its fee and
//! reward, and its priority, which is reward x 1,000,000 / (1 + cost).
//!
//! The steps are those of `calculate_priority_from_bytes` and `calculate_priority_and_cost` in
//! core/src/transaction_priority.rs of Agave v4.4.1, with the same calls into the crates agave-transaction-view,
//! solana-runtime-transaction, solana-cost-model and solana-fee: they give the limits, the cost and the fee.
//! Three things are written out here. Two are values of the bank: its fee rate of 5,000 lamports for every
//! signature (`FeeStructure::default()`) and the reward (`Bank::calculate_reward_and_burn_fee_details` in
//! runtime/src/bank/fee_distribution.rs, which burns 50 % of the signature fees and leaves the rest of the fee).
//! The third is the last division, copied from `calculate_priority_and_cost`, which is private to solana-core.
use {
    agave_feature_set::FeatureSet,
    agave_transaction_view::{
        transaction_version::TransactionVersion, transaction_view::SanitizedTransactionView,
    },
    base64::Engine,
    solana_cost_model::cost_model::CostModel,
    solana_pubkey::Pubkey,
    solana_runtime_transaction::{
        runtime_transaction::RuntimeTransaction, sanitize_config::sanitize_config,
        transaction_meta::TransactionMeta,
    },
    solana_svm_transaction::svm_message::SVMStaticMessage,
    solana_transaction::sanitized::MessageHash,
    std::{
        io::{BufRead, Write},
        str::FromStr,
    },
};

const LAMPORTS_PER_SIGNATURE: u64 = 5_000;
const BURN_PERCENT: u64 = 50;
const MULTIPLIER: u64 = 1_000_000;

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    let mut feature_set = FeatureSet::all_enabled();
    let known = feature_set.active().len();
    let mut switched_off = 0usize;
    let mut rows = 0u64;
    writeln!(
        out,
        "slot,index,version,transaction_signatures,ed25519_signatures,secp256k1_signatures,secp256r1_signatures,\
         write_locks,instruction_data_bytes,compute_unit_limit,loaded_accounts_data_size_limit,priority_fee_lamports,\
         signature_cost,write_lock_cost,data_bytes_cost,programs_execution_cost,loaded_accounts_data_size_cost,\
         cost,cost_by_calculate_cost,signature_fee_lamports,fee_lamports,reward_lamports,priority,simple_vote"
    )
    .unwrap();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let mut parts = line.split_whitespace();
        match parts.next() {
            Some("I") => {
                assert_eq!(rows, 0, "the inactive features come before the transactions");
                let id = Pubkey::from_str(parts.next().unwrap()).unwrap();
                assert!(feature_set.is_active(&id), "feature {id} is not known to this version");
                feature_set.deactivate(&id);
                switched_off += 1;
            }
            Some("T") => {
                let slot = parts.next().unwrap();
                let index = parts.next().unwrap();
                let bytes = base64::engine::general_purpose::STANDARD
                    .decode(parts.next().unwrap())
                    .unwrap();
                let view = SanitizedTransactionView::try_new_sanitized(&bytes[..], &sanitize_config())
                    .unwrap_or_else(|e| panic!("slot {slot} index {index}: {e:?}"));
                let version = match view.version() {
                    TransactionVersion::Legacy => "legacy",
                    TransactionVersion::V0 => "0",
                    TransactionVersion::V1 => "1",
                };
                let tx = RuntimeTransaction::<SanitizedTransactionView<_>>::try_new(
                    view,
                    MessageHash::Compute,
                    None,
                )
                .unwrap_or_else(|e| panic!("slot {slot} index {index}: {e:?}"));
                let config = tx
                    .transaction_configuration(&feature_set)
                    .unwrap_or_else(|e| panic!("slot {slot} index {index}: {e:?}"));
                // the cost as calculate_priority_and_cost takes it
                let cost = CostModel::calculate_cost_for_executed_transaction(
                    &tx,
                    u64::from(config.compute_unit_limit),
                    config.loaded_accounts_data_size_limit,
                    &feature_set,
                );
                // the cost as the cost tracker takes it before the transaction has run
                let estimated = CostModel::calculate_cost(&tx, &feature_set);
                let fee_details = solana_fee::calculate_fee_details(
                    &tx,
                    LAMPORTS_PER_SIGNATURE,
                    config.priority_fee_lamports,
                    solana_fee::FeeFeatures {},
                );
                let burn = fee_details.transaction_fee() * BURN_PERCENT / 100;
                let reward = fee_details
                    .prioritization_fee()
                    .saturating_add(fee_details.transaction_fee().saturating_sub(burn));
                let priority = reward
                    .saturating_mul(MULTIPLIER)
                    .saturating_div(cost.sum().saturating_add(1));
                let details = tx.signature_details();
                writeln!(
                    out,
                    "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
                    slot,
                    index,
                    version,
                    details.num_transaction_signatures(),
                    details.num_ed25519_instruction_signatures(),
                    details.num_secp256k1_instruction_signatures(),
                    details.num_secp256r1_instruction_signatures(),
                    tx.num_write_locks(),
                    tx.instruction_data_len(),
                    config.compute_unit_limit,
                    config.loaded_accounts_data_size_limit,
                    config.priority_fee_lamports,
                    cost.signature_cost(),
                    cost.write_lock_cost(),
                    cost.data_bytes_cost(),
                    cost.programs_execution_cost(),
                    cost.loaded_accounts_data_size_cost(),
                    cost.sum(),
                    estimated.sum(),
                    fee_details.transaction_fee(),
                    fee_details.total_fee(),
                    reward,
                    priority,
                    u8::from(tx.is_simple_vote_transaction()),
                )
                .unwrap();
                rows += 1;
            }
            Some(other) => panic!("unknown line kind {other}"),
            None => {}
        }
    }
    out.flush().unwrap();
    eprintln!("features: {known} known, {switched_off} switched off; transactions: {rows}");
}
