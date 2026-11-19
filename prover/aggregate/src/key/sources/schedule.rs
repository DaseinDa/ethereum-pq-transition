//! The B2 schedule compiler (L5, 2026-11-01; B1's, itself G1's generalized to L0' v2): from the child's shape,
//! configuration and AIRs alone (never from a proof) it derives
//! - the native transcript as an event list and the rows of the native `DuplexChallenger<_, _, 16, 8>`: the child's
//!   prefix as the child's configuration absorbs it (B1: a list of constant or public absorptions; L0' v2's is four
//!   constants: domain, AIR digest, descriptor, program digest), the batch transcript (p3_batch_stark_c3n
//!   transcript.rs: seed, per-table degree bits, main cap, per-table public values, the pinned preprocessed cap, the
//!   lookup challenges, permutation cap, per-table lookup terminals, alpha, quotient cap, zeta), the PCS's claims
//!   (p3-fri pcs_transcript.rs) and FRI (transcript.rs);
//! - the trees: per committed tree its matrices in commitment order (C3n's split matrices, the hiding PCS's random
//!   codewords, the salts), its leaf groups by height (the tallest hashed at the leaf, every shorter group injected
//!   where its height is reached, p3-merkle-tree mmcs/mod.rs l. 783-822), its index bits and its cap;
//! - the query blocks: per query and tree, the injected groups' leaf-hash rows, the path (leaf rows, compression and
//!   injection rows, the cap-read row, and for the canonical tree and the FRI rounds the cap rows that consume the cap
//!   bits);
//! - the DEEP layout per log height (p3-fri verifier.rs l. 1268-1322): the claims in transcript order with their ladder
//!   offsets, one chain per matrix on its group's leaf rows (B1: consecutive single-point matrices whose ladder offsets
//!   are contiguous and whose values end on a row boundary are joined into one chain through their salt rows, K3a's
//!   `deep.pass` rows), each claim's write row and lane;
//! - the ALU program: K2's checks with the roll-ins of the lower heights' reduced openings (verifier.rs l. 1035-1046;
//!   B1: a constant final polynomial is compared with every last fold without the final point), K3a's per (height,
//!   opening point) with x per height, and the compiled batch constraint program (`compiler.rs`);
//! - the bus: every value's address, its single writer and its read count (a cap entry's read count is the prover's);
//! - every control column of the kernel AIR (B2: preprocessed columns; B1: periodic), and the interface map.
//! B1: the table's height is the smallest power of two that holds the transcript and the query blocks (K1's rows) and
//! the ALU program with its reserved rows. B2: the claims, cap entries, lookup terminals, DEEP chain sums and the
//! query's high part are written through the second write slot W2, and the injections read their digest through the
//! slot RI, so none of their rows is reserved: an ALU instruction runs on every row but the LOAD rows and the cap-read
//! rows (which use the operand slots RA and RB).
//! Research prototype; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};

use crate::compiler::{Input, POp, Program};
use crate::kernel::{CAP_BITS, CTRL_NAMES, KernelAir, LOW_BITS, NCTRL, OPS, Op, P2Air, PIdx, constants};

/// One absorption of the child's configuration before the batch transcript (its prefix), as the child's challenger
/// observes it.
#[derive(Clone, Debug)]
pub enum PrefixItem {
    /// `observe_bytes`: the length, then each byte, as constants.
    Bytes(String, Vec<u8>),
    /// `observe_bytes` of a statement part: the length (a constant), then the kernel public values first..first + len.
    PubBytes(String, usize, usize),
    /// Field elements observed as they are, as constants (a descriptor: its length, then its entries).
    Fields(String, Vec<F>),
}

impl PrefixItem {
    pub fn name(&self) -> &str {
        match self {
            PrefixItem::Bytes(n, _) | PrefixItem::PubBytes(n, _, _) | PrefixItem::Fields(n, _) => n,
        }
    }
}

/// The field elements a child's challenger observes for its prefix, with the statement's public values.
pub fn prefix_elements(prefix: &[PrefixItem], pv: &[F]) -> Vec<F> {
    let mut v = vec![];
    for item in prefix {
        match item {
            PrefixItem::Bytes(_, b) => {
                v.push(F::from_usize(b.len()));
                v.extend(b.iter().map(|&x| F::from_u8(x)));
            }
            PrefixItem::PubBytes(_, first, len) => {
                v.push(F::from_usize(*len));
                v.extend(pv[*first..*first + *len].iter().copied());
            }
            PrefixItem::Fields(_, f) => v.extend(f.iter().copied()),
        }
    }
    v
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Src {
    Const(F),
    Pub(usize),
    Wit(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sq {
    LookupAlpha(usize),
    LookupBeta(usize),
    Alpha(usize),
    Zeta(usize),
    PcsAlpha(usize),
    Beta(usize, usize),
    Query(usize),
}

#[derive(Clone, Copy, Debug)]
pub enum Ev {
    Abs(Src),
    Sample(Sq),
}

#[derive(Clone, Debug)]
pub struct TRow {
    pub k: usize,
    pub lanes: [Option<Src>; 8],
    pub samples: Vec<(usize, Sq)>,
}

/// One table of the child, from its AIR, its key and the configuration.
#[derive(Clone, Debug)]
pub struct TableSpec {
    pub name: String,
    /// log2 of the trace domain before the zero-knowledge extension (the selectors' domain).
    pub log_trace: usize,
    pub width: usize,
    pub pre_width: usize,
    /// The kernel public value each of the table's public values is (its index in the kernel's statement).
    pub public: Vec<usize>,
    /// C3n's derived next-row sets: main and preprocessed columns, permutation extension columns.
    pub next_main: Vec<usize>,
    pub next_pre: Vec<usize>,
    pub next_perm: Vec<usize>,
    /// Permutation width in extension columns (lookups + 1; 0 without lookups).
    pub perm_width: usize,
    /// The global bus index of each of the table's lookups.
    pub lookup_bus: Vec<usize>,
    /// log2 of the quotient degree before the zero-knowledge bit, and the committed chunk count.
    pub log_qd: usize,
    pub chunks: usize,
}

impl TableSpec {
    pub fn log_lde(&self, log_blowup: usize) -> usize {
        self.log_trace + 1 + log_blowup
    }
    pub fn has_lookups(&self) -> bool {
        self.perm_width > 0
    }
}

#[derive(Clone)]
pub struct ChildSpec {
    pub name: String,
    pub tables: Vec<TableSpec>,
    pub rc: usize,
    pub salt: usize,
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    /// log2 of the tallest committed height (the query index bits).
    pub index_bits: usize,
    pub fri_log_arities: Vec<usize>,
    /// The child's prefix (its configuration's absorptions before the batch transcript) and the kernel's statement
    /// size: the statement is every public value the prefix and the tables absorb.
    pub prefix: Vec<PrefixItem>,
    pub num_public: usize,
    /// The transcript seeds: the batch transcript's, the PCS's, FRI's.
    pub seeds: [Vec<F>; 3],
    /// The child's verifier-key digest (its identity, covered by the kernel's verifier-key digest).
    pub child_vk: [u8; 32],
    /// The pinned preprocessed commitment (the key's cap).
    pub pre_cap: Vec<[F; 8]>,
    pub num_buses: usize,
    pub max_message_width: usize,
    /// The child's compiled constraint program and the SHA-256 of its canonical file.
    pub program: Arc<Program>,
    pub program_sha256: [u8; 32],
}

impl ChildSpec {
    /// The distinct committed log heights, descending (the FRI inputs).
    pub fn input_log_heights(&self) -> Vec<usize> {
        let set: BTreeSet<usize> = self.tables.iter().map(|t| t.log_lde(self.log_blowup)).collect();
        set.into_iter().rev().collect()
    }
}

/// An opening point: 0 is zeta; 1 + t is zeta * g_t (table t's trace-domain generator).
pub fn pt_name(p: usize) -> String {
    if p == 0 { "zeta".into() } else { format!("zeta_next.table{}", p - 1) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatKind {
    /// Table t's main trace, part 0 (the next-row set, or the whole trace) or 1 (the rest).
    Main(usize, usize),
    Quot(usize, usize),
    Rand(usize),
    Pre(usize),
    /// Table t's permutation trace (base columns), part 0 or 1.
    Perm(usize, usize),
    Fri(usize),
}

#[derive(Clone, Debug)]
pub struct MatSpec {
    pub kind: MatKind,
    pub table: usize,
    /// Committed width (with the hiding PCS's random codewords for a non-preprocessed input matrix).
    pub width: usize,
    /// Trace columns (base columns for a permutation trace) of the matrix, in order (without the random codewords).
    pub cols: Vec<usize>,
    pub log_height: usize,
    pub points: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeKind {
    /// An input round: 0 main, 1 quotient and randomization, 2 preprocessed, 3 permutation.
    Input(usize),
    Fri(usize),
}

/// Matrices hashed together into one digest: the tallest at the leaf, each shorter height injected after
/// `inject_after` compressions (p3-merkle-tree mmcs/mod.rs l. 783-822).
#[derive(Clone, Debug)]
pub struct Group {
    pub mats: Vec<usize>,
    pub log_height: usize,
    pub leaf_len: usize,
    pub lh_rows: usize,
    pub partial: usize,
    pub inject_after: usize,
}

/// How a path's accumulator starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Start {
    /// The canonical path: LOAD of the query element from its squeeze row.
    Load,
    /// The query element (a bus read).
    Xq,
    /// The query element shifted right by d bits (written by the canonical path).
    Shift(usize),
    /// FRI round r >= 1: the accumulator after round r - 1's coset bits.
    Chain(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Node {
    Comp(usize),
    Inj(usize),
}

#[derive(Clone, Debug)]
pub struct TreeSpec {
    pub name: String,
    pub kind: TreeKind,
    pub mats: Vec<MatSpec>,
    pub groups: Vec<Group>,
    /// Index bits of the tree (log2 of its height in leaves).
    pub log_height: usize,
    /// Compression levels walked (log_height - cap bits).
    pub mc: usize,
    /// Index bits consumed on group 0's leaf rows (a FRI round's coset position).
    pub consume_lh: usize,
    /// Index bits below this tree's own bits (consumed by earlier FRI rounds, or the shift of a lower input tree).
    pub skip: usize,
    /// Cap rows after the cap read (the canonical tree and the FRI rounds compute their coset point over every bit).
    pub cap_rows: usize,
    pub start: Start,
    pub canonical: bool,
    // ---- layout inside the tree's block (offsets from the block's first row) ----
    pub group_start: Vec<usize>,
    pub path_start: usize,
    pub nodes: Vec<(usize, Node)>,
    pub cap_read: usize,
    pub end: usize,
    pub block_len: usize,
}

#[derive(Clone, Debug)]
pub struct Segment {
    pub name: String,
    pub kind: &'static str,
    pub first_event: usize,
    pub len: usize,
}

/// One claimed evaluation block: a matrix of an input tree at one opening point, as p3-fri walks them (batch,
/// matrix, point; verifier.rs l. 1280-1298).
#[derive(Clone, Debug)]
pub struct ClaimBlock {
    pub tree: usize,
    pub matrix: usize,
    pub point: usize,
    pub width: usize,
    pub first_claim: usize,
    pub ladder_off: usize,
    pub log_height: usize,
}

/// Contiguous claims at one (height, point) with contiguous ladder offsets: one Horner sum by the ALU.
#[derive(Clone, Debug)]
pub struct ClaimRun {
    pub log_height: usize,
    pub point: usize,
    pub first_claim: usize,
    pub len: usize,
    pub ladder_off: usize,
}

/// One matrix's opened values on its group's leaf rows (B1: or several consecutive single-point matrices joined
/// through the salt rows between them): the DEEP lane sums alpha^(e - 8 row0) v_e over them, the salt rows passing
/// the sum through without a power of alpha, so the joined matrices' terms keep their contiguous ladder offsets.
#[derive(Clone, Debug)]
pub struct DeepChain {
    pub tree: usize,
    /// The chain's first matrix (and every matrix of the chain, in leaf order).
    pub matrix: usize,
    pub matrices: Vec<usize>,
    pub group: usize,
    /// Leaf rows (offsets from the group's first row) holding the chain's values, with the lanes that hold them.
    pub value_rows: Vec<(usize, Vec<usize>)>,
    /// The salt rows between joined matrices (`deep.pass`: D = D').
    pub pass_rows: Vec<usize>,
    /// The lane of the matrix's first value (its chain sum is alpha^shift times the ladder-relative sum).
    pub shift: usize,
    /// For each opening point of the matrix: (point, ladder offset).
    pub offsets: Vec<(usize, usize)>,
    pub log_height: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct ClaimPos {
    pub row: usize,
    pub lane: usize,
}

/// A value carried by the bus (one address each).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Val {
    /// K2's constants: 0 = omega_4^-1, 1 = 2; G1's: see `Schedule::consts`.
    Const(usize),
    Beta(usize),
    Beta2(usize),
    Beta2x2(usize),
    /// beta_r^(2^arity_r), the roll-in factor after round r.
    BetaPow(usize),
    Coeff(usize),
    Squeeze(usize),
    Xq(usize),
    /// The query element shifted right by d bits (a lower input tree's start), written by the canonical path.
    Shift(usize, usize),
    /// The query's high part (bits LOW_BITS..30), written by the canonical path's end row.
    Hi(usize),
    Chain(usize, usize),
    Sigma(usize, usize, usize),
    S(usize, usize),
    E(usize, usize, usize),
    H(usize, usize),
    G(usize, usize, usize),
    HH(usize, usize),
    G2(usize, usize),
    Fold(usize, usize, usize),
    U(usize, usize),
    /// The previous fold plus the roll-in: U(q, r - 1) + beta_{r-1}^(arity) RO(q, h).
    UR(usize, usize),
    Sel(usize, usize, usize),
    M(usize, usize),
    X2(usize),
    XF(usize),
    T(usize, usize),
    // ---- G1: the bus side of the trees ----
    /// Cap entry j of tree t (written by its transcript position through the write port).
    Cap(usize, usize),
    /// The leaf hash of query q's injected group k of tree t (written by the group's last leaf row, WO).
    InjHash(usize, usize, usize),
    // ---- K3a, per height ----
    Alpha,
    Zeta,
    /// zeta * g_t (table t's next point).
    ZetaNext(usize),
    PcsAlpha,
    AP(usize),
    Claim(usize),
    HC(usize, usize),
    /// Partial and final claims sums per (height, point).
    CPart(usize, usize, usize),
    CP(usize, usize),
    /// The input coset point x of query q at log height h (XI(q, H) from the canonical path).
    XI(usize, usize),
    /// x^(2^k) partial powers of the height derivation.
    XP(usize, usize, usize),
    SD(usize, usize),
    DZ(usize, usize, usize),
    IZ(usize, usize, usize),
    UPart(usize, usize, usize, usize),
    UZ(usize, usize, usize),
    TZ(usize, usize, usize),
    /// Reduced opening partial sums: RO(q, h, k); RO(q, h, last) is the reduced opening at height h.
    RO(usize, usize, usize),
    // ---- K3b / G1: the compiled program ----
    LookupAlpha,
    LookupBeta,
    /// Table t's lookup terminal (written by its transcript position through the write port).
    Terminal(usize),
    PubRow(usize),
    Pub(usize),
    Ev(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Writer {
    Alu(usize),
    H(usize),
    O(usize),
    V(usize),
    /// B2: the second write slot W2 on this row (B1: the write port through R).
    W2(usize),
}

#[derive(Clone, Debug)]
pub struct Instr {
    pub op: Op,
    pub a: Option<Val>,
    pub b: Option<Val>,
    pub c: Option<Val>,
    pub r: Option<Val>,
    pub kappa: F,
    pub kappa_x: F,
    pub role: &'static str,
    pub query: Option<usize>,
    pub round: Option<usize>,
    pub lane: usize,
}

pub struct Schedule {
    pub child: ChildSpec,
    pub events: Vec<Ev>,
    pub segments: Vec<Segment>,
    pub ev_pos: Vec<(usize, usize)>,
    pub trows: Vec<TRow>,
    pub wit_len: usize,
    pub wit_segments: Vec<(String, usize, usize)>,
    pub trees: Vec<TreeSpec>,
    pub q: usize,
    pub block_rows: usize,
    pub t_rows: usize,
    pub used_rows: usize,
    pub log_n: usize,
    pub n: usize,
    /// First row of each (query, tree) block.
    pub block_start: Vec<Vec<usize>>,
    pub num_public: usize,
    pub air: KernelAir,
    pub program: Vec<Instr>,
    pub instr_row: Vec<usize>,
    pub addr: HashMap<Val, u32>,
    pub writer: BTreeMap<Val, Writer>,
    pub reads: HashMap<Val, u32>,
    pub rs_reads: Vec<(usize, Val)>,
    /// The rows reading a cap entry (dynamic address): (row, tree).
    pub cap_reads: Vec<(usize, usize)>,
    pub beta_row: Vec<usize>,
    pub coeff_row: Vec<usize>,
    pub alpha_row: usize,
    pub zeta_row: usize,
    pub pcs_alpha_row: usize,
    pub lookup_alpha_row: usize,
    pub lookup_beta_row: usize,
    pub claim_blocks: Vec<ClaimBlock>,
    pub claim_runs: Vec<ClaimRun>,
    pub claim_pos: Vec<ClaimPos>,
    /// Write-port positions of the cap entries and of the terminals.
    pub cap_pos: BTreeMap<(usize, usize), ClaimPos>,
    pub terminal_pos: BTreeMap<usize, ClaimPos>,
    pub chains: Vec<DeepChain>,
    /// B2: the second write slot's writes (row, value): claims, cap entries, terminals, DEEP chain sums, high parts.
    pub w2port: Vec<(usize, Val)>,
    /// B2: the injection rows' reads through the slot RI (row, the injected group's digest).
    pub inj_reads: Vec<(usize, Val)>,
    pub k3a_range: (usize, usize),
    pub k3b_range: (usize, usize),
    /// (height, point) pairs, in program order; the claims' sum of each.
    pub hz: Vec<(usize, usize)>,
    pub c_vals: BTreeMap<(usize, usize), Val>,
    pub u_vals: Vec<BTreeMap<(usize, usize), Val>>,
    /// The roll-in after round r (height h): rounds whose fold is followed by a lower input height.
    pub rollins: BTreeMap<usize, usize>,
    pub pub_src: BTreeMap<(usize, usize), (usize, usize)>,
    pub input_val: BTreeMap<usize, Val>,
    /// G1's ALU constants by name, with their value ids.
    pub consts: Vec<(&'static str, F)>,
    pub heights: Vec<usize>,
}

pub fn bytes_events(ev: &mut Vec<Ev>, bytes: &[u8]) {
    ev.push(Ev::Abs(Src::Const(F::from_usize(bytes.len()))));
    for &b in bytes {
        ev.push(Ev::Abs(Src::Const(F::from_u8(b))));
    }
}

fn seg(segments: &mut Vec<Segment>, ev: &[Ev], start: usize, name: &str, kind: &'static str) {
    segments.push(Segment { name: name.into(), kind, first_event: start, len: ev.len() - start });
}

/// The input trees in the PCS's round order (C3n verifier/mod.rs l. 206-439): main, quotient and randomization,
/// preprocessed, permutation; then the FRI rounds. Matrices in commitment order with their points.
pub fn trees(c: &ChildSpec) -> Vec<TreeSpec> {
    let rc = c.rc;
    let lb = c.log_blowup;
    let mut inputs: Vec<(String, TreeKind, Vec<MatSpec>)> = vec![];
    // Main: per table, C3n's split (verifier/mod.rs l. 233-252; next_row.rs l. 251-260).
    let mut main = vec![];
    for (t, tb) in c.tables.iter().enumerate() {
        let lh = tb.log_lde(lb);
        let next_pt = 1 + t;
        if tb.next_main.is_empty() {
            main.push(MatSpec { kind: MatKind::Main(t, 0), table: t, width: tb.width + rc, cols: (0..tb.width).collect(), log_height: lh, points: vec![0] });
        } else if tb.next_main.len() == tb.width {
            main.push(MatSpec { kind: MatKind::Main(t, 0), table: t, width: tb.width + rc, cols: (0..tb.width).collect(), log_height: lh, points: vec![0, next_pt] });
        } else {
            let rest: Vec<usize> = (0..tb.width).filter(|x| !tb.next_main.contains(x)).collect();
            main.push(MatSpec { kind: MatKind::Main(t, 0), table: t, width: tb.next_main.len() + rc, cols: tb.next_main.clone(), log_height: lh, points: vec![0, next_pt] });
            main.push(MatSpec { kind: MatKind::Main(t, 1), table: t, width: rest.len() + rc, cols: rest, log_height: lh, points: vec![0] });
        }
    }
    inputs.push(("main".into(), TreeKind::Input(0), main));
    // Quotient chunks per table, then the randomization polynomials (C3, verifier/mod.rs l. 298-322).
    let mut quot = vec![];
    for (t, tb) in c.tables.iter().enumerate() {
        for ch in 0..tb.chunks {
            quot.push(MatSpec { kind: MatKind::Quot(t, ch), table: t, width: 8 + rc, cols: (0..8).collect(), log_height: tb.log_lde(lb), points: vec![0] });
        }
    }
    for (t, tb) in c.tables.iter().enumerate() {
        quot.push(MatSpec { kind: MatKind::Rand(t), table: t, width: 8 + rc, cols: (0..8).collect(), log_height: tb.log_lde(lb), points: vec![0] });
    }
    inputs.push(("quotient_and_randomization".into(), TreeKind::Input(1), quot));
    // Preprocessed: one matrix per table that has preprocessed columns, no random codewords (verifier/mod.rs l. 327-404).
    let pre: Vec<MatSpec> = c
        .tables
        .iter()
        .enumerate()
        .filter(|(_, tb)| tb.pre_width > 0)
        .map(|(t, tb)| {
            assert!(tb.next_pre.is_empty() || tb.next_pre.len() == tb.pre_width, "a proper preprocessed subset is refused by C3n");
            let pts = if tb.next_pre.is_empty() { vec![0] } else { vec![0, 1 + t] };
            MatSpec { kind: MatKind::Pre(t), table: t, width: tb.pre_width, cols: (0..tb.pre_width).collect(), log_height: tb.log_lde(lb), points: pts }
        })
        .collect();
    if !pre.is_empty() {
        inputs.push(("preprocessed".into(), TreeKind::Input(2), pre));
    }
    // Permutation: per table with lookups, the accumulator's coordinates and the fractions as two matrices.
    let mut perm = vec![];
    for (t, tb) in c.tables.iter().enumerate() {
        if !tb.has_lookups() {
            continue;
        }
        let w = 8 * tb.perm_width;
        let next: Vec<usize> = tb.next_perm.iter().flat_map(|&j| 8 * j..8 * j + 8).collect();
        let lh = tb.log_lde(lb);
        if next.is_empty() {
            perm.push(MatSpec { kind: MatKind::Perm(t, 0), table: t, width: w + rc, cols: (0..w).collect(), log_height: lh, points: vec![0] });
        } else if next.len() == w {
            perm.push(MatSpec { kind: MatKind::Perm(t, 0), table: t, width: w + rc, cols: (0..w).collect(), log_height: lh, points: vec![0, 1 + t] });
        } else {
            let rest: Vec<usize> = (0..w).filter(|x| !next.contains(x)).collect();
            perm.push(MatSpec { kind: MatKind::Perm(t, 0), table: t, width: next.len() + rc, cols: next, log_height: lh, points: vec![0, 1 + t] });
            perm.push(MatSpec { kind: MatKind::Perm(t, 1), table: t, width: rest.len() + rc, cols: rest, log_height: lh, points: vec![0] });
        }
    }
    if !perm.is_empty() {
        inputs.push(("permutation".into(), TreeKind::Input(3), perm));
    }
    let gbits = c.index_bits;
    let mut out = vec![];
    for (name, kind, mats) in inputs {
        let lh = mats.iter().map(|m| m.log_height).max().unwrap();
        let canonical = kind == TreeKind::Input(0);
        assert!(!canonical || lh == gbits, "the main tree holds the tallest table");
        let skip = gbits - lh;
        let start = if canonical {
            Start::Load
        } else if skip == 0 {
            Start::Xq
        } else {
            Start::Shift(skip)
        };
        out.push(build_tree(c, name, kind, mats, lh, 0, skip, if canonical { CAP_BITS } else { 0 }, start, canonical));
    }
    // FRI rounds: round r commits the codeword of height h_r as 2^(h_r - la_r) rows of 2^la_r values.
    let mut h = gbits;
    let mut skip = 0;
    for (r, &la) in c.fri_log_arities.iter().enumerate() {
        let lh = h - la;
        let mats = vec![MatSpec { kind: MatKind::Fri(r), table: usize::MAX, width: (1 << la) * 8, cols: vec![], log_height: lh, points: vec![] }];
        let start = if r == 0 { Start::Xq } else { Start::Chain(r) };
        out.push(build_tree(c, format!("fri_round{r}"), TreeKind::Fri(r), mats, lh, la, skip, CAP_BITS, start, false));
        skip += la;
        h = lh;
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn build_tree(c: &ChildSpec, name: String, kind: TreeKind, mats: Vec<MatSpec>, lh: usize, consume_lh: usize, skip: usize, cap_rows: usize, start: Start, canonical: bool) -> TreeSpec {
    assert!(lh >= CAP_BITS, "{name}: a tree lower than the cap is not built (its cap is its leaf layer)");
    let mc = lh - CAP_BITS;
    assert_eq!(skip + consume_lh + mc + CAP_BITS, c.index_bits, "{name}: every path ends its walk at bit index_bits - cap");
    // Leaf groups: matrices sorted tallest first (stable), one group per height (mmcs/mod.rs l. 672-690, 783-822).
    let mut heights: Vec<usize> = mats.iter().map(|m| m.log_height).collect::<BTreeSet<_>>().into_iter().rev().collect();
    heights.dedup();
    let groups: Vec<Group> = heights
        .iter()
        .map(|&h| {
            let gm: Vec<usize> = (0..mats.len()).filter(|&m| mats[m].log_height == h).collect();
            let leaf_len: usize = gm.iter().map(|&m| mats[m].width + c.salt).sum();
            let inject_after = lh - h;
            // A group injected at or above the cap layer would not be walked; a group injected after the last walked
            // compression would need the cap read on the injection row.
            assert!(inject_after == 0 || inject_after < mc, "{name}: group of height 2^{h} is injected at or above the last walked level");
            Group { mats: gm, log_height: h, leaf_len, lh_rows: leaf_len.div_ceil(8), partial: leaf_len % 8, inject_after }
        })
        .collect();
    // Layout: the injected groups' leaf rows, group 0's leaf rows (the path starts there), the nodes, the cap rows.
    let mut off = 0;
    let mut group_start = vec![0; groups.len()];
    for (k, g) in groups.iter().enumerate().skip(1) {
        group_start[k] = off;
        off += g.lh_rows;
    }
    group_start[0] = off;
    let path_start = off;
    off += groups[0].lh_rows;
    let mut nodes = vec![];
    for level in 0..mc {
        nodes.push((off, Node::Comp(level)));
        off += 1;
        for (k, g) in groups.iter().enumerate().skip(1) {
            if g.inject_after == level + 1 {
                nodes.push((off, Node::Inj(k)));
                off += 1;
            }
        }
    }
    let (cap_read, last_node) = *nodes.last().expect("at least one walked level");
    assert!(matches!(last_node, Node::Comp(_)), "{name}: the last walked node is a compression");
    off += cap_rows;
    let end = off - 1;
    TreeSpec { name, kind, mats, groups, log_height: lh, mc, consume_lh, skip, cap_rows, start, canonical, group_start, path_start, nodes, cap_read, end, block_len: off }
}

/// The native transcript of the child's verifier, as events, from the shape alone.
pub fn events(c: &ChildSpec, trees: &[TreeSpec]) -> (Vec<Ev>, Vec<Segment>, Vec<(String, usize, usize)>, usize) {
    events_with(c, trees, 1 << c.log_final_poly_len)
}

/// The same with a chosen number of final-polynomial coefficients (only a malicious variant chooses another).
pub fn events_with(c: &ChildSpec, trees: &[TreeSpec], final_coeffs: usize) -> (Vec<Ev>, Vec<Segment>, Vec<(String, usize, usize)>, usize) {
    let mut ev = vec![];
    let mut sg = vec![];
    let mut wit = 0usize;
    let mut wsg = vec![];
    let mut s;
    // The child's prefix (B1: as its configuration absorbs it; G1's was domain, verifier-key digest, PI198).
    for item in &c.prefix {
        match item {
            PrefixItem::Bytes(name, b) => {
                s = ev.len();
                bytes_events(&mut ev, b);
                seg(&mut sg, &ev, s, &format!("prefix.{name}"), "const");
            }
            PrefixItem::PubBytes(name, first, len) => {
                s = ev.len();
                ev.push(Ev::Abs(Src::Const(F::from_usize(*len))));
                seg(&mut sg, &ev, s, &format!("prefix.{name}_length"), "const");
                s = ev.len();
                for i in 0..*len {
                    ev.push(Ev::Abs(Src::Pub(first + i)));
                }
                seg(&mut sg, &ev, s, &format!("prefix.{name}"), "public");
            }
            PrefixItem::Fields(name, f) => {
                s = ev.len();
                for &v in f {
                    ev.push(Ev::Abs(Src::Const(v)));
                }
                seg(&mut sg, &ev, s, &format!("prefix.{name}"), "const");
            }
        }
    }
    s = ev.len();
    for &v in &c.seeds[0] {
        ev.push(Ev::Abs(Src::Const(v)));
    }
    seg(&mut sg, &ev, s, "batch.seed", "const");
    // Per-table degree bits of the extended trace (EF elements (bits, 0, ..., 0); transcript.rs l. 822-828).
    for (t, tb) in c.tables.iter().enumerate() {
        s = ev.len();
        ev.push(Ev::Abs(Src::Const(F::from_usize(tb.log_trace + 1))));
        for _ in 1..8 {
            ev.push(Ev::Abs(Src::Const(F::ZERO)));
        }
        seg(&mut sg, &ev, s, &format!("batch.degree_bits.table{t}"), "const");
    }
    let mut witness = |ev: &mut Vec<Ev>, sg: &mut Vec<Segment>, name: String, n: usize| {
        let s = ev.len();
        for _ in 0..n {
            ev.push(Ev::Abs(Src::Wit(wit)));
            wit += 1;
        }
        wsg.push((name.clone(), wit - n, n));
        seg(sg, ev, s, &name, "witness");
    };
    let caps = 1usize << CAP_BITS;
    let tree_named = |n: &str| trees.iter().position(|t| t.name == n);
    witness(&mut ev, &mut sg, "batch.main_commitment".into(), 8 * caps);
    for (t, tb) in c.tables.iter().enumerate() {
        if tb.public.is_empty() {
            continue;
        }
        s = ev.len();
        for &j in &tb.public {
            ev.push(Ev::Abs(Src::Pub(j)));
        }
        seg(&mut sg, &ev, s, &format!("batch.public_values.table{t}"), "public");
    }
    if tree_named("preprocessed").is_some() {
        s = ev.len();
        for d in &c.pre_cap {
            for &v in d {
                ev.push(Ev::Abs(Src::Const(v)));
            }
        }
        seg(&mut sg, &ev, s, "batch.preprocessed_commitment", "const");
    }
    let has_lookups = c.tables.iter().any(|t| t.has_lookups());
    if has_lookups {
        s = ev.len();
        for i in 0..8 {
            ev.push(Ev::Sample(Sq::LookupAlpha(i)));
        }
        seg(&mut sg, &ev, s, "batch.lookup_alpha", "sample");
        s = ev.len();
        for i in 0..8 {
            ev.push(Ev::Sample(Sq::LookupBeta(i)));
        }
        seg(&mut sg, &ev, s, "batch.lookup_beta", "sample");
        witness(&mut ev, &mut sg, "batch.permutation_commitment".into(), 8 * caps);
        for (t, tb) in c.tables.iter().enumerate() {
            if tb.has_lookups() {
                witness(&mut ev, &mut sg, format!("batch.lookup_terminal.table{t}"), 8);
            }
        }
    }
    s = ev.len();
    for i in 0..8 {
        ev.push(Ev::Sample(Sq::Alpha(i)));
    }
    seg(&mut sg, &ev, s, "batch.constraint_challenge", "sample");
    witness(&mut ev, &mut sg, "batch.quotient_random_commitment".into(), 8 * caps);
    s = ev.len();
    for i in 0..8 {
        ev.push(Ev::Sample(Sq::Zeta(i)));
    }
    seg(&mut sg, &ev, s, "batch.zeta", "sample");
    s = ev.len();
    for &v in &c.seeds[1] {
        ev.push(Ev::Abs(Src::Const(v)));
    }
    seg(&mut sg, &ev, s, "pcs.seed", "const");
    for tree in trees.iter().filter(|t| matches!(t.kind, TreeKind::Input(_))) {
        for (m, mat) in tree.mats.iter().enumerate() {
            for &pt in &mat.points {
                witness(&mut ev, &mut sg, format!("pcs.claims.{}.m{m}.{}", tree.name, pt_name(pt)), 8 * mat.width);
            }
        }
    }
    s = ev.len();
    for i in 0..8 {
        ev.push(Ev::Sample(Sq::PcsAlpha(i)));
    }
    seg(&mut sg, &ev, s, "pcs.alpha", "sample");
    s = ev.len();
    for &v in &c.seeds[2] {
        ev.push(Ev::Abs(Src::Const(v)));
    }
    seg(&mut sg, &ev, s, "fri.seed", "const");
    for (r, _) in c.fri_log_arities.iter().enumerate() {
        witness(&mut ev, &mut sg, format!("fri.round{r}.commitment"), 8 * caps);
        s = ev.len();
        for i in 0..8 {
            ev.push(Ev::Sample(Sq::Beta(r, i)));
        }
        seg(&mut sg, &ev, s, &format!("fri.round{r}.beta"), "sample");
    }
    witness(&mut ev, &mut sg, "fri.final_poly".into(), 8 * final_coeffs);
    s = ev.len();
    for q in 0..c.num_queries {
        ev.push(Ev::Sample(Sq::Query(q)));
    }
    seg(&mut sg, &ev, s, "fri.query_indices", "sample");
    (ev, sg, wsg, wit)
}

/// The native duplex challenger's rows for an event list (K1's, unchanged).
pub fn simulate(events: &[Ev]) -> (Vec<TRow>, Vec<(usize, usize)>) {
    let mut rows: Vec<TRow> = vec![];
    let mut buf: Vec<(usize, Src)> = vec![];
    let mut out: Vec<(usize, usize)> = vec![];
    let mut pos = vec![(usize::MAX, usize::MAX); events.len()];
    let duplex = |rows: &mut Vec<TRow>, buf: &mut Vec<(usize, Src)>, out: &mut Vec<(usize, usize)>, pos: &mut Vec<(usize, usize)>| {
        let r = rows.len();
        let k = buf.len();
        let mut lanes = [None; 8];
        for (l, &(e, s)) in buf.iter().enumerate() {
            lanes[l] = Some(s);
            pos[e] = (r, l);
        }
        if k > 0 {
            for lane in lanes.iter_mut().skip(k) {
                *lane = Some(Src::Const(F::ZERO));
            }
        }
        rows.push(TRow { k, lanes, samples: vec![] });
        buf.clear();
        out.clear();
        out.extend((0..8).map(|l| (r, l)));
    };
    for (e, ev) in events.iter().enumerate() {
        match *ev {
            Ev::Abs(s) => {
                out.clear();
                buf.push((e, s));
                if buf.len() == 8 {
                    duplex(&mut rows, &mut buf, &mut out, &mut pos);
                }
            }
            Ev::Sample(sq) => {
                if !buf.is_empty() || out.is_empty() {
                    duplex(&mut rows, &mut buf, &mut out, &mut pos);
                }
                let (r, l) = out.pop().expect("output");
                rows[r].samples.push((l, sq));
                pos[e] = (r, l);
            }
        }
    }
    assert!(buf.is_empty(), "the transcript must end with a sample");
    (rows, pos)
}

/// The claimed evaluations in p3-fri's order (batch, matrix, point; verifier.rs l. 1280-1298) with their stream
/// positions and ladder offsets per log height (l. 1300-1322), their runs per (height, point), and the DEEP chains.
pub fn deep_layout(trees: &[TreeSpec], salt: usize, join: bool) -> (Vec<ClaimBlock>, Vec<ClaimRun>, Vec<DeepChain>) {
    let mut blocks = vec![];
    let mut claim = 0usize;
    let mut ladder: BTreeMap<usize, usize> = BTreeMap::new();
    for (t, tree) in trees.iter().enumerate() {
        if !matches!(tree.kind, TreeKind::Input(_)) {
            continue;
        }
        for (m, mat) in tree.mats.iter().enumerate() {
            for &pt in &mat.points {
                let off = ladder.entry(mat.log_height).or_insert(0);
                blocks.push(ClaimBlock { tree: t, matrix: m, point: pt, width: mat.width, first_claim: claim, ladder_off: *off, log_height: mat.log_height });
                *off += mat.width;
                claim += mat.width;
            }
        }
    }
    let mut runs: Vec<ClaimRun> = vec![];
    for b in &blocks {
        if let Some(r) = runs.last_mut() {
            if r.point == b.point && r.log_height == b.log_height && r.first_claim + r.len == b.first_claim && r.ladder_off + r.len == b.ladder_off {
                r.len += b.width;
                continue;
            }
        }
        runs.push(ClaimRun { log_height: b.log_height, point: b.point, first_claim: b.first_claim, len: b.width, ladder_off: b.ladder_off });
    }
    // One chain per matrix, on its group's leaf rows (the salts of 8 elements keep two matrices off one row).
    let mut chains: Vec<DeepChain> = vec![];
    for (t, tree) in trees.iter().enumerate() {
        if !matches!(tree.kind, TreeKind::Input(_)) {
            continue;
        }
        for (k, g) in tree.groups.iter().enumerate() {
            let mut start = 0usize;
            for &m in &g.mats {
                let w = tree.mats[m].width;
                let mut rows: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
                for e in start..start + w {
                    rows.entry(e / 8).or_default().push(e % 8);
                }
                let value_rows: Vec<(usize, Vec<usize>)> = rows.into_iter().collect();
                for wnd in value_rows.windows(2) {
                    assert_eq!(wnd[1].0, wnd[0].0 + 1, "a matrix's values occupy consecutive leaf rows");
                }
                let offsets: Vec<(usize, usize)> = tree.mats[m]
                    .points
                    .iter()
                    .map(|&pt| (pt, blocks.iter().find(|b| b.tree == t && b.matrix == m && b.point == pt).unwrap().ladder_off))
                    .collect();
                let shift = start % 8;
                assert!(offsets.iter().all(|&(_, o)| o >= shift), "a matrix's ladder offset is at least its first lane");
                // B1: join this matrix to the previous chain of the group when both are opened at one and the same
                // point, the ladder continues (offset = previous offset + previous width), the previous values end on a
                // row boundary, the salt fills exactly the next row, and this matrix starts on the row after it.
                let joinable = join && salt == 8 && offsets.len() == 1 && shift == 0 && start % 8 == 0 && chains.last().is_some_and(|prev: &DeepChain| {
                    if prev.tree != t || prev.group != k || prev.offsets.len() != 1 || prev.offsets[0].0 != offsets[0].0 {
                        return false;
                    }
                    let pm = *prev.matrices.last().unwrap();
                    let pw = tree.mats[pm].width;
                    assert!(start >= salt + pw, "the previous matrix of the group precedes this one");
                    let pstart = start - salt - pw;
                    (pstart + pw) % 8 == 0 && prev.value_rows.last().unwrap().0 + 2 == value_rows[0].0
                        && blocks.iter().find(|b| b.tree == t && b.matrix == pm && b.point == offsets[0].0).unwrap().ladder_off + pw == offsets[0].1
                });
                if joinable {
                    let prev = chains.last_mut().unwrap();
                    let pass = prev.value_rows.last().unwrap().0 + 1;
                    prev.pass_rows.push(pass);
                    prev.value_rows.extend(value_rows);
                    prev.matrices.push(m);
                } else {
                    chains.push(DeepChain { tree: t, matrix: m, matrices: vec![m], group: k, value_rows, pass_rows: vec![], shift, offsets, log_height: tree.mats[m].log_height });
                }
                start += w + salt;
            }
        }
    }
    // Two chains never share a row (a salt of 8 elements separates them); a pass row holds no value.
    for (t, tree) in trees.iter().enumerate() {
        for k in 0..tree.groups.len() {
            let mut seen = BTreeSet::new();
            for ch in chains.iter().filter(|c| c.tree == t && c.group == k) {
                for r in ch.value_rows.iter().map(|(r, _)| r).chain(&ch.pass_rows) {
                    assert!(seen.insert(*r), "two chains on one leaf row");
                }
            }
        }
    }
    (blocks, runs, chains)
}

struct Cols {
    n: usize,
    names: Vec<String>,
    cols: Vec<Vec<F>>,
}
impl Cols {
    fn add(&mut self, name: String) -> usize {
        self.names.push(name);
        self.cols.push(vec![F::ZERO; self.n]);
        self.cols.len() - 1
    }
}

fn ins(op: Op, r: Option<Val>, a: Option<Val>, b: Option<Val>, c: Option<Val>, role: &'static str, q: Option<usize>, round: Option<usize>) -> Instr {
    Instr { op, a, b, c, r, kappa: F::ZERO, kappa_x: F::ZERO, role, query: q, round, lane: 0 }
}
fn lin(r: Val, a: Val, b: Val, kappa: F, role: &'static str, q: Option<usize>) -> Instr {
    let mut i = ins(Op::Lin, Some(r), Some(a), Some(b), None, role, q, None);
    i.kappa = kappa;
    i
}

/// sum_k AP(off_k) * val_k as a chain of MUL/MAC instructions (a term at offset 0 is the value itself); returns the
/// value holding the sum.
fn weighted_sum(prog: &mut Vec<Instr>, terms: &[(usize, Val)], part: &dyn Fn(usize) -> Val, last: Val, role: &'static str, q: Option<usize>) -> Val {
    let mut terms = terms.to_vec();
    terms.sort_by_key(|t| t.0);
    let n = terms.len();
    assert!(n > 0);
    let name = |k: usize| if k + 1 == n { last } else { part(k) };
    let (off0, v0) = terms[0];
    let mut acc = if off0 == 0 {
        if n == 1 {
            return v0;
        }
        v0
    } else {
        let r = name(0);
        prog.push(ins(Op::Mul, Some(r), Some(Val::AP(off0)), Some(v0), None, role, q, None));
        r
    };
    for (k, &(off, v)) in terms.iter().enumerate().skip(1) {
        let r = name(k);
        prog.push(ins(Op::Mac, Some(r), Some(Val::AP(off)), Some(v), Some(acc), role, q, None));
        acc = r;
    }
    acc
}

/// The rows of a tree's path at query q: (absolute row, role).
impl TreeSpec {
    pub fn comp_rows(&self) -> Vec<usize> {
        self.nodes.iter().filter(|(_, n)| matches!(n, Node::Comp(_))).map(|(o, _)| *o).collect()
    }
    /// The rows (offsets) consuming an index bit, in bit order: FRI coset bits on leaf rows, compressions, cap rows.
    pub fn bit_rows(&self) -> Vec<usize> {
        let mut v: Vec<usize> = (0..self.consume_lh).map(|j| self.path_start + j).collect();
        v.extend(self.comp_rows());
        v.extend(self.cap_read + 1..self.cap_read + 1 + self.cap_rows);
        v
    }
    /// The rows (offsets) consuming one of the tree's own index bits (the coset point's twiddles), in order.
    pub fn tree_bit_rows(&self) -> Vec<usize> {
        let mut v = self.comp_rows();
        v.extend(self.cap_read + 1..self.cap_read + 1 + self.cap_rows);
        v
    }
}

impl Schedule {
    /// The schedule with the DEEP chains joined (B1's lever) in the smallest table that holds it.
    pub fn build(c: &ChildSpec) -> Schedule {
        Self::build_opts(c, true)
    }
    /// The schedule in the smallest power-of-two table that holds K1's rows (transcript and query blocks) and the ALU
    /// program with its reserved rows (B1: the ALU program may run past K1's rows; G1's table was sized by K1's rows).
    pub fn build_opts(c: &ChildSpec, join: bool) -> Schedule {
        let trees = trees(c);
        let t_rows = simulate(&events(c, &trees).0).0.len();
        let block_rows: usize = trees.iter().map(|t| t.block_len).sum();
        let used_rows = t_rows + c.num_queries * block_rows;
        let mut log_n = (used_rows + 1).next_power_of_two().trailing_zeros() as usize;
        loop {
            match Self::build_with(c, join, log_n) {
                Ok(s) => return s,
                Err(_) => log_n += 1,
            }
        }
    }
    /// The schedule in a table of 2^log_n rows; Err(rows needed) when the ALU program does not fit.
    pub fn build_with(c: &ChildSpec, join: bool, log_n: usize) -> Result<Schedule, usize> {
        let trees = trees(c);
        let (events, segments, wit_segments, wit_len) = events(c, &trees);
        let (trows, ev_pos) = simulate(&events);
        let rounds = c.fri_log_arities.len();
        assert_eq!(c.index_bits, LOW_BITS, "the index lane is built for {LOW_BITS}-bit query indices");
        assert!(c.fri_log_arities.iter().all(|&a| a == 1 || a == 2), "K2 builds butterflies for arity 2 and 4");
        let q = c.num_queries;
        let t_rows = trows.len();
        let block_rows: usize = trees.iter().map(|t| t.block_len).sum();
        let used_rows = t_rows + q * block_rows;
        let n = 1usize << log_n;
        assert!(used_rows < n, "K1's rows do not fit 2^{log_n}");
        assert!(trows[0].k == 8, "the first duplexing must absorb a full rate");
        let heights = c.input_log_heights();
        let top_h = heights[0];
        assert_eq!(top_h, c.index_bits);
        let canon = trees.iter().position(|t| t.canonical).unwrap();
        let (claim_blocks, claim_runs, chains) = deep_layout(&trees, c.salt, join);
        let mut pc = Cols { n, names: vec![], cols: vec![] };
        let cf: [usize; 8] = core::array::from_fn(|l| pc.add(format!("const_flag.lane{l}")));
        let cv: [usize; 8] = core::array::from_fn(|l| pc.add(format!("const_value.lane{l}")));
        let kc = pc.add("chain_capacity_into_next".into());
        let tagc = pc.add("length_tag_of_next".into());
        let kr: [usize; 8] = core::array::from_fn(|l| pc.add(format!("keep_rate_into_next.lane{l}")));
        let ivf = pc.add("leaf_hash_start".into());
        let lnk = pc.add("link_into_next_compression".into());
        let cons = pc.add("consume_index_bit".into());
        let path_t = pc.add("path_continues".into());
        let start = pc.add("path_start".into());
        let pend = pc.add("path_end".into());
        let pend_canon = pc.add("path_end_canonical_check".into());
        let lsel: [usize; 8] = core::array::from_fn(|k| pc.add(format!("load_lane_select.coord{k}")));
        let xs = pc.add("base_x_start".into());
        let x0 = pc.add("base_x_start_value".into());
        let xp = pc.add("base_x_continues".into());
        let xc = pc.add("base_x_twiddle_minus_one".into());
        let vs = pc.add("v_is_coset_point".into());
        let xce = pc.add("v_coset_point_last_twiddle_minus_one".into());
        let vacc = pc.add("v_is_acc".into());
        let vsig = pc.add("v_is_half_minus_bit".into());
        let op: [usize; 8] = core::array::from_fn(|k| pc.add(format!("alu_op.{}", OPS[k].name())));
        let kappa = pc.add("alu_immediate".into());
        let ctrl: [usize; NCTRL] = core::array::from_fn(|k| pc.add(format!("schedule.{}", CTRL_NAMES[k])));
        let dv = pc.add("deep_value_row".into());
        let dc = pc.add("deep_continues_into_next".into());
        let dl: [usize; 8] = core::array::from_fn(|l| pc.add(format!("deep_value_lane.lane{l}")));
        let dp = pc.add("deep_pass_row".into());
        let dw = pc.add("deep_write_row".into());
        let cs: [usize; 8] = core::array::from_fn(|l| pc.add(format!("claim_write_start_lane.lane{l}")));
        let bind: [usize; 3] = ["alpha_and_alpha2", "alpha3", "alpha4"].map(|nm| pc.add(format!("deep_bind_power.{nm}")));
        let kx = pc.add("alu_immediate_x".into());
        let unp: [usize; 8] = core::array::from_fn(|k| pc.add(format!("alu_unpack_lane.coord{k}")));
        let inj = pc.add("merkle_injection_row".into());
        let capr = pc.add("merkle_cap_read_row".into());
        let capw = pc.add("cap_entry_write_row_free_multiplicity".into());
        let hiw = pc.add("index_high_part_write_row".into());
        // ---- transcript rows (K1) ----
        let mut pub_terms: Vec<Vec<(usize, usize)>> = vec![vec![]; 8];
        for (r, row) in trows.iter().enumerate() {
            if r > 0 {
                pc.cols[kc][r - 1] = F::ONE;
                pc.cols[tagc][r - 1] = F::from_usize(row.k);
                if row.k == 0 {
                    for l in 0..8 {
                        pc.cols[kr[l]][r - 1] = F::ONE;
                    }
                }
            }
            let mut sel = None;
            for l in 0..8 {
                match row.lanes[l] {
                    Some(Src::Const(v)) => {
                        pc.cols[cf[l]][r] = F::ONE;
                        pc.cols[cv[l]][r] = v;
                    }
                    Some(Src::Pub(j)) => {
                        let s = *sel.get_or_insert_with(|| pc.add(format!("public_row{r}")));
                        pc.cols[s][r] = F::ONE;
                        pub_terms[l].push((s, j));
                    }
                    _ => {}
                }
            }
        }
        // The rows of the challenges (an extension-field challenge's coefficient i is output lane 7 - i of one row),
        // of the final-polynomial coefficients and of the query elements.
        let mut beta_row = vec![usize::MAX; rounds];
        let mut q_pos = vec![(usize::MAX, usize::MAX); q];
        let (mut alpha_row, mut zeta_row, mut pcs_alpha_row, mut la_row, mut lb_row) = (usize::MAX, usize::MAX, usize::MAX, usize::MAX, usize::MAX);
        let one_row = |slot: &mut usize, row: usize, lane: usize, i: usize| {
            assert_eq!(lane, 7 - i, "challenge coefficient i is output lane 7 - i");
            assert!(*slot == usize::MAX || *slot == row, "a challenge spans two rows");
            *slot = row;
        };
        for (e, ev) in events.iter().enumerate() {
            if let Ev::Sample(sq) = ev {
                let (row, lane) = ev_pos[e];
                match *sq {
                    Sq::Beta(r, i) => one_row(&mut beta_row[r], row, lane, i),
                    Sq::Alpha(i) => one_row(&mut alpha_row, row, lane, i),
                    Sq::Zeta(i) => one_row(&mut zeta_row, row, lane, i),
                    Sq::PcsAlpha(i) => one_row(&mut pcs_alpha_row, row, lane, i),
                    Sq::LookupAlpha(i) => one_row(&mut la_row, row, lane, i),
                    Sq::LookupBeta(i) => one_row(&mut lb_row, row, lane, i),
                    Sq::Query(qq) => q_pos[qq] = (row, lane),
                }
            }
        }
        let mut wit_pos = vec![(usize::MAX, usize::MAX); wit_len];
        for (e, ev) in events.iter().enumerate() {
            if let Ev::Abs(Src::Wit(i)) = ev {
                wit_pos[*i] = ev_pos[e];
            }
        }
        let seg_of = |name: &str| wit_segments.iter().find(|w| w.0 == name).cloned().unwrap_or_else(|| panic!("segment {name}"));
        let (_, fp_first, fp_len) = seg_of("fri.final_poly");
        let ncoef = fp_len / 8;
        let mut coeff_row = vec![usize::MAX; ncoef];
        for i in fp_first..fp_first + fp_len {
            let k = (i - fp_first) / 8;
            let (row, lane) = wit_pos[i];
            assert_eq!(lane, (i - fp_first) % 8, "a final-polynomial coefficient fills one row's lanes 0..8");
            assert!(coeff_row[k] == usize::MAX || coeff_row[k] == row);
            coeff_row[k] = row;
        }
        // An 8-element value absorbed from a stream position: its coordinate 0 at (row, s), coordinate j at lane s + j
        // of that row or lane s + j - 8 of the next.
        let pos8 = |positions: &dyn Fn(usize) -> (usize, usize)| -> ClaimPos {
            let (row, lane) = positions(0);
            for j in 0..8 {
                let want = if lane + j < 8 { (row, lane + j) } else { (row + 1, lane + j - 8) };
                assert_eq!(positions(j), want, "an 8-element value is not where its write row reads it");
            }
            ClaimPos { row, lane }
        };
        // Claims: the PCS's claims stream (the segments "pcs.claims.*" in order).
        let n_claims: usize = claim_blocks.iter().map(|b| b.width).sum();
        let claim_wit: Vec<usize> = wit_segments.iter().filter(|w| w.0.starts_with("pcs.claims.")).flat_map(|w| w.1..w.1 + w.2).collect();
        assert_eq!(claim_wit.len(), 8 * n_claims);
        let claim_pos: Vec<ClaimPos> = (0..n_claims).map(|k| pos8(&|j| wit_pos[claim_wit[8 * k + j]])).collect();
        // Cap entries: the witness caps and the pinned preprocessed cap (constants).
        let caps = 1usize << CAP_BITS;
        let mut cap_pos: BTreeMap<(usize, usize), ClaimPos> = BTreeMap::new();
        for (ti, tree) in trees.iter().enumerate() {
            let segname = match tree.kind {
                TreeKind::Input(0) => "batch.main_commitment".to_string(),
                TreeKind::Input(1) => "batch.quotient_random_commitment".to_string(),
                TreeKind::Input(2) => "batch.preprocessed_commitment".to_string(),
                TreeKind::Input(3) => "batch.permutation_commitment".to_string(),
                TreeKind::Fri(r) => format!("fri.round{r}.commitment"),
                TreeKind::Input(_) => unreachable!(),
            };
            if tree.kind == TreeKind::Input(2) {
                let sgm = segments.iter().find(|g| g.name == segname).unwrap();
                assert_eq!(sgm.len, 8 * caps);
                for j in 0..caps {
                    cap_pos.insert((ti, j), pos8(&|k| ev_pos[sgm.first_event + 8 * j + k]));
                }
            } else {
                let (_, first, len) = seg_of(&segname);
                assert_eq!(len, 8 * caps);
                for j in 0..caps {
                    cap_pos.insert((ti, j), pos8(&|k| wit_pos[first + 8 * j + k]));
                }
            }
        }
        let mut terminal_pos: BTreeMap<usize, ClaimPos> = BTreeMap::new();
        for (t, tb) in c.tables.iter().enumerate() {
            if tb.has_lookups() {
                let (_, first, _) = seg_of(&format!("batch.lookup_terminal.table{t}"));
                terminal_pos.insert(t, pos8(&|k| wit_pos[first + k]));
            }
        }
        // ---- query blocks and the paths ----
        let mut block_start = vec![];
        let mut row = t_rows;
        for _ in 0..q {
            let mut st = vec![];
            for t in &trees {
                st.push(row);
                row += t.block_len;
            }
            block_start.push(st);
        }
        assert_eq!(row, used_rows);
        let mut w2port: Vec<(usize, Val)> = vec![];
        let mut shifts: BTreeSet<usize> = BTreeSet::new();
        for t in &trees {
            if let Start::Shift(d) = t.start {
                shifts.insert(d);
            }
        }
        for qq in 0..q {
            for (ti, t) in trees.iter().enumerate() {
                let b0 = block_start[qq][ti];
                // Every group's leaf-hash rows: from the zero state, the sponge chained, the partial last block kept.
                for (k, g) in t.groups.iter().enumerate() {
                    let s = b0 + t.group_start[k];
                    pc.cols[ivf][s] = F::ONE;
                    for j in 1..g.lh_rows {
                        pc.cols[kc][s + j - 1] = F::ONE;
                    }
                    if g.partial > 0 {
                        for l in g.partial..8 {
                            pc.cols[kr[l]][s + g.lh_rows - 2] = F::ONE;
                        }
                    }
                }
                let ps = b0 + t.path_start;
                pc.cols[start][ps] = F::ONE;
                for j in 0..t.consume_lh {
                    pc.cols[cons][ps + j] = F::ONE;
                }
                // Nodes: a compression consumes a bit and links from the previous node (or group 0's last leaf row);
                // an injection consumes none and links on the left (BIT = 0, `merkle.inject`).
                for &(o, nd) in &t.nodes {
                    let r = b0 + o;
                    pc.cols[lnk][r - 1] = F::ONE;
                    match nd {
                        Node::Comp(_) => pc.cols[cons][r] = F::ONE,
                        Node::Inj(_) => pc.cols[inj][r] = F::ONE,
                    }
                }
                pc.cols[capr][b0 + t.cap_read] = F::ONE;
                for j in 0..t.cap_rows {
                    pc.cols[cons][b0 + t.cap_read + 1 + j] = F::ONE;
                }
                let end = b0 + t.end;
                for r in ps..end {
                    pc.cols[path_t][r] = F::ONE;
                }
                if t.cap_rows > 0 {
                    pc.cols[pend][end] = F::ONE;
                    if t.canonical {
                        pc.cols[pend_canon][end] = F::ONE;
                        pc.cols[hiw][end] = F::ONE;
                        w2port.push((end, Val::Hi(qq)));
                    }
                    // The base lane: the canonical tree's x = g prod_i c_i^{bit_i} over the index bits
                    // (p3-fri verifier.rs l. 1244-1248, g = F::GENERATOR); a FRI round's coset point
                    // s = prod_i c_i^{bit_i} over its own index bits, c_i = w_{2^(h+la)}^{2^(h-1-i)}
                    // (two_adic_pcs.rs l. 173-174).
                    let h = t.log_height + t.consume_lh;
                    let lh = t.log_height;
                    let tw: Vec<F> = (0..lh).map(|i| F::two_adic_generator(h).exp_u64(1u64 << (lh - 1 - i))).collect();
                    let bits = t.tree_bit_rows();
                    assert_eq!(bits.len(), lh);
                    pc.cols[xs][ps] = F::ONE;
                    pc.cols[x0][ps] = if t.canonical { F::GENERATOR } else { F::ONE };
                    for r in ps..end {
                        pc.cols[xp][r] = F::ONE;
                    }
                    for (i, &o) in bits.iter().enumerate().take(lh - 1) {
                        pc.cols[xc][b0 + o] = tw[i] - F::ONE;
                    }
                    assert_eq!(b0 + bits[lh - 1], end);
                    pc.cols[vs][end] = F::ONE;
                    pc.cols[xce][end] = tw[lh - 1] - F::ONE;
                }
            }
        }
        // ---- the DEEP lane's flags and write rows; the claims', caps' and terminals' write rows ----
        for qq in 0..q {
            for (ci, ch) in chains.iter().enumerate() {
                let t = &trees[ch.tree];
                let s0 = block_start[qq][ch.tree] + t.group_start[ch.group];
                let last = ch.value_rows.len() - 1;
                for (i, (r, lanes)) in ch.value_rows.iter().enumerate() {
                    pc.cols[dv][s0 + r] = F::ONE;
                    if i < last {
                        pc.cols[dc][s0 + r] = F::ONE;
                    }
                    for &l in lanes {
                        pc.cols[dl[l]][s0 + r] = F::ONE;
                    }
                }
                // B1: a salt row between joined matrices passes the chain's sum through (D = D').
                for &r in &ch.pass_rows {
                    pc.cols[dp][s0 + r] = F::ONE;
                }
                let wr = s0 + ch.value_rows[0].0;
                pc.cols[dw][wr] = F::ONE;
                w2port.push((wr, Val::SD(qq, ci)));
            }
        }
        for (k, p) in claim_pos.iter().enumerate() {
            pc.cols[cs[p.lane]][p.row] = F::ONE;
            w2port.push((p.row, Val::Claim(k)));
        }
        for (&(ti, j), p) in &cap_pos {
            pc.cols[cs[p.lane]][p.row] = F::ONE;
            pc.cols[capw][p.row] = F::ONE;
            w2port.push((p.row, Val::Cap(ti, j)));
        }
        for (&t, p) in &terminal_pos {
            pc.cols[cs[p.lane]][p.row] = F::ONE;
            w2port.push((p.row, Val::Terminal(t)));
        }
        {
            let mut seen = BTreeSet::new();
            for (r, v) in &w2port {
                assert!(seen.insert(*r), "two W2 values on row {r} ({v:?})");
            }
        }
        // ---- the ALU program: constants ----
        let mut prog: Vec<Instr> = vec![];
        let mut consts: Vec<(&'static str, F)> = vec![];
        let konst = |prog: &mut Vec<Instr>, consts: &mut Vec<(&'static str, F)>, name: &'static str, v: F| -> Val {
            let id = consts.len();
            consts.push((name, v));
            let mut k = ins(Op::Const, Some(Val::Const(id)), None, None, None, "const", None, None);
            k.kappa = v;
            prog.push(k);
            Val::Const(id)
        };
        let k_w4inv = konst(&mut prog, &mut consts, "omega_4^-1", F::two_adic_generator(2).inverse());
        let k_two = konst(&mut prog, &mut consts, "2", F::TWO);
        // ---- K2: FRI with roll-ins ----
        for (r, &la) in c.fri_log_arities.iter().enumerate() {
            if la == 2 {
                prog.push(ins(Op::Mul, Some(Val::Beta2(r)), Some(Val::Beta(r)), Some(Val::Beta(r)), None, "fri.beta_power", None, Some(r)));
                prog.push(ins(Op::Mul, Some(Val::Beta2x2(r)), Some(Val::Beta2(r)), Some(k_two), None, "fri.beta_power", None, Some(r)));
            }
        }
        // The roll-ins: after round r the folded height is h_{r+1}; an input of that height is rolled in with
        // beta_r^(2^la_r) (verifier.rs l. 1035-1046; fold_schedule makes every input height a round boundary).
        let mut rollins: BTreeMap<usize, usize> = BTreeMap::new();
        {
            let mut h = top_h;
            for (r, &la) in c.fri_log_arities.iter().enumerate() {
                h -= la;
                if heights.contains(&h) {
                    rollins.insert(r, h);
                }
            }
            assert_eq!(rollins.len(), heights.len() - 1, "every lower input height is rolled in");
        }
        for (&r, _) in &rollins {
            let la = c.fri_log_arities[r];
            if la == 2 {
                prog.push(ins(Op::Mul, Some(Val::BetaPow(r)), Some(Val::Beta2(r)), Some(Val::Beta2(r)), None, "fri.rollin_power", None, Some(r)));
            } else {
                prog.push(ins(Op::Mul, Some(Val::BetaPow(r)), Some(Val::Beta(r)), Some(Val::Beta(r)), None, "fri.rollin_power", None, Some(r)));
            }
        }
        let last = rounds - 1;
        let ro_last = |hz: &[(usize, usize)], h: usize| hz.iter().filter(|x| x.0 == h).count() - 1;
        // The (height, point) pairs (every matrix opened at zeta; the next-row matrices at their table's zeta * g).
        let mut hz: Vec<(usize, usize)> = vec![];
        for b in &claim_blocks {
            if !hz.contains(&(b.log_height, b.point)) {
                hz.push((b.log_height, b.point));
            }
        }
        hz.sort_by_key(|&(h, p)| (std::cmp::Reverse(h), p));
        for qq in 0..q {
            let (sq, sr) = (Some(qq), |r: usize| Some(r));
            for (r, &la) in c.fri_log_arities.iter().enumerate() {
                let e = |j: usize| Some(Val::E(qq, r, j));
                prog.push(ins(Op::Inv2, Some(Val::H(qq, r)), Some(Val::S(qq, r)), None, None, "fri.inverse", sq, sr(r)));
                // The value the selected coset value must equal: the previous fold, plus the roll-in after it.
                let prev = if r >= 1 {
                    match rollins.get(&(r - 1)) {
                        Some(&h) => {
                            let ro = Val::RO(qq, h, ro_last(&hz, h));
                            prog.push(ins(Op::Mac, Some(Val::UR(qq, r)), Some(Val::BetaPow(r - 1)), Some(ro), Some(Val::U(qq, r - 1)), "fri.rollin_add", sq, sr(r)));
                            Some(Val::UR(qq, r))
                        }
                        None => Some(Val::U(qq, r - 1)),
                    }
                } else {
                    None
                };
                if la == 2 {
                    prog.push(ins(Op::Mul, Some(Val::G(qq, r, 0)), Some(Val::Beta(r)), Some(Val::H(qq, r)), None, "fri.twiddle", sq, sr(r)));
                    prog.push(ins(Op::Mul, Some(Val::G(qq, r, 1)), Some(Val::G(qq, r, 0)), Some(k_w4inv), None, "fri.twiddle", sq, sr(r)));
                    prog.push(ins(Op::Mul, Some(Val::HH(qq, r)), Some(Val::H(qq, r)), Some(Val::H(qq, r)), None, "fri.twiddle", sq, sr(r)));
                    prog.push(ins(Op::Mul, Some(Val::G2(qq, r)), Some(Val::Beta2x2(r)), Some(Val::HH(qq, r)), None, "fri.twiddle", sq, sr(r)));
                    prog.push(ins(Op::Bfly, Some(Val::Fold(qq, r, 0)), e(0), e(1), Some(Val::G(qq, r, 0)), "fri.fold", sq, sr(r)));
                    prog.push(ins(Op::Bfly, Some(Val::Fold(qq, r, 1)), e(2), e(3), Some(Val::G(qq, r, 1)), "fri.fold", sq, sr(r)));
                    prog.push(ins(Op::Bfly, Some(Val::U(qq, r)), Some(Val::Fold(qq, r, 0)), Some(Val::Fold(qq, r, 1)), Some(Val::G2(qq, r)), "fri.fold", sq, sr(r)));
                    if let Some(pv) = prev {
                        prog.push(ins(Op::Bfly, Some(Val::Sel(qq, r, 0)), e(0), e(1), Some(Val::Sigma(qq, r, 0)), "fri.select", sq, sr(r)));
                        prog.push(ins(Op::Bfly, Some(Val::Sel(qq, r, 1)), e(2), e(3), Some(Val::Sigma(qq, r, 0)), "fri.select", sq, sr(r)));
                        prog.push(ins(Op::Bfly, Some(Val::M(qq, r)), Some(Val::Sel(qq, r, 0)), Some(Val::Sel(qq, r, 1)), Some(Val::Sigma(qq, r, 1)), "fri.select", sq, sr(r)));
                        prog.push(ins(Op::Eq, None, Some(Val::M(qq, r)), Some(pv), None, "fri.rollin", sq, sr(r)));
                    }
                } else {
                    prog.push(ins(Op::Mul, Some(Val::G(qq, r, 0)), Some(Val::Beta(r)), Some(Val::H(qq, r)), None, "fri.twiddle", sq, sr(r)));
                    prog.push(ins(Op::Bfly, Some(Val::U(qq, r)), e(0), e(1), Some(Val::G(qq, r, 0)), "fri.fold", sq, sr(r)));
                    if let Some(pv) = prev {
                        prog.push(ins(Op::Bfly, Some(Val::M(qq, r)), e(0), e(1), Some(Val::Sigma(qq, r, 0)), "fri.select", sq, sr(r)));
                        prog.push(ins(Op::Eq, None, Some(Val::M(qq, r)), Some(pv), None, "fri.rollin", sq, sr(r)));
                    }
                }
            }
            assert!(!rollins.contains_key(&last), "a roll-in at the final height is not built (no input height at the final height in this child)");
            // B1: a constant final polynomial needs no final point (its value is the constant everywhere).
            if ncoef > 1 && c.fri_log_arities[last] == 1 {
                prog.push(ins(Op::Mul, Some(Val::XF(qq)), Some(Val::S(qq, last)), Some(Val::S(qq, last)), None, "fri.final_point", sq, None));
            } else if ncoef > 1 {
                prog.push(ins(Op::Mul, Some(Val::X2(qq)), Some(Val::S(qq, last)), Some(Val::S(qq, last)), None, "fri.final_point", sq, None));
                prog.push(ins(Op::Mul, Some(Val::XF(qq)), Some(Val::X2(qq)), Some(Val::X2(qq)), None, "fri.final_point", sq, None));
            }
            if ncoef == 1 {
                prog.push(ins(Op::Eq, None, Some(Val::Coeff(0)), Some(Val::U(qq, last)), None, "fri.final", sq, None));
            } else {
                prog.push(ins(Op::Mac, Some(Val::T(qq, ncoef - 2)), Some(Val::Coeff(ncoef - 1)), Some(Val::XF(qq)), Some(Val::Coeff(ncoef - 2)), "fri.final_horner", sq, None));
                for k in (0..ncoef - 2).rev() {
                    prog.push(ins(Op::Mac, Some(Val::T(qq, k)), Some(Val::T(qq, k + 1)), Some(Val::XF(qq)), Some(Val::Coeff(k)), "fri.final_horner", sq, None));
                }
                prog.push(ins(Op::Eq, None, Some(Val::T(qq, 0)), Some(Val::U(qq, last)), None, "fri.final", sq, None));
            }
        }
        // ---- the ALU program: K3a's, per height and opening point ----
        let k3a_start = prog.len();
        // zeta * g_t for every table with a next-row opening (C3n verifier/mod.rs l. 247: trace_domains[i].next_point).
        let point_val = |p: usize| if p == 0 { Val::Zeta } else { Val::ZetaNext(p - 1) };
        let mut next_tables: BTreeSet<usize> = BTreeSet::new();
        for &(_, p) in &hz {
            if p > 0 {
                next_tables.insert(p - 1);
            }
        }
        for &t in &next_tables {
            let name: &'static str = Box::leak(format!("omega_table{t}").into_boxed_str());
            let k = konst(&mut prog, &mut consts, name, F::two_adic_generator(c.tables[t].log_trace));
            prog.push(ins(Op::Mul, Some(Val::ZetaNext(t)), Some(Val::Zeta), Some(k), None, "deep.zeta_next", None, None));
        }
        // The input coset point of each lower height from the tallest: x_h = x_H^(2^d) g^(1 - 2^d), d = H - h.
        let mut x_steps: Vec<(usize, usize, Val)> = vec![];
        {
            let mut prev = top_h;
            for &h in &heights[1..] {
                let d = prev - h;
                let name: &'static str = Box::leak(format!("g^(1-2^{d})").into_boxed_str());
                let g_exp = F::GENERATOR.exp_u64((1u64 << d) - 1).inverse();
                let k = konst(&mut prog, &mut consts, name, g_exp);
                x_steps.push((prev, h, k));
                prev = h;
            }
        }
        let bind_instr = [prog.len(), prog.len() + 1, prog.len() + 2];
        prog.push(ins(Op::Mul, Some(Val::AP(2)), Some(Val::PcsAlpha), Some(Val::PcsAlpha), None, "deep.alpha_power", None, None));
        prog.push(ins(Op::Mul, Some(Val::AP(3)), Some(Val::AP(2)), Some(Val::PcsAlpha), None, "deep.alpha_power", None, None));
        prog.push(ins(Op::Mul, Some(Val::AP(4)), Some(Val::AP(2)), Some(Val::AP(2)), None, "deep.alpha_power", None, None));
        let mut need: BTreeSet<usize> = BTreeSet::new();
        for ch in &chains {
            need.extend(ch.offsets.iter().map(|&(_, o)| o - ch.shift).filter(|&o| o > 0));
        }
        need.extend(claim_runs.iter().map(|r| r.ladder_off).filter(|&o| o > 0));
        let mut have: BTreeSet<usize> = [1usize, 2, 3, 4].into_iter().collect();
        let apv = |e: usize| if e == 1 { Val::PcsAlpha } else { Val::AP(e) };
        let topp = need.iter().max().copied().unwrap_or(1);
        let mut p2 = 4usize;
        while 2 * p2 <= topp {
            prog.push(ins(Op::Mul, Some(Val::AP(2 * p2)), Some(apv(p2)), Some(apv(p2)), None, "deep.ladder_power", None, None));
            have.insert(2 * p2);
            p2 *= 2;
        }
        for &e in &need {
            if have.contains(&e) {
                continue;
            }
            let bits: Vec<usize> = (0..usize::BITS as usize).filter(|b| e >> b & 1 == 1).map(|b| 1usize << b).collect();
            let mut acc = bits[0];
            for &b in &bits[1..] {
                let nxt = acc + b;
                if !have.contains(&nxt) {
                    prog.push(ins(Op::Mul, Some(apv(nxt)), Some(apv(acc)), Some(apv(b)), None, "deep.ladder_power", None, None));
                    have.insert(nxt);
                }
                acc = nxt;
            }
        }
        // The claims' sums per (height, point): sum_i alpha^(off + i) p_i(z), one Horner run per contiguous ladder
        // range, the runs of one (height, point) combined with their offsets.
        let mut run_val = vec![];
        for (ri, run) in claim_runs.iter().enumerate() {
            let f = run.first_claim;
            if run.len == 1 {
                run_val.push(Val::Claim(f));
                continue;
            }
            let l = run.len;
            prog.push(ins(Op::Mac, Some(Val::HC(ri, l - 2)), Some(Val::Claim(f + l - 1)), Some(Val::PcsAlpha), Some(Val::Claim(f + l - 2)), "deep.claims_horner", None, None));
            for i in (0..l - 2).rev() {
                prog.push(ins(Op::Mac, Some(Val::HC(ri, i)), Some(Val::HC(ri, i + 1)), Some(Val::PcsAlpha), Some(Val::Claim(f + i)), "deep.claims_horner", None, None));
            }
            run_val.push(Val::HC(ri, 0));
        }
        let mut c_vals: BTreeMap<(usize, usize), Val> = BTreeMap::new();
        for &(h, pt) in &hz {
            let terms: Vec<(usize, Val)> = claim_runs.iter().zip(&run_val).filter(|(r, _)| r.point == pt && r.log_height == h).map(|(r, &v)| (r.ladder_off, v)).collect();
            c_vals.insert((h, pt), weighted_sum(&mut prog, &terms, &|k| Val::CPart(h, pt, k), Val::CP(h, pt), "deep.claims_sum", None));
        }
        let mut u_vals: Vec<BTreeMap<(usize, usize), Val>> = vec![];
        for qq in 0..q {
            let sq = Some(qq);
            // x per height: XI(q, H) from the canonical path; lower heights by squarings and a constant.
            for &(from, to, k) in &x_steps {
                let d = from - to;
                let mut cur = Val::XI(qq, from);
                for i in 0..d {
                    let nxt = Val::XP(qq, to, i);
                    prog.push(ins(Op::Mul, Some(nxt), Some(cur), Some(cur), None, "deep.x_height", sq, None));
                    cur = nxt;
                }
                prog.push(ins(Op::Mul, Some(Val::XI(qq, to)), Some(cur), Some(k), None, "deep.x_height", sq, None));
            }
            let mut uz_q = BTreeMap::new();
            for &(h, pt) in &hz {
                prog.push(lin(Val::DZ(qq, h, pt), point_val(pt), Val::XI(qq, h), -F::ONE, "deep.denominator", sq));
                prog.push(ins(Op::Inv, Some(Val::IZ(qq, h, pt)), Some(Val::DZ(qq, h, pt)), None, None, "deep.inverse", sq, None));
                let terms: Vec<(usize, Val)> = chains
                    .iter()
                    .enumerate()
                    .filter(|(_, ch)| ch.log_height == h)
                    .filter_map(|(ci, ch)| ch.offsets.iter().find(|o| o.0 == pt).map(|o| (o.1 - ch.shift, Val::SD(qq, ci))))
                    .collect();
                let uz = weighted_sum(&mut prog, &terms, &|k| Val::UPart(qq, h, pt, k), Val::UZ(qq, h, pt), "deep.opened_sum", sq);
                uz_q.insert((h, pt), uz);
            }
            u_vals.push(uz_q.clone());
            for &h in &heights {
                let pts: Vec<usize> = hz.iter().filter(|x| x.0 == h).map(|x| x.1).collect();
                for (k, &pt) in pts.iter().enumerate() {
                    prog.push(lin(Val::TZ(qq, h, pt), c_vals[&(h, pt)], uz_q[&(h, pt)], -F::ONE, "deep.difference", sq));
                    if k == 0 {
                        prog.push(ins(Op::Mul, Some(Val::RO(qq, h, 0)), Some(Val::TZ(qq, h, pt)), Some(Val::IZ(qq, h, pt)), None, "deep.reduced_opening", sq, None));
                    } else {
                        prog.push(ins(Op::Mac, Some(Val::RO(qq, h, k)), Some(Val::TZ(qq, h, pt)), Some(Val::IZ(qq, h, pt)), Some(Val::RO(qq, h, k - 1)), "deep.reduced_opening", sq, None));
                    }
                }
            }
            // Round 0: the coset value at the query's position equals the tallest height's reduced opening.
            let e = |j: usize| Some(Val::E(qq, 0, j));
            if c.fri_log_arities[0] == 2 {
                prog.push(ins(Op::Bfly, Some(Val::Sel(qq, 0, 0)), e(0), e(1), Some(Val::Sigma(qq, 0, 0)), "fri.select0", sq, Some(0)));
                prog.push(ins(Op::Bfly, Some(Val::Sel(qq, 0, 1)), e(2), e(3), Some(Val::Sigma(qq, 0, 0)), "fri.select0", sq, Some(0)));
                prog.push(ins(Op::Bfly, Some(Val::M(qq, 0)), Some(Val::Sel(qq, 0, 0)), Some(Val::Sel(qq, 0, 1)), Some(Val::Sigma(qq, 0, 1)), "fri.select0", sq, Some(0)));
            } else {
                prog.push(ins(Op::Bfly, Some(Val::M(qq, 0)), e(0), e(1), Some(Val::Sigma(qq, 0, 0)), "fri.select0", sq, Some(0)));
            }
            prog.push(ins(Op::Eq, None, Some(Val::M(qq, 0)), Some(Val::RO(qq, top_h, ro_last(&hz, top_h))), None, "fri.rollin0", sq, Some(0)));
        }
        let k3a_range = (k3a_start, prog.len());
        // ---- the ALU program: the compiled batch constraint program (K3b, per table) ----
        let k3b_start = prog.len();
        let cp = c.program.clone();
        assert_eq!(cp.tables.len(), c.tables.len());
        let block = |tree: usize, matrix: usize, pt: usize| -> usize {
            claim_blocks.iter().find(|b| b.tree == tree && b.matrix == matrix && b.point == pt).expect("claim block").first_claim
        };
        let tree_of = |kind: TreeKind| trees.iter().position(|t| t.kind == kind).expect("tree");
        // The matrix and position holding table t's column `col` of a trace of `kind` (main, preprocessed, permutation).
        let locate = |kind: TreeKind, t: usize, col: usize, want_next: bool| -> (usize, usize, usize) {
            let ti = tree_of(kind);
            let tr = &trees[ti];
            for (m, mat) in tr.mats.iter().enumerate() {
                if mat.table != t {
                    continue;
                }
                let is_trace = matches!((&mat.kind, kind), (MatKind::Main(..), TreeKind::Input(0)) | (MatKind::Pre(_), TreeKind::Input(2)) | (MatKind::Perm(..), TreeKind::Input(3)));
                if !is_trace {
                    continue;
                }
                if let Some(pos) = mat.cols.iter().position(|&x| x == col) {
                    if want_next && !mat.points.contains(&(1 + t)) {
                        continue;
                    }
                    return (ti, m, pos);
                }
            }
            panic!("table {t}: column {col} of {kind:?} (next {want_next}) is not opened");
        };
        let input_val: BTreeMap<usize, Val> = cp
            .inputs
            .iter()
            .map(|&(id, inp)| {
                let v = match inp {
                    Input::TraceLocal(t, i) => {
                        let (ti, m, pos) = locate(TreeKind::Input(0), t, i, false);
                        Val::Claim(block(ti, m, 0) + pos)
                    }
                    Input::TraceNext(t, i) => {
                        let (ti, m, pos) = locate(TreeKind::Input(0), t, i, true);
                        Val::Claim(block(ti, m, 1 + t) + pos)
                    }
                    Input::PreLocal(t, i) => {
                        let (ti, m, pos) = locate(TreeKind::Input(2), t, i, false);
                        Val::Claim(block(ti, m, 0) + pos)
                    }
                    Input::PreNext(t, i) => {
                        let (ti, m, pos) = locate(TreeKind::Input(2), t, i, true);
                        Val::Claim(block(ti, m, 1 + t) + pos)
                    }
                    Input::PermLocal(t, j, k) => {
                        let (ti, m, pos) = locate(TreeKind::Input(3), t, 8 * j + k, false);
                        Val::Claim(block(ti, m, 0) + pos)
                    }
                    Input::PermNext(t, j, k) => {
                        let (ti, m, pos) = locate(TreeKind::Input(3), t, 8 * j + k, true);
                        Val::Claim(block(ti, m, 1 + t) + pos)
                    }
                    Input::Chunk(t, ch, k) => {
                        let ti = tree_of(TreeKind::Input(1));
                        let m = trees[ti].mats.iter().position(|mm| mm.kind == MatKind::Quot(t, ch)).expect("chunk matrix");
                        Val::Claim(block(ti, m, 0) + k)
                    }
                    Input::Public(t, i) => Val::Pub(c.tables[t].public[i]),
                    Input::Alpha => Val::Alpha,
                    Input::Zeta => Val::Zeta,
                    Input::LookupAlpha => Val::LookupAlpha,
                    Input::LookupBeta => Val::LookupBeta,
                    Input::Terminal(t) => Val::Terminal(t),
                };
                (id, v)
            })
            .collect();
        let val_of = |id: usize| -> Val { input_val.get(&id).copied().unwrap_or(Val::Ev(id)) };
        // Public values: table t's public value i is absorbed at its batch public-values segment (pinned to the
        // statement by transcript.public); UNPACK takes its lane from the row's absorbed lanes, which WH writes.
        let mut pub_src: BTreeMap<(usize, usize), (usize, usize)> = BTreeMap::new();
        for (t, tb) in c.tables.iter().enumerate() {
            if tb.public.is_empty() {
                continue;
            }
            let sgm = segments.iter().find(|g| g.name == format!("batch.public_values.table{t}")).expect("public-values segment");
            for (i, e) in (sgm.first_event..sgm.first_event + sgm.len).enumerate() {
                match events[e] {
                    Ev::Abs(Src::Pub(j)) => {
                        assert_eq!(j, tb.public[i]);
                        pub_src.insert((t, i), ev_pos[e]);
                    }
                    other => panic!("public-values segment holds {other:?}"),
                }
            }
        }
        let mut pub_rows: BTreeSet<usize> = BTreeSet::new();
        let mut unpacked: BTreeSet<usize> = BTreeSet::new();
        for &(_, inp) in &cp.inputs {
            if let Input::Public(t, i) = inp {
                let j = c.tables[t].public[i];
                if !unpacked.insert(j) {
                    continue;
                }
                let (row, lane) = pub_src[&(t, i)];
                pub_rows.insert(row);
                let mut u = ins(Op::Unpack, Some(Val::Pub(j)), Some(Val::PubRow(row)), None, None, "eval.public", None, None);
                u.lane = lane;
                prog.push(u);
            }
        }
        for pi in &cp.instrs {
            let opc = match pi.op {
                POp::Const => Op::Const,
                POp::Mul => Op::Mul,
                POp::Mac => Op::Mac,
                POp::Lin => Op::Lin,
                POp::Inv => Op::Inv,
                POp::Eq => Op::Eq,
            };
            let mut i = ins(opc, pi.r.map(val_of), pi.a.map(val_of), pi.b.map(val_of), pi.c.map(val_of), pi.role, None, None);
            i.kappa = pi.kappa;
            i.kappa_x = pi.kappa_x;
            prog.push(i);
        }
        let k3b_range = (k3b_start, prog.len());
        // LOADs: each query's canonical path start reads the vector its query element was squeezed into.
        let mut loads: Vec<(usize, Instr)> = vec![];
        for qq in 0..q {
            let (qrow, qlane) = q_pos[qq];
            let mut l = ins(Op::Load, None, Some(Val::Squeeze(qrow)), None, None, "index.load", Some(qq), None);
            l.lane = 7 - qlane;
            loads.push((block_start[qq][canon] + trees[canon].path_start, l));
        }
        // Reserved rows (B2): the LOADs and the cap-read rows (their RA/RB slots). B1 also reserved the write port's rows
        // and the injection rows; B2 writes through W2 and reads an injected digest through RI, so those rows hold ALU
        // instructions.
        let mut reserved: BTreeSet<usize> = loads.iter().map(|(r, _)| *r).collect();
        let mut cap_reads = vec![];
        let mut inj_reads = vec![];
        for qq in 0..q {
            for (ti, t) in trees.iter().enumerate() {
                let b0 = block_start[qq][ti];
                for &(o, nd) in &t.nodes {
                    if let Node::Inj(k) = nd {
                        inj_reads.push((b0 + o, Val::InjHash(qq, ti, k)));
                    }
                }
                reserved.insert(b0 + t.cap_read);
                cap_reads.push((b0 + t.cap_read, ti));
            }
        }
        let mut instr_row = vec![];
        let mut rr = 0;
        for _ in 0..prog.len() {
            while reserved.contains(&rr) {
                rr += 1;
            }
            instr_row.push(rr);
            rr += 1;
        }
        if rr > n {
            return Err(rr);
        }
        for (r0, l) in loads {
            prog.push(l);
            instr_row.push(r0);
        }
        // ---- the bus: writers, path-start reads, read counts, addresses ----
        let mut writer: BTreeMap<Val, Writer> = BTreeMap::new();
        let mut put = |v: Val, w: Writer| {
            assert!(writer.insert(v, w).is_none(), "{v:?} written twice");
        };
        for (i, ins) in prog.iter().enumerate() {
            if let Some(r) = ins.r {
                put(r, Writer::Alu(i));
            }
        }
        for &(rw, v) in &w2port {
            put(v, Writer::W2(rw));
        }
        for (r, &row) in beta_row.iter().enumerate() {
            put(Val::Beta(r), Writer::O(row));
        }
        put(Val::Alpha, Writer::O(alpha_row));
        put(Val::Zeta, Writer::O(zeta_row));
        put(Val::PcsAlpha, Writer::O(pcs_alpha_row));
        if la_row != usize::MAX {
            put(Val::LookupAlpha, Writer::O(la_row));
            put(Val::LookupBeta, Writer::O(lb_row));
        }
        for (k, &row) in coeff_row.iter().enumerate() {
            put(Val::Coeff(k), Writer::H(row));
        }
        for &row in &pub_rows {
            put(Val::PubRow(row), Writer::H(row));
        }
        let mut sq_rows: Vec<usize> = q_pos.iter().map(|p| p.0).collect();
        sq_rows.sort_unstable();
        sq_rows.dedup();
        for &row in &sq_rows {
            put(Val::Squeeze(row), Writer::O(row));
        }
        let mut rs_reads = vec![];
        for qq in 0..q {
            let ct = &trees[canon];
            let cb = block_start[qq][canon];
            put(Val::Xq(qq), Writer::V(cb + ct.path_start));
            for &d in &shifts {
                // The canonical path's row that consumes bit d holds ACC = query element >> d.
                let bits = ct.bit_rows();
                put(Val::Shift(qq, d), Writer::V(cb + bits[d]));
            }
            put(Val::XI(qq, top_h), Writer::V(cb + ct.end));
            for (ti, t) in trees.iter().enumerate() {
                let b0 = block_start[qq][ti];
                // Injected groups: the group's last leaf row writes its digest (WO).
                for (k, g) in t.groups.iter().enumerate().skip(1) {
                    put(Val::InjHash(qq, ti, k), Writer::O(b0 + t.group_start[k] + g.lh_rows - 1));
                }
                match t.start {
                    Start::Load => {}
                    Start::Xq => rs_reads.push((b0 + t.path_start, Val::Xq(qq))),
                    Start::Shift(d) => rs_reads.push((b0 + t.path_start, Val::Shift(qq, d))),
                    Start::Chain(r) => rs_reads.push((b0 + t.path_start, Val::Chain(qq, r))),
                }
                if let TreeKind::Fri(r) = t.kind {
                    let la = c.fri_log_arities[r];
                    let s0 = b0 + t.path_start;
                    put(Val::S(qq, r), Writer::V(b0 + t.end));
                    for j in 0..(1usize << la) {
                        put(Val::E(qq, r, j), Writer::H(s0 + j));
                    }
                    for i in 0..la {
                        put(Val::Sigma(qq, r, i), Writer::V(s0 + i));
                    }
                    if r + 1 < rounds {
                        put(Val::Chain(qq, r + 1), Writer::V(s0 + la));
                    }
                }
            }
        }
        let mut reads: HashMap<Val, u32> = HashMap::new();
        for ins in &prog {
            for v in [ins.a, ins.b, ins.c].into_iter().flatten() {
                *reads.entry(v).or_default() += 1;
            }
        }
        for &(_, v) in &rs_reads {
            *reads.entry(v).or_default() += 1;
        }
        for &(_, v) in &inj_reads {
            *reads.entry(v).or_default() += 1;
        }
        // Every cap read reads Hi(q) through RB.
        for qq in 0..q {
            *reads.entry(Val::Hi(qq)).or_default() += trees.len() as u32;
        }
        for v in reads.keys() {
            assert!(writer.contains_key(v), "{v:?} is read but never written");
        }
        // A value no instruction reads is not written, except the cap entries (their read count is the prover's).
        writer.retain(|v, _| reads.contains_key(v) || matches!(v, Val::Cap(..)));
        for v in writer.keys() {
            if let Val::Cap(..) = v {
                reads.entry(*v).or_insert(0);
            }
        }
        for &(rw, v) in &w2port {
            assert!(writer.get(&v) == Some(&Writer::W2(rw)), "every W2 value is read: {v:?}");
        }
        let mut addr: HashMap<Val, u32> = HashMap::new();
        for (i, v) in writer.keys().enumerate() {
            addr.insert(*v, i as u32 + 1);
        }
        // A tree's cap entries hold consecutive addresses (the cap read adds the cap index to entry 0's).
        for ti in 0..trees.len() {
            for j in 0..caps {
                assert_eq!(addr[&Val::Cap(ti, j)], addr[&Val::Cap(ti, 0)] + j as u32);
            }
        }
        let ad = |v: Val| F::from_u32(addr[&v]);
        // ---- the preprocessed columns (B1: periodic): opcode selectors, immediates, control schedules, payload flags ----
        let mut used: HashMap<(usize, usize), ()> = HashMap::new();
        let mut set = |pc: &mut Cols, col: usize, row: usize, v: F| {
            assert!(used.insert((col, row), ()).is_none(), "slot conflict: {} at row {row}", pc.names[col]);
            pc.cols[col][row] = v;
        };
        for (i, ins) in prog.iter().enumerate() {
            let rw = instr_row[i];
            if ins.op == Op::Load {
                set(&mut pc, ctrl[0], rw, ad(ins.a.unwrap()));
                set(&mut pc, ctrl[1], rw, F::ONE);
                set(&mut pc, lsel[ins.lane], rw, F::ONE);
                continue;
            }
            if ins.op == Op::Unpack {
                set(&mut pc, unp[ins.lane], rw, F::ONE);
                set(&mut pc, ctrl[0], rw, ad(ins.a.unwrap()));
                set(&mut pc, ctrl[1], rw, F::ONE);
                if let Some(&m) = reads.get(&ins.r.unwrap()) {
                    set(&mut pc, ctrl[6], rw, ad(ins.r.unwrap()));
                    set(&mut pc, ctrl[7], rw, F::from_u32(m));
                }
                continue;
            }
            let o = OPS.iter().position(|&x| x == ins.op).unwrap();
            set(&mut pc, op[o], rw, F::ONE);
            if ins.op == Op::Const || ins.op == Op::Lin {
                set(&mut pc, kappa, rw, ins.kappa);
            }
            if ins.op == Op::Const {
                set(&mut pc, kx, rw, ins.kappa_x);
            }
            for (slot, v) in [ins.a, ins.b, ins.c].into_iter().enumerate() {
                if let Some(v) = v {
                    set(&mut pc, ctrl[2 * slot], rw, ad(v));
                    set(&mut pc, ctrl[2 * slot + 1], rw, F::ONE);
                }
            }
            if let Some(v) = ins.r {
                if let Some(&m) = reads.get(&v) {
                    set(&mut pc, ctrl[6], rw, ad(v));
                    set(&mut pc, ctrl[7], rw, F::from_u32(m));
                }
            }
        }
        for (k, &i) in bind_instr.iter().enumerate() {
            set(&mut pc, bind[k], instr_row[i], F::ONE);
        }
        for (v, w) in &writer {
            let m = F::from_u32(reads[v]);
            match *w {
                Writer::Alu(_) => {}
                Writer::W2(rw) => {
                    set(&mut pc, ctrl[16], rw, ad(*v));
                    // A cap entry's multiplicity is the prover's (free under `capw`); the schedule's value is 0.
                    set(&mut pc, ctrl[17], rw, if matches!(v, Val::Cap(..)) { F::ZERO } else { m });
                }
                Writer::H(rw) => {
                    set(&mut pc, ctrl[8], rw, ad(*v));
                    set(&mut pc, ctrl[9], rw, m);
                }
                Writer::O(rw) => {
                    set(&mut pc, ctrl[10], rw, ad(*v));
                    set(&mut pc, ctrl[11], rw, m);
                }
                Writer::V(rw) => {
                    set(&mut pc, ctrl[12], rw, ad(*v));
                    set(&mut pc, ctrl[13], rw, m);
                    match v {
                        Val::Xq(_) | Val::Chain(..) | Val::Shift(..) => set(&mut pc, vacc, rw, F::ONE),
                        Val::Sigma(..) => set(&mut pc, vsig, rw, F::ONE),
                        Val::S(..) | Val::XI(..) => {}
                        other => panic!("unexpected base-slot value {other:?}"),
                    }
                }
            }
        }
        for &(rw, v) in &rs_reads {
            set(&mut pc, ctrl[14], rw, ad(v));
            set(&mut pc, ctrl[15], rw, F::ONE);
        }
        // B2: an injection reads its group's digest through RI (into the input lanes 15..8).
        for &(rw, v) in &inj_reads {
            set(&mut pc, ctrl[18], rw, ad(v));
            set(&mut pc, ctrl[19], rw, F::ONE);
        }
        for &(rw, ti) in &cap_reads {
            set(&mut pc, ctrl[0], rw, ad(Val::Cap(ti, 0)));
            set(&mut pc, ctrl[1], rw, F::ONE);
        }
        for qq in 0..q {
            for ti in 0..trees.len() {
                let rw = block_start[qq][ti] + trees[ti].cap_read;
                set(&mut pc, ctrl[2], rw, ad(Val::Hi(qq)));
                set(&mut pc, ctrl[3], rw, F::ONE);
            }
        }
        let pidx = PIdx {
            cf, cv, kc, tag: tagc, kr, ivf, lnk, cons, path_t, start, pend, pend_canon, lsel, xs, x0, xp, xc, vs, xce, vacc, vsig, op, kappa, kx,
            unp, ctrl, dv, dc, dl, dp, dw, cs, bind, inj, capr, capw, hiw,
        };
        let air = KernelAir { p2: P2Air::new(constants()), log_n, num_public: c.num_public, pre: pc.cols, pre_names: pc.names, pidx, pub_terms, k0: trows[0].k };
        Ok(Schedule {
            child: c.clone(),
            events,
            segments,
            ev_pos,
            trows,
            wit_len,
            wit_segments,
            trees,
            q,
            block_rows,
            t_rows,
            used_rows,
            log_n,
            n,
            block_start,
            num_public: c.num_public,
            air,
            program: prog,
            instr_row,
            addr,
            writer,
            reads,
            rs_reads,
            cap_reads,
            beta_row,
            coeff_row,
            alpha_row,
            zeta_row,
            pcs_alpha_row,
            lookup_alpha_row: la_row,
            lookup_beta_row: lb_row,
            claim_blocks,
            claim_runs,
            claim_pos,
            cap_pos,
            terminal_pos,
            chains,
            w2port,
            inj_reads,
            k3a_range,
            k3b_range,
            hz,
            c_vals,
            u_vals,
            rollins,
            pub_src,
            input_val,
            consts,
            heights,
        })
    }

    pub fn fri_tree(&self, r: usize) -> usize {
        self.trees.iter().position(|t| t.kind == TreeKind::Fri(r)).unwrap()
    }
    pub fn canon(&self) -> usize {
        self.trees.iter().position(|t| t.canonical).unwrap()
    }
    pub fn path_start(&self, qq: usize, ti: usize) -> usize {
        self.block_start[qq][ti] + self.trees[ti].path_start
    }
    pub fn end_row(&self, qq: usize, ti: usize) -> usize {
        self.block_start[qq][ti] + self.trees[ti].end
    }
    pub fn cap_read_row(&self, qq: usize, ti: usize) -> usize {
        self.block_start[qq][ti] + self.trees[ti].cap_read
    }
    pub fn group_row(&self, qq: usize, ti: usize, k: usize) -> usize {
        self.block_start[qq][ti] + self.trees[ti].group_start[k]
    }
    pub fn value_at(&self, address: u32) -> Option<Val> {
        self.addr.iter().find(|&(_, &a)| a == address).map(|(v, _)| *v)
    }
    pub fn n_claims(&self) -> usize {
        self.claim_pos.len()
    }
    pub fn k3b_unpacks(&self) -> usize {
        self.program[self.k3b_range.0..self.k3b_range.1].iter().filter(|i| i.op == Op::Unpack).count()
    }

    /// ALU instruction counts by role and by opcode, and the reserved rows.
    pub fn program_counts(&self) -> Value {
        let mut by_role: BTreeMap<&str, usize> = BTreeMap::new();
        let mut by_op: BTreeMap<&str, usize> = BTreeMap::new();
        for i in &self.program {
            *by_role.entry(i.role).or_default() += 1;
            *by_op.entry(i.op.name()).or_default() += 1;
        }
        let (k0, k1) = self.k3a_range;
        let k3a = &self.program[k0..k1];
        let k3a_per_query = k3a.iter().filter(|i| i.query.is_some()).count();
        let (b0, b1) = self.k3b_range;
        let k3b = &self.program[b0..b1];
        let mut k3b_by_op: BTreeMap<&str, usize> = BTreeMap::new();
        for i in k3b {
            *k3b_by_op.entry(i.op.name()).or_default() += 1;
        }
        let k3b_rows: Vec<usize> = self.instr_row[b0..b1].to_vec();
        let count = |f: &dyn Fn(&Val) -> bool| self.w2port.iter().filter(|(_, v)| f(v)).count();
        // Rows holding an ALU instruction (LOADs included), a W2 write, an injection read or a cap read.
        let busy: BTreeSet<usize> = self
            .instr_row
            .iter()
            .copied()
            .chain(self.w2port.iter().map(|(r, _)| *r))
            .chain(self.inj_reads.iter().map(|(r, _)| *r))
            .chain(self.cap_reads.iter().map(|(r, _)| *r))
            .collect();
        let rows_with_instr: BTreeSet<usize> = self.instr_row.iter().copied().collect();
        let w2_rows_with_instr = self.w2port.iter().filter(|(r, _)| rows_with_instr.contains(r)).count();
        let inj_rows_with_instr = self.inj_reads.iter().filter(|(r, _)| rows_with_instr.contains(r)).count();
        json!({"instructions": self.program.len(), "by_role": by_role, "by_opcode": by_op,
            "k2_instructions_with_loads": self.program.len() - k3a.len() - k3b.len(),
            "k3a_instructions": k3a.len(), "k3a_per_query_instructions": k3a_per_query, "k3a_shared_instructions": k3a.len() - k3a_per_query,
            "k3b_instructions": k3b.len(), "k3b_by_opcode": k3b_by_op, "k3b_unpack_instructions": self.k3b_unpacks(),
            "k3b_compiled_program_instructions": self.child.program.instrs.len(),
            "k3b_rows": [k3b_rows.iter().min(), k3b_rows.iter().max()],
            "w2_writes": {"claims": count(&|v| matches!(v, Val::Claim(_))), "deep_chain_sums": count(&|v| matches!(v, Val::SD(..))),
                "cap_entries": count(&|v| matches!(v, Val::Cap(..))), "lookup_terminals": count(&|v| matches!(v, Val::Terminal(_))),
                "query_high_parts": count(&|v| matches!(v, Val::Hi(_))), "total": self.w2port.len(),
                "rows_that_also_hold_an_alu_instruction": w2_rows_with_instr},
            "injection_reads_ri": {"total": self.inj_reads.len(), "rows_that_also_hold_an_alu_instruction": inj_rows_with_instr},
            "reserved_rows": {"cap_reads": self.cap_reads.len(), "loads": self.q},
            "rows_with_an_instruction": self.instr_row.len(), "rows_using_the_alu_or_a_bus_slot_beyond_k1": busy.len(),
            "share_of_rows": self.program.len() as f64 / self.n as f64, "share_of_rows_busy": busy.len() as f64 / self.n as f64})
    }

    /// The program listing with rows and addresses.
    pub fn program_json(&self) -> Value {
        let name = |v: Option<Val>| v.map(|v| json!({"value": format!("{v:?}"), "address": self.addr.get(&v)}));
        let list: Vec<Value> = self
            .program
            .iter()
            .zip(&self.instr_row)
            .map(|(i, &rw)| {
                json!({"row": rw, "op": i.op.name(), "role": i.role, "query": i.query, "round": i.round,
                    "a": name(i.a), "b": name(i.b), "c": name(i.c), "r": name(i.r),
                    "result_multiplicity": i.r.and_then(|v| self.reads.get(&v)),
                    "immediate": if i.op == Op::Const || i.op == Op::Lin { Some(p3_field::PrimeField32::as_canonical_u32(&i.kappa)) } else { None },
                    "immediate_x": if i.op == Op::Const { Some(p3_field::PrimeField32::as_canonical_u32(&i.kappa_x)) } else { None },
                    "coordinate": if i.op == Op::Load || i.op == Op::Unpack { Some(i.lane) } else { None }})
            })
            .collect();
        let writers: Vec<Value> = self
            .writer
            .iter()
            .map(|(v, w)| {
                let (slot, row) = match *w {
                    Writer::Alu(i) => ("WR", self.instr_row[i]),
                    Writer::W2(r) => ("W2", r),
                    Writer::H(r) => ("WH", r),
                    Writer::O(r) => ("WO", r),
                    Writer::V(r) => ("WV", r),
                };
                json!({"address": self.addr[v], "value": format!("{v:?}"), "slot": slot, "row": row,
                    "multiplicity": if matches!(v, Val::Cap(..)) { json!("prover's") } else { json!(self.reads[v]) }})
            })
            .collect();
        json!({"schema": "l5-layer-b2/program/v1", "counts": self.program_counts(), "instructions": list, "writes": writers,
            "w2_writes": self.w2port.iter().map(|(r, v)| json!({"row": r, "value": format!("{v:?}"), "address": self.addr[v]})).collect::<Vec<_>>(),
            "injection_reads": self.inj_reads.iter().map(|(r, v)| json!({"row": r, "value": format!("{v:?}"), "address": self.addr[v]})).collect::<Vec<_>>(),
            "path_start_reads": self.rs_reads.iter().map(|(r, v)| json!({"row": r, "value": format!("{v:?}"), "address": self.addr[v]})).collect::<Vec<_>>(),
            "cap_reads": self.cap_reads.iter().map(|(r, t)| json!({"row": r, "tree": self.trees[*t].name, "base_address": self.addr[&Val::Cap(*t, 0)]})).collect::<Vec<_>>()})
    }

    /// The interface map: transcript values, witness stream, trees and groups, query blocks, columns, bus, DEEP layout.
    pub fn interface(&self) -> Value {
        let segs: Vec<Value> = self
            .segments
            .iter()
            .map(|s| {
                let (r0, l0) = self.ev_pos[s.first_event];
                let (r1, l1) = self.ev_pos[s.first_event + s.len - 1];
                json!({"name": s.name, "kind": s.kind, "events": s.len, "first": [r0, l0], "last": [r1, l1]})
            })
            .collect();
        let tree_layout: Vec<Value> = self
            .trees
            .iter()
            .map(|t| {
                json!({"tree": t.name, "kind": format!("{:?}", t.kind), "log_height": t.log_height, "walked_levels": t.mc,
                    "index_bits_on_leaf_rows": t.consume_lh, "index_bits_below_this_tree": t.skip, "cap_rows": t.cap_rows,
                    "start": format!("{:?}", t.start), "canonical": t.canonical,
                    "matrices": t.mats.iter().map(|m| json!({"kind": format!("{:?}", m.kind), "width": m.width, "columns": m.cols,
                        "log_height": m.log_height, "points": m.points.iter().map(|&p| pt_name(p)).collect::<Vec<_>>()})).collect::<Vec<_>>(),
                    "groups": t.groups.iter().map(|g| json!({"matrices": g.mats, "log_height": g.log_height, "leaf_elements": g.leaf_len,
                        "leaf_hash_rows": g.lh_rows, "injected_after_compressions": g.inject_after})).collect::<Vec<_>>(),
                    "layout": {"group_starts": t.group_start, "path_start": t.path_start,
                        "nodes": t.nodes.iter().map(|(o, n)| json!([o, format!("{n:?}")])).collect::<Vec<_>>(),
                        "cap_read": t.cap_read, "end": t.end, "rows": t.block_len}})
            })
            .collect();
        let addr_of = |v: Val| self.addr.get(&v).copied();
        let pr = &self.child.program;
        let input_map: Vec<Value> = self.input_val.iter().map(|(id, v)| json!({"value_id": id, "bus_value": format!("{v:?}"), "address": self.addr.get(v)})).collect();
        let tables: Vec<Value> = pr
            .tables
            .iter()
            .enumerate()
            .map(|(t, o)| {
                json!({"table": t, "z_h": addr_of(Val::Ev(o.z_h)), "inv_vanishing": addr_of(Val::Ev(o.inv_vanishing)), "folded": addr_of(Val::Ev(o.folded)),
                    "quotient": addr_of(Val::Ev(o.quotient)), "identity_row": self.instr_row[self.k3b_range.0 + self.k3b_unpacks() + o.identity]})
            })
            .collect();
        json!({
            "schema": "l5-layer-b2/interface/v1",
            "compiled_program": {"sha256": self.child.program_sha256.iter().map(|b| format!("{b:02x}")).collect::<String>(),
                "instructions": pr.instrs.len(), "values": pr.n_values, "inputs": input_map, "tables": tables,
                "terminal_check_row": self.instr_row[self.k3b_range.0 + self.k3b_unpacks() + pr.terminal_check],
                "public_values": self.pub_src.iter().map(|((t, i), (r, l))| json!([t, i, r, l])).collect::<Vec<_>>(),
                "range": [self.k3b_range.0, self.k3b_range.1]},
            "rows": {"n": self.n, "log_n": self.log_n, "transcript": [0, self.t_rows], "query_blocks": [self.t_rows, self.used_rows],
                "rows_per_query": self.block_rows, "padding": [self.used_rows, self.n]},
            "columns": {"poseidon2_inputs": [0, 16], "poseidon2_outputs": [crate::kernel::OUT, crate::kernel::OUT + 16],
                "bit": crate::kernel::BIT, "acc": crate::kernel::ACC, "hi_bits": [crate::kernel::HB, crate::kernel::TP],
                "hi_products": [crate::kernel::TP, crate::kernel::XQ], "xq": crate::kernel::XQ, "x": crate::kernel::X,
                "v": crate::kernel::V, "alu_a": [crate::kernel::A, crate::kernel::B], "alu_b": [crate::kernel::B, crate::kernel::C],
                "alu_c": [crate::kernel::C, crate::kernel::R], "alu_r": [crate::kernel::R, crate::kernel::AA],
                "ra_address_main": crate::kernel::AA, "w2_multiplicity_main": crate::kernel::MW, "w2_value": [crate::kernel::W2, crate::kernel::DL],
                "bus_control_preprocessed_names": CTRL_NAMES,
                "deep_accumulator": [crate::kernel::DL, crate::kernel::PW], "batching_challenge_powers_1_to_4": [crate::kernel::PW, crate::kernel::WIDTH],
                "width": crate::kernel::WIDTH},
            "public_values": {"count": self.num_public,
                "prefix": self.child.prefix.iter().map(|it| match it {
                    PrefixItem::Bytes(n, b) => json!({"name": n, "kind": "constant bytes (length, then each byte)", "bytes": b.len()}),
                    PrefixItem::PubBytes(n, f, l) => json!({"name": n, "kind": "statement bytes (length, then kernel public values)", "kernel_public_values": [f, f + l]}),
                    PrefixItem::Fields(n, f) => json!({"name": n, "kind": "constant field elements", "elements": f.len()}),
                }).collect::<Vec<_>>(),
                "tables": self.child.tables.iter().map(|t| json!({"table": t.name, "kernel_public_values": t.public})).collect::<Vec<_>>()},
            "transcript_segments": segs,
            "witness_stream": self.wit_segments.iter().map(|(n, s, l)| json!({"name": n, "first": s, "len": l})).collect::<Vec<_>>(),
            "trees": tree_layout,
            "query_blocks": (0..self.q).map(|qq| json!({"query": qq, "tree_blocks": self.block_start[qq]})).collect::<Vec<_>>(),
            "bus": {"name": crate::kernel::BUS, "message": "(address, 8 coordinates); a base value v is (address, v, 0, ..., 0)",
                "slots": crate::kernel::SLOTS, "addresses": self.addr.len(),
                "cap_entries": self.cap_pos.iter().map(|(&(t, j), p)| json!({"tree": self.trees[t].name, "entry": j, "row": p.row, "lane": p.lane, "address": addr_of(Val::Cap(t, j))})).collect::<Vec<_>>(),
                "cap_rule": "cap entry j of tree t is written by the second write slot W2 at its transcript position (claim.write), address = entry 0's + j, multiplicity the prover's (main column MW, free under the preprocessed flag cap_entry_write_row_free_multiplicity); a path's cap-read row reads (entry 0's address + its cap bits HB[0..5] in main column AA, its node) through RA",
                "lookup_terminals": self.terminal_pos.iter().map(|(&t, p)| json!({"table": t, "row": p.row, "lane": p.lane, "address": addr_of(Val::Terminal(t))})).collect::<Vec<_>>(),
                "challenge_rows": {"batch.lookup_alpha": self.lookup_alpha_row, "batch.lookup_beta": self.lookup_beta_row, "batch.constraint_challenge": self.alpha_row,
                    "batch.zeta": self.zeta_row, "pcs.alpha": self.pcs_alpha_row, "fri.beta": self.beta_row, "fri.final_poly": self.coeff_row}},
            "deep": {
                "height_point_pairs": self.hz.iter().map(|&(h, p)| json!({"log_height": h, "point": pt_name(p)})).collect::<Vec<_>>(),
                "claim_blocks": self.claim_blocks.iter().map(|b| json!({"tree": self.trees[b.tree].name, "matrix": b.matrix, "point": pt_name(b.point),
                    "width": b.width, "first_claim": b.first_claim, "ladder_offset": b.ladder_off, "log_height": b.log_height})).collect::<Vec<_>>(),
                "claim_runs": self.claim_runs.len(),
                "chains": self.chains.iter().map(|ch| json!({"tree": self.trees[ch.tree].name, "matrix": ch.matrix, "matrices": ch.matrices, "group": ch.group,
                    "value_rows": ch.value_rows.iter().map(|(r, l)| json!([r, l.len()])).collect::<Vec<_>>(), "pass_rows": ch.pass_rows, "first_lane": ch.shift,
                    "offsets": ch.offsets.iter().map(|(p, o)| json!({"point": pt_name(*p), "ladder_offset": o})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
                "rollins": self.rollins.iter().map(|(r, h)| json!({"after_round": r, "log_height": h})).collect::<Vec<_>>(),
                "constants": self.consts.iter().map(|(n, v)| json!([n, p3_field::PrimeField32::as_canonical_u32(v)])).collect::<Vec<_>>()},
            "preprocessed_columns": self.air.pre_names,
        })
    }
}
