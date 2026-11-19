//! The G1 constraint-program compiler (L5, 2026-10-31; K3b's, generalized to a multi-table batch child): from every
//! table's symbolic constraints, base and extension (the LogUp gadget's included), to one straight-line EF8 program
//! that the kernel's ALU runs to check every table's constraint identity at zeta and the global lookup terminal sum.
//!
//! Input: per table, the base and extension constraints as p3_batch_stark_c3n's symbolic evaluation builds them
//! (`symbolic::get_symbolic_constraints`: the AIR's eval, then the LogUp gadget's fraction pins and accumulator
//! constraints for the key's lookups, p3-lookup logup.rs l. 314-459; the expression DAG of p3-air symbolic/mod.rs over
//! the leaves of symbolic/expression.rs and expression_ext.rs), the table's shape, and the batch's lookup layout. Never
//! a proof.
//!
//! Output: one program (`Program`), which the verifier fixes and the kernel's verifier-key digest covers through its
//! file's SHA-256. It computes, exactly as the native C3n verifier states them (verifier/mod.rs l. 903-1027,
//! verifier/data.rs l. 53-123, transcript.rs l. 489-578):
//! 1. the shared part: zeta^(2^k) up to the largest table, gamma = beta_L^W and each bus's prefix alpha_L + (b + 1)
//!    gamma (p3-lookup challenges.rs l. 70-91), the lookup challenges as the gadget reads them, [prefix, beta_L] per
//!    lookup;
//! 2. per table t, over its own trace domain H_t (size 2^log_trace_t, shift 1): Z_H(zeta), inv_vanishing as an `INV`
//!    (zeta in H_t has no valid trace: `OodPointInDomain`, data.rs l. 71-77), is_first_row, is_last_row,
//!    is_transition; the permutation columns at zeta and zeta * g_t from their claimed base coordinates
//!    (`from_ext_basis_coefficients`, verifier/mod.rs l. 936-949); every base constraint, then every extension
//!    constraint (the fold order of `eval_air_and_lookups`: the AIR's, then the lookups', protocol.rs l. 113-130),
//!    folded with alpha (folder.rs l. 374-377, 394-400); the quotient recomposed from the table's chunks over its own
//!    chunk domains; and folded * inv_vanishing = quotient (data.rs l. 117-120);
//! 3. the global terminal check: the sum of the tables' lookup terminals is zero (logup.rs l. 461-478).
//!
//! Instruction set (the kernel's EF8 ALU): CONST (r = kappa + kappa_x X), MUL (r = a b), MAC (r = a b + c), LIN
//! (r = a + kappa b), INV (a r = 1), EQ (a = b). A value is written once; its readers are counted by the kernel.
//! Interfaces kept explicit (each rejected here with the interface it would need): periodic columns (values at
//! zeta^(N/p)), a proper preprocessed next-row subset, extension constants beyond kappa + kappa_x X.
//! Research prototype at small scale; loop-internal self-review; not independently reviewed.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use p3_air::symbolic::{BaseEntry, BaseLeaf, ExtEntry, ExtLeaf, SymbolicExpr, SymbolicExpression, SymbolicExpressionExt};
use p3_commit::PolynomialSpace;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;
use serde_json::{Value, json};

use crate::EF;

pub const SCHEMA: &str = "l5-kernel-g1/constraint-program/v1";

/// A value the kernel puts on the bus before the program reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Input {
    TraceLocal(usize, usize),
    TraceNext(usize, usize),
    PreLocal(usize, usize),
    PreNext(usize, usize),
    /// Untrusted periodic evaluation, separately digest-bound and checked by the native final verifier.
    Periodic(usize, usize),
    /// Table t's permutation column j, base coordinate k, at zeta (a claim of a base column).
    PermLocal(usize, usize, usize),
    PermNext(usize, usize, usize),
    Public(usize, usize),
    Alpha,
    Zeta,
    LookupAlpha,
    LookupBeta,
    Terminal(usize),
    Chunk(usize, usize, usize),
}

impl Input {
    pub fn describe(&self) -> Value {
        match *self {
            Input::TraceLocal(t, i) => json!(["trace_local", t, i]),
            Input::TraceNext(t, i) => json!(["trace_next", t, i]),
            Input::PreLocal(t, i) => json!(["preprocessed_local", t, i]),
            Input::PreNext(t, i) => json!(["preprocessed_next", t, i]),
            Input::Periodic(t, i) => json!(["periodic_advice", t, i]),
            Input::PermLocal(t, j, k) => json!(["permutation_local", t, j, k]),
            Input::PermNext(t, j, k) => json!(["permutation_next", t, j, k]),
            Input::Public(t, i) => json!(["public", t, i]),
            Input::Alpha => json!(["alpha"]),
            Input::Zeta => json!(["zeta"]),
            Input::LookupAlpha => json!(["lookup_alpha"]),
            Input::LookupBeta => json!(["lookup_beta"]),
            Input::Terminal(t) => json!(["lookup_terminal", t]),
            Input::Chunk(t, c, k) => json!(["quotient_chunk", t, c, k]),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sel {
    First,
    Last,
    Transition,
}
impl Sel {
    pub fn name(self) -> &'static str {
        match self {
            Sel::First => "is_first_row",
            Sel::Last => "is_last_row",
            Sel::Transition => "is_transition",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum POp {
    Const,
    Mul,
    Mac,
    Lin,
    Inv,
    Eq,
}
impl POp {
    pub fn name(self) -> &'static str {
        match self {
            POp::Const => "const",
            POp::Mul => "mul",
            POp::Mac => "mac",
            POp::Lin => "lin",
            POp::Inv => "inv",
            POp::Eq => "eq",
        }
    }
}

#[derive(Clone, Debug)]
pub struct PIns {
    pub op: POp,
    pub r: Option<usize>,
    pub a: Option<usize>,
    pub b: Option<usize>,
    pub c: Option<usize>,
    pub kappa: F,
    pub kappa_x: F,
    pub role: &'static str,
}

/// One table's shape, from its AIR, its key and the configuration.
#[derive(Clone, Debug)]
pub struct TableShape {
    pub name: String,
    pub log_trace: usize,
    pub log_ext: usize,
    pub width: usize,
    pub num_public: usize,
    pub preprocessed_width: usize,
    pub perm_width: usize,
    /// The global bus index of each of the table's lookups (two challenges each: the bus prefix and beta).
    pub lookup_bus: Vec<usize>,
    pub log_quotient_degree: usize,
    pub chunks: usize,
}

impl TableShape {
    /// The selectors' domain (C3n verifier/mod.rs l. 896-899: `natural_domain_for_degree(ext_size >> is_zk)`).
    pub fn init_domain(&self) -> TwoAdicMultiplicativeCoset<F> {
        TwoAdicMultiplicativeCoset::new(F::ONE, self.log_trace).unwrap()
    }
    /// The quotient chunk domains (verifier/mod.rs l. 256-286): the committed trace domain's disjoint coset of size
    /// 2^(log_ext + log_quotient_degree), split into `chunks` domains.
    pub fn chunk_domains(&self) -> Vec<TwoAdicMultiplicativeCoset<F>> {
        let trace = TwoAdicMultiplicativeCoset::new(F::ONE, self.log_ext).unwrap();
        let q = trace.try_create_disjoint_domain(1usize << (self.log_ext + self.log_quotient_degree)).unwrap();
        q.split_domains(self.chunks)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum CVal {
    Plain(usize),
    Factored(Sel, usize),
}

#[derive(Clone, Debug, Default)]
pub struct TableOut {
    pub z_h: usize,
    pub inv_vanishing: usize,
    pub is_first_row: usize,
    pub is_last_row: usize,
    pub is_transition: usize,
    /// Every constraint's value (base constraints first, then the extension constraints).
    pub constraints: Vec<Option<CVal>>,
    pub base_constraints: usize,
    /// The permutation columns' values at (column, offset).
    pub perm_values: Vec<(usize, usize, usize)>,
    pub folded: usize,
    pub chunk_vanishing: Vec<usize>,
    pub zps: Vec<usize>,
    pub chunk_values: Vec<usize>,
    pub quotient: usize,
    pub identity_lhs: usize,
    pub identity: usize,
}

#[derive(Clone)]
pub struct Program {
    pub shapes: Vec<TableShape>,
    pub tables: Vec<TableOut>,
    pub n_values: usize,
    pub inputs: Vec<(usize, Input)>,
    pub instrs: Vec<PIns>,
    pub zeta_powers: Vec<usize>,
    pub gamma: Option<usize>,
    pub prefixes: Vec<usize>,
    pub terminal_sum: Option<usize>,
    pub terminal_check: usize,
    pub constants: Vec<(usize, F, F)>,
    pub stats: Value,
    pub runs: Vec<(usize, usize, usize, Sel)>,
    pub num_buses: usize,
    pub max_message_width: usize,
}

// ---------- the intermediate representation: a hash-consed DAG over EF8 values ----------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Node {
    In(Input),
    Sel(usize, Sel),
    /// Table t's permutation column j at row offset o (an EF8 value from 8 claimed coordinates).
    Perm(usize, usize, usize),
    /// Table t's permutation challenge i (2c: the bus prefix of lookup c; 2c + 1: beta).
    Chal(usize, usize),
    /// An EF8 constant kappa + kappa_x X.
    Const(u32, u32),
    Add(usize, usize),
    Sub(usize, usize),
    Neg(usize),
    Mul(usize, usize),
}

#[derive(Default)]
struct Ir {
    nodes: Vec<Node>,
    index: HashMap<Node, usize>,
}

impl Ir {
    fn intern(&mut self, n: Node) -> usize {
        let n = match n {
            Node::Add(a, b) if a > b => Node::Add(b, a),
            Node::Mul(a, b) if a > b => Node::Mul(b, a),
            x => x,
        };
        if let Some(&i) = self.index.get(&n) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push(n);
        self.index.insert(n, i);
        i
    }
    /// A base-field constant node (kappa_x = 0).
    fn konst(&self, i: usize) -> Option<F> {
        match self.nodes[i] {
            Node::Const(c, 0) => Some(F::from_u32(c)),
            _ => None,
        }
    }
    fn kc(&mut self, v: F) -> usize {
        self.intern(Node::Const(v.as_canonical_u32(), 0))
    }
    fn add(&mut self, a: usize, b: usize) -> usize {
        match (self.konst(a), self.konst(b)) {
            (Some(p), Some(q)) => self.kc(p + q),
            (Some(p), _) if p == F::ZERO => b,
            (_, Some(q)) if q == F::ZERO => a,
            _ => self.intern(Node::Add(a, b)),
        }
    }
    fn sub(&mut self, a: usize, b: usize) -> usize {
        match (self.konst(a), self.konst(b)) {
            (Some(p), Some(q)) => self.kc(p - q),
            (_, Some(q)) if q == F::ZERO => a,
            _ => self.intern(Node::Sub(a, b)),
        }
    }
    fn neg(&mut self, a: usize) -> usize {
        match (self.konst(a), self.nodes[a]) {
            (Some(p), _) => self.kc(-p),
            (_, Node::Neg(z)) => z,
            _ => self.intern(Node::Neg(a)),
        }
    }
    fn mul(&mut self, a: usize, b: usize) -> usize {
        match (self.konst(a), self.konst(b)) {
            (Some(p), Some(q)) => self.kc(p * q),
            (Some(p), _) if p == F::ONE => b,
            (_, Some(q)) if q == F::ONE => a,
            (Some(p), _) | (_, Some(p)) if p == F::ZERO => self.kc(F::ZERO),
            _ => self.intern(Node::Mul(a, b)),
        }
    }

    /// Lower one base expression of table t, memoized on node identity (the DAG shares `Arc` children).
    fn lower(&mut self, t: usize, e: &SymbolicExpression<F>, memo: &mut HashMap<*const SymbolicExpression<F>, usize>) -> usize {
        let key = e as *const _;
        if let Some(&i) = memo.get(&key) {
            return i;
        }
        let i = match e {
            SymbolicExpr::Leaf(leaf) => match leaf {
                BaseLeaf::Variable(v) => match v.entry {
                    BaseEntry::Main { offset: 0 } => self.intern(Node::In(Input::TraceLocal(t, v.index))),
                    BaseEntry::Main { offset: 1 } => self.intern(Node::In(Input::TraceNext(t, v.index))),
                    BaseEntry::Preprocessed { offset: 0 } => self.intern(Node::In(Input::PreLocal(t, v.index))),
                    BaseEntry::Preprocessed { offset: 1 } => self.intern(Node::In(Input::PreNext(t, v.index))),
                    BaseEntry::Main { offset } | BaseEntry::Preprocessed { offset } => panic!("row offset {offset}: the window has two rows"),
                    BaseEntry::Public => self.intern(Node::In(Input::Public(t, v.index))),
                    BaseEntry::Periodic => self.intern(Node::In(Input::Periodic(t, v.index))),
                },
                BaseLeaf::IsFirstRow => self.intern(Node::Sel(t, Sel::First)),
                BaseLeaf::IsLastRow => self.intern(Node::Sel(t, Sel::Last)),
                BaseLeaf::IsTransition => self.intern(Node::Sel(t, Sel::Transition)),
                BaseLeaf::Constant(c) => self.kc(*c),
            },
            SymbolicExpr::Add { x, y, .. } => {
                let (a, b) = (self.lower(t, x, memo), self.lower(t, y, memo));
                self.add(a, b)
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, b) = (self.lower(t, x, memo), self.lower(t, y, memo));
                self.sub(a, b)
            }
            SymbolicExpr::Neg { x, .. } => {
                let a = self.lower(t, x, memo);
                self.neg(a)
            }
            SymbolicExpr::Mul { x, y, .. } => {
                let (a, b) = (self.lower(t, x, memo), self.lower(t, y, memo));
                self.mul(a, b)
            }
        };
        memo.insert(key, i);
        i
    }

    /// Lower one extension expression of table t.
    fn lower_ext(
        &mut self,
        t: usize,
        e: &SymbolicExpressionExt<F, EF>,
        memo: &mut HashMap<*const SymbolicExpressionExt<F, EF>, usize>,
        bmemo: &mut HashMap<*const SymbolicExpression<F>, usize>,
    ) -> usize {
        let key = e as *const _;
        if let Some(&i) = memo.get(&key) {
            return i;
        }
        let i = match e {
            SymbolicExpr::Leaf(leaf) => match leaf {
                ExtLeaf::Base(b) => self.lower(t, b, bmemo),
                ExtLeaf::ExtVariable(v) => match v.entry {
                    ExtEntry::Permutation { offset } => {
                        assert!(offset <= 1, "permutation row offset {offset}");
                        self.intern(Node::Perm(t, v.index, offset))
                    }
                    ExtEntry::Challenge => self.intern(Node::Chal(t, v.index)),
                    ExtEntry::PermutationValue => {
                        assert_eq!(v.index, 0, "one terminal per table with lookups");
                        self.intern(Node::In(Input::Terminal(t)))
                    }
                },
                ExtLeaf::ExtConstant(c) => {
                    let co: &[F] = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(c);
                    assert!(co[2..].iter().all(|x| *x == F::ZERO), "extension constant {c:?}: only kappa + kappa_x X is an ALU constant");
                    self.intern(Node::Const(co[0].as_canonical_u32(), co[1].as_canonical_u32()))
                }
            },
            SymbolicExpr::Add { x, y, .. } => {
                let (a, b) = (self.lower_ext(t, x, memo, bmemo), self.lower_ext(t, y, memo, bmemo));
                self.add(a, b)
            }
            SymbolicExpr::Sub { x, y, .. } => {
                let (a, b) = (self.lower_ext(t, x, memo, bmemo), self.lower_ext(t, y, memo, bmemo));
                self.sub(a, b)
            }
            SymbolicExpr::Neg { x, .. } => {
                let a = self.lower_ext(t, x, memo, bmemo);
                self.neg(a)
            }
            SymbolicExpr::Mul { x, y, .. } => {
                let (a, b) = (self.lower_ext(t, x, memo, bmemo), self.lower_ext(t, y, memo, bmemo));
                self.mul(a, b)
            }
        };
        memo.insert(key, i);
        i
    }

    fn children(&self, i: usize) -> Vec<usize> {
        match self.nodes[i] {
            Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => vec![a, b],
            Node::Neg(a) => vec![a],
            _ => vec![],
        }
    }
}

/// The arithmetic operations the AIR's evaluation executes (K3b's count: the symbolic DAG's operator nodes, a value
/// clone counted once), over the base and the extension constraints.
pub fn executed_ops(base: &[SymbolicExpression<F>], ext: &[SymbolicExpressionExt<F, EF>]) -> BTreeMap<&'static str, usize> {
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut seen: HashSet<(u8, usize, usize)> = HashSet::new();
    let mut visited: HashSet<usize> = HashSet::new();
    let mut stack: Vec<&SymbolicExpression<F>> = base.iter().collect();
    let mut ext_stack: Vec<&SymbolicExpressionExt<F, EF>> = ext.iter().collect();
    let p = |k: Option<usize>| k.unwrap_or(0);
    while let Some(e) = ext_stack.pop() {
        if !visited.insert(e as *const _ as usize) {
            continue;
        }
        let (kind, name, kids): (u8, &str, Vec<usize>) = match e {
            SymbolicExpr::Leaf(ExtLeaf::Base(b)) => {
                stack.push(b);
                continue;
            }
            SymbolicExpr::Leaf(_) => continue,
            SymbolicExpr::Add { x, y, .. } => {
                ext_stack.push(x);
                ext_stack.push(y);
                (4, "add", vec![Arc::as_ptr(x) as usize, Arc::as_ptr(y) as usize])
            }
            SymbolicExpr::Sub { x, y, .. } => {
                ext_stack.push(x);
                ext_stack.push(y);
                (5, "sub", vec![Arc::as_ptr(x) as usize, Arc::as_ptr(y) as usize])
            }
            SymbolicExpr::Neg { x, .. } => {
                ext_stack.push(x);
                (6, "neg", vec![Arc::as_ptr(x) as usize])
            }
            SymbolicExpr::Mul { x, y, .. } => {
                ext_stack.push(x);
                ext_stack.push(y);
                (7, "mul", vec![Arc::as_ptr(x) as usize, Arc::as_ptr(y) as usize])
            }
        };
        if seen.insert((kind, p(kids.first().copied()), p(kids.get(1).copied()))) {
            *counts.entry(name).or_default() += 1;
        }
    }
    while let Some(e) = stack.pop() {
        if !visited.insert(e as *const _ as usize) {
            continue;
        }
        let (kind, name, kids): (u8, &str, Vec<&Arc<SymbolicExpression<F>>>) = match e {
            SymbolicExpr::Leaf(_) => continue,
            SymbolicExpr::Add { x, y, .. } => (0, "add", vec![x, y]),
            SymbolicExpr::Sub { x, y, .. } => (1, "sub", vec![x, y]),
            SymbolicExpr::Neg { x, .. } => (2, "neg", vec![x]),
            SymbolicExpr::Mul { x, y, .. } => (3, "mul", vec![x, y]),
        };
        let pp = |k: Option<&&Arc<SymbolicExpression<F>>>| k.map(|a| Arc::as_ptr(a) as usize).unwrap_or(0);
        if seen.insert((kind, pp(kids.first()), pp(kids.get(1)))) {
            *counts.entry(name).or_default() += 1;
        }
        for k in kids {
            stack.push(k);
        }
    }
    counts
}

// ---------- the program builder ----------

struct Pb {
    n_values: usize,
    inputs: Vec<(usize, Input)>,
    input_ids: HashMap<Input, usize>,
    instrs: Vec<PIns>,
    consts: HashMap<(u32, u32), usize>,
    constants: Vec<(usize, F, F)>,
    role: &'static str,
}

impl Pb {
    fn fresh(&mut self) -> usize {
        self.n_values += 1;
        self.n_values - 1
    }
    fn input(&mut self, i: Input) -> usize {
        if let Some(&v) = self.input_ids.get(&i) {
            return v;
        }
        let v = self.fresh();
        self.inputs.push((v, i));
        self.input_ids.insert(i, v);
        v
    }
    fn push(&mut self, op: POp, a: Option<usize>, b: Option<usize>, c: Option<usize>, kappa: F, kappa_x: F, result: bool) -> Option<usize> {
        let r = result.then(|| self.fresh());
        self.instrs.push(PIns { op, r, a, b, c, kappa, kappa_x, role: self.role });
        r
    }
    fn konst(&mut self, k: F, kx: F) -> usize {
        let key = (k.as_canonical_u32(), kx.as_canonical_u32());
        if let Some(&v) = self.consts.get(&key) {
            return v;
        }
        let saved = self.role;
        self.role = "eval.const";
        let v = self.push(POp::Const, None, None, None, k, kx, true).unwrap();
        self.role = saved;
        self.consts.insert(key, v);
        self.constants.push((v, k, kx));
        v
    }
    fn mul(&mut self, a: usize, b: usize) -> usize {
        self.push(POp::Mul, Some(a), Some(b), None, F::ZERO, F::ZERO, true).unwrap()
    }
    fn mac(&mut self, a: usize, b: usize, c: usize) -> usize {
        self.push(POp::Mac, Some(a), Some(b), Some(c), F::ZERO, F::ZERO, true).unwrap()
    }
    fn lin(&mut self, a: usize, b: usize, kappa: F) -> usize {
        self.push(POp::Lin, Some(a), Some(b), None, kappa, F::ZERO, true).unwrap()
    }
    fn inv(&mut self, a: usize) -> usize {
        self.push(POp::Inv, Some(a), None, None, F::ZERO, F::ZERO, true).unwrap()
    }
    fn eq(&mut self, a: usize, b: usize) -> usize {
        self.push(POp::Eq, Some(a), Some(b), None, F::ZERO, F::ZERO, false);
        self.instrs.len() - 1
    }
    /// sum_k X^k v_k by Horner in the constant X (the native `from_ext_basis_coefficients`).
    fn compose(&mut self, coords: &[usize]) -> usize {
        let x_basis = self.konst(F::ZERO, F::ONE);
        let mut h = coords[coords.len() - 1];
        for k in (0..coords.len() - 1).rev() {
            h = self.mac(h, x_basis, coords[k]);
        }
        h
    }
}

struct Emitter<'a> {
    ir: &'a Ir,
    uses: Vec<u32>,
    val: Vec<Option<usize>>,
    /// Per table: the selector values and the permutation challenges' values.
    sel: Vec<[usize; 3]>,
    chal: Vec<Vec<usize>>,
    one: usize,
    pb: Pb,
}

fn sel_index(s: Sel) -> usize {
    match s {
        Sel::First => 0,
        Sel::Last => 1,
        Sel::Transition => 2,
    }
}

impl<'a> Emitter<'a> {
    fn single(&self, n: usize) -> bool {
        self.uses[n] == 1 && self.val[n].is_none()
    }
    fn scaled(&self, n: usize) -> Option<(usize, F)> {
        match self.ir.nodes[n] {
            Node::Mul(p, q) => match (self.ir.konst(p), self.ir.konst(q)) {
                (Some(k), None) => Some((q, k)),
                (None, Some(k)) => Some((p, k)),
                _ => None,
            },
            _ => None,
        }
    }
    fn product(&self, n: usize) -> Option<(usize, usize)> {
        match self.ir.nodes[n] {
            Node::Mul(p, q) if self.ir.konst(p).is_none() && self.ir.konst(q).is_none() => Some((p, q)),
            _ => None,
        }
    }

    fn emit(&mut self, n: usize) -> usize {
        if let Some(v) = self.val[n] {
            return v;
        }
        let v = match self.ir.nodes[n] {
            Node::In(i) => self.pb.input(i),
            Node::Sel(t, s) => self.sel[t][sel_index(s)],
            Node::Chal(t, i) => self.chal[t][i],
            Node::Perm(t, j, o) => {
                let saved = self.pb.role;
                self.pb.role = "eval.permutation_value";
                let coords: Vec<usize> = (0..8).map(|k| self.pb.input(if o == 0 { Input::PermLocal(t, j, k) } else { Input::PermNext(t, j, k) })).collect();
                let v = self.pb.compose(&coords);
                self.pb.role = saved;
                v
            }
            Node::Const(c, cx) => self.pb.konst(F::from_u32(c), F::from_u32(cx)),
            Node::Add(a, b) => self.emit_add(a, b, F::ONE),
            Node::Sub(a, b) => self.emit_add(a, b, F::NEG_ONE),
            Node::Neg(a) => self.emit_scale(a, F::NEG_ONE),
            Node::Mul(a, b) => match (self.ir.konst(a), self.ir.konst(b)) {
                (Some(k), None) => self.emit_scale(b, k),
                (None, Some(k)) => self.emit_scale(a, k),
                _ => {
                    let (va, vb) = (self.emit(a), self.emit(b));
                    self.pb.mul(va, vb)
                }
            },
        };
        self.val[n] = Some(v);
        v
    }

    /// a + s b, with a single-use operand fused when it is a product (MAC), a scaled value or a negation (LIN).
    fn emit_add(&mut self, a: usize, b: usize, s: F) -> usize {
        if let Some(kb) = self.ir.konst(b) {
            let va = self.emit(a);
            return self.pb.lin(va, self.one, s * kb);
        }
        if let Some(ka) = self.ir.konst(a) {
            if s == F::ONE {
                let vb = self.emit(b);
                return self.pb.lin(vb, self.one, ka);
            }
            let (kv, vb) = (self.pb.konst(ka, F::ZERO), self.emit(b));
            return self.pb.lin(kv, vb, s);
        }
        if self.single(b) {
            if s == F::ONE {
                if let Some((p, q)) = self.product(b) {
                    let (vp, vq, va) = (self.emit(p), self.emit(q), self.emit(a));
                    return self.pb.mac(vp, vq, va);
                }
            }
            if let Some((y, k)) = self.scaled(b) {
                let (va, vy) = (self.emit(a), self.emit(y));
                return self.pb.lin(va, vy, s * k);
            }
            if let Node::Neg(y) = self.ir.nodes[b] {
                let (va, vy) = (self.emit(a), self.emit(y));
                return self.pb.lin(va, vy, -s);
            }
        }
        if s == F::ONE && self.single(a) {
            if let Some((p, q)) = self.product(a) {
                let (vp, vq, vb) = (self.emit(p), self.emit(q), self.emit(b));
                return self.pb.mac(vp, vq, vb);
            }
            if let Some((y, k)) = self.scaled(a) {
                let (vb, vy) = (self.emit(b), self.emit(y));
                return self.pb.lin(vb, vy, k);
            }
            if let Node::Neg(y) = self.ir.nodes[a] {
                let (vb, vy) = (self.emit(b), self.emit(y));
                return self.pb.lin(vb, vy, F::NEG_ONE);
            }
        }
        let (va, vb) = (self.emit(a), self.emit(b));
        self.pb.lin(va, vb, s)
    }

    /// k a (k a constant other than 0 and 1): LIN(a, a, k - 1) = a + (k - 1) a.
    fn emit_scale(&mut self, a: usize, k: F) -> usize {
        if self.single(a) {
            if let Some((y, k2)) = self.scaled(a) {
                return self.emit_scale(y, k * k2);
            }
            if let Node::Neg(y) = self.ir.nodes[a] {
                return self.emit_scale(y, -k);
            }
        }
        let va = self.emit(a);
        if k == F::ONE {
            return va;
        }
        self.pb.lin(va, va, k - F::ONE)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Options {
    pub factor_min: usize,
}
impl Default for Options {
    fn default() -> Self {
        Options { factor_min: 3 }
    }
}

/// One table's constraints as the compiler takes them.
pub struct TableConstraints<'a> {
    pub base: &'a [SymbolicExpression<F>],
    pub ext: &'a [SymbolicExpressionExt<F, EF>],
}

/// Compile the batch child's constraint identities at zeta and the global terminal check.
pub fn compile(shapes: &[TableShape], cons: &[TableConstraints], num_buses: usize, max_message_width: usize, opts: Options) -> Program {
    assert_eq!(shapes.len(), cons.len());
    // ---- lower every table to the hash-consed DAG ----
    let mut ir = Ir::default();
    let mut roots: Vec<Vec<usize>> = vec![];
    for (t, tc) in cons.iter().enumerate() {
        let mut bmemo = HashMap::new();
        let mut emo = HashMap::new();
        let mut r: Vec<usize> = tc.base.iter().map(|c| ir.lower(t, c, &mut bmemo)).collect();
        r.extend(tc.ext.iter().map(|c| ir.lower_ext(t, c, &mut emo, &mut bmemo)));
        roots.push(r);
    }
    let mut uses = vec![0u32; ir.nodes.len()];
    for i in 0..ir.nodes.len() {
        for ch in ir.children(i) {
            uses[ch] += 1;
        }
    }
    for r in roots.iter().flatten() {
        uses[*r] += 1;
    }
    let mut node_kinds: BTreeMap<&str, usize> = BTreeMap::new();
    for n in &ir.nodes {
        let k = match n {
            Node::In(_) => "input",
            Node::Sel(..) => "selector",
            Node::Perm(..) => "permutation_value",
            Node::Chal(..) => "lookup_challenge",
            Node::Const(..) => "constant",
            Node::Add(..) => "add",
            Node::Sub(..) => "sub",
            Node::Neg(_) => "neg",
            Node::Mul(..) => "mul",
        };
        *node_kinds.entry(k).or_default() += 1;
    }
    let mut pb = Pb { n_values: 0, inputs: vec![], input_ids: HashMap::new(), instrs: vec![], consts: HashMap::new(), constants: vec![], role: "eval.const" };
    // ---- the shared part: constants, zeta's powers, the lookup challenges ----
    let one = pb.konst(F::ONE, F::ZERO);
    let zeta = pb.input(Input::Zeta);
    let top = shapes.iter().map(|s| s.log_trace.max(s.chunk_domains()[0].log_size())).max().unwrap();
    pb.role = "eval.zeta_power";
    let mut zp = vec![zeta];
    for _ in 0..top {
        let last = *zp.last().unwrap();
        zp.push(pb.mul(last, last));
    }
    let any_lookups = shapes.iter().any(|s| s.perm_width > 0);
    let (mut gamma, mut prefixes, mut beta_l) = (None, vec![], None);
    if any_lookups {
        pb.role = "eval.lookup_challenge";
        let la = pb.input(Input::LookupAlpha);
        let lb = pb.input(Input::LookupBeta);
        // gamma = beta^W by squarings and the binary expansion of W (challenges.rs l. 74-75).
        let w = max_message_width;
        let mut pw: BTreeMap<usize, usize> = BTreeMap::new();
        pw.insert(1, lb);
        let mut p = 1;
        while 2 * p <= w {
            let v = pb.mul(pw[&p], pw[&p]);
            pw.insert(2 * p, v);
            p *= 2;
        }
        let bits: Vec<usize> = (0..usize::BITS as usize).filter(|b| w >> b & 1 == 1).map(|b| 1usize << b).rev().collect();
        let mut acc = bits[0];
        for &b in &bits[1..] {
            let nxt = acc + b;
            if !pw.contains_key(&nxt) {
                let v = pb.mul(pw[&acc], pw[&b]);
                pw.insert(nxt, v);
            }
            acc = nxt;
        }
        let g = pw[&w];
        gamma = Some(g);
        // prefix[b] = alpha + (b + 1) gamma (challenges.rs l. 77-84).
        for b in 0..num_buses {
            prefixes.push(pb.lin(la, g, F::from_usize(b + 1)));
        }
        beta_l = Some(lb);
    }
    // ---- per table: selectors, permutation challenges ----
    let mut sel = vec![];
    let mut chal = vec![];
    let mut outs: Vec<TableOut> = vec![];
    for s in shapes {
        pb.role = "eval.selectors";
        let init = s.init_domain();
        assert!(init.shift() == F::ONE, "the selectors' domain has shift 1");
        let z_h = pb.lin(zp[s.log_trace], one, F::NEG_ONE);
        pb.role = "eval.zeta_not_in_domain";
        let inv_vanishing = pb.inv(z_h);
        pb.role = "eval.selectors";
        let d_first = pb.lin(zeta, one, F::NEG_ONE);
        let i_first = pb.inv(d_first);
        let is_first_row = pb.mul(z_h, i_first);
        let w_inv = init.subgroup_generator().inverse();
        let is_transition = pb.lin(zeta, one, -w_inv);
        let i_last = pb.inv(is_transition);
        let is_last_row = pb.mul(z_h, i_last);
        sel.push([is_first_row, is_last_row, is_transition]);
        chal.push(s.lookup_bus.iter().flat_map(|&b| [prefixes[b], beta_l.unwrap()]).collect::<Vec<usize>>());
        outs.push(TableOut { z_h, inv_vanishing, is_first_row, is_last_row, is_transition, ..Default::default() });
    }
    // ---- per table: the constraints and the folding, the recomposition and the identity ----
    let alpha = pb.input(Input::Alpha);
    let mut em = Emitter { ir: &ir, uses, val: vec![None; ir.nodes.len()], sel, chal, one, pb };
    let factor_of = |r: usize| -> Option<(Sel, usize)> {
        match ir.nodes[r] {
            Node::Mul(p, q) => match (ir.nodes[p], ir.nodes[q]) {
                (Node::Sel(_, s), other) if !matches!(other, Node::Sel(..)) => Some((s, q)),
                (other, Node::Sel(_, s)) if !matches!(other, Node::Sel(..)) => Some((s, p)),
                _ => None,
            },
            _ => None,
        }
    };
    let mut alpha_pow: HashMap<usize, usize> = HashMap::new();
    alpha_pow.insert(1, alpha);
    let mut runs = vec![];
    for (t, s) in shapes.iter().enumerate() {
        let rt = &roots[t];
        let n = rt.len();
        let mut cvals: Vec<Option<CVal>> = vec![None; n];
        let mut acc: Option<usize> = None;
        let mut k = 0;
        while k < n {
            let f = if opts.factor_min > 0 { factor_of(rt[k]) } else { None };
            let mut end = k + 1;
            if let Some((sl, _)) = f {
                while end < n && factor_of(rt[end]).map(|x| x.0) == Some(sl) {
                    end += 1;
                }
            }
            if let (Some((sl, _)), true) = (f, end - k >= opts.factor_min.max(1) && opts.factor_min > 0) {
                let m = end - k;
                let mut h: Option<usize> = None;
                for j in k..end {
                    let (_, tt) = factor_of(rt[j]).unwrap();
                    em.pb.role = "eval.constraint";
                    let vt = em.emit(tt);
                    cvals[j] = Some(CVal::Factored(sl, vt));
                    em.pb.role = "eval.fold";
                    h = Some(match h {
                        None => vt,
                        Some(hv) => em.pb.mac(hv, alpha, vt),
                    });
                }
                em.pb.role = "eval.fold";
                let sv = em.sel[t][sel_index(sl)];
                let p = em.pb.mul(sv, h.unwrap());
                acc = Some(match acc {
                    None => p,
                    Some(a) => {
                        let am = alpha_power(&mut em.pb, &mut alpha_pow, m);
                        em.pb.role = "eval.fold";
                        em.pb.mac(a, am, p)
                    }
                });
                runs.push((t, k, m, sl));
                k = end;
                continue;
            }
            em.pb.role = "eval.constraint";
            let c = em.emit(rt[k]);
            cvals[k] = Some(CVal::Plain(c));
            em.pb.role = "eval.fold";
            acc = Some(match acc {
                None => c,
                Some(a) => em.pb.mac(a, alpha, c),
            });
            k += 1;
        }
        let folded = acc.expect("at least one constraint");
        // The permutation values the program computed (for the native cross-check).
        let mut perm_values = vec![];
        for (i, nd) in ir.nodes.iter().enumerate() {
            if let Node::Perm(tt, j, o) = *nd {
                if tt == t {
                    if let Some(v) = em.val[i] {
                        perm_values.push((j, o, v));
                    }
                }
            }
        }
        // ---- the quotient recomposition (p3-uni-stark verifier.rs l. 73-110 through recompose_quotient_from_chunks) ----
        let pb = &mut em.pb;
        pb.role = "eval.recompose";
        let minus_one = pb.konst(F::NEG_ONE, F::ZERO);
        let chunk_domains = s.chunk_domains();
        let chunk_log = chunk_domains[0].log_size();
        assert!(chunk_domains.iter().all(|d| d.log_size() == chunk_log));
        // Z_{D_j}(zeta) = (zeta s_j^-1)^(2^l) - 1 = -1 + (s_j^-1)^(2^l) zeta^(2^l) (p3-commit domain.rs l. 315-317).
        let zv: Vec<usize> = chunk_domains.iter().map(|d| pb.lin(minus_one, zp[chunk_log], d.shift_inverse().exp_power_of_2(chunk_log))).collect();
        let nc = chunk_domains.len();
        let mut prefix = vec![usize::MAX; nc + 1];
        let mut suffix = vec![usize::MAX; nc + 1];
        if nc >= 2 {
            prefix[1] = zv[0];
            for i in 2..nc {
                prefix[i] = pb.mul(prefix[i - 1], zv[i - 1]);
            }
            suffix[nc - 2] = zv[nc - 1];
            for i in (0..nc - 2).rev() {
                suffix[i] = pb.mul(zv[i + 1], suffix[i + 1]);
            }
        }
        let mut zps = vec![];
        for (i, d) in chunk_domains.iter().enumerate() {
            let mut kinv = F::ONE;
            for (j, o) in chunk_domains.iter().enumerate() {
                if j != i {
                    kinv *= o.vanishing_poly_at_point::<F>(d.first_point()).inverse();
                }
            }
            let prod = if nc == 1 {
                one
            } else if i == 0 {
                suffix[0]
            } else if i == nc - 1 {
                prefix[nc - 1]
            } else {
                pb.mul(prefix[i], suffix[i])
            };
            zps.push(if kinv == F::ONE { prod } else { pb.lin(prod, prod, kinv - F::ONE) });
        }
        let ext = <EF as BasedVectorSpace<F>>::DIMENSION;
        let mut qv = vec![];
        for c in 0..nc {
            let coords: Vec<usize> = (0..ext).map(|kk| pb.input(Input::Chunk(t, c, kk))).collect();
            qv.push(pb.compose(&coords));
        }
        let mut quotient = pb.mul(zps[0], qv[0]);
        for c in 1..nc {
            quotient = pb.mac(zps[c], qv[c], quotient);
        }
        pb.role = "eval.identity";
        let lhs = pb.mul(folded, outs[t].inv_vanishing);
        let identity = pb.eq(lhs, quotient);
        let o = &mut outs[t];
        o.constraints = cvals;
        o.base_constraints = cons[t].base.len();
        o.perm_values = perm_values;
        o.folded = folded;
        o.chunk_vanishing = zv;
        o.zps = zps;
        o.chunk_values = qv;
        o.quotient = quotient;
        o.identity_lhs = lhs;
        o.identity = identity;
    }
    // ---- the global lookup terminal check: the terminals sum to zero (logup.rs l. 461-478) ----
    let mut pb = em.pb;
    pb.role = "eval.terminal_sum";
    let lookup_tables: Vec<usize> = (0..shapes.len()).filter(|&t| shapes[t].perm_width > 0).collect();
    let (terminal_sum, terminal_check) = if lookup_tables.is_empty() {
        (None, usize::MAX)
    } else {
        let mut s = pb.input(Input::Terminal(lookup_tables[0]));
        for &t in &lookup_tables[1..] {
            let tv = pb.input(Input::Terminal(t));
            s = pb.lin(s, tv, F::ONE);
        }
        let zero = pb.konst(F::ZERO, F::ZERO);
        (Some(s), pb.eq(s, zero))
    };
    // ---- statistics ----
    let mut by_op: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_role: BTreeMap<&str, usize> = BTreeMap::new();
    for i in &pb.instrs {
        *by_op.entry(i.op.name()).or_default() += 1;
        *by_role.entry(i.role).or_default() += 1;
    }
    let per_table: Vec<Value> = shapes
        .iter()
        .zip(cons)
        .map(|(s, c)| {
            let ex = executed_ops(c.base, c.ext);
            json!({"table": s.name, "base_constraints": c.base.len(), "extension_constraints": c.ext.len(),
                "max_degree_base": c.base.iter().map(|x| x.degree_multiple()).max().unwrap_or(0),
                "max_degree_extension": c.ext.iter().map(|x| x.degree_multiple()).max().unwrap_or(0),
                "symbolic_executed_ops": ex, "symbolic_executed_ops_total": ex.values().sum::<usize>(),
                "chunks": s.chunks, "log_trace": s.log_trace})
        })
        .collect();
    let executed_total: usize = cons.iter().map(|c| executed_ops(c.base, c.ext).values().sum::<usize>()).sum();
    let n_constraints: usize = cons.iter().map(|c| c.base.len() + c.ext.len()).sum();
    let (live_max, live_at) = live_values(&pb.instrs, pb.n_values, &pb.inputs);
    let constraint_instr = by_role.get("eval.constraint").copied().unwrap_or(0);
    let stats = json!({
        "tables": per_table, "constraints": n_constraints,
        "factored_runs": runs.iter().map(|(t, k, m, s)| json!({"table": t, "first": k, "len": m, "selector": s.name()})).collect::<Vec<_>>(),
        "dag_nodes": node_kinds, "inputs_read": pb.inputs.len(),
        "instructions": pb.instrs.len(), "by_opcode": by_op, "by_role": by_role, "values": pb.n_values,
        "symbolic_executed_ops_total": executed_total, "native_folder_ops_model": executed_total + 2 * n_constraints,
        "constraint_instructions_per_executed_op": constraint_instr as f64 / executed_total.max(1) as f64,
        "live_values_max": live_max, "live_values_max_at_instruction": live_at,
    });
    Program {
        shapes: shapes.to_vec(),
        tables: outs,
        n_values: pb.n_values,
        inputs: pb.inputs,
        instrs: pb.instrs,
        zeta_powers: zp,
        gamma,
        prefixes,
        terminal_sum,
        terminal_check,
        constants: pb.constants,
        stats,
        runs,
        num_buses,
        max_message_width,
    }
}

/// alpha^m by squarings and the binary expansion of m (shared between runs).
fn alpha_power(pb: &mut Pb, have: &mut HashMap<usize, usize>, m: usize) -> usize {
    if let Some(&v) = have.get(&m) {
        return v;
    }
    let saved = pb.role;
    pb.role = "eval.alpha_power";
    let mut p = 1usize;
    while 2 * p <= m {
        if !have.contains_key(&(2 * p)) {
            let h = have[&p];
            let v = pb.mul(h, h);
            have.insert(2 * p, v);
        }
        p *= 2;
    }
    let bits: Vec<usize> = (0..usize::BITS as usize).filter(|b| m >> b & 1 == 1).map(|b| 1usize << b).rev().collect();
    let mut acc = bits[0];
    for &b in &bits[1..] {
        let nxt = acc + b;
        if !have.contains_key(&nxt) {
            let (x, y) = (have[&acc], have[&b]);
            let v = pb.mul(x, y);
            have.insert(nxt, v);
        }
        acc = nxt;
    }
    pb.role = saved;
    have[&m]
}

/// The largest number of intermediate values alive at once in program order, and where it peaks.
fn live_values(instrs: &[PIns], n_values: usize, inputs: &[(usize, Input)]) -> (usize, usize) {
    let mut def = vec![usize::MAX; n_values];
    let mut last = vec![usize::MAX; n_values];
    let is_input: HashSet<usize> = inputs.iter().map(|(v, _)| *v).collect();
    for (i, ins) in instrs.iter().enumerate() {
        if let Some(r) = ins.r {
            def[r] = i;
        }
        for v in [ins.a, ins.b, ins.c].into_iter().flatten() {
            last[v] = i;
        }
    }
    let mut delta = vec![0i64; instrs.len() + 1];
    for v in 0..n_values {
        if is_input.contains(&v) || def[v] == usize::MAX || last[v] == usize::MAX || instrs[def[v]].op == POp::Const {
            continue;
        }
        delta[def[v]] += 1;
        delta[last[v]] -= 1;
    }
    let (mut cur, mut best, mut at) = (0i64, 0i64, 0usize);
    for (i, d) in delta.iter().enumerate() {
        cur += d;
        if cur > best {
            best = cur;
            at = i;
        }
    }
    (best as usize, at)
}

impl Program {
    /// Evaluate the program natively over EF8 (the reference evaluation for the differential test and the kernel's
    /// cross-checks). Returns every value (None if unset or an inverse of zero) and the EQ results.
    pub fn eval(&self, input: &dyn Fn(Input) -> EF) -> (Vec<Option<EF>>, Vec<(usize, bool)>) {
        let mut v: Vec<Option<EF>> = vec![None; self.n_values];
        for &(id, i) in &self.inputs {
            v[id] = Some(input(i));
        }
        let x = EF::from_basis_coefficients_fn(|k| if k == 1 { F::ONE } else { F::ZERO });
        let mut eqs = vec![];
        for (n, ins) in self.instrs.iter().enumerate() {
            let g = |o: Option<usize>| -> Option<EF> { o.and_then(|id| v[id]) };
            let step = || -> Option<EF> {
                match ins.op {
                    POp::Const => Some(EF::from(ins.kappa) + x * ins.kappa_x),
                    POp::Mul => Some(g(ins.a)? * g(ins.b)?),
                    POp::Mac => Some(g(ins.a)? * g(ins.b)? + g(ins.c)?),
                    POp::Lin => Some(g(ins.a)? + g(ins.b)? * ins.kappa),
                    POp::Inv => g(ins.a)?.try_inverse(),
                    POp::Eq => None,
                }
            };
            let res = step();
            if ins.op == POp::Eq {
                eqs.push((n, g(ins.a) == g(ins.b) && g(ins.a).is_some()));
            }
            if let Some(r) = ins.r {
                v[r] = res;
            }
        }
        (v, eqs)
    }

    /// The canonical program file (its SHA-256 enters the kernel's verifier-key digest).
    pub fn to_json(&self, child_vk: &str) -> Value {
        let u = |x: F| x.as_canonical_u32();
        let ins: Vec<Value> = self.instrs.iter().map(|i| json!([i.op.name(), i.r, i.a, i.b, i.c, u(i.kappa), u(i.kappa_x), i.role])).collect();
        let cv = |c: &Option<CVal>| match c {
            Some(CVal::Plain(v)) => json!({"value": v}),
            Some(CVal::Factored(s, v)) => json!({"selector": s.name(), "factor": v}),
            None => Value::Null,
        };
        let tables: Vec<Value> = self
            .shapes
            .iter()
            .enumerate()
            .map(|(t, s)| {
                json!({"table": t, "name": s.name, "log_trace": s.log_trace, "log_committed": s.log_ext, "width": s.width,
                    "public_values": s.num_public, "preprocessed_width": s.preprocessed_width, "permutation_width_ef8": s.perm_width,
                    "lookup_buses": s.lookup_bus, "log_quotient_degree": s.log_quotient_degree, "quotient_chunks": s.chunks,
                    "selector_domain": {"shift": u(s.init_domain().shift()), "log_size": s.log_trace, "generator": u(s.init_domain().subgroup_generator())},
                    "chunk_domains": s.chunk_domains().iter().map(|d| json!({"shift": u(d.shift()), "log_size": d.log_size()})).collect::<Vec<_>>()})
            })
            .collect();
        let outs: Vec<Value> = self
            .tables
            .iter()
            .map(|o| {
                json!({"z_h": o.z_h, "inv_vanishing": o.inv_vanishing, "is_first_row": o.is_first_row, "is_last_row": o.is_last_row,
                    "is_transition": o.is_transition, "base_constraints": o.base_constraints, "constraints": o.constraints.iter().map(cv).collect::<Vec<_>>(),
                    "permutation_values": o.perm_values, "folded": o.folded, "chunk_vanishing": o.chunk_vanishing, "zps": o.zps,
                    "chunk_values": o.chunk_values, "quotient": o.quotient, "identity_lhs": o.identity_lhs, "identity_instruction": o.identity})
            })
            .collect();
        json!({
            "schema": SCHEMA,
            "review": "loop-internal self-review; not independently reviewed",
            "format": {"instruction": "[opcode, result value id or null, operand a, operand b, operand c, kappa, kappa_x, role]",
                "semantics": {"const": "r = kappa + kappa_x X (X the EF8 basis element 1)", "mul": "r = a b", "mac": "r = a b + c",
                    "lin": "r = a + kappa b", "inv": "a r = 1 (no r for a = 0)", "eq": "a = b"},
                "values": "every value id is written once (an input or one instruction's result); field elements are canonical KoalaBear integers; X^8 = 3"},
            "child": {"vk_digest": child_vk, "tables": self.shapes.len()},
            "interface": {
                "tables": tables,
                "lookups": {"buses": self.num_buses, "max_message_width": self.max_message_width,
                    "rule": "gamma = beta_L^W; prefix[b] = alpha_L + (b + 1) gamma; lookup c of a table reads [prefix[bus(c)], beta_L]; one terminal per table with lookups; the terminals sum to zero"},
                "inputs": self.inputs.iter().map(|(v, i)| json!([v, i.describe()])).collect::<Vec<_>>()},
            "instructions": ins,
            "outputs": {"zeta_powers": self.zeta_powers, "gamma": self.gamma, "prefixes": self.prefixes, "tables": outs,
                "terminal_sum": self.terminal_sum, "terminal_check_instruction": self.terminal_check},
            "stats": self.stats,
        })
    }

    pub fn file_bytes(&self, child_vk: &str) -> Vec<u8> {
        serde_json::to_vec(&self.to_json(child_vk)).unwrap()
    }
}
