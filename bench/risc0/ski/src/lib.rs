//! The SKI reducers of the Lean development, ported for the zkVM benchmark.
//!
//! `step` and `run_f` port `step?` and `runF` (`Ski/Fuel.lean`): tree
//! rewriting, normal order, one contraction per call.  `Mach` ports the
//! write-once heap machine (`Ski/Heap.lean`): `mstep` is `Mach.mstep`,
//! `load` is `Mach.load`, `mrun_c` is `Mach.mrunC`.  The heap only grows,
//! so the port appends in place where Lean returns a new list.  The host
//! checks every port against the reference reducer's contraction counts.
//!
//! Values stay shared.  An `S` contraction duplicates its argument by
//! reference, so printing a result can take space exponential in the
//! reduction; `Shared` writes each distinct node once instead.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    S,
    K,
    I,
    App(Rc<Term>, Rc<Term>),
}

fn app(f: Rc<Term>, a: Rc<Term>) -> Rc<Term> {
    Rc::new(Term::App(f, a))
}

/// Parse the prefix form: `S`, `K`, `I`, and `` ` `` for application.
pub fn parse(src: &[u8]) -> Option<Rc<Term>> {
    // Open applications, innermost last: `None` awaits its function,
    // `Some(f)` its argument.
    let mut pending: Vec<Option<Rc<Term>>> = Vec::new();
    let mut i = 0;
    while i < src.len() {
        let leaf = match src[i] {
            b'`' => {
                pending.push(None);
                i += 1;
                continue;
            }
            b'S' => Rc::new(Term::S),
            b'K' => Rc::new(Term::K),
            b'I' => Rc::new(Term::I),
            _ => return None,
        };
        i += 1;
        let mut t = leaf;
        loop {
            match pending.pop() {
                None => return if i == src.len() { Some(t) } else { None },
                Some(None) => {
                    pending.push(Some(t));
                    break;
                }
                // `f` waited for its argument `t`; the application is
                // itself an operand.
                Some(Some(f)) => t = app(f, t),
            }
        }
    }
    None
}

/// `step?`: the contraction at the head of the spine.
pub fn step(t: &Rc<Term>) -> Option<Rc<Term>> {
    match &**t {
        Term::App(f, x) => match step(f) {
            Some(f2) => Some(app(f2, x.clone())),
            None => match &**f {
                Term::I => Some(x.clone()),
                Term::App(k, y) if matches!(**k, Term::K) => Some(y.clone()),
                Term::App(sy, z) => match &**sy {
                    Term::App(s, y) if matches!(**s, Term::S) => {
                        Some(app(app(y.clone(), x.clone()), app(z.clone(), x.clone())))
                    }
                    _ => None,
                },
                _ => None,
            },
        },
        _ => None,
    }
}

/// `runF`: at most `k` step-attempts, with the contraction count.
pub fn run_f(k: u64, t: Rc<Term>) -> Option<(Rc<Term>, u64)> {
    let mut t = t;
    let mut n = 0;
    for _ in 0..k {
        match step(&t) {
            None => return Some((t, n)),
            Some(t2) => {
                t = t2;
                n += 1;
            }
        }
    }
    None
}

#[derive(Clone, Copy, Debug)]
pub enum Cell {
    S,
    K,
    I,
    App(u32, u32),
    Nil,
    Cons(u32, u32),
}

pub struct Mach {
    pub heap: Vec<Cell>,
    pub hd: u32,
    pub stk: u32,
}

impl Mach {
    pub fn get(&self, a: u32) -> Option<Cell> {
        self.heap.get(a as usize).copied()
    }

    /// Write a cell at the counter, the heap's length.
    fn alloc(&mut self, c: Cell) -> u32 {
        let a = self.heap.len() as u32;
        self.heap.push(c);
        a
    }

    pub fn cons(&self, a: u32) -> Option<(u32, u32)> {
        match self.get(a) {
            Some(Cell::Cons(x, s)) => Some((x, s)),
            _ => None,
        }
    }

    /// `mstep`: one transition, or `None` at a weak head normal form.  On
    /// `Some`, reports whether the transition was a contraction
    /// (`isContraction`) rather than an unwind.
    pub fn mstep(&mut self) -> Option<bool> {
        match self.get(self.hd)? {
            Cell::App(f, x) => {
                let c = self.alloc(Cell::Cons(x, self.stk));
                self.hd = f;
                self.stk = c;
                Some(false)
            }
            Cell::I => {
                let (x, s) = self.cons(self.stk)?;
                self.hd = x;
                self.stk = s;
                Some(true)
            }
            Cell::K => {
                let (x, s1) = self.cons(self.stk)?;
                let (_, s2) = self.cons(s1)?;
                self.hd = x;
                self.stk = s2;
                Some(true)
            }
            Cell::S => {
                let (x, s1) = self.cons(self.stk)?;
                let (y, s2) = self.cons(s1)?;
                let (z, s3) = self.cons(s2)?;
                let yz = self.alloc(Cell::App(y, z));
                let c1 = self.alloc(Cell::Cons(yz, s3));
                let c2 = self.alloc(Cell::Cons(z, c1));
                self.hd = x;
                self.stk = c2;
                Some(true)
            }
            Cell::Nil | Cell::Cons(_, _) => None,
        }
    }

    /// `load`: the term's cells children first, then `nil` as the stack.
    pub fn load(t: &Term) -> Mach {
        let mut m = Mach { heap: Vec::new(), hd: 0, stk: 0 };
        // Post-order, as `build`: function, argument, then the application.
        enum Job<'a> {
            Visit(&'a Term),
            Join,
        }
        let mut jobs = vec![Job::Visit(t)];
        let mut addrs: Vec<u32> = Vec::new();
        while let Some(job) = jobs.pop() {
            match job {
                Job::Visit(Term::S) => addrs.push(m.alloc(Cell::S)),
                Job::Visit(Term::K) => addrs.push(m.alloc(Cell::K)),
                Job::Visit(Term::I) => addrs.push(m.alloc(Cell::I)),
                Job::Visit(Term::App(f, a)) => {
                    jobs.push(Job::Join);
                    jobs.push(Job::Visit(a));
                    jobs.push(Job::Visit(f));
                }
                Job::Join => {
                    let pa = addrs.pop().unwrap();
                    let pf = addrs.pop().unwrap();
                    addrs.push(m.alloc(Cell::App(pf, pa)));
                }
            }
        }
        m.hd = addrs.pop().unwrap();
        m.stk = m.alloc(Cell::Nil);
        m
    }

    /// `mrunC`: at most `k` transitions, counting contractions.
    pub fn mrun_c(&mut self, k: u64) -> Option<u64> {
        let mut c = 0;
        for _ in 0..k {
            match self.mstep() {
                None => return Some(c),
                Some(true) => c += 1,
                Some(false) => {}
            }
        }
        None
    }
}

/// A result in shared form: its distinct nodes, children first, each
/// written once.  A cell is a tag byte (`S`, `K`, `I`, or `` ` ``), and an
/// application adds its children's indices as two little-endian `u32`s;
/// the last cell is the root.  The printed form of a reduced term can be
/// exponentially larger than its graph, so results are never printed: the
/// benchmark commits the digest of this form, whose size is linear in the
/// nodes the reduction allocated.
#[derive(Default)]
pub struct Shared {
    pub bytes: Vec<u8>,
    count: u32,
}

impl Shared {
    fn leaf(&mut self, tag: u8) -> u32 {
        self.bytes.push(tag);
        self.count += 1;
        self.count - 1
    }

    fn app(&mut self, f: u32, a: u32) -> u32 {
        self.bytes.push(b'`');
        self.bytes.extend_from_slice(&f.to_le_bytes());
        self.bytes.extend_from_slice(&a.to_le_bytes());
        self.count += 1;
        self.count - 1
    }

    /// The shared form of a term graph, one cell per distinct `Rc` node.
    pub fn of_term(root: &Rc<Term>) -> Shared {
        let mut sh = Shared::default();
        let mut memo: HashMap<*const Term, u32> = HashMap::new();
        let mut todo: Vec<(&Rc<Term>, bool)> = vec![(root, false)];
        while let Some((t, ready)) = todo.pop() {
            let key = Rc::as_ptr(t);
            if memo.contains_key(&key) {
                continue;
            }
            let ix = match &**t {
                Term::S => sh.leaf(b'S'),
                Term::K => sh.leaf(b'K'),
                Term::I => sh.leaf(b'I'),
                Term::App(f, a) => {
                    if !ready {
                        todo.push((t, true));
                        todo.push((a, false));
                        todo.push((f, false));
                        continue;
                    }
                    sh.app(memo[&Rc::as_ptr(f)], memo[&Rc::as_ptr(a)])
                }
            };
            memo.insert(key, ix);
        }
        sh
    }

    /// The shared form of a halted machine's value, `apps hd args`: one cell
    /// per heap cell reachable from the head and the stack, then the
    /// applications to the stack's arguments.
    pub fn of_mach(m: &Mach) -> Shared {
        let mut sh = Shared::default();
        let mut memo: HashMap<u32, u32> = HashMap::new();
        let mut node = |sh: &mut Shared, root: u32| -> u32 {
            let mut todo: Vec<(u32, bool)> = vec![(root, false)];
            while let Some((a, ready)) = todo.pop() {
                if memo.contains_key(&a) {
                    continue;
                }
                let ix = match m.get(a) {
                    Some(Cell::S) => sh.leaf(b'S'),
                    Some(Cell::K) => sh.leaf(b'K'),
                    Some(Cell::I) => sh.leaf(b'I'),
                    Some(Cell::App(f, x)) => {
                        if !ready {
                            todo.push((a, true));
                            todo.push((x, false));
                            todo.push((f, false));
                            continue;
                        }
                        sh.app(memo[&f], memo[&x])
                    }
                    // A value's cells are combinators and applications.
                    _ => unreachable!(),
                };
                memo.insert(a, ix);
            }
            memo[&root]
        };
        let mut acc = node(&mut sh, m.hd);
        let mut s = m.stk;
        while let Some((x, rest)) = m.cons(s) {
            let ix = node(&mut sh, x);
            acc = sh.app(acc, ix);
            s = rest;
        }
        sh
    }
}

/// Convert a halted machine's value to a term graph, sharing as the heap does.
pub fn mach_term(m: &Mach) -> Rc<Term> {
    let mut memo: HashMap<u32, Rc<Term>> = HashMap::new();
    let mut node = |root: u32| -> Rc<Term> {
        let mut todo: Vec<(u32, bool)> = vec![(root, false)];
        while let Some((a, ready)) = todo.pop() {
            if memo.contains_key(&a) {
                continue;
            }
            let t = match m.get(a) {
                Some(Cell::S) => Rc::new(Term::S),
                Some(Cell::K) => Rc::new(Term::K),
                Some(Cell::I) => Rc::new(Term::I),
                Some(Cell::App(f, x)) => {
                    if !ready {
                        todo.push((a, true));
                        todo.push((x, false));
                        todo.push((f, false));
                        continue;
                    }
                    app(memo[&f].clone(), memo[&x].clone())
                }
                _ => unreachable!(),
            };
            memo.insert(a, t);
        }
        memo[&root].clone()
    };
    let mut acc = node(m.hd);
    let mut s = m.stk;
    while let Some((x, rest)) = m.cons(s) {
        acc = app(acc, node(x));
        s = rest;
    }
    acc
}

/// Structural equality of two term graphs without unsharing them: each pair
/// of nodes is compared once.  `None` when more than `limit` pairs would be
/// needed.
pub fn graph_eq(a: &Rc<Term>, b: &Rc<Term>, limit: usize) -> Option<bool> {
    let mut seen: HashSet<(*const Term, *const Term)> = HashSet::new();
    let mut todo: Vec<(&Rc<Term>, &Rc<Term>)> = vec![(a, b)];
    while let Some((x, y)) = todo.pop() {
        if Rc::ptr_eq(x, y) || !seen.insert((Rc::as_ptr(x), Rc::as_ptr(y))) {
            continue;
        }
        if seen.len() > limit {
            return None;
        }
        match (&**x, &**y) {
            (Term::S, Term::S) | (Term::K, Term::K) | (Term::I, Term::I) => {}
            (Term::App(f, p), Term::App(g, q)) => {
                todo.push((p, q));
                todo.push((f, g));
            }
            _ => return Some(false),
        }
    }
    Some(true)
}

/// The two reducers the benchmark measures.
pub const MODE_TREE: u8 = 0;
pub const MODE_HEAP: u8 = 1;

/// The value a run reaches, in the reducer's own representation.
pub enum Value {
    Tree(Rc<Term>),
    Heap(Mach),
}

impl Value {
    pub fn shared(&self) -> Shared {
        match self {
            Value::Tree(t) => Shared::of_term(t),
            Value::Heap(m) => Shared::of_mach(m),
        }
    }

    pub fn term(&self) -> Rc<Term> {
        match self {
            Value::Tree(t) => t.clone(),
            Value::Heap(m) => mach_term(m),
        }
    }
}

/// Run one mode: `Some((contractions, value))`, or `None` on a parse
/// failure or timeout.
pub fn run(mode: u8, fuel: u64, src: &[u8]) -> Option<(u64, Value)> {
    reduce(mode, fuel, parse(src)?)
}

/// Reduce a parsed term in one mode.  The heap mode includes `load`.
pub fn reduce(mode: u8, fuel: u64, t: Rc<Term>) -> Option<(u64, Value)> {
    match mode {
        MODE_TREE => {
            let (v, n) = run_f(fuel, t)?;
            Some((n, Value::Tree(v)))
        }
        MODE_HEAP => {
            let mut m = Mach::load(&t);
            let n = m.mrun_c(fuel)?;
            Some((n, Value::Heap(m)))
        }
        _ => None,
    }
}
