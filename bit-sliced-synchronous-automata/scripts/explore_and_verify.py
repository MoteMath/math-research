#!/usr/bin/env python3
"""
BitSync — Exact Python Synthesis, Independent Verification, Sharpness & Mutation Suite
======================================================================================
Pure exact integer arithmetic (ZERO floats anywhere).

Functions:
1. Mirrors the exact Lean 4 `BitSync` pipelined synchronous automaton compiler.
2. Synthesizes minimal reachable-state invariant certificates `AutomatonCert`
   for 10 flagship infinite-width bitwise theorems (1, 2, and 3 variables;
   pipeline latencies 1 and 2; unsigned/signed arithmetic, shifts, Gray codes,
   carry-save quarter-sums, and Hamming-weight parity).
3. Independently verifies every theorem exhaustively over ALL small bit-widths
   and deterministic exact large-width bitvectors (up to w = 512).
4. Finds and independently verifies exact sharpness counterexamples when
   hypotheses or width thresholds are relaxed.
5. Runs 6 negative/mutation tests verifying `checkCert bad = false`.
6. Optionally emits Lean 4 certificate definitions (`--emit-lean`).
"""

import argparse
import random
from collections import deque

# ==============================================================================
# 1. Tagged Values Matching Lean 4 State Types Unambiguously
# ==============================================================================

UNIT = ("UNIT",)
OPT_NONE = ("OPT_NONE",)

def opt_some(b: bool):
    return ("OPT_SOME", bool(b))

def is_opt_some(v):
    return isinstance(v, tuple) and len(v) == 2 and v[0] == "OPT_SOME"

def opt_val(v):
    return v[1]

def to_lean(v) -> str:
    """Serialize a Python state tuple into an exact Lean 4 literal."""
    if v == UNIT:
        return "()"
    if v == OPT_NONE:
        return "none"
    if is_opt_some(v):
        return f"(some {'true' if v[1] else 'false'})"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return f"({v} : Nat)"
    if isinstance(v, tuple) and len(v) == 2:
        return f"({to_lean(v[0])}, {to_lean(v[1])})"
    raise ValueError(f"Cannot serialize to Lean: {v!r}")

# ==============================================================================
# 2. Exact Bit-Vector Expression & Proposition AST (mirrors Proof.lean)
# ==============================================================================

class BVExpr:
    pass

class Var(BVExpr):
    def __init__(self, idx: int): self.idx = idx
class Zero(BVExpr): pass
class AllOnes(BVExpr): pass
class One(BVExpr): pass
class Not(BVExpr):
    def __init__(self, e: BVExpr): self.e = e
class Neg(BVExpr):
    def __init__(self, e: BVExpr): self.e = e
class Shl1(BVExpr):
    def __init__(self, e: BVExpr): self.e = e
class Ushr1(BVExpr):
    def __init__(self, e: BVExpr): self.e = e
class Ashr1(BVExpr):
    def __init__(self, e: BVExpr): self.e = e
class And(BVExpr):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Or(BVExpr):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Xor(BVExpr):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Add(BVExpr):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Sub(BVExpr):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b

class BVProp:
    pass

class Eq(BVProp):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Ult(BVProp):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Ule(BVProp):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Slt(BVProp):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Sle(BVProp):
    def __init__(self, a: BVExpr, b: BVExpr): self.a = a; self.b = b
class Msb(BVProp):
    def __init__(self, e: BVExpr): self.e = e
class Lsb(BVProp):
    def __init__(self, e: BVExpr): self.e = e
class Parity(BVProp):
    def __init__(self, e: BVExpr): self.e = e
class WidthGe(BVProp):
    def __init__(self, n: int): self.n = n
class PNot(BVProp):
    def __init__(self, p: BVProp): self.p = p
class PAnd(BVProp):
    def __init__(self, a: BVProp, b: BVProp): self.a = a; self.b = b
class POr(BVProp):
    def __init__(self, a: BVProp, b: BVProp): self.a = a; self.b = b
class PImp(BVProp):
    def __init__(self, a: BVProp, b: BVProp): self.a = a; self.b = b
class PIff(BVProp):
    def __init__(self, a: BVProp, b: BVProp): self.a = a; self.b = b

# ==============================================================================
# 3. Independent Exact-Integer BitVec Semantics (for ground-truth checking)
# ==============================================================================

def bv_mask(w: int) -> int:
    return (1 << w) - 1

def bv_to_signed(w: int, x: int) -> int:
    if w == 0:
        return 0
    x &= bv_mask(w)
    if x >= (1 << (w - 1)):
        return x - (1 << w)
    return x

def bv_msb(w: int, x: int) -> bool:
    if w == 0:
        return False
    return bool((x >> (w - 1)) & 1)

def bv_ashr1(w: int, x: int) -> int:
    if w == 0:
        return 0
    m = bv_mask(w)
    x &= m
    sign = (x >> (w - 1)) & 1
    return ((x >> 1) | (sign << (w - 1))) & m

def bv_parity(w: int, x: int) -> bool:
    return ((x & bv_mask(w)).bit_count() & 1) == 1

def eval_expr_exact(w: int, env: list[int], e: BVExpr) -> int:
    m = bv_mask(w)
    if isinstance(e, Var): return env[e.idx] & m
    if isinstance(e, Zero): return 0
    if isinstance(e, AllOnes): return m
    if isinstance(e, One): return 1 & m
    if isinstance(e, Not): return (~eval_expr_exact(w, env, e.e)) & m
    if isinstance(e, Neg): return (-eval_expr_exact(w, env, e.e)) & m
    if isinstance(e, Shl1): return (eval_expr_exact(w, env, e.e) << 1) & m
    if isinstance(e, Ushr1): return (eval_expr_exact(w, env, e.e) >> 1) & m
    if isinstance(e, Ashr1): return bv_ashr1(w, eval_expr_exact(w, env, e.e))
    if isinstance(e, And): return eval_expr_exact(w, env, e.a) & eval_expr_exact(w, env, e.b)
    if isinstance(e, Or): return eval_expr_exact(w, env, e.a) | eval_expr_exact(w, env, e.b)
    if isinstance(e, Xor): return eval_expr_exact(w, env, e.a) ^ eval_expr_exact(w, env, e.b)
    if isinstance(e, Add): return (eval_expr_exact(w, env, e.a) + eval_expr_exact(w, env, e.b)) & m
    if isinstance(e, Sub): return (eval_expr_exact(w, env, e.a) - eval_expr_exact(w, env, e.b)) & m
    raise TypeError(e)

def eval_prop_exact(w: int, env: list[int], p: BVProp) -> bool:
    if isinstance(p, Eq): return eval_expr_exact(w, env, p.a) == eval_expr_exact(w, env, p.b)
    if isinstance(p, Ult): return eval_expr_exact(w, env, p.a) < eval_expr_exact(w, env, p.b)
    if isinstance(p, Ule): return eval_expr_exact(w, env, p.a) <= eval_expr_exact(w, env, p.b)
    if isinstance(p, Slt): return bv_to_signed(w, eval_expr_exact(w, env, p.a)) < bv_to_signed(w, eval_expr_exact(w, env, p.b))
    if isinstance(p, Sle): return bv_to_signed(w, eval_expr_exact(w, env, p.a)) <= bv_to_signed(w, eval_expr_exact(w, env, p.b))
    if isinstance(p, Msb): return bv_msb(w, eval_expr_exact(w, env, p.e))
    if isinstance(p, Lsb): return bool(eval_expr_exact(w, env, p.e) & 1) if w > 0 else False
    if isinstance(p, Parity): return bv_parity(w, eval_expr_exact(w, env, p.e))
    if isinstance(p, WidthGe): return w >= p.n
    if isinstance(p, PNot): return not eval_prop_exact(w, env, p.p)
    if isinstance(p, PAnd): return eval_prop_exact(w, env, p.a) and eval_prop_exact(w, env, p.b)
    if isinstance(p, POr): return eval_prop_exact(w, env, p.a) or eval_prop_exact(w, env, p.b)
    if isinstance(p, PImp): return (not eval_prop_exact(w, env, p.a)) or eval_prop_exact(w, env, p.b)
    if isinstance(p, PIff): return eval_prop_exact(w, env, p.a) == eval_prop_exact(w, env, p.b)
    raise TypeError(p)

# ==============================================================================
# 4. Pipelined Automaton Compiler (bit-for-bit identical state layout to Proof.lean)
# ==============================================================================

def expr_latency(e: BVExpr) -> int:
    if isinstance(e, (Var, Zero, AllOnes, One)): return 0
    if isinstance(e, (Not, Neg, Shl1)): return expr_latency(e.e)
    if isinstance(e, (Ushr1, Ashr1)): return expr_latency(e.e) + 1
    if isinstance(e, (And, Or, Xor, Add, Sub)): return max(expr_latency(e.a), expr_latency(e.b))
    raise TypeError(e)

def compile_delay(comp, n: int):
    if n == 0:
        return comp
    sub_init, sub_step = compile_delay(comp, n - 1)
    init = (sub_init, OPT_NONE)
    def step(st, inp):
        s, buf = st
        s2, o2 = sub_step(s, inp)
        return (s2, o2), buf
    return init, step

def at_least_two(a: bool, b: bool, c: bool) -> bool:
    return (a and b) or (a and c) or (b and c)

def compile_expr(e: BVExpr):
    if isinstance(e, Var):
        idx = e.idx
        def step(st, inp):
            if inp is None: return UNIT, OPT_NONE
            return UNIT, opt_some(bool((inp >> idx) & 1))
        return UNIT, step
    if isinstance(e, Zero):
        return UNIT, lambda st, inp: (UNIT, OPT_NONE if inp is None else opt_some(False))
    if isinstance(e, AllOnes):
        return UNIT, lambda st, inp: (UNIT, OPT_NONE if inp is None else opt_some(True))
    if isinstance(e, One):
        def step(isLsb, inp):
            if inp is None: return False, OPT_NONE
            return False, opt_some(isLsb)
        return True, step
    if isinstance(e, Not):
        s0, f = compile_expr(e.e)
        def step(st, inp):
            s2, o = f(st, inp)
            return s2, (opt_some(not opt_val(o)) if is_opt_some(o) else OPT_NONE)
        return s0, step
    if isinstance(e, Neg):
        s0, f = compile_expr(e.e)
        def step(st, inp):
            s, c = st
            s2, o = f(s, inp)
            if is_opt_some(o):
                nb = not opt_val(o)
                return (s2, nb and c), opt_some(nb ^ c)
            return (s2, c), OPT_NONE
        return (s0, True), step
    if isinstance(e, Shl1):
        s0, f = compile_expr(e.e)
        def step(st, inp):
            s, prev = st
            s2, o = f(s, inp)
            if is_opt_some(o):
                return (s2, opt_val(o)), opt_some(prev)
            return (s2, prev), OPT_NONE
        return (s0, False), step
    if isinstance(e, Ushr1):
        s0, f = compile_expr(e.e)
        def step(st, inp):
            s, had = st
            s2, o = f(s, inp)
            if not had:
                return (s2, is_opt_some(o)), OPT_NONE
            if is_opt_some(o):
                return (s2, True), o
            return (s2, False), opt_some(False)
        return (s0, False), step
    if isinstance(e, Ashr1):
        s0, f = compile_expr(e.e)
        def step(st, inp):
            s, prev = st
            s2, o = f(s, inp)
            if not is_opt_some(prev):
                return (s2, o), OPT_NONE
            if is_opt_some(o):
                return (s2, o), o
            return (s2, OPT_NONE), prev
        return (s0, OPT_NONE), step
    if isinstance(e, (And, Or, Xor, Add, Sub)):
        la, lb = expr_latency(e.a), expr_latency(e.b)
        L = max(la, lb)
        sa, fa = compile_delay(compile_expr(e.a), L - la)
        sb, fb = compile_delay(compile_expr(e.b), L - lb)
        if isinstance(e, (And, Or, Xor)):
            op = (lambda x, y: x and y) if isinstance(e, And) else \
                 (lambda x, y: x or y) if isinstance(e, Or) else \
                 (lambda x, y: x ^ y)
            def step(st, inp):
                s1, s2 = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    return (s1n, s2n), opt_some(op(opt_val(o1), opt_val(o2)))
                return (s1n, s2n), OPT_NONE
            return (sa, sb), step
        if isinstance(e, Add):
            def step(st, inp):
                (s1, s2), c = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    b1, b2 = opt_val(o1), opt_val(o2)
                    return ((s1n, s2n), at_least_two(b1, b2, c)), opt_some(b1 ^ (b2 ^ c))
                return ((s1n, s2n), c), OPT_NONE
            return ((sa, sb), False), step
        if isinstance(e, Sub):
            def step(st, inp):
                (s1, s2), c = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    b1, nb2 = opt_val(o1), (not opt_val(o2))
                    return ((s1n, s2n), at_least_two(b1, nb2, c)), opt_some(b1 ^ (nb2 ^ c))
                return ((s1n, s2n), c), OPT_NONE
            return ((sa, sb), True), step
    raise TypeError(e)

def compile_prop(p: BVProp):
    if isinstance(p, (Eq, Ult, Ule, Slt, Sle)):
        la, lb = expr_latency(p.a), expr_latency(p.b)
        L = max(la, lb)
        sa, fa = compile_delay(compile_expr(p.a), L - la)
        sb, fb = compile_delay(compile_expr(p.b), L - lb)
        if isinstance(p, Eq):
            def step(st, inp):
                (s1, s2), ok = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    return ((s1n, s2n), ok and (opt_val(o1) == opt_val(o2)))
                return ((s1n, s2n), ok)
            return ((sa, sb), True), step, (lambda st: st[1]), L
        if isinstance(p, (Ult, Ule)):
            initB = isinstance(p, Ule)
            def step(st, inp):
                (s1, s2), r = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    b1, b2 = opt_val(o1), opt_val(o2)
                    return ((s1n, s2n), ((not b1) and b2) or ((b1 == b2) and r))
                return ((s1n, s2n), r)
            return ((sa, sb), initB), step, (lambda st: st[1]), L
        if isinstance(p, (Slt, Sle)):
            initB = isinstance(p, Sle)
            def step(st, inp):
                ((s1, s2), u), sg = st
                s1n, o1 = fa(s1, inp)
                s2n, o2 = fb(s2, inp)
                if is_opt_some(o1) and is_opt_some(o2):
                    b1, b2 = opt_val(o1), opt_val(o2)
                    sg2 = (b1 and (not b2)) or ((b1 == b2) and u)
                    u2 = ((not b1) and b2) or ((b1 == b2) and u)
                    return (((s1n, s2n), u2), sg2)
                return (((s1n, s2n), u), sg)
            return (((sa, sb), initB), initB), step, (lambda st: st[1]), L
    if isinstance(p, Msb):
        L = expr_latency(p.e)
        s0, f = compile_expr(p.e)
        def step(st, inp):
            s, last = st
            sn, o = f(s, inp)
            return (sn, opt_val(o) if is_opt_some(o) else last)
        return (s0, False), step, (lambda st: st[1]), L
    if isinstance(p, Lsb):
        L = expr_latency(p.e)
        s0, f = compile_expr(p.e)
        def step(st, inp):
            (s, seen), first = st
            sn, o = f(s, inp)
            if is_opt_some(o):
                if not seen:
                    return ((sn, True), opt_val(o))
                return ((sn, True), first)
            return ((sn, seen), first)
        return ((s0, False), False), step, (lambda st: st[1]), L
    if isinstance(p, Parity):
        L = expr_latency(p.e)
        s0, f = compile_expr(p.e)
        def step(st, inp):
            s, par = st
            sn, o = f(s, inp)
            return (sn, par ^ opt_val(o) if is_opt_some(o) else par)
        return (s0, False), step, (lambda st: st[1]), L
    if isinstance(p, WidthGe):
        n = p.n
        def step(st, inp):
            return min(n, st + 1) if inp is not None else st
        return 0, step, (lambda st: st >= n), 0
    if isinstance(p, PNot):
        s0, f, v, L = compile_prop(p.p)
        return s0, f, (lambda st: not v(st)), L
    if isinstance(p, (PAnd, POr, PImp, PIff)):
        sa, fa, va, la = compile_prop(p.a)
        sb, fb, vb, lb = compile_prop(p.b)
        L = max(la, lb)
        op = (lambda x, y: x and y) if isinstance(p, PAnd) else \
             (lambda x, y: x or y) if isinstance(p, POr) else \
             (lambda x, y: (not x) or y) if isinstance(p, PImp) else \
             (lambda x, y: x == y)
        def step(st, inp):
            return (fa(st[0], inp), fb(st[1], inp))
        return (sa, sb), step, (lambda st: op(va(st[0]), vb(st[1]))), L
    raise TypeError(p)

def to_sync(p: BVProp):
    init, stepTick, verdict, lat = compile_prop(p)
    def step(s, a):
        return stepTick(s, a)
    def accept(s):
        cur = s
        for _ in range(lat):
            cur = stepTick(cur, None)
        return verdict(cur)
    return init, step, accept, lat

def check_cert_py(k: int, sync, states, nextIdx) -> bool:
    init, step, accept, _ = sync
    n = len(states)
    alpha = 1 << k
    if n == 0 or states[0] != init or len(nextIdx) != n:
        return False
    for i in range(n):
        si = states[i]
        row = nextIdx[i]
        if len(row) != alpha or not accept(si):
            return False
        for a in range(alpha):
            j = row[a]
            if not (0 <= j < n):
                return False
            if step(si, a) != states[j]:
                return False
    return True

def synthesize_cert(k: int, p: BVProp):
    init, step, accept, lat = to_sync(p)
    alpha = 1 << k
    idx_map = {init: 0}
    states = [init]
    parent = {0: None}
    q = deque([0])
    bad = None
    nextIdx = []
    while q:
        u = q.popleft()
        su = states[u]
        if not accept(su) and bad is None:
            bad = u
        row = []
        for a in range(alpha):
            sv = step(su, a)
            if sv not in idx_map:
                idx_map[sv] = len(states)
                states.append(sv)
                parent[idx_map[sv]] = (u, a)
                q.append(idx_map[sv])
            row.append(idx_map[sv])
        nextIdx.append(row)
    if bad is not None:
        path = []
        cur = bad
        while parent[cur] is not None:
            par, a = parent[cur]
            path.append(a)
            cur = par
        path.reverse()
        w = len(path)
        vals = [0] * k
        for bit_i, a in enumerate(path):
            for j in range(k):
                if (a >> j) & 1:
                    vals[j] |= (1 << bit_i)
        return False, lat, (w, vals), (states, nextIdx)
    return True, lat, (states, nextIdx), None

# ==============================================================================
# 5. Flagship Theorem Suite (10 Infinite-Width Theorems) + Sharpness Variants
# ==============================================================================

x, y, z = Var(0), Var(1), Var(2)

def avg_u(a, b): return Add(And(a, b), Ushr1(Xor(a, b)))
def avg_s(a, b): return Add(And(a, b), Ashr1(Xor(a, b)))
def maj(a, b, c): return Or(Or(And(a, b), And(b, c)), And(c, a))
def q_u(a, b, c): return avg_u(maj(a, b, c), Ushr1(Xor(Xor(a, b), c)))
def q_s(a, b, c): return avg_s(maj(a, b, c), Ashr1(Xor(Xor(a, b), c)))
def ov_s(a, b): return Msb(And(Xor(a, Add(a, b)), Xor(b, Add(a, b))))
def gray(a): return Xor(a, Ushr1(a))

THEOREMS = [
    ("signedQuarterSumNetOverflow", 3,
     PImp(WidthGe(2),
          PIff(Eq(q_s(x, y, z), Ashr1(Ashr1(Add(Add(x, y), z)))),
               PIff(ov_s(x, y), ov_s(Add(x, y), z))))),

    ("unsignedQuarterSumNoOverflow", 3,
     PImp(WidthGe(2),
          PIff(Eq(q_u(x, y, z), Ushr1(Ushr1(Add(Add(x, y), z)))),
               PAnd(PNot(Ult(Add(x, y), x)), PNot(Ult(Add(Add(x, y), z), Add(x, y))))))),

    ("signedEqUnsignedQuarterSum", 3,
     PIff(Eq(q_s(x, y, z), q_u(x, y, z)),
          PAnd(PAnd(PNot(Msb(x)), PNot(Msb(y))), PNot(Msb(z))))),

    ("signedQuarterSumModReconstruct", 3,
     Eq(Add(Shl1(Shl1(q_s(x, y, z))), And(Add(Add(x, y), z), Or(One(), Shl1(One())))),
        Add(Add(x, y), z))),

    ("nestedAvgVsQuarterSumSandwich", 3,
     PAnd(Ule(Ushr1(Ushr1(z)), Sub(avg_u(avg_u(x, y), z), q_u(x, y, z))),
          Ule(Sub(avg_u(avg_u(x, y), z), q_u(x, y, z)), Add(Ushr1(Ushr1(z)), One())))),

    ("grayTripleZeckendorf", 1,
     PIff(Eq(gray(Add(x, Shl1(x))), Xor(Shl1(x), Ushr1(x))),
          PAnd(Eq(And(x, Shl1(x)), Zero()), PNot(Msb(x))))),

    ("signedVsUnsignedAvgXorMsb", 2,
     Eq(Xor(avg_s(x, y), avg_u(x, y)), And(Xor(x, y), Not(Ushr1(AllOnes()))))),

    ("signedAvgMidpointSandwich", 2,
     PImp(Sle(x, y), PAnd(Sle(x, avg_s(x, y)), Sle(avg_s(x, y), y)))),

    ("grayParityEqLsb", 1,
     PIff(Parity(gray(x)), Lsb(x))),

    ("graySuccOneHot", 1,
     PImp(WidthGe(1),
          PAnd(PNot(Eq(Xor(gray(Add(x, One())), gray(x)), Zero())),
               Eq(And(Xor(gray(Add(x, One())), gray(x)),
                      Sub(Xor(gray(Add(x, One())), gray(x)), One())), Zero())))),
]

SHARPNESS_PROBES = [
    ("T1_without_w_ge_2", 3,
     PIff(Eq(q_s(x, y, z), Ashr1(Ashr1(Add(Add(x, y), z)))),
          PIff(ov_s(x, y), ov_s(Add(x, y), z)))),

    ("T1_naive_no_cancelling_overflow", 3,
     PImp(WidthGe(2),
          PIff(Eq(q_s(x, y, z), Ashr1(Ashr1(Add(Add(x, y), z)))),
               PAnd(PNot(ov_s(x, y)), PNot(ov_s(Add(x, y), z)))))),

    ("T2_without_w_ge_2", 3,
     PIff(Eq(q_u(x, y, z), Ushr1(Ushr1(Add(Add(x, y), z)))),
          PAnd(PNot(Ult(Add(x, y), x)), PNot(Ult(Add(Add(x, y), z), Add(x, y)))))),

    ("T3_allow_all_negative_false", 3,
     PIff(Eq(q_s(x, y, z), q_u(x, y, z)),
          PAnd(PIff(Msb(x), Msb(y)), PIff(Msb(y), Msb(z))))),

    ("T5_tightened_plus0_upper_bound", 3,
     Ule(Sub(avg_u(avg_u(x, y), z), q_u(x, y, z)), Ushr1(Ushr1(z)))),

    ("T6_without_not_msb", 1,
     PIff(Eq(gray(Add(x, Shl1(x))), Xor(Shl1(x), Ushr1(x))),
          Eq(And(x, Shl1(x)), Zero()))),

    ("T6_without_zeckendorf", 1,
     PIff(Eq(gray(Add(x, Shl1(x))), Xor(Shl1(x), Ushr1(x))),
          PNot(Msb(x)))),

    ("T10_without_w_ge_1", 1,
     PAnd(PNot(Eq(Xor(gray(Add(x, One())), gray(x)), Zero())),
          Eq(And(Xor(gray(Add(x, One())), gray(x)),
                 Sub(Xor(gray(Add(x, One())), gray(x)), One())), Zero()))),
]

def independent_verify(name: str, k: int, p: BVProp):
    # Exhaustive verification on small widths
    max_w = 4 if k == 3 else (6 if k == 2 else 11)
    total_exhaustive = 0
    for w in range(0, max_w + 1):
        limit = 1 << w
        if k == 1:
            for a in range(limit):
                assert eval_prop_exact(w, [a], p), f"{name} failed at w={w}, x={a}"
                total_exhaustive += 1
        elif k == 2:
            for a in range(limit):
                for b in range(limit):
                    assert eval_prop_exact(w, [a, b], p), f"{name} failed at w={w}, x={a}, y={b}"
                    total_exhaustive += 1
        elif k == 3:
            for a in range(limit):
                for b in range(limit):
                    for c in range(limit):
                        assert eval_prop_exact(w, [a, b, c], p), f"{name} failed at w={w}, ({a},{b},{c})"
                        total_exhaustive += 1
    # Deterministic PRNG spot-checks at huge widths (w = 32, 64, 128, 256, 512)
    rng = random.Random(20261126 + hash(name) % 10000)
    large_checks = 0
    for w in (32, 64, 128, 256, 512):
        for _ in range(200):
            env = [rng.getrandbits(w) for _ in range(k)]
            assert eval_prop_exact(w, env, p), f"{name} failed at w={w}, env={env}"
            large_checks += 1
    return total_exhaustive, large_checks

def run_mutation_tests():
    # Use T1 (signedQuarterSumNetOverflow, 36 states) for comprehensive mutation tests
    name, k, prop = THEOREMS[0]
    sync = to_sync(prop)
    ok, lat, (states, nextIdx), _ = synthesize_cert(k, prop)
    assert ok and check_cert_py(k, sync, states, nextIdx)

    # 1. Empty states
    assert not check_cert_py(k, sync, [], [])
    # 2. Wrong initial state (swap states[0] and states[1])
    bad_init = [states[1]] + states[1:]
    assert not check_cert_py(k, sync, bad_init, nextIdx)
    # 3. Dropped reachable state
    assert not check_cert_py(k, sync, states[:-1], nextIdx[:-1])
    # 4. Corrupted transition index
    bad_trans = [row[:] for row in nextIdx]
    bad_trans[0][0] = (bad_trans[0][0] + 1) % len(states)
    assert not check_cert_py(k, sync, states, bad_trans)
    # 5. Truncated transition row
    bad_row = [row[:] for row in nextIdx]
    bad_row[0] = bad_row[0][:-1]
    assert not check_cert_py(k, sync, states, bad_row)
    # 6. Forged certificate applied to relaxed false formula (T1 without w >= 2)
    _, k_bad, false_prop = SHARPNESS_PROBES[0]
    sync_false = to_sync(false_prop)
    ok_f, _, cex_f, (st_f, tr_f) = synthesize_cert(k_bad, false_prop)
    assert not ok_f
    assert not check_cert_py(k_bad, sync_false, st_f, tr_f)
    print("[PASS] All 6 certificate mutation tests rejected (checkCert = false).")

def emit_lean_certs():
    for name, k, prop in THEOREMS:
        ok, lat, (states, nextIdx), _ = synthesize_cert(k, prop)
        assert ok, f"Theorem {name} failed synthesis!"
        print(f"def cert_{name} : AutomatonCert prop_{name}.State where")
        print("  states := [")
        for i, s in enumerate(states):
            comma = "," if i + 1 < len(states) else ""
            print(f"    {to_lean(s)}{comma}")
        print("  ]")
        print("  nextIdx := [")
        for i, row in enumerate(nextIdx):
            comma = "," if i + 1 < len(nextIdx) else ""
            print(f"    {row}{comma}")
        print("  ]\n")
    # Also emit the closed-transition forged cert for the false formula (T1 without w >= 2)
    _, k_f, prop_f = SHARPNESS_PROBES[0]
    ok_f, _, _, (st_f, tr_f) = synthesize_cert(k_f, prop_f)
    assert not ok_f
    print("def cert_forged_noWidthGuard : AutomatonCert prop_signedQuarterSumNoWidthGuard.State where")
    print("  states := [")
    for i, s in enumerate(st_f):
        comma = "," if i + 1 < len(st_f) else ""
        print(f"    {to_lean(s)}{comma}")
    print("  ]")
    print("  nextIdx := [")
    for i, row in enumerate(tr_f):
        comma = "," if i + 1 < len(tr_f) else ""
        print(f"    {row}{comma}")
    print("  ]\n")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-lean", action="store_true", help="Emit Lean 4 AutomatonCert literals")
    args = parser.parse_args()

    if args.emit_lean:
        emit_lean_certs()
        return

    print("=== 1. Synthesizing & Independently Verifying 10 Flagship Infinite-Width Theorems ===")
    for name, k, prop in THEOREMS:
        sync = to_sync(prop)
        ok, lat, data, _ = synthesize_cert(k, prop)
        assert ok, f"Unexpected refutation of {name}: {data}"
        states, nextIdx = data
        assert check_cert_py(k, sync, states, nextIdx), f"checkCert failed for {name}"
        exh, lrg = independent_verify(name, k, prop)
        print(f"[CERTIFIED] {name:34s} | k={k} lat={lat} states={len(states):3d} | exhaustive={exh:5d} large(<=512b)={lrg}")

    print("\n=== 2. Sharpness & Falsification Counterexample Synthesis ===")
    for name, k, prop in SHARPNESS_PROBES:
        ok, lat, cex, _ = synthesize_cert(k, prop)
        assert not ok, f"Expected refutation for {name}, but it proved!"
        w, vals = cex
        # Independently verify the counterexample evaluates to False!
        assert not eval_prop_exact(w, vals, prop), f"Counterexample {cex} did not falsify {name}!"
        print(f"[SHARP CEX] {name:34s} | shortest counterexample: w={w}, vars={vals}")

    print("\n=== 3. Negative / Certificate Mutation Tests ===")
    run_mutation_tests()

if __name__ == "__main__":
    main()
