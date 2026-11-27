#!/usr/bin/env python3
"""
explore_and_verify.py — Exact Carry-Presburger Residue-Transition Compiler & Verifier

Pure-silicon exact-integer certificate synthesizer, independent oracle verifier,
sharpness/counterexample generator, hostile mutation tester, and Lean 4.36.0
certificate emitter for CPRTE (`Proof.lean`).

Zero floating-point arithmetic is used anywhere in synthesis, verification, or certificates.
"""

from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple, Union
import sys

# ============================================================================
# 1. Exact Pure-Silicon Primitives (Bit-Identical to Proof.lean)
# ============================================================================

MASK_AND_ZERO = 0x0FFF  # !(b1 && b2)
MASK_XOR3_EQ0 = 0x3CC3  # !(b1 ^^ b2 ^^ b3)


def popcount(n: int) -> int:
    assert n >= 0
    return n.bit_count()


def carry_count(a: int, b: int, cin: bool = False) -> int:
    assert a >= 0 and b >= 0
    c = 1 if cin else 0
    return popcount(a) + popcount(b) + c - popcount(a + b + c)


def bit_idx4(b1: bool, b2: bool, b3: bool, b4: bool) -> int:
    return 8 * int(b1) + 4 * int(b2) + 2 * int(b3) + int(b4)


def test_bit(mask: int, idx: int) -> bool:
    return bool((mask >> idx) & 1)


def bit_rel4_dec(mask: int, v1: int, v2: int, v3: int, v4: int) -> bool:
    while v1 or v2 or v3 or v4:
        idx = bit_idx4(bool(v1 & 1), bool(v2 & 1), bool(v3 & 1), bool(v4 & 1))
        if not test_bit(mask, idx):
            return False
        v1 >>= 1
        v2 >>= 1
        v3 >>= 1
        v4 >>= 1
    return test_bit(mask, 0)


def bits_of_index(d: int, idx: int) -> Tuple[bool, ...]:
    return tuple(bool((idx >> i) & 1) for i in range(d))


def index_of_bits(bs: Sequence[bool]) -> int:
    return sum((1 << i) for i, b in enumerate(bs) if b)


def dot_nat(cs: Sequence[int], vs: Sequence[int]) -> int:
    return sum(c * v for c, v in zip(cs, vs))


def dot_int(cs: Sequence[int], vs: Sequence[int]) -> int:
    return sum(c * v for c, v in zip(cs, vs))


# ============================================================================
# 2. Carry-Presburger AST (Exact Mirror of Proof.lean)
# ============================================================================

@dataclass(frozen=True)
class NatAff:
    coeffs: Tuple[int, ...]
    carry: int = 0

    def eval(self, v: Sequence[int]) -> int:
        return dot_nat(self.coeffs, v) + self.carry

    def step(self, bs: Sequence[bool]) -> Tuple[bool, "NatAff"]:
        s = sum(c * int(b) for c, b in zip(self.coeffs, bs)) + self.carry
        return bool(s & 1), NatAff(self.coeffs, s >> 1)

    def to_lean(self) -> str:
        cs = "[" + ", ".join(str(c) for c in self.coeffs) + "]"
        if self.carry == 0:
            return f"natAff {cs}"
        return f"natAff {cs} {self.carry}"


@dataclass(frozen=True)
class IntAff:
    coeffs: Tuple[int, ...]
    rhs: int

    def to_lean(self) -> str:
        cs = "[" + ", ".join(str(c) for c in self.coeffs) + "]"
        rhs_s = f"({self.rhs})" if self.rhs < 0 else str(self.rhs)
        return f"intAff {cs} {rhs_s}"


@dataclass(frozen=True)
class LinLe:
    t: IntAff

    def to_lean(self) -> str:
        cs = "[" + ", ".join(str(c) for c in self.t.coeffs) + "]"
        rhs_s = f"({self.t.rhs})" if self.t.rhs < 0 else str(self.t.rhs)
        return f"fLinLe {cs} {rhs_s}"


@dataclass(frozen=True)
class LinEq:
    t: IntAff

    def to_lean(self) -> str:
        cs = "[" + ", ".join(str(c) for c in self.t.coeffs) + "]"
        rhs_s = f"({self.t.rhs})" if self.t.rhs < 0 else str(self.t.rhs)
        return f"fLinEq {cs} {rhs_s}"


@dataclass(frozen=True)
class ModEq:
    coeffs: Tuple[int, ...]
    m: int
    r: int

    def to_lean(self) -> str:
        cs = "[" + ", ".join(str(c) for c in self.coeffs) + "]"
        return f"fModEq {cs} {self.m} {self.r}"


@dataclass(frozen=True)
class BitRel4:
    mask: int
    t1: NatAff
    t2: NatAff
    t3: NatAff
    t4: NatAff

    def to_lean(self) -> str:
        if self.mask == MASK_AND_ZERO and self.t3 == NatAff(()) and self.t4 == NatAff(()):
            return f"fDisj ({self.t1.to_lean()}) ({self.t2.to_lean()})"
        if self.mask == MASK_XOR3_EQ0 and self.t4 == NatAff(()):
            return f"fXor3Zero ({self.t1.to_lean()}) ({self.t2.to_lean()}) ({self.t3.to_lean()})"
        return (
            f".atom (.bitRel4 {self.mask} ({self.t1.to_lean()}) ({self.t2.to_lean()}) "
            f"({self.t3.to_lean()}) ({self.t4.to_lean()}))"
        )


@dataclass(frozen=True)
class CarryLe:
    t1: NatAff
    t2: NatAff
    cin: bool
    k: int

    def to_lean(self) -> str:
        cin_s = "true" if self.cin else "false"
        return f"fCarryLe ({self.t1.to_lean()}) ({self.t2.to_lean()}) {cin_s} {self.k}"


@dataclass(frozen=True)
class PopMod:
    terms: Tuple[Tuple[int, NatAff], ...]
    m: int
    r: int

    def to_lean(self) -> str:
        ts = "[" + ", ".join(
            f"({f'({w})' if w < 0 else str(w)}, {t.to_lean()})" for w, t in self.terms
        ) + "]"
        return f"fPopMod {ts} {self.m} {self.r}"


Atom = Union[LinLe, LinEq, ModEq, BitRel4, CarryLe, PopMod]


@dataclass(frozen=True)
class FTT:
    def to_lean(self) -> str:
        return ".tt"


@dataclass(frozen=True)
class FFF:
    def to_lean(self) -> str:
        return ".ff"


@dataclass(frozen=True)
class FAtom:
    a: Atom

    def to_lean(self) -> str:
        return self.a.to_lean()


@dataclass(frozen=True)
class FNot:
    f: "Formula"

    def to_lean(self) -> str:
        return f".not ({self.f.to_lean()})"


@dataclass(frozen=True)
class FAnd:
    f1: "Formula"
    f2: "Formula"

    def to_lean(self) -> str:
        return f".and ({self.f1.to_lean()}) ({self.f2.to_lean()})"


@dataclass(frozen=True)
class FOr:
    f1: "Formula"
    f2: "Formula"

    def to_lean(self) -> str:
        return f".or ({self.f1.to_lean()}) ({self.f2.to_lean()})"


Formula = Union[FTT, FFF, FAtom, FNot, FAnd, FOr]
TT = FTT()
FF = FFF()


def mk_not(f: Formula) -> Formula:
    if isinstance(f, FTT):
        return FF
    if isinstance(f, FFF):
        return TT
    if isinstance(f, FNot):
        return f.f
    return FNot(f)


def mk_and(f1: Formula, f2: Formula) -> Formula:
    if isinstance(f1, FFF) or isinstance(f2, FFF):
        return FF
    if isinstance(f1, FTT):
        return f2
    if isinstance(f2, FTT):
        return f1
    if f1 == f2:
        return f1
    return FAnd(f1, f2)


def mk_or(f1: Formula, f2: Formula) -> Formula:
    if isinstance(f1, FTT) or isinstance(f2, FTT):
        return TT
    if isinstance(f1, FFF):
        return f2
    if isinstance(f2, FFF):
        return f1
    if f1 == f2:
        return f1
    return FOr(f1, f2)


def mk_imp(a: Formula, b: Formula) -> Formula:
    return mk_or(mk_not(a), b)


def mk_iff(a: Formula, b: Formula) -> Formula:
    return mk_and(mk_imp(a, b), mk_imp(b, a))


def big_or(fs: Sequence[Formula]) -> Formula:
    if not fs:
        return FF
    res = fs[-1]
    for f in reversed(fs[:-1]):
        res = mk_or(f, res)
    return res


def big_and(fs: Sequence[Formula]) -> Formula:
    if not fs:
        return TT
    res = fs[-1]
    for f in reversed(fs[:-1]):
        res = mk_and(f, res)
    return res


def eval_atom(a: Atom, v: Sequence[int]) -> bool:
    if isinstance(a, LinLe):
        return dot_int(a.t.coeffs, v) <= a.t.rhs
    if isinstance(a, LinEq):
        return dot_int(a.t.coeffs, v) == a.t.rhs
    if isinstance(a, ModEq):
        return a.m == 0 or (dot_int(a.coeffs, v) % a.m == a.r % a.m)
    if isinstance(a, BitRel4):
        return bit_rel4_dec(a.mask, a.t1.eval(v), a.t2.eval(v), a.t3.eval(v), a.t4.eval(v))
    if isinstance(a, CarryLe):
        return carry_count(a.t1.eval(v), a.t2.eval(v), a.cin) <= a.k
    if isinstance(a, PopMod):
        if a.m == 0:
            return True
        s = sum(w * popcount(t.eval(v)) for w, t in a.terms)
        return (s % a.m) == (a.r % a.m)
    raise TypeError(a)


def eval_formula(f: Formula, v: Sequence[int]) -> bool:
    if isinstance(f, FTT):
        return True
    if isinstance(f, FFF):
        return False
    if isinstance(f, FAtom):
        return eval_atom(f.a, v)
    if isinstance(f, FNot):
        return not eval_formula(f.f, v)
    if isinstance(f, FAnd):
        return eval_formula(f.f1, v) and eval_formula(f.f2, v)
    if isinstance(f, FOr):
        return eval_formula(f.f1, v) or eval_formula(f.f2, v)
    raise TypeError(f)


def simp_atom(a: Atom) -> Formula:
    if isinstance(a, LinLe):
        if all(c <= 0 for c in a.t.coeffs) and 0 <= a.t.rhs:
            return TT
        if all(c >= 0 for c in a.t.coeffs) and a.t.rhs < 0:
            return FF
        return FAtom(a)
    if isinstance(a, LinEq):
        if all(c == 0 for c in a.t.coeffs):
            return TT if a.t.rhs == 0 else FF
        if all(c >= 0 for c in a.t.coeffs) and a.t.rhs < 0:
            return FF
        if all(c <= 0 for c in a.t.coeffs) and 0 < a.t.rhs:
            return FF
        return FAtom(a)
    if isinstance(a, ModEq):
        if a.m <= 1:
            return TT
        return FAtom(ModEq(a.coeffs, a.m, a.r % a.m))
    if isinstance(a, BitRel4):
        if (all(c == 0 for c in a.t1.coeffs) and all(c == 0 for c in a.t2.coeffs)
                and all(c == 0 for c in a.t3.coeffs) and all(c == 0 for c in a.t4.coeffs)):
            return TT if bit_rel4_dec(a.mask, a.t1.carry, a.t2.carry, a.t3.carry, a.t4.carry) else FF
        return FAtom(a)
    if isinstance(a, CarryLe):
        if all(c == 0 for c in a.t1.coeffs) and all(c == 0 for c in a.t2.coeffs):
            return TT if carry_count(a.t1.carry, a.t2.carry, a.cin) <= a.k else FF
        return FAtom(a)
    if isinstance(a, PopMod):
        if a.m <= 1:
            return TT
        return FAtom(PopMod(a.terms, a.m, a.r % a.m))
    raise TypeError(a)


def step_atom(a: Atom, bs: Sequence[bool]) -> Formula:
    if isinstance(a, LinLe):
        s = sum(c * int(b) for c, b in zip(a.t.coeffs, bs))
        return simp_atom(LinLe(IntAff(a.t.coeffs, (a.t.rhs - s) // 2)))
    if isinstance(a, LinEq):
        s = sum(c * int(b) for c, b in zip(a.t.coeffs, bs))
        d = a.t.rhs - s
        if d % 2 == 0:
            return simp_atom(LinEq(IntAff(a.t.coeffs, d // 2)))
        return FF
    if isinstance(a, ModEq):
        if a.m <= 1:
            return TT
        s = sum(c * int(b) for c, b in zip(a.coeffs, bs))
        v = a.r - s
        if a.m % 2 == 0:
            if v % 2 == 0:
                m2 = a.m // 2
                r2 = (v // 2) % m2
                return simp_atom(ModEq(a.coeffs, m2, r2))
            return FF
        inv2 = (a.m + 1) // 2
        r2 = (inv2 * v) % a.m
        return simp_atom(ModEq(a.coeffs, a.m, r2))
    if isinstance(a, BitRel4):
        b1, t1p = a.t1.step(bs)
        b2, t2p = a.t2.step(bs)
        b3, t3p = a.t3.step(bs)
        b4, t4p = a.t4.step(bs)
        if test_bit(a.mask, bit_idx4(b1, b2, b3, b4)):
            return simp_atom(BitRel4(a.mask, t1p, t2p, t3p, t4p))
        return FF
    if isinstance(a, CarryLe):
        b1, t1p = a.t1.step(bs)
        b2, t2p = a.t2.step(bs)
        bsum = int(b1) + int(b2) + int(a.cin)
        cout = bsum >= 2
        if cout:
            if a.k == 0:
                return FF
            return simp_atom(CarryLe(t1p, t2p, True, a.k - 1))
        return simp_atom(CarryLe(t1p, t2p, False, a.k))
    if isinstance(a, PopMod):
        if a.m <= 1:
            return TT
        delta = 0
        terms2 = []
        for w, t in a.terms:
            bit, tp = t.step(bs)
            delta += w * int(bit)
            terms2.append((w, tp))
        r2 = (a.r - delta) % a.m
        return simp_atom(PopMod(tuple(terms2), a.m, r2))
    raise TypeError(a)


def step_formula(f: Formula, bs: Sequence[bool]) -> Formula:
    if isinstance(f, FTT):
        return TT
    if isinstance(f, FFF):
        return FF
    if isinstance(f, FAtom):
        return step_atom(f.a, bs)
    if isinstance(f, FNot):
        return mk_not(step_formula(f.f, bs))
    if isinstance(f, FAnd):
        return mk_and(step_formula(f.f1, bs), step_formula(f.f2, bs))
    if isinstance(f, FOr):
        return mk_or(step_formula(f.f1, bs), step_formula(f.f2, bs))
    raise TypeError(f)


def entails_atom(a1: Atom, a2: Atom) -> bool:
    if isinstance(a1, LinLe) and isinstance(a2, LinLe):
        return a1.t.coeffs == a2.t.coeffs and a1.t.rhs <= a2.t.rhs
    if isinstance(a1, LinEq) and isinstance(a2, LinLe):
        return a1.t.coeffs == a2.t.coeffs and a1.t.rhs <= a2.t.rhs
    if isinstance(a1, LinEq) and isinstance(a2, ModEq):
        return a1.t.coeffs == a2.coeffs and (a2.m == 0 or (a1.t.rhs % a2.m == a2.r % a2.m))
    if isinstance(a1, CarryLe) and isinstance(a2, CarryLe):
        return a1.t1 == a2.t1 and a1.t2 == a2.t2 and a1.cin == a2.cin and a1.k <= a2.k
    return a1 == a2


def entails(p: Formula, q: Formula) -> bool:
    if p == q:
        return True
    if isinstance(p, FFF) or isinstance(q, FTT):
        return True
    if isinstance(p, FOr):
        return entails(p.f1, q) and entails(p.f2, q)
    if isinstance(q, FOr):
        return entails(p, q.f1) or entails(p, q.f2)
    if isinstance(q, FAnd):
        return entails(p, q.f1) and entails(p, q.f2)
    if isinstance(p, FAnd):
        return entails(p.f1, q) or entails(p.f2, q)
    if isinstance(p, FNot) and isinstance(q, FNot):
        return entails(q.f, p.f)
    if isinstance(p, FAtom) and isinstance(q, FAtom):
        return entails_atom(p.a, q.a)
    return False


# ============================================================================
# 3. Certificate Structure, Exact Checker, and Universal / Existential Compilers
# ============================================================================

@dataclass
class StateEntry:
    formula: Formula
    base_y: Tuple[int, ...]
    trans: List[Tuple[List[Tuple[bool, ...]], int]]


@dataclass
class Cert:
    d: int
    e: int
    entries: List[StateEntry]


def check_cert(cert: Cert) -> bool:
    if not cert.entries:
        return False
    n = len(cert.entries)
    for ent in cert.entries:
        if len(ent.base_y) != cert.e:
            return False
        if not eval_formula(ent.formula, [0] * cert.d + list(ent.base_y)):
            return False
        if len(ent.trans) != (1 << cert.d):
            return False
        for idx, (u_list, next_idx) in enumerate(ent.trans):
            if not u_list:
                return False
            if any(len(u) != cert.e for u in u_list):
                return False
            if not (0 <= next_idx < n):
                return False
            b = bits_of_index(cert.d, idx)
            target = cert.entries[next_idx].formula
            stepped = big_or([step_formula(ent.formula, list(b) + list(u)) for u in u_list])
            if not entails(target, stepped):
                return False
    return True


def synthesize_y(cert: Cert, x: Sequence[int]) -> List[int]:
    """Exact mirror of Lean's `synthesizeY`."""
    def go(st_idx: int, xv: List[int]) -> List[int]:
        if sum(xv) == 0:
            return list(cert.entries[st_idx].base_y)
        ent = cert.entries[st_idx]
        b = [bool(v & 1) for v in xv]
        xp = [v >> 1 for v in xv]
        u_list, next_idx = ent.trans[index_of_bits(b)]
        yp = go(next_idx, xp)
        chosen = u_list[-1]
        for u in u_list:
            if eval_formula(step_formula(ent.formula, b + list(u)), xp + yp):
                chosen = u
                break
        return [2 * yv + int(uv) for yv, uv in zip(yp, chosen)]
    return go(0, list(x))


def compile_universal(d: int, root: Formula, max_states: int = 2000) -> Tuple[Optional[Cert], Optional[Tuple[int, ...]]]:
    """Compile a universal Carry-Presburger formula (e = 0) into a finite Cert or counterexample."""
    visited: Dict[Formula, Tuple[int, Optional[Formula], Optional[int]]] = {root: (0, None, None)}
    order: List[Formula] = [root]
    trans_map: Dict[int, List[Tuple[List[Tuple[bool, ...]], int]]] = {}
    q = deque([root])
    while q:
        cur = q.popleft()
        cid = visited[cur][0]
        if not eval_formula(cur, [0] * d):
            # Reconstruct minimal counterexample
            bits_hist = []
            st = cur
            while visited[st][1] is not None:
                _, par, bidx = visited[st]
                bits_hist.append(bits_of_index(d, bidx))
                st = par
            bits_hist.reverse()
            cex = [0] * d
            for pos, bs in enumerate(bits_hist):
                for j in range(d):
                    if bs[j]:
                        cex[j] |= (1 << pos)
            return None, tuple(cex)
        row = []
        for idx in range(1 << d):
            b = bits_of_index(d, idx)
            nxt = step_formula(cur, b)
            if nxt not in visited:
                if len(visited) >= max_states:
                    raise RuntimeError(f"State limit {max_states} exceeded")
                visited[nxt] = (len(order), cur, idx)
                order.append(nxt)
                q.append(nxt)
            row.append(([()], visited[nxt][0]))
        trans_map[cid] = row
    entries = [StateEntry(f, (), trans_map[i]) for i, f in enumerate(order)]
    cert = Cert(d=d, e=0, entries=entries)
    assert check_cert(cert), "Internal error: compiled universal cert failed check_cert"
    return cert, None


def compile_bounded_carry_ternary(
    m: int, r0: int, K: int, qy: int, px: int, c0: int, use_disj_for_k0: bool = True
) -> Tuple[Optional[Cert], Optional[int]]:
    """
    Compile ∀ x, ∃ y, (carry(x,y) <= K  [or x&y=0 if K=0 & use_disj_for_k0])
                       ∧ (x + y) % m = r0 ∧ qy*y - px*x <= c0
    into a compact, Lean-4-checked Carry-Presburger Cert (or exact minimal counterexample x).
    """
    t_x = NatAff((1, 0), 0)
    t_y = NatAff((0, 1), 0)

    def atom_to_formula(st: Tuple[int, bool, int, int]) -> Formula:
        r, cin, k, c = st
        if K == 0 and use_disj_for_k0:
            f1 = FAtom(BitRel4(MASK_AND_ZERO, t_x, t_y, NatAff(()), NatAff(())))
        else:
            f1 = FAtom(CarryLe(t_x, t_y, cin, k))
        f2 = FAtom(ModEq((1, 1), m, r))
        f3 = FAtom(LinLe(IntAff((-px, qy), c)))
        return mk_and(f1, mk_and(f2, f3))

    def macro_to_formula(macro: Tuple[Tuple[int, bool, int, int], ...]) -> Formula:
        return big_or([atom_to_formula(st) for st in macro])

    def step_st(st: Tuple[int, bool, int, int], b: int, u: int) -> Optional[Tuple[int, bool, int, int]]:
        r, cin, k, c = st
        if K == 0 and use_disj_for_k0:
            if b == 1 and u == 1:
                return None
            cout, k2 = False, 0
        else:
            bsum = b + u + int(cin)
            cout = bsum >= 2
            if cout:
                if k == 0:
                    return None
                k2 = k - 1
            else:
                k2 = k
        inv2 = (m + 1) // 2
        r2 = ((r - b - u) * inv2) % m
        c2 = (c - (qy * u - px * b)) // 2
        return (r2, cout, k2, c2)

    def prune(sts: Sequence[Tuple[int, bool, int, int]]) -> Tuple[Tuple[int, bool, int, int], ...]:
        by_rc: Dict[Tuple[int, bool], List[Tuple[int, int]]] = {}
        for r, cin, k, c in sts:
            by_rc.setdefault((r, cin), []).append((k, c))
        res = []
        for (r, cin), pts in sorted(by_rc.items()):
            pts = sorted(set(pts), key=lambda t: (-t[0], -t[1]))
            max_c = -10**9
            for k, c in pts:
                if c > max_c:
                    res.append((r, cin, k, c))
                    max_c = c
        return tuple(sorted(res))

    def base_witness(macro: Tuple[Tuple[int, bool, int, int], ...]) -> Optional[int]:
        for r, cin, k, c in macro:
            if c < 0:
                continue
            max_y = c // qy
            y0 = r
            while y0 <= max_y:
                if K == 0 and use_disj_for_k0:
                    return y0
                if carry_count(0, y0, cin) <= k:
                    return y0
                y0 += m
        return None

    init = prune([(r0, False, K, c0)])
    visited: Dict[Tuple[Tuple[int, bool, int, int], ...], Tuple[int, Optional[Tuple], Optional[int]]] = {
        init: (0, None, None)
    }
    order = [init]
    trans_ids: Dict[int, List[Tuple[List[Tuple[bool, ...]], int]]] = {}
    q = deque([init])
    while q:
        cur = q.popleft()
        cid = visited[cur][0]
        if base_witness(cur) is None:
            bits = []
            st = cur
            while visited[st][1] is not None:
                _, par, b = visited[st]
                bits.append(b)
                st = par
            bits.reverse()
            return None, sum(b << i for i, b in enumerate(bits))
        row = []
        for b in (0, 1):
            nxt_list = []
            used_u = []
            for u in (0, 1):
                sub = [st2 for st in cur if (st2 := step_st(st, b, u)) is not None]
                if sub:
                    used_u.append((bool(u),))
                    nxt_list.extend(sub)
            nxt = prune(nxt_list)
            if nxt not in visited:
                visited[nxt] = (len(order), cur, b)
                order.append(nxt)
                q.append(nxt)
            row.append((used_u, visited[nxt][0]))
        trans_ids[cid] = row

    entries = []
    for i, macro in enumerate(order):
        w = base_witness(macro)
        assert w is not None
        entries.append(StateEntry(macro_to_formula(macro), (w,), trans_ids[i]))
    cert = Cert(d=1, e=1, entries=entries)
    assert check_cert(cert), f"Internal error: compiled cert failed check_cert for K={K}, r={r0}"
    return cert, None


# ============================================================================
# 4. Lean 4 Certificate Emitter
# ============================================================================

def bool_list_lean(bs: Sequence[bool]) -> str:
    return "[" + ", ".join("true" if b else "false" for b in bs) + "]"


def cert_to_lean(name: str, cert: Cert) -> str:
    lines = [f"def {name} : Cert := {{"]
    lines.append(f"  d := {cert.d},")
    lines.append(f"  e := {cert.e},")
    lines.append("  entries := [")
    for idx, ent in enumerate(cert.entries):
        base_s = "[" + ", ".join(str(v) for v in ent.base_y) + "]"
        tr_parts = []
        for u_list, next_idx in ent.trans:
            us_s = "[" + ", ".join(bool_list_lean(u) for u in u_list) + "]"
            tr_parts.append(f"({us_s}, {next_idx})")
        tr_s = "[" + ", ".join(tr_parts) + "]"
        comma = "," if idx + 1 < len(cert.entries) else ""
        lines.append(f"    {{ formula := {ent.formula.to_lean()}, baseY := {base_s}, trans := {tr_s} }}{comma}")
    lines.append("  ]")
    lines.append("}")
    return "\n".join(lines)


# ============================================================================
# 5. Build All 20 Theorems, Independent Verification, Sharpness & Mutations
# ============================================================================

def build_all_certificates() -> Dict[str, Cert]:
    certs: Dict[str, Cert] = {}

    # Family I: All 9 Bounded-Carry Ternary Completion Phase-Transition Theorems
    family1_specs = [
        ("cert_ternary_k0_r0", 3, 0, 0, 3, 5, 5, True),
        ("cert_ternary_k0_r1", 3, 1, 0, 3, 5, 5, True),
        ("cert_ternary_k0_r2", 3, 2, 0, 1, 2, 2, True),
        ("cert_ternary_k1_r0", 3, 0, 1, 1, 1, 1, False),
        ("cert_ternary_k1_r1", 3, 1, 1, 1, 1, 1, False),
        ("cert_ternary_k1_r2", 3, 2, 1, 2, 1, 4, False),
        ("cert_ternary_k2_r0", 3, 0, 2, 4, 1, 7, False),
        ("cert_ternary_k2_r1", 3, 1, 2, 4, 1, 6, False),
        ("cert_ternary_k2_r2", 3, 2, 2, 2, 1, 4, False),
    ]
    for name, m, r, K, qy, px, c0, disj in family1_specs:
        c, cex = compile_bounded_carry_ternary(m, r, K, qy, px, c0, use_disj_for_k0=disj)
        assert c is not None and cex is None, f"{name} unexpectedly failed with cex={cex}"
        certs[name] = c

    # Family II: 4 Matching Infinite Extremal Lower Bounds (Universal e = 0)
    # 10. K=0, r=0: (z+1)&z=0 ∧ z%3=1 ∧ (3z+2)&y=0 ∧ (3z+2+y)%3=0 -> 15z - 3y <= -15
    f_lb_k0_r0 = mk_imp(
        big_and([
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 1), NatAff((1, 0), 0), NatAff(()), NatAff(()))),
            FAtom(ModEq((1, 0), 3, 1)),
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((3, 0), 2), NatAff((0, 1), 0), NatAff(()), NatAff(()))),
            FAtom(ModEq((3, 1), 3, 1)),  # (3z + 2 + y) % 3 = 0  <=>  (3z + y) % 3 = 1
        ]),
        FAtom(LinLe(IntAff((15, -3), -15))),
    )
    c, cex = compile_universal(2, f_lb_k0_r0)
    assert c is not None, f"lb_k0_r0 failed: {cex}"
    certs["cert_lb_k0_r0"] = c

    # 11. K=0, r=1: (z+1)&z=0 ∧ z%3=0 ∧ (3z+2)&y=0 ∧ (3z+2+y)%3=1 -> 15z - 3y <= -15
    f_lb_k0_r1 = mk_imp(
        big_and([
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 1), NatAff((1, 0), 0), NatAff(()), NatAff(()))),
            FAtom(ModEq((1, 0), 3, 0)),
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((3, 0), 2), NatAff((0, 1), 0), NatAff(()), NatAff(()))),
            FAtom(ModEq((3, 1), 3, 2)),  # (3z + 2 + y) % 3 = 1  <=>  (3z + y) % 3 = 2
        ]),
        FAtom(LinLe(IntAff((15, -3), -15))),
    )
    c, cex = compile_universal(2, f_lb_k0_r1)
    assert c is not None, f"lb_k0_r1 failed: {cex}"
    certs["cert_lb_k0_r1"] = c

    # 12. K=0, r=2: x&(x+1)=0 ∧ x&y=0 ∧ (x+y)%3=2 -> 2x - y <= -2
    f_lb_k0_r2 = mk_imp(
        big_and([
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 0), NatAff((1, 0), 1), NatAff(()), NatAff(()))),
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 0), NatAff((0, 1), 0), NatAff(()), NatAff(()))),
            FAtom(ModEq((1, 1), 3, 2)),
        ]),
        FAtom(LinLe(IntAff((2, -1), -2))),
    )
    c, cex = compile_universal(2, f_lb_k0_r2)
    assert c is not None, f"lb_k0_r2 failed: {cex}"
    certs["cert_lb_k0_r2"] = c

    # 13. K=2, r=2: x&(x+1)=0 ∧ carryCount(x,y,false)<=2 ∧ (x+y)%3=2 -> x - 2y <= -1
    f_lb_k2_r2 = mk_imp(
        big_and([
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 0), NatAff((1, 0), 1), NatAff(()), NatAff(()))),
            FAtom(CarryLe(NatAff((1, 0), 0), NatAff((0, 1), 0), False, 2)),
            FAtom(ModEq((1, 1), 3, 2)),
        ]),
        FAtom(LinLe(IntAff((1, -2), -1))),
    )
    c, cex = compile_universal(2, f_lb_k2_r2)
    assert c is not None, f"lb_k2_r2 failed: {cex}"
    certs["cert_lb_k2_r2"] = c

    # Family III: Mersenne-Collatz Affine Zero-Carry Rigidity (a = 3, 7, 15) + Popcount/Sparsity
    for a in (3, 7, 15):
        lhs = FAtom(BitRel4(MASK_AND_ZERO, NatAff((1,), 0), NatAff((a,), 1), NatAff(()), NatAff(())))
        rhs = FAtom(BitRel4(MASK_AND_ZERO, NatAff((a,), 1), NatAff((a,), 0), NatAff(()), NatAff(())))
        c, cex = compile_universal(1, mk_iff(lhs, rhs))
        assert c is not None, f"mersenne_collatz_{a} failed: {cex}"
        certs[f"cert_mersenne_collatz_{a}"] = c

    f_mc3_pop = mk_imp(
        FAtom(BitRel4(MASK_AND_ZERO, NatAff((1,), 0), NatAff((3,), 1), NatAff(()), NatAff(()))),
        mk_and(
            FAtom(PopMod(((1, NatAff((3,), 1)),), 2, 1)),
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1,), 0), NatAff((2,), 0), NatAff(()), NatAff(()))),
        ),
    )
    c, cex = compile_universal(1, f_mc3_pop)
    assert c is not None, f"mc3_pop failed: {cex}"
    certs["cert_mc3_pop_sparse"] = c

    # Family IV: Carry-Parity, Popcount-Mod, and Carry-Word Coupling Laws
    # 18. carryCount(x, y) <= 1 -> ((pop(x)+pop(y)-pop(x+y)) % 2 = 0 <-> x & y = 0)
    f_carry1_par = mk_imp(
        FAtom(CarryLe(NatAff((1, 0), 0), NatAff((0, 1), 0), False, 1)),
        mk_iff(
            FAtom(PopMod(((1, NatAff((1, 0), 0)), (1, NatAff((0, 1), 0)), (-1, NatAff((1, 1), 0))), 2, 0)),
            FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 0), NatAff((0, 1), 0), NatAff(()), NatAff(()))),
        ),
    )
    c, cex = compile_universal(2, f_carry1_par)
    assert c is not None, f"carry1_par failed: {cex}"
    certs["cert_carry1_parity_disj"] = c

    # 19. ((x + y) ^^^ x ^^^ y = 0) <-> (x &&& y = 0)
    f_cw_zero = mk_iff(
        FAtom(BitRel4(MASK_XOR3_EQ0, NatAff((1, 1), 0), NatAff((1, 0), 0), NatAff((0, 1), 0), NatAff(()))),
        FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0), 0), NatAff((0, 1), 0), NatAff(()), NatAff(()))),
    )
    c, cex = compile_universal(2, f_cw_zero)
    assert c is not None, f"cw_zero failed: {cex}"
    certs["cert_carry_word_zero"] = c

    # 20. x & (2*x) = 0 -> popcount(3*x) % 2 = 0
    f_sparse_evil = mk_imp(
        FAtom(BitRel4(MASK_AND_ZERO, NatAff((1,), 0), NatAff((2,), 0), NatAff(()), NatAff(()))),
        FAtom(PopMod(((1, NatAff((3,), 0)),), 2, 0)),
    )
    c, cex = compile_universal(1, f_sparse_evil)
    assert c is not None, f"sparse_evil failed: {cex}"
    certs["cert_sparse_triple_evil"] = c

    return certs


def run_independent_verification(certs: Dict[str, Cert]) -> None:
    print("=== 1. Synthesized Certificate Summary ===")
    total_states = 0
    for name, c in certs.items():
        ok = check_cert(c)
        assert ok, f"check_cert FAILED for {name}"
        total_states += len(c.entries)
        print(f"  {name:28s}: d={c.d}, e={c.e}, states={len(c.entries):3d}, checkCert=True")
    print(f"  TOTAL: {len(certs)} certificates, {total_states} states, 100% PASS.\n")

    print("=== 2. Independent Exact Replay of Synthesized Skolem Transducers (x = 0..4095) ===")
    f1_checks = [
        ("cert_ternary_k0_r0", 0, 0, 3, 5, 5),
        ("cert_ternary_k0_r1", 0, 1, 3, 5, 5),
        ("cert_ternary_k0_r2", 0, 2, 1, 2, 2),
        ("cert_ternary_k1_r0", 1, 0, 1, 1, 1),
        ("cert_ternary_k1_r1", 1, 1, 1, 1, 1),
        ("cert_ternary_k1_r2", 1, 2, 2, 1, 4),
        ("cert_ternary_k2_r0", 2, 0, 4, 1, 7),
        ("cert_ternary_k2_r1", 2, 1, 4, 1, 6),
        ("cert_ternary_k2_r2", 2, 2, 2, 1, 4),
    ]
    for name, K, r, qy, px, c0 in f1_checks:
        cert = certs[name]
        sample = []
        for x in range(4096):
            y = synthesize_y(cert, [x])[0]
            assert carry_count(x, y, False) <= K, f"Carry violation at {name} x={x} y={y}"
            if K == 0:
                assert (x & y) == 0, f"Disjoint violation at {name} x={x} y={y}"
            assert (x + y) % 3 == r, f"Mod violation at {name} x={x} y={y}"
            assert qy * y <= px * x + c0, f"Bound violation at {name} x={x} y={y}"
            if x in (0, 1, 2, 5, 7, 11, 23, 31):
                sample.append((x, y))
        print(f"  {name:22s}: verified all 4096 inputs; sample (x,y)={sample[:5]}")

    print("\n=== 3. Exact Sharpness & Falsification Counterexamples ===")
    sharp_specs = [
        ("K=0,r=0: 3y <= 5x + 4", 3, 0, 0, 3, 5, 4, True),
        ("K=0,r=1: 3y <= 5x + 4", 3, 1, 0, 3, 5, 4, True),
        ("K=0,r=2:  y <= 2x + 1", 3, 2, 0, 1, 2, 1, True),
        ("K=1,r=0:  y <=  x + 0", 3, 0, 1, 1, 1, 0, False),
        ("K=1,r=1:  y <=  x + 0", 3, 1, 1, 1, 1, 0, False),
        ("K=1,r=2: 2y <=  x + 3", 3, 2, 1, 2, 1, 3, False),
        ("K=2,r=0: 4y <=  x + 6", 3, 0, 2, 4, 1, 6, False),
        ("K=2,r=1: 4y <=  x + 5", 3, 1, 2, 4, 1, 5, False),
        ("K=2,r=2: 2y <=  x + 3", 3, 2, 2, 2, 1, 3, False),
        ("K=2,r=2: 4y <=  x + 100 (slope 1/4 fails!)", 3, 2, 2, 4, 1, 100, False),
    ]
    for label, m, r, K, qy, px, c0, disj in sharp_specs:
        c, cex = compile_bounded_carry_ternary(m, r, K, qy, px, c0, use_disj_for_k0=disj)
        assert c is None and cex is not None, f"Expected sharpness failure for {label}"
        # Independently verify by brute force that NO y satisfies the tightened bound at x = cex!
        max_y = (px * cex + c0) // qy
        for y in range(max_y + 1):
            if carry_count(cex, y, False) <= K and (cex + y) % m == r:
                raise AssertionError(f"False counterexample x={cex}, y={y} works for {label}")
        print(f"  REFUTED {label:44s} -> exact counterexample x* = {cex} (brute-force confirmed)")

    # Non-Mersenne a = 5 sharpness
    f_mc5 = mk_iff(
        FAtom(BitRel4(MASK_AND_ZERO, NatAff((1,), 0), NatAff((5,), 1), NatAff(()), NatAff(()))),
        FAtom(BitRel4(MASK_AND_ZERO, NatAff((5,), 1), NatAff((5,), 0), NatAff(()), NatAff(()))),
    )
    c5, cex5 = compile_universal(1, f_mc5)
    assert c5 is None and cex5 == (1,)
    assert (1 & (5 * 1 + 1)) == 0 and ((5 * 1 + 1) & (5 * 1)) == 4 != 0
    print(f"  REFUTED Mersenne-Collatz a=5 (non-Mersenne)    -> exact counterexample x* = 1 (1&6=0, 6&5=4)")

    # Carry <= 2 breaks parity-iff-disjoint at (3, 1)
    assert carry_count(3, 1, False) == 2 and (popcount(3) + popcount(1) - popcount(4)) % 2 == 0 and (3 & 1) == 1
    print("  REFUTED carryCount<=2 parity-iff-disjoint      -> exact counterexample (x,y) = (3, 1)")

    print("\n=== 4. Hostile Certificate Mutation Suite (All MUST Be Rejected) ===")
    good = certs["cert_ternary_k0_r2"]
    mutations = [
        ("empty_entries", Cert(1, 1, [])),
        ("bad_baseY", Cert(1, 1, [StateEntry(good.entries[0].formula, (0,), good.entries[0].trans)] + good.entries[1:])),
        ("wrong_nextIdx", Cert(1, 1, [
            StateEntry(good.entries[0].formula, good.entries[0].base_y,
                       [(good.entries[0].trans[0][0], (good.entries[0].trans[0][1] + 1) % len(good.entries)),
                        good.entries[0].trans[1]])
        ] + good.entries[1:])),
        ("tightened_false_root", Cert(1, 1, [
            StateEntry(
                mk_and(
                    FAtom(BitRel4(MASK_AND_ZERO, NatAff((1, 0)), NatAff((0, 1)), NatAff(()), NatAff(()))),
                    mk_and(FAtom(ModEq((1, 1), 3, 2)), FAtom(LinLe(IntAff((-2, 1), 1)))),
                ),
                good.entries[0].base_y, good.entries[0].trans
            )
        ] + good.entries[1:])),
        ("empty_uList", Cert(1, 1, [
            StateEntry(good.entries[0].formula, good.entries[0].base_y,
                       [([], good.entries[0].trans[0][1]), good.entries[0].trans[1]])
        ] + good.entries[1:])),
        ("truncated_trans", Cert(1, 1, [
            StateEntry(good.entries[0].formula, good.entries[0].base_y, [good.entries[0].trans[0]])
        ] + good.entries[1:])),
    ]
    for mname, bad in mutations:
        res = check_cert(bad)
        assert not res, f"SECURITY BUG: hostile mutation {mname} was ACCEPTED!"
        print(f"  REJECTED hostile mutation {mname:24s}: checkCert = {res}")


if __name__ == "__main__":
    certs = build_all_certificates()
    run_independent_verification(certs)
    if "--emit-lean" in sys.argv:
        out_path = sys.argv[sys.argv.index("--emit-lean") + 1]
        with open(out_path, "w", encoding="utf-8") as f:
            for name, cert in certs.items():
                f.write(cert_to_lean(name, cert) + "\n\n")
        print(f"\nEmitted {len(certs)} Lean 4 certificates to {out_path}")
