#!/usr/bin/env python3
"""
Exact Pure-Silicon Verification & Counterexample Explorer for
Task 15: Generalized Carry-Lookahead Prefix-Monoid Engine.

All arithmetic is 100% exact Python integers (zero floating point).
Tests:
  1. Exact Affine-Floor Monoid M_div composition and mixed-radix / base-b lifting
  2. Canonical Threshold-Step Semigroup T: semantics, injectivity, associativity,
     aperiodicity (e^3 = e^2), and exact finite size |T_[L,U]| = N^2 - N + 1
  3. Super-Critical Collapse Theorem (M >= U - L) and Sharpness Obstruction (M < U - L)
  4. Associative-Tree Universality across arbitrary binary tree topologies
     (ripple, right-leaning, balanced/Sklansky, random unbalanced trees)
  5. Sharpness counterexample when the carry invariant [L, U] is violated
  6. Exact Carry-Absorption Resonance Law for arbitrary width w >= 1, plus
     3-input binary / signed-borrow (x+y-z) exact resonance count = 2^(w+1)
     (digit strings) and 2 * 4^w (binary triples)
  7. Modulo-(M - delta) Crandall / Mersenne feedback & Modulo-(M + 1) Fermat
     negative-feedback dichotomy (exact fixed points vs period-2 oscillation)
  8. General Modulo-m Affine Prefix Monoid A_m and exact absorption criterion m | b^w
"""

from dataclasses import dataclass
from math import gcd
from typing import Callable, List, Optional, Tuple, Union
import random


# ============================================================================
# 1. Exact Floor Division & Affine-Floor Monoid M_div
# ============================================================================

def ediv(a: int, m: int) -> int:
    assert m > 0
    return a // m  # Python // is exact floor division for m > 0


def emod(a: int, m: int) -> int:
    assert m > 0
    return a % m


@dataclass(frozen=True)
class DivElem:
    mod: int  # M > 0
    sum: int  # S in Z

    def act(self, c: int) -> int:
        return ediv(c + self.sum, self.mod)

    @staticmethod
    def one() -> "DivElem":
        return DivElem(1, 0)

    def comp(self, lo: "DivElem") -> "DivElem":
        # (hi ⋆ lo)(c) = hi(lo(c))
        return DivElem(lo.mod * self.mod, lo.sum + lo.mod * self.sum)


# ============================================================================
# 2. Canonical Threshold-Step Semigroup T
# ============================================================================

@dataclass(frozen=True)
class ThreshConst:
    q: int

    def eval(self, c: int) -> int:
        return self.q


@dataclass(frozen=True)
class ThreshStep:
    q: int
    t: int

    def eval(self, c: int) -> int:
        return self.q + (1 if c >= self.t else 0)


ThreshElem = Union[ThreshConst, ThreshStep]


def tcomp(hi: ThreshElem, lo: ThreshElem) -> ThreshElem:
    if isinstance(hi, ThreshConst):
        return hi
    if isinstance(lo, ThreshConst):
        return ThreshConst(hi.q + (1 if lo.q >= hi.t else 0))
    # Both step
    if lo.q >= hi.t:
        return ThreshConst(hi.q + 1)
    elif lo.q + 1 < hi.t:
        return ThreshConst(hi.q)
    else:
        # lo.q + 1 == hi.t (Resonance Lock!)
        return ThreshStep(hi.q, lo.t)


def collapse(L: int, U: int, d: DivElem) -> ThreshElem:
    assert L <= U and d.mod >= U - L and d.mod > 0
    q = ediv(L + d.sum, d.mod)
    r = emod(L + d.sum, d.mod)
    if r + (U - L) < d.mod:
        return ThreshConst(q)
    else:
        return ThreshStep(q, L + d.mod - r)


# ============================================================================
# 3. Binary Prefix Trees (Arbitrary Topologies)
# ============================================================================

@dataclass(frozen=True)
class Leaf:
    val: object


@dataclass(frozen=True)
class Node:
    lo: "PrefixTree"
    hi: "PrefixTree"


PrefixTree = Union[Leaf, Node]


def fringe(tree: PrefixTree) -> List[object]:
    if isinstance(tree, Leaf):
        return [tree.val]
    return fringe(tree.lo) + fringe(tree.hi)


def eval_tree(tree: PrefixTree, enc: Callable, mul: Callable):
    if isinstance(tree, Leaf):
        return enc(tree.val)
    return mul(eval_tree(tree.hi, enc, mul), eval_tree(tree.lo, enc, mul))


def build_ripple_left(items: List[object]) -> PrefixTree:
    t: PrefixTree = Leaf(items[0])
    for x in items[1:]:
        t = Node(t, Leaf(x))
    return t


def build_ripple_right(items: List[object]) -> PrefixTree:
    t: PrefixTree = Leaf(items[-1])
    for x in reversed(items[:-1]):
        t = Node(Leaf(x), t)
    return t


def build_balanced(items: List[object]) -> PrefixTree:
    if len(items) == 1:
        return Leaf(items[0])
    mid = len(items) // 2
    return Node(build_balanced(items[:mid]), build_balanced(items[mid:]))


def build_random_tree(items: List[object], rng: random.Random) -> PrefixTree:
    if len(items) == 1:
        return Leaf(items[0])
    cut = rng.randint(1, len(items) - 1)
    return Node(build_random_tree(items[:cut], rng), build_random_tree(items[cut:], rng))


# ============================================================================
# 4. Modulo-m Affine Prefix Monoid A_m
# ============================================================================

@dataclass(frozen=True)
class AffMod:
    m: int
    a: int
    r: int

    def act(self, c: int) -> int:
        return (self.a * c + self.r) % self.m

    def comp(self, lo: "AffMod") -> "AffMod":
        assert self.m == lo.m
        return AffMod(self.m, (self.a * lo.a) % self.m, (self.a * lo.r + self.r) % self.m)


# ============================================================================
# Verification Suite
# ============================================================================

def test_1_div_monoid():
    for m1 in range(1, 9):
        for m2 in range(1, 9):
            for s1 in range(-6, 7):
                for s2 in range(-6, 7):
                    d1 = DivElem(m1, s1)
                    d2 = DivElem(m2, s2)
                    d12 = d2.comp(d1)
                    for c in range(-8, 9):
                        assert d12.act(c) == d2.act(d1.act(c))
    print("[PASS] 1. Exact Affine-Floor Monoid M_div composition law verified.")


def test_2_thresh_semigroup():
    # Enumerate T_[L, U] for several (L, U)
    for L, U in [(0, 1), (-1, 0), (0, 2), (-1, 1), (-2, 1), (0, 4)]:
        N = U - L + 1
        elems: List[ThreshElem] = [ThreshConst(q) for q in range(L, U + 1)]
        elems += [ThreshStep(q, t) for q in range(L, U) for t in range(L + 1, U + 1)]
        assert len(elems) == N * N - N + 1

        # Closure, exact semantics, injectivity on [L, U], aperiodicity e^3 = e^2
        table_seen = {}
        for e in elems:
            vec = tuple(e.eval(c) for c in range(L, U + 1))
            assert vec not in table_seen, f"Non-injective on [{L},{U}]: {e} vs {table_seen[vec]}"
            table_seen[vec] = e

            e2 = tcomp(e, e)
            e3 = tcomp(e, e2)
            assert e3 == e2, f"Aperiodicity failed: {e}"
            is_self_res = isinstance(e, ThreshStep) and (e.q + 1 == e.t)
            assert isinstance(e2, ThreshConst) == (not is_self_res)

        for e2 in elems:
            for e1 in elems:
                e21 = tcomp(e2, e1)
                assert e21 in elems, f"Not closed: {e2} o {e1} = {e21}"
                for c in range(L - 3, U + 4):
                    assert e21.eval(c) == e2.eval(e1.eval(c))

        # Check associativity on a subset / full set for small N
        if N <= 4:
            for a in elems:
                for b in elems:
                    for c in elems:
                        assert tcomp(a, tcomp(b, c)) == tcomp(tcomp(a, b), c)
    print("[PASS] 2. Threshold-Step Semigroup T_[L,U]: size N^2-N+1, closure, injectivity, assoc, e^3=e^2 verified.")


def test_3_collapse_and_sharpness():
    # Super-critical collapse: M >= U - L
    for L in range(-3, 2):
        for delta in range(1, 6):
            U = L + delta
            for M in range(delta, delta + 4):
                for S in range(-12, 13):
                    d = DivElem(M, S)
                    te = collapse(L, U, d)
                    for c in range(L, U + 1):
                        assert te.eval(c) == d.act(c)
                    # Check exact constancy equivalence on [L, U]
                    vals = {d.act(c) for c in range(L, U + 1)}
                    assert isinstance(te, ThreshConst) == (len(vals) == 1)

    # Sharpness obstruction: M < U - L => S = M - 1 - L hits 3 distinct values {0, 1, 2}
    obstructions = []
    for L in range(-3, 2):
        for delta in range(2, 7):
            U = L + delta
            for M in range(1, delta):
                S = M - 1 - L
                d = DivElem(M, S)
                v0 = d.act(L)
                v1 = d.act(L + 1)
                v2 = d.act(L + M + 1)
                assert L + M + 1 <= U
                assert (v0, v1, v2) == (0, 1, 2)
                obstructions.append((L, U, M, S))
    assert len(obstructions) > 0

    # Concrete base-2 k=4 sharpness witness at w=1: L=0, U=3, M=2, S=1
    d4 = DivElem(2, 1)
    assert [d4.act(c) for c in range(4)] == [0, 1, 1, 2]
    print(f"[PASS] 3. Collapse (M >= U-L) & Sharpness Obstruction (M < U-L, {len(obstructions)} cases; k=4, w=1 witness [0,1,1,2]) verified.")


def test_4_trees_and_invariant_sharpness():
    rng = random.Random(20261126)
    # Signed multi-input base-b: p added, q subtracted => L = -q, U = p - 1, delta = p + q - 1
    configs = [
        (2, 2, 0),  # classical 2-input addition: c in [0,1], w*=1
        (2, 1, 1),  # 2-input signed subtraction x-y: c in [-1,0], w*=1
        (2, 3, 0),  # 3-input addition x+y+z: c in [0,2], w*=1
        (2, 2, 1),  # 3-input signed x+y-z: c in [-1,1], w*=1
        (2, 4, 0),  # 4-input addition: c in [0,3], w*=2 (2^2=4 >= 3)
        (2, 3, 2),  # 5-input signed x1+x2+x3-y1-y2: c in [-2,2], w*=2 (2^2=4 >= 4)
        (3, 4, 0),  # base-3 4-input: c in [0,3], w*=1 (3^1=3 >= 3)
        (10, 5, 3), # BCD-like base-10 8-input signed: c in [-3,4], w*=1 (10 >= 7)
    ]
    for b, p, q in configs:
        L, U = -q, p - 1
        delta = U - L
        w_star = 1
        while b ** w_star < delta:
            w_star += 1
        M_blk = b ** w_star
        dmin = -q * (b - 1)
        dmax = p * (b - 1)

        # Generate random super-blocks (each of width w_star)
        for num_blocks in [1, 2, 5, 12]:
            blocks = []
            for _ in range(num_blocks):
                S_blk = sum(rng.randint(dmin, dmax) * (b ** i) for i in range(w_star))
                blocks.append(DivElem(M_blk, S_blk))

            # Verify carry invariant [L, U] on every block
            for blk in blocks:
                for c in range(L, U + 1):
                    assert L <= blk.act(c) <= U

            enc_t = lambda blk: collapse(L, U, blk)
            t_left = build_ripple_left(blocks)
            t_right = build_ripple_right(blocks)
            t_bal = build_balanced(blocks)
            t_rand = build_random_tree(blocks, rng)

            res_left = eval_tree(t_left, enc_t, tcomp)
            res_right = eval_tree(t_right, enc_t, tcomp)
            res_bal = eval_tree(t_bal, enc_t, tcomp)
            res_rand = eval_tree(t_rand, enc_t, tcomp)
            assert res_left == res_right == res_bal == res_rand

            # Compare against exact multi-block DivElem composition
            exact_div = eval_tree(t_left, lambda x: x, lambda hi, lo: hi.comp(lo))
            for c in range(L, U + 1):
                assert res_left.eval(c) == exact_div.act(c)

    # Sharpness counterexample: violating carry invariant [L, U] breaks collapse homomorphism!
    L, U = 0, 2
    d1 = DivElem(2, 6)  # illegal digit sum S1 = 6: maps c=2 -> (2+6)//2 = 4 not in [0,2]
    d2 = DivElem(2, 0)
    lhs = tcomp(collapse(L, U, d2), collapse(L, U, d1)).eval(2)
    rhs = d2.comp(d1).act(2)
    assert lhs == 1 and rhs == 2 and lhs != rhs
    print("[PASS] 4. Associative-Tree Universality across 8 multi-input/signed/base configs + invariant-violation counterexample (lhs=1 != rhs=2) verified.")


def test_5_absorption_and_3input_counting():
    # Exact 3-input binary addition (L=0, U=2, s_i in {0,1,2,3})
    # Exact signed 3-input x+y-z (L=-1, U=1, d_i in {-1,0,1,2})
    for w in range(1, 7):
        prop_digits = 0
        prop_triples = 0
        for code in range(4 ** w):
            digits = []
            tmp = code
            for _ in range(w):
                digits.append(tmp % 4)
                tmp //= 4
            # Check resonance lock: (s_i // 2) + (s_{i+1} % 2) == 1
            res_lock = all((digits[i] // 2) + (digits[i + 1] % 2) == 1 for i in range(w - 1))

            # Evaluate in T via balanced tree
            enc = lambda s: collapse(0, 2, DivElem(2, s))
            te = eval_tree(build_balanced(digits), enc, tcomp)
            is_non_absorbing = isinstance(te, ThreshStep)
            assert is_non_absorbing == res_lock

            # Also check signed 3-input x+y-z by shifting d_i = s_i - 1, L=-1, U=1
            enc_signed = lambda s: collapse(-1, 1, DivElem(2, s - 1))
            te_signed = eval_tree(build_balanced(digits), enc_signed, tcomp)
            assert isinstance(te_signed, ThreshStep) == res_lock

            # Exact direct check on S = sum s_i 2^i
            S = sum(digits[i] * (2 ** i) for i in range(w))
            vals = {ediv(c + S, 2 ** w) for c in (0, 1, 2)}
            assert (len(vals) == 2) == res_lock

            if res_lock:
                prop_digits += 1
                # multiplicity of (x_i, y_i, z_i) yielding s_i: C(3, s_i) in {1, 3, 3, 1}
                mult = 1
                for s in digits:
                    mult *= (1 if s in (0, 3) else 3)
                prop_triples += mult

        assert prop_digits == 2 ** (w + 1), f"w={w}: got {prop_digits}"
        assert prop_triples == 2 * (4 ** w), f"w={w}: got {prop_triples}"
    print("[PASS] 5. Exact 3-input & signed-3-input Carry-Absorption Resonance Law & counts (2^(w+1) digit strings, 2*4^w triples) verified for w=1..6.")


def test_6_modulo_feedback():
    # (A) Positive Crandall / Mersenne feedback: m = M - delta, delta >= 1, M >= delta * (U - L)
    for L, U in [(0, 1), (0, 2), (-1, 1), (-1, 2)]:
        delta_span = U - L
        for delta in [1, 2, 3, 5]:
            M = max(delta * delta_span, delta + 2)
            m = M - delta
            # Test a wide range of S preserving G_delta([L,U]) subset [L,U]
            dual_count = 0
            for S in range(L * m - M, (U + 1) * m + M):
                G = lambda c: ediv(delta * c + S, M)
                if not all(L <= G(c) <= U for c in range(L, U + 1)):
                    continue
                e = collapse(delta * L, delta * U, DivElem(M, S))
                for c in range(L, U + 1):
                    assert G(c) == e.eval(delta * c)

                fps = [c for c in range(L, U + 1) if G(c) == c]
                # Check exact classification
                if isinstance(e, ThreshStep) and delta * e.q < e.t <= delta * (e.q + 1):
                    assert fps == [e.q, e.q + 1]
                    assert (e.q + 1) * m <= S < (e.q + 1) * m + delta
                    dual_count += 1
                    # Canonical upper fixed point gives residue in [0, delta - 1],
                    # which is canonical (< m) whenever M >= 2*delta (i.e. delta <= m).
                    c_canon = e.q + 1
                    R = emod(delta * c_canon + S, M)
                    assert 0 <= R < delta and (R - S) % m == 0
                    if M >= 2 * delta:
                        assert R < m
                else:
                    assert len(fps) == 1
                    c_star = fps[0]
                    # 2-step stabilization for ALL c0 in [L, U]
                    for c0 in range(L, U + 1):
                        assert G(G(c0)) == c_star
                    R = emod(delta * c_star + S, M)
                    assert 0 <= R < M and (R - S) % m == 0
            assert dual_count > 0

    # Sharpness counterexample for M < 2*delta: M=7, delta=5, m=2, S=4
    assert emod(5 * 1 + 4, 7) == 2 and ediv(5 * 1 + 4, 7) == 1 and 2 >= (7 - 5)

    # (B) Negative / Fermat feedback: m = M + 1, H(c) = ediv(-c + S, M)
    osc_count = 0
    for L, U in [(0, 1), (-1, 1), (-2, 1), (-1, 2)]:
        delta_span = U - L
        for M in range(delta_span, delta_span + 5):
            m = M + 1
            for S in range(-3 * M, 4 * M):
                H = lambda c: ediv(-c + S, M)
                if not all(L <= H(c) <= U for c in range(L, U + 1)):
                    continue
                e = collapse(-U, -L, DivElem(M, S))
                for c in range(L, U + 1):
                    assert H(c) == e.eval(-c)

                fps = [c for c in range(L, U + 1) if H(c) == c]
                if isinstance(e, ThreshStep) and e.q + e.t == 0:
                    assert fps == []
                    assert H(e.q) == e.q + 1 and H(e.q + 1) == e.q
                    assert S == (e.q + 1) * (M + 1) - 1
                    osc_count += 1
                else:
                    assert len(fps) == 1
                    c_star = fps[0]
                    for c0 in range(L, U + 1):
                        assert H(H(c0)) == c_star
                    R = emod(-c_star + S, M)
                    assert 0 <= R < M and (R - S) % m == 0
    assert osc_count > 0
    print(f"[PASS] 6. Modulo-(M-delta) Crandall/Mersenne & Modulo-(M+1) Fermat Feedback Dichotomy ({osc_count} exact period-2 oscillation witnesses) verified.")


def test_7_general_mod_m_affine():
    for m in range(1, 25):
        for b in [2, 3, 6, 10]:
            for w in range(0, 7):
                elem = AffMod(m, pow(b, w, m), 3 % m)
                img = {elem.act(c) for c in range(m)}
                expected_size = m // gcd(m, b ** w)
                assert len(img) == expected_size
                is_const = (len(img) == 1)
                assert is_const == ((b ** w) % m == 0)
    print("[PASS] 7. General Modulo-m Affine Monoid A_m: exact image size m / gcd(m, b^w) & absorption iff m | b^w verified.")


if __name__ == "__main__":
    test_1_div_monoid()
    test_2_thresh_semigroup()
    test_3_collapse_and_sharpness()
    test_4_trees_and_invariant_sharpness()
    test_5_absorption_and_3input_counting()
    test_6_modulo_feedback()
    test_7_general_mod_m_affine()
    print("\nALL 7 PURE-SILICON VERIFICATION SUITES PASSED WITH ZERO FLOATING POINT.")
