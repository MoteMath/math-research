#!/usr/bin/env python3
"""
Exact pure-silicon exploration & independent verification replay for Task 17 (dynsil-17):
Mixed Bitwise-Arithmetic Permutation-Polynomial Engine Mod 2^w.

Zero floating point anywhere. Exact arbitrary-precision Python integers & bitmasks only.
Mirrors every Lean 4 theorem and BSDA instantiation in `Proof.lean`.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, Dict, Tuple, List, Any


# ============================================================
# 1. Mixed Bitwise-Arithmetic AST (matches Lean 4 `MixedExpr`)
# ============================================================

class Expr:
    pass

@dataclass(frozen=True)
class Var(Expr):
    pass

@dataclass(frozen=True)
class Const(Expr):
    c: int

@dataclass(frozen=True)
class Not(Expr):
    e: Expr

@dataclass(frozen=True)
class Shl(Expr):
    k: int
    e: Expr

@dataclass(frozen=True)
class Add(Expr):
    a: Expr
    b: Expr

@dataclass(frozen=True)
class Sub(Expr):
    a: Expr
    b: Expr

@dataclass(frozen=True)
class Xor(Expr):
    a: Expr
    b: Expr

@dataclass(frozen=True)
class And(Expr):
    a: Expr
    b: Expr

@dataclass(frozen=True)
class Or(Expr):
    a: Expr
    b: Expr

@dataclass(frozen=True)
class Mul(Expr):
    a: Expr
    b: Expr


def int_bit(c: int, i: int) -> int:
    """Two's complement bit i of signed integer c."""
    if c >= 0:
        return (c >> i) & 1
    return 1 ^ (((-c - 1) >> i) & 1)


def int_sig_bits(c: int) -> int:
    """Smallest L >= 0 such that int_bit(c, i) == (c < 0) for all i >= L."""
    if c >= 0:
        return c.bit_length()
    return (-c - 1).bit_length()


def eval_mod(e: Expr, x: int, w: int) -> int:
    """Exact BitVec w semantics on {0, ..., 2^w - 1}."""
    mask = (1 << w) - 1
    if isinstance(e, Var): return x & mask
    if isinstance(e, Const): return e.c & mask
    if isinstance(e, Not): return (~eval_mod(e.e, x, w)) & mask
    if isinstance(e, Shl): return (eval_mod(e.e, x, w) << e.k) & mask
    if isinstance(e, Add): return (eval_mod(e.a, x, w) + eval_mod(e.b, x, w)) & mask
    if isinstance(e, Sub): return (eval_mod(e.a, x, w) - eval_mod(e.b, x, w)) & mask
    if isinstance(e, Xor): return (eval_mod(e.a, x, w) ^ eval_mod(e.b, x, w)) & mask
    if isinstance(e, And): return (eval_mod(e.a, x, w) & eval_mod(e.b, x, w)) & mask
    if isinstance(e, Or): return (eval_mod(e.a, x, w) | eval_mod(e.b, x, w)) & mask
    if isinstance(e, Mul): return (eval_mod(e.a, x, w) * eval_mod(e.b, x, w)) & mask
    raise TypeError(e)


def is_bijective_bruteforce(e: Expr, w: int) -> Tuple[bool, Optional[Tuple[int, int]]]:
    """Exact exhaustive bijection check mod 2^w; returns (True, None) or (False, (x, y))."""
    seen: Dict[int, int] = {}
    for x in range(1 << w):
        y = eval_mod(e, x, w)
        if y in seen:
            return False, (seen[y], x)
        seen[y] = x
    return True, None


# ============================================================
# 2. Pure-Data BSDA Compiler & Reachability Engine (matches Lean 4)
# ============================================================

class FullTransducer:
    def __init__(self, init_state: Any, step_fn, out_fn, sig_bits: int):
        self.init_state = init_state
        self.step_fn = step_fn
        self.out_fn = out_fn
        self.sig_bits = sig_bits

    def val0(self, i: int, q: Any) -> int:
        return self.out_fn(i, q, 0)

    def deriv(self, i: int, q: Any) -> int:
        return self.out_fn(i, q, 1) ^ self.out_fn(i, q, 0)


class DerivAutomaton:
    def __init__(self, bit0: Tuple[int, int], init1_fn, step_fn, deriv_fn, L: int):
        self.bit0 = bit0
        self.init1_fn = init1_fn
        self.step_fn = step_fn
        self.deriv_fn = deriv_fn
        self.L = max(1, L)


def compile_full(e: Expr) -> Optional[FullTransducer]:
    if isinstance(e, Var):
        return FullTransducer((), lambda i, q, b: (), lambda i, q, b: b, 0)
    if isinstance(e, Const):
        c = e.c
        return FullTransducer((), lambda i, q, b: (), lambda i, q, b: int_bit(c, i), int_sig_bits(c))
    if isinstance(e, Not):
        t = compile_full(e.e)
        if t is None: return None
        return FullTransducer(t.init_state, t.step_fn, lambda i, q, b: 1 ^ t.out_fn(i, q, b), t.sig_bits)
    if isinstance(e, Shl):
        t = compile_full(e.e)
        if t is None: return None
        k = e.k
        if k == 0: return t
        init = (t.init_state, (0,) * k)
        return FullTransducer(
            init,
            lambda i, q, b: (t.step_fn(i, q[0], b), q[1][1:] + (t.out_fn(i, q[0], b),)),
            lambda i, q, b: q[1][0],
            t.sig_bits,
        )
    if isinstance(e, (Xor, And, Or)):
        ta, tb = compile_full(e.a), compile_full(e.b)
        if ta is None or tb is None: return None
        step = lambda i, q, b: (ta.step_fn(i, q[0], b), tb.step_fn(i, q[1], b))
        if isinstance(e, Xor):
            out = lambda i, q, b: ta.out_fn(i, q[0], b) ^ tb.out_fn(i, q[1], b)
        elif isinstance(e, And):
            out = lambda i, q, b: ta.out_fn(i, q[0], b) & tb.out_fn(i, q[1], b)
        else:
            out = lambda i, q, b: ta.out_fn(i, q[0], b) | tb.out_fn(i, q[1], b)
        return FullTransducer((ta.init_state, tb.init_state), step, out, max(ta.sig_bits, tb.sig_bits))
    if isinstance(e, Add):
        ta, tb = compile_full(e.a), compile_full(e.b)
        if ta is None or tb is None: return None
        def step(i, q, b):
            qa, qb, c = q
            va, vb = ta.out_fn(i, qa, b), tb.out_fn(i, qb, b)
            return (ta.step_fn(i, qa, b), tb.step_fn(i, qb, b), (va & vb) | (va & c) | (vb & c))
        def out(i, q, b):
            qa, qb, c = q
            return ta.out_fn(i, qa, b) ^ tb.out_fn(i, qb, b) ^ c
        return FullTransducer((ta.init_state, tb.init_state, 0), step, out, max(ta.sig_bits, tb.sig_bits))
    if isinstance(e, Sub):
        ta, tb = compile_full(e.a), compile_full(e.b)
        if ta is None or tb is None: return None
        def step(i, q, b):
            qa, qb, brw = q
            va, vb = ta.out_fn(i, qa, b), tb.out_fn(i, qb, b)
            return (ta.step_fn(i, qa, b), tb.step_fn(i, qb, b), ((1 ^ va) & vb) | ((1 ^ va) & brw) | (vb & brw))
        def out(i, q, b):
            qa, qb, brw = q
            return ta.out_fn(i, qa, b) ^ tb.out_fn(i, qb, b) ^ brw
        return FullTransducer((ta.init_state, tb.init_state, 0), step, out, max(ta.sig_bits, tb.sig_bits))
    return None


def full_to_deriv(t: FullTransducer) -> DerivAutomaton:
    return DerivAutomaton(
        bit0=(t.out_fn(0, t.init_state, 0), t.out_fn(0, t.init_state, 1)),
        init1_fn=lambda x0: t.step_fn(0, t.init_state, x0),
        step_fn=t.step_fn,
        deriv_fn=lambda i, q: t.deriv(i, q),
        L=max(1, t.sig_bits),
    )


def analyze_bsda(da: DerivAutomaton) -> Dict[str, Any]:
    L = da.L
    b0_ok = (da.bit0[0] != da.bit0[1])

    layer: Dict[Any, int] = {}
    for x0 in (0, 1):
        q = da.init1_fn(x0)
        if q not in layer:
            layer[q] = x0

    always_one = True
    always_zero = True
    first_fail_one: Optional[Tuple[int, int]] = None

    for i in range(1, L):
        for q, xpref in layer.items():
            d = da.deriv_fn(i, q)
            if d == 0:
                always_one = False
                if first_fail_one is None:
                    first_fail_one = (i, xpref)
            else:
                always_zero = False
        next_layer: Dict[Any, int] = {}
        for q, xpref in layer.items():
            for b in (0, 1):
                qn = da.step_fn(i, q, b)
                if qn not in next_layer:
                    next_layer[qn] = xpref | (b << i)
        layer = next_layer

    visited: Dict[Any, Tuple[int, int]] = {}
    frontier: List[Tuple[Any, int, int]] = []
    for q, xpref in layer.items():
        if q not in visited:
            visited[q] = (L, xpref)
            frontier.append((q, L, xpref))

    stab_d = 0
    cur_d = 0
    while frontier:
        next_frontier = []
        for q, depth_i, xpref in frontier:
            d = da.deriv_fn(L, q)
            if d == 0:
                always_one = False
                if first_fail_one is None or depth_i < first_fail_one[0]:
                    first_fail_one = (depth_i, xpref)
            else:
                always_zero = False
            for b in (0, 1):
                qn = da.step_fn(L, q, b)
                if qn not in visited:
                    visited[qn] = (depth_i + 1, xpref | (b << depth_i))
                    next_frontier.append((qn, depth_i + 1, xpref | (b << depth_i)))
        if next_frontier:
            cur_d += 1
            stab_d = cur_d
        frontier = next_frontier

    horizon_w = L + stab_d + 1
    first_fail: Optional[Tuple[int, Tuple[int, int]]] = None
    if not b0_ok:
        first_fail = (1, (0, 1))
    elif first_fail_one is not None:
        i_fail, xpref = first_fail_one
        first_fail = (i_fail + 1, (xpref, xpref | (1 << i_fail)))

    return {
        "b0_ok": b0_ok,
        "always_one_ge1": always_one,
        "always_zero_ge1": always_zero,
        "bijective_all_w": b0_ok and always_one,
        "L": L,
        "stab_d": stab_d,
        "horizon_w": horizon_w,
        "first_fail": first_fail,
        "reachable_count": len(visited),
    }


def compile_bsda(e: Expr) -> Optional[DerivAutomaton]:
    """Mirrors Lean 4 `compileBSDA` exactly (including L = 1 for Const!)."""
    if isinstance(e, Var):
        return DerivAutomaton((0, 1), lambda x0: (), lambda i, q, b: (), lambda i, q: 1, 1)
    if isinstance(e, Const):
        c0 = int_bit(e.c, 0)
        return DerivAutomaton((c0, c0), lambda x0: (), lambda i, q, b: (), lambda i, q: 0, 1)
    if isinstance(e, Not):
        da = compile_bsda(e.e)
        if da is None: return None
        return DerivAutomaton((1 ^ da.bit0[0], 1 ^ da.bit0[1]), da.init1_fn, da.step_fn, da.deriv_fn, da.L)
    if isinstance(e, Shl):
        if e.k == 0:
            return compile_bsda(e.e)
        return DerivAutomaton((0, 0), lambda x0: (), lambda i, q, b: (), lambda i, q: 0, 1)
    if isinstance(e, (Add, Sub, Xor)):
        da, db = compile_bsda(e.a), compile_bsda(e.b)
        if da is None or db is None: return None
        return DerivAutomaton(
            bit0=(da.bit0[0] ^ db.bit0[0], da.bit0[1] ^ db.bit0[1]),
            init1_fn=lambda x0: (da.init1_fn(x0), db.init1_fn(x0)),
            step_fn=lambda i, q, b: (da.step_fn(i, q[0], b), db.step_fn(i, q[1], b)),
            deriv_fn=lambda i, q: da.deriv_fn(i, q[0]) ^ db.deriv_fn(i, q[1]),
            L=max(da.L, db.L),
        )
    if isinstance(e, Mul):
        da, db = compile_bsda(e.a), compile_bsda(e.b)
        if da is None or db is None: return None
        return DerivAutomaton(
            bit0=(da.bit0[0] & db.bit0[0], da.bit0[1] & db.bit0[1]),
            init1_fn=lambda x0: (da.init1_fn(x0), db.init1_fn(x0), x0),
            step_fn=lambda i, q, b: (da.step_fn(i, q[0], b), db.step_fn(i, q[1], b), q[2]),
            deriv_fn=lambda i, q: (da.bit0[q[2]] & db.deriv_fn(i, q[1])) ^ (db.bit0[q[2]] & da.deriv_fn(i, q[0])),
            L=max(da.L, db.L),
        )
    if isinstance(e, (And, Or)):
        is_or = isinstance(e, Or)
        fta, ftb = compile_full(e.a), compile_full(e.b)
        if fta is not None and ftb is not None:
            return full_to_deriv(compile_full(e))
        da, db = compile_bsda(e.a), compile_bsda(e.b)
        if da is None or db is None: return None
        ia, ib = analyze_bsda(da), analyze_bsda(db)
        b0 = ((da.bit0[0] | db.bit0[0], da.bit0[1] | db.bit0[1]) if is_or
              else (da.bit0[0] & db.bit0[0], da.bit0[1] & db.bit0[1]))
        if ia["always_zero_ge1"] and ib["always_zero_ge1"]:
            return DerivAutomaton(b0, lambda x0: (), lambda i, q, b: (), lambda i, q: 0, 1)
        if fta is not None and ia["always_zero_ge1"]:
            return DerivAutomaton(
                b0,
                lambda x0: (fta.step_fn(0, fta.init_state, x0), db.init1_fn(x0)),
                lambda i, q, b: (fta.step_fn(i, q[0], b), db.step_fn(i, q[1], b)),
                lambda i, q: ((1 ^ fta.val0(i, q[0])) if is_or else fta.val0(i, q[0])) & db.deriv_fn(i, q[1]),
                max(1, fta.sig_bits, db.L),
            )
        if ftb is not None and ib["always_zero_ge1"]:
            return DerivAutomaton(
                b0,
                lambda x0: (da.init1_fn(x0), ftb.step_fn(0, ftb.init_state, x0)),
                lambda i, q, b: (da.step_fn(i, q[0], b), ftb.step_fn(i, q[1], b)),
                lambda i, q: ((1 ^ ftb.val0(i, q[1])) if is_or else ftb.val0(i, q[1])) & da.deriv_fn(i, q[0]),
                max(1, da.L, ftb.sig_bits),
            )
        return None
    raise TypeError(e)


# ============================================================
# 3. Exhaustive Independent Replay of Every Lean 4 Theorem
# ============================================================

def main():
    x = Var()
    x2 = Mul(x, x)
    x3 = Mul(x2, x)
    x5 = Mul(x3, x2)

    print("=== 1. BSDA ENGINE INSTANTIATIONS (EXACT MATCH WITH Proof.lean SECTION 7) ===")
    lean_cases = [
        ("exRivest: x + 2x^2 + 2x^3",
         Add(Add(x, Mul(Const(2), x2)), Mul(Const(2), x3)), True, 2),
        ("exKlimovShamir: x + (x^2 | 5)",
         Add(x, Or(x2, Const(5))), True, 2),
        ("exMaskedRivest: (x & -2) + (x^2 & 1) + (x^3 & 8) + (x^5 & 8)",
         Add(Add(Add(And(x, Const(-2)), And(x2, Const(1))), And(x3, Const(8))), And(x5, Const(8))), True, 5),
        ("exCarryGatedQuintic: x + (((x + 1) << 1) & (x^3 + x^5))",
         Add(x, And(Shl(1, Add(x, Const(1))), Add(x3, x5))), True, 2),
        ("exZeroLinear: (x & (x + 1)) + (~x | (x + 1))",
         Add(And(x, Add(x, Const(1))), Or(Not(x), Add(x, Const(1)))), True, None),
        ("exFullSpectrum: ((x ^ (x << 1)) + (x^2 | 5)) - ((x ^ (x + 1)) & (x^3 ^ x^5))",
         Sub(Add(Xor(x, Shl(1, x)), Or(x2, Const(5))), And(Xor(x, Add(x, Const(1))), Xor(x3, x5))), True, None),
        ("negRivest: x + x^2 + x^3",
         Add(Add(x, x2), x3), False, 2),
        ("negCarryGated: x + (((x + 1) << 1) & x^3)",
         Add(x, And(Shl(1, Add(x, Const(1))), x3)), False, None),
        ("negKlimovEven: x + (x^2 | 4)",
         Add(x, Or(x2, Const(4))), False, 2),
        ("negCarryPair17: x + (x & (x + 1)) + (x & (x + 17))",
         Add(Add(x, And(x, Add(x, Const(1)))), And(x, Add(x, Const(17)))), False, None),
    ]

    for name, expr, expected_bij, expected_W in lean_cases:
        da = compile_bsda(expr)
        assert da is not None, f"Unexpected None on {name}"
        info = analyze_bsda(da)
        assert info["bijective_all_w"] == expected_bij, f"Bijectivity mismatch on {name}: {info}"
        if expected_W is not None:
            assert info["horizon_w"] == expected_W, f"Horizon mismatch on {name}: got {info['horizon_w']}, expected {expected_W}"

        # Independent exhaustive replay for w = 1 .. 10
        bf = []
        for w in range(1, 11):
            ok, col = is_bijective_bruteforce(expr, w)
            bf.append(ok)
            if expected_bij:
                assert ok, f"Brute force failed at w={w} for {name}: col={col}"
        if not expected_bij:
            w_fail, (xa, xb) = info["first_fail"]
            assert xa != xb and eval_mod(expr, xa, w_fail) == eval_mod(expr, xb, w_fail)
            assert all(bf[:w_fail - 1]) and not bf[w_fail - 1], f"Exact fail width mismatch on {name}: bf={bf}"
        print(f"  [PASS] {name}")
        print(f"         bijective={info['bijective_all_w']} | W*={info['horizon_w']} (L={info['L']}, D={info['stab_d']}, |R|={info['reachable_count']}) | first_fail={info['first_fail']}")

    print("\n=== 2. SHARP CUBIC MASKED FAMILY Q_k(x) = x + (x^3 & 2^k) (k = 1..8) ===")
    for k in range(1, 9):
        qk = Add(x, And(x3, Const(1 << k)))
        for w in range(1, k + 2):
            ok, col = is_bijective_bruteforce(qk, w)
            if w <= k:
                assert ok, f"Q_{k} should be bijective at w={w}"
            else:
                assert not ok, f"Q_{k} should FAIL at w={k + 1}"
                assert eval_mod(qk, 1, k + 1) == eval_mod(qk, 1 + (1 << k), k + 1)
        print(f"  [PASS] Q_{k}: bijective for all 1 <= w <= {k}; collision at w={k+1}: (1, {1 + (1 << k)})")

    print("\n=== 3. SHARP CARRY-COUPLED FAMILY F_{{1, 1+2^k}}(x) (k = 1..8) ===")
    for k in range(1, 9):
        fk = Add(Add(x, And(x, Add(x, Const(1)))), And(x, Add(x, Const(1 + (1 << k)))))
        for w in range(1, k + 2):
            ok, col = is_bijective_bruteforce(fk, w)
            if w <= k:
                assert ok, f"F_{{1,1+2^{k}}} should be bijective at w={w}"
            else:
                assert not ok, f"F_{{1,1+2^{k}}} should FAIL at w={k + 1}"
                assert eval_mod(fk, 0, k + 1) == eval_mod(fk, 1 << k, k + 1)
        print(f"  [PASS] F_{{1, 1+2^{k}}}: bijective for all 1 <= w <= {k}; collision at w={k+1}: (0, {1 << k})")

    print("\n=== 4. OUTSIDE-BSDA BOUNDARY WITNESS B(x) = x + (x^2 & (x ^ 1)) ===")
    B = Add(x, And(x2, Xor(x, Const(1))))
    assert compile_bsda(B) is None
    b_res = [is_bijective_bruteforce(B, w)[0] for w in range(1, 9)]
    assert b_res == [True, True, False, False, False, False, False, False]
    assert eval_mod(B, 2, 3) == eval_mod(B, 6, 3) == 2
    print(f"  [PASS] compile_bsda(B) = None | w=1..8 bijectivity: {b_res} | mod-8 collision: B(2)=B(6)=2")

    print("\n=== 5. COMPLEMENT-BRIDGE & GENERALIZED KLIMOV-SHAMIR CHECKS (w = 1..8) ===")
    # Non-transducer g(x) = x^2 & (x + 1)
    g_wild = And(x2, Add(x, Const(1)))
    H_wild = Add(And(x, g_wild), Or(Not(x), g_wild))
    for w in range(1, 9):
        ok, _ = is_bijective_bruteforce(H_wild, w)
        assert ok, f"Complement-bridge failed on wild g at w={w}"
    # Generalized Klimov-Shamir with g(x) = x^2 + x (g(0)_0 = 0 = g(1)_0!) and EVEN c = 4!
    g_even0 = Add(x2, x)
    ks_even_ok = Add(x, Or(Mul(g_even0, g_even0), Const(4)))
    for w in range(1, 9):
        ok, _ = is_bijective_bruteforce(ks_even_ok, w)
        assert ok, f"Generalized Klimov-Shamir failed at w={w}"
    print("  [PASS] H_{x^2 & (x+1)} bijective for all w=1..8 (outside BSDA!)")
    print("  [PASS] x + ((x^2 + x)^2 | 4) bijective for all w=1..8 (even c works since g(0)_0 = g(1)_0!)")

    print("\nALL INDEPENDENT EXACT-INTEGER REPLAY CHECKS PASSED (0 FLOATS USED).")


if __name__ == "__main__":
    main()
