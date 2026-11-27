"""Exact Pure-Silicon Verification & Exploration Replay for the MBA-Hensel Engine.

ZERO floating-point arithmetic anywhere (exact Python `int` only).
Independently implements:
  1. The 10-operator `MBAExpr` AST and width-coherent modular evaluator `eval_mod`.
  2. The Symbolic Order-0 MBA Differential Compiler `sym_deriv0` and finite certificate checker.
  3. The Symbolic Affine Block-Jet Compiler `eval_block_jet` (including XOR annihilation and
     variable-variable `&`/`|` Idempotence Linearization) + exact Newton-Hensel inverse `mod_inv_pow2`.
  4. Independent exhaustive root-tree verification, constructive bit-by-bit lifts up to w = 256,
     constructive quadratic doubling lifts up to w = 4096 bits, and all sharpness counterexamples
     for Theorems 1, 2, 3, and 4 of the Lean sources.
"""

from dataclasses import dataclass
from typing import Optional, Tuple, List


# =============================================================================
# 1. MBAExpr AST & Width-Coherent Modular Semantics
# =============================================================================

@dataclass(frozen=True)
class MBAExpr:
    tag: str
    arg1: object = None
    arg2: object = None


def Var() -> MBAExpr:
    return MBAExpr("var")

def Const(c: int) -> MBAExpr:
    return MBAExpr("const", c)

def Add(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("add", a, b)

def Sub(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("sub", a, b)

def Mul(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("mul", a, b)

def BXor(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("bxor", a, b)

def BAnd(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("band", a, b)

def BOr(a: MBAExpr, b: MBAExpr) -> MBAExpr:
    return MBAExpr("bor", a, b)

def BNot(a: MBAExpr) -> MBAExpr:
    return MBAExpr("bnot", a)

def Shl(a: MBAExpr, k: int) -> MBAExpr:
    return MBAExpr("shl", a, k)


def eval_mod(w: int, e: MBAExpr, x: int) -> int:
    mask = (1 << w) - 1
    mod = 1 << w
    t = e.tag
    if t == "var":
        return x & mask
    if t == "const":
        return e.arg1 & mask
    if t == "add":
        return (eval_mod(w, e.arg1, x) + eval_mod(w, e.arg2, x)) & mask
    if t == "sub":
        return (eval_mod(w, e.arg1, x) + (mod - eval_mod(w, e.arg2, x))) & mask
    if t == "mul":
        return (eval_mod(w, e.arg1, x) * eval_mod(w, e.arg2, x)) & mask
    if t == "bxor":
        return (eval_mod(w, e.arg1, x) ^ eval_mod(w, e.arg2, x)) & mask
    if t == "band":
        return (eval_mod(w, e.arg1, x) & eval_mod(w, e.arg2, x)) & mask
    if t == "bor":
        return (eval_mod(w, e.arg1, x) | eval_mod(w, e.arg2, x)) & mask
    if t == "bnot":
        return mask - eval_mod(w, e.arg1, x)
    if t == "shl":
        return (eval_mod(w, e.arg1, x) << e.arg2) & mask
    raise ValueError(f"Unknown tag {t}")


def root_counts_tree(e: MBAExpr, max_w: int) -> Tuple[List[int], List[int]]:
    """Exact root counts for w = 1..max_w via 1-Lipschitz bit-tree expansion."""
    roots = [0]
    counts: List[int] = []
    for w in range(1, max_w + 1):
        half = 1 << (w - 1)
        nxt = []
        for r in roots:
            if eval_mod(w, e, r) == 0:
                nxt.append(r)
            if eval_mod(w, e, r + half) == 0:
                nxt.append(r + half)
        roots = nxt
        counts.append(len(roots))
    return counts, roots


# =============================================================================
# 2. Symbolic Order-0 MBA Differential Compiler (`sym_deriv0`)
# =============================================================================

def is_bounded_const(w0: int, e: MBAExpr) -> bool:
    return e.tag == "const" and e.arg1 < (1 << w0)


def is_carry_free_self_pair(w0: int, s: int, r: int, a: MBAExpr, b: MBAExpr) -> bool:
    if a.tag == "var" and b.tag == "add" and b.arg1.tag == "var" and b.arg2.tag == "const":
        return s <= w0 and (r + b.arg2.arg1 < (1 << s))
    if b.tag == "var" and a.tag == "add" and a.arg1.tag == "var" and a.arg2.tag == "const":
        return s <= w0 and (r + a.arg2.arg1 < (1 << s))
    return False


def sym_deriv0(w0: int, s: int, r: int, e: MBAExpr) -> Optional[bool]:
    t = e.tag
    if t == "var":
        return True
    if t == "const":
        return False
    if t in ("add", "sub", "bxor"):
        da = sym_deriv0(w0, s, r, e.arg1)
        db = sym_deriv0(w0, s, r, e.arg2)
        return None if (da is None or db is None) else (da ^ db)
    if t == "mul":
        if w0 >= 1 and s >= 1:
            da = sym_deriv0(w0, s, r, e.arg1)
            db = sym_deriv0(w0, s, r, e.arg2)
            if da is None or db is None:
                return None
            a0 = eval_mod(1, e.arg1, r) == 1
            b0 = eval_mod(1, e.arg2, r) == 1
            return (da and b0) ^ (a0 and db)
        return None
    if t == "bnot":
        return sym_deriv0(w0, s, r, e.arg1)
    if t == "shl":
        return sym_deriv0(w0, s, r, e.arg1) if e.arg2 == 0 else False
    if t == "band":
        if is_bounded_const(w0, e.arg1) or is_bounded_const(w0, e.arg2):
            return False
        if is_carry_free_self_pair(w0, s, r, e.arg1, e.arg2):
            return True
        da = sym_deriv0(w0, s, r, e.arg1)
        db = sym_deriv0(w0, s, r, e.arg2)
        return False if (da is False and db is False) else None
    if t == "bor":
        if is_bounded_const(w0, e.arg1):
            return sym_deriv0(w0, s, r, e.arg2)
        if is_bounded_const(w0, e.arg2):
            return sym_deriv0(w0, s, r, e.arg1)
        da = sym_deriv0(w0, s, r, e.arg1)
        db = sym_deriv0(w0, s, r, e.arg2)
        return False if (da is False and db is False) else None
    return None


def lift_core(e: MBAExpr, v: int, w0: int, y0: int, steps: int) -> int:
    """Exact bit-by-bit silicon Hensel lifter matching `liftCore` in the Lean sources."""
    y = y0
    for k in range(steps):
        w = w0 + k
        if eval_mod(w + 1, e, y) != 0:
            y = y + (1 << (w - v))
    return y


# =============================================================================
# 3. Symbolic Affine Block-Jet Compiler & Exact Quadratic Lifter (`w -> 2*w`)
# =============================================================================

@dataclass(frozen=True)
class BlockJet:
    r: int
    q: int
    a: int


def mod_inv_pow2(a: int, w: int) -> int:
    """Exact O(log w) Newton-Hensel modular inverse of odd a modulo 2^w (pure int)."""
    assert a % 2 == 1
    if w == 0:
        return 0
    inv = 1
    cur = 1
    while cur < w:
        cur = min(2 * cur, w)
        mod = 1 << cur
        inv = (inv * (2 + mod - (a * inv) % mod)) % mod
    assert (a * inv) % (1 << w) == 1
    return inv


def eval_block_jet(w: int, e: MBAExpr, x: int) -> Optional[BlockJet]:
    M = 1 << w
    mask = M - 1
    t = e.tag
    if t == "var":
        return BlockJet(x & mask, 0, 1 & mask)
    if t == "const":
        return BlockJet(e.arg1 & mask, (e.arg1 >> w) & mask, 0)
    if t == "add":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        s = J1.r + J2.r
        return BlockJet(s & mask, (J1.q + J2.q + (s >> w)) & mask, (J1.a + J2.a) & mask)
    if t == "sub":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        r = (J1.r + (M - J2.r)) & mask
        borrow = mask if J1.r < J2.r else 0
        return BlockJet(r, (J1.q + (M - J2.q) + borrow) & mask, (J1.a + (M - J2.a)) & mask)
    if t == "mul":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        p = J1.r * J2.r
        return BlockJet(
            p & mask,
            ((p >> w) + J1.r * J2.q + J2.r * J1.q) & mask,
            (J1.r * J2.a + J2.r * J1.a) & mask,
        )
    if t == "shl":
        J1 = eval_block_jet(w, e.arg1, x)
        if J1 is None:
            return None
        p = J1.r << e.arg2
        return BlockJet(p & mask, ((p >> w) + (J1.q << e.arg2)) & mask, (J1.a << e.arg2) & mask)
    if t == "bnot":
        J1 = eval_block_jet(w, e.arg1, x)
        if J1 is None:
            return None
        return BlockJet(mask - J1.r, mask - J1.q, (M - J1.a) & mask)
    if t == "bxor":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        r = (J1.r ^ J2.r) & mask
        if J2.q == 0 and J2.a == 0:
            return BlockJet(r, J1.q, J1.a)
        if J1.q == 0 and J1.a == 0:
            return BlockJet(r, J2.q, J2.a)
        if J2.q == mask and J2.a == 0:
            return BlockJet(r, mask - J1.q, (M - J1.a) & mask)
        if J1.q == mask and J1.a == 0:
            return BlockJet(r, mask - J2.q, (M - J2.a) & mask)
        if J1.q == J2.q and J1.a == J2.a:
            return BlockJet(r, 0, 0)
        return None
    if t == "band":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        r = (J1.r & J2.r) & mask
        if (J2.q == 0 and J2.a == 0) or (J1.q == 0 and J1.a == 0):
            return BlockJet(r, 0, 0)
        if J2.q == mask and J2.a == 0:
            return BlockJet(r, J1.q, J1.a)
        if J1.q == mask and J1.a == 0:
            return BlockJet(r, J2.q, J2.a)
        if J1.q == J2.q and J1.a == J2.a:
            return BlockJet(r, J1.q, J1.a)  # Idempotence Linearization!
        return None
    if t == "bor":
        J1 = eval_block_jet(w, e.arg1, x)
        J2 = eval_block_jet(w, e.arg2, x)
        if J1 is None or J2 is None:
            return None
        r = (J1.r | J2.r) & mask
        if J2.q == 0 and J2.a == 0:
            return BlockJet(r, J1.q, J1.a)
        if J1.q == 0 and J1.a == 0:
            return BlockJet(r, J2.q, J2.a)
        if (J2.q == mask and J2.a == 0) or (J1.q == mask and J1.a == 0):
            return BlockJet(r, mask, 0)
        if J1.q == J2.q and J1.a == J2.a:
            return BlockJet(r, J1.q, J1.a)
        return None
    return None


def mba_quad_lift(e: MBAExpr, w0: int, x0: int, k: int) -> Tuple[int, int]:
    """Iterated quadratic doubling w0 -> w0 * 2^k via `eval_block_jet`."""
    w = w0
    x = x0 & ((1 << w0) - 1)
    assert eval_mod(w, e, x) == 0
    for _ in range(k):
        J = eval_block_jet(w, e, x)
        assert J is not None and J.r == 0 and J.a % 2 == 1
        M = 1 << w
        inv = mod_inv_pow2(J.a, w)
        delta = ((M - J.q) * inv) & (M - 1)
        x = (x & (M - 1)) + (delta << w)
        w *= 2
        assert eval_mod(w, e, x) == 0
    return w, x


# =============================================================================
# 4. Theorem Families & Independent Verification Suite
# =============================================================================

def fam1(a: int, b: int, c: int, d: int) -> MBAExpr:
    return Sub(
        Add(
            Mul(Var(), BXor(Var(), Const(2 * a + 1))),
            Shl(BAnd(Mul(Var(), Var()), Add(Mul(Const(b), Var()), Const(c))), 1),
        ),
        Const(d),
    )


def fam2(H: MBAExpr) -> MBAExpr:
    return Add(Mul(Var(), Sub(Mul(Var(), Var()), Const(1))), Shl(H, 2))


def fam3(a: int, b: int, c: int) -> MBAExpr:
    return Sub(
        Add(
            Add(Mul(Const(a), Mul(Var(), Var())), BAnd(Var(), Add(Var(), Const(1)))),
            Shl(BXor(Var(), Const(c)), 1),
        ),
        Const(2 * b),
    )


SEP_EXPR = Sub(Add(Mul(Var(), Var()), BXor(Var(), Add(Shl(Var(), 1), Const(1)))), Const(1))


def main() -> None:
    print("=== Pure-Silicon MBA-Hensel Engine: Independent Exact Verification ===")

    # --- Theorem 1 ---
    print("\n[Theorem 1] 4-Parameter Odd-Mask XOR-Product & Bitwise-AND Dichotomy:")
    for a, b, c, d in [(0, 1, 1, 0), (2, 3, 5, 6), (2, 3, 5, 7), (7, 11, 13, 20), (5, 9, 4, 15)]:
        e = fam1(a, b, c, d)
        assert sym_deriv0(1, 1, 0, e) is True and sym_deriv0(1, 1, 1, e) is True
        counts, _ = root_counts_tree(e, 14)
        exp = 2 if d % 2 == 0 else 0
        assert all(cnt == exp for cnt in counts), f"Mismatch for {(a,b,c,d)}: {counts}"
        if d % 2 == 0:
            y0 = lift_core(e, 0, 1, 0, 127)
            y1 = lift_core(e, 0, 1, 1, 127)
            assert eval_mod(128, e, y0) == 0 and eval_mod(128, e, y1) == 0 and y0 != y1
            assert y0 % 2 == 0 and y1 % 2 == 1
        print(f"  (a,b,c,d)=({a},{b},{c},{d}): rootCount[1..14]={exp} constant; 128-bit lifts verified OK")

    # Sharpness 1a & 1b
    s1a = Sub(Mul(Var(), BXor(Var(), Const(0))), Const(4))
    c_s1a, _ = root_counts_tree(s1a, 8)
    assert c_s1a[4] == 8  # w = 5 -> 8 roots
    s1b = Sub(Add(Mul(Var(), BXor(Var(), Const(1))), BAnd(Var(), Add(Var(), Const(1)))), Const(2))
    c_s1b, _ = root_counts_tree(s1b, 8)
    assert c_s1b[0] == 2 and c_s1b[1] == 1
    print(f"  Sharpness 1a (even mask 0, d=4): counts[1..8] = {c_s1a} (hits 8 at w=5)")
    print(f"  Sharpness 1b (unshielded &):     counts[1..8] = {c_s1b} (drops 2 -> 1 at w=2)")

    # --- Theorem 2 ---
    print("\n[Theorem 2] Universal 1-or-5 Non-Uniform Ramification Dichotomy (x*(x^2-1) + 4*H(x)):")
    H_five = Add(BXor(Var(), Const(5)), BAnd(Var(), Add(Var(), Const(1))))
    H_one = BXor(Var(), Add(Mul(Const(3), Var()), Const(1)))
    H_wild = BOr(BAnd(Mul(Var(), BXor(Var(), Const(7))), Add(Var(), Const(3))), Shl(Var(), 1))
    for label, H in [("H_five = (x^5)+(x&(x+1))", H_five),
                     ("H_one  = x^(3x+1)", H_one),
                     ("H_wild = ((x*(x^7))&(x+3))|(2x)", H_wild)]:
        e = fam2(H)
        counts, _ = root_counts_tree(e, 14)
        h1 = eval_mod(1, H, 1)
        exp = 5 if h1 == 0 else 1
        assert all(counts[w - 1] == exp for w in range(3, 15))
        # Also verify constructive bit-by-bit lifts: v=0 even root + v=1 odd core roots (if H(1)=0)
        even_base = 0 if eval_mod(1, H, 0) == 0 else 4
        y_even = lift_core(e, 0, 3, even_base, 125)
        assert eval_mod(128, e, y_even) == 0 and y_even % 2 == 0
        if h1 == 0:
            for core in (1, 3):
                yc = lift_core(e, 1, 3, core, 125)
                assert eval_mod(128, e, yc) == 0
                assert eval_mod(128, e, yc + (1 << 127)) == 0  # v=1 fiber of size 2
        print(f"  {label:34s} | H(1)%2={h1} | counts[1..10]={counts[:10]} | 128-bit fibers OK")

    # Sharpness 2 (replace 4 by 2)
    s2 = Add(Mul(Var(), Sub(Mul(Var(), Var()), Const(1))), Shl(BAnd(Var(), Add(Var(), Const(1))), 1))
    c_s2, _ = root_counts_tree(s2, 10)
    assert c_s2[3] == 7 and c_s2[4] == 11
    print(f"  Sharpness 2 (coeff 2 instead of 4): counts[1..10] = {c_s2} (hits 7 at w=4, 11 at w=5)")

    # --- Theorem 3 ---
    print("\n[Theorem 3] Infinite Quadratic Doubling Tower via Bitwise-AND Idempotence Linearization:")
    for a, b, c, w0 in [(3, 11, 7, 4), (1, 2, 13, 4), (5, 7, 15, 4), (9, 3, 11, 4)]:
        e = fam3(a, b, c)
        counts, _ = root_counts_tree(e, 12)
        assert all(cnt == 1 for cnt in counts)
        _, roots_w0 = root_counts_tree(e, w0)
        x0 = roots_w0[0]
        # Quadratic doubling: 4 -> 8 -> 16 -> ... -> 4096 bits (10 steps!)
        w_hi, x_hi = mba_quad_lift(e, w0, x0, 10)
        assert w_hi == 4096 and eval_mod(4096, e, x_hi) == 0 and x_hi % 2 == 0
        # Cross-check k=2 against Lean witness for (3,11,7)
        if (a, b, c) == (3, 11, 7):
            w2, x2 = mba_quad_lift(e, 4, 8, 2)
            assert (w2, x2) == (16, 49944)
        print(f"  (a,b,c)=({a},{b},{c}), x0={x0:2d} (mod 16) -> 4096-bit exact root in 10 quad steps! "
              f"x mod 2^16 = {x_hi & 0xFFFF}")

    # Sharpness 3: below mask threshold c < 2^w0
    assert eval_block_jet(2, fam3(3, 11, 7), 0) is None
    print("  Sharpness 3 (w=2 < bitlen(7)): eval_block_jet(2, fam3(3,11,7), 0) = None OK")

    # --- Theorem 4 ---
    print("\n[Theorem 4] Infinite Separation Theorem (Bit-by-Bit Liftable != Affine Block-Jet Liftable):")
    assert sym_deriv0(1, 1, 0, SEP_EXPR) is True and sym_deriv0(1, 1, 1, SEP_EXPR) is True
    c_sep, _ = root_counts_tree(SEP_EXPR, 14)
    assert all(cnt == 2 for cnt in c_sep)
    y0_sep = lift_core(SEP_EXPR, 0, 1, 0, 255)
    y1_sep = lift_core(SEP_EXPR, 0, 1, 1, 255)
    assert eval_mod(256, SEP_EXPR, y0_sep) == 0 and eval_mod(256, SEP_EXPR, y1_sep) == 0 and y0_sep != y1_sep
    # Verify non-affinity obstruction across ALL bases x < 2^w for w = 3..7
    for w in range(3, 8):
        M = 1 << w
        for x in range(M):
            assert eval_block_jet(w, SEP_EXPR, x) is None
            # Exhaustive check that second finite difference mod 8 is non-zero
            H = [(eval_mod(2 * w, SEP_EXPR, x + (d << w)) + 1) % (1 << (2 * w)) >> w for d in range(4)]
            d2_0 = (H[0] + H[2] - 2 * H[1]) % 8
            d2_1 = (H[1] + H[3] - 2 * H[2]) % 8
            assert d2_0 != 0 or d2_1 != 0
    print(f"  sepExpr rootCount[1..14] = {c_sep} (256-bit bit-by-bit lifts OK)")
    print("  Non-affine block-jet obstruction verified for ALL bases x < 2^w across w = 3..7 (248/248 bases) OK")
    print("\nALL INDEPENDENT EXACT CHECKS PASSED (ZERO FLOATS).")


if __name__ == "__main__":
    main()
