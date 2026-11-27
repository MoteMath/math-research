#!/usr/bin/env python3
"""
Exact pure-silicon exploration, certificate verification, and sharpness/falsification
suite for the Recursive Bit-Sliced Schur-Complement Determinant Engine.

Zero floating-point arithmetic is used anywhere: all matrix determinants are
computed via exact rational (fractions.Fraction) elimination or exact Leibniz
permutation sums over Z and Z/mZ (including rings with zero divisors).
"""

from fractions import Fraction
from itertools import permutations


def det_exact_int(M):
    """Exact determinant of an integer matrix via Fraction elimination (no floats)."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for i in range(n):
        piv = None
        for r in range(i, n):
            if A[r][i] != 0:
                piv = r
                break
        if piv is None:
            return 0
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            det = -det
        pv = A[i][i]
        det *= pv
        for r in range(i + 1, n):
            if A[r][i] != 0:
                fac = A[r][i] / pv
                for c in range(i + 1, n):
                    A[r][c] -= fac * A[i][c]
    assert det.denominator == 1
    return det.numerator


def det_leibniz_mod(M, mod):
    """Exact Leibniz determinant in Z/mod Z (works even when mod is composite)."""
    n = len(M)
    total = 0
    for perm in permutations(range(n)):
        inv = 0
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    inv += 1
        prod = 1
        for i in range(n):
            prod = (prod * M[i][perm[i]]) % mod
        if inv & 1:
            total = (total - prod) % mod
        else:
            total = (total + prod) % mod
    return total % mod


# ============================================================================
# Family I: Non-Uniform Highest-Common-Bit (HCB) Weighted Kernel
# ============================================================================

def msb_pos(z):
    """1-indexed position of highest 1-bit of z, or 0 if z == 0."""
    return z.bit_length()


def mk_hcb_matrix(k, f, g, a, b, d):
    """Build 2^k x 2^k HCB weighted matrix directly from bitwise entry definition."""
    n = 1 << k
    M = []
    for x in range(n):
        row = []
        for y in range(n):
            j = msb_pos(x & y)
            val = f(j)
            for bit in range(k):
                m = bit + 1
                if m == j:
                    continue
                xb = (x >> bit) & 1
                yb = (y >> bit) & 1
                if xb == 0 and yb == 0:
                    val *= g(m)
                elif xb == 0 and yb == 1:
                    val *= a(m)
                elif xb == 1 and yb == 0:
                    val *= b(m)
                else:
                    val *= d(m)
            row.append(val)
        M.append(row)
    return M


def hcb_mask_factor(k, mask, f, g, a, b, d):
    """Exact bitmask factor L_s(f) from the closed-form theorem."""
    def neg_p_prod(lo, hi):
        res = 1
        for bit in range(lo, hi):
            if (mask >> bit) & 1:
                m = bit + 1
                res *= -(a(m) * b(m))
        return res

    def delta_prod(lo, hi):
        res = 1
        for bit in range(lo, hi):
            if (mask >> bit) & 1:
                m = bit + 1
                res *= g(m) * d(m) - a(m) * b(m)
        return res

    total = neg_p_prod(0, k) * f(0)
    for bit in range(k):
        if (mask >> bit) & 1:
            m = bit + 1
            total += delta_prod(0, bit) * g(m) * neg_p_prod(bit + 1, k) * f(m)
    return total


def det_hcb_closed(k, f, g, a, b, d):
    prod = 1
    for mask in range(1 << k):
        prod *= hcb_mask_factor(k, mask, f, g, a, b, d)
    return prod


def det_msb_and_pure_closed(k, f):
    """Corollary I-A: uniform gamma=alpha=beta=delta=1, M(x,y) = f(msbPos(x & y))."""
    if k == 0:
        return f(0)
    prod = f(0)
    for j in range(1, k + 1):
        prod *= (f(j) - f(0)) ** (1 << (k - j))
    if k >= 2:
        prod = -prod
    return prod


# ============================================================================
# Family II: Weighted Boolean-Poset Subset-Disjointness Hybrid Kernel
# ============================================================================

def mk_bool_hybrid_matrix(k, a0, c0, u, w, d):
    """Build 2^k x 2^k weighted subset + disjointness hybrid matrix."""
    n = 1 << k
    M = []
    for x in range(n):
        row = []
        for y in range(n):
            val = 0
            if (x & y) == x:
                term = a0
                for bit in range(k):
                    m = bit + 1
                    xb, yb = (x >> bit) & 1, (y >> bit) & 1
                    if xb == 0 and yb == 1:
                        term *= u(m)
                    elif xb == 1 and yb == 1:
                        term *= d(m)
                val += term
            if (x & y) == 0:
                term = c0
                for bit in range(k):
                    m = bit + 1
                    xb, yb = (x >> bit) & 1, (y >> bit) & 1
                    if xb == 0 and yb == 1:
                        term *= u(m)
                    elif xb == 1 and yb == 0:
                        term *= w(m)
                val += term
            row.append(val)
        M.append(row)
    return M


def bool_hybrid_mask_factor(k, mask, a0, c0, u, w, d):
    aa, cc = a0, c0
    for bit in range(k):
        if (mask >> bit) & 1:
            m = bit + 1
            aa *= d(m)
            cc *= -(u(m) * w(m))
    return aa + cc


def det_bool_hybrid_closed(k, a0, c0, u, w, d):
    prod = 1
    for mask in range(1 << k):
        prod *= bool_hybrid_mask_factor(k, mask, a0, c0, u, w, d)
    return prod


# ============================================================================
# Verification & Sharpness / Falsification Suite
# ============================================================================

def main():
    print("=== 1. FAMILY I (HCB Weighted Kernel) EXACT VERIFICATION ===")
    hcb_cases = [
        ("general non-uniform (incl. g(3)=0)",
         lambda j: 3 * j * j - 2 * j + 5,
         lambda m: 0 if m == 3 else m + 1,
         lambda m: 2 * m - 3,
         lambda m: m + 2,
         lambda m: 3 * m - 1),
        ("popcount-scaled alternating (g=a=b=1, d=2)",
         lambda j: j * j + 1,
         lambda m: 1, lambda m: 1, lambda m: 1, lambda m: 2),
        ("pure MSB-AND profile f(msb(x&y)) (g=a=b=d=1)",
         lambda j: 1 << j,
         lambda m: 1, lambda m: 1, lambda m: 1, lambda m: 1),
        ("degenerate Delta_m=0 non-uniform",
         lambda j: 5 - 3 * j + j * j,
         lambda m: 2, lambda m: 3, lambda m: 2 * m, lambda m: 3 * m),
        ("asymmetric negative weights",
         lambda j: (-2) ** j + 3,
         lambda m: -m, lambda m: m + 1, lambda m: 1 - 2 * m, lambda m: m - 2),
    ]
    for label, f, g, a, b, d in hcb_cases:
        max_k = 5
        for k in range(0, max_k + 1):
            M = mk_hcb_matrix(k, f, g, a, b, d)
            d_ex = det_exact_int(M)
            d_cl = det_hcb_closed(k, f, g, a, b, d)
            assert d_ex == d_cl, f"Mismatch on {label} k={k}: {d_ex} != {d_cl}"
            if label.startswith("pure MSB-AND"):
                assert d_ex == det_msb_and_pure_closed(k, f)
        print(f"  [PASS] {label}: exact match for k = 0..{max_k} (up to {1<<max_k}x{1<<max_k})")

    # Also test k=6 (64x64) on pure MSB-AND and popcount-scaled alternating
    for label, f, g, a, b, d in hcb_cases[1:3]:
        M6 = mk_hcb_matrix(6, f, g, a, b, d)
        d_ex = det_exact_int(M6)
        d_cl = det_hcb_closed(6, f, g, a, b, d)
        assert d_ex == d_cl
        print(f"  [PASS] {label} at k=6 (64x64): exact match ({len(str(abs(d_ex)))} digits)")

    print("\n=== 2. FAMILY I DELAYED-SINGULARITY INVERTIBILITY DICHOTOMY WITNESS ===")
    # f(0)=1, f(1)=3, f(2)=5, f(3)=3, f(j)=2*j+1 for j>=4; g=a=b=1, d=2
    # UNIQUE zero mask at k=3 is s = 7 = 0b111 = {1,2,3}:
    #   L_7(f) = -f(0) + f(1) - f(2) + f(3) = -1 + 3 - 5 + 3 = 0
    f_sing = lambda j: [1, 3, 5, 3, 9, 11][j] if j < 6 else 2 * j + 1
    ones = lambda m: 1
    twos = lambda m: 2
    for k in range(0, 5):
        d_ex = det_exact_int(mk_hcb_matrix(k, f_sing, ones, ones, ones, twos))
        d_cl = det_hcb_closed(k, f_sing, ones, ones, ones, twos)
        assert d_ex == d_cl
        zero_masks = [s for s in range(1 << k) if hcb_mask_factor(k, s, f_sing, ones, ones, ones, twos) == 0]
        print(f"  k={k}: det={d_ex}, zero_masks={zero_masks}")
        if k < 3:
            assert d_ex != 0 and len(zero_masks) == 0
        elif k == 3:
            assert d_ex == 0 and zero_masks == [7]
        else:
            assert d_ex == 0 and 7 in zero_masks

    print("\n=== 3. FAMILY II (Weighted Boolean-Poset Subset-Disjointness Hybrid) ===")
    bh_cases = [
        ("non-uniform weighted hybrid", 3, 5, lambda m: m + 1, lambda m: 2 * m - 1, lambda m: m + 2),
        ("uniform unweighted (a=2, c=3)", 2, 3, lambda m: 1, lambda m: 1, lambda m: 1),
        ("singular dichotomy boundary (a=5, c=-5)", 5, -5, lambda m: 1, lambda m: 1, lambda m: 1),
        ("delayed singularity at k=2 (a=4, c=1, d=1, u=2, w=2)", 4, 1, lambda m: 2, lambda m: 2, lambda m: 1),
    ]
    for label, a0, c0, u, w, d in bh_cases:
        for k in range(0, 6):
            d_ex = det_exact_int(mk_bool_hybrid_matrix(k, a0, c0, u, w, d))
            d_cl = det_bool_hybrid_closed(k, a0, c0, u, w, d)
            assert d_ex == d_cl, f"Mismatch on {label} k={k}"
            if label.startswith("uniform unweighted") and k >= 1:
                assert d_ex == (a0 * a0 - c0 * c0) ** (1 << (k - 1))
        print(f"  [PASS] {label}: exact match for k = 0..5 (up to 32x32)")

    M6_bh = mk_bool_hybrid_matrix(6, 2, 3, lambda m: 1, lambda m: 1, lambda m: 1)
    d6_bh = det_exact_int(M6_bh)
    assert d6_bh == (-5) ** 32
    print(f"  [PASS] uniform unweighted (a=2, c=3) at k=6 (64x64): det = (-5)^32 = {d6_bh}")

    print("\n=== 4. ZERO-DIVISOR RING CHECK (Z/6Z via exact Leibniz sum, k=0..3) ===")
    # Check both families over Z/6Z where 2*3 = 0 and gamma = 2 or 3 is a zero divisor!
    f_z6 = lambda j: (2 * j + 1) % 6
    g_z6 = lambda m: (2 if m % 2 == 1 else 3)
    a_z6 = lambda m: 3
    b_z6 = lambda m: 5
    d_z6 = lambda m: 4
    for k in range(0, 4):
        M = [[x % 6 for x in row] for row in mk_hcb_matrix(k, f_z6, g_z6, a_z6, b_z6, d_z6)]
        d_leib = det_leibniz_mod(M, 6)
        d_cl = det_hcb_closed(k, f_z6, g_z6, a_z6, b_z6, d_z6) % 6
        assert d_leib == d_cl, f"Z/6Z HCB mismatch at k={k}: {d_leib} != {d_cl}"
    print("  [PASS] Family I over Z/6Z (zero-divisor gamma in {2,3}): exact Leibniz match k=0..3")

    for k in range(0, 4):
        M = [[x % 6 for x in row] for row in mk_bool_hybrid_matrix(k, 2, 3, lambda m: 2, lambda m: 3, lambda m: 4)]
        d_leib = det_leibniz_mod(M, 6)
        d_cl = det_bool_hybrid_closed(k, 2, 3, lambda m: 2, lambda m: 3, lambda m: 4) % 6
        assert d_leib == d_cl, f"Z/6Z BoolHybrid mismatch at k={k}: {d_leib} != {d_cl}"
    print("  [PASS] Family II over Z/6Z (zero divisors): exact Leibniz match k=0..3")

    print("\n=== 5. SHARPNESS & FALSIFIED BOUNDARY VARIANTS ===")
    # Counterexample A: Replace (x & y) with (x | y) in pure MSB profile f(j) = 2^j
    M_or = [[1 << msb_pos(x | y) for y in range(4)] for x in range(4)]
    det_or = det_exact_int(M_or)
    pred_and = det_msb_and_pure_closed(2, lambda j: 1 << j)
    print(f"  [COUNTEREXAMPLE A] msb(x | y) at k=2, f(j)=2^j: det={det_or} (vs msb(x & y) det={pred_and})")
    assert det_or == 0 and pred_and == -3

    # Counterexample B: Replace (x & y) with (x ^ y) in pure MSB profile f(j) = 2^j
    M_xor = [[1 << msb_pos(x ^ y) for y in range(4)] for x in range(4)]
    det_xor = det_exact_int(M_xor)
    print(f"  [COUNTEREXAMPLE B] msb(x ^ y) at k=2, f(j)=2^j: det={det_xor} (vs msb(x & y) det={pred_and})")
    assert det_xor == -55 and det_xor != pred_and

    # Counterexample C: Break below-MSB Kronecker uniformity (replace D-block G_k with J when d=2)
    # At k=2, entry (3, 3) has x&y = 3 (bits 1 and 2 set), so HCB gives f(2)*d(1) = 5*2 = 10;
    # changing entry (3, 3) to f(2)*1 = 5 breaks Schur closure.
    f_c = lambda j: j * j + 1
    M_hcb2 = mk_hcb_matrix(2, f_c, ones, ones, ones, twos)
    det_hcb2 = det_exact_int(M_hcb2)
    M_broken = [row[:] for row in M_hcb2]
    M_broken[3][3] = f_c(2)
    det_broken = det_exact_int(M_broken)
    print(f"  [COUNTEREXAMPLE C] breaking below-MSB weight at (3,3), k=2: det={det_broken} (vs HCB det={det_hcb2})")
    assert det_hcb2 == 16 and det_broken == -4

    # Counterexample D: Add superset term b*[y <=_b x] to Boolean-Poset Hybrid (a=1, b=1, c=1)
    M_sup_k2 = [[(1 if (x & y) == x else 0) + (1 if (x & y) == y else 0) + (1 if (x & y) == 0 else 0)
                 for y in range(4)] for x in range(4)]
    M_sup_k3 = [[(1 if (x & y) == x else 0) + (1 if (x & y) == y else 0) + (1 if (x & y) == 0 else 0)
                 for y in range(8)] for x in range(8)]
    print(f"  [COUNTEREXAMPLE D] adding [y<=_b x] to [x<=_b y]+[x&y==0]: det(k=2)={det_exact_int(M_sup_k2)}, det(k=3)={det_exact_int(M_sup_k3)} (non-monotonic parity zeros!)")
    assert det_exact_int(M_sup_k2) == 0 and det_exact_int(M_sup_k3) == -8

    # Counterexample E: Add diagonal term d*[x==y] to Boolean-Poset Hybrid (a=1, c=1, d=1)
    dets_diag = []
    for k in range(1, 5):
        n = 1 << k
        Mk = [[(1 if (x & y) == x else 0) + (1 if (x & y) == 0 else 0) + (1 if x == y else 0)
               for y in range(n)] for x in range(n)]
        dets_diag.append(det_exact_int(Mk))
    print(f"  [COUNTEREXAMPLE E] adding [x==y] to [x<=_b y]+[x&y==0]: dets(k=1..4)={dets_diag} (sudden singularity at k=4!)")
    assert dets_diag == [4, 8, 32, 0]

    print("\nALL EXPLORATION, EXACT REPLAY, AND SHARPNESS CHECKS PASSED.")


if __name__ == "__main__":
    main()
