#!/usr/bin/env python3
"""
Exact Pure-Silicon Exploration, Certificate Synthesis, Verification & Counterexample Suite
for the Dyadic Skew-Congruence & Schur-Elimination Pfaffian Engine (`dyadic-skew-congruence-pfaffian`).

Zero floating-point arithmetic is used anywhere: all matrix entries, congruences,
eliminations, determinants, and Pfaffians are computed in exact Python `int` / `fractions.Fraction`.
"""

from fractions import Fraction


# ============================================================================
# 1. Exact Combinatorial & Congruence Pfaffian Evaluators
# ============================================================================

def pfaffian_laplace(A):
    """Exact combinatorial Pfaffian by row-0 Laplace expansion (matches Lean `pfaffian`)."""
    n = len(A)
    if n == 0:
        return 1
    assert n % 2 == 0
    total = 0
    for j in range(1, n):
        a0j = A[0][j]
        if a0j == 0:
            continue
        sub = [[A[r][c] for c in range(1, n) if c != j] for r in range(1, n) if r != j]
        sign = 1 if (j - 1) % 2 == 0 else -1
        total += sign * a0j * pfaffian_laplace(sub)
    return total


def pfaffian_exact_elim(A):
    """Exact Pfaffian over Q via congruence Schur elimination (fast up to n=64)."""
    n = len(A)
    if n == 0:
        return 1
    assert n % 2 == 0
    for i in range(n):
        assert A[i][i] == 0, f"Nonzero diagonal at {i}"
        for j in range(i + 1, n):
            assert A[i][j] == -A[j][i], f"Not skew at ({i},{j})"
    M = [[Fraction(A[i][j]) for j in range(n)] for i in range(n)]
    pf = Fraction(1)
    for k in range(0, n, 2):
        piv = None
        for j in range(k + 1, n):
            if M[k][j] != 0:
                piv = j
                break
        if piv is None:
            return 0
        if piv != k + 1:
            M[k + 1], M[piv] = M[piv], M[k + 1]
            for i in range(n):
                M[i][k + 1], M[i][piv] = M[i][piv], M[i][k + 1]
            pf = -pf
        p = M[k][k + 1]
        pf *= p
        for i in range(k + 2, n):
            a_i = M[k][i]
            b_i = M[k + 1][i]
            if a_i == 0 and b_i == 0:
                continue
            for j in range(i + 1, n):
                delta = (b_i * M[k][j] - a_i * M[k + 1][j]) / p
                M[i][j] += delta
                M[j][i] -= delta
    assert pf.denominator == 1
    return pf.numerator


def mat_mul(A, B):
    n, m, p = len(A), len(B[0]), len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]


# ============================================================================
# 2. Pure-Silicon Bitwise Primitives & Matrix Families
# ============================================================================

def sgn(d):
    return 1 if d > 0 else (-1 if d < 0 else 0)

def parity(x):
    return 1 if (x.bit_count() & 1) == 0 else -1

def gray(x):
    return x ^ (x >> 1)

def inv_gray(x):
    y = x
    s = 1
    while (x >> s) > 0:
        y ^= (x >> s)
        s += 1
    return y

def msb(x):
    assert x > 0
    return x.bit_length() - 1

def carries(x, y):
    return x.bit_count() + y.bit_count() - (x + y).bit_count()


def carry_asym_matrix(k):
    """C_k(x, y) = carries(x, ~y) - carries(y, ~x) on k-bit integers."""
    n = 1 << k
    mask = n - 1
    return [[carries(i, mask ^ j) - carries(j, mask ^ i) for j in range(n)] for i in range(n)]

def skew_ones_matrix(n):
    """S_n(x, y) = sgn(y - x)."""
    return [[sgn(j - i) for j in range(n)] for i in range(n)]

def carry_pencil_matrix(k, a, b):
    """a * C_k + b * S_{2^k}."""
    n = 1 << k
    C = carry_asym_matrix(k)
    S = skew_ones_matrix(n)
    return [[a * C[i][j] + b * S[i][j] for j in range(n)] for i in range(n)]

def carry_pencil_formula(k, a, b):
    """(b - (2^k - 1)*a) * prod_{j=1}^{k-1} (b - (2^j - 1)*a)^(2^(k-1-j))."""
    assert k >= 1
    res = b - ((1 << k) - 1) * a
    for j in range(1, k):
        res *= (b - ((1 << j) - 1) * a) ** (1 << (k - 1 - j))
    return res

def gray_walsh_matrix(n, weights=None):
    """G_n^{(b)}(x, y) = b_{msb(x^y)} * sgn(y-x) * (-1)^popcount(gray(x) & gray(y))."""
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        gi = gray(i)
        for j in range(n):
            if i == j:
                continue
            w = 1 if weights is None else weights[msb(i ^ j)]
            A[i][j] = w * sgn(j - i) * parity(gi & gray(j))
    return A

def gray_walsh_weighted_formula(k, weights):
    """Exact signed Pfaffian of G_{2^k}^{(b)}."""
    assert k >= 1
    if k == 1:
        return weights[0]
    mu = weights[0] ** 2 + sum((1 << j) * (weights[j] ** 2) for j in range(1, k))
    if k == 2:
        return -mu
    return mu ** (1 << (k - 2))

def gray_walsh_even_formula(n):
    """Exact closed-form signed Pfaffian of unweighted G_n for ANY even n >= 0 via binary reflection."""
    assert n >= 0 and n % 2 == 0
    if n == 0:
        return 1
    if n == 2:
        return 1
    k = (n - 1).bit_length() - 1
    two_k = 1 << k
    r = (n - two_k) // 2
    ref = two_k - 2 * r
    sign = -1 if (r % 2 == 1) else 1
    return sign * ((1 << (k + 1)) - 1) ** r * gray_walsh_even_formula(ref)

def skew_walsh_matrix(n, shift=0):
    """W_n^{(s)}(x, y) = sgn(y - x) * (-1)^popcount((x+s) & (y+s))."""
    return [[sgn(j - i) * parity((i + shift) & (j + shift)) for j in range(n)] for i in range(n)]


# ============================================================================
# 3. Verification Suite
# ============================================================================

def main():
    print("=== [0] Cross-checking Laplace vs Elimination Pfaffian evaluators ===")
    for k in [1, 2, 3]:
        for name, M in [
            (f"C_{k}", carry_asym_matrix(k)),
            (f"G_{1<<k}", gray_walsh_matrix(1 << k)),
            (f"W_{1<<k}", skew_walsh_matrix(1 << k)),
        ]:
            p1 = pfaffian_laplace(M)
            p2 = pfaffian_exact_elim(M)
            assert p1 == p2, f"Mismatch on {name}: {p1} vs {p2}"
    print("  PASS: Laplace and elimination evaluators agree identically on all k <= 3 (n <= 8).")

    print("\n=== [1] Theorem A: Carry-Asymmetry Homogeneous Mersenne-Root Pfaffian Pencil ===")
    # Test pure carry-asymmetry (a=1, b=0) up to k=6 (64x64)
    for k in range(1, 7):
        C = carry_asym_matrix(k)
        pf = pfaffian_exact_elim(C)
        exp = carry_pencil_formula(k, 1, 0)
        assert pf == exp, f"Mismatch at k={k}: {pf} != {exp}"
        print(f"  k={k} (n={1<<k:2d}): Pf(C_k) = {pf}")

    # Test dyadic collapse (a=1, b=-1) up to k=5
    for k in range(1, 6):
        M = carry_pencil_matrix(k, 1, -1)
        pf = pfaffian_exact_elim(M)
        exp = ((-1) ** (1 << (k - 1))) * (1 << ((1 << k) - 1))
        assert pf == exp == carry_pencil_formula(k, 1, -1)
    print("  PASS: Dyadic collapse Pf(C_k - S_{2^k}) = (-1)^(2^(k-1)) * 2^(2^k - 1) verified k=1..5.")

    # Test arbitrary integer pairs (a, b) including singular Mersenne roots and negative values
    test_ab = [(1, 1), (1, 3), (1, 7), (1, 15), (2, 5), (-3, 4), (0, 2), (1, 2), (3, -7)]
    for k in range(1, 6):
        for a, b in test_ab:
            M = carry_pencil_matrix(k, a, b)
            pf = pfaffian_exact_elim(M)
            exp = carry_pencil_formula(k, a, b)
            assert pf == exp, f"Mismatch at k={k}, a={a}, b={b}: {pf} != {exp}"
    print(f"  PASS: Homogeneous pencil formula verified across k=1..5 and {len(test_ab)} (a,b) pairs.")

    # Verify the explicit integral block-congruence certificate Q*L on k=1..4
    for k in range(1, 5):
        m = 1 << k
        for a, b in [(1, 0), (1, 1), (2, 5)]:
            M_big = carry_pencil_matrix(k + 1, a, b)
            # Construct Q = [[I, -I], [0, I]] and L = [[2I, 0], [Y, I]] where Y^T = I - 1*chi^T
            # So P = Q * L = [[2I - Y, -I], [Y, I]]
            # Let's check P^T M_big P == (2*(2a C_k + (b-a) S_m)) (+) (2*(b-a) S_m)
            Y = [[(1 if i == j else 0) - (1 if i % 2 == 0 else -1) for j in range(m)] for i in range(m)]
            P = [[0] * (2 * m) for _ in range(2 * m)]
            for i in range(m):
                for j in range(m):
                    P[i][j] = (2 if i == j else 0) - Y[i][j]
                    P[i][m + j] = -1 if i == j else 0
                    P[m + i][j] = Y[i][j]
                    P[m + i][m + j] = 1 if i == j else 0
            PT = [[P[j][i] for j in range(2 * m)] for i in range(2 * m)]
            res = mat_mul(mat_mul(PT, M_big), P)
            C_k = carry_asym_matrix(k)
            S_m = skew_ones_matrix(m)
            for i in range(m):
                for j in range(m):
                    assert res[i][j] == 2 * (2 * a * C_k[i][j] + (b - a) * S_m[i][j])
                    assert res[i][m + j] == 0
                    assert res[m + i][j] == 0
                    assert res[m + i][m + j] == 2 * (b - a) * S_m[i][j]
    print("  PASS: Exact integer block-congruence certificate P^T (aC_{k+1}+bS) P = block_diag verified k=1..4.")

    print("\n=== [2] Theorem B: Parametric Level-Weighted Gray-Walsh Signed Pfaffian Law ===")
    weight_seqs = [
        [1, 1, 1, 1, 1, 1],
        [2, 3, -1, 5, 2, 1],
        [0, 1, 2, 3, 4, 5],   # Test b_0 = 0 edge case!
        [0, 0, 1, 2, 3, 4],   # Test b_0 = b_1 = 0 edge case!
        [-3, 2, -5, 1, 7, 1],
    ]
    for w in weight_seqs:
        for k in range(1, 6):
            G = gray_walsh_matrix(1 << k, w)
            pf = pfaffian_exact_elim(G)
            exp = gray_walsh_weighted_formula(k, w)
            assert pf == exp, f"Mismatch for weights={w}, k={k}: {pf} != {exp}"
            # Also verify skew-conference identity G^2 = -mu * I
            if k <= 4:
                mu = w[0] ** 2 + sum((1 << j) * (w[j] ** 2) for j in range(1, k))
                G2 = mat_mul(G, G)
                for i in range(1 << k):
                    for j in range(1 << k):
                        assert G2[i][j] == (-mu if i == j else 0)
    print(f"  PASS: Weighted Gray-Walsh Pfaffian & skew-conference G^2 = -mu*I verified for {len(weight_seqs)} weight vectors (including b_0=0) up to k=5 (32x32).")
    # Also unweighted k=6 (64x64)
    G6 = gray_walsh_matrix(64)
    pf6 = pfaffian_exact_elim(G6)
    assert pf6 == (63 ** 16)
    print(f"  PASS: Unweighted k=6 (64x64): Pf(G_64) = 63^16 = {pf6}")

    print("\n=== [3] Theorem C: All-Even Gray-Walsh Signed Binary-Reflection Law ===")
    for n in range(0, 66, 2):
        G = gray_walsh_matrix(n)
        pf = pfaffian_exact_elim(G)
        exp = gray_walsh_even_formula(n)
        assert pf == exp, f"Mismatch at even n={n}: {pf} != {exp}"
    print("  PASS: All-even reflection Pf(G_{2^k + 2r}) = (-1)^r (2^(k+1)-1)^r Pf(G_{2^k - 2r}) verified for EVERY even n in [0..64].")

    print("\n=== [4] Theorem D: Skew-Walsh Unimodularity & Phase-Transition Contrast ===")
    for k in range(1, 7):
        W = skew_walsh_matrix(1 << k, shift=0)
        pf = pfaffian_exact_elim(W)
        assert pf == 1, f"Mismatch on Skew-Walsh k={k}: {pf}"
    print("  PASS: Skew-Walsh Pf(W_{2^k}) = +1 verified for k=1..6 (up to 64x64).")

    print("\n=== [5] Sharpness & Falsification Counterexamples ===")
    # 5a. Carry-asymmetry without bit-complement: sgn(y-x) * carries(x, y)
    bad_carry = [[sgn(j - i) * carries(i, j) for j in range(4)] for i in range(4)]
    pf_bad_carry = pfaffian_laplace(bad_carry)
    print(f"  Counterexample 1 (raw skew-carry without complement, k=2): Pf = {pf_bad_carry} (collapses to 0, vs Pf(C_2) = 3)")
    assert pf_bad_carry == 0

    # 5b. Gray shift r=2 (x ^ (x >> 2)) vs r=1 (Gray code)
    bad_r2_k2 = [[sgn(j - i) * parity((i ^ (i >> 2)) & (j ^ (j >> 2))) for j in range(4)] for i in range(4)]
    bad_r2_k3 = [[sgn(j - i) * parity((i ^ (i >> 2)) & (j ^ (j >> 2))) for j in range(8)] for i in range(8)]
    print(f"  Counterexample 2a (shift-XOR r=2, k=2,3): Pf = {pfaffian_laplace(bad_r2_k2)}, {pfaffian_laplace(bad_r2_k3)} (collapses to 1, vs -3, 49)")
    assert pfaffian_laplace(bad_r2_k2) == 1 and pfaffian_laplace(bad_r2_k3) == 1

    # 5c. Inverse Gray (prefix-XOR) at k=3
    bad_invgray = [[sgn(j - i) * parity(inv_gray(i) & inv_gray(j)) for j in range(8)] for i in range(8)]
    pf_ig = pfaffian_laplace(bad_invgray)
    print(f"  Counterexample 2b (prefix-XOR inv_gray, k=3): Pf = {pf_ig} (breaks 7^2 = 49)")
    assert pf_ig == 33

    # 5d. Shifted Skew-Walsh at s=2, k=2
    bad_sw_s2 = skew_walsh_matrix(4, shift=2)
    pf_sw2 = pfaffian_laplace(bad_sw_s2)
    print(f"  Counterexample 3 (shifted Skew-Walsh s=2, k=2): Pf = {pf_sw2} (breaks unimodularity Pf=1, while s=0,1 give 1)")
    assert pf_sw2 == 3
    assert pfaffian_laplace(skew_walsh_matrix(4, shift=1)) == 1

    # 5e. Non-Gray-Walsh shift r=3 at k=4
    bad_r3_k4 = [[sgn(j - i) * parity((i ^ (i >> 3)) & (j ^ (j >> 3))) for j in range(16)] for i in range(16)]
    pf_r3 = pfaffian_exact_elim(bad_r3_k4)
    print(f"  Counterexample 4 (shift-XOR r=3, k=4): Pf = {pf_r3} (breaks both Pf=1 and Mersenne power 15^4=50625)")
    assert pf_r3 == 1025

    print("\nALL VERIFICATIONS AND SHARPNESS COUNTEREXAMPLES PASSED EXACTLY!")


if __name__ == "__main__":
    main()
