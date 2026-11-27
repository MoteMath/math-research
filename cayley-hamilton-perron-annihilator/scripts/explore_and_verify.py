#!/usr/bin/env python3
"""
explore_and_verify.py — Pure-Silicon Exact Integer Certificate Compiler & Independent Oracle
for CHKAE (Cayley-Hamilton, Krylov & Perron-Cone Annihilator Engine).

Zero floating-point arithmetic anywhere: uses strictly Python arbitrary-precision `int`
and `fractions.Fraction`.
"""

from math import comb, gcd
from fractions import Fraction
from functools import reduce


# ==============================================================================
# 1. Raw Pure-Silicon Bit-Level Primitives & Exact Brute-Force Oracles
# ==============================================================================

def popcount(x: int) -> int:
    return x.bit_count()


def pm1(k: int) -> int:
    return 1 if (k % 2 == 0) else -1


def clmul(a: int, b: int) -> int:
    """Carryless multiplication over F_2[X] encoded as binary integers."""
    res = 0
    while b:
        if b & 1:
            res ^= a
        a <<= 1
        b >>= 1
    return res


def no_adj_ones(x: int) -> bool:
    """Zeckendorf / Fibonacci binary word predicate: no two adjacent 1-bits."""
    return (x & (x >> 1)) == 0


def K_corr_bruteforce(c: int, n: int) -> int:
    """K_c(n) = sum_{x < 2^n} (-1)^{popcount(c*x) + popcount(clmul(c, x))}."""
    return sum(pm1(popcount(c * x) + popcount(clmul(c, x))) for x in range(1 << n))


def Z_corr_bruteforce(c: int, n: int) -> int:
    """Z_c(n) = sum_{y < 2^n, no_adj_ones(y)} (-1)^{popcount(c*y)}."""
    return sum(pm1(popcount(c * y)) for y in range(1 << n) if no_adj_ones(y))


def carry_sum_k_bruteforce(k: int, n: int) -> int:
    """C_k(n) = sum_{x_1,...,x_k < 2^n} (-1)^{popcount(sum x_i) + sum popcount(x_i)}."""
    limit = 1 << n
    if k == 3:
        total = 0
        for x in range(limit):
            px = popcount(x)
            for y in range(limit):
                pxy = px + popcount(y)
                sxy = x + y
                for z in range(limit):
                    total += pm1(popcount(sxy + z) + pxy + popcount(z))
        return total
    elif k == 4:
        total = 0
        for x in range(limit):
            px = popcount(x)
            for y in range(limit):
                pxy = px + popcount(y)
                sxy = x + y
                for z in range(limit):
                    pxyz = pxy + popcount(z)
                    sxyz = sxy + z
                    for w in range(limit):
                        total += pm1(popcount(sxyz + w) + pxyz + popcount(w))
        return total
    elif k == 5:
        total = 0
        for x in range(limit):
            px = popcount(x)
            for y in range(limit):
                pxy = px + popcount(y)
                sxy = x + y
                for z in range(limit):
                    pxyz = pxy + popcount(z)
                    sxyz = sxy + z
                    for w in range(limit):
                        pxyzw = pxyz + popcount(w)
                        sxyzw = sxyz + w
                        for t in range(limit):
                            total += pm1(popcount(sxyzw + t) + pxyzw + popcount(t))
        return total
    raise ValueError(f"Unsupported k={k}")


def v2(n: int) -> int:
    """Exact 2-adic valuation of nonzero integer n."""
    assert n != 0
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


# ==============================================================================
# 2. Exact Integer Matrix & Vector Arithmetic (Mirroring the Lean sources CHKAE)
# ==============================================================================

def vec_dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def vec_add(u, v):
    return [a + b for a, b in zip(u, v)]


def vec_sub(u, v):
    return [a - b for a, b in zip(u, v)]


def vec_scale(a, v):
    return [a * x for x in v]


def mat_vec(M, v):
    return [vec_dot(row, v) for row in M]


def vec_mat(u, A):
    c = len(A[0])
    return [sum(u[i] * A[i][j] for i in range(len(u))) for j in range(c)]


def mat_scale(a, M):
    return [[a * x for x in row] for row in M]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_id(d):
    return [[1 if i == j else 0 for j in range(d)] for i in range(d)]


def mat_mul(A, B):
    r, k, c = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(c)] for i in range(r)]


def mat_pow(M, n):
    d = len(M)
    res = mat_id(d)
    for _ in range(n):
        res = mat_mul(M, res)
    return res


def vec_iter(M, v, n):
    cur = v[:]
    for _ in range(n):
        cur = mat_vec(M, cur)
    return cur


def vec_iter_lin_comb(d, M, v, cs):
    acc = [0] * d
    cur = v[:]
    for c in cs:
        acc = vec_add(acc, vec_scale(c, cur))
        cur = mat_vec(M, cur)
    return acc


def mat_iter_lin_comb(d, M, cs):
    acc = [[0] * d for _ in range(d)]
    cur = mat_id(d)
    for c in cs:
        acc = mat_add(acc, mat_scale(c, cur))
        cur = mat_mul(M, cur)
    return acc


def obs(M, u, v, n):
    return vec_dot(u, vec_iter(M, v, n))


def scaled_coeffs(q, c):
    k = len(c)
    return [c[j] * (q ** (k - j)) for j in range(k)]


def homog_eval(C, a, b):
    K = len(C)
    return a ** K - sum(C[j] * (a ** j) * (b ** (K - j)) for j in range(K))


# ==============================================================================
# 3. Exact Mirror of the Five CHKAE Certificate Checkers
# ==============================================================================

def check_mat_ann(d, M, c):
    if len(M) != d or any(len(r) != d for r in M) or len(c) == 0:
        return False
    return mat_pow(M, len(c)) == mat_iter_lin_comb(d, M, c)


def check_quot_ann(d, M, u, v, n0, c, r):
    if len(M) != d or any(len(row) != d for row in M):
        return False
    if len(u) != d or len(v) != d or len(c) == 0:
        return False
    v0 = vec_iter(M, v, n0)
    w = vec_sub(vec_iter(M, v0, len(c)), vec_iter_lin_comb(d, M, v0, c))
    if vec_iter(M, w, len(r)) != vec_iter_lin_comb(d, M, w, r):
        return False
    return all(vec_dot(u, vec_iter(M, w, j)) == 0 for j in range(len(r)))


def check_identity(d1, M1, u1, v1, off1, scale1, r1, d2, M2, u2, v2, off2, scale2, r2, c):
    if not check_quot_ann(d1, M1, u1, v1, off1, c, r1):
        return False
    if not check_quot_ann(d2, M2, u2, v2, off2, c, r2):
        return False
    return all(
        scale1 * obs(M1, u1, v1, off1 + j) == scale2 * obs(M2, u2, v2, off2 + j)
        for j in range(len(c))
    )


def check_scaled_val(d, M, u, v, n0, pre_shift, q, c, r, init_quot, m0, period_table):
    k = len(c)
    P = len(period_table)
    if q <= 0 or m0 <= 0 or P == 0 or len(init_quot) != k:
        return False
    if not check_quot_ann(d, M, u, v, n0, scaled_coeffs(q, c), r):
        return False
    if not all(obs(M, u, v, n0 + j) == (q ** (j + pre_shift)) * init_quot[j] for j in range(k)):
        return False
    if not all(init_quot[j] % m0 == period_table[j % P] for j in range(k)):
        return False
    if not all(
        period_table[(t + k) % P] == sum(c[j] * period_table[(t + j) % P] for j in range(k)) % m0
        for t in range(P)
    ):
        return False
    return True


def check_pos_bound(d, M, u, v, n0, tau, C, r, alpha, beta, a, b, strict):
    if tau not in (1, -1) or a < 0 or b < 1 or any(x < 0 for x in C):
        return False
    Mtau = mat_scale(tau, M)
    if not check_quot_ann(d, Mtau, u, v, n0, C, r):
        return False
    if beta * homog_eval(C, a, b) < 0:
        return False
    K = len(C)
    if strict:
        if sum(C) <= 0:
            return False
        return all(
            alpha * (tau ** j) * (b ** j) * obs(M, u, v, n0 + j) + beta * (a ** j) > 0
            for j in range(K)
        )
    else:
        return all(
            alpha * (tau ** j) * (b ** j) * obs(M, u, v, n0 + j) + beta * (a ** j) >= 0
            for j in range(K)
        )


def check_cone(d, m, M, u, v, n0, D, G, A, D0, y0, rate_num):
    if len(M) != d or any(len(row) != d for row in M):
        return False
    if len(u) != d or len(v) != d:
        return False
    if len(G) != d or any(len(row) != m for row in G):
        return False
    if len(A) != m or any(len(row) != m for row in A):
        return False
    if len(y0) != m:
        return False
    if D <= 0 or D0 <= 0 or rate_num < 0:
        return False
    if any(A[i][j] < 0 for i in range(m) for j in range(m)):
        return False
    if any(x < 0 for x in y0) or sum(y0) <= 0:
        return False
    uG = vec_mat(u, G)
    if any(x <= 0 for x in uG):
        return False
    if any(sum(A[i][j] for i in range(m)) < 1 for j in range(m)):
        return False
    if mat_scale(D, mat_mul(M, G)) != mat_mul(G, A):
        return False
    if vec_scale(D0, vec_iter(M, v, n0)) != mat_vec(G, y0):
        return False
    uGA = vec_mat(uG, A)
    if any(uGA[j] < rate_num * uG[j] for j in range(m)):
        return False
    return True


# ==============================================================================
# 4. Transfer-Matrix Constructors for Pure-Silicon Binary Families
# ==============================================================================

def build_kway_carry_tm(k: int):
    """k-way binary carry-parity transfer matrix (d = k carry states)."""
    M = [[0] * k for _ in range(k)]
    for c in range(k):
        sign = 1 if (c % 2 == 0) else -1
        for s in range(k + 1):
            M[(c + s) // 2][c] += comb(k, s) * sign
    v = [1 if c == 0 else 0 for c in range(k)]
    u = [pm1(popcount(c)) for c in range(k)]
    return M, u, v


def build_Kc_tm(c: int):
    """Carried vs. carryless parity correlation K_c(n) transfer matrix (d = c carry states)."""
    M = [[0] * c for _ in range(c)]
    pc = popcount(c) % 2
    for q in range(c):
        for b in (0, 1):
            t = q + c * b
            M[t // 2][q] += pm1((t % 2) + pc * b)
    v = [1 if q == 0 else 0 for q in range(c)]
    u = [pm1(popcount(q)) for q in range(c)]
    return M, u, v


def build_Zc_tm(c: int):
    """Zeckendorf (no-adjacent-1s) carried multiply-by-c parity Z_c(n) transfer matrix (d = 2c)."""
    d = 2 * c
    M = [[0] * d for _ in range(d)]
    for q in range(c):
        for lb in (0, 1):
            idx = 2 * q + lb
            for b in (0, 1):
                if lb == 1 and b == 1:
                    continue
                t = q + c * b
                M[2 * (t // 2) + b][idx] += pm1(t % 2)
    v = [1 if i == 0 else 0 for i in range(d)]
    u = [pm1(popcount(i // 2)) for i in range(d)]
    return M, u, v


def char_poly_faddeev(M):
    """Exact integer Faddeev-LeVerrier characteristic polynomial det(X*I - M)."""
    n = len(M)
    c = [0] * (n + 1)
    c[n] = 1
    B = mat_id(n)
    for k in range(1, n + 1):
        MB = mat_mul(M, B)
        tr = sum(MB[i][i] for i in range(n))
        assert -tr % k == 0
        ck = -tr // k
        c[n - k] = ck
        if k < n:
            B = [[MB[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
    return c


# ==============================================================================
# 5. Main Verification, Certificate Synthesis, Independent Replay & Mutation Suite
# ==============================================================================

def main():
    print("=" * 76)
    print("CHKAE Pure-Silicon Exact Integer Verification & Mutation Test Suite")
    print("=" * 76)

    M_K7, u_K7, v_K7 = build_Kc_tm(7)
    M_Z5, u_Z5, v_Z5 = build_Zc_tm(5)
    M_C3, u_C3, v_C3 = build_kway_carry_tm(3)
    M_C4, u_C4, v_C4 = build_kway_carry_tm(4)
    M_C5, u_C5, v_C5 = build_kway_carry_tm(5)
    M_K23, u_K23, v_K23 = build_Kc_tm(23)

    # ------------------------------------------------------------------
    # A. Exact semantic verification: Transfer matrices == Brute force
    # ------------------------------------------------------------------
    print("\n[A] Checking transfer-matrix exactness against raw bit-level brute force...")
    for n in range(11):
        assert obs(M_K7, u_K7, v_K7, n) == K_corr_bruteforce(7, n)
        assert obs(M_Z5, u_Z5, v_Z5, n) == Z_corr_bruteforce(5, n)
    for n in range(9):
        assert obs(M_K23, u_K23, v_K23, n) == K_corr_bruteforce(23, n)
    for n in range(6):
        assert obs(M_C3, u_C3, v_C3, n) == carry_sum_k_bruteforce(3, n)
    for n in range(4):
        assert obs(M_C4, u_C4, v_C4, n) == carry_sum_k_bruteforce(4, n)
    for n in range(3):
        assert obs(M_C5, u_C5, v_C5, n) == carry_sum_k_bruteforce(5, n)
    print("  PASS: All transfer matrices match raw bit-level brute force identically!")

    # Print characteristic polynomials (exact integer Faddeev-LeVerrier)
    print("\n[B] Exact integer characteristic polynomials:")
    print(f"  charpoly(M_C3) = {char_poly_faddeev(M_C3)}")
    print(f"  charpoly(M_C4) = {char_poly_faddeev(M_C4)}")
    print(f"  charpoly(M_C5) = {char_poly_faddeev(M_C5)}")
    print(f"  charpoly(M_K7) = {char_poly_faddeev(M_K7)}")
    print(f"  charpoly(M_Z5) = {char_poly_faddeev(M_Z5)}")

    # ------------------------------------------------------------------
    # C. Verify all 11 positive certificates
    # ------------------------------------------------------------------
    print("\n[C] Checking all 11 pure-data CHKAE certificates...")

    # Cert 1: Full-matrix Cayley-Hamilton for M_C3 and M_C5
    assert check_mat_ann(3, M_C3, [-64, 24, 2])
    assert check_mat_ann(5, M_C5, [32768, -10240, -384, 240, 2])
    print("  1. MatAnnCert(M_C3, M_C5): PASS")

    # Cert 2: Cross-Automaton Identity K_7(n+3) = 2 * Z_5(n)
    # Note: p(X) = X^3 - X^2 + X - 2 -> c = [2, -1, 1]
    # For M_K7 at off1=3: defect w = p(M_K7)(M_K7^3 v_K7) satisfies M_K7 w = w -> r1 = [1]!
    # For M_Z5 at off2=0: defect w = p(M_Z5) v_Z5 satisfies M_Z5 w = 0 -> r2 = [0]!
    c_cubic = [2, -1, 1]
    assert check_identity(7, M_K7, u_K7, v_K7, 3, 1, [1], 10, M_Z5, u_Z5, v_Z5, 0, 2, [0], c_cubic)
    print("  2. IdentityCert(K_7(n+3) = 2*Z_5(n)): PASS")

    # Cert 3: Positivity of Z_5(n) > 0 and K_7(n+3) > 0 via P(X) = (X+1)p(X) = X^4 - X - 2 -> C = [2, 1, 0, 0]
    C_Z5 = [2, 1, 0, 0]
    assert check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, C_Z5, [0], 1, 0, 1, 1, True)
    assert check_pos_bound(7, M_K7, u_K7, v_K7, 0, 1, C_Z5, [1], 1, 0, 1, 1, True)
    print("  3. PosBoundCert(Z_5(n) > 0 and K_7(n) > 0, quotient-projected): PASS")

    # Cert 4: Sharp irrational-rate sandwich for Z_5(n): (23/17)^n <= Z_5(n) <= (5/3)*(19/14)^n
    assert check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, C_Z5, [0], 1, -1, 23, 17, False)
    assert check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, C_Z5, [0], -3, 5, 19, 14, False)
    print("  4. PosBoundCert(Z_5 sandwich 23/17 <= rho <= 19/14): PASS")

    # Cert 5: Exact mod-2 periodicity of Z_5(n) (period 3: [1, 0, 1]) via ScaledValCert(q=1, m0=2)
    assert check_scaled_val(10, M_Z5, u_Z5, v_Z5, 0, 0, 1, c_cubic, [0], [1, 2, 3], 2, [1, 0, 1])
    print("  5. ScaledValCert(Z_5(n) mod 2 period 3): PASS")

    # Cert 6: Exact 2-adic valuation & odd-part mod-4 law for C_3(n) (n >= 2)
    # Scaled coeffs of M_C3: c_scaled = [-8, 6, 1], q = 2, n0 = 2, preShift = 3
    # At n=2,3,4: C_3 = [24, -16, 544] = [2^3 * 3, 2^4 * (-1), 2^5 * 17]
    # Note: for n0 = 3, preShift = 4: C_3(3,4,5) = [-16, 544, -832] = [2^4*(-1), 2^5*17, 2^6*(-13)],
    # odd parts mod 4 = [3, 1, 3, 1, ...] (exact period 2 starting at n0=3!),
    # while for n0 = 2, preShift = 3, odd parts mod 2 = [1] (exact period 1 starting at n0=2!).
    c_C3_sc = [-8, 6, 1]
    assert check_scaled_val(3, M_C3, u_C3, v_C3, 2, 3, 2, c_C3_sc, [], [3, -1, 17], 2, [1])
    assert check_scaled_val(3, M_C3, u_C3, v_C3, 3, 4, 2, c_C3_sc, [], [-1, 17, -13], 4, [3, 1])
    print("  6. ScaledValCert(C_3 exact v_2 = n+1 for n>=2 & odd part mod 4 = (-1)^n for n>=3): PASS")

    # Cert 7: C_3(n) strict alternating sign (-1)^n C_3(n) > 0 for n >= 2
    # Positive annihilator for -M_C3: C = [384, 16, 4, 22, 0]
    C_C3 = [384, 16, 4, 22, 0]
    assert check_pos_bound(3, M_C3, u_C3, v_C3, 2, -1, C_C3, [], 1, 0, 1, 1, True)
    print("  7. PosBoundCert((-1)^n C_3(n) > 0 for n >= 2): PASS")

    # Cert 8: C_3(n) sharp irrational-rate sandwich around 1 + sqrt(17) ~ 5.1231:
    # 1/9 * (128/25)^n <= (-1)^n C_3(n) <= (41/8)^n for n >= 2
    # Shift m = n - 2: (9 * 25^2) * (-1)^m * 25^m * C_3(m+2) - 128^2 * 128^m >= 0
    #                  -(8^2) * (-1)^m * 8^m * C_3(m+2) + 41^2 * 41^m >= 0
    assert check_pos_bound(3, M_C3, u_C3, v_C3, 2, -1, C_C3, [], 5625, -16384, 128, 25, False)
    assert check_pos_bound(3, M_C3, u_C3, v_C3, 2, -1, C_C3, [], -64, 1681, 41, 8, False)
    print("  8. PosBoundCert(C_3 sandwich 128/25 <= 1+sqrt(17) <= 41/8): PASS")

    # Cert 9: C_4(n) exact closed form: 12 * C_4(n) = 8*8^n + 12*(-8)^n - 9*4^n + (-4)^n
    M_diag4 = [[8, 0, 0, 0], [0, -8, 0, 0], [0, 0, 4, 0], [0, 0, 0, -4]]
    u_diag4 = [8, 12, -9, 1]
    v_diag4 = [1, 1, 1, 1]
    c_C4 = [-1024, 0, 80, 0]
    assert check_identity(4, M_C4, u_C4, v_C4, 0, 12, [], 4, M_diag4, u_diag4, v_diag4, 0, 1, [], c_C4)
    print("  9. IdentityCert(12*C_4(n) = 8*8^n + 12*(-8)^n - 9*4^n + (-4)^n): PASS")

    # Cert 10: C_5(n) exact 2-adic valuation v_2(C_5(n)) = n + 2 & odd part mod 8 in {3, 7} for n >= 3
    c_C5_sc = [1024, -640, -48, 60, 1]
    init_C5_odd = [obs(M_C5, u_C5, v_C5, 3 + j) // (2 ** (5 + j)) for j in range(5)]
    assert check_scaled_val(5, M_C5, u_C5, v_C5, 3, 5, 2, c_C5_sc, [], init_C5_odd, 8, [3, 7])
    print(f" 10. ScaledValCert(C_5 exact v_2 = n+2 & odd part mod 8 = [3,7] for n>=3, init={init_C5_odd}): PASS")

    # Cert 11: C_5(n) > 0 for all n >= 12 (and n = 8..11 directly => all n >= 8!) via 5x8 Integer Perron Cone
    D_C5 = 925968
    D0_C5 = 57873
    G_C5 = [
        [0, 1, 0, 1, -14, 15, -5, 6],
        [-11, 4, -17, 10, -19, 12, -13, 6],
        [-19, -19, -33, -6, -19, -19, -33, -6],
        [4, -11, -17, 10, 12, -19, -13, 6],
        [1, 0, 0, 1, 15, -14, -5, 6],
    ]
    A_C5 = [
        [0, 11989452, 0, 0, 0, 456108, 0, 0],
        [11989452, 0, 0, 0, 456108, 0, 0, 0],
        [354151, 354151, 0, 9919008, 3835871, 3835871, 4421376, 4828608],
        [551311, 551311, 7829520, 2065248, 3958919, 3958919, 4426224, 4799520],
        [126060, 0, 0, 0, 4581708, 0, 0, 0],
        [0, 126060, 0, 0, 0, 4581708, 0, 0],
        [118055, 118055, 2210688, 1153824, 91807, 91807, 4033536, 0],
        [0, 0, 3160896, 0, 0, 0, 0, 3829920],
    ]
    y0_C5 = [96973884732997632, 0, 4371335653052416, 4860569286897664, 0, 738304878182400, 1561239040151552, 0]
    rate_C5 = 2469248  # = (8/3) * 925968 exactly!
    assert 3 * rate_C5 == 8 * D_C5
    assert check_cone(5, 8, M_C5, u_C5, v_C5, 12, D_C5, G_C5, A_C5, D0_C5, y0_C5, rate_C5)
    for n_small in [8, 9, 10, 11]:
        assert obs(M_C5, u_C5, v_C5, n_small) > 0
    print(" 11. ConeCert(C_5(n) > 0 for all n >= 8 & Perron rate >= 8/3 for n >= 12): PASS")

    # ------------------------------------------------------------------
    # D. Independent Exact Replay up to n = 60
    # ------------------------------------------------------------------
    print("\n[D] Independent exact integer replay up to n = 60...")
    for n in range(60):
        k7 = obs(M_K7, u_K7, v_K7, n + 3)
        z5 = obs(M_Z5, u_Z5, v_Z5, n)
        assert k7 == 2 * z5
        assert z5 > 0 and obs(M_K7, u_K7, v_K7, n) > 0
        assert (17 ** n) * z5 >= (23 ** n)
        assert 3 * (14 ** n) * z5 <= 5 * (19 ** n)
        assert (z5 % 2) == (0 if n % 3 == 1 else 1)

        c4 = obs(M_C4, u_C4, v_C4, n)
        assert 12 * c4 == 8 * (8 ** n) + 12 * ((-8) ** n) - 9 * (4 ** n) + ((-4) ** n)

        if n >= 2:
            c3 = obs(M_C3, u_C3, v_C3, n)
            assert ((-1) ** n) * c3 > 0
            assert v2(c3) == n + 1
            if n >= 3:
                assert (c3 // (1 << (n + 1))) % 4 == (1 if n % 2 == 0 else 3)
            assert 9 * (25 ** n) * (((-1) ** n) * c3) >= (128 ** n)
            assert (8 ** n) * (((-1) ** n) * c3) <= (41 ** n)

        if n >= 3:
            c5 = obs(M_C5, u_C5, v_C5, n)
            assert v2(c5) == n + 2
            assert (c5 // (1 << (n + 2))) % 8 == (7 if n % 2 == 0 else 3)
        if n >= 8:
            assert obs(M_C5, u_C5, v_C5, n) > 0
        if n >= 12:
            m = n - 12
            assert (D_C5 ** m) * obs(M_C5, u_C5, v_C5, n) >= obs(M_C5, u_C5, v_C5, 12) * (rate_C5 ** m)
    print("  PASS: All 60-step exact integer replays match every infinite theorem!")

    # ------------------------------------------------------------------
    # E. Sharpness & Boundary Falsification Witnesses
    # ------------------------------------------------------------------
    print("\n[E] Checking sharpness & falsification counterexamples...")
    k23_3 = K_corr_bruteforce(23, 3)
    k23_4 = K_corr_bruteforce(23, 4)
    assert k23_3 == 0 and k23_4 == -4
    assert obs(M_K23, u_K23, v_K23, 3) == 0 and obs(M_K23, u_K23, v_K23, 4) == -4
    print(f"  Sharpness 1 (K_c positivity fails at c=23 after 10 odd wins): K_23(3)={k23_3}, K_23(4)={k23_4}")

    c3_1 = carry_sum_k_bruteforce(3, 1)
    assert c3_1 == 0
    print(f"  Sharpness 2 (C_3 n>=2 bound): C_3(1)={c3_1}")

    c5_2 = carry_sum_k_bruteforce(5, 2)
    c5_7 = obs(M_C5, u_C5, v_C5, 7)
    c5_8 = obs(M_C5, u_C5, v_C5, 8)
    c5_9 = obs(M_C5, u_C5, v_C5, 9)
    assert c5_2 == 320 and v2(c5_2) == 6  # != 2+2
    assert c5_7 == -5614080 and c5_8 == 1734802432 and c5_9 == 1465391104
    print(f"  Sharpness 3 (C_5 deceptive alternation breaks at n=9; n>=8 sharp): C_5(7)={c5_7}, C_5(8)={c5_8}, C_5(9)={c5_9}")
    print(f"  Sharpness 4 (C_5 valuation n>=3 sharp): C_5(2)={c5_2}, v2={v2(c5_2)} != 4")

    assert K_corr_bruteforce(7, 2) != 2 * Z_corr_bruteforce(5, 2)
    print(f"  Sharpness 5 (K_7 vs 2*Z_5 shift +3 sharp): K_7(2)={K_corr_bruteforce(7,2)} != 2*Z_5(2)={2*Z_corr_bruteforce(5,2)}")

    # ------------------------------------------------------------------
    # F. Hostile Negative / Mutation Tests (Every Broken Cert MUST Return False!)
    # ------------------------------------------------------------------
    print("\n[F] Running 15 hostile certificate mutation tests (all must reject = False)...")
    mutations = [
        ("M01 MatAnn bad coeff", check_mat_ann(3, M_C3, [-64, 24, 3])),
        ("M02 QuotAnn empty defect on K7", check_quot_ann(7, M_K7, u_K7, v_K7, 3, c_cubic, [])),
        ("M03 QuotAnn wrong defect r=[2]", check_quot_ann(7, M_K7, u_K7, v_K7, 3, c_cubic, [2])),
        ("M04 Identity bad off1=2", check_identity(7, M_K7, u_K7, v_K7, 2, 1, [1], 10, M_Z5, u_Z5, v_Z5, 0, 2, [0], c_cubic)),
        ("M05 Identity bad scale2=3", check_identity(7, M_K7, u_K7, v_K7, 3, 1, [1], 10, M_Z5, u_Z5, v_Z5, 0, 3, [0], c_cubic)),
        ("M06 ScaledVal over-strong preShift+1", check_scaled_val(3, M_C3, u_C3, v_C3, 2, 4, 2, c_C3_sc, [], [3, -1, 17], 2, [1])),
        ("M07 ScaledVal corrupted period table", check_scaled_val(5, M_C5, u_C5, v_C5, 3, 5, 2, c_C5_sc, [], init_C5_odd, 8, [3, 5])),
        ("M08 PosBound tau=0 loophole blocked", check_pos_bound(3, M_C3, u_C3, v_C3, 2, 0, C_C3, [], 1, 0, 1, 1, True)),
        ("M09 PosBound negative C coeff", check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, [2, -1, 1], [0], 1, 0, 1, 1, True)),
        ("M10 PosBound invalid lower base 24/17", check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, C_Z5, [0], 1, -1, 24, 17, False)),
        ("M11 PosBound invalid upper base 23/17", check_pos_bound(10, M_Z5, u_Z5, v_Z5, 0, 1, C_Z5, [0], -3, 5, 23, 17, False)),
        ("M12 Cone negative A entry", check_cone(5, 8, M_C5, u_C5, v_C5, 12, D_C5, G_C5, [[-1] + A_C5[0][1:]] + A_C5[1:], D0_C5, y0_C5, rate_C5)),
        ("M13 Cone perturbed G breaks intertwining", check_cone(5, 8, M_C5, u_C5, v_C5, 12, D_C5, [[1] + G_C5[0][1:]] + G_C5[1:], A_C5, D0_C5, y0_C5, rate_C5)),
        ("M14 Cone invalid n0=7 (C_5(7)<0)", check_cone(5, 8, M_C5, u_C5, v_C5, 7, D_C5, G_C5, A_C5, D0_C5, y0_C5, rate_C5)),
        ("M15 Cone over-tight Perron rate", check_cone(5, 8, M_C5, u_C5, v_C5, 12, D_C5, G_C5, A_C5, D0_C5, y0_C5, rate_C5 + 1)),
    ]
    for name, res in mutations:
        assert res is False, f"MUTATION FAILED TO REJECT: {name}"
        print(f"  {name}: REJECTED (False)")

    print("\n" + "=" * 76)
    print("ALL VERIFICATION, REPLAY, SHARPNESS, AND 15/15 MUTATION TESTS PASSED!")
    print("=" * 76)


if __name__ == "__main__":
    main()
