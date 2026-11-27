#!/usr/bin/env python3
"""
Pure-Silicon Exact Exploration & Independent Verification for specmat-16:
The Walsh-Defect, Weyl-Heisenberg & Hyperplane-Rotation Spectral Conjugacy Engine.

Strictly exact integer / F_2 arithmetic (zero floating-point values anywhere).
"""
import math
from fractions import Fraction


# =============================================================================
# 1. Exact k-bit F_2 linear operators and 2^k x 2^k integer matrix algebra
# =============================================================================

def vec_dot(x: int, y: int) -> int:
    return (x & y).bit_count() & 1

def sgn(bit: int) -> int:
    return -1 if (bit & 1) else 1

def bits_of(x: int, k: int):
    return [(x >> i) & 1 for i in range(k)]

def from_bits(bs) -> int:
    x = 0
    for i, b in enumerate(bs):
        if b & 1:
            x |= (1 << i)
    return x

def gray_fwd(x: int, k: int) -> int:
    mask = (1 << k) - 1
    return (x ^ (x >> 1)) & mask

def gray_inv(x: int, k: int) -> int:
    y = x
    s = 1
    while s < k:
        y ^= (y >> s)
        s <<= 1
    return y & ((1 << k) - 1)

def gray_adj(x: int, k: int) -> int:
    # (G_k^T x)_i = x_i ^ x_{i-1} (with x_{-1} = 0)
    mask = (1 << k) - 1
    return (x ^ (x << 1)) & mask

def gray_adj_inv(x: int, k: int) -> int:
    mask = (1 << k) - 1
    y = x
    s = 1
    while s < k:
        y = (y ^ (y << s)) & mask
        s <<= 1
    return y

def bitrev_fwd(x: int, k: int) -> int:
    r = 0
    for i in range(k):
        if (x >> i) & 1:
            r |= 1 << (k - 1 - i)
    return r

def rotl1_fwd(x: int, k: int) -> int:
    # (C_k x)_i = x_{(i - 1) mod k}, i.e. cyclic left shift by 1 bit
    if k == 0:
        return 0
    mask = (1 << k) - 1
    return (((x << 1) | (x >> (k - 1))) & mask)

def rotr1_fwd(x: int, k: int) -> int:
    if k == 0:
        return 0
    mask = (1 << k) - 1
    return (((x >> 1) | ((x & 1) << (k - 1))) & mask)

def mat_mul(A, B):
    n = len(A)
    C = [[0] * n for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for t in range(n):
            v = Ai[t]
            if v:
                Bt = B[t]
                for j in range(n):
                    Ci[j] += v * Bt[j]
    return C

def mat_id(n: int):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]

def mat_smul(c: int, A):
    return [[c * v for v in row] for row in A]

def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A))] for i in range(len(A))]

def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A))] for i in range(len(A))]

def mat_trace(A) -> int:
    return sum(A[i][i] for i in range(len(A)))

def mat_pow(A, e: int):
    n = len(A)
    res = mat_id(n)
    base = A
    while e > 0:
        if e & 1:
            res = mat_mul(res, base)
        base = mat_mul(base, base)
        e >>= 1
    return res

def walsh_mat(k: int):
    n = 1 << k
    return [[sgn(vec_dot(i, j)) for j in range(n)] for i in range(n)]

def perm_mat(f, k: int):
    # P_f[i, j] = 1 iff f(j) == i
    n = 1 << k
    M = [[0] * n for _ in range(n)]
    for j in range(n):
        M[f(j, k)][j] = 1
    return M

def diag_phase_mat(a: int, k: int):
    n = 1 << k
    M = [[0] * n for _ in range(n)]
    for x in range(n):
        M[x][x] = sgn(vec_dot(a, x))
    return M

def trans_mat(b: int, k: int):
    return perm_mat(lambda x, _k: x ^ b, k)

def is_scalar_multiple_of_id(M) -> bool:
    n = len(M)
    c = M[0][0]
    for i in range(n):
        for j in range(n):
            if i == j:
                if M[i][j] != c:
                    return False
            else:
                if M[i][j] != 0:
                    return False
    return True


# =============================================================================
# 2. Exact k-bit F_2 matrix helpers for high-width checks (up to k = 32)
# =============================================================================

def lin_to_gf2_mat(f, k: int):
    # Column j is f(1 << j)
    M = [[0] * k for _ in range(k)]
    for j in range(k):
        y = f(1 << j, k)
        for i in range(k):
            M[i][j] = (y >> i) & 1
    return M

def gf2_mul(A, B):
    k = len(A)
    return [[sum(A[i][t] & B[t][j] for t in range(k)) & 1 for j in range(k)] for i in range(k)]

def gf2_pow(A, e: int):
    k = len(A)
    res = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    base = A
    while e > 0:
        if e & 1:
            res = gf2_mul(res, base)
        base = gf2_mul(base, base)
        e >>= 1
    return res

def gf2_nullity(M) -> int:
    k = len(M)
    A = [row[:] for row in M]
    rank = 0
    for col in range(k):
        piv = None
        for r in range(rank, k):
            if A[r][col]:
                piv = r
                break
        if piv is not None:
            A[rank], A[piv] = A[piv], A[rank]
            for r in range(k):
                if r != rank and A[r][col]:
                    for c in range(k):
                        A[r][c] ^= A[rank][c]
            rank += 1
    return k - rank

def gf2_id(k: int):
    return [[1 if i == j else 0 for j in range(k)] for i in range(k)]


# =============================================================================
# 3. Verification Suite
# =============================================================================

def verify_all():
    print("=" * 72)
    print("specmat-16 EXACT PURE-SILICON VERIFICATION SUITE")
    print("=" * 72)

    # -------------------------------------------------------------------------
    # Test 1: Theorem A — Gray-Walsh (k+1)-Cycle Collapse, Trace Law, Mod-4
    #         Antisymmetry, and Even-Width Half-Power Block-Gray Symplectic Law
    # -------------------------------------------------------------------------
    print("\n[1] Theorem A: Gray-Walsh (W_k * P_{G_k}) full 2^k x 2^k replay (k = 1..6)")
    for k in range(1, 7):
        W = walsh_mat(k)
        PG = perm_mat(gray_fwd, k)
        M = mat_mul(W, PG)
        n = 1 << k

        # (a) Periodicity: M^{2(k+1)} == 2^{k(k+1)} I
        M_per = mat_pow(M, 2 * (k + 1))
        assert M_per == mat_smul(1 << (k * (k + 1)), mat_id(n)), f"Period failed at k={k}"

        # (b) Sharpness for k >= 2: M^{2d} not a scalar multiple of I for 1 <= d < k+1
        if k >= 2:
            for d in range(1, k + 1):
                Md = mat_pow(M, 2 * d)
                assert not is_scalar_multiple_of_id(Md), f"Sharpness failed at k={k}, d={d}"
        else:
            # Boundary counterexample at k = 1: M^2 == 2 I
            assert mat_pow(M, 2) == mat_smul(2, mat_id(n))

        # (c) Exact even-power trace formula for m = 0..k+1
        for m in range(k + 2):
            tr = mat_trace(mat_pow(M, 2 * m))
            g = math.gcd(m, k + 1)
            q = (k + 1) // g
            exp = k * m + (g if (q % 2 == 0) else (g - 1))
            assert tr == (1 << exp), f"Even trace mismatch at k={k}, m={m}: {tr} != 2^{exp}"

        # (d) Mod-4 Weyl-Heisenberg anticommutation for k % 4 == 1
        if k % 4 == 1:
            b = sum((1 << i) for i in range(0, k, 2))
            a = gray_fwd(b, k)
            assert a == gray_adj(b, k) and vec_dot(b, a) == 1
            U = mat_mul(diag_phase_mat(a, k), trans_mat(b, k))
            assert mat_mul(U, U) == mat_smul(-1, mat_id(n))
            assert mat_mul(U, M) == mat_smul(-1, mat_mul(M, U))
            for m in range(k + 1):
                assert mat_trace(mat_pow(M, 2 * m + 1)) == 0
        else:
            # Sharpness: Tr(M) != 0 when k % 4 != 1
            assert mat_trace(M) != 0, f"Expected nonzero trace at k={k}"

        # (e) Even-width half-power block-Gray symplectic law: k = 2r
        if k % 2 == 0:
            r = k // 2
            def block_gray(x, _k, r=r):
                lo = x & ((1 << r) - 1)
                hi = x >> r
                new_lo = gray_fwd(hi, r)
                new_hi = gray_adj(lo, r)
                return new_lo | (new_hi << r)
            M_half = mat_pow(M, k + 1)
            rhs = mat_smul(1 << (2 * r * r), mat_mul(W, perm_mat(block_gray, k)))
            assert M_half == rhs, f"Half-power block-Gray failed at k={k}"
            assert mat_trace(M_half) == (1 << (2 * r * r + 2 * r))

        print(f"    k={k} (dim {n:2d}x{n:2d}): period 2({k+1})={2*(k+1)}, "
              f"Tr(M)={mat_trace(M):4d}, ALL checks PASSED")

    # High-width F_2 certificate replay for Theorem A (k = 1..30)
    print("    High-width F_2 defect replay (k = 1..30)...", end=" ")
    for k in range(1, 31):
        delta = lambda x, kk=k: gray_adj_inv(gray_fwd(x, kk), kk)
        D = lin_to_gf2_mat(delta, k)
        I = gf2_id(k)
        assert gf2_pow(D, k + 1) == I
        if k >= 2:
            for d in range(1, k + 1):
                assert gf2_pow(D, d) != I
        # Check exact nullity for all m = 1..k+1
        for m in range(1, k + 2):
            Dm = gf2_pow(D, m)
            Mdiff = [[Dm[i][j] ^ I[i][j] for j in range(k)] for i in range(k)]
            nul = gf2_nullity(Mdiff)
            g = math.gcd(m, k + 1)
            q = (k + 1) // g
            expected = g if (q % 2 == 0) else (g - 1)
            assert nul == expected
    print("PASSED (all k = 1..30)")

    # -------------------------------------------------------------------------
    # Test 2: Theorem B — Gray / Inverse-Gray Walsh Similarity via P_{R_k} W_k
    # -------------------------------------------------------------------------
    print("\n[2] Theorem B: Gray / Inverse-Gray Walsh Similarity (k = 1..6)")
    for k in range(1, 7):
        W = walsh_mat(k)
        PR = perm_mat(bitrev_fwd, k)
        S = mat_mul(PR, W)
        MG = mat_mul(W, perm_mat(gray_fwd, k))
        MGinv = mat_mul(W, perm_mat(gray_inv, k))
        n = 1 << k
        assert mat_mul(S, S) == mat_smul(1 << k, mat_id(n))
        assert mat_mul(S, MG) == mat_mul(MGinv, S)
        for m in range(1, 2 * (k + 1) + 1):
            assert mat_trace(mat_pow(MG, m)) == mat_trace(mat_pow(MGinv, m))
        print(f"    k={k}: (P_R W) (W P_G) == (W P_{{G^-1}}) (P_R W), all power traces match")

    # -------------------------------------------------------------------------
    # Test 3: Theorem C — Bit-Reversal vs. Gray o Bit-Reversal Parity Dichotomy
    # -------------------------------------------------------------------------
    print("\n[3] Theorem C: Bit-Reversal vs. Gray o Bit-Reversal Dichotomy (k = 1..6)")
    for k in range(1, 7):
        W = walsh_mat(k)
        n = 1 << k
        M_R = mat_mul(W, perm_mat(bitrev_fwd, k))
        M_GR = mat_mul(W, perm_mat(lambda x, kk: gray_fwd(bitrev_fwd(x, kk), kk), k))

        assert mat_mul(M_R, M_R) == mat_smul(n, mat_id(n))
        assert mat_mul(M_GR, M_GR) == mat_smul(n, mat_id(n))

        tr_R = mat_trace(M_R)
        tr_GR = mat_trace(M_GR)
        assert tr_GR == 0

        if k % 2 == 1:
            assert tr_R == 0
            status = f"odd k: both balanced (Tr=0)"
        else:
            r = k // 2
            assert tr_R == n
            # Check exact integer projectors Pi_+ and Pi_-
            scale = 1 << r
            Pi_p_R = mat_add(mat_smul(scale, mat_id(n)), M_R)
            Pi_m_R = mat_sub(mat_smul(scale, mat_id(n)), M_R)
            assert mat_mul(Pi_p_R, Pi_m_R) == [[0]*n for _ in range(n)]
            m_plus_R = mat_trace(Pi_p_R) // (2 * scale)
            m_minus_R = mat_trace(Pi_m_R) // (2 * scale)
            assert m_plus_R == (1 << (k - 1)) + (1 << (r - 1))
            assert m_minus_R == (1 << (k - 1)) - (1 << (r - 1))

            Pi_p_GR = mat_add(mat_smul(scale, mat_id(n)), M_GR)
            Pi_m_GR = mat_sub(mat_smul(scale, mat_id(n)), M_GR)
            m_plus_GR = mat_trace(Pi_p_GR) // (2 * scale)
            m_minus_GR = mat_trace(Pi_m_GR) // (2 * scale)
            assert m_plus_GR == (1 << (k - 1)) and m_minus_GR == (1 << (k - 1))
            status = (f"even k: W*P_R has (m+, m-)=({m_plus_R}, {m_minus_R}) [asym {1<<r}], "
                      f"W*P_{{GR}} has ({m_plus_GR}, {m_minus_GR}) [balanced]")
        print(f"    k={k}: {status}")

    # -------------------------------------------------------------------------
    # Test 4: Theorem D — Gray o Cyclic Butterfly Rotation (2k-Cycle Collapse)
    # -------------------------------------------------------------------------
    print("\n[4] Theorem D: Gray o Butterfly-Rotation (W_k * P_{G_k C_k}) (k = 1..6)")
    for k in range(1, 7):
        W = walsh_mat(k)
        n = 1 << k
        gc = lambda x, kk: gray_fwd(rotl1_fwd(x, kk), kk)
        M = mat_mul(W, perm_mat(gc, k))

        if k >= 2:
            assert mat_pow(M, 2 * k) == mat_smul(1 << (k * k), mat_id(n))
        if k >= 3:
            for d in range(1, k):
                assert not is_scalar_multiple_of_id(mat_pow(M, 2 * d))
        else:
            # Boundary counterexample at k = 2: M^2 == 4 I (period 2 < 2*2)
            assert mat_pow(M, 2) == mat_smul(n, mat_id(n))

        if k >= 2:
            for m in range(k + 1):
                tr = mat_trace(mat_pow(M, 2 * m))
                g = math.gcd(m, k)
                q = k // g
                exp = k * m + (g + 1 if (q % 2 == 0) else g)
                assert tr == (1 << exp), f"GC trace mismatch at k={k}, m={m}"
        print(f"    k={k} (dim {n:2d}x{n:2d}): period={2*k if k>=3 else 2}, ALL checks PASSED")

    # High-width F_2 replay for Theorem D (k = 2..30)
    print("    High-width F_2 defect replay for G_k C_k (k = 2..30)...", end=" ")
    for k in range(2, 31):
        # (G_k C_k)^{-T} (G_k C_k) = G_k^{-T} C_k G_k C_k
        delta = lambda x, kk=k: gray_adj_inv(rotl1_fwd(gray_fwd(rotl1_fwd(x, kk), kk), kk), kk)
        D = lin_to_gf2_mat(delta, k)
        I = gf2_id(k)
        assert gf2_pow(D, k) == I
        if k >= 3:
            for d in range(1, k):
                assert gf2_pow(D, d) != I
        for m in range(1, k + 1):
            Dm = gf2_pow(D, m)
            Mdiff = [[Dm[i][j] ^ I[i][j] for j in range(k)] for i in range(k)]
            nul = gf2_nullity(Mdiff)
            g = math.gcd(m, k)
            q = k // g
            expected = (g + 1) if (q % 2 == 0) else g
            assert nul == expected
    print("PASSED (all k = 2..30)")

    # -------------------------------------------------------------------------
    # Test 5: Sharpness Counterexamples (where relaxing hypotheses breaks laws)
    # -------------------------------------------------------------------------
    print("\n[5] Sharpness & Falsification Counterexamples")
    # (5a) Nonlinear carry-increment permutation breaks Walsh-defect squaring!
    W2 = walsh_mat(2)
    P_inc2 = perm_mat(lambda x, kk: (x + 1) & ((1 << kk) - 1), 2)
    M_inc2 = mat_mul(W2, P_inc2)
    M_inc2_sq = mat_mul(M_inc2, M_inc2)
    # Already at k=2, (W_2 P_inc)^2 has negative entry -4 (so NOT 2^2 * P_sigma)!
    assert M_inc2_sq[1][0] == -4
    print(f"    (5a-i) Nonlinear inc mod 4 (k=2): (W_2 P_inc)^2[1,0] = {M_inc2_sq[1][0]} "
          f"(negative! NOT 2^2 P_sigma; F_2-linearity is SHARP.)")
    # At k=3, (W_3 P_inc)^2 is not even monomial (bit 2 receives carry x_0 & x_1, so row 4 splits)!
    W3 = walsh_mat(3)
    P_inc3 = perm_mat(lambda x, kk: (x + 1) & ((1 << kk) - 1), 3)
    M_inc3 = mat_mul(W3, P_inc3)
    M_inc3_sq = mat_mul(M_inc3, M_inc3)
    nz_row4 = [v for v in M_inc3_sq[4] if v != 0]
    assert len(nz_row4) > 1, f"Row 4 was monomial: {M_inc3_sq[4]}"
    print(f"    (5a-ii) Nonlinear inc mod 8 (k=3): (W_3 P_inc)^2 row 4 = {M_inc3_sq[4]} "
          f"({len(nz_row4)} nonzeros! Not even monomial.)")

    # (5b) Boundary k=1 for Gray-Walsh sharpness
    print(f"    (5b) Gray-Walsh k=1 boundary: (W_1 P_{{G_1}})^2 = 2*I (period 2 < 2(1+1)=4; k>=2 is SHARP.)")

    # (5c) Boundary k=2 for Gray o Rot sharpness
    print(f"    (5c) Gray o Rot k=2 boundary: (W_2 P_{{G_2 C_2}})^2 = 4*I (period 2 < 2*2=4; k>=3 is SHARP.)")

    # (5d) Mod-4 antisymmetry sharpness
    for kk in (2, 3, 4):
        tr = mat_trace(mat_mul(walsh_mat(kk), perm_mat(gray_fwd, kk)))
        print(f"    (5d) Gray-Walsh k={kk} (k mod 4 = {kk%4}): Tr(W_{kk} P_{{G_{kk}}}) = {tr} != 0 (k=1 mod 4 is SHARP.)")

    # (5e) Even-width bit-reversal asymmetry sharpness
    print(f"    (5e) Bit-Reversal k=2: Tr(W_2 P_{{R_2}}) = {mat_trace(mat_mul(W2, perm_mat(bitrev_fwd, 2)))} != 0 "
          f"(odd k balance is SHARP.)")

    print("\nALL EXACT REPLAYS AND SHARPNESS COUNTEREXAMPLES PASSED WITH ZERO FLOATS.")


if __name__ == "__main__":
    verify_all()
