"""
Exact Pure-Silicon Verification & Sharpness Counterexample Suite for:
  Exact Smith Normal Form (SNF) Bit-Slice Lifting Mechanism (specmat-5)

Strictly pure Python arbitrary-precision `int` arithmetic (standard library only, exact integers).
Independently verifies:
  1. Exact Smith Normal Form diagonals + explicit unimodular certificates U * M * V = diag(d)
     for all four infinite theorem families proved in Proof.lean.
  2. Exact bit-slice block elimination identities (LSB coupled-state, MSB divisibility
     Block-Schur, upper-bidiagonal Delta, additive rank-1, Kronecker) up to k = 6 (64 x 64).
  3. Explicit sharpness counterexamples showing where every hypothesis is strictly necessary.
"""

from collections import Counter
from math import comb, gcd, lcm


# ============================================================================
# Pure-Integer Exact SNF Solver & Matrix Verification Utilities
# ============================================================================

def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def transpose(A):
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]


def block2(A, B, C, D):
    m = len(A)
    return [A[i] + B[i] for i in range(m)] + [C[i] + D[i] for i in range(m)]


def lsb_perm_mat(k):
    n = 1 << k
    half = 1 << (k - 1)
    P = [[0] * n for _ in range(n)]
    for b in range(2):
        for q in range(half):
            P[b * half + q][2 * q + b] = 1
    return P


def snf_with_cert(mat):
    """Exact Smith Normal Form over Z returning (diag, U, V) with U * mat * V == diag(d)
    and exact divisibility chain d[0] | d[1] | ... | d[n-1]. Pure Python int only."""
    n = len(mat)
    A = [list(map(int, row)) for row in mat]
    U = eye(n)
    V = eye(n)
    diag = []

    def swap_rows(r1, r2):
        A[r1], A[r2] = A[r2], A[r1]
        U[r1], U[r2] = U[r2], U[r1]

    def swap_cols(c1, c2):
        for i in range(n):
            A[i][c1], A[i][c2] = A[i][c2], A[i][c1]
            V[i][c1], V[i][c2] = V[i][c2], V[i][c1]

    def neg_row(r):
        A[r] = [-x for x in A[r]]
        U[r] = [-x for x in U[r]]

    def add_mul_row(dst, src, factor):
        for j in range(n):
            A[dst][j] += factor * A[src][j]
            U[dst][j] += factor * U[src][j]

    def add_mul_col(dst, src, factor):
        for i in range(n):
            A[i][dst] += factor * A[i][src]
            V[i][dst] += factor * V[i][src]

    for k in range(n):
        while True:
            best = None
            bi = bj = -1
            for i in range(k, n):
                row = A[i]
                for j in range(k, n):
                    v = abs(row[j])
                    if v != 0 and (best is None or v < best):
                        best = v
                        bi, bj = i, j
            if best is None:
                diag.extend([0] * (n - k))
                return diag, U, V
            if bi != k:
                swap_rows(k, bi)
            if bj != k:
                swap_cols(k, bj)
            if A[k][k] < 0:
                neg_row(k)
            pivot = A[k][k]
            changed = False
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    q = A[i][k] // pivot
                    if q != 0:
                        add_mul_row(i, k, -q)
                    if A[i][k] != 0:
                        changed = True
            if changed:
                continue
            for j in range(k + 1, n):
                if A[k][j] != 0:
                    q = A[k][j] // pivot
                    if q != 0:
                        add_mul_col(j, k, -q)
                    if A[k][j] != 0:
                        changed = True
            if changed:
                continue
            bad = None
            for i in range(k + 1, n):
                for j in range(k + 1, n):
                    if A[i][j] % pivot != 0:
                        bad = (i, j)
                        break
                if bad is not None:
                    break
            if bad is not None:
                add_mul_row(k, bad[0], 1)
                continue
            diag.append(pivot)
            break
    return diag, U, V


def verify_snf_cert(M, expected_diag, check_cert=True):
    d, U, V = snf_with_cert(M)
    assert d == expected_diag, f"SNF mismatch:\n  got:      {d}\n  expected: {expected_diag}"
    # Verify canonical divisibility chain
    for i in range(len(d) - 1):
        assert d[i] >= 0
        if d[i] == 0:
            assert d[i + 1] == 0
        else:
            assert d[i + 1] % d[i] == 0
    if check_cert:
        n = len(M)
        D = [[d[i] if i == j else 0 for j in range(n)] for i in range(n)]
        assert mat_mul(mat_mul(U, M), V) == D, "U * M * V != diag(d)"
    return d


def fmt_multiset(d):
    c = Counter(d)
    items = sorted((v, cnt) for v, cnt in c.items() if v != 0)
    if 0 in c:
        items.append((0, c[0]))
    return items


# ============================================================================
# Bitwise Primitives
# ============================================================================

def popcount(x):
    return x.bit_count()


def carries_k(k, x, y, cin=0):
    c = cin
    cnt = 0
    for _ in range(k):
        s = (x & 1) + (y & 1) + c
        c = s >> 1
        cnt += c
        x >>= 1
        y >>= 1
    return cnt


def add_xor_snf_diag(i):
    if i == 0:
        return 1
    return 1 << (i.bit_length() + 1)  # 2^(floor(log2 i) + 2)


# ============================================================================
# Verification Suites
# ============================================================================

def verify_theorem_1():
    print("=== Theorem 1: Carry-Parity, Carry-Coupling Unimodularity, Dichotomy & Affine Family ===")
    # 1a. Kummer's identity for all k <= 5
    for k in range(0, 6):
        n = 1 << k
        for x in range(n):
            for y in range(n):
                for c in (0, 1):
                    lhs = carries_k(k, x, y, c) + popcount(x + y + c)
                    rhs = popcount(x) + popcount(y) + c
                    assert lhs == rhs
    print("  [OK] Kummer carry identity verified exhaustively for k = 0..5.")

    # 1b. Exact SNF of C_k^(0), C_k^(1), S_k, carrySignMat for k = 1..5
    for k in range(1, 6):
        n = 1 << k
        C0 = [[carries_k(k, x, y, 0) & 1 for y in range(n)] for x in range(n)]
        C1 = [[carries_k(k, x, y, 1) & 1 for y in range(n)] for x in range(n)]
        S  = [[C0[x][y] + C1[x][y] - 1 for y in range(n)] for x in range(n)]
        H  = [[1 if (carries_k(k, x, y, 0) & 1) == 0 else -1 for y in range(n)] for x in range(n)]

        verify_snf_cert(S, [1] * n, check_cert=(k <= 4))
        verify_snf_cert(C0, [1] * (n - 1) + [0], check_cert=(k <= 4))
        exp_C1 = [1] * n if (k % 2 == 1) else [1] * (n - 1) + [0]
        verify_snf_cert(C1, exp_C1, check_cert=(k <= 4))
        verify_snf_cert(H, [1] + [2] * (n - 1), check_cert=(k <= 4))
        print(f"  [OK] k={k} (n={n:2d}): S_k unimodular, C0=(1^{n-1},0), "
              f"C1={'unimodular' if k%2==1 else f'(1^{n-1},0)'}, H_carry=(1,2^{n-1})")

    # 1c. Two-parameter affine family M_k(a, b) = a + b * C_k^(0) across diverse (a, b)
    test_params = [(0, 0), (0, 1), (0, -7), (5, 0), (1, -2), (3, 5), (-6, 4), (12, 18), (-9, -15)]
    for k in range(1, 5):
        n = 1 << k
        for a, b in test_params:
            M = [[a + b * (carries_k(k, x, y, 0) & 1) for y in range(n)] for x in range(n)]
            g = gcd(abs(a), abs(b))
            L = lcm(abs(a), abs(b))
            exp = [g] + [abs(b)] * (n - 2) + [L]
            verify_snf_cert(M, exp, check_cert=(k <= 3))
    print(f"  [OK] Affine family M_k(a,b) verified for k=1..4 across {len(test_params)} (a,b) pairs.")

    # 1d. LSB block-triangular identity up to k = 6 (64 x 64)
    for k in range(1, 7):
        n = 1 << k
        half = 1 << (k - 1)
        C0 = [[carries_k(k, x, y, 0) & 1 for y in range(n)] for x in range(n)]
        C1 = [[carries_k(k, x, y, 1) & 1 for y in range(n)] for x in range(n)]
        S  = [[C0[x][y] + C1[x][y] - 1 for y in range(n)] for x in range(n)]
        C0p = [[carries_k(k - 1, x, y, 0) & 1 for y in range(half)] for x in range(half)]
        C1p = [[carries_k(k - 1, x, y, 1) & 1 for y in range(half)] for x in range(half)]
        Sp  = [[C0p[x][y] + C1p[x][y] - 1 for y in range(half)] for x in range(half)]
        Rp  = [[C1p[x][y] - C0p[x][y] for y in range(half)] for x in range(half)]
        P = lsb_perm_mat(k)
        Pt = transpose(P)
        I = eye(half)
        Z = [[0] * half for _ in range(half)]
        E = block2(I, Z, [[-I[i][j] for j in range(half)] for i in range(half)], I)
        lhs = mat_mul(mat_mul(E, mat_mul(mat_mul(P, S), Pt)), E)
        rhs = block2(Sp, [[-Rp[i][j] for j in range(half)] for i in range(half)],
                     Z,  [[-Sp[i][j] for j in range(half)] for i in range(half)])
        assert lhs == rhs
    print("  [OK] LSB coupled-state block-triangular identity E * P * S_k * P^T * E = [[S,-R],[0,-S]] verified up to k=6 (64x64).")


def verify_theorem_2():
    print("\n=== Theorem 2: Add-XOR Carry-Difference D_k, T_k^(1), and Half-Rank Truncation Collapse ===")
    for k in range(1, 6):
        n = 1 << k
        half = 1 << (k - 1)
        mask = n - 1
        T1  = [[(x + y + 1) ^ x for y in range(n)] for x in range(n)]
        D   = [[((x + y + 1) ^ x) - ((x + y) ^ x) for y in range(n)] for x in range(n)]
        T1m = [[((x + y + 1) ^ x) & mask for y in range(n)] for x in range(n)]
        Dm  = [[(((x + y + 1) ^ x) & mask) - (((x + y) ^ x) & mask) for y in range(n)] for x in range(n)]

        exp_full = [add_xor_snf_diag(i) for i in range(n)]
        exp_mod  = [add_xor_snf_diag(i) for i in range(half)] + [0] * half

        verify_snf_cert(D,   exp_full, check_cert=(k <= 4))
        verify_snf_cert(T1,  exp_full, check_cert=(k <= 4))
        verify_snf_cert(Dm,  exp_mod,  check_cert=(k <= 4))
        verify_snf_cert(T1m, exp_mod,  check_cert=(k <= 4))
        print(f"  [OK] k={k} (n={n:2d}): SNF(D_k)=SNF(T1_k)={fmt_multiset(exp_full)} | "
              f"SNF(D_mod)=SNF(T1_mod)={fmt_multiset(exp_mod)}")

    # Verify MSB block decomposition + Delta identity up to k = 6 (64 x 64)
    for k in range(1, 7):
        n = 1 << k
        half = 1 << (k - 1)
        mask = n - 1
        T1 = [[(x + y + 1) ^ x for y in range(n)] for x in range(n)]
        D  = [[((x + y + 1) ^ x) - ((x + y) ^ x) for y in range(n)] for x in range(n)]
        Dp = [[((x + y + 1) ^ x) - ((x + y) ^ x) for y in range(half)] for x in range(half)]
        Dm = [[(((x + y + 1) ^ x) & mask) - (((x + y) ^ x) & mask) for y in range(n)] for x in range(n)]
        Delta = [[1 if i == j else (-1 if i + 1 == j else 0) for j in range(n)] for i in range(n)]
        assert mat_mul(T1, Delta) == D
        Pa = [[1 if x + y == half - 1 else 0 for y in range(half)] for x in range(half)]
        B10 = [[Dp[x][y] + 2 * half * Pa[x][y] for y in range(half)] for x in range(half)]
        B11 = [[Dp[x][y] - 2 * half * Pa[x][y] for y in range(half)] for x in range(half)]
        assert D == block2(Dp, Dp, B10, B11)
        assert Dm == block2(Dp, B11, Dp, B11)
    print("  [OK] MSB Divisibility Block-Schur & Delta identities verified up to k=6 (64x64).")


def verify_theorem_3():
    print("\n=== Theorem 3: Divisibility-Weighted Bitwise-AND Additive SNF Family ===")
    for k in range(1, 6):
        n = 1 << k
        M_pop = [[popcount(x & y) for y in range(n)] for x in range(n)]
        M_and = [[x & y for y in range(n)] for x in range(n)]
        verify_snf_cert(M_pop, [1] * k + [0] * (n - k), check_cert=(k <= 4))
        verify_snf_cert(M_and, [1 << i for i in range(k)] + [0] * (n - k), check_cert=(k <= 4))
        # General divisibility chain w = (2, 6, 12, 60, 120)
        weights = [2, 6, 12, 60, 120][:k]
        M_w = [[sum(weights[r] for r in range(k) if ((x & y) >> r) & 1) for y in range(n)] for x in range(n)]
        verify_snf_cert(M_w, weights + [0] * (n - k), check_cert=(k <= 4))
        print(f"  [OK] k={k} (n={n:2d}): popcount(x&y)=(1^{k},0^{n-k}), "
              f"x&y=({[1<<i for i in range(k)]},0^{n-k}), weighted({weights}) exact.")


def verify_theorem_4():
    print("\n=== Theorem 4: Kronecker Bit-Slice SNF for q^popcount(x & y) ===")
    for k in range(1, 5):
        n = 1 << k
        for q in (-2, -1, 0, 1, 2, 3, 4):
            M = [[q ** popcount(x & y) for y in range(n)] for x in range(n)]
            if q == 1:
                exp = [1] + [0] * (n - 1)
            else:
                exp = []
                m = abs(q - 1)
                for j in range(k + 1):
                    exp.extend([m ** j] * comb(k, j))
            verify_snf_cert(M, exp, check_cert=(k <= 3))
        print(f"  [OK] k={k} (n={n:2d}): q^popcount(x&y) exact for q in {{-2,-1,0,1,2,3,4}} "
              f"(q=2 unimodular, q=-1 Walsh-Hadamard binomial SNF).")


def verify_sharpness_counterexamples():
    print("\n=== Sharpness & Falsification Counterexamples ===")
    # 1. Modulus sharpness: carries(x, y) mod 3 breaks unimodularity of nonzero block at k = 2
    M_mod3 = [[carries_k(2, x, y, 0) % 3 for y in range(4)] for x in range(4)]
    d_mod3, _, _ = snf_with_cert(M_mod3)
    assert d_mod3 == [1, 1, 3, 0]
    print(f"  [CE1] carries(x,y) mod 3 at k=2 has SNF {d_mod3} != [1, 1, 1, 0] (torsion 3 appears!).")

    # 2. Untruncated carries(x, y) at k = 2, 3, 4 develops LCM of Mersenne numbers 3, 21, 105
    for k, exp_last in [(2, 3), (3, 21), (4, 105)]:
        n = 1 << k
        M_car = [[carries_k(k, x, y, 0) for y in range(n)] for x in range(n)]
        d_car, _, _ = snf_with_cert(M_car)
        assert d_car[-2] == exp_last and d_car[-1] == 0
        print(f"  [CE2] untruncated carries(x,y) at k={k} has max nonzero invariant factor {d_car[-2]} (SNF={fmt_multiset(d_car)}).")

    # 3. Carry-in parity dichotomy: C_2^(1) is singular (corank 1), C_3^(1) is unimodular
    C1_2 = [[carries_k(2, x, y, 1) & 1 for y in range(4)] for x in range(4)]
    d_c1_2, _, _ = snf_with_cert(C1_2)
    assert d_c1_2 == [1, 1, 1, 0]
    print(f"  [CE3] C_2^(1) (even k=2) has SNF {d_c1_2} (singular!), whereas C_1^(1), C_3^(1), C_5^(1) are unimodular.")

    # 4. Divisibility Block-Schur sharpness: A=diag(1,4), C=2*I_2 (4 does not divide 2!), E=0
    M_nondiv = [
        [1, 0, 0, 0],
        [0, 4, 0, 0],
        [2, 0, 0, 0],
        [0, 2, 0, 0],
    ]
    d_nondiv, _, _ = snf_with_cert(M_nondiv)
    assert d_nondiv == [1, 2, 0, 0]
    print(f"  [CE4] Non-divisible Block-Schur [[diag(1,4),0],[2I,0]] has SNF {d_nondiv} != [1, 4, 0, 0].")

    # 5. Non-divisibility-chain weights w = (2, 3) on weightedAndMat
    M_w23 = [[(2 if (x & y) & 1 else 0) + (3 if ((x & y) >> 1) & 1 else 0) for y in range(4)] for x in range(4)]
    d_w23, _, _ = snf_with_cert(M_w23)
    assert d_w23 == [1, 6, 0, 0]
    print(f"  [CE5] Non-chain weights w=(2,3) on weightedAndMat has SNF {d_w23} != [2, 3, 0, 0] (Bezout merges to [1,6]).")


if __name__ == "__main__":
    verify_theorem_1()
    verify_theorem_2()
    verify_theorem_3()
    verify_theorem_4()
    verify_sharpness_counterexamples()
    print("\nALL EXACT INTEGER SNF & SHARPNESS CHECKS PASSED (ZERO FLOATS).")
