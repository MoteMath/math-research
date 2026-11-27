"""
explore_and_verify.py — Pure-Silicon Exact Integer Replay & Certificate Verifier
for Task 7 (2-Regular Sequence Linear-Representation Proof Engine).

ZERO floating-point arithmetic anywhere (exact Python `int` and `fractions.Fraction` only).
Independently verifies:
  1. All 8 finite integer certificates (IdentityCert, IntertwineCert, ModCert, ConeCert, ConePosCert),
     including hostile mutation rejection checks.
  2. All 5 infinite theorems on native bitwise functions across n = 0..65536 (and parametric q).
  3. Infinite extremal sharpness families (exact zero-slack and +1-slack sequences) up to n > 10^7.
  4. Boundary counterexamples proving every hypothesis and constant is sharp.
"""

from fractions import Fraction
import sys


# ============================================================================
# 1. Native Pure-Silicon Bitwise Operations (exact Python int)
# ============================================================================

def gray(n: int) -> int:
    return n ^ (n >> 1)


def popcount(n: int) -> int:
    return n.bit_count()


def high_bit(n: int) -> int:
    return 0 if n == 0 else (1 << (n.bit_length() - 1))


def dq(q: int, n: int) -> int:
    """Base-q Gray-vs-Binary bitwise defect: sum_{i >= 0} (g_i - b_i) * q^i."""
    if n == 0:
        return 0
    val = 0
    pw = 1
    x = n
    while x > 0:
        b = x & 1
        nb = (x >> 1) & 1
        g = b ^ nb
        val += (g - b) * pw
        pw *= q
        x >>= 1
    return val


def q_dyadic(n: int) -> int:
    h = high_bit(n)
    return (n - h) * (2 * h - n)


# ============================================================================
# 2. Exact Integer Matrix & Linear Representation Engine
# ============================================================================

def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def matvec(M, v):
    return [dot(row, v) for row in M]


def matmul(A, B):
    n = len(B[0])
    k = len(B)
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(n)] for i in range(len(A))]


def matT(M):
    return [[M[i][j] for i in range(len(M))] for j in range(len(M[0]))]


def mat_scale(c, M):
    return [[c * x for x in row] for row in M]


def vec_scale(c, v):
    return [c * x for x in v]


def kron_mat(A, B):
    """Kronecker product matching Lean `kronMat` indexing (k = j * d1 + i)."""
    d1, d2 = len(A), len(B)
    N = d1 * d2
    return [
        [A[r % d1][c % d1] * B[r // d1][c // d1] for c in range(N)]
        for r in range(N)
    ]


def kron_vec(u, v):
    d1, d2 = len(u), len(v)
    return [u[k % d1] * v[k // d1] for k in range(d1 * d2)]


def eval_linrep(u, M0, M1, v, n: int) -> int:
    """Evaluate f(n) = u^T * M_{b_0} * ... * M_{b_k} * v (LSB-first)."""
    assert matvec(M0, v) == v, "Leading-zero stability M0 * v = v violated"
    bits = []
    x = n
    while x > 0:
        bits.append(x & 1)
        x >>= 1
    state = list(v)
    for b in reversed(bits):
        state = matvec(M1 if b else M0, state)
    return dot(u, state)


# Pure-data certificate verifiers (mirroring Lean 4 checkers)
def check_identity_cert(u, M0, M1, v, K, C0, C1, c, alpha, beta) -> bool:
    if alpha == 0 or beta == 0:
        return False
    if matvec(K, v) != [0] * len(K):
        return False
    if mat_scale(beta, matmul(K, M0)) != matmul(C0, K):
        return False
    if mat_scale(beta, matmul(K, M1)) != matmul(C1, K):
        return False
    if vec_scale(alpha, u) != matvec(matT(K), c):
        return False
    return True


def check_intertwine_cert(u1, A0, A1, v1, u2, B0, B1, v2, T) -> bool:
    return (
        matvec(T, v1) == v2
        and matmul(T, A0) == matmul(B0, T)
        and matmul(T, A1) == matmul(B1, T)
        and matvec(matT(T), u2) == u1
    )


def check_mod_cert(u, M0, M1, v, K, C0, C1, c, m) -> bool:
    if m <= 0:
        return False
    if any(x % m != 0 for x in matvec(K, v)):
        return False
    L0, R0 = matmul(K, M0), matmul(C0, K)
    L1, R1 = matmul(K, M1), matmul(C1, K)
    if any((L0[i][j] - R0[i][j]) % m != 0 for i in range(len(K)) for j in range(len(v))):
        return False
    if any((L1[i][j] - R1[i][j]) % m != 0 for i in range(len(K)) for j in range(len(v))):
        return False
    cov = matvec(matT(K), c)
    if any((u[j] - cov[j]) % m != 0 for j in range(len(u))):
        return False
    return True


def check_cone_cert(u, M0, M1, v, P, C0, C1, c, alpha, beta, pos_only=False) -> bool:
    if alpha <= 0 or beta <= 0:
        return False
    if any(x < 0 for row in C0 for x in row):
        return False
    if any(x < 0 for row in C1 for x in row):
        return False
    if any(x < 0 for x in c):
        return False
    v_init = matvec(M1, v) if pos_only else v
    if any(x < 0 for x in matvec(P, v_init)):
        return False
    if mat_scale(beta, matmul(P, M0)) != matmul(C0, P):
        return False
    if mat_scale(beta, matmul(P, M1)) != matmul(C1, P):
        return False
    if vec_scale(alpha, u) != matvec(matT(P), c):
        return False
    return True


def sub_rep(u1, A0, A1, v1, u2, B0, B1, v2):
    d1, d2 = len(v1), len(v2)
    u = u1 + [-x for x in u2]
    M0 = [A0[i] + [0] * d2 for i in range(d1)] + [[0] * d1 + B0[i] for i in range(d2)]
    M1 = [A1[i] + [0] * d2 for i in range(d1)] + [[0] * d1 + B1[i] for i in range(d2)]
    v = v1 + v2
    return u, M0, M1, v


# ============================================================================
# 3. Verify All 8 Finite Certificates + Hostile Mutation Rejection Tests
# ============================================================================

def verify_all_certificates():
    print("=== [1] Verifying All 8 Finite Integer Certificates ===")

    # Helper SqRep(q)
    def sq_rep(q):
        u = [1, 0, 0, 0]
        M0 = [[2 * q, 0, 0, 0], [0, q, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
        M1 = [[2 * q, q, 1, 0], [0, q, -1, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
        v = [0, 0, 0, 1]
        return u, M0, M1, v

    # Cert 1: Parametric ConeCert for S_q(q, n) >= 0 (checked for q = 0..10)
    for q in range(0, 11):
        u, M0, M1, v = sq_rep(q)
        P = [[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        C0 = [[2 * q, 0, 0, 0], [q, q, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
        C1 = [[q, q, 1, 0], [0, 2 * q, 0, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
        c = [1, 0, 0, 0]
        assert check_cone_cert(u, M0, M1, v, P, C0, C1, c, 1, 1, pos_only=False)
    # Hostile mutation: q = -1 fails cone nonnegativity!
    u_m, M0_m, M1_m, v_m = sq_rep(-1)
    P_m = [[1, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
    C0_m = [[-2, 0, 0, 0], [-1, -1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
    C1_m = [[-1, -1, 1, 0], [0, -2, 0, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
    assert not check_cone_cert(u_m, M0_m, M1_m, v_m, P_m, C0_m, C1_m, [1, 0, 0, 0], 1, 1)
    print("  [PASS] Cert 1 (ConeCert, 4 rows, alpha=1, beta=1): S_q(q, n) >= 0 for q in 0..10 (q=-1 rejected)")

    # Cert 2: 6-row ConePosCert (alpha=1, beta=2) for 5*W_G(n) <= 2n - 2 + (n % 2)
    u_wg = [-5, 0, 1, -2, 2]
    M0_wg = [[2, 0, 0, 0, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2]]
    M1_wg = [[2, 1, 1, 0, 0], [0, 1, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 2]]
    v_wg = [0, 0, 0, 1, 0]
    P_wg = [
        [0, 0, 1, 0, 0],
        [0, 0, -1, 1, 0],
        [-5, -5, -1, 1, 2],
        [-5, -3, -1, -1, 2],
        [-5, -1, 0, -2, 2],
        [-5, 0, 1, -2, 2],
    ]
    C0_wg = [
        [0, 0, 0, 0, 0, 0],
        [2, 2, 0, 0, 0, 0],
        [0, 7, 0, 3, 1, 0],
        [0, 5, 0, 1, 3, 0],
        [0, 4, 0, 0, 2, 2],
        [0, 4, 0, 0, 0, 4],
    ]
    C1_wg = [
        [2, 2, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0],
        [4, 0, 4, 0, 0, 0],
        [0, 0, 2, 2, 0, 0],
        [0, 4, 0, 4, 0, 0],
        [0, 7, 0, 3, 1, 0],
    ]
    c_wg = [0, 0, 0, 0, 0, 1]
    assert check_cone_cert(u_wg, M0_wg, M1_wg, v_wg, P_wg, C0_wg, C1_wg, c_wg, 1, 2, pos_only=True)
    # Hostile mutations: tightened target (-2 -> -3) and corrupted C0[2][1] (7 -> 6)
    assert not check_cone_cert([-5, 0, 1, -3, 2], M0_wg, M1_wg, v_wg, P_wg, C0_wg, C1_wg, c_wg, 1, 2, pos_only=True)
    C0_bad = [row[:] for row in C0_wg]
    C0_bad[2][1] = 6
    assert not check_cone_cert(u_wg, M0_wg, M1_wg, v_wg, P_wg, C0_bad, C1_wg, c_wg, 1, 2, pos_only=True)
    print("  [PASS] Cert 2 (ConePosCert, 6 rows, alpha=1, beta=2): 5*W_G(n) <= 2n-2+(n%2) (2 mutations rejected)")

    # Cert 3: ModCert (m=2, 3 rows) for aperiodic Thue-Morse parity of W_G(n)
    u_tm = [1, 0, 0]
    M0_tm = [[0, 0, 0], [0, 1, 0], [0, 0, 1]]
    M1_tm = [[0, 0, 1], [0, 0, 1], [0, 1, 0]]
    v_tm = [0, 1, 0]
    u_m2, M0_m2, M1_m2, v_m2 = sub_rep(*sq_rep(1), u_tm, M0_tm, M1_tm, v_tm)
    K_m2 = [[1, 0, 0, 0, -1, 0, 0], [0, 1, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, -1, -1]]
    C0_m2 = [[0, 0, 0], [0, 1, 0], [0, 0, 1]]
    C1_m2 = [[0, 1, 0], [0, 1, 1], [0, 0, 1]]
    assert check_mod_cert(u_m2, M0_m2, M1_m2, v_m2, K_m2, C0_m2, C1_m2, [1, 0, 0], 2)
    assert not check_mod_cert(u_m2, M0_m2, M1_m2, v_m2, K_m2, C0_m2, C1_m2, [1, 0, 0], 4)
    print("  [PASS] Cert 3 (ModCert m=2, 3 rows): W_G(n) == (n%2)*(1 - pop(n)%2) mod 2 (m=4 rejected)")

    # Cert 4: ModCert (m=4, 4 rows) for E_G(n) mod 4
    u_r4 = [1, 0, 0, 0]
    M0_r4 = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1]]
    M1_r4 = [[0, 1, 2, 0], [0, 0, 0, 1], [0, 1, 0, 0], [0, 0, 0, 1]]
    v_r4 = [0, 0, 0, 1]
    u_m4, M0_m4, M1_m4, v_m4 = sub_rep(*sq_rep(2), u_r4, M0_r4, M1_r4, v_r4)
    K_m4 = [
        [1, 0, 0, 0, -1, 0, 0, 0],
        [0, 2, 0, 0, 0, 0, -2, 0],
        [0, 0, 1, 0, 0, -1, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, -1],
    ]
    C0_m4 = [[0, 0, 0, 0], [0, 0, 2, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
    C1_m4 = [[0, 1, 1, 0], [0, 0, 2, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
    assert check_mod_cert(u_m4, M0_m4, M1_m4, v_m4, K_m4, C0_m4, C1_m4, [1, 0, 0, 0], 4)
    print("  [PASS] Cert 4 (ModCert m=4, 4 rows): E_G(n) == (n%2)*((n//2)%4) mod 4")

    # Cert 5: IntertwineCert (9x5) linking QRep to Kronecker product LRep (x) RRep
    u_L, M0_L, M1_L, v_L = [1, 0, 0], [[2, 0, 0], [0, 1, 0], [0, 0, 1]], [[2, -1, 1], [0, 0, 0], [0, 0, 1]], [0, 1, 1]
    u_R, M0_R, M1_R, v_R = [1, 0, 0], [[2, 0, 0], [0, 1, 0], [0, 0, 1]], [[2, 2, -1], [0, 0, 0], [0, 0, 1]], [0, 1, 1]
    u_Q = [1, 0, 0, 0, 0]
    M0_Q = [[4, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 2, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]
    M1_Q = [[4, -2, 2, 1, -1], [0, 2, 0, -1, 1], [0, 0, 2, 2, -1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1]]
    v_Q = [0, 0, 0, 1, 1]
    T_Q = [
        [1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0],
        [0, 0, 0, 1, 0],
        [0, 1, 0, 0, 0],
        [0, 0, 0, 1, 0],
        [0, 0, 0, 0, 1],
    ]
    assert check_intertwine_cert(
        u_Q, M0_Q, M1_Q, v_Q,
        kron_vec(u_L, u_R), kron_mat(M0_L, M0_R), kron_mat(M1_L, M1_R), kron_vec(v_L, v_R),
        T_Q,
    )
    print("  [PASS] Cert 5 (IntertwineCert 9x5): QRep == LRep (x) RRep (Kronecker product)")

    # Cert 6 & 7: ConePosCert (alpha=1, beta=1) for Q(n) - E_G(n) >= 0 and 2*E_G(n) - Q(n) >= 0
    u_up, M0_up, M1_up, v_up = sub_rep(u_Q, M0_Q, M1_Q, v_Q, *sq_rep(2))
    P_up = [
        [0, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, -1, 1],
        [1, 0, 0, 0, 0, -1, 0, 0, 0],
        [1, -1, 1, 0, -1, -1, -1, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0, -1],
    ]
    C0_up = [[0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0], [0, 1, 2, 2, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]
    C1_up = [[1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 1, 2, 2, 1, 1], [0, 0, 0, 4, 4, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1]]
    assert check_cone_cert(u_up, M0_up, M1_up, v_up, P_up, C0_up, C1_up, [0, 0, 1, 0, 0, 0], 1, 1, pos_only=True)

    u_sq2, M0_sq2, M1_sq2, v_sq2 = sq_rep(2)
    u_lo, M0_lo, M1_lo, v_lo = sub_rep(vec_scale(2, u_sq2), M0_sq2, M1_sq2, v_sq2, u_Q, M0_Q, M1_Q, v_Q)
    P_lo = [
        [0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, -1, 1, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, -1, 0, 0, 0, 0],
        [2, 2, 1, 0, -1, 1, -1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 1, 0, 0, 0, 0, -1],
        [0, 0, 0, -1, 0, 0, 0, 0, 1],
    ]
    C0_lo = [[0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 0, 2, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]
    C1_lo = [[1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0], [1, 1, 2, 2, 1, 0, 1], [0, 4, 0, 4, 4, 0, 3], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]
    assert check_cone_cert(u_lo, M0_lo, M1_lo, v_lo, P_lo, C0_lo, C1_lo, [0, 0, 1, 0, 0, 0, 0], 1, 1, pos_only=True)
    print("  [PASS] Cert 6 & 7 (ConePosCert, alpha=1, beta=1): Q(n) <= 2*E_G(n) <= 2*Q(n)")

    # Cert 8: Parametric 1-row IdentityCert for second-difference law (checked for q in -5..5)
    for q in range(-5, 6):
        _, M0, M1, v = sq_rep(q)
        Z4 = [[0] * 4 for _ in range(4)]
        M0_sh = [M0[i] + Z4[i] for i in range(4)] + [M1[i] + Z4[i] for i in range(4)]
        M1_sh = [M1[i] + Z4[i] for i in range(4)] + [Z4[i] + M0[i] for i in range(4)]
        v_sh = v + matvec(M1, v)
        u_sd = [-2 * q, -2 * q, 0, 0, 2 * q, 0, 0, 0]
        K_sd = [[-1, -1, 0, 0, 1, 0, 0, 0]]
        assert check_identity_cert(u_sd, M0_sh, M1_sh, v_sh, K_sd, [[0]], [[2 * q]], [2 * q], 1, 1)
    print("  [PASS] Cert 8 (IdentityCert, 1 row): S_q(2n)+S_q(2n+2)-2*S_q(2n+1) = -2*(n%2) for q in -5..5")


# ============================================================================
# 4. Independent Exact-Integer Replay Across n = 0..65536 + Sharpness & Extremals
# ============================================================================

def verify_instances_and_sharpness():
    N = 65536
    print(f"\n=== [2] Independent Exact-Integer Replay on n = 0..{N} ===")
    WG = [0] * (N + 1)
    EG = [0] * (N + 1)
    S3 = [0] * (N + 1)
    for k in range(N):
        gk = gray(k)
        WG[k + 1] = WG[k] + popcount(gk) - popcount(k)
        EG[k + 1] = EG[k] + gk - k
        S3[k + 1] = S3[k] + dq(3, k)

    # Check all 5 theorems on 0..N
    for n in range(N + 1):
        assert WG[n] >= 0 and EG[n] >= 0 and S3[n] >= 0
        if n >= 1:
            assert 5 * WG[n] <= 2 * n - 2 + (n & 1)
        assert (WG[n] - (n & 1) * (1 - (popcount(n) & 1))) % 2 == 0
        assert (EG[n] - (n & 1) * ((n >> 1) & 3)) % 4 == 0
        qn = q_dyadic(n)
        assert qn <= 2 * EG[n] <= 2 * qn
    for n in range(N // 2 - 1):
        assert WG[2 * n] + WG[2 * n + 2] - 2 * WG[2 * n + 1] == -2 * (n & 1)
        assert EG[2 * n] + EG[2 * n + 2] - 2 * EG[2 * n + 1] == -2 * (n & 1)
        assert S3[2 * n] + S3[2 * n + 2] - 2 * S3[2 * n + 1] == -2 * (n & 1)
    print(f"  [PASS] All 5 infinite theorems verified on all {N + 1} exact integer instances!")

    print("\n=== [3] Extremal Sharpness Families & Boundary Counterexamples ===")
    # Infinite extremal family for Theorem 2 (computed directly via LinRep up to k=8, n > 47 million!)
    u1 = [1, 0, 0, 0]
    M0_1 = [[2, 0, 0, 0], [0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
    M1_1 = [[2, 1, 1, 0], [0, 1, -1, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
    v1 = [0, 0, 0, 1]
    b = 2
    for k in range(9):
        a = b + 1
        w_odd = eval_linrep(u1, M0_1, M1_1, v1, a)
        w_even = eval_linrep(u1, M0_1, M1_1, v1, 2 * a)
        if a <= N:
            assert w_odd == WG[a]
        if 2 * a <= N:
            assert w_even == WG[2 * a]
        assert 5 * w_odd == 2 * a - 1
        assert 5 * w_even == 2 * (2 * a) - 2
        if k <= 4 or k == 8:
            ratio = Fraction(w_odd, a)
            gap = Fraction(2, 5) - ratio
            print(f"  k={k}: a_k={a:10d}, W_G(a_k)={w_odd:10d}, 5*W_G-(2n-1)=0, 2/5 - W_G/n = {gap}")
        b = 8 * b + 6

    # Infinite extremal families for Theorem 4
    for m in range(1, 16):
        n_lo = (1 << m) + 1
        n_hi = 3 * (1 << (m - 1))
        assert 2 * EG[n_lo] == q_dyadic(n_lo) + 1
        assert EG[n_hi] == q_dyadic(n_hi)
    print("  [PASS] Theorem 4 extremals verified for m=1..15: 2*E_G(2^m+1) = Q+1 and E_G(3*2^{m-1}) = Q")

    # Sharpness counterexamples
    assert popcount(gray(7)) - popcount(7) == -2
    assert gray(7) - 7 == -3
    S_neg1_5 = sum(dq(-1, k) for k in range(5))
    assert S_neg1_5 == -1
    assert WG[1463] == 585 and 1000 * WG[1463] > 399 * 1463
    assert WG[3] % 2 == 1 and WG[7] % 2 == 0
    assert EG[65] == 32 and q_dyadic(65) == 63 and 100 * EG[65] < 51 * q_dyadic(65)
    print("  [PASS] All 6 sharpness & non-triviality counterexamples independently verified!")
    print(f"         - Termwise negative at k=7: pop(G(7))-pop(7)=-2, G(7)-7=-3")
    print(f"         - q=-1 fails at n=5: S_{{-1}}(5) = {S_neg1_5}")
    print(f"         - Slope 399/1000 fails at n=1463: W_G(1463)={WG[1463]}, 1000*585=585000 > {399*1463}=399*1463")
    print(f"         - Period-4 parity fails: W_G(3)%2=1 != 0=W_G(7)%2")
    print(f"         - Ratio 51/100 fails at n=65: E_G(65)=32, Q(65)=63, 100*32=3200 < {51*63}=51*63")


if __name__ == "__main__":
    verify_all_certificates()
    verify_instances_and_sharpness()
    print("\nALL EXACT CHECKS PASSED (ZERO FLOATS).")
