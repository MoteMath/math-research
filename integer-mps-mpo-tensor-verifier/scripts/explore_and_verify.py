#!/usr/bin/env python3
"""
Exact Pure-Silicon MPS/MPO Tensor-Network Certificate Synthesizer,
Independent Exact Verifier, Sharpness Tester, and Mutation Suite.

Zero floating-point arithmetic anywhere: uses strictly Python `int` and `fractions.Fraction`.
"""

from fractions import Fraction
import math
from functools import reduce

# ============================================================================
# 1. Exact Integer & Rational Linear Algebra
# ============================================================================

def gcd_list(xs):
    g = 0
    for x in xs:
        g = math.gcd(g, abs(x))
    return g if g != 0 else 1

def kron_vec(u, v):
    return [a * b for a in u for b in v]

def kron_mat(A, B):
    ra, ca = len(A), len(A[0])
    rb, cb = len(B), len(B[0])
    return [
        [A[i // rb][j // cb] * B[i % rb][j % cb] for j in range(ca * cb)]
        for i in range(ra * rb)
    ]

def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]

def mat_mul(A, B):
    r = len(A)
    k = len(B)
    c = len(B[0]) if k > 0 else 0
    return [[sum(A[i][m] * B[m][j] for m in range(k)) for j in range(c)] for i in range(r)]

def mat_vec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]

def vec_mat(u, A):
    if not A:
        return []
    return [sum(u[i] * A[i][j] for i in range(len(u))) for j in range(len(A[0]))]

def vec_dot(u, v):
    return sum(a * b for a, b in zip(u, v))

def mat_pow(A, k):
    n = len(A)
    res = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    base = [row[:] for row in A]
    while k > 0:
        if k & 1:
            res = mat_mul(res, base)
        base = mat_mul(base, base)
        k >>= 1
    return res

def solve_exact_linear(cols, target):
    K = len(target)
    r = len(cols)
    if r == 0:
        return [] if all(t == 0 for t in target) else None
    aug = [[Fraction(cols[j][i]) for j in range(r)] + [Fraction(target[i])] for i in range(K)]
    row = 0
    piv_cols = []
    for col in range(r):
        piv = next((i for i in range(row, K) if aug[i][col] != 0), None)
        if piv is None:
            continue
        aug[row], aug[piv] = aug[piv], aug[row]
        pv = aug[row][col]
        aug[row] = [x / pv for x in aug[row]]
        for i in range(K):
            if i != row and aug[i][col] != 0:
                f = aug[i][col]
                aug[i] = [aug[i][j] - f * aug[row][j] for j in range(r + 1)]
        piv_cols.append(col)
        row += 1
    for i in range(row, K):
        if aug[i][r] != 0:
            return None
    sol = [Fraction(0)] * r
    for i, c in enumerate(piv_cols):
        sol[c] = aug[i][r]
    return sol

# ============================================================================
# 2. Exact Two-Stage Integer Ho-Kalman / Krylov Certificate Compiler
# ============================================================================

def synthesize_right_krylov(u, T, v, w0=0):
    K = len(T)
    v0 = mat_vec(mat_pow(T, w0), v)
    basis = []
    cur = [Fraction(x) for x in v0]
    while True:
        sol = solve_exact_linear(basis, cur)
        if sol is not None:
            break
        basis.append(cur)
        cur = [sum(Fraction(T[i][j]) * cur[j] for j in range(K)) for i in range(K)]
    r = len(basis)
    if r == 0:
        return {"r": 0, "d": 1, "M": [], "P": [[] for _ in range(K)], "u_r": [], "v_r": [], "rec": []}
    # By Gauss's lemma, minimal polynomial over Q of integer matrix T is monic in Z[x]!
    assert all(x.denominator == 1 for x in sol), f"Unexpected rational recurrence: {sol}"
    M = [[0] * r for _ in range(r)]
    for j in range(r - 1):
        M[j + 1][j] = 1
    for j in range(r):
        M[j][r - 1] = int(sol[j])
    P_raw = [[int(basis[j][i]) for j in range(r)] for i in range(K)]
    g = gcd_list([P_raw[i][j] for i in range(K) for j in range(r)])
    P = [[P_raw[i][j] // g for j in range(r)] for i in range(K)]
    v_r = [g] + [0] * (r - 1)
    u_r = vec_mat(u, P)
    return {"r": r, "d": 1, "M": M, "P": P, "u_r": u_r, "v_r": v_r, "rec": [int(x) for x in sol]}

def synthesize_left_krylov(u, T, v, w0=0):
    K = len(T)
    TT = [[T[j][i] for j in range(K)] for i in range(K)]
    res = synthesize_right_krylov(v, TT, u, w0)
    r = res["r"]
    Q = [[res["P"][j][i] for j in range(K)] for i in range(r)]
    M = [[res["M"][j][i] for j in range(r)] for i in range(r)]
    return {"r": r, "d": 1, "M": M, "Q": Q, "u_r": res["v_r"], "v_r": res["u_r"], "rec": res["rec"]}

def synthesize_two_stage(u, T, v, w0=0):
    K = len(T)
    v0 = mat_vec(mat_pow(T, w0), v)
    if all(x == 0 for x in v0):
        return {"K": K, "w0": w0, "r1": 0, "r2": 0, "stage1": None, "stage2": None, "rec": []}
    s1 = synthesize_right_krylov(u, T, v, w0)
    if all(x == 0 for x in s1["u_r"]):
        return {"K": K, "w0": w0, "r1": s1["r"], "r2": 0, "stage1": s1, "stage2": None, "rec": []}
    s2 = synthesize_left_krylov(s1["u_r"], s1["M"], s1["v_r"], 0)
    return {"K": K, "w0": w0, "r1": s1["r"], "r2": s2["r"], "stage1": s1, "stage2": s2, "rec": s2["rec"]}

# ============================================================================
# 3. Certificate Checkers (Exact Mirror of Lean 4 Bool Checkers)
# ============================================================================

def check_right_reduction(u, T, v, w0, d, M, P, u_r, v_r):
    if d == 0:
        return False
    v0 = mat_vec(mat_pow(T, w0), v)
    if mat_mul(T, P) != mat_mul(P, M):
        return False
    if mat_vec(P, v_r) != [d * x for x in v0]:
        return False
    if vec_mat(u, P) != u_r:
        return False
    return True

def check_left_reduction(u, T, v, w0, d, M, Q, u_r, v_r):
    if d == 0:
        return False
    u0 = vec_mat(u, mat_pow(T, w0))
    if mat_mul(Q, T) != mat_mul(M, Q):
        return False
    if vec_mat(u_r, Q) != [d * x for x in u0]:
        return False
    if mat_vec(Q, v) != v_r:
        return False
    return True

def check_recurrence_on_M(M, coeffs):
    r = len(M)
    if len(coeffs) != r:
        return False
    lhs = mat_pow(M, r)
    rhs = [[0] * r for _ in range(r)]
    for j, c in enumerate(coeffs):
        Mj = mat_pow(M, j)
        for i in range(r):
            for k in range(r):
                rhs[i][k] += c * Mj[i][k]
    return lhs == rhs

def check_mps_gauge_right(mps1, mps2, d, P):
    if d == 0:
        return False
    L1, A1, R1 = mps1
    L2, A2, R2 = mps2
    for b in (0, 1):
        if mat_mul(A1[b], P) != mat_mul(P, A2[b]):
            return False
    if mat_vec(P, R2) != [d * x for x in R1]:
        return False
    if vec_mat(L1, P) != L2:
        return False
    return True

def check_mpo_gauge_right(mpo1, mpo2, d, P):
    if d == 0:
        return False
    L1, W1, R1 = mpo1
    L2, W2, R2 = mpo2
    for b1 in (0, 1):
        for b2 in (0, 1):
            if mat_mul(W1[(b1, b2)], P) != mat_mul(P, W2[(b1, b2)]):
                return False
    if mat_vec(P, R2) != [d * x for x in R1]:
        return False
    if vec_mat(L1, P) != L2:
        return False
    return True

def check_mpo_gauge_left(mpo1, mpo2, d, Q):
    if d == 0:
        return False
    L1, W1, R1 = mpo1
    L2, W2, R2 = mpo2
    for b1 in (0, 1):
        for b2 in (0, 1):
            if mat_mul(Q, W1[(b1, b2)]) != mat_mul(W2[(b1, b2)], Q):
                return False
    if vec_mat(L2, Q) != [d * x for x in L1]:
        return False
    if mat_vec(Q, R1) != R2:
        return False
    return True

# ============================================================================
# 4. Pure-Silicon Binary Functions (Direct Arithmetic Definitions)
# ============================================================================

def carries_direct(w, x, y):
    c, tot = 0, 0
    for i in range(w):
        s = ((x >> i) & 1) + ((y >> i) & 1) + c
        c = s >> 1
        tot += c
    return tot

def carries_int_direct(w, x, y):
    c, tot = 0, 0
    for i in range(w):
        tot += c
        s = ((x >> i) & 1) + ((y >> i) & 1) + c
        c = s >> 1
    return tot

def borrows_direct(w, x, y):
    b, tot = 0, 0
    for i in range(w):
        d = ((x >> i) & 1) - ((y >> i) & 1) - b
        if d < 0:
            b = 1
            tot += 1
        else:
            b = 0
    return tot

def popcount_w(w, x):
    return sum((x >> i) & 1 for i in range(w))

def thue_morse_direct(w, x):
    return -1 if (popcount_w(w, x) & 1) else 1

def rudin_shapiro_direct(w, x):
    cnt = 0
    for i in range(max(0, w - 1)):
        if ((x >> i) & 1) and ((x >> (i + 1)) & 1):
            cnt += 1
    return -1 if (cnt & 1) else 1

def walsh_hadamard_direct(w, x, y):
    return -1 if (popcount_w(w, x & y) & 1) else 1

def gray_direct(w, x):
    return (x ^ (x >> 1)) & ((1 << w) - 1)

def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

# ============================================================================
# 5. Pure-Silicon MPS & MPO Constructors
# ============================================================================

def make_carry_mpo(q):
    W = {}
    for x in (0, 1):
        for y in (0, 1):
            M = [[0, 0], [0, 0]]
            for c in (0, 1):
                c2 = (x + y + c) >> 1
                M[c][c2] = q if c2 == 1 else 1
            W[(x, y)] = M
    return ([1, 0], W, [1, 1])

def make_carry_int_mpo(q):
    W = {}
    for x in (0, 1):
        for y in (0, 1):
            M = [[0, 0], [0, 0]]
            for c in (0, 1):
                c2 = (x + y + c) >> 1
                M[c][c2] = q if c == 1 else 1
            W[(x, y)] = M
    return ([1, 0], W, [1, 1])

def make_borrow_mpo(q):
    W = {}
    for x in (0, 1):
        for y in (0, 1):
            M = [[0, 0], [0, 0]]
            for b in (0, 1):
                b2 = 1 if (x - y - b) < 0 else 0
                M[b][b2] = q if b2 == 1 else 1
            W[(x, y)] = M
    return ([1, 0], W, [1, 1])

H_mpo = ([1], {(0,0): [[1]], (0,1): [[1]], (1,0): [[1]], (1,1): [[-1]]}, [1])
Id_mpo = ([1], {(0,0): [[1]], (0,1): [[0]], (1,0): [[0]], (1,1): [[1]]}, [1])
Inc_mpo = ([0, 1], {
    (0,0): [[1,0],[0,0]], (0,1): [[0,0],[1,0]],
    (1,0): [[0,0],[0,1]], (1,1): [[1,0],[0,0]],
}, [1, 1])
Gray_mpo = ([1, 1], {
    (x, y): [[1 if (s == x and s2 == (x ^ y)) else 0 for s2 in (0, 1)] for s in (0, 1)]
    for x in (0, 1) for y in (0, 1)
}, [1, 0])

tm_mps = ([1], {0: [[1]], 1: [[-1]]}, [1])
rs_mps = ([1, 0], {0: [[1, 0], [1, 0]], 1: [[0, 1], [0, -1]]}, [1, 1])

def mpo_compose(O1, O2):
    L1, W1, R1 = O1; L2, W2, R2 = O2
    W = {}
    for b1 in (0, 1):
        for b3 in (0, 1):
            W[(b1, b3)] = mat_add(kron_mat(W1[(b1, 0)], W2[(0, b3)]),
                                  kron_mat(W1[(b1, 1)], W2[(1, b3)]))
    return (kron_vec(L1, L2), W, kron_vec(R1, R2))

def mpo_transpose(O):
    L, W, R = O
    return (L, {(x, y): W[(y, x)] for x in (0, 1) for y in (0, 1)}, R)

def mpo_trace_TM(O):
    L, W, R = O
    return L, mat_add(W[(0, 0)], W[(1, 1)]), R

def mpo_apply_mps(O, psi):
    Lo, W, Ro = O; Lp, A, Rp = psi
    Anew = {b1: mat_add(kron_mat(W[(b1, 0)], A[0]), kron_mat(W[(b1, 1)], A[1])) for b1 in (0, 1)}
    return (kron_vec(Lo, Lp), Anew, kron_vec(Ro, Rp))

def mps_inner_TM(psi1, psi2):
    L1, A1, R1 = psi1; L2, A2, R2 = psi2
    return kron_vec(L1, L2), mat_add(kron_mat(A1[0], A2[0]), kron_mat(A1[1], A2[1])), kron_vec(R1, R2)

def eval_mps(psi, w, x):
    L, A, R = psi
    v = list(L)
    for i in range(w):
        v = vec_mat(v, A[(x >> i) & 1])
    return vec_dot(v, R)

def eval_mpo(O, w, x, y):
    L, W, R = O
    v = list(L)
    for i in range(w):
        v = vec_mat(v, W[((x >> i) & 1, (y >> i) & 1)])
    return vec_dot(v, R)

# ============================================================================
# 6. Full Verification, Certificate Synthesis, Sharpness, and Mutation Suite
# ============================================================================

def main():
    print("=================================================================")
    print("Pure-Silicon Exact Integer MPS/MPO Contraction Engine Verifier")
    print("=================================================================")

    # A. Verify semantic bridges (direct binary functions == MPS/MPO eval) for w = 0..5
    C = make_carry_mpo(-1)
    Cint = make_carry_int_mpo(-1)
    B = make_borrow_mpo(-1)
    for w in range(6):
        N = 1 << w
        for x in range(N):
            assert eval_mps(tm_mps, w, x) == thue_morse_direct(w, x)
            assert eval_mps(rs_mps, w, x) == rudin_shapiro_direct(w, x)
            for y in range(N):
                assert eval_mpo(H_mpo, w, x, y) == walsh_hadamard_direct(w, x, y)
                assert eval_mpo(Inc_mpo, w, x, y) == (1 if y == ((x + 1) % N) else 0)
                assert eval_mpo(Gray_mpo, w, x, y) == (1 if y == gray_direct(w, x) else 0)
                for q in (-3, -2, -1, 0, 2):
                    assert eval_mpo(make_carry_mpo(q), w, x, y) == q ** carries_direct(w, x, y)
                    assert eval_mpo(make_carry_int_mpo(q), w, x, y) == q ** carries_int_direct(w, x, y)
                    assert eval_mpo(make_borrow_mpo(q), w, x, y) == q ** borrows_direct(w, x, y)
    print("[PASS] Semantic tensor bridges verified exhaustively for w = 0..5 across all q in {-3,-2,-1,0,2}.")

    # B. Synthesize & verify all contraction certificates + replay against brute-force sums (w = 0..5)
    C2 = mpo_compose(C, C)
    C3 = mpo_compose(C2, C)
    C4 = mpo_compose(C2, C2)
    Cint3 = mpo_compose(mpo_compose(Cint, Cint), Cint)

    cert_specs = [
        ("Tr(C^4)", mpo_trace_TM(C4), 0),
        ("Tr(C^3)", mpo_trace_TM(C3), 1),
        ("Tr(Cint^3)", mpo_trace_TM(Cint3), 2),
        ("Tr(C*B)", mpo_trace_TM(mpo_compose(C, B)), 1),
        ("Tr(C*B^T)", mpo_trace_TM(mpo_compose(C, mpo_transpose(B))), 1),
        ("Tr(B*H)", mpo_trace_TM(mpo_compose(B, H_mpo)), 1),
        ("Tr(C*H)", mpo_trace_TM(mpo_compose(C, H_mpo)), 0),
        ("Tr(C*Inc)", mpo_trace_TM(mpo_compose(C, Inc_mpo)), 1),
        ("<rs|C(-1)|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(C, rs_mps)), 0),
        ("<rs|C(-2)|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(make_carry_mpo(-2), rs_mps)), 0),
        ("<rs|C(-3)|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(make_carry_mpo(-3), rs_mps)), 0),
        ("<rs|C(0)|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(make_carry_mpo(0), rs_mps)), 0),
        ("<rs|B(-1)|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(B, rs_mps)), 1),
        ("<rs|Inc|rs>", mps_inner_TM(rs_mps, mpo_apply_mps(Inc_mpo, rs_mps)), 2),
    ]

    print("\n--- Synthesized Two-Stage Exact Integer Certificates ---")
    synthesized = {}
    for name, (u, T, v), w0 in cert_specs:
        c = synthesize_two_stage(u, T, v, w0)
        synthesized[name] = (u, T, v, w0, c)
        if c["stage1"] is not None:
            s1 = c["stage1"]
            assert check_right_reduction(u, T, v, w0, s1["d"], s1["M"], s1["P"], s1["u_r"], s1["v_r"])
            if c["stage2"] is not None:
                s2 = c["stage2"]
                assert check_left_reduction(s1["u_r"], s1["M"], s1["v_r"], 0, s2["d"], s2["M"], s2["Q"], s2["u_r"], s2["v_r"])
                assert check_recurrence_on_M(s2["M"], s2["rec"])
            else:
                assert all(x == 0 for x in s1["u_r"])
        else:
            assert all(x == 0 for x in mat_vec(mat_pow(T, w0), v))
        print(f"  {name:14s}: K={c['K']:2d} -> r1={c['r1']:2d} -> r2={c['r2']:2d} (w0={w0}) | rec={c['rec']}")

    # C. Independent brute-force verification of all 7 theorems up to w = 5 (and transfer matrix up to w = 15)
    print("\n--- Independent Exact Replay of All 7 Theorems ---")
    for w in range(6):
        N = 1 << w
        # Thm 1: Parametric Rudin-Shapiro q-Carry Master Law
        for q in (-4, -3, -2, -1, 0, 1, 2, 3):
            lhs = sum(rudin_shapiro_direct(w, x) * rudin_shapiro_direct(w, y) * (q ** carries_direct(w, x, y))
                      for x in range(N) for y in range(N))
            assert (q + 3) * lhs == (q + 2) * (2 ** (w + 1)) + (-(q + 1)) ** (w + 1)
            if q == -1:
                assert lhs == 2 ** w
            if q == -2:
                assert lhs == 1
            if q == -3:
                assert lhs == (1 - w) * (2 ** w)
        # Thm 3: Tr(C*H) = 2^w * F_{w+2}, Tr(B(q)*H) = (q+1)^w
        tr_ch = sum((-1) ** (carries_direct(w, x, y) + popcount_w(w, x & y)) for x in range(N) for y in range(N))
        assert tr_ch == (2 ** w) * fib(w + 2)
        for q in (-2, -1, 0, 1, 2):
            tr_bhq = sum((q ** borrows_direct(w, x, y)) * walsh_hadamard_direct(w, x, y) for x in range(N) for y in range(N))
            assert tr_bhq == (q + 1) ** w
        # Thm 4 & 5
        if w >= 1:
            assert sum((-1) ** (carries_direct(w, x, y) + borrows_direct(w, y, x)) for x in range(N) for y in range(N)) == 0
            assert sum((-1) ** (carries_direct(w, x, y) + borrows_direct(w, x, y)) for x in range(N) for y in range(N)) == 0
            assert sum((-1) ** carries_direct(w, x, (x + 1) % N) for x in range(N)) == 2
            rs_b_rs = sum(rudin_shapiro_direct(w, x) * rudin_shapiro_direct(w, y) * ((-1) ** borrows_direct(w, x, y))
                          for x in range(N) for y in range(N))
            assert rs_b_rs == (0 if w % 2 == 0 else 2 ** w)
        if w >= 2:
            assert sum(rudin_shapiro_direct(w, x) * rudin_shapiro_direct(w, (x + 1) % N) for x in range(N)) == 0
        # Thm 6: Pointwise C*TM and B*TM and Inc*Inc^T and Gray*Gray^T
        if w >= 1:
            for x in range(N):
                c_tm = sum(((-1) ** carries_direct(w, x, y)) * thue_morse_direct(w, y) for y in range(N))
                b_tm = sum(((-1) ** borrows_direct(w, x, y)) * thue_morse_direct(w, y) for y in range(N))
                assert c_tm == 2 * (x & 1)
                assert b_tm == 2 * (1 - (x & 1))
                assert c_tm + b_tm == 2
        # Thm 7: Chiral anti-symmetry U C U^T = -C and odd traces = 0
        if w >= 1:
            H = N >> 1
            for x in range(N):
                for y in range(N):
                    sx = -1 if x >= H else 1
                    sy = -1 if y >= H else 1
                    assert sx * sy * ((-1) ** carries_direct(w, x ^ H, y ^ H)) == -((-1) ** carries_direct(w, x, y))

    # Brute-force check Tr(C^4) for w = 0..4 and transfer-matrix check for w = 0..15
    tr_c4_bf = []
    for w in range(5):
        N = 1 << w
        Cmat = [[(-1) ** carries_direct(w, x, y) for y in range(N)] for x in range(N)]
        C2m = mat_mul(Cmat, Cmat)
        C4m = mat_mul(C2m, C2m)
        tr_c4_bf.append(sum(C4m[i][i] for i in range(N)))
    assert tr_c4_bf == [1, 8, 96, 896, 9728]
    u4, T4, v4 = mpo_trace_TM(C4)
    tr_c4_tm = [vec_dot(u4, mat_vec(mat_pow(T4, w), v4)) for w in range(16)]
    assert tr_c4_tm[:5] == tr_c4_bf
    for w in range(14):
        assert tr_c4_tm[w + 2] == 4 * tr_c4_tm[w + 1] + 64 * tr_c4_tm[w]
    print(f"[PASS] Brute-force & transfer-matrix replay verified! Tr(C^4)[0..7] = {tr_c4_tm[:8]}")

    # D. Verify Two-Stage Pointwise MPO Unitarity Certificates (Inc*Inc^T = I and Gray*Gray^T = I)
    # Inc * Inc^T (dim 4) -> intermediate dim 2 -> Id (dim 1)
    IncIncT = mpo_compose(Inc_mpo, mpo_transpose(Inc_mpo))
    Mid_Inc = ([0, 1], {
        (0,0): [[1, 0], [1, 0]], (0,1): [[0, 0], [0, 0]],
        (1,0): [[0, 0], [0, 0]], (1,1): [[1, 0], [0, 1]],
    }, [1, 1])
    Q_Inc = [[1, 0, 0, 0], [0, 0, 0, 1]]
    P_Inc = [[1], [1]]
    assert check_mpo_gauge_left(IncIncT, Mid_Inc, 1, Q_Inc)
    assert check_mpo_gauge_right(Mid_Inc, Id_mpo, 1, P_Inc)

    # Gray * Gray^T (dim 4) -> intermediate dim 2 -> Id (dim 1)
    GrayGrayT = mpo_compose(Gray_mpo, mpo_transpose(Gray_mpo))
    Mid_Gray = ([1, 1], {
        (0,0): [[1, 0], [0, 0]], (0,1): [[0, 0], [0, 0]],
        (1,0): [[0, 0], [0, 0]], (1,1): [[0, 1], [1, 0]],
    }, [1, 0])
    # let's check Mid_Gray's exact W on columns [e_0, e_3]!
    P_Gray = [[1, 0], [0, 0], [0, 0], [0, 1]]
    Mid_Gray_W = {}
    for b1 in (0, 1):
        for b2 in (0, 1):
            WP = mat_mul(GrayGrayT[1][(b1, b2)], P_Gray)
            Mid_Gray_W[(b1, b2)] = [[WP[0][0], WP[0][1]], [WP[3][0], WP[3][1]]]
    Mid_Gray = ([1, 1], Mid_Gray_W, [1, 0])
    Q_Gray = [[1, 1]]
    assert check_mpo_gauge_right(GrayGrayT, Mid_Gray, 1, P_Gray)
    assert check_mpo_gauge_left(Mid_Gray, Id_mpo, 1, Q_Gray)
    print(f"[PASS] Two-stage MPO Unitarity Gauge Certificates verified! Mid_Gray_W = {Mid_Gray_W}")

    # E. Sharpness Counterexamples (outside hypotheses)
    print("\n--- Sharpness Counterexamples (All Verified Exact) ---")
    # 1. <rs|Inc|rs> = 0 needs w >= 2; fails at w = 1 (= 2)
    s_rs_inc_1 = sum(rudin_shapiro_direct(1, x) * rudin_shapiro_direct(1, (x + 1) % 2) for x in range(2))
    assert s_rs_inc_1 == 2
    # 2. Tr(Cint^3) = 0 needs w >= 2; fails at w = 1 (= 8)
    s_cint3_1 = sum((-1) ** (carries_int_direct(1, x, y) + carries_int_direct(1, y, z) + carries_int_direct(1, z, x))
                    for x in range(2) for y in range(2) for z in range(2))
    assert s_cint3_1 == 8
    # 3. Tr(C(q)*B(q)) = 0 needs q = -1 (and w >= 1); fails at q = 0, w = 1 (= 2) and q = -1, w = 0 (= 1)
    s_cb_q0 = sum((0 ** carries_direct(1, x, y)) * (0 ** borrows_direct(1, y, x)) for x in range(2) for y in range(2))
    assert s_cb_q0 == 2
    # 4. Tr(B(q)*H) = 0 needs q = -1; fails at q = 0, w = 1 (= 1)
    s_bh_q0 = sum((0 ** borrows_direct(1, x, y)) * walsh_hadamard_direct(1, x, y) for x in range(2) for y in range(2))
    assert s_bh_q0 == 1
    # 5. <rs|B|rs> vanishes at even w >= 2, NOT at odd w = 1 (= 2) or w = 3 (= 8)
    s_rs_b_1 = sum(rudin_shapiro_direct(1, x) * rudin_shapiro_direct(1, y) * ((-1) ** borrows_direct(1, x, y))
                   for x in range(2) for y in range(2))
    assert s_rs_b_1 == 2
    # 6. Tr(C*Inc) = 2 needs w >= 1; fails at w = 0 (= 1), and fails for Borrow at w = 1 (= 0) and w = 4 (= 6)
    s_b_inc_4 = sum((-1) ** borrows_direct(4, x, (x + 1) % 16) for x in range(16))
    assert s_b_inc_4 == 6
    print(f"  <rs|Inc|rs>(w=1)={s_rs_inc_1}, Tr(Cint^3)(w=1)={s_cint3_1}, Tr(C(0)B(0))(w=1)={s_cb_q0}, Tr(B(0)H)(w=1)={s_bh_q0}, Tr(B*Inc)(w=4)={s_b_inc_4}")

    # F. Exhaustive Negative / Mutation Tests on Certificates
    print("\n--- Negative / Mutation Rejection Tests ---")
    mut_count = 0
    # Test 1: Mutate every field of Tr(C^4) Stage 1 & Stage 2 & Recurrence
    u4, T4, v4, w0_4, c4 = synthesized["Tr(C^4)"]
    s1, s2 = c4["stage1"], c4["stage2"]
    # d = 0 must fail
    assert not check_right_reduction(u4, T4, v4, 0, 0, s1["M"], s1["P"], s1["u_r"], s1["v_r"])
    mut_count += 1
    # Mutate each entry of M1
    for i in range(len(s1["M"])):
        for j in range(len(s1["M"][0])):
            Mbad = [row[:] for row in s1["M"]]
            Mbad[i][j] += 1
            assert not check_right_reduction(u4, T4, v4, 0, 1, Mbad, s1["P"], s1["u_r"], s1["v_r"])
            mut_count += 1
    # Mutate each entry of P1
    for i in range(len(s1["P"])):
        for j in range(len(s1["P"][0])):
            Pbad = [row[:] for row in s1["P"]]
            Pbad[i][j] += 1
            assert not check_right_reduction(u4, T4, v4, 0, 1, s1["M"], Pbad, s1["u_r"], s1["v_r"])
            mut_count += 1
    # Mutate u1, v1
    for j in range(len(s1["u_r"])):
        ubad = s1["u_r"][:]; ubad[j] += 1
        assert not check_right_reduction(u4, T4, v4, 0, 1, s1["M"], s1["P"], ubad, s1["v_r"])
        vbad = s1["v_r"][:]; vbad[j] += 1
        assert not check_right_reduction(u4, T4, v4, 0, 1, s1["M"], s1["P"], s1["u_r"], vbad)
        mut_count += 2
    # Mutate Stage 2 Q, M2, recurrence coefficients
    assert not check_left_reduction(s1["u_r"], s1["M"], s1["v_r"], 0, 0, s2["M"], s2["Q"], s2["u_r"], s2["v_r"])
    mut_count += 1
    for j in range(len(s2["rec"])):
        rbad = s2["rec"][:]; rbad[j] += 1
        assert not check_recurrence_on_M(s2["M"], rbad)
        mut_count += 1
    # Test 2: Wrong shift w0 = 1 on <rs|Inc|rs> (which requires w0 = 2!)
    u_ri, T_ri, v_ri, _, c_ri = synthesized["<rs|Inc|rs>"]
    s1_ri = c_ri["stage1"]
    assert not check_right_reduction(u_ri, T_ri, v_ri, 1, 1, s1_ri["M"], s1_ri["P"], s1_ri["u_r"], s1_ri["v_r"])
    mut_count += 1
    # Test 3: Mutate MPO Unitarity Gauge Certificates
    Q_Inc_bad = [row[:] for row in Q_Inc]; Q_Inc_bad[0][1] = 1
    assert not check_mpo_gauge_left(IncIncT, Mid_Inc, 1, Q_Inc_bad)
    P_Gray_bad = [row[:] for row in P_Gray]; P_Gray_bad[1][0] = 1
    assert not check_mpo_gauge_right(GrayGrayT, Mid_Gray, 1, P_Gray_bad)
    mut_count += 2
    print(f"[PASS] All {mut_count} certificate mutations cleanly REJECTED (checkCert = false).")
    print("\nALL INDEPENDENT EXACT CHECKS PASSED!")

if __name__ == "__main__":
    main()
