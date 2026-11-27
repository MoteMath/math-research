"""
Exact Dyadic-Rational (Z[1/2]) Infinite Positive-Definite Form Engine
Independent Exact-Rational Discovery, Synthesis, Replay & Falsification Suite
Worker: adic-10 (Thread 4: 2-Adic, Nimber, Carry-Arithmetic & Number-Theoretic Infinite Mechanisms)

ZERO floating-point arithmetic anywhere: 100% Python int & fractions.Fraction,
with strict power-of-2 denominator (Z[1/2]) checks on all synthesized certificates.
"""

from fractions import Fraction


def is_dyadic(q: Fraction) -> bool:
    d = q.denominator
    return d > 0 and (d & (d - 1)) == 0


def v2_nat(n: int) -> int:
    if n == 0:
        return 0
    c = 0
    while (n & 1) == 0:
        n >>= 1
        c += 1
    return c


def bitrev(k: int, i: int) -> int:
    if k == 0:
        return 0
    return ((i & 1) << (k - 1)) + bitrev(k - 1, i >> 1)


def mat_mul(A, B):
    m, n, p = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(p)] for i in range(m)]


def mat_T(A):
    return [[A[i][j] for i in range(len(A))] for j in range(len(A[0]))]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_kron(A, B):
    ra, ca = len(A), len(A[0])
    rb, cb = len(B), len(B[0])
    out = [[Fraction(0) for _ in range(ca * cb)] for _ in range(ra * rb)]
    for i in range(ra):
        for j in range(ca):
            for p in range(rb):
                for q in range(cb):
                    out[i * rb + p][j * cb + q] = A[i][j] * B[p][q]
    return out


def is_symm(A) -> bool:
    n = len(A)
    return all(A[i][j] == A[j][i] for i in range(n) for j in range(n))


def ldlt_strict_pd(A):
    """Independent exact-rational LDL^T strict positive-definiteness oracle."""
    n = len(A)
    if not is_symm(A):
        return False, []
    M = [row[:] for row in A]
    pivots = []
    for k in range(n):
        piv = M[k][k]
        if piv <= 0:
            return False, pivots + [piv]
        pivots.append(piv)
        row_k = M[k][:]
        for i in range(k + 1, n):
            fac = row_k[i] / piv
            for j in range(k + 1, n):
                M[i][j] -= fac * row_k[j]
    return True, pivots


def quad_eval(M, x) -> Fraction:
    n = len(x)
    return sum(M[i][j] * x[i] * x[j] for i in range(n) for j in range(n))


def compute_delta(H, U, C, W):
    UtW = mat_mul(mat_T(U), W)
    UtWU = mat_mul(UtW, U)
    HW = mat_kron(H, W)
    return mat_sub(mat_add(C, UtWU), HW)


def sos_reconstruct(d: int, terms):
    M = [[Fraction(0) for _ in range(d)] for _ in range(d)]
    for w, v in terms:
        assert w > 0 and is_dyadic(w), f"Non-positive or non-dyadic weight {w}"
        assert len(v) == d and all(is_dyadic(x) for x in v), f"Non-dyadic vector {v}"
        for i in range(d):
            for j in range(d):
                M[i][j] += w * v[i] * v[j]
    return M


def check_strict_pd_cert(q0, l0, H, U0, U1, C, Wtarget, W, h_terms, delta_terms, surplus_terms) -> bool:
    m = len(l0)
    if not (is_symm(C) and is_symm(W) and is_symm(Wtarget)):
        return False
    if len(h_terms) < 2:
        return False
    if any(w <= 0 or not is_dyadic(w) for w, _, _ in h_terms):
        return False
    (_, p1, q1), (_, p2, q2) = h_terms[0], h_terms[1]
    if p1 * q2 - q1 * p2 == 0:
        return False
    Hrec = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]]
    for w, p, q in h_terms:
        if not (is_dyadic(p) and is_dyadic(q)):
            return False
        Hrec[0][0] += w * p * p
        Hrec[0][1] += w * p * q
        Hrec[1][0] += w * q * p
        Hrec[1][1] += w * q * q
    if Hrec != H:
        return False
    U = [U0[p] + U1[p] for p in range(m)]
    Delta = compute_delta(H, U, C, W)
    try:
        if sos_reconstruct(2 * m, delta_terms) != Delta:
            return False
        if sos_reconstruct(m, surplus_terms) != mat_sub(Wtarget, W):
            return False
    except AssertionError:
        return False
    f0 = q0 + quad_eval(W, l0)
    return f0 > 0


def check_boundary_strict_pd_cert(q0, l0, H, U0, U1, C, Wtarget, W, h_terms, delta_terms, surplus_terms, tau) -> bool:
    m = len(l0)
    if not (is_symm(C) and is_symm(W) and is_symm(Wtarget)):
        return False
    if len(h_terms) < 2 or tau == 0:
        return False
    (_, p1, q1), (_, p2, q2) = h_terms[0], h_terms[1]
    if p1 * q2 - q1 * p2 == 0:
        return False
    Hrec = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]]
    for w, p, q in h_terms:
        if w <= 0 or not (is_dyadic(w) and is_dyadic(p) and is_dyadic(q)):
            return False
        Hrec[0][0] += w * p * p
        Hrec[0][1] += w * p * q
        Hrec[1][0] += w * q * p
        Hrec[1][1] += w * q * q
    if Hrec != H:
        return False
    U = [U0[p] + U1[p] for p in range(m)]
    Delta = compute_delta(H, U, C, W)
    try:
        if sos_reconstruct(2 * m, delta_terms) != Delta:
            return False
        if sos_reconstruct(m, surplus_terms) != mat_sub(Wtarget, W):
            return False
    except AssertionError:
        return False
    f0 = q0 + quad_eval(W, l0)
    if f0 < 0:
        return False
    # Check U0 * l0 = tau * l0
    for p in range(m):
        if sum(U0[p][q] * l0[q] for q in range(m)) != tau * l0[p]:
            return False
    # Check right killer in delta_terms
    vL = l0 + [Fraction(0)] * m
    vR = [Fraction(0)] * m + l0
    has_killer = any(
        sum(u[i] * vL[i] for i in range(2 * m)) == 0 and
        sum(u[i] * vR[i] for i in range(2 * m)) != 0
        for _, u in delta_terms
    )
    if not has_killer:
        return False
    surp_l0 = quad_eval(mat_sub(Wtarget, W), l0)
    return surp_l0 > 0


def build_recursive_bqs(q0, l0, H, U0, U1, C, k: int):
    """Build exact rational (M_k, L_k) of a BQS m system by binary recursion."""
    m = len(l0)
    if k == 0:
        return [[q0]], [[l0[p]] for p in range(m)]
    Mk, Lk = build_recursive_bqs(q0, l0, H, U0, U1, C, k - 1)
    n = 1 << (k - 1)
    N = 2 * n
    Lpair = [[Fraction(0)] * N for _ in range(2 * m)]
    for i in range(n):
        for p in range(m):
            Lpair[p][2 * i] = Lk[p][i]
            Lpair[m + p][2 * i + 1] = Lk[p][i]
    U = [U0[p] + U1[p] for p in range(m)]
    Lnew = [[sum(U[p][r] * Lpair[r][j] for r in range(2 * m)) for j in range(N)] for p in range(m)]
    Mnew = [[Fraction(0)] * N for _ in range(N)]
    h00, h01, h11 = H[0][0], H[0][1], H[1][1]
    for i in range(n):
        for j in range(n):
            Mnew[2 * i][2 * j] = h00 * Mk[i][j]
            Mnew[2 * i][2 * j + 1] = h01 * Mk[i][j]
            Mnew[2 * i + 1][2 * j] = h01 * Mk[i][j]
            Mnew[2 * i + 1][2 * j + 1] = h11 * Mk[i][j]
    for i in range(N):
        for j in range(N):
            s = Fraction(0)
            for a in range(2 * m):
                la = Lpair[a][i]
                if la == 0:
                    continue
                for b in range(2 * m):
                    cab = C[a][b]
                    if cab != 0 and Lpair[b][j] != 0:
                        s += la * cab * Lpair[b][j]
            Mnew[i][j] += s
    return Mnew, Lnew


def add_boundary_W(M, L, W):
    N = len(M)
    m = len(W)
    out = [row[:] for row in M]
    for i in range(N):
        for j in range(N):
            out[i][j] += sum(L[a][i] * W[a][b] * L[b][j] for a in range(m) for b in range(m))
    return out


def build_explicit_riesz(s: int, k: int):
    N = 1 << k
    sc = Fraction(1, N * N)
    return [
        [Fraction(0) if i == j else sc * Fraction(1, 1 << (s * v2_nat(i ^ j))) for j in range(N)]
        for i in range(N)
    ]


def build_explicit_monna_arch(k: int):
    N = 1 << k
    sc = Fraction(1, N * N)
    rho = [Fraction(bitrev(k, i), N) for i in range(N)]
    return [[sc * abs(rho[i] - rho[j]) for j in range(N)] for i in range(N)]


def main():
    print("=" * 76)
    print("adic-10: Exact Z[1/2] Infinite Positive-Definite Form Engine (ZERO FLOATS)")
    print("=" * 76)

    # 0. Verify pure-silicon 2-adic valuation identity v2(|i - j|) == ctz(i ^ j)
    for i in range(256):
        for j in range(256):
            assert v2_nat(i ^ j) == v2_nat(abs(i - j))
    print("[PASS] Pure-silicon identity v2(|i - j|) == ctz(i ^ j) verified on 256 x 256 pairs.")

    # Shared Monna linear transfer U0, U1
    U0_monna = [[Fraction(1, 2), Fraction(0)], [Fraction(0), Fraction(1, 4)]]
    U1_monna = [[Fraction(1, 2), Fraction(0)], [Fraction(1, 4), Fraction(1, 4)]]
    l0_monna = [Fraction(1), Fraction(0)]

    # 1. THEOREM 1: 2-Parameter Sharp 2-Adic Riesz Family (s >= 1, k >= 0)
    print("\n--- Theorem 1: 2^s * mu_k(x)^2 - (2^(s+1) - 1) * R_k^(s)(x) > 0 (forall s >= 1, k >= 0) ---")
    for s in [1, 2, 3, 4]:
        H = [[Fraction(1, 1 << (s + 2)), Fraction(0)], [Fraction(0), Fraction(1, 1 << (s + 2))]]
        U0 = [[Fraction(1, 2)]]
        U1 = [[Fraction(1, 2)]]
        c_off = Fraction(-((1 << (s + 1)) - 1), 4)
        C = [[Fraction(0), c_off], [c_off, Fraction(0)]]
        W = [[Fraction(1 << s)]]
        ok_cert = check_strict_pd_cert(
            Fraction(0), [Fraction(1)], H, U0, U1, C, W, W,
            [(Fraction(1, 1 << (s + 2)), Fraction(1), Fraction(0)),
             (Fraction(1, 1 << (s + 2)), Fraction(0), Fraction(1))],
            [(Fraction((1 << s) - 1, 4), [Fraction(1), Fraction(-1)])],
            []
        )
        assert ok_cert
        # Verify exact double-sum bridge and strict PD via independent LDL^T for k=0..5
        for k in range(6):
            Mk, Lk = build_recursive_bqs(Fraction(0), [Fraction(1)], H, U0, U1, C, k)
            Rk = build_explicit_riesz(s, k)
            N = 1 << k
            coeff = (1 << (s + 1)) - 1
            for i in range(N):
                for j in range(N):
                    assert Mk[i][j] == -coeff * Rk[i][j], f"Bridge mismatch s={s} k={k}"
            Fk = add_boundary_W(Mk, Lk, W)
            ok_pd, _ = ldlt_strict_pd(Fk)
            assert ok_pd, f"LDL^T failed s={s} k={k}"
        # Sharpness counterexample: c = 2^s - 1/16 on vecOnes at k = 4
        k_sh = 4
        Mk, Lk = build_recursive_bqs(Fraction(0), [Fraction(1)], H, U0, U1, C, k_sh)
        F_bad = add_boundary_W(Mk, Lk, [[Fraction(1 << s) - Fraction(1, 16)]])
        ones = [Fraction(1)] * (1 << k_sh)
        v_bad = quad_eval(F_bad, ones)
        assert v_bad < 0
        print(f"  [PASS] s={s}: cert=True, bridge+LDLT exact for k=0..5 (N<=32); sharp c=2^{s}-1/16 -> {v_bad} < 0 at k={k_sh}")

    # 2. THEOREM 2: Sharp Archimedean-Monna Distance Form via Mode-2 Boundary-Kernel Collapse
    print("\n--- Theorem 2: (1/2) * mu_k(x)^2 - A_k(x) > 0 (Mode-2 Boundary-Kernel Lifting) ---")
    H_arch = [[Fraction(1, 8), Fraction(0)], [Fraction(0), Fraction(1, 8)]]
    C_arch = [
        [Fraction(0), Fraction(0), Fraction(-1, 8), Fraction(-1, 8)],
        [Fraction(0), Fraction(0), Fraction(1, 8), Fraction(0)],
        [Fraction(-1, 8), Fraction(1, 8), Fraction(0), Fraction(0)],
        [Fraction(-1, 8), Fraction(0), Fraction(0), Fraction(0)],
    ]
    W_arch_target = [[Fraction(1, 2), Fraction(0)], [Fraction(0), Fraction(0)]]
    W_BB = [[Fraction(0), Fraction(1)], [Fraction(1), Fraction(-2)]]
    h_arch = [(Fraction(1, 8), Fraction(1), Fraction(0)), (Fraction(1, 8), Fraction(0), Fraction(1))]
    d_arch = [(Fraction(1, 8), [Fraction(0), Fraction(1), Fraction(1), Fraction(-1)])]
    s_arch = [(Fraction(1, 2), [Fraction(1), Fraction(-2)])]
    assert check_boundary_strict_pd_cert(
        Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch,
        W_arch_target, W_BB, h_arch, d_arch, s_arch, Fraction(1, 2)
    )
    # Direct induction obstruction: Delta(W_arch_target) has negative 2x2 minor on {0,3} = -1/64
    U_monna = [U0_monna[p] + U1_monna[p] for p in range(2)]
    D_naive = compute_delta(H_arch, U_monna, C_arch, W_arch_target)
    minor03 = D_naive[0][0] * D_naive[3][3] - D_naive[0][3] * D_naive[3][0]
    assert minor03 == Fraction(-1, 64) < 0
    for k in range(6):
        Mk, Lk = build_recursive_bqs(Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch, k)
        Ak = build_explicit_monna_arch(k)
        N = 1 << k
        for i in range(N):
            for j in range(N):
                assert Mk[i][j] == -Ak[i][j]
        Fk = add_boundary_W(Mk, Lk, W_arch_target)
        ok_pd, _ = ldlt_strict_pd(Fk)
        assert ok_pd
    # Sharpness counterexample: c = 1/2 - 1/16 on e_0 + e_{2^k-1} at k=5
    k_sh = 5
    Mk, Lk = build_recursive_bqs(Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch, k_sh)
    F_bad = add_boundary_W(Mk, Lk, [[Fraction(1, 2) - Fraction(1, 16), Fraction(0)], [Fraction(0), Fraction(0)]])
    ep = [Fraction(1) if (i == 0 or i == (1 << k_sh) - 1) else Fraction(0) for i in range(1 << k_sh)]
    v_bad = quad_eval(F_bad, ep)
    assert v_bad < 0
    print(f"  [PASS] Mode-2 cert=True; naive Delta minor_{{0,3}}={minor03} < 0; bridge+LDLT exact k=0..5; sharp c=7/16 -> {v_bad} < 0 at k={k_sh}")

    # 3. THEOREM 3: Coupled Non-Commuting Adelic-Monna-Dipole Form
    print("\n--- Theorem 3: 3*mu_k^2 - (mu_k - 2*nu_k)^2 - 3*R_k^(1) - 2*A_k > 0 ---")
    C_adelic = [
        [Fraction(0), Fraction(0), Fraction(-1), Fraction(-1, 4)],
        [Fraction(0), Fraction(0), Fraction(1, 4), Fraction(0)],
        [Fraction(-1), Fraction(1, 4), Fraction(0), Fraction(0)],
        [Fraction(-1, 4), Fraction(0), Fraction(0), Fraction(0)],
    ]
    W_adelic = [[Fraction(2), Fraction(2)], [Fraction(2), Fraction(-4)]]
    d_adelic = [
        (Fraction(1, 2), [Fraction(-1, 2), Fraction(1, 2), Fraction(1), Fraction(-1, 2)]),
        (Fraction(1, 8), [Fraction(1), Fraction(1), Fraction(0), Fraction(-1)]),
    ]
    assert check_strict_pd_cert(
        Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_adelic,
        W_adelic, W_adelic, h_arch, d_adelic, []
    )
    # Non-commutativity witness for k=2, 3, 4
    for k in [2, 3, 4]:
        Rk = build_explicit_riesz(1, k)
        Ak = build_explicit_monna_arch(k)
        RA = mat_mul(Rk, Ak)
        AR = mat_mul(Ak, Rk)
        assert RA != AR, f"Expected non-commutativity at k={k}"
    for k in range(6):
        Mk, Lk = build_recursive_bqs(Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_adelic, k)
        Rk = build_explicit_riesz(1, k)
        Ak = build_explicit_monna_arch(k)
        N = 1 << k
        for i in range(N):
            for j in range(N):
                assert Mk[i][j] == -3 * Rk[i][j] - 2 * Ak[i][j]
        Fk = add_boundary_W(Mk, Lk, W_adelic)
        ok_pd, _ = ldlt_strict_pd(Fk)
        assert ok_pd
    # Finite-verification trap: c = 11/4 (d = 1) is PD for k=1,2,3 and FAILS at k=4!
    W_trap = [[Fraction(7, 4), Fraction(2)], [Fraction(2), Fraction(-4)]]  # 11/4 mu^2 - (mu - 2 nu)^2
    trap_res = []
    for k in range(1, 5):
        Mk, Lk = build_recursive_bqs(Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_adelic, k)
        ok_pd, _ = ldlt_strict_pd(add_boundary_W(Mk, Lk, W_trap))
        trap_res.append((k, ok_pd))
    assert trap_res == [(1, True), (2, True), (3, True), (4, False)]
    # Concrete sharpness at c=5/2, k=2 on all-ones
    M2, L2 = build_recursive_bqs(Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_adelic, 2)
    v_c52 = quad_eval(add_boundary_W(M2, L2, [[Fraction(3, 2), Fraction(2)], [Fraction(2), Fraction(-4)]]),
                      [Fraction(1)] * 4)
    assert v_c52 < 0
    print(f"  [PASS] Cert=True (2 pure-Z[1/2] SOS terms); [R,A]!=0 for k=2..4; bridge+LDLT exact k=0..5.")
    print(f"  [PASS] Sharpness: c=5/2 k=2 -> {v_c52} < 0; finite-trap c=11/4 PD(k=1..4) = {trap_res}.")

    # 4. THEOREM 4: Asymmetric Non-Diagonal Bilinear H + Indefinite Adelic Interface C
    print("\n--- Theorem 4: Asymmetric Non-Diagonal H=[[1/8,1/16],[1/16,3/16]] + Indefinite Adelic C ---")
    H_asym = [[Fraction(1, 8), Fraction(1, 16)], [Fraction(1, 16), Fraction(3, 16)]]
    C_asym = [
        [Fraction(0), Fraction(0), Fraction(-3, 8), Fraction(-1, 8)],
        [Fraction(0), Fraction(0), Fraction(1, 8), Fraction(0)],
        [Fraction(-3, 8), Fraction(1, 8), Fraction(0), Fraction(0)],
        [Fraction(-1, 8), Fraction(0), Fraction(0), Fraction(0)],
    ]
    W_asym_indef = [[Fraction(1), Fraction(2)], [Fraction(2), Fraction(-2)]]
    W_asym_mean = [[Fraction(3), Fraction(0)], [Fraction(0), Fraction(0)]]
    h_asym = [
        (Fraction(1, 8), Fraction(1), Fraction(1, 2)),
        (Fraction(5, 32), Fraction(0), Fraction(1)),
    ]
    d_asym = [
        (Fraction(1, 8), [Fraction(1), Fraction(0), Fraction(1, 2), Fraction(0)]),
        (Fraction(1, 8), [Fraction(0), Fraction(1), Fraction(1), Fraction(0)]),
        (Fraction(1, 32), [Fraction(0), Fraction(0), Fraction(1), Fraction(0)]),
        (Fraction(1, 4), [Fraction(0), Fraction(0), Fraction(1), Fraction(-1)]),
    ]
    s_asym_mean = [(Fraction(2), [Fraction(1), Fraction(-1)])]
    assert check_strict_pd_cert(
        Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym,
        W_asym_indef, W_asym_indef, h_asym, d_asym, []
    )
    assert check_strict_pd_cert(
        Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym,
        W_asym_mean, W_asym_indef, h_asym, d_asym, s_asym_mean
    )
    for k in range(6):
        Mk, Lk = build_recursive_bqs(Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym, k)
        Fk_indef = add_boundary_W(Mk, Lk, W_asym_indef)
        Fk_mean = add_boundary_W(Mk, Lk, W_asym_mean)
        assert ldlt_strict_pd(Fk_indef)[0]
        assert ldlt_strict_pd(Fk_mean)[0]
        if k >= 2:
            N = 1 << k
            # Verify asymmetric diagonal and failure of diagonal dominance!
            assert Fk_indef[0][0] != Fk_indef[N - 1][N - 1]
            is_dd = all(Fk_indef[i][i] > sum(abs(Fk_indef[i][j]) for j in range(N) if j != i) for i in range(N))
            assert not is_dd
    # Sharpness counterexample: W_00 = 0 fails at k = 1 on (4, 1)
    M1, L1 = build_recursive_bqs(Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym, 1)
    v_w00 = quad_eval(add_boundary_W(M1, L1, [[Fraction(0), Fraction(2)], [Fraction(2), Fraction(-2)]]),
                      [Fraction(4), Fraction(1)])
    assert v_w00 == Fraction(-5, 8) < 0
    print(f"  [PASS] Certs 4A (indef W, det=-6) & 4B (pure mean c=3) = True; LDLT exact k=0..5 (N<=32).")
    print(f"  [PASS] Structural: asymmetric diagonal + non-diagonally-dominant for all k=2..5.")
    print(f"  [PASS] Sharpness: dropping W_00 from 1 to 0 -> F_1(4, 1) = {v_w00} < 0.")

    # 5. Hostile Mutation Tests (mirroring Proof.lean)
    print("\n--- Hostile Mutation Tests (all 7 corrupted certs must return False) ---")
    mutations = [
        ("collinear H (det=0)", check_strict_pd_cert(
            Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym, W_asym_indef, W_asym_indef,
            [(Fraction(1, 8), Fraction(1), Fraction(1, 2)), (Fraction(5, 32), Fraction(1), Fraction(1, 2))],
            d_asym, [])),
        ("negative H weight", check_strict_pd_cert(
            Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym, W_asym_indef, W_asym_indef,
            [(Fraction(-1, 8), Fraction(1), Fraction(1, 2)), (Fraction(5, 32), Fraction(0), Fraction(1))],
            d_asym, [])),
        ("empty deltaTerms", check_strict_pd_cert(
            Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym, W_asym_indef, W_asym_indef,
            h_asym, [], [])),
        ("insufficient target mean c=2", check_strict_pd_cert(
            Fraction(0), l0_monna, H_asym, U0_monna, U1_monna, C_asym,
            [[Fraction(2), Fraction(0)], [Fraction(0), Fraction(0)]], W_asym_indef,
            h_asym, d_asym, s_asym_mean)),
        ("Mode-1 rejects degenerate base Arch", check_strict_pd_cert(
            Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch,
            W_arch_target, W_BB, h_arch, d_arch, s_arch)),
        ("Mode-2 rejects tau=0", check_boundary_strict_pd_cert(
            Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch,
            W_arch_target, W_BB, h_arch, d_arch, s_arch, Fraction(0))),
        ("Mode-2 rejects missing killer", check_boundary_strict_pd_cert(
            Fraction(0), l0_monna, H_arch, U0_monna, U1_monna, C_arch,
            W_arch_target, W_BB, h_arch, [], s_arch, Fraction(1, 2))),
    ]
    for label, res in mutations:
        assert res is False, f"Mutation {label} unexpectedly passed!"
        print(f"  [PASS] Rejected mutation: {label}")

    print("\nALL EXACT Z[1/2] VERIFICATIONS, BRIDGES, SHARPNESS & MUTATION CHECKS PASSED!")


if __name__ == "__main__":
    main()
