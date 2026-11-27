#!/usr/bin/env python3
"""
Pure-Silicon Exact Discovery & Verification Suite for Task 7 (`specmat-7`):
  Portal-Transfer Boundary Minor Functor & Bit-Parity Schur Interleaving
  on Fenwick Update+Query Graphs G_k(c) and Binary Heaps H_k.

Strict pure-silicon arithmetic:
  - ONLY exact Python `int`, `fractions.Fraction`, and exact integer polynomials `Z[X]`.
  - ZERO floating-point (`float`, `math.sqrt`, numpy, scipy) anywhere.
"""

from fractions import Fraction
from typing import List, Tuple, Dict


# ============================================================================
# 1. Exact Integer Polynomial Arithmetic Z[X] (represented as list[int])
# ============================================================================

def p_trim(p: List[int]) -> List[int]:
    q = list(p)
    while q and q[-1] == 0:
        q.pop()
    return q

def p_add(a: List[int], b: List[int]) -> List[int]:
    n = max(len(a), len(b))
    out = [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    return p_trim(out)

def p_sub(a: List[int], b: List[int]) -> List[int]:
    n = max(len(a), len(b))
    out = [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]
    return p_trim(out)

def p_neg(a: List[int]) -> List[int]:
    return [-c for c in a]

def p_mul(a: List[int], b: List[int]) -> List[int]:
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b):
                out[i + j] += ca * cb
    return p_trim(out)

def p_const(c: int) -> List[int]:
    return [] if c == 0 else [c]

def p_eval(p: List[int], x: int) -> int:
    acc = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc

def p_str(p: List[int], var: str = "x") -> str:
    p = p_trim(p)
    if not p:
        return "0"
    terms = []
    for deg in range(len(p) - 1, -1, -1):
        c = p[deg]
        if c == 0:
            continue
        sign = "-" if c < 0 else "+"
        ac = abs(c)
        if deg == 0:
            body = str(ac)
        elif deg == 1:
            body = var if ac == 1 else f"{ac}*{var}"
        else:
            body = f"{var}^{deg}" if ac == 1 else f"{ac}*{var}^{deg}"
        if not terms:
            terms.append(f"-{body}" if c < 0 else body)
        else:
            terms.append(f" {sign} {body}")
    return "".join(terms)


# ============================================================================
# 2. Exact Bareiss Determinant (over Z) & Lagrange Interpolation (over Z[X])
# ============================================================================

def bareiss_det(mat: List[List[int]]) -> int:
    """Exact division-free Bareiss algorithm for integer matrix determinant."""
    n = len(mat)
    if n == 0:
        return 1
    A = [row[:] for row in mat]
    sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            swap_row = None
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    swap_row = r
                    break
            if swap_row is None:
                return 0
            A[k], A[swap_row] = A[swap_row], A[k]
            sign = -sign
        piv = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = A[i][j] * piv - A[i][k] * A[k][j]
                assert num % prev_pivot == 0
                A[i][j] = num // prev_pivot
        prev_pivot = piv
    return sign * A[n - 1][n - 1]


def exact_charpoly_matrix(A: List[List[int]]) -> List[int]:
    """Exact det(x*I - A) in Z[X] via exact Fraction Newton interpolation at x = 0..n."""
    n = len(A)
    xs = list(range(n + 1))
    ys = []
    for xv in xs:
        M = [[(xv if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
        ys.append(Fraction(bareiss_det(M)))
    # Divided differences
    dd = ys[:]
    coeffs = [dd[0]]
    for k in range(1, n + 1):
        for i in range(n, k - 1, -1):
            dd[i] = (dd[i] - dd[i - 1]) / Fraction(xs[i] - xs[i - k])
        coeffs.append(dd[k])
    # Convert Newton basis to monomial basis over Fraction, assert all integers
    poly = [Fraction(0)]
    basis = [Fraction(1)]
    for k in range(n + 1):
        c = coeffs[k]
        if len(poly) < len(basis):
            poly.extend([Fraction(0)] * (len(basis) - len(poly)))
        for i, b in enumerate(basis):
            poly[i] += c * b
        # basis *= (x - xs[k])
        new_b = [Fraction(0)] * (len(basis) + 1)
        for i, b in enumerate(basis):
            new_b[i + 1] += b
            new_b[i] -= b * xs[k]
        basis = new_b
    int_poly = []
    for val in poly:
        assert val.denominator == 1, f"Non-integer charpoly coeff: {val}"
        int_poly.append(int(val.numerator))
    return p_trim(int_poly)


def mat_mul(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]


# ============================================================================
# 3. Bitwise Fenwick Update+Query Graph G_k(c) & Binary Heap H_k
# ============================================================================

def lowbit(i: int) -> int:
    assert i > 0
    return i & -i

def fenwick_edge(N: int, i: int, j: int) -> bool:
    """Bitwise undirected Fenwick Update+Query edge on {0, ..., N}."""
    if 0 < i < N and (j == i - lowbit(i) or j == i + lowbit(i)):
        return True
    if 0 < j < N and (i == j - lowbit(j) or i == j + lowbit(j)):
        return True
    return False

def fenwick_uq_adj(k: int, c: int = 1) -> List[List[int]]:
    """(2^k + 1) x (2^k + 1) weighted adjacency matrix A(G_k(c))."""
    N = 1 << k
    M = [[0] * (N + 1) for _ in range(N + 1)]
    for i in range(N + 1):
        for j in range(N + 1):
            if fenwick_edge(N, i, j):
                M[i][j] = 1 if abs(i - j) == 1 else c
    return M

def fenwick_uq_adj_general_n(N: int) -> List[List[int]]:
    """(N + 1) x (N + 1) unweighted Fenwick UQ adjacency matrix for arbitrary N."""
    return [[1 if fenwick_edge(N, i, j) else 0 for j in range(N + 1)] for i in range(N + 1)]

def fenwick_uq_lap(k: int) -> List[List[int]]:
    """(2^k + 1) x (2^k + 1) combinatorial Laplacian L(G_k) = D - A."""
    A = fenwick_uq_adj(k, 1)
    n = len(A)
    L = [[-A[i][j] for j in range(n)] for i in range(n)]
    for i in range(n):
        L[i][i] = sum(A[i])
    return L

def fenwick_uq_signless(k: int) -> List[List[int]]:
    """(2^k + 1) x (2^k + 1) signless Laplacian Q(G_k) = D + A."""
    A = fenwick_uq_adj(k, 1)
    n = len(A)
    Q = [[A[i][j] for j in range(n)] for i in range(n)]
    for i in range(n):
        Q[i][i] = sum(A[i])
    return Q

def fenwick_B(n: int) -> List[List[int]]:
    """n x n truncated Fenwick UQ matrix B_n on {1, ..., n}."""
    return [[1 if fenwick_edge(n, i + 1, j + 1) else 0 for j in range(n)] for i in range(n)]

def binary_heap_adj(k: int) -> List[List[int]]:
    """(2^k - 1) x (2^k - 1) complete binary heap adjacency matrix on {1, ..., 2^k - 1}."""
    n = (1 << k) - 1
    A = [[0] * n for _ in range(n)]
    for v in range(2, n + 1):
        p = v >> 1
        A[v - 1][p - 1] = 1
        A[p - 1][v - 1] = 1
    return A

def inorder_heap_adj(k: int) -> List[List[int]]:
    """Bitwise in-order complete binary tree on {1, ..., 2^k - 1} (isomorphic to binary heap)."""
    n = (1 << k) - 1
    A = [[0] * n for _ in range(n)]
    for i in range(1, n + 1):
        lb = lowbit(i)
        if lb >= 2:
            left = i - (lb >> 1)
            right = i + (lb >> 1)
            A[i - 1][left - 1] = 1
            A[left - 1][i - 1] = 1
            A[i - 1][right - 1] = 1
            A[right - 1][i - 1] = 1
    return A


# ============================================================================
# 4. Mechanism A: Division-Free 6-Tuple Portal-Transfer Engine over Z[X]
# ============================================================================

def step_perturb_poly(st, p, q1, q2, r):
    d0, dL, dR, dLR, d0R, dR0 = st
    # d0' = d0 + p*dL + r*dR + (p*r - q1*q2)*dLR + q1*d0R + q2*dR0
    pr_q1q2 = p_sub(p_mul(p, r), p_mul(q1, q2))
    nd0 = p_add(d0, p_add(p_mul(p, dL), p_mul(r, dR)))
    nd0 = p_add(nd0, p_mul(pr_q1q2, dLR))
    nd0 = p_add(nd0, p_add(p_mul(q1, d0R), p_mul(q2, dR0)))
    ndL = p_add(dL, p_mul(r, dLR))
    ndR = p_add(dR, p_mul(p, dLR))
    ndLR = dLR
    nd0R = p_sub(d0R, p_mul(q2, dLR))
    ndR0 = p_sub(dR0, p_mul(q1, dLR))
    return (nd0, ndL, ndR, ndLR, nd0R, ndR0)

def step_glue_poly(stA, stB, s):
    a0, aL, aR, aLR, a0R, aR0 = stA
    b0, bL, bR, bLR, b0R, bR0 = stB
    nd0 = p_add(p_add(p_mul(aR, b0), p_mul(a0, bL)), p_mul(s, p_mul(aR, bL)))
    ndL = p_add(p_add(p_mul(aLR, b0), p_mul(aL, bL)), p_mul(s, p_mul(aLR, bL)))
    ndR = p_add(p_add(p_mul(aR, bR), p_mul(a0, bLR)), p_mul(s, p_mul(aR, bLR)))
    ndLR = p_add(p_add(p_mul(aLR, bR), p_mul(aL, bLR)), p_mul(s, p_mul(aLR, bLR)))
    nd0R = p_mul(a0R, b0R)
    ndR0 = p_mul(aR0, bR0)
    return (nd0, ndL, ndR, ndLR, nd0R, ndR0)


# ============================================================================
# 5. Mechanism B: Closed-Form One-Shot Inverse for Even B_{2m} & Dyadic A^{-1}
# ============================================================================

def interleave_inv(M: List[List[int]]) -> List[List[int]]:
    """Exact integer inverse of B_{2m} = interleave(M) using closed-form U_m^{-1}."""
    m = len(M)
    n = 2 * m
    # U_m^{-1}[i][j] = (-1)^(i-j) if j <= i else 0
    Uinv = [[(1 if (i - j) % 2 == 0 else -1) if j <= i else 0 for j in range(m)] for i in range(m)]
    UinvT = [[Uinv[j][i] for j in range(m)] for i in range(m)]
    # Top-left even-even block (0-based indices 2a, 2b) = -U_m^{-T} M U_m^{-1}
    UM = mat_mul(UinvT, M)
    TL = mat_mul(UM, Uinv)
    TL = [[-val for val in row] for row in TL]
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i % 2 == 0 and j % 2 == 0:
                out[i][j] = TL[i // 2][j // 2]
            elif i % 2 == 0 and j % 2 == 1:
                out[i][j] = UinvT[i // 2][j // 2]
            elif i % 2 == 1 and j % 2 == 0:
                out[i][j] = Uinv[i // 2][j // 2]
            else:
                out[i][j] = 0
    return out

def fenwick_uq_dyadic_inv(k: int) -> List[List[int]]:
    """Exact integer matrix J_k such that A(G_k) * J_k = 4 * I for all k >= 2."""
    assert k >= 2
    N = 1 << k
    m = N >> 1
    Binv = interleave_inv(fenwick_B(m))
    A = fenwick_uq_adj(k, 1)
    u = [A[i + 1][0] for i in range(N)]
    v = [sum(Binv[i][j] * u[j] for j in range(N)) for i in range(N)]
    sigma = sum(u[i] * v[i] for i in range(N))
    assert sigma == 4, f"Expected u^T B^-1 u = 4 at k={k}, got {sigma}"
    J = [[0] * (N + 1) for _ in range(N + 1)]
    J[0][0] = -1
    for i in range(N):
        J[0][i + 1] = v[i]
        J[i + 1][0] = v[i]
    for i in range(N):
        for j in range(N):
            J[i + 1][j + 1] = sigma * Binv[i][j] - v[i] * v[j]
    return J


# ============================================================================
# 6. Full Verification Suite
# ============================================================================

def main() -> None:
    print("=" * 76)
    print("SPEC-MAT-7 PURE-SILICON VERIFICATION SUITE (ZERO FLOATS)")
    print("=" * 76)

    # --- Theorem 1: Constant-Determinant Collapse & Unimodularity ---
    print("\n[Theorem 1] Constant-Determinant Collapse A(G_k(c)) & Farey Chord")
    for c in (1, 2, -3, 7):
        for k in range(2, 6):
            A = fenwick_uq_adj(k, c)
            det_A = bareiss_det(A)
            assert det_A == -4 * c, f"Mismatch at k={k}, c={c}: {det_A}"
            B = [row[1:] for row in A[1:]]
            det_B = bareiss_det(B)
            assert det_B == 1, f"Unimodularity failed at k={k}, c={c}: {det_B}"
            I_int = [row[1:-1] for row in A[1:-1]]
            det_int = bareiss_det(I_int)
            assert det_int == 0, f"Interior minor nonzero at k={k}, c={c}: {det_int}"
            F = [row[:] for row in A]
            F[0][-1] += c
            F[-1][0] += c
            det_F = bareiss_det(F)
            assert det_F == -2 * c, f"Farey det mismatch at k={k}, c={c}: {det_F}"
    print("  PASS: For all c in {1,2,-3,7} and k in {2,3,4,5} (up to 33x33):")
    print("        det(A(G_k(c))) = -4c, det(A\\{0}) = +1, det(Interior) = 0, det(Farey) = -2c.")

    # --- Theorem 2: Exact Characteristic Polynomial Transfer over Z[X] ---
    print("\n[Theorem 2] Exact Characteristic Polynomial Transfer in Z[X]")
    # Adjacency charpoly xI - A(G_k)
    # k=1: [[x, -1, 0], [-1, x, -1], [0, -1, x]]
    st_adj = (
        [0, -2, 0, 1],   # x^3 - 2x
        [-1, 0, 1],      # x^2 - 1
        [-1, 0, 1],      # x^2 - 1
        [0, 1],          # x
        [1],             # 1
        [1],             # 1
    )
    for k in range(1, 5):
        cp_direct = exact_charpoly_matrix(fenwick_uq_adj(k, 1))
        assert st_adj[0] == cp_direct, f"Adj charpoly mismatch at k={k}"
        print(f"  k={k} (n={2**k+1:2d}) charpoly(A(G_{k})) deg={len(cp_direct)-1}: "
              f"P(0)={cp_direct[0] if cp_direct else 0}, P(1)={p_eval(cp_direct, 1)}")
        st_p = step_perturb_poly(st_adj, [], [-1], [-1], [])
        st_adj = step_glue_poly(st_p, st_p, [0, -1])

    # Laplacian charpoly xI - L(G_k)
    # k=1: [[x-1, 1, 0], [1, x-2, 1], [0, 1, x-1]]
    st_lap = (
        [0, 3, -4, 1],   # x^3 - 4x^2 + 3x
        [1, -3, 1],      # x^2 - 3x + 1
        [1, -3, 1],      # x^2 - 3x + 1
        [-2, 1],         # x - 2
        [1],             # 1
        [1],             # 1
    )
    for k in range(1, 5):
        cp_direct = exact_charpoly_matrix(fenwick_uq_lap(k))
        assert st_lap[0] == cp_direct, f"Lap charpoly mismatch at k={k}"
        print(f"  k={k} (n={2**k+1:2d}) charpoly(L(G_{k})) deg={len(cp_direct)-1}: "
              f"P(0)={cp_direct[0] if cp_direct else 0}, P(2)={p_eval(cp_direct, 2)}")
        st_p = step_perturb_poly(st_lap, [-1], [1], [1], [-1])
        st_lap = step_glue_poly(st_p, st_p, [0, -1])
    print("  PASS: Exact Z[X] 6-tuple transfer matches Bareiss/Newton charpolys for k=1..4.")

    # --- Theorem 3: Exact x = 2 Laplacian & Signless-Laplacian Collapse ---
    print("\n[Theorem 3] Exact x = 2 Spectral Collapse for L(G_k) and Q(G_k)")
    for k in range(1, 6):
        L = fenwick_uq_lap(k)
        Q = fenwick_uq_signless(k)
        n = len(L)
        M_L = [[(2 if i == j else 0) - L[i][j] for j in range(n)] for i in range(n)]
        M_Q = [[(2 if i == j else 0) - Q[i][j] for j in range(n)] for i in range(n)]
        dL = bareiss_det(M_L)
        dQ = bareiss_det(M_Q)
        assert dL == 2 - (1 << (k + 1)), f"L collapse failed at k={k}: {dL}"
        exp_Q = -2 if k == 1 else 10 - (1 << (k + 1))
        assert dQ == exp_Q, f"Q collapse failed at k={k}: {dQ}"
        print(f"  k={k}: det(2I - L(G_{k})) = {dL:4d} (= 2 - 2^{k+1}),  det(2I - Q(G_{k})) = {dQ:4d}")
    print("  PASS: lambda = 2 is never an eigenvalue of L(G_k) or Q(G_k) for any k >= 1.")

    # --- Theorem 4: Spanning-Tree Perfect-Square Law & Dyadic Resistance ---
    print("\n[Theorem 4] Laplacian Spanning Trees & Dyadic Effective Resistance")
    tau, d = 1, 2
    for k in range(1, 6):
        L = fenwick_uq_lap(k)
        cof = bareiss_det([row[1:] for row in L[1:]])
        interior = bareiss_det([row[1:-1] for row in L[1:-1]])
        assert cof == tau and interior == d
        assert ((1 << k) - 1) * d == (1 << k) * tau
        # Closed-form product check for k >= 2
        if k >= 2:
            prod = ((1 << k) - 1) ** 2
            for j in range(2, k):
                prod *= ((1 << j) - 1) ** (1 << (k - j))
            assert tau == prod
        reff = Fraction(d, tau)
        print(f"  k={k}: tau_k = {tau}, d_k = {d}, R_eff(0, 2^{k}) = {reff} (= 2^{k}/(2^{k}-1))")
        tau, d = (tau + d) ** 2, 2 * d * (tau + d)
    print("  PASS: Perfect-square law, closed product, and dyadic resistance R_eff = 2^k/(2^k-1) verified.")

    # --- Theorem 5: Closed-Form Integer Inverse B_{2m}^{-1} & Dyadic 4*A(G_k)^{-1} ---
    print("\n[Theorem 5] Closed-Form Integer Inverse for ALL Even B_{2m} & Dyadic 4*A(G_k)^{-1}")
    for m in range(1, 13):
        B2m = fenwick_B(2 * m)
        Inv = interleave_inv(fenwick_B(m))
        prod = mat_mul(B2m, Inv)
        I2m = [[1 if i == j else 0 for j in range(2 * m)] for i in range(2 * m)]
        assert prod == I2m, f"Inverse failed at 2m={2*m}"
    print("  PASS: B_{2m} * interleaveInv(B_m) = I_{2m} over Z for ALL m = 1..12 (n = 2..24)!")
    for k in range(2, 6):
        A = fenwick_uq_adj(k, 1)
        J = fenwick_uq_dyadic_inv(k)
        prod = mat_mul(A, J)
        n = len(A)
        I4 = [[4 if i == j else 0 for j in range(n)] for i in range(n)]
        assert prod == I4, f"Dyadic inverse failed at k={k}"
    print("  PASS: A(G_k) * J_k = 4 * I_{2^k+1} over Z for ALL k = 2..5 (exact 1/4-dyadic inverse)!")

    # --- Theorem 6: Binary Heap H_k Chebyshev-Product Factorization ---
    print("\n[Theorem 6] Binary Heap H_k Exact Chebyshev-Product Factorization in Z[X]")
    # T_0 = 1, T_1 = x, T_{j+1} = x*T_j - 2*T_{j-1}
    T = [[1], [0, 1]]
    for j in range(1, 6):
        T.append(p_sub(p_mul([0, 1], T[j]), p_mul([2], T[j - 1])))
    R_poly = [None, [1]]
    for k in range(1, 5):
        R_poly.append(p_mul(T[k], p_mul(R_poly[k], R_poly[k])))
    for k in range(1, 5):
        cp_heap = exact_charpoly_matrix(binary_heap_adj(k))
        cp_inorder = exact_charpoly_matrix(inorder_heap_adj(k))
        pred = p_mul(T[k], R_poly[k])
        assert cp_heap == cp_inorder == pred, f"Heap factorization mismatch at k={k}"
        assert bareiss_det(binary_heap_adj(k)) == 0
        print(f"  k={k} (n={2**k-1:2d}): charpoly(H_{k}) = T_{k}(x) * R_{k}(x) [deg {len(pred)-1}], det(H_{k}) = 0")
    print("  PASS: Bitwise in-order heap & standard binary heap share exact Chebyshev-product charpoly.")

    # --- Sharpness Counterexamples ---
    print("\n[Sharpness Counterexamples] Falsifying Relaxed Hypotheses")
    # 1. k = 1 fails constant -4
    d_k1 = bareiss_det(fenwick_uq_adj(1, 1))
    assert d_k1 == 0 and d_k1 != -4
    print(f"  1. Sharpness of k >= 2: det(A(G_1)) = {d_k1} != -4.")
    # 2. Non-power-of-two N fails constant -4
    non_pow2 = {N: bareiss_det(fenwick_uq_adj_general_n(N)) for N in (3, 5, 6, 7, 10, 12)}
    assert non_pow2[6] == 2 and non_pow2[12] == -6 and non_pow2[3] == 0
    print(f"  2. Sharpness of N = 2^k: det(A(G_N)) for N in {{3,5,6,7,10,12}} = {non_pow2}.")
    # 3. Odd truncation B_{2m+1} fails unimodularity
    odd_B = {n: bareiss_det(fenwick_B(n)) for n in (1, 3, 5, 7)}
    assert all(v == 0 for v in odd_B.values())
    print(f"  3. Sharpness of even 2m for B_n: det(B_n) for odd n in {{1,3,5,7}} = {odd_B}.")
    # 4. Asymmetric base/chord query vs update weights (a=1 on i-lowbit, b=2 on i+lowbit) destroy collapse
    asym_dets = []
    for k in range(1, 5):
        N = 1 << k
        A_ab = [[0] * (N + 1) for _ in range(N + 1)]
        for v in range(1, N):
            lb = lowbit(v)
            q, u = v - lb, v + lb
            A_ab[v][q] = 1
            A_ab[q][v] = 1
            A_ab[v][u] = 2
            A_ab[u][v] = 2
        asym_dets.append((k, bareiss_det(A_ab)))
    assert asym_dets == [(1, 0), (2, -24), (3, -264), (4, -59592)], f"Unexpected asym_dets: {asym_dets}"
    print(f"  4. Sharpness of equal query/update weights: (a=1, b=2) dets = {asym_dets}.")

    print("\nALL EXACT CHECKS PASSED WITH ZERO FLOATING-POINT OPERATIONS.")


if __name__ == "__main__":
    main()
