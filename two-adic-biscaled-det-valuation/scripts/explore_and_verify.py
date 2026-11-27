"""
Pure-Silicon 2-Adic Bi-Scaled Elimination & Finite-Corner Mod-2 Certification Engine
Independent exact-integer (zero-float) synthesis, verification, and sharpness suite.

Companion script to `Proof.lean` and `MECHANISM.md` (specmat-12).
"""

import sys


def pop(x: int) -> int:
    return x.bit_count()


def pop_sum(n: int) -> int:
    return sum(pop(k) for k in range(n))


def v2_int(x: int):
    """Exact 2-adic valuation of nonzero integer x (returns None for x = 0)."""
    if x == 0:
        return None
    x = abs(x)
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def v2_succ(x: int) -> int:
    """Exact v_2(x + 1) = number of trailing 1-bits of x."""
    c = 0
    while x & 1:
        x >>= 1
        c += 1
    return c


def bit_diff(v: int, u: int) -> int:
    """Width-independent bitwise set difference v \\ u = v ^ (u & v)."""
    return v ^ (u & v)


def row_exp(e: int, i: int) -> int:
    return 0 if i <= 1 else (e * pop(i)) // 2


def col_exp(e: int, j: int) -> int:
    return 0 if j <= 1 else (e * pop(j) + 1) // 2


def det_bareiss(M: list[list[int]]) -> int:
    """Exact integer determinant via fraction-free Bareiss elimination (zero floats)."""
    n = len(M)
    if n == 0:
        return 1
    A = [list(row) for row in M]
    sign = 1
    prev_pivot = 1
    for k in range(n):
        if A[k][k] == 0:
            swap_row = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    swap_row = i
                    break
            if swap_row is None:
                return 0
            A[k], A[swap_row] = A[swap_row], A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = A[i][j] * pivot - A[i][k] * A[k][j]
                assert num % prev_pivot == 0
                A[i][j] = num // prev_pivot
        prev_pivot = pivot
    return sign * A[n - 1][n - 1]


def inv_mod2(M: list[list[int]]):
    """Exact Gauss-Jordan inversion over F_2."""
    n = len(M)
    A = [[x & 1 for x in row] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    for col in range(n):
        piv = next((r for r in range(col, n) if A[r][col] == 1), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        for r in range(n):
            if r != col and A[r][col] == 1:
                for c in range(2 * n):
                    A[r][c] ^= A[col][c]
    return [row[n:] for row in A]


def mat_mul_mod2(A: list[list[int]], B: list[list[int]]) -> list[list[int]]:
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) & 1 for j in range(n)] for i in range(n)]


def full_hybrid_matrix(a: int, q: int, lam: int, c: int, d: int, n: int) -> list[list[int]]:
    """5-parameter non-symmetric dense bitwise matrix M_n(a, q, lam, c, d)."""
    return [
        [
            (a ** v2_succ(i ^ j))
            + (q ** pop(i & j))
            + (2 * lam) * (c ** pop(bit_diff(j, i))) * (d ** pop(i & j))
            for j in range(n)
        ]
        for i in range(n)
    ]


def W_kernel(a: int, i: int, j: int) -> int:
    if i == 0 and j == 0:
        return 1
    m = i | j
    if ((m + 1) & m) == 0:
        return (a - 1) * (a ** (pop(m) - 1)) * ((-2) ** pop(i & j))
    return 0


def build_omega_mod2(e: int, r: int, n: int) -> list[list[int]]:
    """Universal mod-2 quotient matrix Omega_{e,r} mod 2 (independent of odd units u_a, u_q)."""
    M = []
    for i in range(n):
        row = []
        for j in range(n):
            if i == 0 and j == 0:
                w = 1
            else:
                m = i | j
                if ((m + 1) & m) == 0:
                    vW = r * (pop(m) - 1) + pop(i & j)
                    ex = row_exp(e, i) + col_exp(e, j)
                    assert ex <= vW, f"Dominance failed at ({i},{j}): {ex} > {vW}"
                    w = 1 if vW == ex else 0
                else:
                    w = 0
            d = 0
            if i == j:
                d = 1 if i == 0 else (0 if i == 1 else 1)
            row.append((w + d) & 1)
        M.append(row)
    return M


def verify_mobius_identities(n: int = 24) -> None:
    print(f"=== 1. Exact Bitwise Mobius Transform Verification (n = {n}) ===")
    U = [[((-1) ** pop(i ^ k)) if (k & i) == k else 0 for k in range(n)] for i in range(n)]

    def mob2_mat(M):
        T = [[sum(U[i][k] * M[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        return [[sum(T[i][k] * U[j][k] for k in range(n)) for j in range(n)] for i in range(n)]

    # Kernel 1: q^pop(u & v)
    for q in [3, 5, -7]:
        K = [[q ** pop(u & v) for v in range(n)] for u in range(n)]
        G = mob2_mat(K)
        for i in range(n):
            for j in range(n):
                exp = ((q - 1) ** pop(i)) if i == j else 0
                assert G[i][j] == exp

    # Kernel 2: a^v2Succ(u ^ v)
    for a in [2, 4, -6, 3]:
        V = [[a ** v2_succ(u ^ v) for v in range(n)] for u in range(n)]
        G = mob2_mat(V)
        for i in range(n):
            for j in range(n):
                assert G[i][j] == W_kernel(a, i, j)

    # Kernel 3: c^pop(v \ u) * d^pop(u & v)
    for c, d in [(3, 5), (5, 9), (-3, 13)]:
        Q = [[(c ** pop(bit_diff(v, u))) * (d ** pop(u & v)) for v in range(n)] for u in range(n)]
        G = mob2_mat(Q)
        for i in range(n):
            for j in range(n):
                exp = ((c - 1) ** pop(j ^ i)) * ((d - c) ** pop(i)) if (i & j) == i else 0
                assert G[i][j] == exp

    print(f"  PASS: All 3 exact Mobius transforms verified with 0 mismatches on {n}x{n}.")


def synthesize_and_verify_certificates() -> None:
    print("\n=== 2. Finite-Corner F_2 Certificate Synthesis & Verification ===")
    regimes = [
        ("Supercritical (e=3, r=5, C=2)", 3, 5, 2),
        ("Critical Rescue I (e=1, r=1, C=8)", 1, 1, 8),
        ("Critical Rescue II (e=2, r=2, C=4)", 2, 2, 4),
    ]
    for label, e, r, C in regimes:
        Om32 = build_omega_mod2(e, r, 32)
        # Verify exact identity outside C x C (in fact for all rows i >= C)
        for i in range(C, 32):
            for j in range(32):
                assert Om32[i][j] == (1 if i == j else 0), f"Non-identity at ({i},{j}) for {label}"
        for k in range(2, C + 1):
            sub = [row[:k] for row in Om32[:k]]
            R = inv_mod2(sub)
            assert R is not None, f"Corner k={k} singular for {label}"
            prod = mat_mul_mod2(R, sub)
            for i in range(k):
                for j in range(k):
                    assert prod[i][j] == (1 if i == j else 0)
        print(f"  PASS: {label}: identity for rows i >= {C} (checked to 32x32) & F_2 inverses certified for k = 2..{C}.")


def verify_infinite_families(max_n: int = 20) -> None:
    print(f"\n=== 3. Independent Exact Bareiss Replay Across ALL n = 1..{max_n} (Non-2^k Included) ===")
    cases = [
        ("Supercritical (e=1, r=2, asym)", 1, 4, 3, 1, 3, 5),
        ("Supercritical (e=2, r=3, asym)", 2, 8, 5, -3, 9, 13),
        ("Supercritical (e=3, r=5, asym)", 3, 32, 9, 1, 9, 17),
        ("Critical I    (e=1, r=1, pure)", 1, 2, 3, 0, 1, 1),
        ("Critical I    (e=1, r=1, asym)", 1, 2, 3, 1, 3, 5),
        ("Critical I    (e=1, r=1, neg )", 1, -6, 7, 2, -1, 3),
        ("Critical II   (e=2, r=2, pure)", 2, 4, 5, 0, 1, 1),
        ("Critical II   (e=2, r=2, asym)", 2, 4, 5, 1, 5, 9),
        ("Critical II   (e=2, r=2, neg )", 2, -12, -3, -1, 5, 13),
    ]
    for label, e, a, q, lam, c, d in cases:
        # Check n = 1
        d1 = det_bareiss(full_hybrid_matrix(a, q, lam, c, d, 1))
        assert d1 == 2 + 2 * lam
        odds = []
        for n in range(2, max_n + 1):
            M = full_hybrid_matrix(a, q, lam, c, d, n)
            det_val = det_bareiss(M)
            v = v2_int(det_val)
            expected = e * pop_sum(n) - e
            assert v == expected, f"Mismatch in {label} at n={n}: got v2={v}, expected {expected}"
            if n <= 6:
                odds.append(det_val >> v)
        print(f"  PASS {label:32s}: v2(det M_n) = {e}*S(n)-{e} for ALL n=2..{max_n}; odd(n=2..6)={odds}")

    # Verify Lean concrete non-vacuity witnesses
    assert det_bareiss(full_hybrid_matrix(2, 3, 1, 3, 5, 4)) == 8 * 149
    assert det_bareiss(full_hybrid_matrix(4, 5, 1, 5, 9, 4)) == 64 * (-171)
    print("  PASS: Lean concrete odd-part witnesses det M_4 = 8*149 and det M_4 = 64*(-171) matched exactly.")


def verify_sharpness_and_phase_diagram() -> None:
    print("\n=== 4. Sharpness & Phase-Transition Breakdown Counterexamples ===")

    # S1: Odd a (r = 0) fails at n = 2 for all odd (a, q)
    for a in [-3, -1, 1, 3, 5, 7]:
        for q in [-5, -1, 3, 5, 9]:
            d2 = det_bareiss(full_hybrid_matrix(a, q, 0, 1, 1, 2))
            assert d2 % 4 == 0, f"Expected 4 | det N_2({a},{q}), got {d2}"
    print("  PASS S1 (r = 0, odd a): 4 | det N_2(a, q) for all 30 tested odd (a, q) pairs (breaks v2 = 0).")

    # S2: Exact singularity at (e=2, r=1) -> det N_4(2, 5) = 0
    d_sing = det_bareiss(full_hybrid_matrix(2, 5, 0, 1, 1, 4))
    assert d_sing == 0
    print(f"  PASS S2 (e = 2, r = 1): det N_4(2, 5) = {d_sing} (exact singularity!).")

    # S3: Infinite breakdown line r = 2e - 2 for e = 3, 4, 5, 6 across odd units
    for e in [3, 4, 5, 6]:
        r = 2 * e - 2
        for ua in [1, 3, -1, 5]:
            for uq in [1, 3, -1, 5]:
                a = (1 << r) * ua
                q = 1 + (1 << e) * uq
                d4 = det_bareiss(full_hybrid_matrix(a, q, 0, 1, 1, 4))
                v = v2_int(d4)
                assert v is None or v >= 3 * e + 1, f"Expected failure at e={e}, r={r}, ua={ua}, uq={uq}: v={v}"
    print("  PASS S3 (r = 2e - 2, e = 3..6): 2^(3e+1) | det N_4(a, q) across all 64 odd-unit combinations.")

    # S4: Odd perturbation multiple breaks invariance at n = 3
    M_odd_pert = [
        [(4 ** v2_succ(i ^ j)) + (3 ** pop(i & j)) + (3 ** pop(bit_diff(j, i))) * (5 ** pop(i & j))
         for j in range(3)]
        for i in range(3)
    ]
    d_odd_pert = det_bareiss(M_odd_pert)
    assert v2_int(d_odd_pert) == 2 and pop_sum(3) - 1 == 1
    print(f"  PASS S4 (odd perturbation 1*Q(3,5)): det = {d_odd_pert}, v2 = {v2_int(d_odd_pert)} != S(3)-1 = 1.")

    # Compact phase diagram summary for e = 1..5
    print("\n=== 5. Complete (e, r) Phase Diagram Summary (N_n(2^r, 1 + 2^e), n = 2..14) ===")
    for e in range(1, 6):
        q = 1 + (1 << e)
        row_str = []
        for r in range(0, 2 * e + 1):
            a = (1 << r) if r > 0 else 3
            ok = all(v2_int(det_bareiss(full_hybrid_matrix(a, q, 0, 1, 1, n))) == e * pop_sum(n) - e
                     for n in range(2, 15))
            tag = "OK" if ok else "XX"
            row_str.append(f"r={r}:{tag}")
        print(f"  e={e}: " + "  ".join(row_str))


if __name__ == "__main__":
    verify_mobius_identities(24)
    synthesize_and_verify_certificates()
    verify_infinite_families(20)
    verify_sharpness_and_phase_diagram()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED (exit 0).")
