#!/usr/bin/env python3
"""
Pure Silicon Binary Math — Thread 3 (specmat-2)
Independent Exact-Integer Replay, Certificate Synthesis, Verification,
and Sharpness Counterexample Suite for the:
  Walsh-Hadamard & Boolean-Lattice Möbius Transfer-Operator Diagonalization Engine

STRICT ZERO-FLOATING-POINT ARITHMETIC:
  All matrix determinants, WHT transforms, Boolean Möbius transforms, transfer-operator
  products, and quadratic-form witnesses use exact Python `int` and `fractions.Fraction`.
"""

import math
from collections import Counter
from fractions import Fraction


def popcount(x: int) -> int:
    return x.bit_count()


def runs(z: int) -> int:
    """Number of maximal 1-bit runs (0 -> 1 transitions) in binary word z."""
    return popcount(z & ~(z >> 1))


def falls(z: int) -> int:
    """Number of internal 1 -> 0 bit-falls in binary word z."""
    return runs(z) - (z & 1)


def trans_kernel(z: int, q: int, s: int) -> int:
    """2-parameter binary-transition kernel: f_{q,s}(z) = q^(rises z) * s^(falls z)."""
    return (q ** runs(z)) * (s ** falls(z))


def runs_kernel(z: int, q: int) -> int:
    """1-parameter binary-runs kernel: f_q(z) = q^(runs z) = f_{q,1}(z)."""
    return q ** runs(z)


def gray_code(w: int) -> int:
    return w ^ (w >> 1)


def inv_gray(u: int) -> int:
    """Exact inverse Gray code G^{-1}(u)."""
    w = u
    sh = 1
    while w >> sh:
        w ^= (w >> sh)
        sh <<= 1
    return w


def pell_q(m: int, q: int) -> int:
    """q-Pell-Lucas sequence: pellQ(0,q)=1, pellQ(1,q)=1, pellQ(n+2,q)=2*pellQ(n+1,q)+(q-1)*pellQ(n,q)."""
    if m <= 1:
        return 1
    a, b = 1, 1
    for _ in range(m - 1):
        a, b = b, 2 * b + (q - 1) * a
    return b


def jacobsthal(k: int) -> int:
    """J_k = (2^k - (-1)^k) / 3."""
    return ((1 << k) - ((-1) ** k)) // 3


def trans_exp(k: int) -> int:
    """E_k = ((3k - 2)*2^k + 2*(-1)^k) / 9."""
    return ((3 * k - 2) * (1 << k) + 2 * ((-1) ** k)) // 9


def runs_exp(k: int) -> int:
    """E_k + J_k = ((3k + 1)*2^k - (-1)^k) / 9."""
    return ((3 * k + 1) * (1 << k) - ((-1) ** k)) // 9


def wht_exact(f: list[int]) -> list[int]:
    """Exact integer Walsh-Hadamard transform (in-place butterfly, zero floats)."""
    a = list(f)
    n = len(a)
    h = 1
    while h < n:
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                u, v = a[j], a[j + h]
                a[j] = u + v
                a[j + h] = u - v
        h *= 2
    return a


def mobius_down_exact(g: list[int]) -> list[int]:
    """Exact integer downward Boolean Möbius transform (for AND-lattice)."""
    a = list(g)
    n = len(a)
    h = 1
    while h < n:
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                a[j + h] -= a[j]
        h *= 2
    return a


def mobius_up_exact(g: list[int]) -> list[int]:
    """Exact integer upward Boolean Möbius transform (for OR-lattice)."""
    a = list(g)
    n = len(a)
    h = 1
    while h < n:
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                a[j] -= a[j + h]
        h *= 2
    return a


def exact_det(M: list[list[int]]) -> int:
    """Exact rational Gaussian elimination determinant (returns exact Python int)."""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if A[r][i] != 0), None)
        if piv is None:
            return 0
        if piv != i:
            A[i], A[piv] = A[piv], A[i]
            det = -det
        det *= A[i][i]
        for r in range(i + 1, n):
            factor = A[r][i] / A[i][i]
            if factor != 0:
                for c in range(i + 1, n):
                    A[r][c] -= factor * A[i][c]
    assert det.denominator == 1
    return det.numerator


def mat_mul_2x2(A, B):
    return [
        [A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]],
        [A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]],
    ]


def verify_scaled_dihedral_certificate():
    """Step 1: Verify the finite 2x2 Scaled-Dihedral Certificate across integer pairs (q, s)."""
    print("=== 1. FINITE 2x2 SCALED-DIHEDRAL CERTIFICATE CHECK ===")
    for q in (-3, -1, 0, 1, 2, 3, 5):
        for s in (-2, 0, 1, 3):
            T0 = [[1, 0], [s, 0]]
            T1 = [[0, q], [0, 1]]
            A = [[T0[i][j] + T1[i][j] for j in range(2)] for i in range(2)]
            S = [[T0[i][j] - T1[i][j] for j in range(2)] for i in range(2)]
            Abar = [[1, -q], [-s, 1]]
            c = 1 - q * s
            cI = [[c, 0], [0, c]]
            assert mat_mul_2x2(S, S) == cI
            assert mat_mul_2x2(A, Abar) == cI
            assert mat_mul_2x2(Abar, A) == cI
            assert mat_mul_2x2(S, A) == mat_mul_2x2(Abar, S)
    print("  PASS: S^2 = (1-qs)I, A*Abar = Abar*A = (1-qs)I, S*A = Abar*S verified for all 28 (q, s) pairs.")


def verify_theorem_1_xor_spectrum_and_det():
    """Step 2: Independently verify Theorem 1 (Inverse-Gray q-Pell-Lucas Spectrum, CharPoly & Det)."""
    print("\n=== 2. THEOREM 1: XOR-CONVOLUTION INVERSE-GRAY q-PELL-LUCAS SPECTRUM & DETERMINANT ===")
    # 2a. Full spectrum up to k = 10 (1024 frequencies) across multiple q
    for q in (-3, -1, 0, 1, 2, 3, 5):
        for k in range(1, 11):
            N = 1 << k
            vals = [runs_kernel(z, q) for z in range(N)]
            W = wht_exact(vals)
            for u in range(N):
                v = popcount(inv_gray(u))
                r = min(v, k + 1 - v)
                pred = ((1 - q) ** r) * pell_q(k + 1 - 2 * r, q)
                assert W[u] == pred, f"WHT mismatch q={q} k={k} u={u}: got {W[u]} vs {pred}"
    print("  PASS: Exact WHT spectrum matches (1-q)^r * pellQ(k+1-2r, q) for all q in {-3,-1,0,1,2,3,5}, k=1..10 (up to N=1024).")

    # 2b. Pascal multiplicity law & direct exact Gaussian-elimination determinant + charpoly check for k=1..5
    for q in (-1, 0, 1, 2, 3):
        for k in range(1, 6):
            N = 1 << k
            M = [[runs_kernel(x ^ y, q) for y in range(N)] for x in range(N)]
            det_direct = exact_det(M)
            # Closed-form Pascal-multiplicity product
            det_closed = 1
            for r in range(0, (k + 1) // 2 + 1):
                mult = math.comb(k, r) if 2 * r == k + 1 else math.comb(k + 1, r)
                eig = ((1 - q) ** r) * pell_q(k + 1 - 2 * r, q)
                det_closed *= eig ** mult
            assert det_direct == det_closed, f"XOR det mismatch q={q} k={k}: {det_direct} vs {det_closed}"
            # Also check characteristic polynomial at lambda = 5 for k <= 4
            if k <= 4:
                lam = 5
                Lmat = [[(lam if x == y else 0) - M[x][y] for y in range(N)] for x in range(N)]
                cp_direct = exact_det(Lmat)
                cp_closed = 1
                for r in range(0, (k + 1) // 2 + 1):
                    mult = math.comb(k, r) if 2 * r == k + 1 else math.comb(k + 1, r)
                    eig = ((1 - q) ** r) * pell_q(k + 1 - 2 * r, q)
                    cp_closed *= (lam - eig) ** mult
                assert cp_direct == cp_closed
            if q == 2:
                print(f"    q=2, k={k} ({N}x{N}): det(M_k(2)) = {det_direct}")
            if q == -1:
                print(f"    q=-1, k={k} ({N}x{N}): det(M_k(-1)) = {det_direct} ({'singular (odd k)' if k % 2 == 1 else 'bent power-of-2'})")
    print("  PASS: Direct Gaussian-elimination det & charpoly match closed-form Pascal formula for k=1..5 (up to 32x32).")


def verify_theorem_2_and_lattice_det_and_unimodularity():
    """Step 3: Independently verify Theorem 2 (2-Parameter AND-Lattice Det, Unimodularity, Non-PosDef)."""
    print("\n=== 3. THEOREM 2: 2-PARAMETER BINARY-TRANSITION AND-LATTICE DETERMINANT & UNIMODULARITY ===")
    # 3a. Direct exact Gaussian elimination for k=1..5 across (q, s)
    for q, s in ((2, 1), (3, 1), (-1, 1), (0, 1), (1, 1), (2, 3), (3, -2), (5, 2), (1, 2)):
        for k in range(1, 6):
            N = 1 << k
            A = [[trans_kernel(x & y, q, s) for y in range(N)] for x in range(N)]
            det_direct = exact_det(A)
            pred = (q - 1) if k == 1 else -((q * s - 1) ** trans_exp(k)) * ((q - 1) ** jacobsthal(k))
            assert det_direct == pred, f"AND det mismatch q={q} s={s} k={k}: {det_direct} vs {pred}"
            if (q, s) in ((2, 1), (2, 3)) and k <= 4:
                print(f"    (q={q}, s={s}), k={k} ({N}x{N}): det(A_k) = {det_direct}")
    print("  PASS: Direct exact Gaussian-elimination det(A_k(q,s)) matches closed form for all 9 (q,s) pairs, k=1..5.")

    # 3b. Möbius transform product up to k = 12 (4096 x 4096) for unimodular q=2,s=1 and (q=2,s=3)
    for k in range(2, 13):
        N = 1 << k
        MD_unimod = mobius_down_exact([runs_kernel(z, 2) for z in range(N)])
        assert set(MD_unimod) == {-1, 1}
        prod = 1
        for x in MD_unimod:
            prod *= x
        assert prod == -1
    print("  PASS: A_k(2) = [2^runs(x & y)] has Mobius entries strictly in {-1, +1} and det = -1 for all k=2..12 (up to 4096x4096).")

    # 3c. OR-lattice duality check for k=1..4
    for q in (2, 3):
        for k in range(1, 5):
            N = 1 << k
            O = [[runs_kernel(x | y, q) for y in range(N)] for x in range(N)]
            MU = mobius_up_exact([runs_kernel(z, q) for z in range(N)])
            prod = 1
            for x in MU:
                prod *= x
            assert exact_det(O) == prod
    print("  PASS: OR-lattice det(g(x | y)) == prod(mobius_up(g)) verified for k=1..4.")


def verify_sharpness_and_counterexamples():
    """Step 4: Explicit sharpness counterexamples outside theorem hypotheses."""
    print("\n=== 4. SHARPNESS & BOUNDARY COUNTEREXAMPLES ===")

    # Counterexample 1: Breaking k >= 2 in Non-Positive-Definiteness Barrier
    # At k = 1, q = 2: A_1(2) = [[1, 1], [1, 2]] has Mobius entries [1, 1] > 0 -> strictly positive definite!
    MD_k1 = mobius_down_exact([runs_kernel(z, 2) for z in range(2)])
    assert MD_k1 == [1, 1]
    print(f"  Sharpness 1 (k=1 vs k>=2): A_1(2) Mobius diagonal = {MD_k1} (strictly positive definite, det = +1);")
    # At k = 2, q = 2: Mobius diagonal at z=3 is -1, witness v = mobius row 3 = [1, -1, -1, 1] gives v^T A_2(2) v = -1 < 0!
    A2 = [[runs_kernel(x & y, 2) for y in range(4)] for x in range(4)]
    v_wit = [1, -1, -1, 1]  # (-1)^popcount(3 ^ x)
    qf = sum(v_wit[x] * A2[x][y] * v_wit[y] for x in range(4) for y in range(4))
    assert qf == -1
    print(f"    while at k=2, q=2: witness v = {v_wit} gives v^T A_2(2) v = {qf} < 0 (barrier is sharp at k >= 2).")

    # Counterexample 2: Breaking the trace-zero Scaled-Dihedral condition (a = 1 -> a = 2)
    # f(z) = 2^popcount(z) * 2^runs(z) has T0 - T1 = [[1, -4], [1, -2]], trace = -1 != 0 -> S^2 is NOT scalar!
    k = 3
    broken_vals = [(2 ** popcount(z)) * (2 ** runs(z)) for z in range(1 << k)]
    W_broken = wht_exact(broken_vals)
    MD_broken = mobius_down_exact(broken_vals)
    assert popcount(inv_gray(2)) == popcount(inv_gray(5)) == 2
    assert W_broken[2] != W_broken[5]
    det_broken_and = 1
    for x in MD_broken:
        det_broken_and *= x
    assert det_broken_and == -1215
    print(f"  Sharpness 2 (breaking trace-zero dihedral condition a=1 -> a=2, f(z)=2^popcount(z)*2^runs(z)):")
    print(f"    u1=2 (010) and u2=5 (101) share popcount(G^-1(u))=2, yet WHT[2]={W_broken[2]} != WHT[5]={W_broken[5]}.")
    print(f"    AND-lattice Mobius spectrum = {MD_broken}, det = {det_broken_and} (new prime factor 5, non-unimodular).")

    # Counterexample 3: Singularity at q = 1 (and at q = 1, s = 2 in 2-parameter family)
    A2_sing = [[trans_kernel(x & y, 1, 2) for y in range(4)] for x in range(4)]
    assert exact_det(A2_sing) == 0
    print(f"  Sharpness 3 (boundary singularity q=1, s=2): qs-1 = 1 is a unit, yet q-1 = 0 forces det(A_2(1,2)) = 0.")

    # Counterexample 4: Odd vs even k at q = -1 (Rudin-Shapiro bent dichotomy)
    for k in (2, 3, 4, 5):
        W = wht_exact([runs_kernel(z, -1) for z in range(1 << k)])
        if k % 2 == 0:
            assert set(abs(x) for x in W) == {1 << (k // 2)}
        else:
            assert 0 in W
    print("  Sharpness 4 (Rudin-Shapiro q=-1 parity dichotomy): even k has flat bent spectrum |lambda|=2^(k/2); odd k is always singular.")


if __name__ == "__main__":
    verify_scaled_dihedral_certificate()
    verify_theorem_1_xor_spectrum_and_det()
    verify_theorem_2_and_lattice_det_and_unimodularity()
    verify_sharpness_and_counterexamples()
    print("\nALL EXACT-INTEGER CHECKS PASSED (ZERO FLOATS).")
