#!/usr/bin/env python3
"""
Exact Pure-Silicon Exploration, Certificate Verification, and Sharpness Audit
for the Exact F_2-Rank & Corank Block-Elimination Automaton Mechanism.

Strictly exact integer / bitmask arithmetic over F_2 (zero floating point).
"""

from __future__ import annotations


def popcount(x: int) -> int:
    return x.bit_count()


def pop_parity(x: int) -> int:
    return x.bit_count() & 1


def gray(m: int) -> int:
    return m ^ (m >> 1)


def ctz(x: int) -> int:
    assert x > 0
    return (x & -x).bit_length() - 1


def f2_rank_bitmasks(rows: list[int]) -> int:
    """Exact Gaussian elimination over F_2 using Python arbitrary-precision bitmasks."""
    basis: list[tuple[int, int]] = []
    for r in rows:
        x = r
        for b, piv in basis:
            if (x >> piv) & 1:
                x ^= b
        if x:
            basis.append((x, x.bit_length() - 1))
    return len(basis)


def build_rows(fn, n: int) -> list[int]:
    rows = []
    for i in range(n):
        mask = 0
        for j in range(n):
            if fn(i, j):
                mask |= (1 << j)
        rows.append(mask)
    return rows


def brute_ker_count(rows: list[int], n: int) -> int:
    """Exact brute-force enumeration of all 2^n vectors v in F_2^n with M * v = 0."""
    cnt = 0
    for v in range(1 << n):
        ok = True
        for r in rows:
            if (r & v).bit_count() & 1:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


# --- Matrix families ---

def M0(i: int, j: int) -> int:
    """Carry-free XOR-sum parity matrix (carry-in c = 0)."""
    return pop_parity((i + j) & (i ^ j))


def M1(i: int, j: int) -> int:
    """Carry-in c = 1 companion matrix."""
    return pop_parity((i + j + 1) & (i ^ j))


def D_mat(i: int, j: int) -> int:
    """Carry-defect matrix D(i,j) = M0(i,j) ^ M1(i,j) = ctz((i ^ j) + 1) mod 2."""
    return ctz((i ^ j) + 1) & 1


def Dbar_mat(i: int, j: int) -> int:
    """Complement carry-defect matrix Dbar(i,j) = D(i,j) ^ 1."""
    return D_mat(i, j) ^ 1


def H_mat(d: int):
    """Induced hypercube adjacency (d=0) and closed-neighborhood (d=1) over F_2."""
    def fn(i: int, j: int) -> int:
        val = 1 if popcount(i ^ j) == 1 else 0
        if d and i == j:
            val ^= 1
        return val
    return fn


# --- Closed-form / Automaton predictors ---

def m0_nullity_formula(n: int) -> int:
    if n == 0:
        return 0
    if n == 1:
        return 1
    return popcount(gray(n - 1)) - 1


def hc_nullity_automaton(d: int, n: int) -> int:
    if n == 0:
        return 0
    if n == 1:
        return 1 - d
    k = n.bit_length() - 1
    r = n - (1 << k)
    if (k + d) % 2 == 1:
        return r
    half = 1 << (k - 1)
    if r <= half:
        return half - r
    return hc_nullity_automaton(d, r - half)


def hc0_invertible_base4_dfa(n: int) -> bool:
    """
    Exact base-4 regular language acceptor for invertibility of H^(0)_n:
    n == 0, or n is even and n/2 in base 4 matches (0|3)* (1|eps) 0*.
    """
    if n == 0:
        return True
    if n % 2 == 1:
        return False
    m = n // 2
    # Strip trailing base-4 zeros
    while m > 0 and (m % 4) == 0:
        m //= 4
    # Lowest nonzero base-4 digit may be 1 or 3
    if (m % 4) not in (1, 3):
        return False
    m //= 4
    # All higher base-4 digits must be in {0, 3}
    while m > 0:
        if (m % 4) not in (0, 3):
            return False
        m //= 4
    return True


def main() -> None:
    print("=================================================================")
    print("EXACT PURE-SILICON VERIFICATION SUITE (ZERO FLOATING POINT)")
    print("=================================================================")

    # 1. Verify D(i,j) == M0(i,j) ^ M1(i,j)
    for i in range(128):
        for j in range(128):
            assert D_mat(i, j) == (M0(i, j) ^ M1(i, j))
    print("[PASS] Identity D(i,j) = M0(i,j) XOR M1(i,j) = ctz((i^j)+1) mod 2 for all 0<=i,j<128.")

    # 2. Verify Theorem 1: M0(n) Gray-code bit-transition nullity + power-of-2 invertibility
    N1 = 150
    for n in range(N1 + 1):
        rows = build_rows(M0, n)
        rk = f2_rank_bitmasks(rows)
        nu = n - rk
        pred_nu = m0_nullity_formula(n)
        assert nu == pred_nu, f"M0 mismatch at n={n}: got {nu}, expected {pred_nu}"
        if n >= 1:
            is_pow2 = (n & (n - 1)) == 0 and n >= 2
            assert (nu == 0) == is_pow2, f"Power-of-2 invertibility failed at n={n}"
        if n <= 12:
            kc = brute_ker_count(rows, n)
            assert kc == (1 << nu), f"M0 brute kerCount failed at n={n}: {kc} != 2^{nu}"
    print(f"[PASS] Theorem 1 (M0 Gray-code nullity & 2^k invertibility): exact match for all n = 0..{N1}, brute-force 2^n kernel count verified for n = 0..12.")

    # 3. Verify explicit 2-bit isotropic witness x = e_0 ^ e_{2^k} for M0(m) x = 1_m
    for m in range(2, N1 + 1):
        k = (m - 1).bit_length() - 1
        p = 1 << k
        assert 0 < p < m
        for i in range(m):
            assert (M0(i, 0) ^ M0(i, p)) == 1, f"Witness failed at m={m}, i={i}, p={p}"
    print(f"[PASS] Explicit 2-bit isotropic witness x = e_0 XOR e_{{2^k}} satisfies M0(m) x = 1_m and 1^T x = 0 for all m = 2..{N1}.")

    # 4. Verify Theorem 2: Dbar_{2^d}^2 = I, Dbar_n invertible, nu(D_n) = n mod 2
    for d in range(8):
        sz = 1 << d
        rows = build_rows(Dbar_mat, sz)
        # Check Dbar^2 = I (symmetric, so entry (i,j) of Dbar^2 is popcount(rows[i] & rows[j]) & 1)
        for i in range(sz):
            for j in range(sz):
                prod = (rows[i] & rows[j]).bit_count() & 1
                assert prod == (1 if i == j else 0), f"Dbar^2 != I at d={d}, ({i},{j})"
    for n in range(N1 + 1):
        rows_db = build_rows(Dbar_mat, n)
        rows_d = build_rows(D_mat, n)
        assert f2_rank_bitmasks(rows_db) == n, f"Dbar_{n} not invertible"
        assert f2_rank_bitmasks(rows_d) == 2 * (n // 2), f"D_{n} rank wrong"
        if n <= 12:
            assert brute_ker_count(rows_db, n) == 1
            assert brute_ker_count(rows_d, n) == (1 << (n & 1))
    print(f"[PASS] Theorem 2 (Dbar_{{2^d}}^2 = I for d=0..7; rank(Dbar_n) = n, rank(D_n) = 2*floor(n/2) for n = 0..{N1}).")

    # 5. Verify Theorem 3: Hypercube H^(0)_n and H^(1)_n MSB Corank Automaton + Base-4 DFA
    N3 = 160
    for d in (0, 1):
        fn = H_mat(d)
        for n in range(N3 + 1):
            rows = build_rows(fn, n)
            rk = f2_rank_bitmasks(rows)
            nu = n - rk
            pred_nu = hc_nullity_automaton(d, n)
            assert nu == pred_nu, f"H^({d}) mismatch at n={n}: got {nu}, expected {pred_nu}"
            if d == 0:
                assert (nu == 0) == hc0_invertible_base4_dfa(n), f"Base-4 DFA mismatch at n={n}"
            if n <= 12:
                assert brute_ker_count(rows, n) == (1 << nu)
    print(f"[PASS] Theorem 3 (H^(0)_n and H^(1)_n MSB Corank Automaton + Base-4 Invertibility DFA): exact match for all n = 0..{N3}, brute-force 2^n kernel count verified for n = 0..12.")

    # 6. Sharpness / Falsification Witnesses
    print("\n--- SHARPNESS & FALSIFICATION COUNTEREXAMPLES ---")
    # (a) Carry-in c=0 -> c=1 collapses Gray-code tower to period-2 {1, 2}
    for n in range(1, 65):
        nu_m1 = n - f2_rank_bitmasks(build_rows(M1, n))
        assert nu_m1 == 2 - (n & 1)
    nu_m0_11 = 11 - f2_rank_bitmasks(build_rows(M0, 11))
    nu_m1_11 = 11 - f2_rank_bitmasks(build_rows(M1, 11))
    print(f"[SHARP 1] Carry-in c=0 vs c=1: at n=11, nu(M0)={nu_m0_11} (popcount(gray(10))-1=3) vs nu(M1)={nu_m1_11} (collapses to 2-(n mod 2) for all n=1..64).")

    # (b) Bitwise AND -> OR breaks Theorem 1 at n=4
    fn_or = lambda i, j: pop_parity((i + j) | (i ^ j))
    nu_or_4 = 4 - f2_rank_bitmasks(build_rows(fn_or, 4))
    assert nu_or_4 == 2 and m0_nullity_formula(4) == 0
    print(f"[SHARP 2] AND -> OR perturbation: popcount((i+j)|(i^j)) mod 2 has nu(4)={nu_or_4} != 0 = nu(M0(4)).")

    # (c) Boundary n=1 of Theorem 1
    nu_m0_1 = 1 - f2_rank_bitmasks(build_rows(M0, 1))
    assert nu_m0_1 == 1 and popcount(gray(0)) == 0
    print(f"[SHARP 3] n >= 2 lower-bound sharpness: at n=1, nu(M0(1))={nu_m0_1} while popcount(gray(0))=0.")

    # (d) Hamming distance 1 -> 2 breaks hypercube involutive automaton at n=4
    fn_d2 = lambda i, j: 1 if popcount(i ^ j) == 2 else 0
    nu_d2_4 = 4 - f2_rank_bitmasks(build_rows(fn_d2, 4))
    assert nu_d2_4 == 0 and hc_nullity_automaton(0, 4) == 2
    print(f"[SHARP 4] Hamming distance 1 -> 2 perturbation: nu(Q^(2)_4)={nu_d2_4} != 2 = nu(H^(0)_4).")

    # Summary sample table
    print("\n--- SAMPLE EXACT TABLE (n = 0..24) ---")
    print("  n | M0_rk M0_nu gray(n-1) | D_rk Dbar_rk | H0_rk H0_nu | H1_rk H1_nu")
    for n in range(25):
        m0_nu = m0_nullity_formula(n)
        g_str = f"{gray(n-1):05b}" if n >= 1 else "  -  "
        h0_nu = hc_nullity_automaton(0, n)
        h1_nu = hc_nullity_automaton(1, n)
        print(f" {n:2d} |  {n-m0_nu:2d}    {m0_nu:2d}     {g_str}   |  {2*(n//2):2d}    {n:2d}    |  {n-h0_nu:2d}    {h0_nu:2d}   |  {n-h1_nu:2d}    {h1_nu:2d}")

    print("\nALL CHECKS PASSED WITH ZERO ERRORS.")


if __name__ == "__main__":
    main()
