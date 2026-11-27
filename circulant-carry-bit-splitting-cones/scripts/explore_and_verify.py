#!/usr/bin/env python3
"""
Pure-Silicon Exact Integer Explorer & Independent Verifier (adic-16)
====================================================================
Zero floating-point arithmetic anywhere (only Python exact `int`).

Verifies both reusable infinite proof mechanisms and all concrete theorems,
sharpness counterexamples, and mutation rejections:
  1. Engine I (Involutive Circulant Base-2^m Carry-Transfer Engine):
     - Exact circulant & rev-Hermitian structure of H_m over Z[Z/mZ] for m=1..7.
     - Universal All-m, All-k Palindromic Symmetry:
         #{n < 2^(m*k) : s2((2^m-1)*n) == r (mod m)} == #{n < 2^(m*k) : s2((2^m-1)*n) == -r (mod m)}.
     - Exact 3-orbit reduction for m=3 (c=7): 3-term recurrence
         D3(k+3) = 4*D3(k+2) + 4*D3(k+1) - D3(k), D3(k) >= 4^k > 0.
     - Exact orbit-lumped sharp phase-transition refutations of mod-m 0-dominance:
         m=6, c=63, k=12 (N = 2^72): c0 - c2 = -4543260596431345 < 0 (after positive for all k <= 11!).
         m=7, c=127, k=6 (N = 2^42): c0 - c3 = -8839825770 < 0.
     - Sharpness witnesses: exponent L not divisible by m (m=3, L=4), non-Mersenne c=5,
       and failure of naive involutions n -> 2^(mk)-n and n -> 2^(mk)-1-n.
  2. Engine II (2-Window Bit-Splitting Polyhedral Cone Certificate Engine):
     - Pure-data row-scaled Farkas cone verifier (denom_i * (C * T_b)_i == (U_b * C)_i,
       U_b >= 0, row_sum(U_b, i) >= 1, (C * W(1))_i >= 1).
     - Exact certificates & independent brute-force verification up to N = 50,000 for:
         * Nonlinear Bitwise-OR Evil Dominance: s2(n | 5n) mod 2 (q=18, max denom=6)
           + Exact Tribonacci Dyadic Law: sum_{n < 2^k} (-1)^s2(n | 5n) = 2 * Trib(k).
         * Nonlinear Bitwise-OR Evil Dominance: s2(n | 3n) mod 2 (q=27, max denom=2062).
         * Classical Newman Benchmark: s2(3n) mod 2 (q=9, max denom=3).
     - 3-way sharpness counterexamples (| -> ^, | -> &, c in {3,5} -> c=7) + negative mutation tests.
"""

from typing import Callable, List, Tuple


def popcount(n: int) -> int:
    return n.bit_count()


# ============================================================================
# PART 1: INVOLUTIVE CIRCULANT BASE-2^m CARRY-TRANSFER ENGINE
# ============================================================================

def gr_add(a: List[int], b: List[int]) -> List[int]:
    return [x + y for x, y in zip(a, b)]


def gr_rev(a: List[int]) -> List[int]:
    m = len(a)
    return [a[(m - r) % m] for r in range(m)]


def gr_shift(a: List[int], s: int) -> List[int]:
    m = len(a)
    s %= m
    return [a[(r - s) % m] for r in range(m)]


def gr_mul(a: List[int], b: List[int]) -> List[int]:
    m = len(a)
    out = [0] * m
    for i in range(m):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(m):
            out[(i + j) % m] += ai * b[j]
    return out


def build_mersenne_H(m: int) -> List[List[List[int]]]:
    """
    Build the (2^m - 1) x (2^m - 1) circulant carry-transfer matrix H_m over Z[Z/mZ]:
      H_m[g][gp] = delta_{g, gp} * e_0 + e_{s2((g - gp) mod (2^m - 1)) mod m}.
    """
    n = (1 << m) - 1
    H = [[[0] * m for _ in range(n)] for _ in range(n)]
    for g in range(n):
        for gp in range(n):
            if g == gp:
                H[g][gp][0] = 2
            else:
                sh = popcount((g - gp) % n) % m
                H[g][gp][sh] = 1
    return H


def build_mersenne_v0(m: int) -> List[List[int]]:
    n = (1 << m) - 1
    v0 = [[0] * m for _ in range(n)]
    for g in range(n):
        v0[g][popcount(g) % m] = 1
    return v0


def verify_H_structural_axioms(m: int) -> None:
    """Verify exact rev-Hermiticity and row-0 telescoping axioms for H_m."""
    n = (1 << m) - 1
    H = build_mersenne_H(m)
    v0 = build_mersenne_v0(m)
    for g in range(n):
        for gp in range(n):
            assert H[gp][g] == gr_rev(H[g][gp]), f"Not rev-Hermitian at m={m}, ({g},{gp})"
    for gp in range(n):
        expected = gr_rev(v0[gp])
        if gp == 0:
            expected[0] += 1
        assert H[0][gp] == expected, f"Row-0 telescoping failed at m={m}, gp={gp}"


def direct_mersenne_hist(m: int, k: int, gamma: int = 0) -> List[int]:
    c = (1 << m) - 1
    N = 1 << (m * k)
    cnt = [0] * m
    for n in range(N):
        cnt[popcount(c * n + gamma) % m] += 1
    return cnt


def iter_mersenne_H(m: int, k: int) -> List[List[int]]:
    n = (1 << m) - 1
    v = build_mersenne_v0(m)
    for _ in range(k):
        nv = [[0] * m for _ in range(n)]
        for g in range(n):
            for gp in range(n):
                if g == gp:
                    for r in range(m):
                        nv[g][r] += 2 * v[gp][r]
                else:
                    sh = popcount((g - gp) % n) % m
                    for r in range(m):
                        nv[g][(r + sh) % m] += v[gp][r]
        v = nv
    return v


def build_cyclic_orbits(m: int) -> Tuple[List[List[int]], List[List[List[int]]], List[List[int]]]:
    """
    Exact orbit lumping of H_m under the cyclic bit-rotation g -> (2*g) mod (2^m - 1).
    Returns (orbits, M_orb, v0_orb) and verifies exact lumpability on every orbit member.
    """
    n = (1 << m) - 1
    seen = {}
    orbits: List[List[int]] = []
    for g in range(n):
        if g in seen:
            continue
        orb = []
        x = g
        while x not in seen:
            seen[x] = len(orbits)
            orb.append(x)
            x = (2 * x) % n
        orbits.append(orb)
    O = len(orbits)
    M_orb = [[[0] * m for _ in range(O)] for _ in range(O)]
    for i in range(O):
        g0 = orbits[i][0]
        for j in range(O):
            for gp in orbits[j]:
                if g0 == gp:
                    M_orb[i][j][0] += 2
                else:
                    sh = popcount((g0 - gp) % n) % m
                    M_orb[i][j][sh] += 1
        # Verify exact invariance for every element of orbits[i]
        for g in orbits[i][1:]:
            row = [[0] * m for _ in range(O)]
            for j in range(O):
                for gp in orbits[j]:
                    if g == gp:
                        row[j][0] += 2
                    else:
                        sh = popcount((g - gp) % n) % m
                        row[j][sh] += 1
            assert row == M_orb[i], f"Orbit lumping failed at m={m}, orbit={i}, g={g}"
    v0_orb = [[0] * m for _ in range(O)]
    for i in range(O):
        w = popcount(orbits[i][0]) % m
        for g in orbits[i]:
            assert popcount(g) % m == w
        v0_orb[i][w] = 1
    return orbits, M_orb, v0_orb


def iter_orbit_matrix(m: int, M_orb: List[List[List[int]]], v0_orb: List[List[int]], k: int) -> List[List[int]]:
    O = len(v0_orb)
    v = [row[:] for row in v0_orb]
    for _ in range(k):
        nv = [[0] * m for _ in range(O)]
        for i in range(O):
            for j in range(O):
                mij = M_orb[i][j]
                vj = v[j]
                for r1 in range(m):
                    c1 = mij[r1]
                    if c1 == 0:
                        continue
                    for r2 in range(m):
                        nv[i][(r1 + r2) % m] += c1 * vj[r2]
        v = nv
    return v


# ============================================================================
# PART 2: 2-WINDOW BIT-SPLITTING POLYHEDRAL CONE CERTIFICATE ENGINE
# ============================================================================

def build_window_system(
    d: int,
    nxt_fn: Callable[[int, int], int],
    out_fn: Callable[[int, int], int],
    base_fn: Callable[[int], int],
) -> Tuple[List[List[int]], List[List[int]], List[int]]:
    """
    Build exact integer 2-window transfer matrices (T0, T1) of size (2d)x(2d)
    and initial vector W(1) = T1 * W(0) for a parity transducer.
    """
    L0 = [[0] * d for _ in range(d)]
    L1 = [[0] * d for _ in range(d)]
    for g in range(d):
        L0[g][nxt_fn(g, 0)] += 1 if (out_fn(g, 0) % 2 == 0) else -1
        L1[g][nxt_fn(g, 1)] += 1 if (out_fn(g, 1) % 2 == 0) else -1
    T0 = [[0] * (2 * d) for _ in range(2 * d)]
    T1 = [[0] * (2 * d) for _ in range(2 * d)]
    for i in range(d):
        for j in range(d):
            T0[i][j] = L0[i][j] + L1[i][j]
            T0[d + i][j] = L1[i][j]
            T0[d + i][d + j] = L0[i][j]
            T1[i][j] = L1[i][j]
            T1[i][d + j] = L0[i][j]
            T1[d + i][d + j] = L0[i][j] + L1[i][j]
    P0 = [0] * d
    P1 = [1 if (base_fn(g) % 2 == 0) else -1 for g in range(d)]
    W0 = P0 + P1
    W1 = [sum(T1[i][j] * W0[j] for j in range(2 * d)) for i in range(2 * d)]
    return T0, T1, W1


def check_cone_cert(
    T0: List[List[int]],
    T1: List[List[int]],
    W1: List[int],
    C: List[List[int]],
    U0: List[List[int]],
    U1: List[List[int]],
    den0: List[int],
    den1: List[int],
) -> bool:
    """
    Pure-integer checker mirroring Lean 4's `checkConeCert`.
    Soundness guarantees: if True, then (C * W(N))_i >= 1 for ALL N >= 1 and ALL i.
    """
    q = len(C)
    dim = len(W1)
    if len(U0) != q or len(U1) != q or len(den0) != q or len(den1) != q:
        return False
    # 1. Base positivity: (C * W(1))_i >= 1
    for i in range(q):
        if sum(C[i][j] * W1[j] for j in range(dim)) < 1:
            return False
    # 2. Row-wise positivity & exact invariance equations for b=0 and b=1
    for T, U, den in [(T0, U0, den0), (T1, U1, den1)]:
        for i in range(q):
            if den[i] <= 0:
                return False
            if any(x < 0 for x in U[i]):
                return False
            if sum(U[i]) <= 0:
                return False
            for col in range(dim):
                lhs = den[i] * sum(C[i][k] * T[k][col] for k in range(dim))
                rhs = sum(U[i][r] * C[r][col] for r in range(q))
                if lhs != rhs:
                    return False
    return True


# Exact certificates (synthesized and verified strictly in exact integer arithmetic)
CERT_OR_MUL5 = {
    "d": 5,
    "den0": [1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1],
    "den1": [1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 2, 6],
    "C": [
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, -1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, -1, 0, 0, 1, 0, 0, 0, 0],
        [1, -1, -1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, -1, 1, 0, 1, -1, 0, 0, 0],
        [0, -1, -1, 1, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 1, -1, -1, 0, 0],
        [2, -2, -1, 2, -1, 0, 0, 0, 0, 0],
        [0, 0, -1, 2, -1, 2, -2, 0, 0, 0],
        [0, -2, -1, 2, -1, 2, 0, 0, 0, 0],
        [0, 0, 0, 2, -1, 2, -2, -1, 0, 0],
        [0, 0, 0, 0, -1, 2, -2, -1, 2, 0],
        [0, 0, 0, 3, -1, 4, -3, -3, 0, 0],
        [0, 0, 0, 0, -1, 4, -3, -3, 3, 0],
        [0, 0, 0, 0, 1, 4, -3, -3, 3, -2],
        [0, 0, 0, 0, -2, 7, -6, -5, 6, 0],
        [0, 0, 0, 0, 1, 7, -6, -5, 6, -3],
        [0, 0, 0, 0, 2, 13, -11, -9, 11, -6],
    ],
    "U0": [
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 2, 0, 0, 4, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 4, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0],
        [0, 0, 2, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 2, 0, 4, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    ],
    "U1": [
        [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 7, 0, 7, 0, 5],
    ],
}

CERT_OR_MUL3 = {
    "d": 3,
    "den0": [1, 1, 2, 1, 3, 2, 16, 8, 1, 10, 1, 2062, 1, 9, 1031, 1, 141, 2, 1, 733, 1, 19, 489, 1, 11, 1797, 13],
    "den1": [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 1, 1, 13, 1, 1, 294, 1, 173, 1, 1, 39],
    "C": [
        [1, 0, 0, 0, 0, 0],
        [1, -1, 0, 0, 0, 0],
        [0, -1, 0, 1, 0, 0],
        [2, -1, 1, 0, 0, 0],
        [0, -1, 1, 2, 0, 0],
        [0, 0, 1, 2, -1, 0],
        [0, -2, 0, 3, 1, 0],
        [0, 0, 0, 3, -1, 0],
        [0, 0, -1, 3, -1, 1],
        [0, 0, 2, 4, -3, -1],
        [0, 0, 0, 4, -3, 1],
        [0, -4, 1, 4, 1, 0],
        [0, 0, -2, 7, -3, 4],
        [0, 0, 3, 7, -3, -1],
        [0, -9, 1, 10, 4, 0],
        [0, 0, -3, 10, -5, 4],
        [0, 0, 8, 15, -9, -4],
        [0, -13, 4, 15, 4, 0],
        [0, 0, -8, 24, -11, 13],
        [0, 0, 9, 24, -11, -4],
        [0, -32, 6, 35, 13, 0],
        [0, 0, -9, 35, -19, 15],
        [0, 0, 26, 54, -29, -13],
        [0, 0, -26, 83, -41, 42],
        [0, -109, 25, 124, 42, 0],
        [0, 0, 84, 191, -99, -42],
        [0, 0, -84, 290, -149, 141],
    ],
    "U0": [
        [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [2, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 16, 0, 8, 0, 0, 0, 0, 0, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 10, 0, 5, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [2480, 64, 0, 2852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 30, 9, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 8, 0, 4, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [418, 3157, 0, 2852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 30, 9, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 0, 0, 140, 0, 0, 0, 0, 20, 30, 0, 0, 0, 0, 7, 0, 0],
        [4, 4, 0, 9, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 544, 0, 0, 0, 0, 187, 493, 0, 0, 0, 0, 291, 0, 0, 0, 0, 34, 0],
        [0, 8, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 47, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 7, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 798, 301, 0, 0, 76, 28, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
        [58, 299, 0, 421, 0, 0, 0, 164, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3696, 4636, 0, 0, 1049, 403, 697, 0],
        [0, 0, 0, 0, 146, 0, 69, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0],
    ],
    "U1": [
        [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 32, 32, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 272, 0, 0, 0, 340, 0, 0, 0, 0, 0, 73, 0, 0, 0, 17],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 380, 0, 0, 0, 0, 0, 129, 0, 0, 0, 0, 0, 167, 0, 0, 0, 67, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148, 90, 0, 0, 31, 4],
    ],
}

CERT_NEWMAN3 = {
    "d": 3,
    "den0": [1, 1, 2, 1, 1, 1, 1, 1, 1],
    "den1": [1, 1, 1, 3, 1, 1, 1, 3, 1],
    "C": [
        [1, 0, 0, 0, 0, 0],
        [1, -1, 0, 0, 0, 0],
        [0, -1, 0, 1, 0, 0],
        [2, -1, -1, 0, 0, 0],
        [0, -1, -1, 2, 0, 0],
        [0, 0, -1, 2, -1, 0],
        [0, 0, 0, 3, -3, 0],
        [0, 0, 1, 3, -3, -1],
        [0, 0, 0, 6, -3, -3],
    ],
    "U0": [
        [0, 1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1, 0, 0, 0, 0],
        [0, 3, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 2, 0, 0, 0, 0, 0, 0],
        [0, 0, 3, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 3, 0, 0, 0, 0],
        [0, 0, 0, 0, 2, 1, 0, 0, 0],
        [0, 0, 6, 0, 0, 0, 1, 0, 0],
    ],
    "U1": [
        [0, 0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 6, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, 0, 3, 0, 0, 2],
        [0, 0, 0, 0, 0, 0, 3, 0, 0],
    ],
}


def main() -> None:
    print("===================================================================")
    print("ADIC-16 PURE-SILICON EXACT INTEGER VERIFICATION SUITE (ZERO FLOATS)")
    print("===================================================================")

    # --- ENGINE I: Involutive Circulant Base-2^m Carry-Transfer Engine ---
    print("\n[1] Engine I: Structural Axioms & Exact Compilation of H_m (m=1..7)")
    for m in range(1, 8):
        verify_H_structural_axioms(m)
    print("  PASS: H_m is rev-Hermitian and satisfies row-0 telescoping for m=1..7.")

    # Verify exact agreement with direct brute-force enumeration for (m, k)
    for m, k in [(2, 4), (3, 3), (4, 2), (5, 2)]:
        h_iter = iter_mersenne_H(m, k)[0]
        h_direct = direct_mersenne_hist(m, k, 0)
        assert h_iter == h_direct, f"Compilation mismatch at m={m}, k={k}"
        assert h_iter == gr_rev(h_iter), f"Palindromy failed at m={m}, k={k}"
        print(f"  PASS: m={m}, k={k} (N=2^{m*k}={1<<(m*k)}): exact hist = {h_iter}, rev-palindromic = True")

    # Verify m=3 exact 3-orbit recurrence D3(k+3) = 4*D3(k+2) + 4*D3(k+1) - D3(k)
    print("\n[2] Theorem 1b: Exact Mod-3 Mersenne Recurrence & Positivity (m=3, c=7)")
    orbs3, M3, v03 = build_cyclic_orbits(3)
    assert len(orbs3) == 3
    D3 = []
    for k in range(12):
        h = iter_orbit_matrix(3, M3, v03, k)[0]
        assert h[1] == h[2]
        d = h[0] - h[1]
        assert d >= (1 << (2 * k))  # 4^k
        D3.append(d)
    for k in range(len(D3) - 3):
        assert D3[k + 3] == 4 * D3[k + 2] + 4 * D3[k + 1] - D3[k]
    print(f"  PASS: 3-orbit reduction verified; D3(0..9) = {D3[:10]}")
    print("  PASS: D3(k+3) = 4*D3(k+2) + 4*D3(k+1) - D3(k) and D3(k) >= 4^k > 0.")

    # Verify sharp phase transition at m=6 (N=2^72) and m=7 (N=2^42)
    print("\n[3] Theorem 1c: Sharp Phase Transition — Exact Mod-m 0-Dominance Breakdown")
    orbs6, M6, v06 = build_cyclic_orbits(6)
    assert len(orbs6) == 13
    for k in range(1, 13):
        h6 = iter_orbit_matrix(6, M6, v06, k)[0]
        assert h6 == gr_rev(h6)
        diffs6 = [h6[0] - h6[r] for r in range(1, 6)]
        if k <= 11:
            assert min(diffs6) > 0
        else:
            assert h6[0] - h6[2] == -4543260596431345
            assert h6[0] - h6[4] == -4543260596431345
            print(f"  PASS: m=6 (c=63, 13 orbits): positive for k=1..11 (up to 2^66), BREAKS at k=12 (N=2^72):")
            print(f"        c0(2^72) - c2(2^72) = {h6[0] - h6[2]} < 0")

    orbs7, M7, v07 = build_cyclic_orbits(7)
    assert len(orbs7) == 19
    h7_6 = iter_orbit_matrix(7, M7, v07, 6)[0]
    assert h7_6 == gr_rev(h7_6)
    assert h7_6[0] - h7_6[3] == -8839825770
    assert h7_6[0] - h7_6[4] == -8839825770
    print(f"  PASS: m=7 (c=127, 19 orbits): BREAKS at k=6 (N=2^42):")
    print(f"        c0(2^42) - c3(2^42) = {h7_6[0] - h7_6[3]} < 0")

    # Verify sharpness counterexamples for Theorem 1 (Palindromy)
    print("\n[4] Engine I Sharpness & Non-Triviality Witnesses")
    cnt_m3_L4 = [0, 0, 0]
    for n in range(16):
        cnt_m3_L4[popcount(7 * n) % 3] += 1
    assert cnt_m3_L4 == [13, 2, 1] and cnt_m3_L4[1] != cnt_m3_L4[2]
    print(f"  PASS: Exponent sharpness (m=3, L=4, 3 nmid 4): hist = {cnt_m3_L4}, c1 != c2")

    cnt_c5_m3 = [0, 0, 0]
    for n in range(8):
        cnt_c5_m3[popcount(5 * n) % 3] += 1
    assert cnt_c5_m3[1] != cnt_c5_m3[2]
    print(f"  PASS: Multiplier sharpness (m=3, c=5 != 2^3-1, N=8): hist = {cnt_c5_m3}, c1 != c2")

    assert popcount(7 * 11) % 3 == 1 and popcount(7 * (64 - 11)) % 3 == 0
    assert popcount(7 * 13) % 3 == 2 and popcount(7 * (63 - 13)) % 3 == 0
    print("  PASS: Naive involutions n -> 2^(mk)-n and n -> 2^(mk)-1-n do NOT pair r with -r.")

    # --- ENGINE II: 2-Window Bit-Splitting Polyhedral Cone Certificate Engine ---
    print("\n[5] Engine II: Pure-Data Polyhedral Cone Certificates & Exact Replay")
    cases = [
        (
            "Theorem 2: s2(n | 5n) mod 2 (Nonlinear Bitwise-OR)",
            CERT_OR_MUL5,
            lambda g, b: (5 * b + g) >> 1,
            lambda g, b: b | ((5 * b + g) & 1),
            lambda n: popcount(n | (5 * n)),
        ),
        (
            "Theorem 3: s2(n | 3n) mod 2 (Nonlinear Bitwise-OR)",
            CERT_OR_MUL3,
            lambda g, b: (3 * b + g) >> 1,
            lambda g, b: b | ((3 * b + g) & 1),
            lambda n: popcount(n | (3 * n)),
        ),
        (
            "Theorem 4: s2(3n) mod 2 (Classical Newman Benchmark)",
            CERT_NEWMAN3,
            lambda g, b: (3 * b + g) >> 1,
            lambda g, b: (3 * b + g) & 1,
            lambda n: popcount(3 * n),
        ),
    ]

    for label, cert, nxt_fn, out_fn, direct_fn in cases:
        T0, T1, W1 = build_window_system(cert["d"], nxt_fn, out_fn, popcount)
        ok = check_cone_cert(T0, T1, W1, cert["C"], cert["U0"], cert["U1"], cert["den0"], cert["den1"])
        assert ok, f"Cone certificate failed for {label}"
        # Independent brute-force check up to N = 50,000
        s = 0
        mn = 10**9
        for n in range(50000):
            s += 1 if (direct_fn(n) % 2 == 0) else -1
            if s < mn:
                mn = s
        assert mn == 1
        print(f"  PASS: {label}")
        print(f"        q={len(cert['C'])}, 2d={2*cert['d']}, max_denom={max(max(cert['den0']), max(cert['den1']))}, min(N<=50000)={mn}, end={s}")

    # Negative / mutation tests on check_cone_cert
    print("\n[6] Engine II: Negative & Hostile Mutation Tests")
    T0_5, T1_5, W1_5 = build_window_system(
        5, lambda g, b: (5 * b + g) >> 1, lambda g, b: b | ((5 * b + g) & 1), popcount
    )
    # Mutation 1: perturb one entry of U0
    bad_U0 = [row[:] for row in CERT_OR_MUL5["U0"]]
    bad_U0[0][1] += 1
    assert not check_cone_cert(T0_5, T1_5, W1_5, CERT_OR_MUL5["C"], bad_U0, CERT_OR_MUL5["U1"], CERT_OR_MUL5["den0"], CERT_OR_MUL5["den1"])
    # Mutation 2: zero denominator
    bad_den0 = CERT_OR_MUL5["den0"][:]
    bad_den0[0] = 0
    assert not check_cone_cert(T0_5, T1_5, W1_5, CERT_OR_MUL5["C"], CERT_OR_MUL5["U0"], CERT_OR_MUL5["U1"], bad_den0, CERT_OR_MUL5["den1"])
    # Mutation 3: apply n|5n certificate to n^5n transducer (must fail!)
    T0_x5, T1_x5, W1_x5 = build_window_system(
        5, lambda g, b: (5 * b + g) >> 1, lambda g, b: b ^ ((5 * b + g) & 1), popcount
    )
    assert not check_cone_cert(T0_x5, T1_x5, W1_x5, CERT_OR_MUL5["C"], CERT_OR_MUL5["U0"], CERT_OR_MUL5["U1"], CERT_OR_MUL5["den0"], CERT_OR_MUL5["den1"])
    print("  PASS: All 3 hostile certificate mutations rejected (check_cone_cert == False).")

    # Exact Tribonacci Law for s2(n | 5n) mod 2 on N = 2^k
    print("\n[7] Theorem 2b: Exact Tribonacci Dyadic Law for s2(n | 5n) mod 2")
    trib = [0, 1, 2, 4]
    while len(trib) <= 16:
        trib.append(trib[-1] + trib[-2] + trib[-3])
    for k in range(1, 15):
        delta = sum(1 if (popcount(n | (5 * n)) % 2 == 0) else -1 for n in range(1 << k))
        assert delta == 2 * trib[k], f"Tribonacci mismatch at k={k}: {delta} vs {2*trib[k]}"
    print(f"  PASS: sum_{{n < 2^k}} (-1)^s2(n | 5n) == 2 * Trib(k) verified for k=1..14: {[2*trib[k] for k in range(1, 11)]}")

    # 3-Way Sharpness Counterexamples for Engine II
    print("\n[8] Engine II: 3-Way Sharpness Counterexamples (all fail at N=3 with sum = -1)")
    for name, fn in [
        ("n ^ 3n", lambda n: popcount(n ^ (3 * n))),
        ("n & 3n", lambda n: popcount(n & (3 * n))),
        ("n ^ 5n", lambda n: popcount(n ^ (5 * n))),
        ("n & 5n", lambda n: popcount(n & (5 * n))),
        ("n | 7n", lambda n: popcount(n | (7 * n))),
    ]:
        s3 = sum(1 if (fn(n) % 2 == 0) else -1 for n in range(3))
        assert s3 == -1
        print(f"  PASS: {name:8s} -> sum_{{n < 3}} (-1)^s2({name}) = {s3} < 0")

    print("\nALL EXACT INTEGER VERIFICATIONS PASSED (0 FLOATS, 0 ERRORS).")


if __name__ == "__main__":
    main()
