#!/usr/bin/env python3
"""
Exact Pure-Silicon Exploration, Certificate Synthesis, Independent Verification,
and Sharpness Counterexample Suite for Task 15 (specmat-15):
  The Walsh-Automaton Transfer-Matrix Spectral-Gap Engine.

All verification is performed in exact arbitrary-precision Python integers (int)
and exact rationals (fractions.Fraction). Zero floating-point arithmetic is used
in any verification, certificate, or theorem check.
"""

from fractions import Fraction


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def lucas(n: int) -> int:
    if n == 0:
        return 2
    return fib(n - 1) + fib(n + 1)


def mod3_bound(w: int) -> int:
    """B(w): exact 3-adic amplitude bound for popcount w >= 1."""
    assert w >= 1
    if w % 2 == 1:
        return 3 ** ((w - 1) // 2)
    else:
        return 2 * (3 ** ((w // 2) - 1))


def exact_wht(vals: list[int]) -> list[int]:
    """Exact integer Walsh-Hadamard transform on length 2^k."""
    w = vals[:]
    n = len(w)
    step = 1
    while step < n:
        for i in range(0, n, 2 * step):
            for j in range(i, i + step):
                u, v = w[j], w[j + step]
                w[j] = u + v
                w[j + step] = u - v
        step *= 2
    return w


def bit_inner(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def rotl1(x: int, k: int) -> int:
    mask = (1 << k) - 1
    return ((x << 1) & mask) | (x >> (k - 1))


# =============================================================================
# 1. Exact Automaton Transfer-Matrix Compiler (Finite -> Infinite Bridge)
# =============================================================================

def eval_automaton_transfer(m: int, q0: int, delta, accept_vec: list[int], xi: int, k: int) -> int:
    """
    Evaluate (T_{xi_{k-1}} ... T_{xi_0} accept_vec)[q0] for a partial bit-automaton
    delta(q, b) -> Optional[int] reading bits LSB-first (or MSB-first when matched).
    Here we read bits in index order i = 0, 1, ..., k-1 from v_0 = accept_vec:
      at step i, bit b = (xi >> i) & 1:
      v_{i+1}[q] = val(v_i, delta(q, 0)) + (-1)^b * val(v_i, delta(q, 1)).
    """
    v = accept_vec[:]
    for i in range(k):
        b = (xi >> i) & 1
        sgn = -1 if b else 1
        nv = [0] * m
        for q in range(m):
            q0_next = delta(q, 0)
            q1_next = delta(q, 1)
            t0 = v[q0_next] if q0_next is not None else 0
            t1 = v[q1_next] if q1_next is not None else 0
            nv[q] = t0 + sgn * t1
        v = nv
    return v[q0]


def delta_mod3_msb(q: int, bit: int) -> int:
    """MSB-first mod-3 residue transition: r -> (2*r + bit) % 3."""
    return (2 * q + bit) % 3


def delta_fib_lsb(q: int, bit: int):
    """2-state partial automaton for Fibbinary (no adjacent 1s)."""
    if q == 0:
        return 0 if bit == 0 else 1
    else:
        return 0 if bit == 0 else None


# =============================================================================
# 2. Exact Verification of Finite Certificates (Algebraic Invariants)
# =============================================================================

def verify_finite_certificates():
    print("=== 1. FINITE CERTIFICATE VERIFICATION (EXACT INTEGER) ===")
    # Mod-3 Eisenstein quadratic form certificate on Z^3:
    # T0(a,b,c) = (a+b, a+c, b+c), T1(a,b,c) = (a-b, c-a, b-c)
    # Q(a,b,c) = (a-b)^2 + (b-c)^2 + (c-a)^2
    def Q(a, b, c):
        return (a - b) ** 2 + (b - c) ** 2 + (c - a) ** 2

    for a in range(-4, 5):
        for b in range(-4, 5):
            for c in range(-4, 5):
                t0 = (a + b, a + c, b + c)
                t1 = (a - b, c - a, b - c)
                assert Q(*t0) == Q(a, b, c)
                assert Q(*t1) == 3 * Q(a, b, c)
                assert sum(t1) == 0
                if a + b + c == 0:
                    assert 2 * Q(a, b, c) == 9 * a * a + 3 * (b - c) ** 2
    print("  [PASS] Mod-3 Eisenstein quadratic form: Q(T0 v)=Q(v), Q(T1 v)=3 Q(v), S(T1 v)=0")

    # Fibbinary 5-inequality polytope base case n=2:
    # Start (1,1), after 2 steps of T0(a,b)=(a+b,a), T1(a,b)=(a-b,a)
    s2 = [(3, 2), (1, 2), (1, 0), (-1, 0)]
    for (a, b) in s2:
        assert a <= fib(4) and b <= fib(3) and a >= -fib(1) and b >= -fib(0) and (a - b) >= -fib(2)
    print("  [PASS] Fibbinary 5-inequality polytope base case n=2 (all 4 states certified)")


# =============================================================================
# 3. Direct Graph-Level Replay (Rayleigh Quotient, Eigenfunctions, EML)
# =============================================================================

def verify_direct_graph_identities(name: str, k: int, pred, expected_deg: int,
                                   expected_gap: int, witness_xi: int,
                                   expected_mu: int | None = None):
    """Independently builds the 2^k-vertex graph and checks WHT, Rayleigh, eigenfunction, EML."""
    N = 1 << k
    ind = [1 if (s != 0 and pred(s, k)) else 0 for s in range(N)]
    deg = sum(ind)
    assert deg == expected_deg, f"{name} k={k}: deg={deg} != {expected_deg}"

    lam = exact_wht(ind)
    assert lam[0] == deg
    l2 = max(lam[1:])
    lmin = min(lam[1:])
    gap = deg - l2
    assert gap == expected_gap, f"{name} k={k}: gap={gap} != {expected_gap}"
    assert lam[witness_xi] == l2, f"{name} k={k}: witness xi={bin(witness_xi)} gave {lam[witness_xi]} != {l2}"

    if expected_mu is not None:
        mu = max(abs(l2), abs(lmin))
        assert mu == expected_mu, f"{name} k={k}: mu={mu} != {expected_mu}"

    # Direct pointwise eigenfunction check for chi_{witness_xi} on small k <= 8
    if k <= 8:
        chi = [-1 if bit_inner(witness_xi, x) else 1 for x in range(N)]
        assert sum(chi) == 0
        norm2 = sum(c * c for c in chi)
        assert norm2 == N
        # Direct Laplacian L chi(x) = deg * chi(x) - sum_{P(x^y)} chi(y)
        dirichlet = 0
        for x in range(N):
            adj_sum = sum(chi[y] for y in range(N) if ind[x ^ y])
            lx = deg * chi[x] - adj_sum
            assert lx == gap * chi[x], f"Eigenfunction failed at x={x}"
            dirichlet += chi[x] * lx
        assert dirichlet == gap * norm2

        # Direct Expander Mixing Lemma check on nontrivial subsets S, T
        if expected_mu is not None and k <= 6:
            S = [x for x in range(N) if x < N // 3 + 1]
            T = [x for x in range(N) if (x & 1) == 1]
            e_st = sum(1 for x in S for y in T if ind[x ^ y])
            lhs = (N * e_st - deg * len(S) * len(T)) ** 2
            rhs = (expected_mu ** 2) * len(S) * (N - len(S)) * len(T) * (N - len(T))
            assert lhs <= rhs, f"EML violated for {name} k={k}"

    return deg, l2, lmin, gap


def verify_theorem_a_mod3():
    print("\n=== 2. THEOREM A: DIVISIBILITY-BY-3 BITWISE CAYLEY SUPER-EXPANDER ===")
    for k in range(1, 13):
        N = 1 << k
        # 1. Verify transfer-matrix bridge matches WHT for every xi in BitVec k (up to k=10)
        ind_incl0 = [1 if (s % 3 == 0) else 0 for s in range(N)]
        a_wht = exact_wht(ind_incl0)
        if k <= 10:
            for xi in range(N):
                # MSB-first automaton uses bits from LSB to MSB in backward recursion!
                # check bit order: for s = sum b_j 2^j, MSB-first reads b_{k-1} first, then ..., then b_0.
                # Backward recursion starts at accept_vec after b_0, so step 0 uses xi_0, ..., step k-1 uses xi_{k-1}!
                tval = eval_automaton_transfer(3, 0, delta_mod3_msb, [1, 0, 0], xi, k)
                assert tval == a_wht[xi], f"Transfer mismatch k={k}, xi={xi}: {tval} != {a_wht[xi]}"

        # 2. Verify exact 3-adic amplitude bound |a(xi)| <= B(popcount(xi)) for ALL xi != 0
        for xi in range(1, N):
            w = xi.bit_count()
            assert abs(a_wht[xi]) <= mod3_bound(w), f"3-adic bound failed at k={k}, xi={xi}"

        expected_deg = (N - 1) // 3
        expected_gap = ((N + 2) // 3) - mod3_bound(k)
        expected_mu = (mod3_bound(k) - 1) if k >= 4 else None
        witness_xi = N - 1  # all-ones vector (popcount parity)
        deg, l2, lmin, gap = verify_direct_graph_identities(
            "G_mod3", k, lambda s, _k: s % 3 == 0,
            expected_deg, expected_gap, witness_xi, expected_mu
        )
        ratio = Fraction(gap, deg) if deg > 0 else Fraction(0)
        print(f"  k={k:2d}: deg={deg:4d}, B(k)={mod3_bound(k):3d}, gap={gap:4d}, "
              f"l2={l2:4d}, lmin={lmin:5d}, gap/deg={ratio.numerator}/{ratio.denominator}")


def verify_theorem_b_fib():
    print("\n=== 3. THEOREM B: FIBBINARY BITWISE CAYLEY EXPANDER ===")
    for k in range(1, 13):
        N = 1 << k
        ind_incl0 = [1 if ((s & (s >> 1)) == 0) else 0 for s in range(N)]
        a_wht = exact_wht(ind_incl0)
        if k <= 10:
            for xi in range(N):
                tval = eval_automaton_transfer(2, 0, delta_fib_lsb, [1, 1], xi, k)
                assert tval == a_wht[xi], f"Fib transfer mismatch k={k}, xi={xi}: {tval} != {a_wht[xi]}"

        expected_deg = fib(k + 2) - 1
        expected_gap = 2 if k <= 2 else 2 * fib(k - 1)
        witness_xi = 1 if k <= 2 else 2  # 0b10 for k >= 3!
        expected_mu = (fib(k + 2) - 2 * fib(k - 1) - 1) if k >= 3 else None
        deg, l2, lmin, gap = verify_direct_graph_identities(
            "G_fib", k, lambda s, _k: (s & (s >> 1)) == 0,
            expected_deg, expected_gap, witness_xi, expected_mu
        )
        # Verify exact minimum eigenvalue -(F_{k-1} + 1) for k >= 2
        if k >= 2:
            assert lmin == -(fib(k - 1) + 1)
            assert a_wht[3] - 1 == lmin  # achieved at xi = 0b11
        ratio = Fraction(gap, deg)
        print(f"  k={k:2d}: deg={deg:4d}, gap={gap:4d} (=2*F_{k-1} for k>=3), "
              f"l2={l2:4d}, lmin={lmin:5d}, gap/deg={ratio.numerator}/{ratio.denominator}")


def verify_theorem_c_cfib():
    print("\n=== 4. THEOREM C: CIRCULAR FIBBINARY EDGE-SPARSE DOMINANCE ===")
    for k in range(3, 13):
        N = 1 << k
        expected_deg = lucas(k) - 1
        expected_gap = 2 * fib(k - 1)
        witness_xi = 1  # weight-1 character 0b0...01
        deg, l2, lmin, gap = verify_direct_graph_identities(
            "G_cfib", k, lambda s, kk: (s & rotl1(s, kk)) == 0,
            expected_deg, expected_gap, witness_xi, expected_mu=None
        )
        # Edge-sparse dominance check: strictly fewer edges, identical gap!
        fib_deg = fib(k + 2) - 1
        assert deg + fib(k - 2) == fib_deg
        assert gap == 2 * fib(k - 1)
        ratio = Fraction(gap, deg)
        print(f"  k={k:2d}: deg_cfib={deg:4d} < deg_fib={fib_deg:4d} (-{fib(k-2):3d} edges/vtx), "
              f"SAME gap={gap:4d}, gap/deg={ratio.numerator}/{ratio.denominator}")


def verify_sharpness_counterexamples():
    print("\n=== 5. SHARPNESS & FALSIFICATION COUNTEREXAMPLES ===")
    # Counterexample 1: G_mod3 at k=4 is disconnected (gap = 0), so k >= 5 is sharp
    N4 = 16
    w4 = exact_wht([1 if (s != 0 and s % 3 == 0) else 0 for s in range(N4)])
    assert w4[0] - max(w4[1:]) == 0 and w4[15] == w4[0]
    print("  [CE-1] G_mod3 at k=4: deg=5, lam(0b1111)=5 -> gap=0 (disconnected; k>=5 is sharp)")

    # Counterexample 2: Even modulus (s % 2 == 0) is disconnected for ALL k >= 1
    for k in range(1, 8):
        N = 1 << k
        w = exact_wht([1 if (s != 0 and s % 2 == 0) else 0 for s in range(N)])
        assert w[0] - w[1] == 0  # xi = 0b1 achieves deg
    print("  [CE-2] G_mod2 (even modulus): lam(0b1)=deg -> gap=0 for all k>=1 (odd modulus required)")

    # Counterexample 3: G_fib LSB character 0b01 is strictly suboptimal for all k >= 3
    for k in range(3, 11):
        N = 1 << k
        w = exact_wht([1 if (s != 0 and (s & (s >> 1)) == 0) else 0 for s in range(N)])
        assert w[1] < w[2], f"Expected lam(0b01) < lam(0b10) at k={k}"
    print("  [CE-3] G_fib k>=3: lam(0b01) < lam(0b10) strictly (boundary bit is suboptimal; interior bit 1 is tight)")

    # Counterexample 4: G_fib at k=2 has |lmin| = 2 > 0 = l2 (so k >= 3 is sharp for mu = l2)
    w2 = exact_wht([1 if (s != 0 and (s & (s >> 1)) == 0) else 0 for s in range(4)])
    assert w2[1] == 0 and w2[2] == 0 and w2[3] == -2
    print("  [CE-4] G_fib k=2: l2=0 but lmin=-2 -> |lmin| > l2 (k>=3 is sharp for two-sided radius mu=l2)")

    # Counterexample 5: Baum-Sweet automaton fails connectivity on all even widths k=2,4,6,8
    def is_baum_sweet(s: int, k: int) -> bool:
        run = 0
        for i in range(k):
            if (s >> i) & 1:
                if run % 2 == 1:
                    return False
                run = 0
            else:
                run += 1
        return run % 2 == 0

    for k in [2, 4, 6, 8]:
        N = 1 << k
        w = exact_wht([1 if (s != 0 and is_baum_sweet(s, k)) else 0 for s in range(N)])
        assert w[N - 1] == w[0]
    print("  [CE-5] Baum-Sweet automaton at even k=2,4,6,8: lam(2^k-1)=deg -> gap=0 (disconnected)")


if __name__ == "__main__":
    verify_finite_certificates()
    verify_theorem_a_mod3()
    verify_theorem_b_fib()
    verify_theorem_c_cfib()
    verify_sharpness_counterexamples()
    print("\nALL EXACT INTEGER VERIFICATIONS AND SHARPNESS CHECKS PASSED.")
