#!/usr/bin/env python3
"""
Exact Pure-Silicon Binary Exploration & Verification Engine for `dynsil-9`
Task 9: 2-Adic Piecewise-Affine & Carryless-Collatz Conjugacy Engine

Zero floating-point arithmetic anywhere: all computations use exact Python `int`.
Verifies:
  1. Shift-Faithful axioms, O(k) Hensel inversion R_T, exact bijectivity & 2-adic isometry of Q_T.
  2. Exact 2-adic Haar measure preservation (m-step preimage fibers have exact size 2^m).
  3. Universal transfer conjugacy Phi_{T1 -> T2} and exact Syracuse v_2 preservation & conjugacy.
  4. Universal 2-adic p-periodic orbit classification (exact bijection with {0, ..., 2^p - 1}).
  5. Finite-Table Ultrametric Gluing Certifier (IFF) for 2^r-branch carried & carryless tables.
  6. Carry-vs-Carryless Self-Coding Phase Transition:
       - Carryless T_{p,1}^xor: F(k) = 2^min(k, v_2(p - 1)) for all odd p > 1, k >= 1.
       - Carried T_{a,1}^+ (a = 1 mod 4): F(k) = 2 for all k >= 1.
       - Carried T_{a,1}^+ (a = 11 mod 16): F(k) = 6 for all k >= 3.
       - Carried T_{a,1}^+ (a = 23 mod 32): F(k) = 8 for all k >= 4.
       - Carried Collatz T_{3,1}^+: F(k) >= k + 1 (explicit family -2^r mod 2^k).
  7. Carryless-Collatz Trajectory Degree Identity, Cycle Degree-Balance Obstruction L = d * m,
     and Carryless 3x+1 unique non-zero cycle {1}.
  8. Explicit sharpness counterexamples breaking each hypothesis.
"""

from typing import Callable, List, Tuple


def clmul(a: int, b: int) -> int:
    """Exact carryless multiplication in F_2[t] encoded as nonnegative integers."""
    res = 0
    while b:
        if b & 1:
            res ^= a
        a <<= 1
        b >>= 1
    return res


def bit_deg(n: int) -> int:
    """Bit-degree floor(log2(n)) for n >= 1 (0 for n = 0)."""
    return n.bit_length() - 1 if n > 0 else 0


def v2(n: int) -> int:
    """Exact 2-adic valuation of positive integer n."""
    assert n > 0
    return (n & -n).bit_length() - 1


def popcount(n: int) -> int:
    return n.bit_count()


def T_carried(a: int, b: int) -> Callable[[int], int]:
    return lambda x: (x >> 1) if (x & 1) == 0 else ((a * x + b) >> 1)


def T_carryless(p: int, q: int) -> Callable[[int], int]:
    return lambda x: (x >> 1) if (x & 1) == 0 else ((clmul(p, x) ^ q) >> 1)


def eval_aff_table(r: int, table: List[Tuple[int, int]]) -> Callable[[int], int]:
    mask = (1 << r) - 1
    def T(x: int) -> int:
        a, b = table[x & mask]
        return (a * x + b) >> 1
    return T


def eval_cl_table(r: int, table: List[Tuple[int, int]]) -> Callable[[int], int]:
    mask = (1 << r) - 1
    def T(x: int) -> int:
        p, q = table[x & mask]
        return (clmul(p, x) ^ q) >> 1
    return T


def Q_encode(T: Callable[[int], int], k: int, x: int) -> int:
    """k-bit parity-vector encoder Q_T(k, x)."""
    y = 0
    cur = x
    for j in range(k):
        y |= (cur & 1) << j
        cur = T(cur)
    return y


def R_hensel(T: Callable[[int], int], k: int, y: int) -> int:
    """O(k)-bit constructive Hensel inverse R_T(k, y)."""
    x = 0
    for j in range(k):
        cur = x
        for _ in range(j):
            cur = T(cur)
        if (cur & 1) != ((y >> j) & 1):
            x |= (1 << j)
    return x


def Phi_transfer(T1: Callable[[int], int], T2: Callable[[int], int], k: int, x: int) -> int:
    """Constructive 2-adic transfer conjugacy Phi_{T1 -> T2}(k, x) = R_{T2}(k, Q_{T1}(k, x))."""
    return R_hensel(T2, k, Q_encode(T1, k, x))


def bijective_lift(T: Callable[[int], int]) -> Callable[[int], int]:
    return lambda x: (x & 1) + 2 * T(x)


def rep_word(p: int, w: int, k: int) -> int:
    """k-bit truncation of periodic bit-stream with period p and pattern w."""
    y = 0
    for j in range(k):
        y |= ((w >> (j % p)) & 1) << j
    return y


def check_branch_table(r: int, table: List[Tuple[int, int]], carryless: bool = False) -> bool:
    """Exact finite necessary-and-sufficient certificate for ShiftFaithful 2^r-branch tables."""
    assert r >= 1 and len(table) == (1 << r)
    ev = eval_cl_table(r, table) if carryless else eval_aff_table(r, table)
    N = 1 << r
    # 1. All branch slopes must be odd
    for i in range(N):
        a, _ = table[i]
        if (a & 1) != 1:
            return False
    # 2. Ultrametric gluing across branches for 1 <= k < r
    for k in range(1, r):
        mask_k = (1 << k) - 1
        mask_kp1 = (1 << (k + 1)) - 1
        bit_k = 1 << k
        bit_km1 = 1 << (k - 1)
        for i in range(N):
            if (ev(i) & mask_k) != (ev(i & mask_kp1) & mask_k):
                return False
            if (ev(i ^ bit_k) & mask_k) != ((ev(i) + bit_km1) & mask_k):
                return False
    return True


def verify_shift_faithful_engine():
    print("=== 1. Shift-Faithful Engine, Hensel Inverse, Measure Preservation & Bijective Lift ===")
    tab4_aff = [(1, 0), (3, 1), (5, 0), (7, 1)]
    tab8_aff = [(1, 0), (3, 1), (5, 0), (7, 1), (9, 0), (11, 1), (13, 0), (15, 1)]
    tab4_cl = [(1, 0), (3, 1), (5, 0), (7, 1)]

    assert check_branch_table(2, tab4_aff, carryless=False)
    assert check_branch_table(3, tab8_aff, carryless=False)
    assert check_branch_table(2, tab4_cl, carryless=True)

    maps = [
        ("Carried 3x+1", T_carried(3, 1)),
        ("Carryless 3x+1", T_carryless(3, 1)),
        ("Carryless 5x+1", T_carryless(5, 1)),
        ("4-branch carried (slopes 1,3,5,7)", eval_aff_table(2, tab4_aff)),
        ("8-branch carried (slopes 1..15)", eval_aff_table(3, tab8_aff)),
        ("4-branch carryless (slopes 1,3,5,7)", eval_cl_table(2, tab4_cl)),
    ]

    for name, T in maps:
        # Check Q/R bijection, shift conjugacy, bijectiveLift bijection up to k = 9
        for k in range(1, 10):
            N = 1 << k
            mask = N - 1
            G = bijective_lift(T)
            g_imgs = set()
            for x in range(N):
                q = Q_encode(T, k, x)
                assert 0 <= q < N
                assert R_hensel(T, k, q) == x
                assert Q_encode(T, k, R_hensel(T, k, x)) == x
                # Shift conjugacy at width k-1
                assert Q_encode(T, k - 1, T(x)) == (q >> 1)
                g_imgs.add(G(x) & mask)
            assert len(g_imgs) == N

        # Check m-step Haar measure preservation: for k=4, m=3, every fiber has size 2^3 = 8
        k, m = 4, 3
        counts = [0] * (1 << k)
        for x in range(1 << (k + m)):
            cur = x
            for _ in range(m):
                cur = T(cur)
            counts[cur & ((1 << k) - 1)] += 1
        assert all(c == (1 << m) for c in counts)

        # Check universal 2-adic periodic-orbit classification for p = 1..5 at precision k = 10
        prec = 10
        mask_p = (1 << prec) - 1
        for p in range(1, 6):
            orbits = set()
            for w in range(1 << p):
                x_hi = R_hensel(T, prec + p, rep_word(p, w, prec + p))
                x_lo = R_hensel(T, prec, rep_word(p, w, prec))
                assert (x_hi & mask_p) == x_lo
                cur = x_hi
                for _ in range(p):
                    cur = T(cur)
                assert (cur & mask_p) == x_lo
                assert Q_encode(T, p, x_lo) == w
                orbits.add(x_lo)
            assert len(orbits) == (1 << p)

        print(f"  [OK] {name}: Q/R bijection (k=1..9), bijectiveLift (k=1..9), "
              f"Haar measure (m=3, k=4), 2-adic p-orbits (p=1..5, prec=10)")


def verify_syracuse_conjugacy():
    print("\n=== 2. Constructive Transfer Conjugacy & Exact Syracuse v_2 Preservation ===")
    T1 = T_carried(3, 1)
    T2 = T_carryless(3, 1)
    k = 14
    tested = 0
    for x in range(1, 512, 2):
        t1 = T1(x)
        val1 = v2(t1)
        if val1 + 2 >= k:
            continue
        y = Phi_transfer(T1, T2, k, x)
        assert (y & 1) == 1
        t2 = T2(y)
        assert t2 > 0
        val2 = v2(t2)
        assert val1 == val2
        syr1 = t1 >> val1
        syr2 = t2 >> val2
        m = k - 1 - val1
        lhs = Phi_transfer(T1, T2, m, syr1)
        rhs = syr2 & ((1 << m) - 1)
        assert lhs == rhs
        # Inverse check
        assert Phi_transfer(T2, T1, k, y) == (x & ((1 << k) - 1))
        tested += 1
    print(f"  [OK] Carried 3x+1 <-> Carryless 3x+1: {tested} odd inputs at k={k}, "
          f"100% exact v_2 preservation & Syracuse conjugacy")


def verify_self_coding_phase_transition():
    print("\n=== 3. Carry-vs-Carryless Self-Coding Phase Transition ===")
    # 3A. Carryless T_{p,1}^xor: F(k) = 2^min(k, v_2(p - 1))
    for p in range(3, 34, 2):
        v = v2(p - 1)
        T = T_carryless(p, 1)
        for k in range(1, 10):
            fx = [x for x in range(1 << k) if Q_encode(T, k, x) == x]
            expected_step = 1 << max(0, k - v)
            expected = list(range(0, 1 << k, expected_step))
            assert fx == expected, f"Mismatch at p={p}, k={k}"
            assert len(fx) == (1 << min(k, v))
    print("  [OK] Carryless T_{p,1}^xor (all odd 3 <= p <= 33, k=1..9): F(k) = 2^min(k, v_2(p-1)) EXACT")

    # 3B. Carried T_{a,1}^+ with a == 1 mod 4: F(k) = 2 for all k >= 1
    for a in range(1, 38, 4):
        T = T_carried(a, 1)
        for k in range(1, 10):
            fx = [x for x in range(1 << k) if Q_encode(T, k, x) == x]
            assert fx == [0, 1 << (k - 1)]
            assert len(fx) == 2
    print("  [OK] Carried T_{a,1}^+ (a = 1 mod 4, a <= 37, k=1..9): F(k) = 2 EXACT (single-carry collapse)")

    # 3C. Carried T_{a,1}^+ with a == 11 mod 16: F(k) = 6 for all k >= 3
    for a in [11, 27, 43, 59, 75]:
        T = T_carried(a, 1)
        odd4 = [x for x in range(1, 16, 2) if Q_encode(T, 4, x) == x]
        assert odd4 == []
        for k in range(3, 10):
            fx = [x for x in range(1 << k) if Q_encode(T, k, x) == x]
            assert len(fx) == 6
    print("  [OK] Carried T_{a,1}^+ (a = 11 mod 16, k=3..9): oddFixed(4)=0 -> F(k) = 6 EXACT")

    # 3D. Carried T_{a,1}^+ with a == 23 mod 32: F(k) = 8 for all k >= 4
    for a in [23, 55, 87]:
        T = T_carried(a, 1)
        odd5 = [x for x in range(1, 32, 2) if Q_encode(T, 5, x) == x]
        assert odd5 == []
        for k in range(4, 10):
            fx = [x for x in range(1 << k) if Q_encode(T, k, x) == x]
            assert len(fx) == 8
    print("  [OK] Carried T_{a,1}^+ (a = 23 mod 32, k=4..9): oddFixed(5)=0 -> F(k) = 8 EXACT")

    # 3E. Classical Carried Collatz T_{3,1}^+: explicit family (2^k - 2^r) mod 2^k, F(k) >= k + 1
    T3 = T_carried(3, 1)
    counts_3 = []
    for k in range(1, 11):
        N = 1 << k
        for r in range(k + 1):
            x = (N - (1 << r)) % N
            assert Q_encode(T3, k, x) == x
        c = sum(1 for x in range(N) if Q_encode(T3, k, x) == x)
        assert c >= k + 1
        counts_3.append(c)
    print(f"  [OK] Carried Collatz T_{{3,1}}^+: F(1..10) = {counts_3} (all >= k+1, explicit -2^r family)")


def verify_carryless_cycle_obstruction():
    print("\n=== 4. Carryless-Collatz Degree Identity, Cycle Obstruction & Unique {1} Cycle ===")
    # Trajectory degree identity: bitDeg(T^L(x)) + L = bitDeg(x) + d * popcount(Q(L, x))
    for p in [3, 5, 7, 9, 11, 13, 15, 17]:
        d = bit_deg(p)
        for q in range(1, 1 << d, 2):
            T = T_carryless(p, q)
            for x in range(1, 64):
                cur = x
                for L in range(1, 15):
                    cur = T(cur)
                    assert cur > 0
                    m = popcount(Q_encode(T, L, x))
                    assert bit_deg(cur) + L == bit_deg(x) + d * m
    print("  [OK] Trajectory degree identity verified across p in {3..17}, all odd q < 2^d, x < 64, L <= 14")

    # Non-trivial finite cycles for p=5, q=1 (d=2): verify L = 2*m
    T5 = T_carryless(5, 1)
    cyc2 = [1, 2]
    assert T5(1) == 2 and T5(2) == 1
    assert 2 == bit_deg(5) * popcount(Q_encode(T5, 2, 1))
    # 4-cycle starting at 7
    c4 = [7, T5(7), T5(T5(7)), T5(T5(T5(7)))]
    assert T5(c4[-1]) == 7
    assert 4 == bit_deg(5) * popcount(Q_encode(T5, 4, 7))
    print(f"  [OK] Carryless 5x+1 cycles: {cyc2} (L=2=2*1), {c4} (L=4=2*2)")

    # Carryless 3x+1: verify all x in 1..2048 reach 1 (only cycle is {1})
    T3x = T_carryless(3, 1)
    assert T3x(1) == 1
    for s in range(1, 2049):
        cur = s
        for _ in range(500):
            if cur == 1:
                break
            cur = T3x(cur)
        assert cur == 1
    print("  [OK] Carryless 3x+1: all 1 <= x <= 2048 reach unique non-zero fixed point 1")


def verify_sharpness_counterexamples():
    print("\n=== 5. Sharpness & Boundary Falsification Counterexamples ===")
    # 5A. Even slope breaks ShiftFaithful & Q_2 bijectivity
    tab_even = [(1, 0), (2, 2)]
    assert not check_branch_table(1, tab_even, carryless=False)
    T_ev = eval_aff_table(1, tab_even)
    assert Q_encode(T_ev, 2, 1) == Q_encode(T_ev, 2, 3) == 1
    print("  [SHARP] Even slope a_1=2: check_branch_table=False, Q_2(1) = Q_2(3) = 1 (collision!)")

    # 5B. All odd slopes + exact division, but ONE cross-branch gluing bit fails
    tab4_bad = [(1, 0), (3, 1), (5, 2), (7, 1)]
    assert not check_branch_table(2, tab4_bad, carryless=False)
    T_bad = eval_aff_table(2, tab4_bad)
    assert Q_encode(T_bad, 2, 0) == Q_encode(T_bad, 2, 2) == 0
    print("  [SHARP] Broken 4-branch gluing tab4_bad: check_branch_table=False, Q_2(0) = Q_2(2) = 0 (collision!)")

    # 5C. Violating q < 2^d breaks Carryless Cycle Degree-Balance L = d * m
    T_3_7 = T_carryless(3, 7)  # d = 1, q = 7 >= 2^1
    assert T_3_7(1) == 2 and T_3_7(2) == 1
    assert 2 != bit_deg(3) * popcount(Q_encode(T_3_7, 2, 1))
    print("  [SHARP] Carryless p=3 (d=1), q=7 >= 2^1: non-zero 2-cycle {1, 2} has L=2 != 1*1 = d*m!")

    # 5D. Single-carry phase contrast at multiplier 5: Carryless F(k)=4 vs Carried F(k)=2
    f_cl_5 = sum(1 for x in range(1 << 6) if Q_encode(T_carryless(5, 1), 6, x) == x)
    f_ca_5 = sum(1 for x in range(1 << 6) if Q_encode(T_carried(5, 1), 6, x) == x)
    assert f_cl_5 == 4 and f_ca_5 == 2
    print(f"  [SHARP] Multiplier 5 at k=6: Carryless F(6)={f_cl_5} vs Carried F(6)={f_ca_5} (1-bit carry collapse!)")


if __name__ == "__main__":
    verify_shift_faithful_engine()
    verify_syracuse_conjugacy()
    verify_self_coding_phase_transition()
    verify_carryless_cycle_obstruction()
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED.")
