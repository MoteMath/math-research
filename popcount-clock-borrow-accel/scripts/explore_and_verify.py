#!/usr/bin/env python3
"""
Exact pure-silicon exploration, certificate verification, and sharpness replay
for the Quadratic Bit-Moment Clock & Borrow-Acceleration Mechanism (dynsil-11).

Zero floating-point arithmetic is used anywhere in verification or reporting.
All computations use exact arbitrary-precision Python integers.
"""

from collections import Counter


def popcount(x: int) -> int:
    return x.bit_count()


def bit_index_sum(x: int) -> int:
    """Exact sum_{i >= 0} i * bit_i(x)."""
    total = 0
    i = 0
    t = x
    while t:
        if t & 1:
            total += i
        t >>= 1
        i += 1
    return total


def phi(x: int) -> int:
    """Binary inversion count / Young-diagram energy: sum(i * x_i) - C(s_2(x), 2)."""
    p = popcount(x)
    return bit_index_sum(x) - (p * (p - 1)) // 2


def V_unit(x: int) -> int:
    """Exact unit-clock potential for c = 0: V(x) = 2 * sum(i * x_i) - s_2(x)^2 = 2*phi(x) - s_2(x)."""
    p = popcount(x)
    return 2 * bit_index_sum(x) - p * p


def V_sub1(x: int) -> int:
    """Exact unit-clock potential for c = -1: V_{-1}(x) = 2 * sum(i * x_i) - (s_2(x) - 1)^2."""
    p = popcount(x)
    return 2 * bit_index_sum(x) - (p - 1) * (p - 1)


def ctz(n: int) -> int:
    """Exact 2-adic valuation / trailing zero count for n > 0."""
    assert n > 0
    return (n & -n).bit_length() - 1


def T_xor(x: int) -> int:
    """Carry-free popcount-pointer flow on N: x ^ 2^{s_2(x)}."""
    return x ^ (1 << popcount(x))


def T_sub(x: int) -> int:
    """Borrow-coupled popcount-pointer flow on N: x - 2^{s_2(x)} (defined when phi(x) > 0)."""
    p = popcount(x)
    assert x >= (1 << p)
    return x - (1 << p)


def T_xor_m1(x: int) -> int:
    """Subcritical (c = -1) carry-free flow on N: x ^ 2^{s_2(x) - 1} for x > 0, else 0."""
    if x == 0:
        return 0
    return x ^ (1 << (popcount(x) - 1))


def T_sub_m1(x: int) -> int:
    """Subcritical (c = -1) borrow-accelerated flow on N: x - 2^{s_2(x) - 1} for x > 0, else 0."""
    if x == 0:
        return 0
    return x - (1 << (popcount(x) - 1))


def F_xor_wrap(x: int, w: int) -> int:
    """Finite-width modular carry-free flow on [0, 2^w): x ^ (1 << (s_2(x) % w))."""
    return x ^ (1 << (popcount(x) % w))


def F_sub_wrap(x: int, w: int) -> int:
    """Finite-width modular borrow-coupled flow on [0, 2^w): (x - (1 << (s_2(x) % w))) mod 2^w."""
    return (x - (1 << (popcount(x) % w))) & ((1 << w) - 1)


def F_add_dual_wrap(x: int, w: int) -> int:
    """Complement carry-synchronized dual on [0, 2^w): (x + (1 << ((w - s_2(x)) % w))) mod 2^w."""
    return (x + (1 << ((w - popcount(x)) % w))) & ((1 << w) - 1)


def F_add_desync_wrap(x: int, w: int) -> int:
    """Desynchronized carry flow (sharpness counterexample): (x + (1 << (s_2(x) % w))) mod 2^w."""
    return (x + (1 << (popcount(x) % w))) & ((1 << w) - 1)


def verify_infinite_width_laws(max_n: int = 8192):
    print(f"[1] Verifying infinite-width laws on N for all 0 <= x < {max_n}...")
    for x in range(max_n):
        p = popcount(x)
        ph = phi(x)
        assert ph >= 0, f"phi({x}) = {ph} < 0"
        assert V_unit(x) == 2 * ph - p
        # Mersenne characterization: phi(x) == 0 <=> x == 2^p - 1
        is_mersenne = (x == (1 << p) - 1)
        assert (ph == 0) == is_mersenne

        # Theorem 1A: Exact unit clock for T_xor
        nx = T_xor(x)
        assert V_unit(nx) == V_unit(x) - 1
        bit_p = (x >> p) & 1
        assert phi(nx) == ph - bit_p

        # Theorem 1B: Exact hitting time to 2^m - 1 for m = max(x.bit_length(), 1)
        m = max(x.bit_length(), 1)
        t_hit = V_unit(x) + m
        assert t_hit >= 0
        cur = x
        for _ in range(t_hit):
            assert cur != (1 << m) - 1 or t_hit == 0
            cur = T_xor(cur)
        assert cur == (1 << m) - 1, f"Failed hit for x={x}, m={m}: got {cur}"

        # Theorem 2: Exact stopping time for subcritical c = -1
        if x > 0:
            assert V_sub1(x) >= p - 1 >= 0
            if x > 1:
                assert V_sub1(T_xor_m1(x)) == V_sub1(x) - 1
            cur = x
            steps = V_sub1(x) + 1
            for s in range(steps):
                assert cur != 0
                cur = T_xor_m1(cur)
            assert cur == 0

            # Theorem 3B: Subcritical borrow acceleration & exact Psi-clock
            q_gap = ctz(x >> (p - 1))
            acc = x
            for _ in range(q_gap + 1):
                acc = T_xor_m1(acc)
            sub1 = T_sub_m1(x)
            assert sub1 == acc, f"Subcritical borrow mismatch at x={x}"
            assert (phi(sub1) + popcount(sub1)) == (ph + p) - 1

        # Theorem 3A: Supercritical borrow acceleration & exact phi-clock
        if ph > 0:
            assert x >= (1 << p)
            q_gap = ctz(x >> p)
            acc = x
            for _ in range(q_gap + 1):
                acc = T_xor(acc)
            sub0 = T_sub(x)
            assert sub0 == acc, f"Borrow acceleration mismatch at x={x}"
            assert phi(sub0) == ph - 1

    # Verify exact Mersenne hitting time for T_sub and exact zero hitting time for T_sub_m1
    for x in range(min(max_n, 2048)):
        cur = x
        for _ in range(phi(x)):
            assert phi(cur) > 0
            cur = T_sub(cur)
        assert phi(cur) == 0 and cur == (1 << popcount(cur)) - 1

        cur = x
        for _ in range(phi(x) + popcount(x)):
            assert cur != 0
            cur = T_sub_m1(cur)
        assert cur == 0

    print("    PASS: All infinite-width unit-clock, inversion-clock, stopping-time, and borrow-acceleration laws verified!")


def verify_non_monotone_bijection_engine(max_n: int = 2048):
    """Verify reusable ClockCertificate engine on a NON-MONOTONE bijection h(p) = p ^ 1."""
    print(f"[2] Verifying general ClockCertificate engine on non-monotone involution h(p) = p ^ 1 (0 <= x < {max_n})...")
    def h(p: int) -> int:
        return p ^ 1  # involution on N: h^{-1} = h

    def V_h(x: int) -> int:
        p = popcount(x)
        # sum_{r: bit h(r) of x is 1} 2*r - p^2
        # since h is involution, bit i has rank h(i) = i ^ 1
        s = 0
        i = 0
        t = x
        while t:
            if t & 1:
                s += (i ^ 1)
            t >>= 1
            i += 1
        return 2 * s - p * p

    def T_h(x: int) -> int:
        return x ^ (1 << h(popcount(x)))

    for x in range(max_n):
        assert V_h(T_h(x)) == V_h(x) - 1
    # Check exact synchronous collision equivalence on pairs with same V_h
    by_V = {}
    for x in range(256):
        by_V.setdefault(V_h(x), []).append(x)
    checked_pairs = 0
    for v, xs in by_V.items():
        if len(xs) >= 2:
            a, b = xs[0], xs[1]
            ca, cb = a, b
            for t in range(1, 200):
                ca, cb = T_h(ca), T_h(cb)
                if ca == cb:
                    checked_pairs += 1
                    break
            else:
                raise AssertionError(f"Expected collision for {a}, {b} with V_h={v}")
    print(f"    PASS: Non-monotone involution h(p)=p^1 exact unit clock verified; {checked_pairs} colliding V_h-classes confirmed!")


def analyze_graph(fn, w):
    N = 1 << w
    img = [fn(x, w) for x in range(N)]
    indeg = Counter(img)
    state = [0] * N
    cycles = []
    depth = [0] * N
    for i in range(N):
        if state[i] != 0:
            continue
        path, idx = [], {}
        cur = i
        while state[cur] == 0:
            state[cur] = 1
            idx[cur] = len(path)
            path.append(cur)
            cur = img[cur]
        if state[cur] == 1:
            cs = idx[cur]
            cycles.append(path[cs:])
            for nd in path[cs:]:
                depth[nd] = 0
                state[nd] = 2
            for k in range(cs - 1, -1, -1):
                depth[path[k]] = depth[img[path[k]]] + 1
                state[path[k]] = 2
        else:
            for k in range(len(path) - 1, -1, -1):
                depth[path[k]] = depth[img[path[k]]] + 1
                state[path[k]] = 2
    return cycles, max(depth), Counter(indeg.values())


def verify_finite_width_laws(max_w: int = 12):
    print(f"[3] Verifying finite-width modular flows, in-degree spectra, and complement duality for w = 2..{max_w}...")
    for w in range(2, max_w + 1):
        mask = (1 << w) - 1
        # A. F_xor_wrap
        cycs_x, tail_x, in_x = analyze_graph(F_xor_wrap, w)
        assert len(cycs_x) == 1 and len(cycs_x[0]) == 2 * w
        assert tail_x == (w - 1) * (w - 2) // 2
        if w >= 3:
            assert in_x == Counter({1: 1 << (w - 1), 2: 1 << (w - 2)})

        # B. F_sub_wrap
        cycs_s, tail_s, in_s = analyze_graph(F_sub_wrap, w)
        assert len(cycs_s) == 1 and len(cycs_s[0]) == w + 1
        assert tail_s == ((w - 1) * (w - 1)) // 4 + 1
        expected_in_s = Counter()
        expected_in_s[w] += 1
        expected_in_s[1] += 1
        for k in range(1, w):
            expected_in_s[k] += 1 << (w - 1 - k)
        assert in_s == expected_in_s, f"w={w}: got {in_s}, expected {expected_in_s}"

        # C. Exact complement conjugacy between F_sub_wrap and F_add_dual_wrap
        for x in range(1 << w):
            comp_x = mask - x
            assert (mask - F_sub_wrap(comp_x, w)) == F_add_dual_wrap(x, w)

        # D. Parameterized wrap index k in [0, w-1] for arbitrary permutation pi(p) = (p + 1) % w
        if w <= 8:
            for k in range(w):
                def f_wrap_k(x, w=w, k=k):
                    p = popcount(x)
                    pos = (p + 1) % w if p < w else (k + 1) % w
                    return x ^ (1 << pos)
                cycs_k, _, _ = analyze_graph(f_wrap_k, w)
                assert len(cycs_k) == 1 and len(cycs_k[0]) == 2 * (w - k)

    print(f"    PASS: All finite-width cycle lengths (2w, w+1, 2(w-k)), exact tails, in-degree spectra, and complement dualities verified for w=2..{max_w}!")


def verify_sharpness_counterexamples():
    print("[4] Exhibiting exact sharpness counterexamples (where relaxing hypotheses breaks the theorems)...")

    # Sharpness 1: Carry vs Borrow desynchronization at w = 3
    cycs_add, _, _ = analyze_graph(F_add_desync_wrap, 3)
    lens_add = sorted(len(c) for c in cycs_add)
    assert lens_add == [3, 4], f"Unexpected cycles: {cycs_add}"
    print(f"    Sharpness 1 (Carry vs Borrow at w=3): F_add_desync_wrap splits into {len(cycs_add)} disjoint cycles of lengths {lens_add}: {cycs_add}")

    # Sharpness 2: Non-injective address map h(p) = p // 2 breaks unit clock / acyclicity
    def T_noninj(x: int) -> int:
        return x ^ (1 << (popcount(x) // 2))
    assert T_noninj(0) == 1 and T_noninj(1) == 0
    print("    Sharpness 2 (Non-injective h(p)=p//2): immediate 2-cycle 0 -> 1 -> 0 on N (no unit clock possible)")

    # Sharpness 3: Non-coprime affine stride gcd(a, w) > 1 splits unique 2w-cycle
    cycs_stride, tail_stride, _ = analyze_graph(lambda x, w: x ^ (1 << ((2 * popcount(x)) % w)), 4)
    lens_stride = sorted(len(c) for c in cycs_stride)
    assert lens_stride == [4, 4, 4, 4] and tail_stride == 0
    print(f"    Sharpness 3 (Affine stride a=2, w=4, gcd=2>1): shatters into {len(cycs_stride)} disjoint 4-cycles (bijection, tail=0)")

    # Sharpness 4: Synchronous collision example & non-collision example for T_xor
    # Find two distinct x, y with same V_unit(x) = V_unit(y)
    # x = 4 (100_2): p=1, sum=2, V = 4 - 1 = 3.
    # y = 10 (1010_2): p=2, sum=1+3=4, V = 8 - 4 = 4.
    # x = 8 (1000_2): p=1, sum=3, V = 6 - 1 = 5.
    # y = 6 (110_2): p=2, sum=1+2=3, V = 6 - 4 = 2.
    # x = 2 (10_2): p=1, sum=1, V = 2 - 1 = 1.
    # y = 5 (101_2): p=2, sum=0+2=2, V = 4 - 4 = 0.
    # x = 0: V = 0! y = 5: V = 0!
    assert V_unit(0) == 0 and V_unit(5) == 0
    c0, c5 = 0, 5
    for t in range(1, 10):
        c0, c5 = T_xor(c0), T_xor(c5)
        if c0 == c5:
            print(f"    Non-vacuity collision witness: V(0)=V(5)=0 => T_xor^{t}(0) = T_xor^{t}(5) = {c0} (bin {bin(c0)})")
            break
    assert V_unit(0) != V_unit(1)  # V(0)=0, V(1)=-1 => NEVER collide at same t!
    print(f"    Non-collision witness: V(0)={V_unit(0)} != V(1)={V_unit(1)} => T_xor^t(0) != T_xor^t(1) for ALL t in N")


if __name__ == "__main__":
    verify_infinite_width_laws(8192)
    verify_non_monotone_bijection_engine(2048)
    verify_finite_width_laws(12)
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED (ZERO FLOATS).")
