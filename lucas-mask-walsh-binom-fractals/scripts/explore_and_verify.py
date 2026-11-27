#!/usr/bin/env python3
"""
Exact Pure-Silicon Exploration, Verification & Sharpness Replay
for the Bitwise-Weighted Binomial & Lucas-Mask Fractal Engine (adic-9).

ZERO floating-point values are used anywhere in this script.
All arithmetic is exact arbitrary-precision integer arithmetic.
"""

import math
import sys


def popcount(x: int) -> int:
    return x.bit_count()


def v2(x: int):
    """Exact 2-adic valuation of integer x (None if x == 0)."""
    if x == 0:
        return None
    return (x & -x).bit_length() - 1


def is_submask(k: int, n: int) -> bool:
    return (k & n) == k


def submasks(n: int):
    """Yield all bitwise submasks k <=_2 n (i.e. k & ~n == 0)."""
    k = n
    while True:
        yield k
        if k == 0:
            break
        k = (k - 1) & n


def endpoint_mask(n: int) -> int:
    """
    Pure-silicon run-endpoint bitmask:
      E(n) = n & ((n << 1) ^ (n >> 1))
    Marks bit i iff bit i is an endpoint of a run of >= 2 consecutive 1-bits in n.
    """
    return n & ((n << 1) ^ (n >> 1))


def comb0(n: int, k: int) -> int:
    if n < 0 or k < 0 or k > n:
        return 0
    return math.comb(n, k)


def delta(n: int, j: int, c: int = 0) -> int:
    """Shifted Boolean Mobius derivative on the Lucas cube of j."""
    total = 0
    for k in submasks(j):
        sign = 1 if (popcount(j ^ k) % 2 == 0) else -1
        total += sign * comb0(n, k - c)
    return total


def transducer_ab(N: int, j: int):
    """
    The 2-state finite-state bitmask transducer (alpha, beta) derived from
    bit-slicing the Lucas-mask Mobius derivative.
    """
    if N == 0:
        return (1, 0)
    M, N0 = N >> 1, N & 1
    h, j0 = j >> 1, j & 1
    aM, bM = transducer_ab(M, h)
    M0 = M & 1
    if N0 == 0 and j0 == 0:
        return (aM, bM)
    elif N0 == 1 and j0 == 0:
        return (aM ^ (M0 & bM), 0)
    elif N0 == 1 and j0 == 1:
        return (M0 & (aM ^ bM), aM ^ (M0 & bM))
    else:
        raise ValueError(f"j={j} is not a submask of N={N}")


def fwht_on_submasks(n: int, fn):
    """
    Exact integer Fast Walsh-Hadamard Transform on {k : k <=_2 n}.
    Returns list of (m, sum_{k <=_2 n} (-1)^popcount(k & m) * fn(k)).
    """
    bits = [i for i in range(n.bit_length()) if (n >> i) & 1]
    p = len(bits)
    vals = [0] * (1 << p)
    for mask in range(1 << p):
        k = 0
        for idx, b in enumerate(bits):
            if (mask >> idx) & 1:
                k |= 1 << b
        vals[mask] = fn(k)
    w = vals[:]
    for idx in range(p):
        step = 1 << idx
        for base in range(0, 1 << p, step * 2):
            for u in range(base, base + step):
                a, b = w[u], w[u + step]
                w[u] = a + b
                w[u + step] = a - b
    out = []
    for mask in range(1 << p):
        m = 0
        for idx, b in enumerate(bits):
            if (mask >> idx) & 1:
                m |= 1 << b
        out.append((m, w[mask]))
    return out


def verify_stage1():
    print("[Stage 1] Verifying 2-State Bit-Slice Divisibility & Transducer Closed Form...")
    # 1a. Two-state shifted divisibility for all N < 48
    checked_s0 = 0
    checked_s1 = 0
    for N in range(48):
        for j in submasks(N):
            pj = popcount(j)
            # State 0: 2c <= N
            for c in range(N // 2 + 1):
                val = delta(N - 2 * c, j, c)
                exp = max(0, pj - c)
                assert val % (1 << exp) == 0, f"State 0 failed at N={N}, j={j}, c={c}"
                checked_s0 += 1
            # State 1: 1 <= c, 2c <= N + 1
            for c in range(1, (N + 1) // 2 + 1):
                val = delta(N - 2 * c + 1, j, c)
                exp = max(0, pj - c)
                assert val % (1 << exp) == 0, f"State 1 failed at N={N}, j={j}, c={c}"
                checked_s1 += 1
    print(f"  PASS: Two-state shifted divisibility verified on {checked_s0} (eps=0) + {checked_s1} (eps=1) triples (N < 48).")

    # 1b. Exact mod-2 leading bit: transducer vs exact Delta vs closed-form E(N)
    checked_pairs = 0
    for N in range(128):
        en = endpoint_mask(N)
        lowbit = N & -N if N > 0 else 0
        # Fast Mobius transform on submasks of N for c=0
        bits = [i for i in range(N.bit_length()) if (N >> i) & 1]
        p = len(bits)
        mod = 1 << (p + 2)
        f = [0] * (1 << p)
        for mask in range(1 << p):
            k = 0
            for idx, b in enumerate(bits):
                if (mask >> idx) & 1:
                    k |= 1 << b
            f[mask] = math.comb(N, k) % mod
        hat = f[:]
        for idx in range(p):
            step = 1 << idx
            for mask in range(1 << p):
                if mask & step:
                    hat[mask] = (hat[mask] - hat[mask ^ step]) % mod
        for mask in range(1 << p):
            j = 0
            for idx, b in enumerate(bits):
                if (mask >> idx) & 1:
                    j |= 1 << b
            pj = popcount(j)
            assert hat[mask] % (1 << pj) == 0
            a_exact = (hat[mask] >> pj) & 1
            a_tr, b_tr = transducer_ab(N, j)
            a_cf = 1 if is_submask(j, en) else 0
            assert a_exact == a_tr == a_cf, f"Alpha mismatch at N={N}, j={j}"
            if N > 0:
                b_cf = 1 if ((j & lowbit) != 0 and is_submask(j ^ lowbit, en)) else 0
                assert b_tr == b_cf, f"Beta closed form mismatch at N={N}, j={j}"
            checked_pairs += 1
    print(f"  PASS: Exact mod-2 Mobius law Delta(N,j) == 2^pc(j)*[j <= E(N)] (mod 2^(pc(j)+1)) verified on {checked_pairs} pairs (N < 128).")

    # 1c. Bonus Mod-4 Lucas-Mask Congruence: C(n,k) == (-1)^pc(k & E(n)) (mod 4)
    checked_mod4 = 0
    for n in range(128):
        en = endpoint_mask(n)
        for k in submasks(n):
            expected = 1 if (popcount(k & en) % 2 == 0) else 3
            assert math.comb(n, k) % 4 == expected, f"Mod-4 failed at n={n}, k={k}"
            checked_mod4 += 1
    print(f"  PASS: Lucas-Mask Mod-4 Law C(n,k) == (-1)^pc(k & E(n)) (mod 4) verified on {checked_mod4} pairs (n < 128).")


def verify_stage2_and_3():
    print("[Stage 2 & 3] Verifying Walsh-Lucas Power Theorems & Mixed-Product XOR-Spike Law...")
    for r in [1, 2, 3, 4, 5, 6, 8]:
        vr = v2(r)
        count = 0
        for n in range(64):
            p = popcount(n)
            en = endpoint_mask(n)
            w_list = fwht_on_submasks(n, lambda k: math.comb(n, k) ** r)
            for m, val in w_list:
                count += 1
                if r % 2 == 1:
                    expected = (1 << p) if (m == en) else 0
                    assert (val - expected) % (1 << (p + 1)) == 0, f"Odd Walsh failed r={r}, n={n}, m={m}"
                else:
                    expected = (1 << p) if (m == 0) else 0
                    assert (val - expected) % (1 << (p + vr + 1)) == 0, f"Even Walsh failed r={r}, n={n}, m={m}"
            # Also explicitly check m = 0 unweighted sum laws:
            s0 = w_list[0][1]
            if r % 2 == 1:
                sparse = (n & (n >> 1)) == 0
                assert (v2(s0) == p) == sparse, f"Sparse iff failed at r={r}, n={n}"
            else:
                assert v2(s0) == p, f"Even exact v2 failed at r={r}, n={n}"
        print(f"  PASS: r={r} (v2(r)={vr}): all {count} Walsh-Lucas sums (n < 64) exact.")

    # Mixed product XOR-spike law: C(n1, k)^r1 * C(n2, k)^r2 over k <=_2 n
    mixed_count = 0
    for n in range(1, 32):
        p = popcount(n)
        supers = [x for x in range(n, 64) if is_submask(n, x)]
        for n1 in supers[:6]:
            for n2 in supers[:6]:
                target = (endpoint_mask(n1) ^ endpoint_mask(n2)) & n
                w_list = fwht_on_submasks(n, lambda k: math.comb(n1, k) * math.comb(n2, k))
                for m, val in w_list:
                    mixed_count += 1
                    expected = (1 << p) if (m == target) else 0
                    assert (val - expected) % (1 << (p + 1)) == 0, f"Mixed failed n={n}, n1={n1}, n2={n2}, m={m}"
    print(f"  PASS: Mixed-product XOR-spike law verified on {mixed_count} triples (n < 32).")


def verify_high_popcount():
    print("[High-Popcount Exact Mod-2^E Check] Testing up to n = 16383 (popcount = 14)...")
    MAXN = 16384
    E_BITS = 20
    MOD = 1 << E_BITS
    odd_fact = [1] * (MAXN + 1)
    for i in range(1, MAXN + 1):
        x = i
        while (x & 1) == 0:
            x >>= 1
        odd_fact[i] = (odd_fact[i - 1] * x) % MOD

    def comb_sub_mod(n: int, k: int, mod: int) -> int:
        den = (odd_fact[k] * odd_fact[n - k]) % mod
        return (odd_fact[n] * pow(den, -1, mod)) % mod

    test_ns = [
        255, 511, 1023, 2047, 4095, 8191, 16383,
        0b1010101010101,   # 5461, pc=7, sparse
        0b10101010101010,  # 10922, pc=7, sparse
        0b11011011011011,  # 14043, pc=10
        0b11101110111011,  # 15291, pc=11
    ]
    for n in test_ns:
        p = popcount(n)
        mod = 1 << (p + 4)
        assert p + 4 <= E_BITS
        s1 = s2 = s4 = 0
        en = endpoint_mask(n)
        w_en = 0
        for k in submasks(n):
            c = comb_sub_mod(n, k, mod)
            s1 = (s1 + c) % mod
            sign = 1 if (popcount(k & en) % 2 == 0) else -1
            w_en = (w_en + sign * c) % mod
            c2 = (c * c) % mod
            s2 = (s2 + c2) % mod
            s4 = (s4 + c2 * c2) % mod
        sparse = (n & (n >> 1)) == 0
        assert (s2 - (1 << p)) % (1 << (p + 2)) == 0
        assert (s4 - (1 << p)) % (1 << (p + 3)) == 0
        assert (w_en - (1 << p)) % (1 << (p + 1)) == 0
        assert ((s1 % (1 << (p + 1))) == (1 << p)) == sparse
    print(f"  PASS: All {len(test_ns)} high-popcount cases (up to pc=14, n=16383) verified exactly.")


def verify_sharpness_counterexamples():
    print("[Sharpness & Falsification Witnesses]")
    # 1. Non-submask failure: n=2, j=1 (j & ~n != 0)
    d_bad = delta(2, 1, 0)  # C(2,1) - C(2,0) = 1
    assert not is_submask(1, 2) and d_bad == 1 and d_bad % 2 != 0
    print(f"  CE-1 (Non-submask): n=2, j=1 (1 not <=_2 2) => Delta(2,1) = {d_bad}, NOT divisible by 2^pc(1)=2.")

    # 2. Even-power modulus sharpness: r=2, n=3 and r=4, n=3
    s2_3 = sum(math.comb(3, k) ** 2 for k in submasks(3))  # 20
    assert s2_3 == 20 and (s2_3 - 4) % 16 == 0 and (s2_3 - 4) % 32 != 0
    s4_3 = sum(math.comb(3, k) ** 4 for k in submasks(3))  # 164
    assert s4_3 == 164 and (s4_3 - 4) % 32 == 0 and (s4_3 - 4) % 64 != 0
    print(f"  CE-2 (Modulus sharpness): n=3, r=2 => S_2(3)={s2_3} == 4 (mod 16) but != 4 (mod 32); r=4 => S_4(3)={s4_3} == 4 (mod 32) but != 4 (mod 64).")

    # 3. Full binomial sum (dropping Lucas mask k <=_2 n) fails mod 2^(pc(n)+2):
    full_s2_2 = sum(math.comb(2, k) ** 2 for k in range(3))  # 6
    mask_s2_2 = sum(math.comb(2, k) ** 2 for k in submasks(2))  # 2
    assert mask_s2_2 == 2 and full_s2_2 == 6 and (full_s2_2 - 2) % 8 != 0
    print(f"  CE-3 (Dropping Lucas mask): n=2, r=2 => masked sum={mask_s2_2} == 2 (mod 8), full sum={full_s2_2} != 2 (mod 8).")

    # 4. Unique Walsh spike sharpness: n=7 (E(7)=5)
    w7 = dict(fwht_on_submasks(7, lambda k: math.comb(7, k)))
    assert v2(w7[5]) == 3 and all((w7[m] % 16 == 0) for m in w7 if m != 5)
    print(f"  CE-4 (Unique Walsh spike): n=7, E(7)=5 => W(7,5)={w7[5]} (v2=3), while W(7,3)={w7[3]} (v2={v2(w7[3])}), W(7,0)={w7[0]} (v2={v2(w7[0])}).")

    # 5. Necessity of exact spike-mask law [j <= E] in abstract Squaring Jump Law:
    # n=3, f = [1, 3, 1, 7] satisfies 2^pc(j) | hat_f(j) for all j <= 3,
    # yet hat_{f^2}(3) = 49 - 9 - 1 + 1 = 40, NOT divisible by 2^(pc(3)+2) = 16!
    f_ce = {0: 1, 1: 3, 2: 1, 3: 7}
    hat_f = {j: sum(((-1) ** popcount(j ^ k)) * f_ce[k] for k in submasks(j)) for j in range(4)}
    hat_f2_3 = sum(((-1) ** popcount(3 ^ k)) * (f_ce[k] ** 2) for k in submasks(3))
    assert all(hat_f[j] % (1 << popcount(j)) == 0 for j in range(4))
    assert hat_f == {0: 1, 1: 2, 2: 0, 3: 4} and hat_f2_3 == 40 and hat_f2_3 % 16 != 0
    print(f"  CE-5 (Squaring Jump hypothesis necessity): f=[1,3,1,7] on n=3 has hat_f={hat_f} (all div by 2^pc), yet hat_(f^2)(3)={hat_f2_3} != 0 (mod 16).")


if __name__ == "__main__":
    verify_stage1()
    verify_stage2_and_3()
    verify_high_popcount()
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED (0 floats, 0 mismatches).")
