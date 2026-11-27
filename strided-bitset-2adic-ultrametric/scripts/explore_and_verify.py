#!/usr/bin/env python3
"""
Independent Exact Pure-Silicon Exploration, Certificate Synthesis & Replay Verifier
for Task 13 (adic-13): Strided-Bitset Decomposition & 2-Adic Odd-Parity Ultrametric Engine.

Strict pure-silicon exact integer arithmetic only (Python arbitrary-precision `int`; zero floats).
Verifies:
  1. Direct combinatorial tuple-enumeration agreement with the base-2^m carry-convolution bridge.
  2. Theorem 1 (Even-Window Strided Valuation Law): ALL m in [1..4], ALL even k in [2^m, 2^(m+1)-2].
  3. Corollary 1A (Universal (2^(m+1)-2)-Collapse): v2(r_{(2^(m+1)-2) S_m}(n)) == v2(n + 1).
  4. Theorem 2 (Power-of-Two Strided Kummer Stability Law): ALL m in [1..4], ALL r in [m..m+3],
     including exact verification that minimizer tie multiplicity is ALWAYS in {1, 3}.
  5. Corollary 2A (Exact r-Invariance) & Corollary 2B (Exact Oddness: n in 2^r * S_m).
  6. Finite-Certificate Unit-Carry Compiler (`check_unit_carry_cert`): synthesizes and verifies
     49 non-binomial periodic bitmask sumsets (including 3*S_2 + N and 2*S_3 + 2*B(3, {0,2})).
  7. Explicit Sharpness & Boundary Counterexamples outside every hypothesis.
"""

import math
from functools import lru_cache
from itertools import combinations_with_replacement


def v2(n: int) -> int:
    """Exact 2-adic valuation on positive integers (0 for n = 0)."""
    if n == 0:
        return 0
    return (n & -n).bit_length() - 1


def in_mask(m: int, mask: int, x: int) -> bool:
    """Exact bit-position support predicate: every set bit i of x satisfies bit (i % m) of mask = 1."""
    i = 0
    while x > 0:
        if (x & 1) and not ((mask >> (i % m)) & 1):
            return False
        x >>= 1
        i += 1
    return True


def in_strided(m: int, x: int) -> bool:
    """Moser-de Bruijn m-strided set S_m = B(m, 1): bits only at multiples of m."""
    return in_mask(m, 1, x)


def direct_mask_rep_count(m: int, masks: list[int], n: int) -> int:
    """Direct combinatorial tuple count by dynamic programming over genuine B(m, mask_i) elements."""
    dp = [0] * (n + 1)
    dp[0] = 1
    for mask in masks:
        allowed = [x for x in range(n + 1) if in_mask(m, mask, x)]
        ndp = [0] * (n + 1)
        for s in range(n + 1):
            c = dp[s]
            if c:
                for x in allowed:
                    if s + x <= n:
                        ndp[s + x] += c
        dp = ndp
    return dp[n]


def digit_weights(m: int, masks: list[int]) -> dict[int, int]:
    """Exact base-2^m digit-slice sum multiplicities w(s)."""
    B = 1 << m
    poly = {0: 1}
    for mask in masks:
        ds = [d for d in range(B) if (d & ~mask) == 0]
        new_poly: dict[int, int] = {}
        for s, cnt in poly.items():
            for d in ds:
                new_poly[s + d] = new_poly.get(s + d, 0) + cnt
        poly = new_poly
    return poly


def make_recurrence_counter(m: int, masks: list[int]):
    """Exact base-2^m carry-convolution counter."""
    B = 1 << m
    poly = digit_weights(m, masks)
    max_s = max(poly.keys())

    @lru_cache(maxsize=None)
    def f(n: int) -> int:
        if n < 0:
            return 0
        if n == 0:
            return 1
        q, r = divmod(n, B)
        total = 0
        s = r
        while s <= max_s:
            w = poly.get(s, 0)
            if w:
                total += w * f(q - (s - r) // B)
            s += B
        return total

    return f, poly


def make_strided_counter(m: int, k: int):
    """Exact base-2^m binomial carry-convolution counter for r_{k S_m}(n)."""
    B = 1 << m

    @lru_cache(maxsize=None)
    def f(n: int) -> int:
        if n < 0:
            return 0
        if n == 0:
            return 1
        q, r = divmod(n, B)
        total = 0
        s = r
        while s <= k:
            total += math.comb(k, s) * f(q - (s - r) // B)
            s += B
        return total

    return f


def check_unit_carry_cert(B: int, w0: list[int], w1: list[int]) -> bool:
    """Finite Boolean certificate checker matching Lean 4 `checkUnitCarryCert`."""
    if B < 2 or B % 2 != 0:
        return False
    if any(w <= 0 for w in w0):
        return False
    if w1[0] <= 0 or w1[B - 1] != 0:
        return False
    for r in range(B):
        if w1[r] > 0 and v2(w0[r]) != v2(w1[r]):
            return False
    if not (v2(w0[0]) < v2(w0[B - 1])):
        return False
    for r in range(0, B, 2):
        if not ((w1[r] > 0 or w1[r + 1] == 0) and v2(w0[r]) < v2(w0[r + 1])):
            return False
        if r >= 2:
            if not ((w1[r] > 0 or w1[r - 1] == 0) and v2(w0[r]) < v2(w0[r - 1])):
                return False
    return True


def cert_val(B: int, w0: list[int], w1: list[int], n: int) -> int:
    """2-state base-B valuation transducer matching Lean 4 `certVal`."""
    acc = 0
    while n > 0:
        q, r = divmod(n, B)
        acc += v2(w0[r])
        n = (q & ~1) if w1[r] > 0 else q
    return acc


def v_base(m: int, n: int) -> int:
    """Universal r-independent stride-m valuation transducer `vBase`."""
    B = 1 << m
    acc = 0
    while n > 0:
        q, r = divmod(n, B)
        if r == 0:
            n = q & ~1
        else:
            acc += m - v2(r)
            n = q
    return acc


def pow2_strided_val(m: int, r: int, n: int) -> int:
    """Closed-form valuation formula `pow2StridedVal` for r_{2^r S_m}(n) (r >= m)."""
    K = 1 << r
    a, b = divmod(n, K)
    if b == 0:
        return v_base(m, a & ~1)
    return (r - v2(b)) + v_base(m, a)


def main() -> None:
    print("==========================================================================")
    print("adic-13: Strided-Bitset Decomposition & 2-Adic Odd-Parity Ultrametric Engine")
    print("Independent Exact Pure-Silicon Verification & Falsification Suite")
    print("==========================================================================\n")

    # 1. Verify Combinatorial Bit-Slice Carry-Convolution Bridge
    print("[1] Direct Combinatorial Tuple-Count vs Bit-Slice Recurrence Bridge:")
    bridge_cases = [
        (2, [1, 1, 1, 1], 40, "4*S_2"),
        (2, [1, 1, 1, 1, 1, 1], 40, "6*S_2"),
        (2, [1, 1, 1, 3], 40, "3*S_2 + N"),
        (3, [1, 1, 5, 5], 40, "2*S_3 + 2*B(3,{0,2})"),
    ]
    for m, masks, N, label in bridge_cases:
        f_rec, _ = make_recurrence_counter(m, masks)
        for n in range(N + 1):
            c_dir = direct_mask_rep_count(m, masks, n)
            c_rec = f_rec(n)
            assert c_dir == c_rec, f"Bridge mismatch for {label} at n={n}: {c_dir} != {c_rec}"
        print(f"    PASS {label:22s}: exact tuple-count == bit-slice recurrence for all n in 0..{N}")

    # 2. Verify Theorem 1 (Even-Window Law) & Corollary 1A ((2^(m+1)-2)-Collapse)
    print("\n[2] Theorem 1 (Even-Window Strided Valuation Law) & Corollary 1A ((2^(m+1)-2)-Collapse):")
    total_ew_checks = 0
    for m in [1, 2, 3, 4]:
        B = 1 << m
        N = 1024 if m <= 3 else 512
        for t in range(1 << (m - 1)):
            k = B + 2 * t
            w0 = [math.comb(k, r) for r in range(B)]
            w1 = [math.comb(k, B + r) for r in range(B)]
            assert check_unit_carry_cert(B, w0, w1), f"UnitCarryCert failed for m={m}, t={t}"
            f = make_strided_counter(m, k)
            for n in range(N):
                val = f(n)
                assert val > 0
                assert v2(val) == cert_val(B, w0, w1, n)
                if t == (1 << (m - 1)) - 1:
                    assert v2(val) == v2(n + 1), f"Collapse failed at m={m}, n={n}"
                total_ew_checks += 1
        print(f"    PASS m={m} (B={B:2d}): all {1 << (m - 1)} even k in [{B}..{2*B-2}] verified on 0..{N-1}; "
              f"k={2*B-2} collapses to v2(n+1)!")
    print(f"    Total Even-Window exact instances verified: {total_ew_checks}")

    # 3. Verify Theorem 2 (Power-of-Two Strided Kummer Stability Law) + Tie Multiplicity Audit + Corollaries 2A/2B
    print("\n[3] Theorem 2 (Power-of-Two Strided Kummer Stability Law, r >= m) & Tie-Multiplicity Audit:")
    total_p2_checks = 0
    total_3way_ties = 0
    for m in [1, 2, 3, 4]:
        B = 1 << m
        for r in range(m, m + 4):
            K = 1 << r
            f = make_strided_counter(m, K)
            N = 2048 if m <= 3 else 512
            ties_3 = 0
            for n in range(N):
                val = f(n)
                pred = pow2_strided_val(m, r, n)
                assert val > 0 and v2(val) == pred, f"Fail m={m},r={r},n={n}"
                # Corollary 2B (Exact Oddness)
                is_odd = (val % 2 == 1)
                expected_odd = (n % K == 0) and in_strided(m, n // K)
                assert is_odd == expected_odd, f"Oddness fail m={m},r={r},n={n}"
                # Audit tie multiplicity in recurrence for n > 0
                if n > 0:
                    q, rem = divmod(n, B)
                    term_vals = []
                    s = rem
                    while s <= K:
                        c = (s - rem) // B
                        if c <= q:
                            term_vals.append(v2(math.comb(K, s) * f(q - c)))
                        s += B
                    mn = min(term_vals)
                    mult = term_vals.count(mn)
                    assert mn == pred and mult in (1, 3), f"Unexpected tie mult={mult} at m={m},r={r},n={n}"
                    if mult == 3:
                        ties_3 += 1
                total_p2_checks += 1
            total_3way_ties += ties_3
        # Corollary 2A: r-Invariance across r in [m..m+3]
        f_list = [make_strided_counter(m, 1 << r) for r in range(m, m + 4)]
        for a in range(128):
            vs = [v2(f_list[idx]((1 << (m + idx)) * a)) for idx in range(4)]
            assert len(set(vs)) == 1, f"r-invariance fail at m={m}, a={a}: {vs}"
        print(f"    PASS m={m}: r in [{m}..{m+3}] verified; exact oddness & r-invariance hold; "
              f"tie multiplicity strictly in {{1, 3}}!")
    print(f"    Total Power-of-Two instances verified: {total_p2_checks} (including {total_3way_ties} surviving 3-way ties)")

    # 4. Finite-Certificate Synthesis for Non-Binomial Periodic Bitmask Sumsets
    print("\n[4] Finite-Certificate Synthesis for Non-Binomial Periodic Bitmask Sumsets:")
    nonbin_found = []
    for m in [2, 3]:
        B = 1 << m
        for num in range(2, 6):
            for comb in combinations_with_replacement(range(1, B), num):
                if all(x == 1 for x in comb):
                    continue
                poly = digit_weights(m, list(comb))
                if max(poly.keys()) >= 2 * B:
                    continue
                w0 = [poly.get(r, 0) for r in range(B)]
                w1 = [poly.get(B + r, 0) for r in range(B)]
                if check_unit_carry_cert(B, w0, w1):
                    nonbin_found.append((m, comb, w0, w1))
    print(f"    Synthesized {len(nonbin_found)} distinct certified non-binomial periodic bitmask sumsets (m in {{2, 3}}).")
    for m, masks, label in [(2, [1, 1, 1, 3], "3*S_2 + N"), (3, [1, 1, 5, 5], "2*S_3 + 2*B(3,{0,2})")]:
        B = 1 << m
        f, poly = make_recurrence_counter(m, masks)
        w0 = [poly.get(r, 0) for r in range(B)]
        w1 = [poly.get(B + r, 0) for r in range(B)]
        assert check_unit_carry_cert(B, w0, w1)
        for n in range(1024):
            assert f(n) > 0 and v2(f(n)) == cert_val(B, w0, w1, n)
        print(f"    PASS {label:22s}: cert=True, w0={w0}, w1={w1}, verified on 0..1023")

    # 5. Sharpness & Boundary Counterexamples
    print("\n[5] Sharpness & Boundary Counterexamples (Exact Falsification Outside Hypotheses):")
    # Counterexample 1: k < 2^m (m=2, k=2, n=3)
    f22 = make_strided_counter(2, 2)
    assert f22(3) == 0
    print(f"    SHARPNESS 1 (k < 2^m):      m=2, k=2, n=3 -> r_{{2 S_2}}(3) = {f22(3)} (breaks positivity)")

    # Counterexample 2: Odd k = 2^m + 1 (m=2, k=5, n=4)
    f25 = make_strided_counter(2, 5)
    t0, t1 = math.comb(5, 0) * f25(1), math.comb(5, 4) * f25(0)
    assert (t0, t1, f25(4), v2(t0), v2(t1), v2(f25(4))) == (5, 5, 10, 0, 0, 1)
    print(f"    SHARPNESS 2 (odd k=2^m+1):  m=2, k=5, n=4 -> terms ({t0}, {t1}) both v2=0, sum={f25(4)} has v2={v2(f25(4))} (2-way cancellation)")

    # Counterexample 3: Even k > 2^(m+1)-2, non-power-of-2 (m=2, k=10, n=4)
    f210 = make_strided_counter(2, 10)
    u0, u1 = math.comb(10, 0) * f210(1), math.comb(10, 4) * f210(0)
    assert (u0, u1, f210(4), v2(u0), v2(u1), v2(f210(4))) == (10, 210, 220, 1, 1, 2)
    print(f"    SHARPNESS 3 (even k=10):    m=2, k=10, n=4 -> terms ({u0}, {u1}) both v2=1, sum={f210(4)} has v2={v2(f210(4))} (2-way cancellation)")

    # Positive Witness 4: Surviving 3-way tie in Theorem 2 (m=2, r=3, K=8, n=12)
    f28 = make_strided_counter(2, 8)
    s0, s1, s2 = math.comb(8, 0) * f28(3), math.comb(8, 4) * f28(2), math.comb(8, 8) * f28(1)
    assert (s0, s1, s2, f28(12), v2(s0), v2(s1), v2(s2), v2(f28(12))) == (56, 1960, 8, 2024, 3, 3, 3, 3)
    print(f"    WITNESS 4 (3-way tie):      m=2, r=3, n=12 -> terms ({s0}, {s1}, {s2}) all v2=3, sum={f28(12)} keeps v2={v2(f28(12))} (odd parity!)")

    print("\nALL EXACT PURE-SILICON CHECKS PASSED (0 errors, 0 floats used).")


if __name__ == "__main__":
    main()
