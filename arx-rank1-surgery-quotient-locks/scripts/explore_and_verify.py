"""
Pure-Silicon Exact Integer Discovery, Certificate Replay & Sharpness Suite
for `dynsil-3`: ARX Infinite-Width Period-Lock, Rank-1 Carry-Defect Surgery,
and Speck Carry-Barrier Invariant-Subspace Engine.

STRICTLY PURE INTEGER ARITHMETIC (zero floating-point operations anywhere).
Independently replays and stress-tests every theorem proved in `Proof.lean`.
"""

import math
import random


def rotl(x: int, r: int, w: int) -> int:
    r %= w
    mask = (1 << w) - 1
    return ((x << r) | (x >> (w - r))) & mask


def rotr(x: int, r: int, w: int) -> int:
    return rotl(x, w - (r % w), w)


def arx_round(x: int, w: int, r: int, c: int, d: int) -> int:
    mask = (1 << w) - 1
    return rotl((x + c) & mask, r, w) ^ d


def speck_round(x: int, y: int, w: int, a: int, b: int, k: int) -> tuple[int, int]:
    mask = (1 << w) - 1
    nx = ((rotr(x, a, w) + y) & mask) ^ k
    ny = rotl(y, b, w) ^ nx
    return nx, ny


def full_cycle_lengths_1d(f, w: int) -> list[int]:
    n = 1 << w
    seen = bytearray(n)
    lens: list[int] = []
    for s in range(n):
        if seen[s]:
            continue
        cur = s
        cnt = 0
        while not seen[cur]:
            seen[cur] = 1
            cur = f(cur)
            cnt += 1
        lens.append(cnt)
    return lens


def exact_orbit_len(f, x0: int, limit: int) -> int:
    cur = f(x0)
    k = 1
    while cur != x0:
        cur = f(cur)
        k += 1
        if k > limit:
            raise AssertionError(f"Orbit exceeded limit {limit}")
    return k


def predicted_fermat_mersenne_order(w: int, r: int) -> int:
    g = math.gcd(w, r)
    q = w // g
    if q % 2 == 1:
        return 2 * q
    if w == 2 and g == 1:
        return 3
    return q * ((1 << g) + 1)


def suite1_fermat_mersenne_exhaustive() -> None:
    print("=== SUITE 1: Exhaustive Theorem A (Fermat-Mersenne Period Lock, w=2..14, all 0<=r<w) ===")
    checked = 0
    for w in range(2, 15):
        mask = (1 << w) - 1
        for r in range(0, w):
            pred = predicted_fermat_mersenne_order(w, r)
            f = lambda x, w=w, r=r, mask=mask: arx_round(x, w, r, 1, mask)
            lens = full_cycle_lengths_1d(f, w)
            lcm_val = math.lcm(*lens)
            max_val = max(lens)
            p0 = exact_orbit_len(f, 0, pred + 10)
            assert lcm_val == pred, f"LCM mismatch w={w} r={r}: {lcm_val} != {pred}"
            assert max_val == pred, f"MAX mismatch w={w} r={r}: {max_val} != {pred}"
            assert p0 == pred, f"Master witness 0 mismatch w={w} r={r}: {p0} != {pred}"
            checked += 1
    print(f"  PASS: {checked} (w, r) instances exhaustively verified (exact LCM = max = minPeriod(0)).")


def suite2_silicon_64_128_bit_fermat() -> None:
    print("\n=== SUITE 2: Exact 64-bit & 128-bit Fermat-Number Order Replay (Corollary A4) ===")
    rng = random.Random(20261126)
    cases = [
        (64, 1, 64 * 3),
        (64, 2, 32 * 5),
        (64, 4, 16 * 17),
        (64, 8, 8 * 257),
        (64, 16, 4 * 65537),
        (63, 1, 126),
        (63, 9, 14),
        (63, 21, 6),
        (128, 1, 128 * 3),
        (128, 2, 64 * 5),
        (128, 4, 32 * 17),
        (128, 8, 16 * 257),
    ]
    for w, r, expected in cases:
        mask = (1 << w) - 1
        assert predicted_fermat_mersenne_order(w, r) == expected
        f = lambda x, w=w, r=r, mask=mask: arx_round(x, w, r, 1, mask)
        p0 = exact_orbit_len(f, 0, expected + 5)
        assert p0 == expected, f"w={w} r={r}: p0={p0} != {expected}"
        # Also verify 10 random w-bit states return in exact dividing step count
        for _ in range(10):
            x0 = rng.randrange(1 << w)
            cur = x0
            for _ in range(expected):
                cur = f(cur)
            assert cur == x0, f"Random state failed global lock at w={w}, r={r}"
        print(f"  w={w:3d}, r={r:2d}: exact minPeriod(0) = {p0:6d} = global order (10 random states PASS)")


def suite3_arx_conjugacy_group() -> None:
    print("\n=== SUITE 3: 8-Member ARX Conjugacy Group Isospectrality (w=3..11, all 1<=r<w) ===")
    checked = 0
    for w in range(3, 12):
        mask = (1 << w) - 1
        msb = 1 << (w - 1)
        for r in range(1, w):
            rmsb = rotl(msb, r, w)
            for base_c, base_d in [(1, mask), (1, 0)]:
                f0 = lambda x, w=w, r=r, c=base_c, d=base_d: arx_round(x, w, r, c, d)
                sp0 = sorted(full_cycle_lengths_1d(f0, w))
                neg_c = (-base_c) & mask
                orbit_params = [
                    (base_c, base_d),
                    (base_c ^ msb, base_d ^ rmsb),
                    (base_c, base_d ^ msb ^ rmsb),
                    (base_c ^ msb, base_d ^ msb),
                    (neg_c, base_d),
                    (neg_c ^ msb, base_d ^ rmsb),
                    (neg_c, base_d ^ msb ^ rmsb),
                    (neg_c ^ msb, base_d ^ msb),
                ]
                for c, d in orbit_params:
                    fg = lambda x, w=w, r=r, c=c, d=d: arx_round(x, w, r, c, d)
                    sp = sorted(full_cycle_lengths_1d(fg, w))
                    assert sp == sp0, f"Conjugacy mismatch w={w} r={r} c={c} d={d}"
                checked += 1
    print(f"  PASS: {checked} base systems x 8 ARX parameter pairs verified identically isospectral.")


def suite4_rank1_carry_defect_surgery() -> None:
    print("\n=== SUITE 4: Exhaustive Theorem B (Rank-1 Carry-Defect Surgery, w=2..14, all 0<=r<w) ===")
    checked = 0
    for w in range(2, 15):
        mask = (1 << w) - 1
        msb = 1 << (w - 1)
        for r in range(0, w):
            g = math.gcd(w, r)
            q = w // g
            B = q * ((1 << g) - 1)
            f = lambda x, w=w, r=r: arx_round(x, w, r, 1, 0)
            p0 = exact_orbit_len(f, 0, B + 5)
            assert p0 == B + 1, f"Anomalous cycle mismatch w={w} r={r}: {p0} != {B+1}"
            lens = full_cycle_lengths_1d(f, w)
            rem = list(lens)
            rem.remove(B + 1)
            for L in rem:
                assert B % L == 0, f"Outside cycle {L} does not divide B={B} at w={w} r={r}"
            # Also check genuine Add+Rotate+XOR conjugate G(x) = rotl(x + (1^msb), r) ^ msb
            fg = lambda x, w=w, r=r, msb=msb: arx_round(x, w, r, 1 ^ msb, msb)
            pm = exact_orbit_len(fg, msb, B + 5)
            assert pm == B + 1, f"ARX conjugate surgery mismatch w={w} r={r}"
            checked += 1
    # 64-bit replay for r=1,2,4
    for r in [1, 2, 4]:
        w = 64
        g = math.gcd(w, r)
        q = w // g
        B = q * ((1 << g) - 1)
        f = lambda x, w=w, r=r: arx_round(x, w, r, 1, 0)
        assert exact_orbit_len(f, 0, B + 5) == B + 1
        # Test an outside state (e.g. 0x123456789ABCDEF0) returns in B steps!
        x_out = 0x123456789ABCDEF0
        cur = x_out
        for _ in range(B):
            cur = f(cur)
        assert cur == x_out, f"64-bit outside state failed B-lock at r={r}"
    print(f"  PASS: {checked} (w, r) instances + 64-bit exact surgery replay verified (B+1 anomaly + B outside lock).")


def in_speck_Vh(x: int, y: int, h: int) -> bool:
    mask_lo = (1 << (h - 1)) - 1
    return ((y & mask_lo) == 0) and ((((x ^ y) >> h) & mask_lo) == 0)


def speck_pi(x: int, y: int, h: int) -> tuple[int, int]:
    return (((x ^ y) >> (2 * h - 1)) & 1, (y >> (h - 1)) & 1)


def suite5_speck_carry_barrier() -> None:
    print("\n=== SUITE 5: Theorem C (Speck Carry-Barrier Subspace V_h & Period-3 Quotient Lock) ===")
    rng = random.Random(314159)
    for h in [1, 2, 3, 4]:
        w = 2 * h
        mask_lo = (1 << (h - 1)) - 1
        all_keys = [k for k in range(1 << w) if (k & mask_lo) == 0]
        test_keys = all_keys if h <= 3 else rng.sample(all_keys, 16)
        cnt = 0
        carry_hits = 0
        for y_lo in [0, 1 << (h - 1)]:
            for x_lo in range(1 << h):
                for y_hi in range(1 << h):
                    for u in [0, 1]:
                        x_hi = y_hi ^ (u << (h - 1))
                        x = (x_hi << h) | x_lo
                        y = (y_hi << h) | y_lo
                        assert in_speck_Vh(x, y, h)
                        cnt += 1
                        # Check non-zero carry in upper h-bit addition
                        rx = rotr(x, h, w)
                        if ((rx >> h) + (y >> h)) >= (1 << h):
                            carry_hits += 1
                        for k in test_keys:
                            nx, ny = speck_round(x, y, w, h, h, k)
                            assert in_speck_Vh(nx, ny, h)
                            pu, pv = speck_pi(x, y, h)
                            kbit = (k >> (h - 1)) & 1
                            assert speck_pi(nx, ny, h) == (pv, pu ^ pv ^ kbit)
        assert cnt == (1 << (2 * h + 2))
        if h >= 2:
            assert not in_speck_Vh(0, 1, h)
            assert carry_hits > 0
        print(f"  h={h} (w={w:2d}): |V_h|=2^{2*h+2}={cnt:4d}, upper-carry states={carry_hits:4d}, keys={len(test_keys):2d} -> PASS")

    # 64-bit (h=32, 128-bit state) & 128-bit (h=64, 256-bit state) round-varying replay!
    for h in [32, 64]:
        w = 2 * h
        for _ in range(5000):
            y_lo = rng.choice([0, 1 << (h - 1)])
            x_lo = rng.randrange(1 << h)
            y_hi = rng.randrange(1 << h)
            u = rng.choice([0, 1])
            x_hi = y_hi ^ (u << (h - 1))
            x = (x_hi << h) | x_lo
            y = (y_hi << h) | y_lo
            p0 = speck_pi(x, y, h)
            cx, cy = x, y
            for _ in range(3):
                k_step = rng.randrange(1 << h) << h  # independent arbitrary upper half each round!
                cx, cy = speck_round(cx, cy, w, h, h, k_step)
                assert in_speck_Vh(cx, cy, h)
            assert speck_pi(cx, cy, h) == p0
        print(f"  h={h:2d} (w={w:3d}, {2*w}-bit Speck state): 5000 independent round-varying 3-round locks -> PASS")


def suite6_sharpness_counterexamples() -> None:
    print("\n=== SUITE 6: Sharpness & Boundary Falsification Counterexamples ===")
    # 1. LSB XOR flip breaks Theorem A at w=4, r=1
    f_lsb = lambda x: arx_round(x, 4, 1, 1, 15 ^ 1)
    cur = 0
    for _ in range(12):
        cur = f_lsb(cur)
    assert cur != 0
    sp_lsb = full_cycle_lengths_1d(f_lsb, 4)
    print(f"  Sharpness 1 (d = allOnes ^ 1 at w=4, r=1): F^12(0) = {cur} != 0, lcm = {math.lcm(*sp_lsb)} (vs 12)")

    # 2. Addend c = 2 breaks Theorem A at w=4, r=1 (13-cycle)
    f_c2 = lambda x: arx_round(x, 4, 1, 2, 15)
    p_c2 = exact_orbit_len(f_c2, 0, 50)
    assert p_c2 == 13 and 13 != 12
    print(f"  Sharpness 2 (c = 2 at w=4, r=1): minPeriod(0) = {p_c2} (13 does not divide 12)")

    # 3. Speck rotation (2, 2) -> (1, 2) breaks V_2
    assert in_speck_Vh(2, 0, 2)
    nx, ny = speck_round(2, 0, 4, 1, 2, 0)
    assert not in_speck_Vh(nx, ny, 2)
    print(f"  Sharpness 3 (Speck rot (2,2)->(1,2) at w=4): (0010,0000) in V_2 -> ({nx:04b},{ny:04b}) NOT in V_2")

    # 4. Speck key k = 0 -> 1 breaks V_2
    assert in_speck_Vh(0, 0, 2)
    nx2, ny2 = speck_round(0, 0, 4, 2, 2, 1)
    assert not in_speck_Vh(nx2, ny2, 2)
    print(f"  Sharpness 4 (Speck key k=0->1 at w=4): (0000,0000) in V_2 -> ({nx2:04b},{ny2:04b}) NOT in V_2")

    # 5. Summary table showing wider sharpness across w=4..8
    print("  Wider sharpness table (w=4..8, r=1):")
    for w in range(4, 9):
        m = (1 << w) - 1
        pred = predicted_fermat_mersenne_order(w, 1)
        lcm_lsb = math.lcm(*full_cycle_lengths_1d(lambda x, w=w, m=m: arx_round(x, w, 1, 1, m ^ 1), w))
        lcm_c2 = math.lcm(*full_cycle_lengths_1d(lambda x, w=w, m=m: arx_round(x, w, 1, 2, m), w))
        print(f"    w={w}: exact lock={pred:2d} | LSB-flip lcm={lcm_lsb:4d} | c=2 lcm={lcm_c2:4d}")


if __name__ == "__main__":
    suite1_fermat_mersenne_exhaustive()
    suite2_silicon_64_128_bit_fermat()
    suite3_arx_conjugacy_group()
    suite4_rank1_carry_defect_surgery()
    suite5_speck_carry_barrier()
    suite6_sharpness_counterexamples()
    print("\nALL 6 PURE-SILICON EXACT VERIFICATION SUITES PASSED WITH ZERO ERRORS.")
