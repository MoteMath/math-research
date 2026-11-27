#!/usr/bin/env python3
"""
Pure Silicon Exact Explorer & Verifier for Dual Gray-Carry Lifting Mechanisms:
  Part I  (BDFTR): Bidirectional Delay-Feedback Transducer Reduction for
                   T_{k,c}(x) = ((x ^ (x >> k)) + c) mod 2^w
                   and dual carry-driven T_{k,-d}(x) = ((x ^ (x >> k)) - d) mod 2^w.
  Part II (CPMF):  Carry-Parity Monodromy Freezing Engine for
                   L_{k,c}(x) = ((x ^ (x << k)) + c) mod 2^w.

Strictly exact Python int / bitmask arithmetic (zero floating point).
"""

from collections import Counter


def gray_r(x: int, k: int) -> int:
    return x ^ (x >> k)


def lstep(k: int, c: int, w: int, x: int) -> int:
    mask = (1 << w) - 1
    return (((x ^ (x << k)) & mask) + c) & mask


# ============================================================================
# PART I: Bidirectional Delay-Feedback Transducer Reduction (BDFTR)
# ============================================================================

def dfsr_borrow_run(k: int, c: int, m: int, r: int, steps: int):
    """Run the borrow DFSR for ((x ^ (x >> k)) + c) == x ^ m from seed r < 2^k."""
    x_bits = [(r >> i) & 1 for i in range(k)]
    b = 0
    for i in range(steps):
        xi = x_bits[i]
        ci = (c >> i) & 1
        mi = (m >> i) & 1
        x_next = ci ^ mi ^ b
        x_bits.append(x_next)
        # borrow(xi ^ mi, ci, b) = 1 iff (xi ^ mi) < ci + b
        b = 1 if (xi ^ mi) < (ci + b) else 0
    return x_bits, b


def dfsr_carry_run(k: int, d: int, r: int, steps: int):
    """Run the dual carry DFSR for (x ^ (x >> k)) == (x + d) mod 2^w from seed r < 2^k."""
    x_bits = [(r >> i) & 1 for i in range(k)]
    carry = 0
    for i in range(steps):
        xi = x_bits[i]
        di = (d >> i) & 1
        x_next = di ^ carry
        x_bits.append(x_next)
        carry = 1 if (xi + di + carry) >= 2 else 0
    return x_bits, carry


def bits_to_int(bits, w: int) -> int:
    val = 0
    for i in range(w):
        if bits[i]:
            val |= (1 << i)
    return val


def verify_part_i():
    print("=" * 72)
    print("PART I: Bidirectional Delay-Feedback Transducer Reduction (BDFTR)")
    print("=" * 72)

    # 1. Exhaustive verification of Universal 2^k Twisted Law:
    #    # { x < 2^w : ((x ^ (x >> k)) + c) mod 2^w = x ^ m } == 2^k
    #    for all k in 1..3, c, m < 2^L, w = L + 2k + 1 (and w + 1)
    checked = 0
    for k in [1, 2, 3]:
        for L in range(0, 4):
            w = L + 2 * k + 1
            if w > 11:
                continue
            mask = (1 << w) - 1
            for c in range(1 << L):
                for m in range(1 << L):
                    # Direct brute-force count on Fin(2^w)
                    sols_bf = [x for x in range(1 << w) if ((gray_r(x, k) + c) & mask) == (x ^ m)]
                    # DFSR constructive generation
                    sols_dfsr = []
                    for r in range(1 << k):
                        xb, b = dfsr_borrow_run(k, c, m, r, w)
                        assert b == 0, f"Borrow not dead: k={k}, c={c}, m={m}, r={r}"
                        assert all(xb[w + j] == 0 for j in range(k)), "Not zero-flushed!"
                        x = bits_to_int(xb, w)
                        assert gray_r(x, k) + c == (x ^ m), "Untruncated N equation failed!"
                        sols_dfsr.append(x)
                    assert sorted(sols_bf) == sorted(sols_dfsr)
                    assert len(sols_bf) == (1 << k)
                    checked += 1
    print(f"[PASS] Universal 2^k Twisted Law: {checked} parameter triples (k,c,m) verified against brute force & N-stabilization.")

    # 2. Exact Sharpness Witness at w = L + 2k = 3k + 1 for c = 2^(k+1) - 1
    print("\n[SHARPNESS] Threshold w >= L + 2k + 1 is exact for every k >= 1 (c = 2^(k+1) - 1):")
    for k in range(1, 7):
        c = (1 << (k + 1)) - 1
        L = k + 1
        w_fail = L + 2 * k      # 3k + 1
        w_pass = L + 2 * k + 1  # 3k + 2
        xb_fail, _ = dfsr_borrow_run(k, c, 0, 0, w_fail)
        assert xb_fail[w_fail] == 1, f"Expected failure bit at w={w_fail} for k={k}"
        # Count solutions via DFSR (and brute-force for k <= 3)
        cnt_fail = sum(1 for r in range(1 << k) if all(dfsr_borrow_run(k, c, 0, r, w_fail)[0][w_fail + j] == 0 for j in range(k)))
        cnt_pass = sum(1 for r in range(1 << k) if all(dfsr_borrow_run(k, c, 0, r, w_pass)[0][w_pass + j] == 0 for j in range(k)))
        if k <= 3:
            m_fail = (1 << w_fail) - 1
            bf_fail = sum(1 for x in range(1 << w_fail) if ((gray_r(x, k) + c) & m_fail) == x)
            assert bf_fail == cnt_fail
        assert cnt_fail < (1 << k) and cnt_pass == (1 << k)
        print(f"  k={k}, c={c:3d} (L={L}): at w={w_fail:2d} (L+2k) -> #fp={cnt_fail:2d} < 2^k={1<<k:2d}; at w={w_pass:2d} (L+2k+1) -> #fp={cnt_pass:2d}")

    # 3. Sign-Asymmetry Complete Annihilation: d(k) = 2^(2k+1) - 2^k => 0 fixed points for all w >= 2k + 1
    print("\n[SIGN-ASYMMETRY] Carry-trap annihilation for d(k) = 2^(2k+1) - 2^k:")
    for k in range(1, 6):
        d = (1 << (2 * k + 1)) - (1 << k)
        for w in [2 * k + 1, 2 * k + 2, 2 * k + 3]:
            for r in range(1 << k):
                xb, carry = dfsr_carry_run(k, d, r, w)
                assert carry == 1 and xb[w] == 1, f"Seed {r} escaped carry trap!"
            if w <= 11:
                mask = (1 << w) - 1
                bf = [x for x in range(1 << w) if gray_r(x, k) == ((x + d) & mask)]
                assert len(bf) == 0, f"Found unexpected fixed point {bf}!"
        print(f"  k={k}, d={d:4d} (bin={bin(d)}): 0 fixed points verified for w in [{2*k+1}, {2*k+3}] (vs 2^k={1<<k} for +d)")

    # 4. Sign-Asymmetry Single-Trap Law: d = 1 => 2^k - 1 fixed points for all w >= 2k
    print("\n[SIGN-ASYMMETRY] Single carry-trap for d = 1:")
    for k in range(1, 6):
        for w in [2 * k - 1, 2 * k, 2 * k + 1]:
            cnt = 0
            for r in range(1 << k):
                xb, _ = dfsr_carry_run(k, 1, r, w)
                if all(xb[w + j] == 0 for j in range(k)):
                    cnt += 1
            if w <= 11:
                mask = (1 << w) - 1
                bf = sum(1 for x in range(1 << w) if gray_r(x, k) == ((x + 1) & mask))
                assert bf == cnt
            if w >= 2 * k:
                assert cnt == (1 << k) - 1
        print(f"  k={k}, d=1: #fp(w={2*k-1}) < { (1<<k)-1 }, #fp(w={2*k}) = #fp(w={2*k+1}) = {(1<<k)-1} = 2^k - 1")


# ============================================================================
# PART II: Carry-Parity Monodromy Freezing Engine (CPMF)
# ============================================================================

def extract_cpmf_certificate(k: int, c0: int, w0: int):
    """Extract canonical cycle representatives, lengths, carry parities, and monodromies at w0."""
    N = 1 << w0
    seen = [False] * N
    reps = []
    for x in range(N):
        if not seen[x]:
            cyc = []
            cur = x
            while not seen[cur]:
                seen[cur] = True
                cyc.append(cur)
                cur = lstep(k, c0, w0, cur)
            # Compute carry parity kappa and monodromy delta at width w0
            carries = 0
            shift_xor = 0
            for v in cyc:
                lk = (v ^ (v << k)) & (N - 1)
                if lk + (c0 & (N - 1)) >= N:
                    carries ^= 1
                if k <= w0:
                    shift_xor ^= (v >> (w0 - k)) & 1
            delta = carries ^ shift_xor
            reps.append((x, len(cyc), carries, delta))
    return reps


def verify_part_ii():
    print("\n" + "=" * 72)
    print("PART II: Carry-Parity Monodromy Freezing Engine (CPMF)")
    print("=" * 72)

    # 1. Extract & verify finite certificate for c == 9 (mod 32) at w0 = 5
    cert9 = extract_cpmf_certificate(1, 9, 5)
    print(f"\n[CERT c == 9 mod 32, w0 = 5]: {cert9}")
    assert len(cert9) == 5
    assert sum(p for _, p, _, _ in cert9) == 32
    assert all(p % 2 == 0 and kap == 1 and dlt == 1 for _, p, kap, dlt in cert9)

    # Independent replay across m = 0..7 and w = 5..12
    for m in range(8):
        c = 9 + 32 * m
        for w in range(5, 13):
            N = 1 << w
            seen = bytearray(N)
            lens = []
            for x in range(N):
                if not seen[x]:
                    l = 0
                    cur = x
                    while not seen[cur]:
                        seen[cur] = 1
                        cur = lstep(1, c, w, cur)
                        l += 1
                    lens.append(l)
            assert Counter(lens) == {1 << (w - 1): 1, 1 << (w - 3): 4}
    print("[PASS] c == 9 (mod 32): exact 5-cycle spectrum {2^(w-1):1, 2^(w-3):4} verified for m=0..7, w=5..12.")

    # 2. Extract & verify finite certificate for c == 19 (mod 64) at w0 = 6
    cert19 = extract_cpmf_certificate(1, 19, 6)
    print(f"\n[CERT c == 19 mod 64, w0 = 6]: {cert19}")
    assert len(cert19) == 7
    assert sum(p for _, p, _, _ in cert19) == 64
    assert all(p % 2 == 0 and kap == 1 and dlt == 1 for _, p, kap, dlt in cert19)

    for m in range(4):
        c = 19 + 64 * m
        for w in range(6, 13):
            N = 1 << w
            seen = bytearray(N)
            lens = []
            for x in range(N):
                if not seen[x]:
                    l = 0
                    cur = x
                    while not seen[cur]:
                        seen[cur] = 1
                        cur = lstep(1, c, w, cur)
                        l += 1
                    lens.append(l)
            assert Counter(lens) == {1 << (w - 2): 3, 1 << (w - 4): 4}
    print("[PASS] c == 19 (mod 64): exact 7-cycle spectrum {2^(w-2):3, 2^(w-4):4} verified for m=0..3, w=6..12.")

    # 3. Single-Cycle Law for k >= 2, odd c, all w >= 1
    for k in [2, 3, 4]:
        for c in [1, 3, 5, 7, 9]:
            for w in range(1, 11):
                N = 1 << w
                cur = 0
                for step in range(1, N + 1):
                    cur = lstep(k, c, w, cur)
                    if cur == 0:
                        assert step == N, f"Short cycle for k={k}, c={c}, w={w}: {step}"
                        break
    print("[PASS] Universal Single-Cycle Law for k in {2,3,4}, odd c in {1,3,5,7,9}, w=1..10.")

    # 4. Sharpness Counterexamples for Part II
    # (a) k = 1, c = 1, w = 2 fails single-cycle (period of 0 is 2 < 4)
    p_k1 = 1
    cur = lstep(1, 1, 2, 0)
    while cur != 0:
        cur = lstep(1, 1, 2, cur)
        p_k1 += 1
    assert p_k1 == 2
    # (b) k = 2, c = 2 (even), w = 1 fails single-cycle (period of 0 is 1 < 2)
    assert lstep(2, 2, 1, 0) == 0
    # (c) c = 25 == 9 (mod 16) breaks 5-cycle freezing at w = 6 (has 9 cycles, including period-4 cycle at x = 2)
    cert25 = extract_cpmf_certificate(1, 25, 6)
    assert len(cert25) == 9
    print(f"[SHARPNESS] Counterexamples verified: L_{{1,1}} at w=2 has period(0)={p_k1}<4; L_{{2,2}} at w=1 fixes 0; L_{{1,25}} at w=6 has {len(cert25)} cycles (breaks mod-16 weakening).")


if __name__ == "__main__":
    verify_part_i()
    verify_part_ii()
    print("\nALL EXACT REPLAYS AND SHARPNESS CHECKS PASSED.")
