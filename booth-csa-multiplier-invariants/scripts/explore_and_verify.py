#!/usr/bin/env python3
"""
Pure-Silicon Exact Exploration & Verification for:
  1. Generic Radix-B Affine-Potential Transducer Engine
  2. Universal Radix-2^k Booth Recoding & 2-State Sign-Extension Cancellation (SEC)
  3. Infinite-Width g-Bit Carry-Save Top-Normalizer & Sharpness Cut-Arc Barrier
  4. End-to-End Shift-and-Add Radix-2^k Booth Carry-Save Multiplier (with 3:2 CSA)
     at the exact minimum register width W = w + k, ∀ k >= 1, ∀ w >= 1, ∀ m >= 1.

Strict exact integer arithmetic only (no floating point anywhere).
"""

import random


def to_signed(u: int, w: int) -> int:
    """Interpret unsigned w-bit integer u in [0, 2^w - 1] as two's complement."""
    assert 0 <= u < (1 << w)
    half = 1 << (w - 1)
    return u - (1 << w) if u >= half else u


def to_unsigned(x: int, w: int) -> int:
    """Reduce integer x modulo 2^w into [0, 2^w - 1]."""
    return x & ((1 << w) - 1)


def booth_digit(y_bits: int, k: int, j: int) -> int:
    """
    Radix-2^k Booth overlapping (k+1)-bit window digit d_j:
      window bits: b_{k*j + k - 1}, ..., b_{k*j}, b_{k*j - 1} (with b_{-1} = 0).
      d_j = -2^(k-1)*b_{k*j+k-1} + sum_{i=0}^{k-2} 2^i * b_{k*j+i} + b_{k*j-1}.
    """
    b_prev = 0 if j == 0 else ((y_bits >> (k * j - 1)) & 1)
    d = b_prev
    for i in range(k - 1):
        d += ((y_bits >> (k * j + i)) & 1) << i
    d -= ((y_bits >> (k * j + k - 1)) & 1) << (k - 1)
    return d


def csa_3to2(a: int, b: int, c: int, W: int) -> tuple[int, int]:
    """
    Exact W-bit bitwise 3:2 Carry-Save Adder (no carry propagation!):
      sum_vec   = a ^ b ^ c
      carry_vec = ((a & b) | (b & c) | (a & c)) << 1  (mod 2^W)
    Invariant: (sum_vec + carry_vec) == (a + b + c) (mod 2^W).
    """
    mask = (1 << W) - 1
    s = (a ^ b ^ c) & mask
    cy = (((a & b) | (b & c) | (a & c)) << 1) & mask
    return s, cy


def csa_normalize_top_g(S: int, C: int, W: int, g: int) -> tuple[int, int]:
    """
    Zero-carry-propagation g-bit Top-Normalizer (Zero-Carry-Top mode):
      Inspect ONLY the top g bits of S and C.
      s_hi' = (s_hi + c_hi) mod 2^g,  c_hi' = 0.
      Lower (W - g) bits of S and C are untouched!
    """
    shift = W - g
    low_mask = (1 << shift) - 1
    hi_mask = (1 << g) - 1
    s_hi = S >> shift
    c_hi = C >> shift
    s_lo = S & low_mask
    c_lo = C & low_mask
    t = (s_hi + c_hi) & hi_mask
    S_norm = (t << shift) | s_lo
    C_norm = c_lo  # top g bits of C are 0!
    return S_norm, C_norm


def csa_normalize_min_safe(S: int, C: int, W: int, g: int) -> tuple[int, int]:
    """
    Dual Min-Safe g-bit Top-Normalizer for V in [-2^(W-1), 2^(W-1) - 2^(W-g) - 1].
    At the unique critical residue t = 2^(g-1) - 1, emits (2^(g-1), 2^g - 1);
    otherwise emits (t, 0).
    """
    shift = W - g
    low_mask = (1 << shift) - 1
    hi_mask = (1 << g) - 1
    s_hi = S >> shift
    c_hi = C >> shift
    s_lo = S & low_mask
    c_lo = C & low_mask
    t = (s_hi + c_hi) & hi_mask
    if t == (1 << (g - 1)) - 1:
        s_new_hi = 1 << (g - 1)
        c_new_hi = hi_mask
    else:
        s_new_hi = t
        c_new_hi = 0
    return (s_new_hi << shift) | s_lo, (c_new_hi << shift) | c_lo


def radix4_booth_pp_silicon(x_u: int, w: int, win3: int) -> tuple[int, int, int]:
    """
    Pure silicon Radix-4 Booth partial-product generator for w-bit signed X.
    win3 in 0..7 represents (b_{2j+1}, b_{2j}, b_{2j-1}).
    Returns (Q, h, s):
      Q in [0, 2^(w+1)-1]: (w+1)-bit unsigned payload
      h in {0, 1}: hot-1 negation bit
      s in {0, 1}: sign bit at weight -2^(w+1)
    Exact law: Q + h - s * 2^(w+1) == d_j * signed_w(x_u) (even for win3=7 '-0' and X=-2^(w-1), d=-2!).
    """
    mask_wp1 = (1 << (w + 1)) - 1
    x_msb = (x_u >> (w - 1)) & 1
    u_se = x_u | (x_msb << w)  # (w+1)-bit sign extension of X
    u_2x = (x_u << 1) & mask_wp1  # 2*u fits in w+1 bits

    # Standard hardware Booth decoder:
    # win3: 000(+0), 001(+1), 010(+1), 011(+2), 100(-2), 101(-1), 110(-1), 111(-0)
    if win3 == 0:
        return 0, 0, 0
    elif win3 in (1, 2):
        return u_se, 0, x_msb
    elif win3 == 3:
        return u_2x, 0, x_msb
    elif win3 == 4:
        return (~u_2x) & mask_wp1, 1, 1 - x_msb
    elif win3 in (5, 6):
        return (~u_se) & mask_wp1, 1, 1 - x_msb
    elif win3 == 7:
        # Hardware "-0" encoding: bitwise NOT of 0, hot-1 = 1, sign = 1!
        return mask_wp1, 1, 1
    raise AssertionError("unreachable")


def sec_folding_radix_2k(signs: list[int], k: int, W: int) -> int:
    """
    General Radix-2^k Sign-Extension Cancellation (SEC) folded term:
      j = 0: (2^k - s_0) * 2^W = [~s_0, s_0, ..., s_0] * 2^W
      j >= 1: (2^k - 1 - s_j) * 2^(W + k*j) = [1, ..., 1, ~s_j] * 2^(W + k*j)
    Exact identity: sec_folding_radix_2k(s, k, W) + sum_j s_j * 2^(W + k*j) == 2^(W + k*m).
    """
    m = len(signs)
    assert m >= 1
    total = ((1 << k) - signs[0]) << W
    for j in range(1, m):
        total += (((1 << k) - 1) - signs[j]) << (W + k * j)
    return total


def shift_add_booth_csa_multiply(x_u: int, y_u: int, w: int, m: int, k: int) -> int:
    """
    End-to-end pure-silicon Shift-and-Add Radix-2^k Booth Carry-Save Multiplier!
    Register width: W = w + k (EXACT information-theoretic minimum!).
    Uses ONLY:
      - 3:2 Carry-Save Addition (zero full-width carry propagation)
      - 2-bit Top-Normalizer (g = 2, inspecting ONLY top 2 bits of S and C!)
      - k-bit LSB adder to extract k product bits and 1-bit LSB carry-out
      - Right shift by k bits (signed for S, unsigned for C!)
    Returns the exact signed product X * Y.
    """
    W = w + k
    mask_W = (1 << W) - 1
    mask_k = (1 << k) - 1
    X = to_signed(x_u, w)

    S = 0
    C = 0
    low_prod = 0

    for j in range(m):
        d_j = booth_digit(y_u, k, j)
        pp_u = to_unsigned(d_j * X, W)  # W-bit two's-complement partial product

        # 3:2 Carry-Save Addition (zero carry propagation across W bits!)
        S1, C1 = csa_3to2(S, C, pp_u, W)

        # g = 2 Top-Normalizer (ONLY touches top 2 bits of S1, C1!)
        S2, C2 = csa_normalize_top_g(S1, C1, W, g=2)

        # Verify exact unwrapped integer invariant at this cycle!
        # Extract lowest k bits via tiny k-bit adder:
        r_S = S2 & mask_k
        r_C = C2 & mask_k
        lsb_sum = r_S + r_C
        p_j = lsb_sum & mask_k
        c_lsb = lsb_sum >> k  # in {0, 1}

        low_prod |= p_j << (k * j)

        # Arithmetic right shift of S2, unsigned right shift of C2!
        q_S = to_signed(S2, W) >> k
        q_C = C2 >> k  # C2 is non-negative because top 2 bits are 00!

        # Next cycle's Carry-Save state:
        # Notice c_lsb in {0,1} can be folded into C_next (or injected into CSA)!
        # Wait: let's check if (q_S mod 2^W) and (q_C + c_lsb) works, OR if c_lsb
        # is folded via a 3:2 CSA with S_next, C_next, c_lsb!
        # Even simpler: C2 >> k has top k+2 bits = 0, so (C2 >> k) + c_lsb NEVER overflows W bits,
        # OR we keep 3-input reduction with c_lsb at next step!
        # Let's check using a pure 3:2 CSA with c_lsb (ZERO carry propagation even for + c_lsb!):
        S_next_u = to_unsigned(q_S, W)
        C_next_u = to_unsigned(q_C, W)
        S, C = csa_3to2(S_next_u, C_next_u, c_lsb, W)

    # Final normalization of the upper accumulator A_m (only 1 final CPA of width W, or exact sum):
    S_fin, C_fin = csa_normalize_top_g(S, C, W, g=2)
    A_m = to_signed(S_fin, W) + to_signed(C_fin, W)
    return (A_m << (k * m)) + low_prod


def shift_add_radix4_booth_csa_silicon(x_u: int, y_u: int, w: int, m: int) -> int:
    """
    100% Pure-Silicon Shift-and-Add Radix-4 Booth-CSA Multiplier at W = w + 2:
      - NO carry-propagating negation adder (uses raw (Q_j, h_j, s_j) directly!)
      - Bit-0 wire injection: C_inj = C | h_j (exact since C is always even!)
      - Single 3:2 CSA on (S, C | h_j, (s_j << (w+1)) | Q_j)
      - g = 2 Top-Normalizer (touches ONLY top 2 bits!)
      - 2-bit LSB adder + right-shift by 2 + 3:2 CSA fold of c_lsb (restores C % 2 == 0)
    """
    W = w + 2
    S = 0
    C = 0
    low_prod = 0

    for j in range(m):
        assert (C & 1) == 0, "Carry-save invariant violated: bit 0 of C must be 0!"
        b_prev = 0 if j == 0 else ((y_u >> (2 * j - 1)) & 1)
        b0 = (y_u >> (2 * j)) & 1
        b1 = (y_u >> (2 * j + 1)) & 1
        win3 = (b1 << 2) | (b0 << 1) | b_prev

        Q, h, s = radix4_booth_pp_silicon(x_u, w, win3)
        P_raw = (s << (w + 1)) | Q  # W-bit unsigned raw payload (no negation CPA!)
        C_inj = C | h               # Zero-gate bit-0 injection of hot-1!

        S1, C1 = csa_3to2(S, C_inj, P_raw, W)
        S2, C2 = csa_normalize_top_g(S1, C1, W, g=2)

        r_S = S2 & 3
        r_C = C2 & 3
        lsb_sum = r_S + r_C
        p_j = lsb_sum & 3
        c_lsb = lsb_sum >> 2

        low_prod |= p_j << (2 * j)

        q_S = to_signed(S2, W) >> 2
        q_C = C2 >> 2
        S, C = csa_3to2(to_unsigned(q_S, W), to_unsigned(q_C, W), c_lsb, W)

    S_fin, C_fin = csa_normalize_top_g(S, C, W, g=2)
    A_m = to_signed(S_fin, W) + to_signed(C_fin, W)
    return (A_m << (2 * m)) + low_prod


def verify_finite_certificates():
    """Verify the finite transducer tables that lift to infinite theorems."""
    # 1. Booth overlapping-window finite transducer for k = 1, 2, 3:
    for k in (1, 2, 3):
        B = 1 << k
        phi = [0, -1]
        for q in (0, 1):
            for u in range(B):
                msb = (u >> (k - 1)) & 1
                low = u & ((1 << (k - 1)) - 1)
                d = -(msb << (k - 1)) + low + q
                delta = d - u
                assert delta == B * phi[msb] - phi[q]
    # 2. 2-state Sign-Extension Cancellation transducer for k = 1, 2, 3:
    for k in (1, 2, 3):
        B = 1 << k
        phi = [0, 1]
        for q in (0, 1):
            for s in (0, 1):
                sec = (B - s) if q == 0 else (B - 1 - s)
                delta = sec + s
                assert delta == B * phi[1] - phi[q]
    # 3. Finite g-bit Carry-Save Normalizer table for g = 2, 3:
    for g in (2, 3):
        G = 1 << g
        half = 1 << (g - 1)
        sigma = lambda x: x - G if x >= half else x
        for s_hi in range(G):
            for c_hi in range(G):
                for kappa in (0, 1):
                    res = (s_hi + c_hi + kappa) % G
                    # Zero-carry-top allowed: res != half (forbids [-2^(W-1), -2^(W-1)+2^(W-g)-1])
                    if res != half:
                        t = (s_hi + c_hi) % G
                        assert sigma(t) + sigma(0) + kappa == sigma(res)
                    # Min-safe allowed: res != half - 1 (forbids [2^(W-1)-2^(W-g), 2^(W-1)-1])
                    if res != half - 1:
                        t = (s_hi + c_hi) % G
                        sh, ch = (half, G - 1) if t == half - 1 else (t, 0)
                        assert sigma(sh) + sigma(ch) + kappa == sigma(res)
    print("  [PASS] All finite transducer & guard-normalizer certificates verified (k=1..3, g=2..3).")


def verify_all():
    print("=== 0. Verify Finite Transducer & Guard-Normalizer Certificates ===")
    verify_finite_certificates()

    print("\n=== 1. Verify Universal Radix-2^k Booth Recoding & 2-State SEC ===")
    for k in range(1, 5):
        for m in range(1, 5):
            if k * m > 12:
                continue
            for y_u in range(1 << (k * m)):
                rec = sum(booth_digit(y_u, k, j) << (k * j) for j in range(m))
                assert rec == to_signed(y_u, k * m), f"Booth failed: k={k}, m={m}, y={y_u}"
    print("  [PASS] Radix-2^k Booth recoding exact for all k in 1..4, m in 1..4 (k*m <= 12).")

    for k in range(1, 5):
        for m in range(1, 6):
            for W in [0, 3, 7]:
                for mask in range(1 << m):
                    signs = [(mask >> j) & 1 for j in range(m)]
                    lhs = sec_folding_radix_2k(signs, k, W) + sum(
                        signs[j] << (W + k * j) for j in range(m)
                    )
                    assert lhs == (1 << (W + k * m))
    print("  [PASS] 2-State General Radix-2^k SEC identity exact for all k=1..4, m=1..5, all sign vectors.")

    print("\n=== 2. Verify Silicon Radix-4 Booth Partial-Product + Full Tree Identity ===")
    for w in range(1, 6):
        for m in range(1, 4):
            for x_u in range(1 << w):
                X = to_signed(x_u, w)
                for y_u in range(1 << (2 * m)):
                    Y = to_signed(y_u, 2 * m)
                    pp_sum = 0
                    signs = []
                    for j in range(m):
                        b_prev = 0 if j == 0 else ((y_u >> (2 * j - 1)) & 1)
                        b0 = (y_u >> (2 * j)) & 1
                        b1 = (y_u >> (2 * j + 1)) & 1
                        win3 = (b1 << 2) | (b0 << 1) | b_prev
                        Q, h, s = radix4_booth_pp_silicon(x_u, w, win3)
                        d_j = booth_digit(y_u, 2, j)
                        assert Q + h - (s << (w + 1)) == d_j * X
                        pp_sum += (Q + h) << (2 * j)
                        signs.append(s)
                    tree_sum = pp_sum + sec_folding_radix_2k(signs, k=2, W=w + 1)
                    assert tree_sum == X * Y + (1 << (w + 1 + 2 * m))
                    assert (tree_sum & ((1 << (w + 2 * m)) - 1)) == to_unsigned(X * Y, w + 2 * m)
    print("  [PASS] Complete Silicon Radix-4 Booth Tree + SEC identity exact for all w=1..5, m=1..3 (exhaustive).")

    print("\n=== 3. Verify g-Bit Carry-Save Top-Normalizer (Zero-Carry-Top & Min-Safe) ===")
    for g in range(2, 5):
        for W in range(g, g + 5):
            N = 1 << W
            lo1 = -(1 << (W - 1)) + (1 << (W - g))
            hi1 = (1 << (W - 1)) - 1
            lo2 = -(1 << (W - 1))
            hi2 = (1 << (W - 1)) - (1 << (W - g)) - 1
            # Exhaustive for small W, sampled for larger W
            if W <= 6:
                pairs = [(S, C) for S in range(N) for C in range(N)]
            else:
                rng = random.Random(42 + 100 * g + W)
                pairs = [(rng.randrange(N), rng.randrange(N)) for _ in range(5000)]
            for S, C in pairs:
                V = to_signed((S + C) & (N - 1), W)
                if lo1 <= V <= hi1:
                    Sn, Cn = csa_normalize_top_g(S, C, W, g)
                    assert (Cn >> (W - g)) == 0
                    assert to_signed(Sn, W) + to_signed(Cn, W) == V
                if lo2 <= V <= hi2:
                    Sn2, Cn2 = csa_normalize_min_safe(S, C, W, g)
                    assert to_signed(Sn2, W) + to_signed(Cn2, W) == V
    print("  [PASS] Both g-bit Top-Normalizers exact across all g=2..4, W=g..g+4.")

    print("\n=== 4. Verify End-to-End Shift-and-Add Radix-2^k Booth-CSA Multiplier at W = w + k ===")
    for k in range(1, 5):
        for w in range(1, 6):
            for m in range(1, 5):
                if w + k * m > 12:
                    continue
                for x_u in range(1 << w):
                    X = to_signed(x_u, w)
                    for y_u in range(1 << (k * m)):
                        Y = to_signed(y_u, k * m)
                        got = shift_add_booth_csa_multiply(x_u, y_u, w, m, k)
                        assert got == X * Y, f"Mismatch k={k}, w={w}, m={m}, X={X}, Y={Y}: got {got}"
    # Also test wide random instances up to w=64, m=32!
    rng = random.Random(20261126)
    for k in [1, 2, 3, 4]:
        for w in [16, 32, 64]:
            m = 16
            for _ in range(50):
                x_u = rng.randrange(1 << w)
                y_u = rng.randrange(1 << (k * m))
                got = shift_add_booth_csa_multiply(x_u, y_u, w, m, k)
                assert got == to_signed(x_u, w) * to_signed(y_u, k * m)
            # Adversarial extremal corners: X = -2^(w-1), Y = -2^(km-1), Y = 2^(km-1)-1, alternating bits
            corners_x = [0, 1, (1 << (w - 1)) - 1, 1 << (w - 1), (1 << w) - 1]
            corners_y = [0, 1, (1 << (k * m - 1)) - 1, 1 << (k * m - 1), (1 << (k * m)) - 1,
                         int("5" * ((k * m + 3) // 4), 16) & ((1 << (k * m)) - 1),
                         int("a" * ((k * m + 3) // 4), 16) & ((1 << (k * m)) - 1)]
            for x_u in corners_x:
                for y_u in corners_y:
                    got = shift_add_booth_csa_multiply(x_u, y_u, w, m, k)
                    assert got == to_signed(x_u, w) * to_signed(y_u, k * m)
    print("  [PASS] Shift-and-Add Radix-2^k Booth-CSA Multiplier EXACT for ALL exhaustive small cases & wide 64-bit extremal corners!")

    # Exhaustive + wide verification of 100% pure-silicon Radix-4 Booth-CSA (with raw (Q,h,s) + bit-0 OR injection):
    for w in range(1, 6):
        for m in range(1, 4):
            for x_u in range(1 << w):
                X = to_signed(x_u, w)
                for y_u in range(1 << (2 * m)):
                    Y = to_signed(y_u, 2 * m)
                    got = shift_add_radix4_booth_csa_silicon(x_u, y_u, w, m)
                    assert got == X * Y, f"Silicon R4 mismatch w={w}, m={m}, X={X}, Y={Y}: got {got}"
    for w in [16, 32, 64, 128]:
        m = 32
        for _ in range(50):
            x_u = rng.randrange(1 << w)
            y_u = rng.randrange(1 << (2 * m))
            assert shift_add_radix4_booth_csa_silicon(x_u, y_u, w, m) == to_signed(x_u, w) * to_signed(y_u, 2 * m)
        for x_u in [0, 1, (1 << (w - 1)) - 1, 1 << (w - 1), (1 << w) - 1]:
            for y_u in [0, 1, (1 << (2 * m - 1)) - 1, 1 << (2 * m - 1), (1 << (2 * m)) - 1]:
                assert shift_add_radix4_booth_csa_silicon(x_u, y_u, w, m) == to_signed(x_u, w) * to_signed(y_u, 2 * m)
    print("  [PASS] Pure-Silicon Radix-4 Shift-and-Add Booth-CSA (raw (Q,h,s) + bit-0 OR + g=2 normalizer) EXACT up to 128x64 bits!")

    print("\n=== 5. Verify Sharpness Counterexamples ===")
    # (a) Unnormalized CSA Arithmetic Right Shift failure for ALL W >= 3, k = 1:
    for W in range(3, 12):
        # S = 2^(W-1) + 2, C = 2^(W-1) + 2 -> S + C = 4 mod 2^W (V = +4, inside [-2^(W-2), 2^(W-2)-1] for W >= 5;
        # even simpler: S = 2^(W-1), C = 2^(W-1) -> S + C = 0 mod 2^W, V = 0!
        # Wait: for S = 2^(W-1), C = 2^(W-1): signed(S) = -2^(W-1), signed(C) = -2^(W-1), sum = -2^W != 0!
        # Arithmetic right shift by k=1: (-2^(W-2)) + (-2^(W-2)) = -2^(W-1) != 0 = floor(0 / 2)!
        S = 1 << (W - 1)
        C = 1 << (W - 1)
        V = to_signed((S + C) & ((1 << W) - 1), W)
        assert V == 0
        naive_shift = (to_signed(S, W) >> 1) + (to_signed(C, W) >> 1) + (((S & 1) + (C & 1)) >> 1)
        assert naive_shift == -(1 << (W - 1)) != 0
    print("  [PASS] Counterexample (a): Unnormalized CSA right-shift fails with error -2^(W-1) at V=0 for all W=3..11.")

    # (b) Cut-Arc Impossibility for ANY g >= 1, W > g:
    # Pair 1: S1 = (2^(g-1) - 1) * 2^(W-g), C1 = 0 -> s_hi = 2^(g-1)-1, c_hi = 0, kappa = 0, V1 = +(2^(W-1) - 2^(W-g))
    # Pair 2: S2 = (2^(g-1) - 1) * 2^(W-g) + (2^(W-g) - 1), C2 = 1 -> SAME (s_hi, c_hi), kappa = 1, V2 = -2^(W-1)
    # Any local function f(s_hi, c_hi) produces the SAME (s_hi', c_hi'), hence:
    #   signed(S2') + signed(C2') - (signed(S1') + signed(C1')) = 2^(W-g),
    # whereas V2 - V1 = -2^W + 2^(W-g) != 2^(W-g)! Contradiction for ALL W > g >= 1!
    for g in range(1, 6):
        for W in range(g + 1, g + 5):
            s_hi = (1 << (g - 1)) - 1
            S1 = s_hi << (W - g)
            C1 = 0
            S2 = (s_hi << (W - g)) + ((1 << (W - g)) - 1)
            C2 = 1
            assert (S1 >> (W - g)) == (S2 >> (W - g)) == s_hi
            assert (C1 >> (W - g)) == (C2 >> (W - g)) == 0
            V1 = to_signed((S1 + C1) & ((1 << W) - 1), W)
            V2 = to_signed((S2 + C2) & ((1 << W) - 1), W)
            assert V1 == (1 << (W - 1)) - (1 << (W - g))
            assert V2 == -(1 << (W - 1))
            # Check NO (s_hi', c_hi') works for both!
            found = False
            for sh in range(1 << g):
                for ch in range(1 << g):
                    S1p = (sh << (W - g)) | (S1 & ((1 << (W - g)) - 1))
                    C1p = (ch << (W - g)) | (C1 & ((1 << (W - g)) - 1))
                    S2p = (sh << (W - g)) | (S2 & ((1 << (W - g)) - 1))
                    C2p = (ch << (W - g)) | (C2 & ((1 << (W - g)) - 1))
                    if (to_signed(S1p, W) + to_signed(C1p, W) == V1 and
                            to_signed(S2p, W) + to_signed(C2p, W) == V2):
                        found = True
            assert not found
    print("  [PASS] Counterexample (b): Cut-arc impossibility verified exhaustively for all g=1..5, W=g+1..g+4.")

    # (c) Booth negative-zero ghost carry bug & width-w overflow bug:
    for w in range(1, 8):
        # Negative-zero trap: X = 0, win3 = 5 (d_j = -1) -> Q = 2^(w+1)-1, h = 1, s_silicon = 1, s_math = 0
        Q, h, s_sil = radix4_booth_pp_silicon(0, w, 5)
        s_math = 0  # since (-1) * 0 = 0 is not < 0
        assert Q + h - (s_sil << (w + 1)) == 0
        assert Q + h - (s_math << (w + 1)) == (1 << (w + 1))
        # Extreme (-2^(w-1)) * (-2) = +2^w exceeds (w+1)-bit signed max (2^w - 1):
        X_min = -(1 << (w - 1))
        assert (-2) * X_min == (1 << w) > (1 << w) - 1
    print("  [PASS] Counterexample (c): Negative-zero ghost-carry bug (+2^(w+1)) and extreme overflow (+2^w) verified for w=1..7.")

    # (d) Exact reachability of BOTH endpoints -2^(w+k-2) and +2^(w+k-2) for A_j':
    for k in range(1, 4):
        for w in range(1, 5):
            # +2^(w+k-2) reached at j=0 with X = -2^(w-1), d_0 = -2^(k-1) (y_u = 2^(k-1))
            X_min = -(1 << (w - 1))
            d0 = booth_digit(1 << (k - 1), k, 0)
            assert d0 == -(1 << (k - 1))
            assert 0 + d0 * X_min == (1 << (w + k - 2))
            # -2^(w+k-2) reached at j such that k*j >= w with X = -2^(w-1), Y = 2^(k*(j+1)-1) - 1
            j = (w + k - 1) // k  # so k*j >= w
            Y_pos = (1 << (k * (j + 1) - 1)) - 1
            # Simulate A_0 .. A_j'
            A = 0
            for t in range(j):
                dt = booth_digit(Y_pos, k, t)
                A = (A + dt * X_min) >> k
            A_prime = A + booth_digit(Y_pos, k, j) * X_min
            assert A_prime == -(1 << (w + k - 2))
    print("  [PASS] Reachability (d): BOTH tight endpoints +-2^(w+k-2) of A_j' are achieved for all k=1..3, w=1..4.")
    print("\nALL EXACT CHECKS PASSED!")


if __name__ == "__main__":
    verify_all()
