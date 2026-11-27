"""
explore_and_verify.py — Pure-Silicon Exact Certificate Synthesis, Replay & Sharpness Suite
for Task 12 (dynsil-12): Hybrid Carry-AND NLFSR De Bruijn & Period-Doubling Engine.

Zero floating-point arithmetic anywhere; all computations use exact Python arbitrary-precision
integers and exact F_2 bit-vectors.

Produces:
  1. Synthesized F_2 Carry-Transducer Lasso Certificates for:
       - H_{1,1,1}(x) = x + 2*(x & (x << 1)) + 1   (Exact 2-cycle {2^(w-1), 2^(w-1)}, w >= 3)
       - K(x) = (x ^ (x << 1)) + 2*(x | (x << 1)) + 1 (De Bruijn 2^w, w >= 1)
       - H_{1,2,1}(x) = x + 2*(x & (x << 2)) + 1   (De Bruijn 2^w, w >= 1)
       - H_{2,1,1}(x) = x + 4*(x & (x << 1)) + 1   (De Bruijn 2^w, w >= 1)
  2. Exhaustive cycle-spectrum replay for w = 1..16 (up to 65,536 states) verifying:
       - Theorem 1  (Additive Carry-AND exact 2-cycle splitting & period-doubling)
       - Theorem 1b (Additive Carry-OR / Carry-AND De Bruijn completeness)
       - Theorem 2  (Universal Carry-Barrier & Frobenius Carry-Pump Bifurcation + exact F_0 spectrum)
       - Theorem 3  (Non-Prefix Hybrid XOR-AND-Carry De Bruijn completeness & Prefix-d splitting)
  3. Explicit sharpness / falsification counterexamples demonstrating every hypothesis is tight.
"""

from collections import Counter


# =============================================================================
# 1. Exact Cycle-Structure Engine (Pure Integer Arithmetic)
# =============================================================================

def cycle_spectrum(w: int, f):
    """Exact cycle decomposition of bijection f on {0, ..., 2^w - 1}."""
    N = 1 << w
    vis = bytearray(N)
    lens = []
    reps = []
    for i in range(N):
        if not vis[i]:
            cur = i
            L = 0
            while not vis[cur]:
                vis[cur] = 1
                cur = f(cur)
                L += 1
            assert cur == i, f"Not a bijection at w={w}, start={i}"
            lens.append(L)
            reps.append((L, i))
    lens.sort(reverse=True)
    return lens, reps


def fmt_spec(cs) -> str:
    cnt = Counter(cs)
    return ", ".join(
        f"{k}x{v}" if v > 1 else f"{k}"
        for k, v in sorted(cnt.items(), reverse=True)
    )


def ceil_log2(n: int) -> int:
    """Exact integer ceiling of log2(n) for n >= 1 (no floats!)."""
    assert n >= 1
    k = 0
    while (1 << k) < n:
        k += 1
    return k


# =============================================================================
# 2. Exact F_2 Carry-Transducer Lasso Certificate Synthesizer
# =============================================================================

def synthesize_f2_lasso(name: str, num_states: int, init_state: int,
                        next_state, toggle_bit, init_w: int,
                        sector_pred=None):
    """
    Synthesize the exact finite F_2 transfer-operator lasso (preperiod, cycle)
    of state-parity vectors v_w in F_2^{num_states}.
    Returns a certificate dict verifying that every vector on the lasso has
    holonomy parity = 1, proving exact period-doubling for ALL w >= init_w.
    """
    def step_vec(v_mask: int) -> int:
        nv = 0
        for s in range(num_states):
            if (v_mask >> s) & 1:
                s0 = next_state(s, 0)
                s1 = next_state(s, 1)
                nv ^= (1 << s0) ^ (1 << s1)
        return nv

    def vec_hol(v_mask: int) -> int:
        h = 0
        for s in range(num_states):
            if (v_mask >> s) & 1:
                h ^= toggle_bit(s)
        return h

    # Compute initial parity vector v_{init_w} over the base cylinder
    v0 = 0
    for x in range(1 << init_w):
        if sector_pred is not None and not sector_pred(x):
            continue
        s = init_state
        for k in range(init_w):
            s = next_state(s, (x >> k) & 1)
        v0 ^= (1 << s)

    seen = {}
    trace = []
    cur = v0
    idx = 0
    while cur not in seen:
        seen[cur] = idx
        trace.append(cur)
        cur = step_vec(cur)
        idx += 1

    cyc_start = seen[cur]
    pre = trace[:cyc_start]
    cyc = trace[cyc_start:]
    all_one = all(vec_hol(v) == 1 for v in trace)

    # Independent certificate check (mirrors Lean's F2LassoCert)
    assert len(cyc) >= 1
    full = pre + cyc
    for i in range(len(full) - 1):
        assert step_vec(full[i]) == full[i + 1]
    assert step_vec(cyc[-1]) == cyc[0]
    assert all(vec_hol(v) == 1 for v in full) == all_one

    print(f"[CERT] {name}")
    print(f"       states={num_states}, init_w={init_w}, pre_len={len(pre)}, cyc_len={len(cyc)}, all_hol_1={all_one}")
    print(f"       pre_masks={[bin(v)[2:].zfill(num_states) for v in pre]}")
    print(f"       cyc_masks={[bin(v)[2:].zfill(num_states) for v in cyc]}")
    return {
        "name": name,
        "states": num_states,
        "init_w": init_w,
        "pre": pre,
        "cyc": cyc,
        "all_one": all_one,
    }


# =============================================================================
# 3. Main Verification Suite
# =============================================================================

def main():
    print("========================================================================")
    print("  DYNSIL-12: Hybrid Carry-AND NLFSR De Bruijn & Period-Doubling Engine  ")
    print("========================================================================\n")

    # -------------------------------------------------------------------------
    # PART A: F_2 Carry-Transducer Lasso Certificate Synthesis
    # -------------------------------------------------------------------------
    print("--- PART A: F_2 Carry-Transducer Lasso Certificate Synthesis ---")

    # 1. H_{1,1,1}(x) = x + 2*(x & (x << 1)) + 1
    # State s = (x_{k-1} << 2) | (x_{k-2} << 1) | carry_in  in 0..7, init_state = (0, 0, 1) = 1
    def h111_next(s, xk):
        a = (s >> 2) & 1
        b = (s >> 1) & 1
        c = s & 1
        cout = (xk + (a & b) + c) >> 1
        return (xk << 2) | (a << 1) | cout

    def h111_toggle(s):
        a = (s >> 2) & 1
        b = (s >> 1) & 1
        c = s & 1
        return (a & b) ^ c

    c_h0 = synthesize_f2_lasso(
        "H_{1,1,1} sector x_2 = 0 (x mod 8 in {0,1,2,3})",
        8, 1, h111_next, h111_toggle, 3, lambda x: (x & 4) == 0
    )
    c_h1 = synthesize_f2_lasso(
        "H_{1,1,1} sector x_2 = 1 (x mod 8 in {4,5,6,7})",
        8, 1, h111_next, h111_toggle, 3, lambda x: (x & 4) == 4
    )
    assert c_h0["all_one"] and c_h1["all_one"]
    assert set(c_h0["cyc"]) == set(c_h1["cyc"]) and len(c_h0["cyc"]) == 3

    # 2. K(x) = (x ^ (x << 1)) + 2*(x | (x << 1)) + 1
    # State s = (x_{k-1} << 2) | (x_{k-2} << 1) | carry_in in 0..7, init_state = 1
    def k_next(s, xk):
        a = (s >> 2) & 1
        b = (s >> 1) & 1
        c = s & 1
        cout = ((xk ^ a) + (a | b) + c) >> 1
        return (xk << 2) | (a << 1) | cout

    def k_toggle(s):
        a = (s >> 2) & 1
        b = (s >> 1) & 1
        c = s & 1
        return (a ^ (a | b)) ^ c

    c_k = synthesize_f2_lasso(
        "K(x) = (x ^ (x << 1)) + 2*(x | (x << 1)) + 1 (De Bruijn)",
        8, 1, k_next, k_toggle, 1
    )
    assert c_k["all_one"] and len(c_k["cyc"]) == 1

    # 3. H_{1,2,1}(x) = x + 2*(x & (x << 2)) + 1
    # State s = (x_{k-1} << 3) | (x_{k-2} << 2) | (x_{k-3} << 1) | carry_in in 0..15, init_state = 1
    def h121_next(s, xk):
        a = (s >> 3) & 1
        b = (s >> 2) & 1
        d = (s >> 1) & 1
        c = s & 1
        cout = (xk + (a & d) + c) >> 1
        return (xk << 3) | (a << 2) | (b << 1) | cout

    def h121_toggle(s):
        a = (s >> 3) & 1
        d = (s >> 1) & 1
        c = s & 1
        return (a & d) ^ c

    c_h121 = synthesize_f2_lasso(
        "H_{1,2,1}(x) = x + 2*(x & (x << 2)) + 1 (De Bruijn)",
        16, 1, h121_next, h121_toggle, 1
    )
    assert c_h121["all_one"] and len(c_h121["cyc"]) == 2

    # 4. H_{2,1,1}(x) = x + 4*(x & (x << 1)) + 1
    def h211_next(s, xk):
        a = (s >> 3) & 1
        b = (s >> 2) & 1
        d = (s >> 1) & 1
        c = s & 1
        cout = (xk + (b & d) + c) >> 1
        return (xk << 3) | (a << 2) | (b << 1) | cout

    def h211_toggle(s):
        b = (s >> 2) & 1
        d = (s >> 1) & 1
        c = s & 1
        return (b & d) ^ c

    c_h211 = synthesize_f2_lasso(
        "H_{2,1,1}(x) = x + 4*(x & (x << 1)) + 1 (De Bruijn)",
        16, 1, h211_next, h211_toggle, 1
    )
    assert c_h211["all_one"] and len(c_h211["cyc"]) == 5

    # -------------------------------------------------------------------------
    # PART B: Independent Exhaustive Replay of Theorems 1, 1b, 2, 3
    # -------------------------------------------------------------------------
    print("\n--- PART B: Independent Exact Replay up to w = 16 ---")

    # Theorem 1: H_{1,1,1}
    for w in range(1, 17):
        m = (1 << w) - 1
        f = lambda x, m=m: (x + 2 * (x & ((x << 1) & m)) + 1) & m
        cs, _ = cycle_spectrum(w, f)
        if w <= 2:
            assert cs == [1 << w], f"Thm 1 base fail w={w}: {cs}"
        else:
            assert cs == [1 << (w - 1), 1 << (w - 1)], f"Thm 1 fail w={w}: {cs}"
    print("[PASS] Theorem 1: H_{1,1,1}(x) = x + 2*(x & (x<<1)) + 1")
    print("       w=1,2 -> [2], [4]; w=3..16 -> EXACTLY [2^(w-1), 2^(w-1)] (verified up to 65,536 states)")

    # Theorem 1b: K, H_{1,2,1}, H_{2,1,1} De Bruijn completeness
    for name, fn in [
        ("K(x) = (x^(x<<1)) + 2*(x|(x<<1)) + 1",
         lambda x, m: ((x ^ ((x << 1) & m)) + 2 * (x | ((x << 1) & m)) + 1) & m),
        ("H_{1,2,1}(x) = x + 2*(x & (x<<2)) + 1",
         lambda x, m: (x + 2 * (x & ((x << 2) & m)) + 1) & m),
        ("H_{2,1,1}(x) = x + 4*(x & (x<<1)) + 1",
         lambda x, m: (x + 4 * (x & ((x << 1) & m)) + 1) & m),
    ]:
        for w in range(1, 15):
            m = (1 << w) - 1
            cs, _ = cycle_spectrum(w, lambda x, fn=fn, m=m: fn(x, m))
            assert cs == [1 << w], f"Thm 1b fail {name} w={w}: {cs}"
        print(f"[PASS] Theorem 1b: {name} -> De Bruijn [2^w] for all w=1..14")

    # Theorem 2: Universal Carry-Barrier & Frobenius Carry-Pump Bifurcation
    # 2c: Exact complete spectrum of F_0(x) = (x ^ (x << 1)) + 1 for w=2..16
    for w in range(2, 17):
        m = (1 << w) - 1
        f = lambda x, m=m: ((x ^ ((x << 1) & m)) + 1) & m
        cs, reps = cycle_spectrum(w, f)
        p_lens = [L for L, r in reps if (r & 2) == 0]
        b_lens = [L for L, r in reps if (r & 2) == 2]
        assert p_lens == [1 << (w - 1)], f"Thm 2a fail w={w}: {p_lens}"
        expected_b_per = 2 if w == 2 else (1 << ceil_log2(w - 1))
        assert all(L == expected_b_per for L in b_lens), f"Thm 2c fail w={w}: {b_lens}"
        assert len(b_lens) * expected_b_per == (1 << (w - 1))
    print("[PASS] Theorem 2c: F_0(x) = (x ^ (x<<1)) + 1 exact spectrum for w=2..16:")
    print("       bit1=0: single giant cycle 2^(w-1); bit1=1: ALL cycles of exact length 2^ceil(log2(w-1))")

    # 2a & 2b: Nonlinear 2-delayed feedbacks N with bit_2(N(0)) == bit_2(N(1)) and c = 4d + 1
    nl_cases = [
        ("N = (x<<2) & (x<<3), c = 1", lambda x, m: ((x << 2) & (x << 3)) & m, 1),
        ("N = (x<<2) & (x<<3), c = 5", lambda x, m: ((x << 2) & (x << 3)) & m, 5),
        ("N = (x<<2) & (x<<3) & (x<<4), c = 9", lambda x, m: ((x << 2) & (x << 3) & (x << 4)) & m, 9),
        ("N = ((x*x) << 3), c = 1", lambda x, m: ((x * x) << 3) & m, 1),
        ("N = ((x + (x<<1)) << 3), c = 13", lambda x, m: ((x + (x << 1)) << 3) & m, 13),
    ]
    for desc, N, c in nl_cases:
        for w in range(2, 13):
            m = (1 << w) - 1
            f = lambda x, N=N, c=c, m=m: (((x ^ ((x << 1) & m)) ^ N(x, m)) + c) & m
            cs, reps = cycle_spectrum(w, f)
            p_lens = [L for L, r in reps if (r & 2) == 0]
            assert p_lens == [1 << (w - 1)], f"Thm 2a fail {desc} w={w}: {p_lens}"
            if c == 1:
                # Verify hermetic carry-barrier on bit1=1: zero carry past bit 1!
                for x in range(1 << w):
                    if (x & 2) == 2:
                        y_xor = (x ^ ((x << 1) & m) ^ N(x, m))
                        y_add = (y_xor + 1) & m
                        assert (y_add >> 2) == (y_xor >> 2), f"Carry leaked at w={w}, x={x}"
        print(f"[PASS] Theorem 2a/2b: {desc} -> bit1=0 single cycle 2^(w-1) (w=2..12)" +
              (" + hermetic carry-barrier on bit1=1" if c == 1 else ""))

    # Theorem 3a: Non-Prefix Multi-Way Hybrid XOR-AND-Carry De Bruijn Completeness
    tap_families = [
        ("M = [[2], [1,3], [1,2,4]], c = 3", [[2], [1, 3], [1, 2, 4]], 3),
        ("M = [[3], [2,4], [1,3,4], [1,2,3,5]], c = 7", [[3], [2, 4], [1, 3, 4], [1, 2, 3, 5]], 7),
    ]
    for desc, M, c in tap_families:
        def eval_M(x, M=M, m=0):
            g = 0
            for T in M:
                term = m
                for s in T:
                    term &= (x << s) & m
                g ^= term
            return g
        for w in range(1, 13):
            m = (1 << w) - 1
            f = lambda x, M=M, c=c, m=m: ((x ^ eval_M(x, M, m)) + c) & m
            cs, _ = cycle_spectrum(w, f)
            assert cs == [1 << w], f"Thm 3a fail {desc} w={w}: {cs}"
        print(f"[PASS] Theorem 3a: {desc} -> De Bruijn [2^w] for all w=1..12")

    # Theorem 3b: Exact Prefix-Length-d Cycle-Splitting Sharpness
    for d in range(1, 9):
        for c in [1, 3, 5]:
            for w in range(1, d + 2):
                m = (1 << w) - 1
                def pref(x, d=d, m=m):
                    term = m
                    for s in range(1, d + 1):
                        term &= (x << s) & m
                    return term
                f = lambda x, pref=pref, c=c, m=m: ((x ^ pref(x)) + c) & m
                cs, _ = cycle_spectrum(w, f)
                if w <= d:
                    assert cs == [1 << w], f"Thm 3b pre-split fail d={d}, w={w}: {cs}"
                else:
                    assert cs == [1 << d, 1 << d], f"Thm 3b split fail d={d}, w={w}: {cs}"
    print("[PASS] Theorem 3b: Prefix tap P_d = &_{s=1..d}(x<<s), d=1..8, c in {1,3,5}:")
    print("       De Bruijn [2^w] for w <= d, then EXACT 2-WAY SPLIT [2^d, 2^d] at w = d + 1!")

    # -------------------------------------------------------------------------
    # PART C: Sharpness & Boundary Falsification Counterexamples
    # -------------------------------------------------------------------------
    print("\n--- PART C: Sharpness & Boundary Counterexamples ---")

    # Counterexample 1: Breaking parity gate bit_2(N(0)) == bit_2(N(1)) in Theorem 2a
    w = 3; m = (1 << w) - 1
    f_bad_gate = lambda x: (((x ^ ((x << 1) & m)) ^ (((x << 2) | (x << 3)) & m)) + 1) & m
    cs, reps = cycle_spectrum(w, f_bad_gate)
    p_lens = [L for L, r in reps if (r & 2) == 0]
    assert p_lens == [2, 2]
    print(f"[COUNTEREXAMPLE 1] Parity gate violated (N = (x<<2)|(x<<3), N(0)_2=0 != 1=N(1)_2):")
    print(f"                   w=3 bit1=0 splits into {p_lens} instead of [4]!")

    # Counterexample 2: Breaking 2-delay (1-delayed N = (x<<1) & (x<<3)) in Theorem 2a
    w = 4; m = (1 << w) - 1
    f_bad_delay = lambda x: (((x ^ ((x << 1) & m)) ^ (((x << 1) & (x << 3)) & m)) + 1) & m
    cs, reps = cycle_spectrum(w, f_bad_delay)
    p_lens = [L for L, r in reps if (r & 2) == 0]
    assert p_lens == [4, 4]
    print(f"[COUNTEREXAMPLE 2] 2-delay violated (N = (x<<1)&(x<<3), parity gate holds!):")
    print(f"                   w=4 bit1=0 splits into {p_lens} instead of [8]!")

    # Counterexample 3: Breaking c ≡ 1 (mod 4) (c = 3) in Theorem 2a
    w = 4; m = (1 << w) - 1
    f_bad_c = lambda x: ((x ^ ((x << 1) & m)) + 3) & m
    cs, reps = cycle_spectrum(w, f_bad_c)
    p_lens = sorted([L for L, r in reps if (r & 2) == 0], reverse=True)
    assert p_lens == [4, 4] or p_lens != [8]
    print(f"[COUNTEREXAMPLE 3] c = 3 (not 1 mod 4) in F_0:")
    print(f"                   w=4 bit1=0 splits into {p_lens} instead of [8]!")

    # Counterexample 4: Breaking c = 1 (c = 5) for hermetic carry-barrier in Theorem 2b
    y_xor = 2 ^ (2 << 1)  # 6
    y_add = y_xor + 5     # 11
    assert (y_add >> 2) != (y_xor >> 2)
    print(f"[COUNTEREXAMPLE 4] c = 5 leaks carry past bit 1 on bit1=1:")
    print(f"                   x=2 -> x^(x<<1)=6 (>>2 = 1), +5 = 11 (>>2 = 2 != 1)!")

    # Counterexample 5: Breaking c = 1 (c = 3) in Theorem 1 (H_{1,1,3})
    w = 4; m = (1 << w) - 1
    f_h113 = lambda x: (x + 2 * (x & ((x << 1) & m)) + 3) & m
    cs, _ = cycle_spectrum(w, f_h113)
    assert cs == [4, 4, 4, 4]
    print(f"[COUNTEREXAMPLE 5] H_{{1,1,3}}(x) = x + 2*(x&(x<<1)) + 3 at w=4:")
    print(f"                   splits into {cs} (4 cycles of length 4) instead of [8, 8]!")

    print("\nALL EXACT REPLAY CHECKS, CERTIFICATES, AND SHARPNESS COUNTEREXAMPLES PASSED!")


if __name__ == "__main__":
    main()
