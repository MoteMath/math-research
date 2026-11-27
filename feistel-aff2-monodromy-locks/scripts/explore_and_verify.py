"""
Exact Pure-Silicon Verification, Certificate Synthesis & Falsification Suite
for the Bit-Slice Aff(F_2^2)-Monodromy Tower Engine (dynsil-6).

All computations use exact arbitrary-precision Python integers / bitmasks (ZERO floats).
"""
from collections import Counter
from math import comb


# ============================================================================
# 1. Exact Finite Group Aff(F_2^2) Certificate Synthesis & Verification
# ============================================================================

def aff_id():
    return (1, 0, 0, 1, 0, 0)

def aff_det(T):
    m00, m01, m10, m11, _, _ = T
    return (m00 & m11) ^ (m01 & m10)

def aff_apply(T, x):
    m00, m01, m10, m11, v0, v1 = T
    a, b = x
    return (((m00 & a) ^ (m01 & b) ^ v0), ((m10 & a) ^ (m11 & b) ^ v1))

def aff_comp(T2, T1):
    a00, a01, a10, a11, av0, av1 = T2
    b00, b01, b10, b11, bv0, bv1 = T1
    return (
        (a00 & b00) ^ (a01 & b10),
        (a00 & b01) ^ (a01 & b11),
        (a10 & b00) ^ (a11 & b10),
        (a10 & b01) ^ (a11 & b11),
        (a00 & bv0) ^ (a01 & bv1) ^ av0,
        (a10 & bv0) ^ (a11 & bv1) ^ av1,
    )

def aff_pow(T, n):
    res = aff_id()
    for _ in range(n):
        res = aff_comp(T, res)
    return res

def feistel_step_aff(d, c):
    return (0, 1, 1, d, 0, c)

def verify_finite_group_certificates():
    print("=== 1. Finite Aff(F_2^2) Group Certificates ===")
    all_inv = [
        (m00, m01, m10, m11, v0, v1)
        for m00 in (0, 1) for m01 in (0, 1)
        for m10 in (0, 1) for m11 in (0, 1)
        for v0 in (0, 1) for v1 in (0, 1)
        if ((m00 & m11) ^ (m01 & m10)) == 1
    ]
    assert len(all_inv) == 24, f"Expected |Aff(F_2^2)| = 24, got {len(all_inv)}"

    cycle_types = Counter()
    for T in all_inv:
        assert aff_pow(T, 12) == aff_id()
        pts = [(0, 0), (0, 1), (1, 0), (1, 1)]
        seen = set()
        lens = []
        for p in pts:
            if p in seen:
                continue
            cur = p
            k = 0
            while cur not in seen:
                seen.add(cur)
                cur = aff_apply(T, cur)
                k += 1
            lens.append(k)
        cycle_types[tuple(sorted(lens))] += 1

    expected_types = {
        (1, 1, 1, 1): 1,
        (2, 2): 3,
        (1, 1, 2): 6,
        (4,): 6,
        (1, 3): 8,
    }
    assert dict(cycle_types) == expected_types, f"Unexpected cycle types: {cycle_types}"

    J0 = feistel_step_aff(0, 0)
    J1 = feistel_step_aff(1, 0)
    T_on_1001 = feistel_step_aff(0, 1)
    T_on_1011 = feistel_step_aff(1, 1)

    assert aff_comp(J0, J0) == aff_id()
    assert aff_pow(J1, 3) == aff_id()
    # Period-12 hit-pairing identity
    assert aff_comp(T_on_1001, aff_comp(J1, aff_comp(J1, T_on_1001))) == J1
    # Period-6 half-block & carry cancellation
    half6 = aff_comp(J1, aff_comp(J1, T_on_1011))
    assert half6 == (1, 0, 0, 1, 1, 0)
    assert aff_comp(half6, half6) == aff_id()
    # ctz(tau) even-hit cancellation
    assert aff_pow(aff_comp(J0, J1), 2) == aff_id()
    # R - 1 double-hit translation
    assert aff_comp(T_on_1011, aff_comp(J1, T_on_1011)) == (1, 0, 0, 1, 1, 1)

    print(f"  |Aff(F_2^2)| = {len(all_inv)}, 5 orbit-split classes = {dict(cycle_types)}")
    print("  All 6 key finite-group cancellation certificates VERIFIED.")


# ============================================================================
# 2. Single-Trigger Compiler & Concrete Hardware Bit-Vector Verification
# ============================================================================

def single_trigger_eval(d_off, c_off, d_on, c_on, tau_fn, w, R):
    out = 0
    matched = True
    for k in range(w):
        rk = (R >> k) & 1
        bk = ((d_on & rk) ^ c_on) if matched else ((d_off & rk) ^ c_off)
        out |= (bk << k)
        if rk != tau_fn(k):
            matched = False
    return out

def verify_hardware_bridge():
    print("\n=== 2. Concrete Hardware Mixed-Op BitVec Bridge (w = 1..10) ===")
    hw_specs = [
        ("R + 1",            lambda R, m: (R + 1) & m,                  (1, 0, 1, 1), lambda k: 1),
        ("R - 1",            lambda R, m: (R - 1) & m,                  (1, 0, 1, 1), lambda k: 0),
        ("R | (R + 1)",      lambda R, m: (R | (R + 1)) & m,            (1, 0, 0, 1), lambda k: 1),
        ("R | (R - 1)",      lambda R, m: (R | (R - 1)) & m,            (1, 0, 0, 1), lambda k: 0),
        ("R ^ (R + 1)",      lambda R, m: (R ^ (R + 1)) & m,            (0, 0, 0, 1), lambda k: 1),
        ("R ^ (R - 1)",      lambda R, m: (R ^ (R - 1)) & m,            (0, 0, 0, 1), lambda k: 0),
        ("R & (-R)",         lambda R, m: (R & (-R)) & m,               (0, 0, 1, 0), lambda k: 0),
        ("R & ~(R + 1)",     lambda R, m: (R & (~(R + 1))) & m,         (0, 0, 1, 0), lambda k: 1),
    ]
    for name, hw_fn, rule, tau_fn in hw_specs:
        for w in range(1, 11):
            m = (1 << w) - 1
            for R in range(1 << w):
                got = hw_fn(R, m)
                exp = single_trigger_eval(*rule, tau_fn, w, R)
                assert got == exp, f"Mismatch for {name} at w={w}, R={R}: {got} != {exp}"
        print(f"  {name:16s} == SingleTrigger{rule}  VERIFIED for all w=1..10")


# ============================================================================
# 3. Exact Cycle Spectrum Verification of All Four Infinite Theorems
# ============================================================================

def exact_cycle_spectrum(w, f_table):
    N = 1 << w
    visited = bytearray(N * N)
    spec = Counter()
    for L in range(N):
        for R in range(N):
            idx = (L << w) | R
            if visited[idx]:
                continue
            curL, curR = L, R
            length = 0
            while not visited[(curL << w) | curR]:
                visited[(curL << w) | curR] = 1
                curL, curR = curR, curL ^ f_table[curR]
                length += 1
            spec[length] += 1
    return dict(sorted(spec.items()))

def verify_four_theorems(max_w=6):
    print(f"\n=== 3. Exhaustive Cycle-Spectrum Verification (w = 1..{max_w}) ===")

    # Theorem I: Rule (1,0,0,1) Universal Period-12 Lock across multiple triggers
    triggers = [
        ("tau=-1 [R|(R+1)]", lambda k: 1),
        ("tau=0  [R|(R-1)]", lambda k: 0),
        ("tau=alt(0101..)",  lambda k: k & 1),
        ("tau=0b11010..",    lambda k: 1 if (k % 3 != 0) else 0),
    ]
    for tname, tfn in triggers:
        for w in range(1, max_w + 1):
            ftab = [single_trigger_eval(1, 0, 0, 1, tfn, w, R) for R in range(1 << w)]
            sp = exact_cycle_spectrum(w, ftab)
            expected = {4: 1} if w == 1 else {4: 1, 12: ((1 << (2 * w)) - 4) // 12}
            assert sp == expected, f"Thm I fail ({tname}, w={w}): {sp} != {expected}"
    print(f"  Theorem I   (Universal Period-12 Lock, Rule (1,0,0,1)):    PASS for 4 triggers, w=1..{max_w}")

    # Theorem II: R + 1 Period-6 Lock vs R - 1 Exponential Escape (3 * 2^(w-1))
    for w in range(1, max_w + 1):
        m = (1 << w) - 1
        ftab_add1 = [(R + 1) & m for R in range(1 << w)]
        sp_add1 = exact_cycle_spectrum(w, ftab_add1)
        exp_add1 = {1: 1, 3: 1} if w == 1 else {1: 1, 3: 1, 6: ((1 << (2 * w)) - 4) // 6}
        assert sp_add1 == exp_add1, f"Thm IIa fail (w={w}): {sp_add1} != {exp_add1}"

        # Check (0, 0) exact minimal period = 3 * 2^(w-1) under R - 1
        ftab_sub1 = [(R - 1) & m for R in range(1 << w)]
        L, R = 0, 0
        steps = 0
        while True:
            L, R = R, L ^ ftab_sub1[R]
            steps += 1
            if (L, R) == (0, 0):
                break
        assert steps == 3 * (1 << (w - 1)), f"Thm IIb fail (w={w}): {steps}"
    # Also test R - 1 orbit of (0, 0) up to w = 14!
    for w in range(1, 15):
        m = (1 << w) - 1
        L, R = 0, 0
        steps = 0
        while True:
            L, R = R, L ^ ((R - 1) & m)
            steps += 1
            if (L, R) == (0, 0):
                break
        assert steps == 3 * (1 << (w - 1))
    print(f"  Theorem II  (R+1 Period-6 Lock vs R-1 Escape 3*2^(w-1)):   PASS (full w=1..{max_w}; R-1 orbit w=1..14)")

    # Theorem III: Rule (0,0,1,0) Binomial Power-of-3 & ctz(tau) Phase Transition
    for w in range(1, max_w + 1):
        m = (1 << w) - 1
        ftab_lsb = [(R & (-R)) & m for R in range(1 << w)]
        sp = exact_cycle_spectrum(w, ftab_lsb)
        exp = {3 ** j: comb(w, j) for j in range(w + 1)}
        assert sp == exp, f"Thm IIIa fail (w={w}): {sp} != {exp}"
    # Phase transition for tau with ctz(tau) = m in {0, 1, 2, 3}
    for tau_val, m_ctz in [(1, 0), (3, 0), (2, 1), (6, 1), (4, 2), (12, 2), (8, 3)]:
        tfn = lambda k, tv=tau_val: (tv >> k) & 1
        for w in range(1, max_w + 1):
            ftab = [single_trigger_eval(0, 0, 1, 0, tfn, w, R) for R in range(1 << w)]
            sp = exact_cycle_spectrum(w, ftab)
            if w <= m_ctz + 1:
                exp = {3 ** j: comb(w, j) for j in range(w + 1)}
            else:
                r = w - (m_ctz + 1)
                exp = {}
                for j in range(m_ctz + 2):
                    c = comb(m_ctz + 1, j)
                    exp[3 ** j] = (1 << r) * c
                    exp[2 * (3 ** j)] = ((1 << r) * ((1 << r) - 1) // 2) * c
            assert sp == dict(sorted(exp.items())), f"Thm IIIb fail (tau={tau_val}, w={w}): {sp} != {exp}"
    print(f"  Theorem III (Binomial 3^w & ctz(tau) Lock 2*3^(m+1)):      PASS for tau=0 and 7 nonzero triggers, w=1..{max_w}")

    # Theorem IV: Rule (0,0,0,1) Universal Isoperiodic 2^(w+1) Law
    for tname, tfn in triggers:
        for w in range(1, max_w + 1):
            ftab = [single_trigger_eval(0, 0, 0, 1, tfn, w, R) for R in range(1 << w)]
            sp = exact_cycle_spectrum(w, ftab)
            exp = {1 << (w + 1): 1 << (w - 1)}
            assert sp == exp, f"Thm IV fail ({tname}, w={w}): {sp} != {exp}"
    print(f"  Theorem IV  (Universal Isoperiodic 2^(w+1), Rule (0,0,0,1)): PASS for 4 triggers, w=1..{max_w}")


# ============================================================================
# 4. Sharpness & Boundary Counterexamples
# ============================================================================

def verify_sharpness_counterexamples():
    print("\n=== 4. Sharpness & Falsification Counterexamples ===")

    def orbit_period(w, f_fn, L0, R0):
        m = (1 << w) - 1
        L, R = L0 & m, R0 & m
        steps = 0
        while True:
            L, R = R, (L ^ f_fn(R, m)) & m
            steps += 1
            if (L, R) == (L0 & m, R0 & m):
                return steps

    # Counterexample 1: R | (R + 3) breaks Period-12 Lock at w = 3 (period 36!)
    s36 = next((L, R) for L in range(8) for R in range(8)
               if orbit_period(3, lambda R, m: (R | (R + 3)) & m, L, R) == 36)
    p1 = orbit_period(3, lambda R, m: (R | (R + 3)) & m, s36[0], s36[1])
    assert p1 == 36
    print(f"  [Sharpness Thm I-a]  f(R) = R | (R + 3) at w=3, state {s36}: exact period = {p1} (breaks lock 12)")

    # Counterexample 2: Flipping 1 rule bit (1,0,0,1) -> (1,0,0,0) [R & (R - 1)] breaks Period-12 at w = 4
    ftab_1000 = [(R & (R - 1)) & 15 for R in range(16)]
    sp_1000 = exact_cycle_spectrum(4, ftab_1000)
    assert max(sp_1000) == 16
    print(f"  [Sharpness Thm I-b]  f(R) = R & (R - 1) [Rule (1,0,0,0)] at w=4: max period = {max(sp_1000)} (breaks lock 12)")

    # Counterexample 3: R - 1 breaks R + 1 Period-6 Lock at w = 3 (period 12, grows as 3*2^(w-1))
    p3 = orbit_period(3, lambda R, m: (R - 1) & m, 0, 0)
    assert p3 == 12
    print(f"  [Sharpness Thm II]   f(R) = R - 1 at w=3, state (0,0): exact period = {p3} (breaks lock 6)")

    # Counterexample 4: Even constant R ^ (R + 2) breaks 2^(w+1) isoperiodic law at w = 2
    p4 = orbit_period(2, lambda R, m: (R ^ (R + 2)) & m, 0, 0)
    assert p4 == 4  # instead of 2^(2+1) = 8
    print(f"  [Sharpness Thm IV]   f(R) = R ^ (R + 2) at w=2, state (0,0): exact period = {p4} != 8 (needs odd carry)")

    # Counterexample 5: Non-triangular right-shift f(R) = R + (R >> 1) breaks universal 2^a * 3^b law at w = 2
    s5 = next((L, R) for L in range(4) for R in range(4)
              if orbit_period(2, lambda R, m: (R + (R >> 1)) & m, L, R) == 5)
    p5 = orbit_period(2, lambda R, m: (R + (R >> 1)) & m, s5[0], s5[1])
    assert p5 == 5
    print(f"  [Sharpness Engine]   Non-triangular f(R) = R + (R >> 1) at w=2, state {s5}: exact period = {p5} (prime 5 not 2^a*3^b!)")


if __name__ == "__main__":
    verify_finite_group_certificates()
    verify_hardware_bridge()
    verify_four_theorems(max_w=6)
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED.")
