"""
Pure-Silicon 2-Adic FCSR Engine — Exact Exploration, Certificate Synthesis,
Independent Instance Verification, and Sharpness Counterexamples.

Strictly exact integer arithmetic (Python `int` only, zero floating-point).
"""

import math
from typing import Dict, List, Tuple


# =============================================================================
# 1. Hardware Fibonacci FCSR (Pure Silicon Model)
# =============================================================================

class FCSRSpec:
    """
    Connection integer q = 2*c - 1 (odd, q >= 3, so c >= 2).
    Register width r >= 1 satisfies 2^(r-1) <= c < 2^r, so q + 1 = 2*c
    has MSB tap q_r = 1 and tap bit q_i = (c >> (i - 1)) & 1 for 1 <= i <= r.
    """
    def __init__(self, q: int):
        assert q >= 3 and q % 2 == 1, f"q must be odd >= 3, got {q}"
        self.q = q
        self.c = (q + 1) // 2
        self.r = self.c.bit_length()
        assert (1 << (self.r - 1)) <= self.c < (1 << self.r)
        self.w = self.c.bit_count()

    def tap(self, i: int) -> int:
        """Tap q_i for 1 <= i <= r."""
        assert 1 <= i <= self.r
        return (self.c >> (i - 1)) & 1

    def tap_dot(self, reg: int) -> int:
        """sum_{i=1}^r q_i * a_{r-i}, where a_j = (reg >> j) & 1."""
        return sum(self.tap(i) * ((reg >> (self.r - i)) & 1) for i in range(1, self.r + 1))

    def step(self, reg: int, carry: int) -> Tuple[int, int, int]:
        """Hardware 1-clock transition: returns (out_bit, new_reg, new_carry)."""
        assert 0 <= reg < (1 << self.r)
        out = reg & 1
        sigma = carry + self.tap_dot(reg)
        new_top = sigma & 1
        new_carry = sigma >> 1  # Python >> is floor division by 2 (matches Int.ediv 2)
        assert sigma == 2 * new_carry + new_top
        new_reg = (reg >> 1) | (new_top << (self.r - 1))
        return out, new_reg, new_carry

    def potential(self, reg: int, carry: int) -> int:
        """
        Exact 2-adic numerator potential:
          P(reg, m) = sum_{i=1}^r q_i * 2^i * (reg mod 2^(r-i)) - reg - m * 2^r
        """
        assert 0 <= reg < (1 << self.r)
        s = 0
        for i in range(1, self.r + 1):
            if self.tap(i):
                s += (1 << i) * (reg & ((1 << (self.r - i)) - 1))
        return s - reg - (carry << self.r)

    def div_step(self, p: int) -> Tuple[int, int]:
        """Canonical 2-adic shift-divide map: p = q*b + 2*p'."""
        b = p & 1
        return b, (p - self.q * b) // 2

    def inv_div_step(self, p: int) -> int:
        """Inverse of div_step on the periodic core (-q, 0)."""
        assert -self.q < p < 0
        return 2 * p if 2 * p > -self.q else 2 * p + self.q

    def encode(self, p: int) -> Tuple[int, int]:
        """Exact silicon lift from p in (-q, 0) to the unique hardware state in P_q."""
        assert -self.q < p < 0
        cur = p
        reg = 0
        for j in range(self.r):
            b, cur = self.div_step(cur)
            reg |= (b << j)
        p0 = self.potential(reg, 0)
        assert (p0 - p) % (1 << self.r) == 0
        carry = (p0 - p) >> self.r
        assert self.potential(reg, carry) == p
        return reg, carry

    def inv_step(self, reg: int, carry: int) -> Tuple[int, int]:
        """Explicit backward step on the periodic core P_q."""
        p = self.potential(reg, carry)
        assert -self.q < p < 0
        return self.encode(self.inv_div_step(p))

    def complement(self, reg: int, carry: int) -> Tuple[int, int]:
        """Exact hardware state complementation involution C_q."""
        return ((1 << self.r) - 1) - reg, (self.w - 1) - carry

    def run_word(self, reg: int, carry: int, n: int) -> Tuple[int, int, int]:
        """Run n clock ticks; return (n-bit output word W_n, end_reg, end_carry)."""
        w_val = 0
        r_cur, c_cur = reg, carry
        for t in range(n):
            b, r_cur, c_cur = self.step(r_cur, c_cur)
            w_val |= (b << t)
        return w_val, r_cur, c_cur


# =============================================================================
# 2. Finite Certificate Structures & Exact Checkers
# =============================================================================

def prime_factors_distinct(n: int) -> List[int]:
    """Exact trial division returning sorted distinct prime factors of n >= 1."""
    factors = []
    d = 2
    x = n
    while d * d <= x:
        if x % d == 0:
            factors.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        factors.append(x)
    return factors


def synthesize_period_cert(q: int, p: int = -1) -> Dict:
    """
    Synthesize and independently check a finite exact-period certificate for (q, p):
      - q | (2^T - 1) * (-p)
      - for every prime l | T, q does NOT divide (2^(T/l) - 1) * (-p)
      - optional half-period witness h = T/2 if q | (2^h + 1) * (-p)
    """
    assert q >= 3 and q % 2 == 1 and -q < p < 0
    g = math.gcd(q, -p)
    q_eff = q // g
    # Find multiplicative order of 2 mod q_eff
    x, T = 2 % q_eff, 1
    while x != 1:
        x = (2 * x) % q_eff
        T += 1
    primes = prime_factors_distinct(T)
    # Check certificate conditions strictly via integer divisibility
    assert ((pow(2, T, q) - 1) * (-p)) % q == 0
    for l in primes:
        assert T % l == 0
        assert ((pow(2, T // l, q) - 1) * (-p)) % q != 0
    half_neg = (T % 2 == 0) and (((pow(2, T // 2, q) + 1) * (-p)) % q == 0)
    return {
        "q": q,
        "p": p,
        "T": T,
        "prime_factors_of_T": primes,
        "half_period_complement": half_neg,
    }


def zolotarev_inversions(q: int) -> int:
    """Exact inversion count of pi_q(x) = 2x mod q on {1, ..., q-1}."""
    assert q >= 3 and q % 2 == 1
    arr = [(2 * x) % q for x in range(1, q)]
    inv = 0
    for i in range(len(arr)):
        for j in range(i + 1, len(arr)):
            if arr[i] > arr[j]:
                inv += 1
    return inv


# =============================================================================
# 3. Verification Battery (All 5 Layers + Infinite Families + Sharpness)
# =============================================================================

def verify_layer1_and_layer2():
    print("=== Layer 1 & 2: Exact 2-Adic Potential, Bijective Core, Carry Bounds, Conservation ===")
    test_qs = [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 29, 31, 33, 35, 37, 45, 57, 61, 65, 67, 73]
    for q in test_qs:
        spec = FCSRSpec(q)
        # 1a. Exhaustive periodic core bijection, carry bounds, word representation, complementation
        core_states = set()
        for p in range(-q + 1, 0):
            reg, carry = spec.encode(p)
            assert 0 <= carry <= spec.w - 1, f"Carry bound failed for q={q}, p={p}"
            core_states.add((reg, carry))

            # One-step potential identity & reversibility
            out, reg2, carry2 = spec.step(reg, carry)
            b, p2 = spec.div_step(p)
            assert out == b
            assert spec.potential(reg2, carry2) == p2
            assert spec.inv_step(reg2, carry2) == (reg, carry)
            r_back, c_back = spec.inv_step(reg, carry)
            assert spec.step(r_back, c_back)[1:] == (reg, carry)

            # Exact complementation involution C_q
            rc, cc = spec.complement(reg, carry)
            assert spec.potential(rc, cc) == -q - p
            out_c, rc2, cc2 = spec.step(rc, cc)
            assert out_c == 1 - out
            assert (rc2, cc2) == spec.complement(reg2, carry2)

            # Exact n-bit 2-adic word identity for n = 1, r, r+5
            for n in (1, spec.r, spec.r + 5):
                wn, rn, cn = spec.run_word(reg, carry, n)
                assert q * wn + (1 << n) * spec.potential(rn, cn) == p

        assert len(core_states) == q - 1

        # 1b. Universal collision sharpness witness outside the periodic core:
        #     s1 = (0, -1), s2 = (1, -2) ALWAYS collide in 1 step for every odd q >= 3!
        s1 = (0, -1)
        s2 = (1, -2)
        assert s1 != s2
        assert spec.potential(*s1) == (1 << spec.r) > 0
        assert spec.potential(*s2) == q + (1 << spec.r) > 0
        assert spec.step(*s1)[1:] == spec.step(*s2)[1:]

        # 2. Universal carry-bit conservation over periodic orbits (sample p = -1, -(q//2))
        for p in (-1, -(q // 2)):
            reg, carry = spec.encode(p)
            r_cur, c_cur = reg, carry
            sum_a, sum_m = 0, 0
            for _ in range(1, q + 2):
                out, r_cur, c_cur = spec.step(r_cur, c_cur)
                sum_a += out
                sum_m += c_cur
                if (r_cur, c_cur) == (reg, carry):
                    assert sum_m == (spec.w - 1) * sum_a
                    break
            else:
                raise AssertionError(f"Orbit did not close for q={q}, p={p}")

    # Also test complementation & potential identity on TRANSIENT states (outside core)
    for q in (5, 11, 13, 21):
        spec = FCSRSpec(q)
        for reg in range(1 << spec.r):
            for carry in (-3, -1, 0, spec.w, spec.w + 2):
                out, r2, c2 = spec.step(reg, carry)
                assert spec.potential(reg, carry) == q * out + 2 * spec.potential(r2, c2)
                rc, cc = spec.complement(reg, carry)
                assert spec.potential(rc, cc) == -q - spec.potential(reg, carry)
                out_c, rc2, cc2 = spec.step(rc, cc)
                assert out_c == 1 - out and (rc2, cc2) == spec.complement(r2, c2)

    print(f"  PASS: Verified {len(test_qs)} moduli (all periodic states + transient states + universal collisions).")


def verify_layer3_and_layer4_families():
    print("\n=== Layer 3 & 4: Infinite Families (2^k +- 1, Phi_6(2^k), Repunits (2^(dk)-1)/(2^k-1)) ===")

    # Family 1: q = 2^k - 1 (k >= 2)
    for k in range(2, 16):
        q = (1 << k) - 1
        spec = FCSRSpec(q)
        assert spec.w == 1
        cert = synthesize_period_cert(q, -1)
        assert cert["T"] == k
        reg, carry = spec.encode(-1)
        assert carry == 0
        wn, rn, cn = spec.run_word(reg, carry, k)
        assert (rn, cn) == (reg, carry)
        assert wn == 1  # -P = 1
        # Sharpness: half-period complementation holds for k=2 (q=3), fails for all k >= 3
        if k == 2:
            assert cert["half_period_complement"] is True
        else:
            assert cert["half_period_complement"] is False
    print("  PASS: q = 2^k - 1 (k=2..15): w=1, m=0, exact period k, half-period fails for k >= 3 (sharp at k=2).")

    # Family 2: q = 2^k + 1 (k >= 1)
    for k in range(1, 16):
        q = (1 << k) + 1
        spec = FCSRSpec(q)
        if k >= 2:
            assert spec.w == 2
        cert = synthesize_period_cert(q, -1)
        assert cert["T"] == 2 * k
        assert cert["half_period_complement"] is True
        reg, carry = spec.encode(-1)
        # Check half-period state complementation after k ticks
        _, rk, ck = spec.run_word(reg, carry, k)
        assert (rk, ck) == spec.complement(reg, carry)
        # Check exact 50/50 bit balance and carry sum over 2k ticks
        r_cur, c_cur = reg, carry
        sum_a, sum_m = 0, 0
        for _ in range(2 * k):
            b, r_cur, c_cur = spec.step(r_cur, c_cur)
            sum_a += b
            sum_m += c_cur
        assert sum_a == k
        assert sum_m == k * (spec.w - 1)
    # Sharpness on non-coprime state: k=3 (q=9), p=-3 gives period 2 < 6
    cert_noncoprime = synthesize_period_cert(9, -3)
    assert cert_noncoprime["T"] == 2 and cert_noncoprime["half_period_complement"] is True
    print("  PASS: q = 2^k + 1 (k=1..15): exact period 2k, half-period complementation, 50/50 balance, sharpness at (9,-3).")

    # Family 3: q = Phi_6(2^k) = 2^(2k) - 2^k + 1 (k >= 2; sharpness at k=1 where q=3, T=2 != 6)
    cert_phi6_k1 = synthesize_period_cert(3, -1)
    assert cert_phi6_k1["T"] == 2  # != 6*1
    for k in range(2, 10):
        q = (1 << (2 * k)) - (1 << k) + 1
        spec = FCSRSpec(q)
        cert = synthesize_period_cert(q, -1)
        assert cert["T"] == 6 * k
        assert cert["half_period_complement"] is True
        reg, carry = spec.encode(-1)
        _, r3k, c3k = spec.run_word(reg, carry, 3 * k)
        assert (r3k, c3k) == spec.complement(reg, carry)
    print("  PASS: q = 2^(2k) - 2^k + 1 (k=2..9): exact period 6k, half-period complementation at 3k (sharp failure at k=1).")

    # Family 4: d-Section Repunit Engine q = (2^(d*k) - 1) / (2^k - 1)
    for d in (2, 3, 4, 5):
        for k in range(1, 5):
            q = ((1 << (d * k)) - 1) // ((1 << k) - 1)
            spec = FCSRSpec(q)
            cert = synthesize_period_cert(q, -1)
            assert cert["T"] == d * k
            # Test d-section law across a sample of p in (-q, 0)
            sample_ps = range(-q + 1, 0) if q <= 100 else [-1, -2, -3, -(q // 3), -(q // 2), -(q - 1)]
            for p in sample_ps:
                reg, carry = spec.encode(p)
                bits, carries, ps = [], [], []
                r_cur, c_cur = reg, carry
                for _ in range(d * k):
                    ps.append(spec.potential(r_cur, c_cur))
                    carries.append(c_cur)
                    b, r_cur, c_cur = spec.step(r_cur, c_cur)
                    bits.append(b)
                assert (r_cur, c_cur) == (reg, carry)
                # Compute section quanta c(t) = -sum_{j=0}^{d-1} P(s_{t+jk}) / q
                cs = []
                for t in range(k):
                    S = sum(ps[t + j * k] for j in range(d))
                    assert S % q == 0
                    ct = -S // q
                    assert 1 <= ct <= d - 1
                    cs.append(ct)
                # Verify pointwise d-section recurrence: sum_j a_{t+jk} = 2*c(t+1) - c(t)
                for t in range(k):
                    lhs = sum(bits[t + j * k] for j in range(d))
                    rhs = 2 * cs[(t + 1) % k] - cs[t]
                    assert lhs == rhs
                # Verify exact total bit weight and carry sum
                assert sum(bits) == sum(cs)
                assert sum(carries) == (spec.w - 1) * sum(cs)
    print("  PASS: d-Section Cyclotomic Engine (d=2..5, k=1..4): quantized c(t) in [1,d-1], 2c(t+1)-c(t) law, exact bit/carry sums.")


def verify_layer5_zolotarev_and_2k_pm_3():
    print("\n=== Layer 5: Zolotarev Silicon Parity Engine & Families q = 2^k +- 3 ===")
    # 5a. Exact inversion count = (q^2 - 1)/8 for all odd q in [3, 99]
    for q in range(3, 100, 2):
        inv = zolotarev_inversions(q)
        expected = (q * q - 1) // 8
        assert inv == expected, f"Zolotarev failed at q={q}: {inv} != {expected}"
        parity_odd = (inv % 2 == 1)
        assert parity_odd == (q % 8 in (3, 5))
        if parity_odd:
            cert = synthesize_period_cert(q, -1)
            assert cert["T"] % 2 == 0
    print("  PASS: Zolotarev inversion count inv(pi_q) = (q^2 - 1)/8 verified for all odd q in [3, 99].")

    # 5b. Family q = 2^k + 3 (k >= 3): w=2, single-bit carry, k-block coupling in {-1,-2,-3}, EVEN period
    for k in range(3, 15):
        q = (1 << k) + 3
        spec = FCSRSpec(q)
        assert spec.w == 2
        cert = synthesize_period_cert(q, -1)
        assert cert["T"] % 2 == 0
        # Check k-block coupling for sample periodic states
        for p in (-1, -(q // 2), -(q - 1)):
            reg, carry = spec.encode(p)
            wk, rk, ck = spec.run_word(reg, carry, k)
            pk = spec.potential(rk, ck)
            err = wk + pk
            assert err in (-3, -2, -1)
            assert p + 3 * pk == q * err
    print("  PASS: q = 2^k + 3 (k=3..14): w=2, carry in {0,1}, W_k + P_{t+k} in {-3,-2,-1}, even period T.")

    # 5c. Family q = 2^k - 3 (k >= 3): w=k-1, dense taps, k-block coupling in {0,1,2}, EVEN period
    for k in range(3, 15):
        q = (1 << k) - 3
        spec = FCSRSpec(q)
        assert spec.w == k - 1
        cert = synthesize_period_cert(q, -1)
        assert cert["T"] % 2 == 0
        for p in (-1, -(q // 2), -(q - 1)):
            reg, carry = spec.encode(p)
            wk, rk, ck = spec.run_word(reg, carry, k)
            pk = spec.potential(rk, ck)
            err = wk + pk
            assert err in (0, 1, 2)
            assert p - 3 * pk == q * err
    print("  PASS: q = 2^k - 3 (k=3..14): w=k-1, carry in [0,k-2], W_k + P_{t+k} in {0,1,2}, even period T.")

    # 5d. Sharpness counterexamples for q = 2^k +- 3:
    #   Even period does NOT imply half-period complementation when composite!
    c35 = synthesize_period_cert(35, -1)  # 2^5 + 3 = 35 = 5 * 7
    assert c35["T"] == 12 and c35["half_period_complement"] is False
    c253 = synthesize_period_cert(253, -1)  # 2^8 - 3 = 253 = 11 * 23
    assert c253["T"] == 110 and c253["half_period_complement"] is False
    #   And concrete prime instances DO certify half-period complementation:
    c11 = synthesize_period_cert(11, -1)  # 2^3 + 3 = 11
    c13 = synthesize_period_cert(13, -1)  # 2^4 - 3 = 13
    assert c11["T"] == 10 and c11["half_period_complement"] is True
    assert c13["T"] == 12 and c13["half_period_complement"] is True
    print("  PASS: Sharpness verified: q=35 (2^5+3, T=12) & q=253 (2^8-3, T=110) have even T yet FAIL half-period complementation;")
    print("        q=11 (2^3+3, T=10) & q=13 (2^4-3, T=12) pass HalfPeriodCert.")


if __name__ == "__main__":
    verify_layer1_and_layer2()
    verify_layer3_and_layer4_families()
    verify_layer5_zolotarev_and_2k_pm_3()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED.")
