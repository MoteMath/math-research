#!/usr/bin/env python3
"""
Task 12 (adic-12): Carryless (F_2[x]) vs. Carried (Z) 2-Adic Polynomial-Bridge
Hensel-Isometry Engine — Exact Exploration, Certificate Synthesis, Verification,
and Sharpness Counterexample Suite.

Pure silicon integer arithmetic only (zero floating-point values anywhere).
"""

import sys


def clmul(a: int, b: int) -> int:
    """Carryless multiplication in F_2[x] encoded as non-negative integers."""
    res = 0
    while b:
        if b & 1:
            res ^= a
        a <<= 1
        b >>= 1
    return res


def clpow(a: int, k: int) -> int:
    """Carryless exponentiation P_a(x)^k mod 2 encoded as a non-negative integer."""
    res = 1
    base = a
    while k:
        if k & 1:
            res = clmul(res, base)
        base = clmul(base, base)
        k >>= 1
    return res


def spread(r: int, n: int) -> int:
    """Bit-spreading operator S_r(n) = sum_i bit(n, i) * 2^(r * i)."""
    res = 0
    shift = 0
    while n:
        if n & 1:
            res |= 1 << shift
        shift += r
        n >>= 1
    return res


def v2(n: int) -> int:
    """Exact 2-adic valuation of a nonzero integer."""
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length() - 1


def F_bridge(a: int, e: int, B: int, n: int) -> int:
    """
    Perturbed Carried-vs-Carryless Resonant Bridge Operator:
        F_{a,e,B}(n) = B * a^(2^e * (2n + 1)) - clmul(B, clpow(a, 2^e * (2n + 1))).
    """
    k = (1 << e) * (2 * n + 1)
    return B * pow(a, k) - clmul(B, clpow(a, k))


def hensel_lift(F, L: int, steps: int) -> int:
    """
    Constructive bit-by-bit silicon Hensel lifter for any scaled isometry F at scale L.
    Returns nu_steps < 2^steps such that 2^(L + steps) | F(nu_steps).
    """
    n = 0
    for t in range(steps):
        if F(n) % (1 << (L + t + 1)) != 0:
            n += 1 << t
    return n


def verify_four_regime_law() -> None:
    print("[1] Verifying Complete 4-Regime Global Valuation Law...")
    regimes = {1: 0, 2: 0, 3: 0, 4: 0}
    for a in range(3, 128, 2):
        r = v2(a - 1)
        s = v2(a + 1) if (a % 4 == 3) else 0
        for k in range(2, 129, 2):
            e = v2(k)
            diff = pow(a, k) - clpow(a, k)
            assert diff > 0, f"Expected strict positivity at a={a}, k={k}"
            val = v2(diff)
            if a % 4 == 1:
                assert val == r + e, f"Regime I failed at a={a}, k={k}"
                regimes[1] += 1
            else:
                E = 1 << e
                if E < s + e:
                    assert val == E, f"Regime II failed at a={a}, k={k}"
                    regimes[2] += 1
                elif E > s + e:
                    assert val == s + e, f"Regime III failed at a={a}, k={k}"
                    regimes[3] += 1
                else:
                    assert s == E - e
                    assert val >= E + 1, f"Regime IV lower bound failed at a={a}, k={k}"
                    regimes[4] += 1
    print(
        f"    PASS: {sum(regimes.values())} pairs checked "
        f"(Regime I: {regimes[1]}, II: {regimes[2]}, III: {regimes[3]}, IV-resonant: {regimes[4]})."
    )


def verify_hensel_isometry_and_root_shift() -> None:
    print("[2] Verifying 2-Adic Hensel-Isometry Lifting, Exact Valuation, Invariance & Bit-(2^e) Shift...")
    resonant_pairs = [(3, 2), (11, 2), (19, 2), (27, 2), (35, 2), (31, 3), (95, 3)]
    checked_lifts = 0
    checked_vals = 0
    for a, e in resonant_pairs:
        E = 1 << e
        L = E + 1
        assert a % 4 == 3 and v2(a + 1) == E - e
        steps = 5 if e == 2 else 4
        nu1 = hensel_lift(lambda n, a=a, e=e: F_bridge(a, e, 1, n), L, steps)
        # Verify coherence of tower
        for t in range(steps):
            nu_t = hensel_lift(lambda n, a=a, e=e: F_bridge(a, e, 1, n), L, t)
            assert nu_t == (nu1 % (1 << t))
            assert F_bridge(a, e, 1, nu_t) % (1 << (L + t)) == 0

        multipliers = [1, 3, 5, 7, 15, 17, 19, 31, 255, 257]
        for B in multipliers:
            nuB = hensel_lift(lambda n, a=a, e=e, B=B: F_bridge(a, e, B, n), L, steps)
            checked_lifts += 1
            # Root invariance for B < 2^(2^e)
            if B < (1 << E):
                assert nuB == nu1, f"Invariance failed at a={a}, e={e}, B={B}"
            # Bit-(2^e) root shift law
            bit_E = (B >> E) & 1
            assert (nuB & 1) == ((nu1 ^ bit_E) & 1), (
                f"Root-shift law failed at a={a}, e={e}, B={B}"
            )
            # Exhaustive valuation law on all n < 2^steps
            for n in range(1 << steps):
                val = F_bridge(a, e, B, n)
                assert val > 0
                if n == nuB:
                    assert val % (1 << (L + steps)) == 0
                else:
                    assert v2(val) == L + v2(n - nuB)
                checked_vals += 1

    print(
        f"    PASS: {checked_lifts} resonant Hensel lifts & {checked_vals} exact valuations verified."
    )


def synthesize_deep_roots() -> None:
    print("[3] Synthesizing High-Precision 2-Adic Resonant Roots (Exact Silicon Lift):")
    for a, e, steps in [(3, 2, 10), (11, 2, 8), (19, 2, 8), (31, 3, 6)]:
        E = 1 << e
        L = E + 1
        nu = hensel_lift(lambda n, a=a, e=e: F_bridge(a, e, 1, n), L, steps)
        m = 2 * nu + 1
        k = E * m
        val = pow(a, k) - clpow(a, k)
        got_v2 = v2(val)
        assert got_v2 >= L + steps
        print(
            f"    (a={a:2d}, e={e}, s={E-e}): nu mod 2^{steps:2d} = {nu:4d} "
            f"(m={m:4d}, k={k:5d}) -> v2(a^k - clpow(a,k)) = {got_v2} >= {L + steps}"
        )


def verify_sharpness_counterexamples() -> None:
    print("[4] Verifying Sharpness / Boundary Counterexamples (Exact Falsification Witnesses):")

    # C1: a == 1 (mod 4) never resonates
    d1 = pow(5, 4) - clpow(5, 4)
    assert d1 == 368 and v2(d1) == 4
    print(f"    C1 (a=5 == 1 mod 4, k=4): 5^4 - clpow(5,4) = {d1}, v2 = {v2(d1)} (Regime I, no resonance)")

    # C2: a == 3 (mod 4) off the curve s = 2^e - e (e.g. a=7 has s=3)
    d2_2 = pow(7, 2) - clpow(7, 2)
    d2_4 = pow(7, 4) - clpow(7, 4)
    d2_8 = pow(7, 8) - clpow(7, 8)
    assert (v2(d2_2), v2(d2_4), v2(d2_8)) == (2, 4, 6)
    print(
        f"    C2 (a=7, s=3 off curve): v2 at k=2,4,8 = ({v2(d2_2)}, {v2(d2_4)}, {v2(d2_8)}) "
        f"= min(2^e, 3+e), zero resonance"
    )

    # C3: Sharpness of B < 2^(2^e) for root invariance (a=3, e=2, threshold 2^4 = 16)
    nu_1 = hensel_lift(lambda n: F_bridge(3, 2, 1, n), 5, 5)
    nu_15 = hensel_lift(lambda n: F_bridge(3, 2, 15, n), 5, 5)
    nu_17 = hensel_lift(lambda n: F_bridge(3, 2, 17, n), 5, 5)
    assert nu_1 == 22 and nu_15 == 22 and nu_17 == 9
    assert (nu_1 & 1) == 0 and (nu_17 & 1) == 1
    print(
        f"    C3 (a=3, e=2, threshold B < 16): nu(B=1)={nu_1}, nu(B=15)={nu_15} [invariant], "
        f"nu(B=17)={nu_17} [bit-4 flips parity!]"
    )

    # C4: Falsification of naive parity-invariance v2(a^(2m+1)-clpow) == v2(a^(2m)-clpow) at a=19=16+3
    v_even = v2(pow(19, 4) - clpow(19, 4))
    v_odd = v2(pow(19, 5) - clpow(19, 5))
    assert v_even == 8 and v_odd == 5 and v_even != v_odd
    print(
        f"    C4 (a=19=16+3, k=4 vs 5): v2(19^4-clpow)={v_even} != {v_odd}=v2(19^5-clpow) "
        f"[bit_4(19)=1 shifts odd-exponent root!]"
    )

    # C5: Sharpness of shift c in {0, 1} for a^(2^e*m + c) - clpow(a, 2^e*m + c)
    d5 = pow(3, 6) - clpow(3, 6)
    assert d5 == 644 and v2(d5) == 2
    print(f"    C5 (a=3, e=2, c=2, k=6): 3^6 - clpow(3,6) = {d5}, v2 = {v2(d5)} < 5 (base divisibility breaks)")

    # C6: Sharpness of B odd (even B=2 shifts isometry scale from L=5 to L=6)
    d6_0 = F_bridge(3, 2, 2, 0)
    d6_1 = F_bridge(3, 2, 2, 1)
    assert v2(d6_1 - d6_0) == 6 != 5
    print(
        f"    C6 (a=3, e=2, B=2 even): v2(F(1)-F(0)) = {v2(d6_1 - d6_0)} != 5 "
        f"(scale-5 isometry breaks for even B)"
    )


def main() -> None:
    verify_four_regime_law()
    verify_hensel_isometry_and_root_shift()
    synthesize_deep_roots()
    verify_sharpness_counterexamples()
    print("\nALL EXACT SILICON CHECKS PASSED (ZERO FLOATS, ZERO ERRORS).")


if __name__ == "__main__":
    main()
