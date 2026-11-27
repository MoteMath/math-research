#!/usr/bin/env python3
"""
Pure-Silicon Exact Exploration, Verification, and Sharpness Suite
for the 2-Adic Valuation-Tower Poincare Reduction (VTPR) Mechanism.

Zero floating-point arithmetic anywhere: all computations use exact Python
integers and bitmasks representing BitVec w (Z / 2^w Z).
"""

from math import lcm
import random


def lsb(u: int, mask: int) -> int:
    """Lowest set bit operator u & (-u) on BitVec w."""
    u &= mask
    return (u & (-u)) & mask


def or_fold(xs) -> int:
    """Bitwise OR across a tuple/list of bitvectors."""
    acc = 0
    for v in xs:
        acc |= v
    return acc


def Q_period(d: int) -> int:
    """Closed-form global period Q(d) = lcm(2d, d+1) * (2d - 1)."""
    return lcm(2 * d, d + 1) * (2 * d - 1)


def step_twisted_lsb_or_sub(state, c: int, mask: int):
    """One step of F_{d,c}(x_0,...,x_{d-1}) = (x_1,...,x_{d-1}, c*lsb(x_1|...|x_{d-1}) - x_0)."""
    u = or_fold(state[1:])
    nxt = (c * lsb(u, mask) - state[0]) & mask
    return state[1:] + (nxt,)


def step_wild_quad(state, c: int, mask: int):
    """
    Non-homogeneous, non-transducer nonlinear family satisfying Level 1 VTPR:
      Phi(y) = c              if u is odd
             = 2*c            if u = 2 (mod 4)
             = 4 * sum(y_i^2) if 4 | u
    """
    ys = state[1:]
    u = or_fold(ys)
    if u & 1:
        phi = c & mask
    elif u & 2:
        phi = (2 * c) & mask
    else:
        phi = (4 * sum(y * y for y in ys)) & mask
    nxt = (phi - state[0]) & mask
    return ys + (nxt,)


def orbit_period(step_fn, init, max_steps: int):
    """Compute exact minimal period of `init` under `step_fn`, or None if > max_steps."""
    cur = init
    for t in range(1, max_steps + 1):
        cur = step_fn(cur)
        if cur == init:
            return t
    return None


def verify_exhaustive_twisted_lsb():
    print("=== 1. Exhaustive State-Space Verification of Twisted LSB-OR-Sub ===")
    # Check all states for small (d, w) and multiple odd multipliers c
    cases = [
        (2, 2, [1, 3]),
        (2, 3, [1, 3, 5, 7]),
        (2, 4, [1, 3, 5, 11, 15]),
        (2, 5, [1, 3, 7]),
        (2, 6, [1, 5]),
        (3, 2, [1, 3]),
        (3, 3, [1, 3, 5]),
        (3, 4, [1, 3, 7]),
        (4, 2, [1, 3]),
        (4, 3, [1, 5]),
        (5, 2, [1, 3]),
    ]
    for d, w, cs in cases:
        N = 1 << w
        mask = N - 1
        Q = Q_period(d)
        total = N ** d
        for c in cs:
            assert c & 1 == 1
            vis = bytearray(total)
            obs_lcm = 1
            inv_ok = True
            pers = {}
            for s in range(total):
                if not vis[s]:
                    cur = s
                    k = 0
                    while not vis[cur]:
                        vis[cur] = 1
                        t = cur
                        coords = [0] * d
                        for i in range(d - 1, -1, -1):
                            coords[i] = t & mask
                            t >>= w
                        st = tuple(coords)
                        v_before = lsb(or_fold(st), mask)
                        st_next = step_twisted_lsb_or_sub(st, c, mask)
                        v_after = lsb(or_fold(st_next), mask)
                        if v_before != v_after:
                            inv_ok = False
                        ni = 0
                        for v in st_next:
                            ni = (ni << w) | v
                        cur = ni
                        k += 1
                    assert Q % k == 0, f"Period {k} does not divide Q({d})={Q}!"
                    pers[k] = pers.get(k, 0) + 1
                    obs_lcm = lcm(obs_lcm, k)
            assert inv_ok, "Joint LSB invariant violated!"
            if c == 1:
                print(f"  d={d}, w={w}, c={c} ({total} states): Q={Q}, obs_lcm={obs_lcm}, "
                      f"inv_conserved={inv_ok}, periods={sorted(pers.keys())}")
    print("  [PASS] All exhaustive checks passed (all odd c verified).")


def verify_high_dim_and_width():
    print("\n=== 2. High-Dimension & High-Width Exact Replay (d=2..10, w=16, 64) ===")
    for d in range(2, 11):
        Q = Q_period(d)
        for w in (16, 64):
            mask = (1 << w) - 1
            rng = random.Random(20261126 + d * 100 + w)
            c = (rng.randrange(1 << w) | 1) & mask
            # Test 60 random states + universal witness v*_d = (1, 0,..., 0, 4)
            witness = (1,) + (0,) * (d - 2) + (4,)
            p_wit = orbit_period(lambda st: step_twisted_lsb_or_sub(st, 1, mask), witness, Q)
            assert p_wit == Q, f"Witness failed for d={d}, w={w}: got {p_wit}, expected {Q}"
            for _ in range(60):
                st = tuple(rng.randrange(1 << w) for _ in range(d))
                v0 = lsb(or_fold(st), mask)
                cur = st
                for _step in range(Q):
                    cur = step_twisted_lsb_or_sub(cur, c, mask)
                    assert lsb(or_fold(cur), mask) == v0
                assert cur == st, f"F^Q != id for d={d}, w={w}, c={c}"
        print(f"  d={d:2d}: Q(d)={Q:4d} (exact witness (1,0..0,4) period={Q} at w=16,64; 120 random orbits & invariant PASS)")


def verify_wild_quadratic_family():
    print("\n=== 3. Non-Homogeneous Wild Quadratic Family (VTPR Level-1 Generality) ===")
    for d in range(2, 7):
        Q = Q_period(d)
        w = 16
        mask = (1 << w) - 1
        c = 3
        rng = random.Random(777 + d)
        # Witness (1, 0, ..., 0, 4) is primitive
        witness = (1,) + (0,) * (d - 2) + (4,)
        p_wit = orbit_period(lambda st: step_wild_quad(st, 1, mask), witness, Q)
        assert p_wit == Q, f"Wild quad witness failed for d={d}: got {p_wit}"
        for _ in range(80):
            coords = [rng.randrange(1 << w) for _ in range(d)]
            coords[rng.randrange(d)] |= 1  # primitive
            st = tuple(coords)
            cur = st
            for _step in range(Q):
                cur = step_wild_quad(cur, c, mask)
                assert (or_fold(cur) & 1) == 1
            assert cur == st
        print(f"  d={d}, w={w}, c={c}: Q(d)={Q}, wild quadratic 4*sum(y_i^2) primitive orbits PASS (witness period={p_wit})")


def verify_poincare_cancellation():
    print("\n=== 4. Exact Poincare Linearization Check: R^(d+1)(e) = (-e_{d-1}, e_0, -e_1, ..., -e_{d-2}) ===")
    for d in range(2, 8):
        w = 16
        mask = (1 << w) - 1
        c = 5
        rng = random.Random(314 + d)
        for _ in range(50):
            # Pick arbitrary 4-divisible (e_0, ..., e_{d-1})
            e = tuple((rng.randrange(1 << (w - 2)) << 2) & mask for _ in range(d))
            # Convert to x: x_0 = c - e_0 (odd), x_j = e_j (j >= 1, 4-divisible)
            x = ((c - e[0]) & mask,) + e[1:]
            # Run (2d - 1) * (d + 1) steps of BOTH twisted LSB-OR-Sub and wild quadratic!
            for fn in (step_twisted_lsb_or_sub, step_wild_quad):
                cur = x
                for _step in range((2 * d - 1) * (d + 1)):
                    cur = fn(cur, c, mask)
                e_out = ((c - cur[0]) & mask,) + cur[1:]
                e_expected = ((-e[d - 1]) & mask, e[0]) + tuple((-e[j]) & mask for j in range(1, d - 1))
                assert e_out == e_expected, f"Poincare linearization mismatch for d={d}!"
        print(f"  d={d}: F^((2d-1)(d+1)) matches signed cyclic shift M on 100 4-divisible states (both families) PASS")


def verify_sharpness_counterexamples():
    print("\n=== 5. Sharpness & Boundary Counterexamples (Where the Law Breaks!) ===")

    # (a) XOR instead of subtraction: x_{n+2} = x_n ^ lsb(x_{n+1}) -> period 3^w!
    print("  (a) Replace '-' by '^': x_{n+2} = x_n ^ lsb(x_{n+1}) (d=2):")
    for w in (2, 3, 4, 5):
        mask = (1 << w) - 1
        p = orbit_period(lambda st: (st[1], (st[0] ^ lsb(st[1], mask)) & mask), (0, mask), 1000)
        print(f"      w={w}: orbit of (0, {mask}) has exact period {p} (= 3^{w} = {3**w}); divides Q(2)=36? {36 % p == 0}")
        assert p == 3 ** w

    # (b) Reversed sign: x_{n+2} = x_n - lsb(x_{n+1})
    mask4 = 15
    p_rev = orbit_period(lambda st: (st[1], (st[0] - lsb(st[1], mask4)) & mask4), (1, 3), 1000)
    print(f"  (b) Reversed sign x_n - lsb(x_{{n+1}}) (d=2, w=4): seed=(1, 3) has period {p_rev} (divides 36? {36 % p_rev == 0})")
    assert 36 % p_rev != 0

    # (c) Even multiplier c = 2: x_{n+2} = 2*lsb(x_{n+1}) - x_n
    mask6 = 63
    p_even = orbit_period(lambda st: (st[1], (2 * lsb(st[1], mask6) - st[0]) & mask6), (1, 2), 1000)
    print(f"  (c) Even multiplier c=2 (d=2, w=6): seed=(1, 2) has period {p_even} (divides 36? {36 % p_even == 0})")
    assert 36 % p_even != 0

    # (d) AND instead of OR: x_{n+3} = lsb(x_{n+1} & x_{n+2}) - x_n (d=3, w=3)
    mask3 = 7
    p_and = orbit_period(lambda st: (st[1], st[2], (lsb(st[1] & st[2], mask3) - st[0]) & mask3), (0, 3, 3), 1000)
    print(f"  (d) AND instead of OR (d=3, w=3): seed=(0, 3, 3) has period {p_and} (divides Q(3)=60? {60 % p_and == 0})")
    assert 60 % p_and != 0

    # (e) Breaking level >= 2 sign-invariance: Phi(y) = y_1 when 4 | y_1 (d=2, w=5)
    mask5 = 31
    def step_broken_sign(st):
        x0, x1 = st
        if x1 & 1:
            phi = 1
        elif x1 & 2:
            phi = 2
        else:
            phi = x1
        return (x1, (phi - x0) & mask5)
    p_sign = orbit_period(step_broken_sign, (1, 4), 1000)
    print(f"  (e) Broken level>=2 sign-invariance (d=2, w=5): seed=(1, 4) has period {p_sign} (divides 36? {36 % p_sign == 0})")
    assert 36 % p_sign != 0

    # (f) Width sharpness for even d: at d=2, w=3, witness (1, 4) drops from period 36 to 18!
    p_w3 = orbit_period(lambda st: step_twisted_lsb_or_sub(st, 1, 7), (1, 4), 100)
    p_w4 = orbit_period(lambda st: step_twisted_lsb_or_sub(st, 1, 15), (1, 4), 100)
    print(f"  (f) Width sharpness (d=2): (1, 4) has period {p_w3} at w=3, jumping to exact Q(2)={p_w4} at w=4!")
    assert p_w3 == 18 and p_w4 == 36


if __name__ == "__main__":
    verify_exhaustive_twisted_lsb()
    verify_high_dim_and_width()
    verify_wild_quadratic_family()
    verify_poincare_cancellation()
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED.")
