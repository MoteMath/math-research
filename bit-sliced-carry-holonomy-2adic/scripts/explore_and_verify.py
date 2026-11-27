"""Exact pure-silicon integer exploration, holonomy-tower certificate synthesis,
independent replay verification, and boundary counterexample search for the
Bit-Sliced Carry-Holonomy 2-Adic Lifting Engine (`adic-17`).

Strictly CPU-only, pure Python exact `int` / `bool` arithmetic (ZERO floating point).
"""


def v2(n: int) -> int:
    """Exact 2-adic valuation of a positive integer (returns 0 for n == 0)."""
    if n == 0:
        return 0
    return (n & -n).bit_length() - 1


def test_bit(x: int, k: int) -> bool:
    return ((x >> k) & 1) == 1


def iter_map(f, n: int, x0: int = 0) -> int:
    x = x0
    for _ in range(n):
        x = f(x)
    return x


def iter_map_mod(f, n: int, mod: int, x0: int = 0) -> int:
    x = x0 % mod
    for _ in range(n):
        x = f(x) % mod
    return x


def holonomy(f, k: int, x0: int, L: int) -> bool:
    """Exact bit-k cycle holonomy: XOR_{i=0}^{L-1} testBit(f(iter f i x0 % 2^k), k)."""
    mod = 1 << k
    acc = False
    x = x0 % mod
    for _ in range(L):
        acc ^= test_bit(f(x), k)
        x = f(x) % mod
    return acc


def minimal_period_mod(f, k: int, x0: int = 0) -> tuple[int, int]:
    """Return (preperiod, minimal_period) of orbit of x0 modulo 2^k."""
    mod = 1 << k
    seen: dict[int, int] = {}
    x = x0 % mod
    t = 0
    while x not in seen:
        seen[x] = t
        x = f(x) % mod
        t += 1
    pre = seen[x]
    return pre, t - pre


# ---------------------------------------------------------------------------
# Recurrence families
# ---------------------------------------------------------------------------

def gray_carry_step(s: int, c: int):
    return lambda x: (x ^ (x << s)) + c


def quad_and_step(s: int, t: int, c: int):
    return lambda x: (x ^ ((x << s) & (x << t))) + c


def affine_xor_step(A: int, c: int):
    return lambda x: A * x + (x ^ c)


def carryless_gray_step(c: int):
    return lambda x: (x ^ (x << 1)) ^ c


# ---------------------------------------------------------------------------
# Verification suites
# ---------------------------------------------------------------------------

def verify_theorem_1_gray_carry() -> None:
    print("=== [1] Theorem 1: Gray-Carry Phase-Transition Dichotomy ===")
    print("    a_0 = 0, a_{n+1} = (a_n ^ (2^s * a_n)) + c")
    # 1A: Regime I (s >= 2): v2(a_n) = v2(c) + v2(n) for ALL c >= 1, n >= 1
    checked_1a = 0
    for s in range(2, 7):
        for c in range(1, 65):
            e = v2(c)
            mod = 1 << 24
            f = gray_carry_step(s, c)
            x = 0
            for n in range(1, 513):
                x = f(x) % mod
                assert x != 0
                got = v2(x)
                exp = e + v2(n)
                assert got == exp, f"1A mismatch: s={s}, c={c}, n={n}, got={got}, exp={exp}"
                checked_1a += 1
            if c % 2 == 1 and c <= 15 and s <= 4:
                for k in range(1, 10):
                    pre, per = minimal_period_mod(f, k)
                    assert pre == 0 and per == (1 << k), f"1A period mismatch: s={s}, c={c}, k={k}"
                    assert holonomy(f, k, 0, 1 << k) is True
    print(f"    [PASS] Regime I (s >= 2): {checked_1a} exact valuation checks + periods & holonomies mod 2^1..2^9")

    # 1B: Regime II (s = 1): v2(a_n) = v2(c) (odd n) or v2(n) + v2(c) + v2(c/2^v2(c) + 1) (even n)
    checked_1b = 0
    for c in range(1, 129):
        e = v2(c)
        c_odd = c >> e
        r = v2(c_odd + 1)
        mod = 1 << 28
        f = gray_carry_step(1, c)
        x = 0
        for n in range(1, 513):
            x = f(x) % mod
            assert x != 0
            got = v2(x)
            exp = e if (n % 2 == 1) else (v2(n) + e + r)
            assert got == exp, f"1B mismatch: c={c}, n={n}, got={got}, exp={exp}"
            checked_1b += 1
        if c % 2 == 1 and c <= 31:
            # Verify exact coset holonomy tower from k0 = r + 1
            for m in range(0, 7):
                k = r + 1 + m
                L = 2 << m
                pre, per = minimal_period_mod(f, k)
                assert pre == 0 and per == L, f"1B period mismatch: c={c}, k={k}, got={(pre, per)}"
                assert holonomy(f, k, 0, L) is True
    # Exact unbounded integer spot checks (no modulo truncation!)
    assert v2(iter_map(gray_carry_step(2, 6), 12, 0)) == 3
    assert v2(iter_map(gray_carry_step(1, 7), 8, 0)) == 6
    print(f"    [PASS] Regime II (s = 1): {checked_1b} exact valuation checks + coset-tower periods & holonomies")


def verify_theorem_2_quad_and() -> None:
    print("=== [2] Theorem 2: Nonlinear Quadratic Bitwise-AND Carry Ergodicity ===")
    print("    b_0 = 0, b_{n+1} = (b_n ^ ((2^s * b_n) & (2^t * b_n))) + c  (1 <= s < t, t >= 3)")
    checked_2 = 0
    for s in range(1, 6):
        for t in range(max(s + 1, 3), 8):
            for c in range(1, 33):
                e = v2(c)
                mod = 1 << 24
                f = quad_and_step(s, t, c)
                x = 0
                for n in range(1, 257):
                    x = f(x) % mod
                    assert x != 0
                    got = v2(x)
                    exp = e + v2(n)
                    assert got == exp, f"Thm2 mismatch: s={s}, t={t}, c={c}, n={n}, got={got}, exp={exp}"
                    checked_2 += 1
                if c % 2 == 1 and c <= 7 and t <= 5:
                    for k in range(1, 9):
                        pre, per = minimal_period_mod(f, k)
                        assert pre == 0 and per == (1 << k)
                        assert holonomy(f, k, 0, 1 << k) is True
    # Unbounded integer spot check matching Proof.lean witness
    assert v2(iter_map(quad_and_step(1, 3, 5), 16, 0)) == 4
    print(f"    [PASS] Theorem 2 (t >= 3): {checked_2} exact valuation checks + ergodic periods & holonomies")


def verify_theorem_3_affine_xor() -> None:
    print("=== [3] Theorem 3: Complete Classification of Affine-XOR Recurrences ===")
    print("    d_0 = 0, d_{n+1} = A * d_n + (d_n ^ c)  (even A >= 2, c >= 1)")
    checked_3 = 0
    for A in range(2, 66, 2):
        vA = v2(A)
        for c in range(1, 33):
            e = v2(c)
            mod = 1 << 28
            f = affine_xor_step(A, c)
            x = 0
            for n in range(1, 257):
                x = f(x) % mod
                assert x != 0
                got = v2(x)
                exp = e if (n % 2 == 1) else (v2(n) + e + vA - 1)
                assert got == exp, f"Thm3 mismatch: A={A}, c={c}, n={n}, got={got}, exp={exp}"
                checked_3 += 1
            if c % 2 == 1 and c <= 7 and A <= 16:
                for m in range(0, 6):
                    k = vA + m
                    L = 2 << m
                    pre, per = minimal_period_mod(f, k)
                    assert pre == 0 and per == L
                    assert holonomy(f, k, 0, L) is True
    # Unbounded integer spot check matching Proof.lean witness
    assert v2(iter_map(affine_xor_step(8, 3), 4, 0)) == 4
    print(f"    [PASS] Theorem 3 (even A >= 2): {checked_3} exact valuation checks + holonomy conservation")


def verify_sharpness_counterexamples() -> None:
    print("=== [4] Sharpness & Boundary Counterexamples ===")

    # Sharpness 1: A = 1 in Affine-XOR -> exact stabilization d_n = c for all n >= 1
    for c in [1, 3, 6, 13, 42]:
        f = affine_xor_step(1, c)
        for n in range(1, 33):
            assert iter_map(f, n, 0) == c
    print("    [SHARP] A = 1 (a_{n+1} = a_n + (a_n ^ c)): stabilizes at d_n = c for all n >= 1 (2-adic contraction)")

    # Sharpness 2: A = 0 in Affine-XOR -> exact period 2 forever
    for c in [1, 3, 6, 13]:
        f = affine_xor_step(0, c)
        for m in range(16):
            assert iter_map(f, 2 * m, 0) == 0
            assert iter_map(f, 2 * m + 1, 0) == c
            assert holonomy(f, 1, 0, 2) is False
    print("    [SHARP] A = 0 (a_{n+1} = a_n ^ c): exact period 2 forever (holonomy = False at every level)")

    # Sharpness 3: (s, t) = (1, 2) boundary in Theorem 2
    f12 = quad_and_step(1, 2, 1)
    b4 = iter_map(f12, 4, 0)
    h2 = holonomy(f12, 2, 0, 4)
    assert b4 == 8 and v2(b4) == 3 and v2(b4) != v2(1) + v2(4) and h2 is False
    # Also report c = 3, 5, 7
    b4_c3 = iter_map(quad_and_step(1, 2, 3), 4, 0)
    assert b4_c3 == 32 and v2(b4_c3) == 5
    print(f"    [SHARP] (s, t) = (1, 2) boundary: c=1 gives b_4={b4} (v2={v2(b4)} != 2, holonomy(k=2)={h2}); c=3 gives b_4={b4_c3} (v2={v2(b4_c3)})")

    # Sharpness 4: Carryless Gray (x ^ 2x) ^ c (no arithmetic carry)
    fc = carryless_gray_step(1)
    a4 = iter_map(fc, 4, 0)
    hc2 = holonomy(fc, 2, 0, 4)
    per_k3 = minimal_period_mod(fc, 3)
    per_k6 = minimal_period_mod(fc, 6)
    assert a4 == 8 and a4 % 8 == 0 and v2(a4) == 3 and hc2 is False
    assert per_k3 == (0, 4) and per_k6 == (0, 8)
    print(f"    [SHARP] Carryless Gray (x ^ 2x) ^ 1: a_4={a4} (v2={v2(a4)} != 2), holonomy(k=2)={hc2}, periods mod 8,64 = {per_k3[1]}, {per_k6[1]}")

    # Sharpness 5: Odd A >= 3 in Affine-XOR -> non-bijective contraction (fixed point mod 2^k)
    for A in [3, 5, 7]:
        f = affine_xor_step(A, 1)
        pers = [minimal_period_mod(f, k) for k in range(1, 7)]
        assert all(per == 1 for _, per in pers)
    print("    [SHARP] Odd A in {3, 5, 7}: period = 1 mod 2^k for all k=1..6 (2-adic contraction, not TPerm)")


def main() -> None:
    verify_theorem_1_gray_carry()
    verify_theorem_2_quad_and()
    verify_theorem_3_affine_xor()
    verify_sharpness_counterexamples()
    print("\nALL EXACT INTEGER CHECKS PASSED (0 errors, 0 floats).")


if __name__ == "__main__":
    main()
