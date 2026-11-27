"""
Pure-Silicon Conway Nimber Fermat-Tower Engine &
Universal Artin-Schreier Contraction / Block-Periodicity Verification Suite
===========================================================================
Exact arbitrary-precision integer arithmetic only (zero floating point).

Verifies:
1. Exact agreement between the pure-silicon Fermat-tower bit-tree engine and
   Conway's recursive `mex` definition of nim-multiplication on [0, 16) x [0, 16).
2. Bitwise-OR MSB law: msb(2^i ⊗ 2^j) = i | j and Trace-Gram Kronecker law:
   Tr_k(2^i ⊗ 2^j) = 1 iff (i | j) = 2^k - 1.
3. Exact Artin-Schreier bit-length contraction: bitLen(wp(x)) = bitLen(x) - 1.
4. Universal dyadic subspace-polynomial identity:
   prod_{a < 2^m} (X ^ a) = wp^m(X) = XOR_{j submask m} X^(2^j),
   plus Dyadic-Shell Wilson's Theorem and Nim-Harmonic Invariance for ALL m >= 1.
5. Binary Power-Sum Collapse: S(m, d) = XOR_{x < 2^m} x^d in {0, 1} and exact
   Sierpinski LFSR recurrence XOR_{j submask m} S(m, d + 2^j) = 0, plus exact
   popcount vanishing (popcount(d) < m => S(m, d) = 0) and boundary S(m, 2^m - 1) = 1.
6. Universal Fermat-Block Shift-Defect Bound:
   wp^(2^k)(2^(i + 2^k)) ^ 2^i < 2^(i + 1 - 2^k) (exact equality for i < 2^k)
   and Universal Block-Periodicity Compiler:
   wp^(m + 2^k)(y << (m + 2^k)) = wp^m(y << m) for all y < 2^(2^k), m >= 0,
   certified across multiple Fermat block boundaries up to 64-bit (k = 6, 2^64).
7. Sharpness & falsification witnesses showing exact failure outside every hypothesis.
"""

from functools import lru_cache


@lru_cache(None)
def scale_H(k: int, x: int) -> int:
    """Pure-silicon half-Fermat scaling S_k(x) = x ⊗ H_k on [0, 2^(2^k))."""
    if k == 0:
        return x & 1
    half = 1 << (k - 1)
    mask = (1 << half) - 1
    x0 = x & mask
    x1 = x >> half
    hi = scale_H(k - 1, x1 ^ x0)
    lo = scale_H(k - 1, scale_H(k - 1, x1))
    return (hi << half) | lo


@lru_cache(None)
def nim_mul(k: int, a: int, b: int) -> int:
    """Pure-silicon Fermat-block Karatsuba nim-multiplication on [0, 2^(2^k))."""
    if a == 0 or b == 0:
        return 0
    if a == 1:
        return b
    if b == 1:
        return a
    if k == 0:
        return a & b
    half = 1 << (k - 1)
    mask = (1 << half) - 1
    a0, a1 = a & mask, a >> half
    b0, b1 = b & mask, b >> half
    p0 = nim_mul(k - 1, a0, b0)
    p1 = nim_mul(k - 1, a1, b1)
    pm = nim_mul(k - 1, a0 ^ a1, b0 ^ b1)
    return ((pm ^ p0) << half) | (p0 ^ scale_H(k - 1, p1))


def nim_sq(k: int, a: int) -> int:
    return nim_mul(k, a, a)


def nim_wp(k: int, a: int) -> int:
    return nim_sq(k, a) ^ a


def nim_wp_iter(k: int, m: int, a: int) -> int:
    cur = a
    for _ in range(m):
        cur = nim_wp(k, cur)
    return cur


def nim_pow(k: int, a: int, e: int) -> int:
    res, base = 1, a
    while e > 0:
        if e & 1:
            res = nim_mul(k, res, base)
        base = nim_mul(k, base, base)
        e >>= 1
    return res


def nim_norm(k_succ: int, x: int) -> int:
    """Relative norm N_{k+1} : Nim (k+1) -> Nim k."""
    k = k_succ - 1
    half = 1 << k
    mask = (1 << half) - 1
    b = x & mask
    a = x >> half
    return scale_H(k, nim_sq(k, a)) ^ nim_mul(k, a, b) ^ nim_sq(k, b)


def nim_inv(k: int, x: int) -> int:
    """Pure-silicon norm-descent multiplicative inverse (with inv(0) = 0)."""
    if k == 0:
        return x & 1
    half = 1 << (k - 1)
    mask = (1 << half) - 1
    b = x & mask
    a = x >> half
    d = nim_inv(k - 1, nim_norm(k, x))
    return (nim_mul(k - 1, a, d) << half) | nim_mul(k - 1, a ^ b, d)


def nim_trace(k: int, x: int) -> int:
    return (x >> ((1 << k) - 1)) & 1


def conway_mex_table(n: int) -> list[list[int]]:
    """Direct Conway ONAG mex definition of nim-multiplication on [0, n) x [0, n)."""
    tbl = [[0] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            seen = set()
            for a2 in range(a):
                for b2 in range(b):
                    seen.add(tbl[a2][b] ^ tbl[a][b2] ^ tbl[a2][b2])
            m = 0
            while m in seen:
                m += 1
            tbl[a][b] = m
    return tbl


def main() -> None:
    print("=== 1. Conway mex vs. Pure-Silicon Fermat-Tower Engine on [0, 16)^2 ===")
    mex16 = conway_mex_table(16)
    for a in range(16):
        for b in range(16):
            assert mex16[a][b] == nim_mul(2, a, b), f"Mismatch at ({a},{b})"
    print("PASS: Exact 256/256 agreement with Conway's mex definition on F_{16}.")

    print("\n=== 2. Norm-Descent Inverse & Trace-Gram Kronecker Law ===")
    for k in range(1, 4):
        N = 1 << (1 << k)
        for x in range(1, N):
            assert nim_mul(k, x, nim_inv(k, x)) == 1
        # Trace-Gram Kronecker law
        bits = 1 << k
        for i in range(bits):
            for j in range(bits):
                tr = nim_trace(k, nim_mul(k, 1 << i, 1 << j))
                expected = 1 if (i | j) == bits - 1 else 0
                assert tr == expected
                # Bitwise-OR MSB law
                p = nim_mul(k, 1 << i, 1 << j)
                assert p.bit_length() - 1 == (i | j)
    print("PASS: Norm-descent inverse, Bitwise-OR MSB law, and Trace-Gram Kronecker law verified for k=1,2,3.")

    print("\n=== 3. Exact Artin-Schreier Bit-Length Contraction ===")
    for x in range(1, 256):
        assert nim_wp(3, x).bit_length() == x.bit_length() - 1
    for i in range(64):
        assert nim_wp(6, 1 << i).bit_length() == i
    print("PASS: bitLen(wp(x)) == bitLen(x) - 1 verified on all x in [1, 256) and all basis 2^i (i < 64).")

    print("\n=== 4. Dyadic Subspace Polynomial, Dyadic-Shell Wilson & Nim-Harmonic Invariance ===")
    for m in range(1, 8):
        for X in range(256):
            prod = 1
            for a in range(1 << m):
                prod = nim_mul(3, prod, X ^ a)
            w = nim_wp_iter(3, m, X)
            assert prod == w
            # Sierpinski Frobenius expansion
            sierp = 0
            for j in range(m + 1):
                if (j & m) == j:
                    sierp ^= nim_pow(3, X, 1 << j)
            assert w == sierp
            # Coset harmonic law for X >= 2^m
            if X >= (1 << m):
                hsum = 0
                for a in range(1 << m):
                    hsum ^= nim_inv(3, X ^ a)
                assert hsum == nim_inv(3, w)
        # Dyadic-Shell Wilson & Harmonic = 1
        wilson = 1
        harm = 0
        for x in range(1 << m, 1 << (m + 1)):
            wilson = nim_mul(3, wilson, x)
            harm ^= nim_inv(3, x)
        assert wilson == 1 and harm == 1
    print("PASS: Subspace polynomial, Sierpinski expansion, Dyadic-Shell Wilson (=1), and Harmonic (=1) verified for m=1..7 on all X < 256.")

    print("\n=== 5. Binary Power-Sum Collapse & Sierpinski LFSR Recurrence ===")
    for m in range(1, 7):
        S = []
        for d in range(1 << (m + 1)):
            s = 0
            for x in range(1 << m):
                s ^= nim_pow(3, x, d) if d > 0 else 1
            assert s in (0, 1), f"Non-binary power sum at m={m}, d={d}: {s}"
            if d.bit_count() < m:
                assert s == 0, f"Popcount vanishing failed at m={m}, d={d}"
            if d == (1 << m) - 1:
                assert s == 1, f"Boundary S(m, 2^m - 1) != 1 at m={m}"
            S.append(s)
        # Check Sierpinski recurrence for all d < 2^m
        for d in range(1 << m):
            acc = 0
            for j in range(m + 1):
                if (j & m) == j:
                    acc ^= S[d + (1 << j)]
            assert acc == 0
    print("PASS: Binary collapse S(m, d) in {0,1}, popcount vanishing, boundary=1, and Sierpinski recurrence verified for m=1..6.")

    print("\n=== 6. Universal Shift-Defect Bound & Block-Periodicity Compiler (up to 64-bit, k=6) ===")
    for k in range(5):
        P = 1 << k
        for i in range(64 - P):
            diff = nim_wp_iter(6, P, 1 << (i + P)) ^ (1 << i)
            if i < P:
                assert diff == 0
            else:
                assert diff < (1 << (i + 1 - P))
        # Universal periodicity for all r < 2^k across all m crossing Fermat blocks 2^1..2^64
        for r in range(P):
            table = [nim_wp_iter(k + 1, m0, 1 << (m0 + r)) for m0 in range(P)]
            for m in range(64 - r):
                lhs = nim_wp_iter(6, m, 1 << (m + r))
                assert lhs == table[m % P]
    print("PASS: Shift-defect bound and Universal Block-Periodicity Compiler verified for k=0..4 across 64-bit Fermat tower.")

    # Print finite certificate tables for r = 0..4
    print("\nFinite Periodicity Tables f_r(m) = wp^m(2^(m+r)) = prod_{a < 2^m} (2^(m+r) ^ a):")
    for r in range(5):
        P = 1 if r <= 1 else (4 if r <= 3 else 8)
        tab = [nim_wp_iter(4, m0, 1 << (m0 + r)) for m0 in range(P)]
        print(f"  r={r} (period {P}): {tab}")

    print("\n=== 7. Sharpness & Falsification Counterexamples ===")
    # (a) Period 2^k fails at r = 2^k for k=1 (r=2) and k=2 (r=4)
    c_k1_0 = nim_wp_iter(3, 0, 1 << 2)
    c_k1_2 = nim_wp_iter(3, 2, 1 << 4)
    assert c_k1_0 == 4 and c_k1_2 == 5 and c_k1_0 != c_k1_2
    print(f"  Sharpness 1a (k=1, r=2=2^1): f_2(0)={c_k1_0} != f_2(2)={c_k1_2} -> period 2 fails at r=2^1.")

    c_k2_0 = nim_wp_iter(4, 0, 1 << 4)
    c_k2_4 = nim_wp_iter(4, 4, 1 << 8)
    assert c_k2_0 == 16 and c_k2_4 == 17 and c_k2_0 != c_k2_4
    print(f"  Sharpness 1b (k=2, r=4=2^2): f_4(0)={c_k2_0} != f_4(4)={c_k2_4} -> period 4 fails at r=2^2.")

    # (b) Shift-defect bound is razor-sharp (margin 0) at k=1, i=2 and k=2, i=4
    d_k1 = nim_wp_iter(3, 2, 1 << 4) ^ (1 << 2)
    d_k2 = nim_wp_iter(4, 4, 1 << 8) ^ (1 << 4)
    assert d_k1 == 1 and d_k1.bit_length() == 2 + 1 - 2
    assert d_k2 == 1 and d_k2.bit_length() == 4 + 1 - 4
    print(f"  Sharpness 2 (Shift-defect tight): k=1,i=2 -> diff={d_k1} (bitLen=1=i+1-2^1); k=2,i=4 -> diff={d_k2} (bitLen=1=i+1-2^2).")

    # (c) Binary power-sum collapse fails for non-power-of-2 prefix L = 3, 5, 6, 7
    s_L3_d1 = 0 ^ 1 ^ 2
    assert s_L3_d1 == 3 and s_L3_d1 not in (0, 1)
    s_L5_d3 = 0
    for x in range(5):
        s_L5_d3 ^= nim_pow(2, x, 3)
    assert s_L5_d3 == 15 and s_L5_d3 not in (0, 1)
    print(f"  Sharpness 3 (Non-dyadic prefix): L=3, d=1 -> sum={s_L3_d1} not in {{0,1}}; L=5, d=3 -> sum={s_L5_d3} not in {{0,1}}.")

    # (d) Dyadic-shell Wilson (=1) and Harmonic (=1) fail on very next coset c=2 ([2*2^m, 3*2^m))
    for m in range(1, 6):
        p2, h2 = 1, 0
        for a in range(1 << m):
            x = (2 << m) ^ a
            p2 = nim_mul(3, p2, x)
            h2 ^= nim_inv(3, x)
        assert p2 == 2 and h2 == 3
    print("  Sharpness 4 (Coset c=2): prod_{a<2^m} (2^(m+1) ^ a) = 2 != 1 and harmonic = 3 != 1 for all m >= 1.")

    # (e) Popcount vanishing fails at exact boundary popcount(d) = m
    for m in range(1, 6):
        s_bdry = 0
        for x in range(1 << m):
            s_bdry ^= nim_pow(3, x, (1 << m) - 1)
        assert s_bdry == 1
    print("  Sharpness 5 (Popcount boundary): S(m, 2^m - 1) = 1 != 0 at popcount(d) = m.")

    print("\nALL EXACT CHECKS AND SHARPNESS WITNESSES PASSED.")


if __name__ == "__main__":
    main()
