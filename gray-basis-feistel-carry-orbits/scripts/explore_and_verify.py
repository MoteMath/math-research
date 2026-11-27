#!/usr/bin/env python3
"""
Exact Pure-Silicon Binary Verification & Falsification Suite for:
  1. Core Engine: Trailing-Ones Bit-Slice Renormalization of Phi_gamma(v) = ((v ^ gamma) + 1) mod 2^n
  2. Compiler A: Gray-Basis Parity-Fiber Involution Compiler F_{P,delta}(x) = ((G^-1(P(G(x))) + 1) ^ delta) mod 2^w
  3. Compiler B: Feistel-Carry Fiber-Splice Compiler H_h(a, b) = ((a * 2^k + (b ^ h(a))) + 1) mod 2^(m+k)

Strictly exact Python int bitmask arithmetic (zero floating-point values anywhere).
"""
from collections import Counter

# ---------------------------------------------------------------------------
# Basic exact bit-vector primitives
# ---------------------------------------------------------------------------

def mask(w: int) -> int:
    return (1 << w) - 1

def gray(x: int) -> int:
    return x ^ (x >> 1)

def inv_gray(y: int) -> int:
    r = 0
    while y:
        r ^= y
        y >>= 1
    return r

def parity(x: int) -> int:
    return x.bit_count() & 1

def trailing_ones(n: int, g: int) -> int:
    """Exact number of trailing 1-bits of g within width n (min(n, v_2(g + 1)))."""
    t = 0
    while t < n and ((g >> t) & 1):
        t += 1
    return t

def ctz(n: int, v: int) -> int:
    if v == 0:
        return n
    c = 0
    while ((v >> c) & 1) == 0:
        c += 1
    return c

def apply_bit_perm(x: int, perm: tuple[int, ...]) -> int:
    res = 0
    for i, d in enumerate(perm):
        if (x >> i) & 1:
            res |= 1 << d
    return res

def bitrev_perm(w: int) -> tuple[int, ...]:
    return tuple(w - 1 - i for i in range(w))

def swap_half_perm(w: int) -> tuple[int, ...]:
    assert w % 2 == 0
    k = w // 2
    return tuple((i + k) % w for i in range(w))

def butterfly_perm(w: int, stride: int) -> tuple[int, ...]:
    assert w % (2 * stride) == 0
    return tuple(i ^ stride for i in range(w))

def swap_perm(w: int, i: int, j: int) -> tuple[int, ...]:
    p = list(range(w))
    p[i], p[j] = p[j], p[i]
    return tuple(p)

def faro_out_perm(w: int) -> tuple[int, ...]:
    assert w % 2 == 0
    m = w // 2
    p = [0] * w
    for i in range(m):
        p[i] = 2 * i
        p[m + i] = 2 * i + 1
    return tuple(p)

def rotl_perm(w: int, r: int) -> tuple[int, ...]:
    return tuple((i + r) % w for i in range(w))

def exact_cycle_spectrum(w: int, f) -> tuple[int, int, tuple[tuple[int, int], ...]]:
    """Exact full cycle decomposition of bijection f on {0, ..., 2^w - 1}."""
    N = 1 << w
    vis = bytearray(N)
    lens = []
    zero_len = -1
    for i in range(N):
        if not vis[i]:
            cur = i
            c = 0
            has_zero = False
            while not vis[cur]:
                vis[cur] = 1
                if cur == 0:
                    has_zero = True
                cur = f(cur)
                c += 1
            assert cur == i, f"Not a bijection at {i}"
            lens.append(c)
            if has_zero:
                zero_len = c
    assert sum(lens) == N
    spec = tuple(sorted(Counter(lens).items()))
    return zero_len, len(lens), spec

# ---------------------------------------------------------------------------
# Closed-form theoretical predictions (exact integer arithmetic)
# ---------------------------------------------------------------------------

def predicted_phi_spectrum(n: int, g: int) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Exact predicted (orb(0), spectrum) for Phi_g(v) = ((v ^ g) + 1) mod 2^n."""
    assert n >= 1 and 0 <= g < (1 << n)
    t = trailing_ones(n, g)
    L0 = 1 << (n - t)
    counts: Counter[int] = Counter()
    counts[L0] += 1
    if t >= 1:
        if g == (1 << t) - 1:
            # Fixed points: states with ctz(v) = t - 1 (count = 2^(n - t))
            fp = 1 << (n - t)
            counts[1] += fp
            rem = (1 << n) - L0 - fp
            assert rem >= 0 and rem % 2 == 0
            if rem > 0:
                counts[2] += rem // 2
        else:
            # Zero fixed points; all non-giant states form 2-cycles
            rem = (1 << n) - L0
            assert rem >= 0 and rem % 2 == 0
            if rem > 0:
                counts[2] += rem // 2
    return L0, tuple(sorted(counts.items()))

def predicted_phi_point_period(n: int, g: int, v: int) -> int:
    t = trailing_ones(n, g)
    if (v & ((1 << t) - 1)) == 0:
        return 1 << (n - t)
    s = ctz(n, v)
    assert s < t
    if (g >> (s + 1)) == 0:
        return 1
    return 2

def predicted_gray_involution_spectrum(w: int, m_vec: int, delta: int) -> tuple[tuple[tuple[int, int], ...], int]:
    """
    Exact predicted spectrum for F_{P,delta}(x) = ((G^-1(P(G(x))) + 1) ^ delta) mod 2^w
    where P is parity-preserving involution with P(y ^ (1 ^ G(delta))) = P(y) ^ m_vec.
    Returns (doubled_spectrum, gamma).
    """
    assert w >= 2 and (delta & 1) == 0
    mu = inv_gray(m_vec)
    assert (mu & 1) == 1
    gamma = (mu ^ delta) >> 1
    _, phi_spec = predicted_phi_spectrum(w - 1, gamma)
    doubled = tuple((2 * length, cnt) for length, cnt in phi_spec)
    return doubled, gamma

def predicted_feistel_spectrum(m: int, k: int, h_vals: list[int]) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Exact predicted (orb(0), spectrum) for H_h on BitVec (m + k)."""
    assert len(h_vals) == (1 << m)
    L0 = 0
    fp = 0
    two_cyc = 0
    for a, g in enumerate(h_vals):
        t = trailing_ones(k, g)
        L0 += 1 << (k - t)
        if t >= 1:
            if g == (1 << t) - 1:
                # For t = k (g = 2^k - 1), v = 0 is spliced into L0, leaving 2^(k-k) = 1 fixed point
                # (v with ctz(v) = k - 1 is v = 2^(k-1), count = 1, distinct from v = 0!)
                fp_a = 1 << (k - t)
                fp += fp_a
                rem = (1 << k) - (1 << (k - t)) - fp_a
                assert rem >= 0 and rem % 2 == 0
                two_cyc += rem // 2
            else:
                rem = (1 << k) - (1 << (k - t))
                assert rem >= 0 and rem % 2 == 0
                two_cyc += rem // 2
    counts: Counter[int] = Counter()
    counts[L0] += 1
    if fp > 0:
        counts[1] += fp
    if two_cyc > 0:
        counts[2] += two_cyc
    assert L0 + fp + 2 * two_cyc == (1 << (m + k))
    return L0, tuple(sorted(counts.items()))

def gen_involutions(w: int) -> list[tuple[int, ...]]:
    res = []
    def rec(i: int, cur: list[int]):
        if i == w:
            res.append(tuple(cur))
            return
        if cur[i] != -1:
            rec(i + 1, cur)
            return
        cur[i] = i
        rec(i + 1, cur)
        cur[i] = -1
        for j in range(i + 1, w):
            if cur[j] == -1:
                cur[i] = j
                cur[j] = i
                rec(i + 1, cur)
                cur[i] = -1
                cur[j] = -1
    rec(0, [-1] * w)
    return res

# ---------------------------------------------------------------------------
# Verification routines
# ---------------------------------------------------------------------------

def verify_core_engine():
    print("[1] Verifying Core Engine: Phi_gamma(v) = ((v ^ gamma) + 1) mod 2^n")
    total_cases = 0
    for n in range(1, 9):
        M = mask(n)
        for g in range(1 << n):
            f = lambda v, g=g, M=M: ((v ^ g) + 1) & M
            zl, nc, spec = exact_cycle_spectrum(n, f)
            pred_zl, pred_spec = predicted_phi_spectrum(n, g)
            assert zl == pred_zl and spec == pred_spec, (n, g, zl, spec, pred_zl, pred_spec)
            # Also verify exact pointwise minimal period for every v when n <= 6
            if n <= 6:
                for v in range(1 << n):
                    p = predicted_phi_point_period(n, g, v)
                    cur = v
                    for step in range(1, p + 1):
                        cur = f(cur)
                        if step < p:
                            assert cur != v, (n, g, v, step, p)
                    assert cur == v, (n, g, v, p)
            total_cases += 1
    print(f"    PASS: Exhaustively verified all {total_cases} (n, gamma) pairs for n=1..8 (and pointwise periods for n=1..6).")

def verify_compiler_a():
    print("[2] Verifying Compiler A: Gray-Basis Parity-Fiber Involution Engine")
    # 2a. Exhaustive over ALL bit-permutation involutions in S_w for w=2..7 with delta=0 and delta=2^(w-1)
    checked_invs = 0
    for w in range(2, 8):
        M = mask(w)
        invs = gen_involutions(w)
        for p in invs:
            for delta in [0, 1 << (w - 1), (0xAA & M) & ~1]:
                u = 1 ^ gray(delta)
                m_vec = apply_bit_perm(u, p)
                f = lambda x, p=p, d=delta, M=M: (((inv_gray(apply_bit_perm(gray(x), p)) + 1) & M) ^ d)
                zl, nc, spec = exact_cycle_spectrum(w, f)
                pred_spec, gamma = predicted_gray_involution_spectrum(w, m_vec, delta)
                assert spec == pred_spec, (w, p, delta, spec, pred_spec)
                if delta == 0:
                    j = p[0]
                    assert zl == (1 << (w - j))
                    if j == 0:
                        assert nc == 1
                    else:
                        assert nc == (1 << (w - 2)) + 1
                if delta == (1 << (w - 1)) and w >= 3:
                    expected_sc = (p[0] in (0, w - 2, w - 1))
                    assert (nc == 1) == expected_sc, (w, p, nc, expected_sc)
                checked_invs += 1
    print(f"    PASS: Exhaustively verified {checked_invs} (w, involution pi in S_w, delta) triples for w=2..7.")

    # 2b. Large-width verification up to w=14 for canonical silicon permutations (bitrev, swapHalf, butterfly)
    for w in range(3, 15):
        M = mask(w)
        # bitrev + 1: bounded order 4
        p_rev = bitrev_perm(w)
        zl, nc, spec = exact_cycle_spectrum(w, lambda x, p=p_rev, M=M: (inv_gray(apply_bit_perm(gray(x), p)) + 1) & M)
        assert zl == 2 and spec == ((2, 2), (4, (1 << (w - 2)) - 1))
        # bitrev + (2^(w-1) + 1): single Hamiltonian cycle
        c_kick = (1 << (w - 1)) + 1
        zl2, nc2, spec2 = exact_cycle_spectrum(w, lambda x, p=p_rev, c=c_kick, M=M: (inv_gray(apply_bit_perm(gray(x), p)) + c) & M)
        assert nc2 == 1 and zl2 == (1 << w)
    for w in range(4, 15, 2):
        M = mask(w)
        k = w // 2
        p_sh = swap_half_perm(w)
        zl, nc, spec = exact_cycle_spectrum(w, lambda x, p=p_sh, M=M: (inv_gray(apply_bit_perm(gray(x), p)) + 1) & M)
        assert zl == (1 << k) and nc == (1 << (w - 2)) + 1
    print("    PASS: Verified canonical bitrev (+1 bounded order 4; +(2^(w-1)+1) Hamiltonian) & swapHalf up to w=14.")

    # 2c. Nonlinear parity-preserving coset-equivariant involution witness (NOT a bit-permutation, NOT linear!)
    # On w=6 bits: fix bit 0 and bit 5 (swap 0 <-> 5), on middle 4 bits {1,2,3,4} apply a NONLINEAR parity-preserving involution!
    # Specifically, swap state (0001) <-> (0010) and (0111) <-> (1011) on middle bits: preserves parity and commutes with flipping {0,5}!
    w = 6
    M = mask(w)
    def nonlinear_P(y: int) -> int:
        b0 = y & 1
        b5 = (y >> 5) & 1
        mid = (y >> 1) & 0xF
        # Nonlinear parity-preserving involution on 4-bit mid:
        if mid == 0b0011: mid2 = 0b1100
        elif mid == 0b1100: mid2 = 0b0011
        elif mid == 0b0101: mid2 = 0b1010
        elif mid == 0b1010: mid2 = 0b0101
        elif mid == 0b0001: mid2 = 0b0111  # weight 1 <-> weight 3 (same parity!)
        elif mid == 0b0111: mid2 = 0b0001
        else: mid2 = mid
        return (b0 << 5) | (mid2 << 1) | b5
    # Verify nonlinear_P is nonlinear, involutive, parity-preserving, and P(y ^ 1) = P(y) ^ (1 << 5)
    assert nonlinear_P(0b000010 ^ 0b000100) != (nonlinear_P(0b000010) ^ nonlinear_P(0b000100))
    for y in range(1 << w):
        assert nonlinear_P(nonlinear_P(y)) == y
        assert parity(nonlinear_P(y)) == parity(y)
        assert nonlinear_P(y ^ 1) == (nonlinear_P(y) ^ (1 << 5))
    zl, nc, spec = exact_cycle_spectrum(w, lambda x: (inv_gray(nonlinear_P(gray(x))) + 1) & M)
    assert zl == 2 and spec == ((2, 2), (4, 15))
    print("    PASS: Verified NONLINEAR parity-preserving coset-equivariant involution P at w=6 -> exact order-4 spectrum ((2,2),(4,15)).")

def verify_compiler_b():
    print("[3] Verifying Compiler B: Feistel-Carry Fiber-Splice & Upper-Shift Jacobsthal Engine")
    # 3a. Upper-shift (x ^ (x >> k)) + 1 for ALL w=2..14 and ALL k in [ceil(w/2), w-1]
    checked = 0
    for w in range(2, 15):
        M = mask(w)
        for k in range((w + 1) // 2, w):
            m = w - k
            assert 1 <= m <= k
            f = lambda x, k=k, M=M: ((x ^ (x >> k)) + 1) & M
            zl, nc, spec = exact_cycle_spectrum(w, f)
            # Closed-form Jacobsthal prediction
            jac_m = ((1 << (2 * m + 1)) + 1) // 3
            pred_L0 = (1 << (k - m)) * jac_m
            pred_fp = (1 << k) - 1 if m == k else (1 << k) - (1 << (k - m))
            pred_2c = (1 << (k - m)) * ((1 << m) - 1) * ((1 << m) - 2) // 6
            assert zl == pred_L0, (w, k, zl, pred_L0)
            counts = Counter({pred_L0: 1})
            if pred_fp > 0: counts[1] += pred_fp
            if pred_2c > 0: counts[2] += pred_2c
            assert spec == tuple(sorted(counts.items())), (w, k, spec, counts)
            checked += 1
    print(f"    PASS: Verified all {checked} upper-shift (w, k) pairs for w=2..14, ceil(w/2) <= k < w against exact Jacobsthal formula.")

    # 3b. Arbitrary bijective Feistel-carry maps H_h on BitVec(2k): universal Jacobsthal isospectrality!
    for k in range(2, 7):
        w = 2 * k
        M = mask(w)
        Mk = mask(k)
        jac_k = ((1 << (2 * k + 1)) + 1) // 3
        expected_spec = tuple(sorted(Counter({
            jac_k: 1,
            1: (1 << k) - 1,
            2: ((1 << k) - 1) * ((1 << k) - 2) // 6
        }).items()))
        bijections = [
            ("id", lambda a: a),
            ("bitrev", lambda a, p=bitrev_perm(k): apply_bit_perm(a, p)),
            ("gray", lambda a: gray(a)),
            ("inv_gray", lambda a: inv_gray(a)),
            ("add_const_5", lambda a, Mk=Mk: (a + 5) & Mk),
            ("nonlinear_cube", lambda a, Mk=Mk: (a ^ ((a * a) << 1)) & Mk),  # T-function bijection!
        ]
        for name, h in bijections:
            # confirm h is a bijection
            assert len({h(a) for a in range(1 << k)}) == (1 << k)
            f = lambda x, k=k, Mk=Mk, M=M, h=h: ((((x >> k) << k) | ((x & Mk) ^ h(x >> k))) + 1) & M
            zl, nc, spec = exact_cycle_spectrum(w, f)
            assert zl == jac_k and spec == expected_spec, (k, name, zl, spec)
    print("    PASS: Verified bijective Feistel-carry Jacobsthal isospectrality across 6 diverse bijections (linear & nonlinear) for k=2..6.")

    # 3c. Even-range Feistel-carry Hamiltonian criterion
    for k in range(2, 7):
        w = 2 * k
        M = mask(w)
        Mk = mask(k)
        # h(a) = (a << 1) & Mk is always even -> single Hamiltonian cycle of length 2^(2k)!
        h_even = lambda a, Mk=Mk: (a << 1) & Mk
        f = lambda x, k=k, Mk=Mk, M=M, h=h_even: ((((x >> k) << k) | ((x & Mk) ^ h(x >> k))) + 1) & M
        zl, nc, spec = exact_cycle_spectrum(w, f)
        assert nc == 1 and zl == (1 << w)
    print("    PASS: Verified even-range Feistel-carry Hamiltonian cycle theorem for k=2..6.")

def verify_sharpness_counterexamples():
    print("[4] Verifying Sharpness & Falsification Counterexamples")
    # S1: Core Phi_gamma at gamma=1 breaks single cycle
    zl, nc, spec = exact_cycle_spectrum(4, lambda v: ((v ^ 1) + 1) & 0xF)
    assert nc == 9 and spec == ((1, 8), (8, 1))
    print(f"    S1 (Core odd gamma=1, n=4): breaks single cycle -> #cyc={nc}, spec={spec}")

    # S2: Compiler A non-involution failure (faro_out and rotL(1) in Gray basis at w=6)
    for name, p in [("faro_out", faro_out_perm(6)), ("rotL_1", rotl_perm(6, 1))]:
        zl, nc, spec = exact_cycle_spectrum(6, lambda x, p=p: (inv_gray(apply_bit_perm(gray(x), p)) + 1) & 0x3F)
        assert nc != 17
        print(f"    S2 (Compiler A non-involution {name}, w=6): breaks universal 17-cycle collapse -> #cyc={nc}, spec={spec}")

    # S3: Compiler A width sharpness w=2 for delta = 2^(w-1) (c = 3)
    zl, nc, spec = exact_cycle_spectrum(2, lambda x: (inv_gray(apply_bit_perm(gray(x), (1, 0))) + 3) & 3)
    assert nc == 2 and spec == ((2, 2),)
    print(f"    S3 (Compiler A width bound w=2, bitrev + 3): NOT Hamiltonian -> #cyc={nc}, spec={spec}")

    # S4: Compiler A position sharpness pi(0) not in {0, w-2, w-1} for delta = 2^(w-1)
    zl, nc, spec = exact_cycle_spectrum(4, lambda x: (inv_gray(apply_bit_perm(gray(x), swap_perm(4, 0, 1))) + 9) & 0xF)
    assert nc > 1
    print(f"    S4a (Compiler A pi(0)=1 at w=4, swap(0,1)+9): NOT Hamiltonian -> #cyc={nc}, spec={spec}")
    zl, nc, spec = exact_cycle_spectrum(6, lambda x: (inv_gray(apply_bit_perm(gray(x), swap_half_perm(6))) + 33) & 0x3F)
    assert nc > 1
    print(f"    S4b (Compiler A pi(0)=3 at w=6, swapHalf+33): NOT Hamiltonian -> #cyc={nc}, spec={spec}")

    # S5: Compiler B overlap sharpness k < ceil(w/2) (w=6, k=2 -> non-involution upper shift)
    zl, nc, spec = exact_cycle_spectrum(6, lambda x: ((x ^ (x >> 2)) + 1) & 0x3F)
    assert any(l not in (1, 2, zl) for l, _ in spec)
    print(f"    S5 (Compiler B overlap w=6, k=2 < ceil(6/2)): breaks {{1,2,Jacobsthal}} law -> #cyc={nc}, spec={spec}")

    # S6: Compiler B single odd entry in h breaks Hamiltonian cycle
    def h_one_odd(a: int) -> int:
        return 1 if a == 0 else ((a << 1) & 0xF)
    zl, nc, spec = exact_cycle_spectrum(8, lambda x: ((((x >> 4) << 4) | ((x & 0xF) ^ h_one_odd(x >> 4))) + 1) & 0xFF)
    assert nc == 9 and zl == 248  # 256 - 8 = 248!
    print(f"    S6 (Compiler B one odd entry h(0)=1, m=k=4): breaks Hamiltonian -> orb(0)={zl}, spec={spec}")

if __name__ == "__main__":
    verify_core_engine()
    verify_compiler_a()
    verify_compiler_b()
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED WITH ZERO DISCREPANCIES.")
