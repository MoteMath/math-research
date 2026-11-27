#!/usr/bin/env python3
"""
explore_and_verify.py — Pure-Silicon Carry-Propagation Depth & Run-Length Automaton Transfer Engine
Worker: transducer-3 (Thread 1)

Exact integer / rational arithmetic ONLY (zero floating-point values anywhere).
Performs:
  1. Exact transfer-matrix synthesis for general 3-parameter ripple-carry depth <= L
     and 4-parameter carry-bit run-length <= L automata (arbitrary L >= 1, radix B >= 2).
  2. Exact certificate verification:
     - Hyperplane intertwining certificate: iota(M_run^{(2m)}(L) * v) = m * rotR(iota(v))
     - Universal 3-parameter ripple matrix annihilator: M^(L+1) - (k+p+g)M^L + g*p^L*I = 0
     - Universal 4-parameter carry-run matrix annihilator: M^(L+2) - (a+r)M^(L+1) + (ar-bc)M^L + b*c*r^L*I = 0
     - Exact rational generating function Cauchy-product identities.
  3. Independent brute-force verification against actual integer addition (x + y) over all
     pairs (x, y) in [0, B^w)^2 for B in {2, 4, 6}, multiple L, and absorption weights t.
  4. Explicit sharpness & falsification counterexamples demonstrating exact boundaries:
     - Metric/parity swap (carryRun + input parity; rippleDepth + output parity)
     - Odd radix B = 3 (breaks both collapses)
     - Non-unit absorption weight t = -1 (breaks bounded periodicity; yields alternating Fibonacci at L=1)
     - Zero-absorption (t = 0) odd-vs-even L finite-support dichotomy.
"""

from fractions import Fraction


def popcount(n: int) -> int:
    return bin(n).count("1")


def digit_sum(n: int, B: int, w: int) -> int:
    s = 0
    for _ in range(w):
        s += n % B
        n //= B
    return s


def parity_sign(n: int) -> int:
    return 1 if (n % 2 == 0) else -1


def analyze_addition(x: int, y: int, B: int, w: int):
    """Exact bit/digit-by-digit ripple addition in base B for w digits.
    Returns (max_ripple_depth, max_carry_run, absorptions, carry_out, low_digit_sum).
    """
    c = 0
    cur_rip = 0
    max_rip = 0
    cur_run = 0
    max_run = 0
    absorptions = 0
    low_sum_digits = 0
    for _ in range(w):
        xi = x % B
        yi = y % B
        x //= B
        y //= B
        tot = xi + yi + c
        si = tot % B
        c_next = tot // B
        low_sum_digits += si
        if c == 1 and c_next == 0:
            absorptions += 1
        if c_next == 1:
            cur_run += 1
            if xi + yi >= B:  # Generate: starts fresh dependency chain of depth 1
                cur_rip = 1
            else:             # Propagate: extends incoming dependency chain
                cur_rip += 1
        else:
            cur_run = 0
            cur_rip = 0
        if cur_run > max_run:
            max_run = cur_run
        if cur_rip > max_rip:
            max_rip = cur_rip
        c = c_next
    return max_rip, max_run, absorptions, c, low_sum_digits


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mat_pow(A, e: int):
    n = len(A)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    base = [row[:] for row in A]
    while e > 0:
        if e & 1:
            R = mat_mul(R, base)
        base = mat_mul(base, base)
        e >>= 1
    return R


def mat_vec(A, v):
    return [sum(row[j] * v[j] for j in range(len(v))) for row in A]


def build_ripple_matrix(L: int, k: int, p: int, g: int):
    """Exact (L+1)x(L+1) integer transfer matrix for ripple-carry depth <= L."""
    n = L + 1
    M = [[0] * n for _ in range(n)]
    M[0][0] = k + p
    M[1][0] = g
    for d in range(1, L + 1):
        M[0][d] = k
        M[1][d] = g
        if d < L:
            M[d + 1][d] = p
    return M


def build_carryrun_matrix(L: int, a: int, b: int, c: int, r: int):
    """Exact (L+1)x(L+1) integer transfer matrix for carry-bit run length <= L."""
    n = L + 1
    M = [[0] * n for _ in range(n)]
    M[0][0] = a
    M[1][0] = b
    for d in range(1, L + 1):
        M[0][d] = c
        if d < L:
            M[d + 1][d] = r
    return M


def check_intertwining_certificate():
    """Verify exact hyperplane intertwining iota(M_run^{(2m)}(L) v) = m * rotR(iota(v))
    on all basis vectors for L = 1..8 and m = 1..5."""
    print("[1] Checking Hyperplane Intertwining Certificate iota(M_run * v) = m * rotR(iota(v))")
    checked = 0
    for L in range(1, 9):
        for m in range(1, 6):
            M = build_carryrun_matrix(L, -m, m, -m, m)
            n = L + 1
            for e_idx in range(n):
                v = [1 if i == e_idx else 0 for i in range(n)]
                Mv = mat_vec(M, v)
                lhs = Mv + [-sum(Mv)]
                iv = v + [-sum(v)]
                rot_iv = [iv[-1]] + iv[:-1]
                rhs = [m * x for x in rot_iv]
                assert lhs == rhs, f"Intertwining failed at L={L}, m={m}, e={e_idx}"
                checked += 1
            # Also verify M^(L+2) = m^(L+2) * I
            P = mat_pow(M, L + 2)
            target = m ** (L + 2)
            for i in range(n):
                for j in range(n):
                    assert P[i][j] == (target if i == j else 0)
    print(f"    PASS: {checked} basis intertwining checks + 40 matrix power identities M^(L+2) = m^(L+2)*I verified.")


def check_matrix_annihilators():
    """Verify universal 3-parameter ripple and 4-parameter carry-run exact matrix annihilators."""
    print("[2] Checking Universal Parametric Matrix Annihilators (Ripple 3-param & Carry-Run 4-param)")
    rip_cases = [(1, 2, 1), (1, -2, 1), (1, 2, -1), (2, -4, 2), (3, -5, 2), (-2, 3, 5)]
    run_cases = [(-1, 1, -1, 1), (-1, 1, 0, 1), (-1, 1, 1, 1), (-1, 1, -2, 1), (3, 1, 1, 3), (2, -3, 5, -1)]
    for L in range(1, 7):
        n = L + 1
        for (k, p, g) in rip_cases:
            M = build_ripple_matrix(L, k, p, g)
            ML = mat_pow(M, L)
            ML1 = mat_mul(M, ML)
            T = k + p + g
            gpL = g * (p ** L)
            for i in range(n):
                for j in range(n):
                    val = ML1[i][j] - T * ML[i][j] + (gpL if i == j else 0)
                    assert val == 0, f"Ripple annihilator failed at L={L}, {(k, p, g)}"
        for (a, b, c, r) in run_cases:
            M = build_carryrun_matrix(L, a, b, c, r)
            ML = mat_pow(M, L)
            ML1 = mat_mul(M, ML)
            ML2 = mat_mul(M, ML1)
            bcrL = b * c * (r ** L)
            for i in range(n):
                for j in range(n):
                    val = ML2[i][j] - (a + r) * ML1[i][j] + (a * r - b * c) * ML[i][j] + (bcrL if i == j else 0)
                    assert val == 0, f"Carry-run annihilator failed at L={L}, {(a, b, c, r)}"
    print(f"    PASS: All {6 * len(rip_cases)} ripple & {6 * len(run_cases)} carry-run matrix annihilators exact 0.")


def check_brute_force_theorems():
    """Independently verify Theorems 1, 2, and 3 by brute-force enumeration over [0, B^w)^2."""
    print("[3] Independent Brute-Force Verification on Exact Integer Addition [0, B^w)^2")

    # 3A: Binary (B=2), w=0..7, L=1..5 — Theorems 1B, 1C, 2B, 2C
    for L in range(1, 6):
        plain_rip = []
        for w in range(0, 8):
            s_run_low = 0
            s_run_full = 0
            s_rip_in = 0
            cnt_rip = 0
            mask = (1 << w) - 1
            for x in range(1 << w):
                for y in range(1 << w):
                    mr, mc, ab, cout, low_d = analyze_addition(x, y, 2, w)
                    # Cross-check concrete addition bit-sum against (x+y) & mask and x+y!
                    assert low_d == popcount((x + y) & mask)
                    assert low_d + cout == popcount(x + y)
                    if mc <= L:
                        s_run_low += parity_sign(popcount((x + y) & mask))
                        s_run_full += parity_sign(popcount(x + y))
                    if mr <= L:
                        s_rip_in += parity_sign(popcount(x) + popcount(y))
                        cnt_rip += 1
            plain_rip.append(cnt_rip)
            # Theorem 1B prediction:
            rem = w % (L + 2)
            pred_run_low = 1 if rem == 0 else (-1 if rem == L + 1 else 0)
            assert s_run_low == pred_run_low, f"Thm 1B mismatch L={L}, w={w}: {s_run_low} vs {pred_run_low}"
            # Theorem 1C prediction (for w >= 1):
            if w >= 1:
                pred_run_full = -2 if rem == 1 else (1 if (rem == 0 or rem == L + 1) else 0)
                assert s_run_full == pred_run_full, f"Thm 1C mismatch L={L}, w={w}: {s_run_full} vs {pred_run_full}"
            # Theorem 2B prediction:
            if w % (L + 1) == 0:
                q = w // (L + 1)
                pred_rip_in = (((-1) ** (L + 1)) * (2 ** L)) ** q
            else:
                pred_rip_in = 0
            assert s_rip_in == pred_rip_in, f"Thm 2B mismatch L={L}, w={w}: {s_rip_in} vs {pred_rip_in}"
        # Theorem 2C recurrence: R(w+L+1) = 4 R(w+L) - 2^L R(w)
        for w in range(0, len(plain_rip) - L - 1):
            assert plain_rip[w + L + 1] == 4 * plain_rip[w + L] - (2 ** L) * plain_rip[w]
    print("    PASS: Binary Theorems 1B, 1C, 2B, 2C verified across L=1..5, w=0..7 (exact popcount cross-check).")

    # 3B: Even radices B=4 (m=2, w=0..4) and B=6 (m=3, w=0..3) — Theorems 1A, 2B
    for B, max_w in [(4, 4), (6, 3)]:
        m = B // 2
        for L in range(1, 4):
            for w in range(0, max_w + 1):
                s_run = 0
                s_rip = 0
                for x in range(B ** w):
                    for y in range(B ** w):
                        mr, mc, ab, cout, low_d = analyze_addition(x, y, B, w)
                        assert low_d == digit_sum((x + y) % (B ** w), B, w)
                        if mc <= L:
                            s_run += parity_sign(low_d)
                        if mr <= L:
                            s_rip += parity_sign(digit_sum(x, B, w) + digit_sum(y, B, w))
                rem = w % (L + 2)
                pred_run = (m ** w) if rem == 0 else (-(m ** w) if rem == L + 1 else 0)
                assert s_run == pred_run, f"Thm 1A mismatch B={B}, L={L}, w={w}"
                if w % (L + 1) == 0:
                    q = w // (L + 1)
                    pred_rip = (((-1) ** (L + 1)) * (2 ** L) * (m ** (L + 1))) ** q
                else:
                    pred_rip = 0
                assert s_rip == pred_rip, f"Thm 2B(even B) mismatch B={B}, L={L}, w={w}"
    print("    PASS: Even-radix Theorems 1A & 2B verified for B=4 (w=0..4) and B=6 (w=0..3), L=1..3.")

    # 3C: Theorem 3 (Absorption-weighted binary carry-run) & Theorem 3B (t=0 odd/even dichotomy)
    for t in [0, 1, -1, 2, 3]:
        for L in range(1, 5):
            vals = []
            for w in range(0, 8):
                tot = 0
                mask = (1 << w) - 1
                for x in range(1 << w):
                    for y in range(1 << w):
                        mr, mc, ab, cout, low_d = analyze_addition(x, y, 2, w)
                        if mc <= L:
                            wt = (1 if ab == 0 else 0) if t == 0 else (t ** ab)
                            if wt != 0:
                                tot += parity_sign(popcount((x + y) & mask)) * wt
                vals.append(tot)
            # Recurrence A(w+L+2) = (1-t)*A(w+L) + t*A(w)
            for w in range(0, len(vals) - L - 2):
                assert vals[w + L + 2] == (1 - t) * vals[w + L] + t * vals[w]
            if t == 0:
                for w in range(L + 1, len(vals)):
                    expected = 0 if (L % 2 == 1) else parity_sign(w)
                    assert vals[w] == expected, f"Thm 3B mismatch L={L}, w={w}: {vals[w]} vs {expected}"
    print("    PASS: Absorption-weighted Theorem 3 (t in {0,1,-1,2,3}) & t=0 odd/even dichotomy verified.")


def check_large_width_transfer():
    """Verify exact transfer engine at large widths (e.g. w=100, L=7) via matrix exponentiation."""
    print("[4] Large-Width Exact Transfer Replay (w = 0..100, L = 7)")
    L = 7
    M_run = build_carryrun_matrix(L, -1, 1, -1, 1)
    M_rip = build_ripple_matrix(L, 1, -2, 1)
    v0 = [1] + [0] * L
    v_run = list(v0)
    v_rip = list(v0)
    for w in range(0, 101):
        s_run = sum(v_run)
        s_rip = sum(v_rip)
        rem = w % (L + 2)
        pred_run = 1 if rem == 0 else (-1 if rem == L + 1 else 0)
        assert s_run == pred_run
        pred_rip = (((-1) ** (L + 1)) * (2 ** L)) ** (w // (L + 1)) if (w % (L + 1) == 0) else 0
        assert s_rip == pred_rip
        v_run = mat_vec(M_run, v_run)
        v_rip = mat_vec(M_rip, v_rip)
    print(f"    PASS: w=0..100, L=7 exact match! At w=96: run_sum={1 if 96%9==0 else (-1 if 96%9==8 else 0)}, "
          f"rip_sum=((-1)^8 * 128)^12 = {128**12} (out of 4^96 pairs).")


def check_sharpness_counterexamples():
    """Exhibit exact counterexamples proving sharpness of every hypothesis."""
    print("[5] Sharpness & Falsification Counterexamples")

    # S1: Swap metric/parity -> Carry-run <= 1 with INPUT parity (-1)^(s2(x)+s2(y))
    s1 = []
    for w in range(1, 7):
        tot = 0
        for x in range(1 << w):
            for y in range(1 << w):
                _, mc, _, _, _ = analyze_addition(x, y, 2, w)
                if mc <= 1:
                    tot += parity_sign(popcount(x) + popcount(y))
        s1.append(tot)
    assert s1 == [0, 1, -1, 2, -3, 5]  # alternating Fibonacci!
    print(f"    S1 (CarryRun<=1 + InputParity, w=1..6):  {s1}  [Fibonacci growth; breaks BOTH collapses!]")

    # S2: Swap metric/parity -> Ripple-depth <= 1 with OUTPUT parity (-1)^s2((x+y) mod 2^w)
    s2 = []
    for w in range(1, 7):
        tot = 0
        mask = (1 << w) - 1
        for x in range(1 << w):
            for y in range(1 << w):
                mr, _, _, _, _ = analyze_addition(x, y, 2, w)
                if mr <= 1:
                    tot += parity_sign(popcount((x + y) & mask))
        s2.append(tot)
    assert s2 == [0, -2, 4, -4, 0, 8]
    print(f"    S2 (RippleDepth<=1 + OutParity, w=1..6): {s2}  [|lambda|=sqrt(2) growth; breaks boundedness!]")

    # S3: Odd radix B = 3 (L = 1, w = 1..4)
    s3_rip, s3_run = [], []
    for w in range(1, 5):
        sr, sc = 0, 0
        for x in range(3 ** w):
            for y in range(3 ** w):
                mr, mc, _, _, low_d = analyze_addition(x, y, 3, w)
                if mr <= 1:
                    sr += parity_sign(digit_sum(x, 3, w) + digit_sum(y, 3, w))
                if mc <= 1:
                    sc += parity_sign(low_d)
        s3_rip.append(sr)
        s3_run.append(sc)
    assert s3_rip == [1, 4, 7, 19] and s3_run == [3, 7, 17, 41]
    print(f"    S3 (Odd radix B=3, L=1, w=1..4):         rip={s3_rip}, run={s3_run}  [breaks BOTH collapses!]")

    # S4: Non-unit absorption weight t = -1 (L = 1, w = 0..7)
    s4 = []
    for w in range(0, 8):
        tot = 0
        mask = (1 << w) - 1
        for x in range(1 << w):
            for y in range(1 << w):
                _, mc, ab, _, _ = analyze_addition(x, y, 2, w)
                if mc <= 1:
                    tot += parity_sign(popcount((x + y) & mask)) * ((-1) ** ab)
        s4.append(tot)
    assert s4 == [1, 0, 1, -1, 2, -3, 5, -8]
    print(f"    S4 (CarryRun<=1 + OutParity * (-1)^abs): {s4}  [Fibonacci growth; breaks period-3 bound!]")

    # S5: Zero-absorption (t = 0) odd L=1 vs even L=2 (w = 0..6)
    def zero_abs_seq(L):
        out = []
        for w in range(0, 7):
            tot = 0
            mask = (1 << w) - 1
            for x in range(1 << w):
                for y in range(1 << w):
                    _, mc, ab, _, _ = analyze_addition(x, y, 2, w)
                    if mc <= L and ab == 0:
                        tot += parity_sign(popcount((x + y) & mask))
            out.append(tot)
        return out
    s5_odd = zero_abs_seq(1)
    s5_even = zero_abs_seq(2)
    assert s5_odd == [1, 0, 0, 0, 0, 0, 0]
    assert s5_even == [1, 0, 1, -1, 1, -1, 1]
    print(f"    S5 (Zero-absorption t=0, w=0..6):        L=1 (odd)={s5_odd} vs L=2 (even)={s5_even}")


def main():
    print("=" * 78)
    print("PURE-SILICON CARRY-DEPTH & RUN-LENGTH AUTOMATON TRANSFER VERIFICATION")
    print("=" * 78)
    check_intertwining_certificate()
    check_matrix_annihilators()
    check_brute_force_theorems()
    check_large_width_transfer()
    check_sharpness_counterexamples()
    print("=" * 78)
    print("ALL EXACT INTEGER CHECKS PASSED (ZERO FLOATS, ZERO DISCREPANCIES).")
    print("=" * 78)


if __name__ == "__main__":
    main()
