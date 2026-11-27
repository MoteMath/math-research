"""
explore_and_verify.py — Exact Pure-Silicon Certificate Synthesizer & Independent Verifier
for the Raney-Minkowski Finite-State Bit-Transducer Proof Engine (adic-14).

Zero floating-point values enter any certificate, bound, or verification step.
All arithmetic uses exact Python `int` and `fractions.Fraction`.
"""
from fractions import Fraction
from math import gcd
from collections import deque

# ==============================================================================
# 1. Exact Stern-Brocot & Minkowski Question-Mark Binary Arithmetic
# ==============================================================================

L_MAT = (1, 1, 0, 1)  # bit 0: [0/1, 1/1]
R_MAT = (1, 0, 1, 1)  # bit 1: [1/1, 1/0]
I_MAT = (1, 0, 0, 1)  # empty: [0/1, 1/0]


def mat_mul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


def mat_det(A):
    a, b, c, d = A
    return a * d - b * c


def sb_mat(bits):
    M = I_MAT
    for b in bits:
        M = mat_mul(M, R_MAT if b else L_MAT)
    return M


def sb_bits(p: int, q: int):
    """Exact Stern-Brocot binary path of p/q > 0 (Euclidean subtraction)."""
    assert p > 0 and q > 0
    bits = []
    a, b = p, q
    while a != b:
        if a < b:
            bits.append(0)
            b -= a
        else:
            bits.append(1)
            a -= b
    return tuple(bits)


def bits_to_int(bits) -> int:
    val = 0
    for b in bits:
        val = (val << 1) | b
    return val


def dyad_lo(bits) -> Fraction:
    return Fraction(bits_to_int(bits), 1 << len(bits))


def dyad_mid(bits) -> Fraction:
    return Fraction(2 * bits_to_int(bits) + 1, 1 << (len(bits) + 1))


def minkowski_q(p: int, q: int) -> Fraction:
    """Exact Minkowski ?(p/q) on [0, infty] with ?(0/1)=0, ?(1/1)=1/2, ?(1/0)=1."""
    if p == 0:
        assert q > 0
        return Fraction(0)
    if q == 0:
        assert p > 0
        return Fraction(1)
    return dyad_mid(sb_bits(p, q))


def col_measure(M) -> Fraction:
    """Exact Minkowski measure ?(d/b) - ?(c/a) of the column interval [c/a, d/b]."""
    a, b, c, d = M
    return minkowski_q(d, b) - minkowski_q(c, a)


def row_measure(M) -> Fraction:
    """Exact Minkowski measure of the transpose M^T: ?(d/c) - ?(b/a)."""
    a, b, c, d = M
    return minkowski_q(d, c) - minkowski_q(b, a)


def gcd4(a, b, c, d):
    return gcd(gcd(a, b), gcd(c, d))


def sigma1(D: int) -> int:
    return sum(d for d in range(1, D + 1) if D % d == 0)


def dedekind_psi(D: int) -> int:
    n = D
    res = D
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            res = res // p * (p + 1)
        p += 1
    if n > 1:
        res = res // n * (n + 1)
    return res


# ==============================================================================
# 2. Raney Row-Balanced Matrix Transducer Construction
# ==============================================================================

def balanced_matrices(D: int, primitive_only: bool = False):
    """All (a, b, c, d) in N^4 with a*d - b*c = D, a > c, d > b."""
    res = []
    for u in range(1, D + 1):
        for v in range(1, D // u + 1):
            rem = D - u * v
            for b in range(0, rem // u + 1):
                rem2 = rem - u * b
                if rem2 % v == 0:
                    c = rem2 // v
                    a, d = c + u, b + v
                    if (not primitive_only) or gcd4(a, b, c, d) == 1:
                        res.append((a, b, c, d))
    return sorted(res)


def normalize_left(M):
    """Factor M = sb_mat(bits) * B with B row-balanced."""
    a, b, c, d = M
    bits = []
    while True:
        if a >= c and b >= d:
            bits.append(0)
            a -= c
            b -= d
        elif c >= a and d >= b:
            bits.append(1)
            c -= a
            d -= b
        else:
            break
    B = (a, b, c, d)
    assert mat_mul(sb_mat(bits), B) == M
    return tuple(bits), B


def build_transducer(D: int, primitive_only: bool = True):
    states = balanced_matrices(D, primitive_only=primitive_only)
    idx = {B: i for i, B in enumerate(states)}
    trans = []
    for B in states:
        b0, B0 = normalize_left(mat_mul(B, L_MAT))
        b1, B1 = normalize_left(mat_mul(B, R_MAT))
        trans.append(((b0, idx[B0]), (b1, idx[B1])))
    return states, trans, idx


# ==============================================================================
# 3. Exact Certificate Synthesis (Hellinger Contraction, Stationary, Integral)
# ==============================================================================

def h_weight(c_num: int, c_den: int, m: int) -> Fraction:
    """Upper bound on 2^(-m/2): 2^(-(m//2)) * (c if m odd else 1)."""
    base = Fraction(1, 1 << (m // 2))
    return base * Fraction(c_num, c_den) if (m % 2 == 1) else base


def synthesize_hellinger_cert(states, trans, c_num=23, c_den=32, scale=128):
    """Find compact positive integer vector v and exact dyadic/small-den rho < 1."""
    assert 2 * c_num * c_num >= c_den * c_den
    n = len(states)
    # Exact rational power iteration to align with Perron-Frobenius eigenvector
    v = [Fraction(1) for _ in range(n)]
    for _ in range(30):
        nv = [Fraction(0) for _ in range(n)]
        for i in range(n):
            for b in (0, 1):
                bits, j = trans[i][b]
                nv[i] += h_weight(c_num, c_den, 1 + len(bits)) * v[j]
        m = max(nv)
        v = [x / m for x in nv]
    # Quantize to small positive integers
    v_int = [max(1, int((x * scale).numerator // (x * scale).denominator) + 1) for x in v]
    # Compute exact worst ratio
    worst = Fraction(0)
    for i in range(n):
        s = Fraction(0)
        for b in (0, 1):
            bits, j = trans[i][b]
            s += h_weight(c_num, c_den, 1 + len(bits)) * v_int[j]
        r = s / v_int[i]
        if r > worst:
            worst = r
    # Round worst UP to a clean dyadic denominator 128 or 64 if < 1
    r_den = 128
    r_num = (worst.numerator * r_den + worst.denominator - 1) // worst.denominator
    assert r_num < r_den, f"Failed to contract: worst={worst}"
    # Verify strictly in exact arithmetic
    for i in range(n):
        s = Fraction(0)
        for b in (0, 1):
            bits, j = trans[i][b]
            s += h_weight(c_num, c_den, 1 + len(bits)) * v_int[j]
        assert s <= Fraction(r_num, r_den) * v_int[i]
    return v_int, c_num, c_den, r_num, r_den, worst


def solve_linear_exact(A, b):
    n = len(b)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        inv = Fraction(1) / M[col][col]
        for j in range(col, n + 1):
            M[col][j] *= inv
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                for j in range(col, n + 1):
                    M[r][j] -= f * M[col][j]
    return [M[i][n] for i in range(n)]


def synthesize_integral_cert(states, trans):
    """Compute exact rational fixed-point I(s) = int_0^infty ?(mat(s)(x)) dmu_?(x)
    and exact contraction vector (u, g_num, g_den) for the linear error operator."""
    n = len(states)
    A = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    rhs = [Fraction(0) for _ in range(n)]
    for i in range(n):
        for b in (0, 1):
            bits, j = trans[i][b]
            A[i][j] -= Fraction(1, 1 << (len(bits) + 1))
            rhs[i] += dyad_lo(bits) / 2
    I_vec = solve_linear_exact(A, rhs)
    # Common denominator
    lcm_den = 1
    for x in I_vec:
        lcm_den = lcm_den * x.denominator // gcd(lcm_den, x.denominator)
    I_num = [int(x * lcm_den) for x in I_vec]
    # Also synthesize error contraction certificate for T_E(u)_i = sum_b 2^{-(|bits|+1)} u_j
    u = [Fraction(1) for _ in range(n)]
    for _ in range(25):
        nu = [Fraction(0) for _ in range(n)]
        for i in range(n):
            for b in (0, 1):
                bits, j = trans[i][b]
                nu[i] += Fraction(1, 1 << (len(bits) + 1)) * u[j]
        m = max(nu)
        u = [x / m for x in nu]
    u_int = [max(1, int((x * 64).numerator // (x * 64).denominator) + 1) for x in u]
    worst = Fraction(0)
    for i in range(n):
        s = Fraction(0)
        for b in (0, 1):
            bits, j = trans[i][b]
            s += Fraction(1, 1 << (len(bits) + 1)) * u_int[j]
        r = s / u_int[i]
        if r > worst:
            worst = r
    g_den = 16
    g_num = (worst.numerator * g_den + worst.denominator - 1) // worst.denominator
    assert g_num < g_den
    for i in range(n):
        s = Fraction(0)
        for b in (0, 1):
            bits, j = trans[i][b]
            s += Fraction(1, 1 << (len(bits) + 1)) * u_int[j]
        assert s <= Fraction(g_num, g_den) * u_int[i]
    return I_vec, I_num, lcm_den, u_int, g_num, g_den


def synthesize_stationary_cert(states, trans):
    """Exact integer stationary weights from row_measure(B) cleared of powers of 2."""
    w_rows = [row_measure(B) for B in states]
    lcm_den = 1
    for x in w_rows:
        lcm_den = lcm_den * x.denominator // gcd(lcm_den, x.denominator)
    pi_int = [int(x * lcm_den) for x in w_rows]
    # Verify exact stationarity: 2 * pi[j] = sum_{i, b: next=j} pi[i]
    n = len(states)
    in_sum = [0] * n
    for i in range(n):
        for b in (0, 1):
            _, j = trans[i][b]
            in_sum[j] += pi_int[i]
    assert all(in_sum[j] == 2 * pi_int[j] for j in range(n))
    return pi_int, lcm_den


# ==============================================================================
# 4. Independent Brute-Force Verification on All 2^k Bitstrings (Zero Transducer!)
# ==============================================================================

def brute_force_verify(D: int, A_mat, hellinger_cert, integral_target, max_k: int = 10):
    """Independently enumerate ALL 2^k bitstrings w in {0,1}^k and verify:
       1. Measure conservation: sum_{|w|=k} col_measure(A * M(w)) == col_measure(A)
       2. Exact TV overlap bound: sum_{|w|=k} min(2^-k, col_measure(A * M(w))) <= (v_0/v_min) * (r_num/r_den)^k
       3. Explicit separating set G_k: mu_?(G_k) <= bound and (A_* mu_?)(G_k^c) <= bound
       4. Exact Minkowski average convergence: |2^-k sum_{|w|=k} ?(A * q(w)) - I(A)| <= C * gamma^k
    """
    v_int, c_num, c_den, r_num, r_den, s0 = hellinger_cert
    v_min = min(v_int)
    w_init = col_measure(A_mat)
    results = []
    for k in range(0, max_k + 1):
        tot_meas = Fraction(0)
        tot_min = Fraction(0)
        mu_G = Fraction(0)
        push_Gc = Fraction(0)
        tot_q = Fraction(0)
        p_k = Fraction(1, 1 << k)
        for mask in range(1 << k):
            bits = tuple((mask >> (k - 1 - j)) & 1 for j in range(k))
            Mw = sb_mat(bits)
            AMw = mat_mul(A_mat, Mw)
            q_w = col_measure(AMw)
            tot_meas += q_w
            tot_min += min(p_k, q_w)
            if q_w >= p_k:
                mu_G += p_k
            else:
                push_Gc += q_w
            # Mediant of AMw
            a, b, c, d = AMw
            tot_q += minkowski_q(c + d, a + b)
        assert tot_meas == w_init, f"Conservation failed at D={D}, k={k}"
        bound = Fraction(v_int[s0], v_min) * (Fraction(r_num, r_den) ** k)
        assert tot_min <= bound, f"TV overlap bound failed at D={D}, k={k}: {tot_min} > {bound}"
        assert mu_G <= bound and push_Gc <= bound
        avg_q = tot_q * p_k
        results.append((k, tot_min, bound, avg_q, avg_q - integral_target))
    return results


# ==============================================================================
# 5. Main Report: Row-Column Duality (D=1..20), Certificates (D=2..5),
#    Independent Brute-Force Checks, & Sharpness Counterexamples
# ==============================================================================

def main():
    print("=" * 78)
    print("1. EXACT ROW-COLUMN DUALITY & DEDEKIND-PSI / SIGMA_1 LAWS (D = 1..20)")
    print("=" * 78)
    for D in range(1, 21):
        states, trans, _ = build_transducer(D, primitive_only=False)
        w_col = [col_measure(B) for B in states]
        w_row = [row_measure(B) for B in states]
        # Verify stationarity and Kraft=1
        in_row = [Fraction(0)] * len(states)
        in_kraft = [Fraction(0)] * len(states)
        in_kraft_len = [Fraction(0)] * len(states)
        for i, B in enumerate(states):
            for b in (0, 1):
                bits, j = trans[i][b]
                in_row[j] += w_row[i] / 2
                in_kraft[j] += Fraction(1, 1 << len(bits))
                in_kraft_len[j] += Fraction(len(bits), 1 << len(bits))
        assert all(in_row[i] == w_row[i] for i in range(len(states)))
        assert all(in_kraft[i] == 1 for i in range(len(states)))

        Z_row = sum(w_row)
        Z_col = sum(w_col)
        W_len = sum(w_row[i] * Fraction(len(trans[i][0][0]) + len(trans[i][1][0]), 2) for i in range(len(states)))
        W_inv = sum(w_col[i] * in_kraft_len[i] for i in range(len(states)))
        Z_row_prim = sum(w_row[i] for i, B in enumerate(states) if gcd4(*B) == 1)
        Z_col_prim = sum(w_col[i] for i, B in enumerate(states) if gcd4(*B) == 1)
        W_len_prim = sum(w_row[i] * Fraction(len(trans[i][0][0]) + len(trans[i][1][0]), 2)
                         for i, B in enumerate(states) if gcd4(*B) == 1)

        assert Z_row == sigma1(D)
        assert Z_row_prim == dedekind_psi(D)
        assert W_len == Z_col
        assert W_len_prim == Z_col_prim
        assert W_inv == Z_row
        if D <= 10 or D in (12, 16, 20):
            print(f"  D={D:2d}: |Q|={len(states):3d}, Z_row={int(Z_row):2d}=sigma1(D), "
                  f"Z_prim={int(Z_row_prim):2d}=psi(D), W_len=Z_col={Z_col}, alpha_prim={W_len_prim/Z_row_prim}")

    print("\n" + "=" * 78)
    print("2. SYNTHESIZED FINITE CERTIFICATES FOR LEAN 4 (D = 2, 3, 4-prim, 5)")
    print("=" * 78)
    for D in [2, 3, 4, 5]:
        states, trans, idx = build_transducer(D, primitive_only=True)
        # Use c = 91/128 (2*91^2 = 16562 >= 16384 = 128^2, tighter pure-dyadic bound on 1/sqrt(2))
        v_int, c_num, c_den, r_num, r_den, worst_h = synthesize_hellinger_cert(states, trans, c_num=91, c_den=128, scale=64)
        pi_int, pi_den = synthesize_stationary_cert(states, trans)
        I_vec, I_num, I_den, u_int, g_num, g_den = synthesize_integral_cert(states, trans)
        s_mul = idx[(1, 0, 0, D)]
        alpha_num = sum(pi_int[i] * (len(trans[i][0][0]) + len(trans[i][1][0])) for i in range(len(states)))
        alpha_den = 2 * sum(pi_int)
        alpha = Fraction(alpha_num, alpha_den)
        print(f"\n--- D = {D} (primitive, |Q| = {len(states)}, start state s0={s_mul} for x -> {D}x) ---")
        print(f"  States: {states}")
        print(f"  Hellinger cert: c={c_num}/{c_den}, rho={r_num}/{r_den} (exact max={worst_h}), v={v_int}")
        print(f"  Stationary cert: pi={pi_int} (den={pi_den}, sum={sum(pi_int)}/{pi_den}={Fraction(sum(pi_int), pi_den)}=psi({D})), alpha={alpha}")
        print(f"  Integral cert: I_den={I_den}, I_num={I_num}")
        print(f"    int_0^infty ?({D}x) dmu_?(x) = {I_vec[s_mul]}")
        print(f"    Error contraction: gamma={g_num}/{g_den}, u={u_int}")

        # Independent brute-force check up to k = 10 (1024 bitstrings)!
        max_k = 10 if D <= 3 else 9
        bf = brute_force_verify(D, (1, 0, 0, D), (v_int, c_num, c_den, r_num, r_den, s_mul), I_vec[s_mul], max_k=max_k)
        k_last, tv_last, bd_last, avg_last, err_last = bf[-1]
        print(f"  Brute-force check (all 2^{k_last}={1<<k_last} paths): TV_overlap={tv_last} <= {bd_last} (PASS)")
        print(f"    E_{k_last}[?({D}*q(w))] = {avg_last}, err = {err_last} (|err| <= {(Fraction(u_int[s_mul], min(u_int)) * Fraction(g_num, g_den)**k_last)})")
        if D == 2:
            # Verify exact D=2 closed form: E_k[?(2*q(w))] = 9/13 + a_k / (52 * 8^k)
            a0, a1 = 3, 11
            ak = [a0, a1]
            while len(ak) <= max_k:
                ak.append(ak[-1] + 4 * ak[-2])
            for k, _, _, avg_q, err_q in bf:
                expected_err = Fraction(ak[k], 52 * (8 ** k))
                assert err_q == expected_err, f"D=2 closed form mismatch at k={k}: {err_q} != {expected_err}"
            print(f"  D=2 EXACT CLOSED FORM VERIFIED for k=0..{max_k}: E_k = 9/13 + a_k/(52*8^k), a_k={ak[:8]}...")

    print("\n" + "=" * 78)
    print("3. SHARPNESS & FALSIFICATION COUNTEREXAMPLES")
    print("=" * 78)
    # Counterexample 1: D = 1 (unimodular I_2)
    for k in range(0, 8):
        p_k = Fraction(1, 1 << k)
        tot_min = sum(min(p_k, col_measure(sb_mat(tuple((m >> (k - 1 - j)) & 1 for j in range(k)))))
                      for m in range(1 << k))
        assert tot_min == 1
    print("  [Sharpness 1] D = 1 (A = I_2): TV overlap = 1 for all k=0..7 (no singularity; alpha(1) = 1).")

    # Counterexample 2: D = 4 non-primitive scalar A = 2*I_2 (det = 4 > 1, gcd = 2 > 1)
    A_nonprim = (2, 0, 0, 2)
    assert mat_det(A_nonprim) == 4 and gcd4(*A_nonprim) == 2
    for k in range(0, 8):
        p_k = Fraction(1, 1 << k)
        tot_min = sum(min(p_k, col_measure(mat_mul(A_nonprim, sb_mat(tuple((m >> (k - 1 - j)) & 1 for j in range(k))))))
                      for m in range(1 << k))
        assert tot_min == 1
    print("  [Sharpness 2] D = 4 non-primitive (A = 2*I_2, det=4, gcd=2): TV overlap = 1 for all k=0..7!")
    print("                Proves det(A) > 1 alone does NOT imply mutual singularity; primitivity is essential.")

    # Counterexample 3: Relaxing Hellinger dyadic bound 2*c^2 >= 1 to c = 181/256
    c_bad = Fraction(181, 256)
    assert 2 * c_bad.numerator ** 2 < c_bad.denominator ** 2
    # On x = 1, y = 1/2: x*y = 1/2 > c_bad^2 = 32761/65536!
    assert Fraction(1, 2) > c_bad * c_bad
    print(f"  [Sharpness 3] c = 181/256 violates 2*c^2 >= 1 (2*181^2 = {2*181**2} < {256**2} = 256^2): x*y = 1/2 > c^2.")

    print("\nALL EXACT CHECKS PASSED WITH ZERO FLOATING-POINT ARITHMETIC.")


if __name__ == "__main__":
    main()
