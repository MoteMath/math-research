"""
Pure-Silicon Exact Verification & Falsification Harness for the
Bit-Slice Hankel Congruence & 3-State Difference LDU Engine (specmat-8).

STRICT ZERO-FLOAT POLICY:
  All arithmetic uses exact arbitrary-precision Python `int`.
  No floating-point operations, libraries, or approximations appear anywhere.

Verifies:
  1. Universal Bit-Slice Operators A, B1, B2, C, D1, D2 against exact Bareiss det
     on arbitrary non-automatic integer sequences.
  2. Theorem 1: Closed 3-state bit-slice recurrence for ecSeq(c, alpha, beta)
     against exact Bareiss det (n <= 16) across 8 diverse parameter triples.
  3. Theorem 2: Exact mod-8 period-8 law, non-singularity, strict period-4 failure,
     mod-16 breakdown counterexamples, and even-parameter sharpness counterexamples
     across ALL 64 odd residue triples (c, alpha, beta) mod 8 up to n = 128.
  4. Theorem 3: Ruler family (c = 0) odd vanishing, even signed perfect squares,
     and odd-(alpha, beta) period-4 mod-8 law up to n = 128.
  5. Theorem 4: Signed ruler (-1)^{v_2(n+1)} exact vanishing at n = 4k+2 and
     exact 2-adic valuation v_2(det H_n) = 2 * floor(n/2) for n % 4 != 2 up to n = 128.
  6. Theorem 5: Reuse of Operators B and C on Thue-Morse (-1)^{popcount(n)},
     Gould r^{popcount(n)}, shifted paperfolding (q = -1), and lacunary 2^k-1 (q = 0).
"""

import sys


# ---------------------------------------------------------------------------
# Pure-Integer Utilities (Zero Floats)
# ---------------------------------------------------------------------------

def det_bareiss(M):
    """Exact fraction-free Bareiss integer determinant for an n x n list-of-lists."""
    n = len(M)
    if n == 0:
        return 1
    A = [[int(x) for x in row] for row in M]
    sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        pivot_row = None
        for i in range(k, n):
            if A[i][k] != 0:
                pivot_row = i
                break
        if pivot_row is None:
            return 0
        if pivot_row != k:
            A[k], A[pivot_row] = A[pivot_row], A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = A[i][j] * pivot - A[i][k] * A[k][j]
                assert num % prev_pivot == 0, "Bareiss divisibility invariant violated"
                A[i][j] = num // prev_pivot
            A[i][k] = 0
        prev_pivot = pivot
    return sign * A[n - 1][n - 1]


def det_laplace_small(M):
    """Direct recursive Laplace expansion (cross-checks Bareiss for n <= 6)."""
    n = len(M)
    if n == 0:
        return 1
    if n == 1:
        return M[0][0]
    total = 0
    for j in range(n):
        sub = [[M[i][c] for c in range(n) if c != j] for i in range(1, n)]
        term = M[0][j] * det_laplace_small(sub)
        total += term if (j % 2 == 0) else -term
    return total


def hankel_matrix(seq_fn, n):
    return [[seq_fn(i + j) for j in range(n)] for i in range(n)]


def hankel_det(seq_fn, n):
    return det_bareiss(hankel_matrix(seq_fn, n))


def q_diff(q, seq_fn):
    return lambda k: seq_fn(k + 1) - q * seq_fn(k)


def diff1(seq_fn):
    return q_diff(1, seq_fn)


def diff2(seq_fn):
    return diff1(diff1(seq_fn))


def int_pow(base, exp):
    assert exp >= 0
    res = 1
    for _ in range(exp):
        res *= base
    return res


def alt_sign(k):
    return 1 if (k % 2 == 0) else -1


def v2_nat(n):
    """Exact 2-adic valuation of positive integer n."""
    assert n > 0
    c = 0
    while (n & 1) == 0:
        n >>= 1
        c += 1
    return c


def v2_int(x):
    """Exact 2-adic valuation of nonzero integer x."""
    assert x != 0
    return v2_nat(abs(x))


def popcount(n):
    c = 0
    while n > 0:
        c += n & 1
        n >>= 1
    return c


def exact_isqrt(n):
    """Pure-integer exact square root check (returns s with s*s == n, or None)."""
    if n < 0:
        return None
    if n == 0:
        return 0
    lo, hi = 1, 1
    while hi * hi < n:
        hi <<= 1
    while lo <= hi:
        mid = (lo + hi) >> 1
        sq = mid * mid
        if sq == n:
            return mid
        if sq < n:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


# ---------------------------------------------------------------------------
# Sequence Families
# ---------------------------------------------------------------------------

def ec_seq(c, alpha, beta):
    """Binary-valuation automatic family: a(2k) = c, a(2k+1) = alpha*a(k) + beta."""
    cache = {0: c}
    def a(n):
        if n in cache:
            return cache[n]
        val = c if (n % 2 == 0) else (alpha * a(n // 2) + beta)
        cache[n] = val
        return val
    return a


def ec_3state_table(c, alpha, beta, N):
    """Exact O(N) integer 3-state recurrence (Theorem 1) for A_n, B_n, C_n up to N."""
    A = [0] * (N + 1)
    B = [0] * (N + 1)
    C = [0] * (N + 1)
    A[0] = B[0] = C[0] = 1
    for n in range(1, N + 1):
        if n % 2 == 1:
            m = n // 2
            am = int_pow(alpha, m)
            a2m = am * am
            A[n] = alt_sign(m) * c * a2m * (B[m] * B[m])
            S = alpha * am * A[m + 1] + (beta - c) * am * C[m]
            B[n] = S * am * B[m]
            C[n] = alt_sign(m + 1) * 2 * S * am * C[m]
        else:
            m = n // 2
            am1 = int_pow(alpha, m - 1)
            am = alpha * am1
            S_A = am * A[m] + beta * am1 * C[m - 1]
            A[n] = alt_sign(m) * (S_A * S_A) + alt_sign(m - 1) * (c * c) * (am1 * am1) * (C[m - 1] * C[m - 1])
            S_B = am * A[m] + (beta - c) * am1 * C[m - 1]
            B[n] = S_B * am * B[m]
            C[n] = alt_sign(m) * (am * am) * (B[m] * B[m])
    return A, B, C


def mod8_pattern(c, alpha, beta, r):
    """Exact closed-form mod-8 period-8 residue for odd (c, alpha, beta) and r = n % 8."""
    if r in (1, 5):
        return c % 8
    if r in (3, 7):
        return (-c) % 8
    if r in (2, 6):
        return 5 if ((c * alpha * beta) % 4 == 1) else 1
    if r == 4:
        return 5
    return 1


# ---------------------------------------------------------------------------
# Verification Suites
# ---------------------------------------------------------------------------

def verify_bareiss_vs_laplace():
    # Deterministic arbitrary non-automatic sequence
    seq = lambda k: ((k * k * 7 + 3 * k - 5) % 13) - 6
    for n in range(0, 7):
        M = hankel_matrix(seq, n)
        d1 = det_bareiss(M)
        d2 = det_laplace_small(M)
        assert d1 == d2, f"Bareiss != Laplace at n={n}: {d1} vs {d2}"
    print("[PASS] Bareiss vs direct Laplace cross-check (0 <= n <= 6)")


def verify_universal_operators():
    # Arbitrary non-automatic sequence d(k)
    d = lambda k: ((k * k * k * 5 - 3 * k * k + 11 * k + 2) % 17) - 8

    # Operator A: det H_{m+1}(alpha*a + beta) = alpha^{m+1} det H_{m+1}(a) + beta*alpha^m det H_m(Delta^2 a)
    for alpha, beta in [(1, 1), (-2, 3), (3, -5), (0, 7), (2, -1)]:
        a_shift = lambda k, al=alpha, be=beta: al * d(k) + be
        for m in range(0, 10):
            lhs = hankel_det(a_shift, m + 1)
            rhs = int_pow(alpha, m + 1) * hankel_det(d, m + 1) + beta * int_pow(alpha, m) * hankel_det(diff2(d), m)
            assert lhs == rhs, f"Operator A failed: alpha={alpha}, beta={beta}, m={m}"

    # Operators B1 & B2: a(2k) = c*q^k, a(2k+1) = d(k)
    for c, q in [(1, 1), (1, -1), (2, 0), (-3, 2), (0, 1)]:
        a_geom = lambda k, cc=c, qq=q: cc * int_pow(qq, k // 2) if (k % 2 == 0) else d(k // 2)
        for m in range(0, 7):
            # B1 (even size 2*(m+1))
            lhs_e = hankel_det(a_geom, 2 * (m + 1))
            h_b = hankel_det(d, m + 1)
            h_dd = hankel_det(q_diff(q, q_diff(q, d)), m)
            rhs_e = alt_sign(m + 1) * h_b * h_b + alt_sign(m) * c * c * q * h_dd * h_dd
            assert lhs_e == rhs_e, f"Operator B1 failed: c={c}, q={q}, m={m}"
            # B2 (odd size 2*m + 1)
            lhs_o = hankel_det(a_geom, 2 * m + 1)
            h_d = hankel_det(q_diff(q, d), m)
            rhs_o = alt_sign(m) * c * h_d * h_d
            assert lhs_o == rhs_o, f"Operator B2 failed: c={c}, q={q}, m={m}"

    # Operator C: u(2k) = d(k), u(2k+1) = r*d(k)
    for r in [-1, 0, 1, 2, -3]:
        u = lambda k, rr=r: d(k // 2) if (k % 2 == 0) else rr * d(k // 2)
        d_sub = lambda k, rr=r: d(k + 1) - rr * rr * d(k)
        for n in range(0, 14):
            lhs = hankel_det(u, n)
            rhs = hankel_det(d, (n + 1) // 2) * hankel_det(d_sub, n // 2)
            assert lhs == rhs, f"Operator C failed: r={r}, n={n}"

    # Operators D1 & D2: v(2k) = -2*d(k), v(2k+1) = d(k) + d(k+1)
    v = lambda k: -2 * d(k // 2) if (k % 2 == 0) else d(k // 2) + d(k // 2 + 1)
    for m in range(0, 7):
        lhs_e = hankel_det(v, 2 * m)
        h_d1 = hankel_det(diff1(d), m)
        rhs_e = alt_sign(m) * h_d1 * h_d1
        assert lhs_e == rhs_e, f"Operator D1 failed: m={m}"

        lhs_o = hankel_det(v, 2 * m + 1)
        rhs_o = alt_sign(m + 1) * 2 * hankel_det(d, m + 1) * hankel_det(diff2(d), m)
        assert lhs_o == rhs_o, f"Operator D2 failed: m={m}"

    print("[PASS] Universal Silicon Bit-Slice Operators A, B1, B2, C, D1, D2 verified on arbitrary non-automatic sequence")


def verify_theorem1_closed_system():
    triples = [
        (1, -1, 1),   # Period-doubling
        (1, 1, 1),    # Shifted ruler 1 + v_2(n+1)
        (0, 1, 1),    # Ruler v_2(n+1)
        (1, -1, 0),   # Signed ruler (-1)^{v_2(n+1)}
        (1, 2, 0),    # Exponential ruler 2^{v_2(n+1)}
        (3, 5, 7),    # Generic positive odd triple
        (-3, 7, -5),  # Generic mixed-sign odd triple
        (2, 3, 1),    # Even c triple
    ]
    N_direct = 14
    for c, alpha, beta in triples:
        a = ec_seq(c, alpha, beta)
        A, B, C = ec_3state_table(c, alpha, beta, N_direct)
        for n in range(0, N_direct + 1):
            assert A[n] == hankel_det(a, n), f"T1 A mismatch at {(c, alpha, beta)}, n={n}"
            assert B[n] == hankel_det(diff1(a), n), f"T1 B mismatch at {(c, alpha, beta)}, n={n}"
            assert C[n] == hankel_det(diff2(a), n), f"T1 C mismatch at {(c, alpha, beta)}, n={n}"
    print(f"[PASS] Theorem 1 (Closed 3-State Bit-Slice Automaton) verified vs Bareiss up to n={N_direct} across {len(triples)} parameter triples")


def verify_theorem2_mod8_and_sharpness():
    N = 128
    odd_residues = [1, 3, 5, 7]
    count = 0
    for c in odd_residues:
        for alpha in odd_residues:
            for beta in odd_residues:
                A, B, C = ec_3state_table(c, alpha, beta, N)
                for n in range(1, N + 1):
                    assert A[n] != 0, f"Singular matrix at {(c, alpha, beta)}, n={n}"
                    assert A[n] % 2 == 1
                    assert B[n] % 2 == 1
                    if n % 2 == 0:
                        assert C[n] % 2 == 1
                    elif n % 4 == 1:
                        assert C[n] % 4 == 2
                    else:
                        assert C[n] % 4 == 0
                    exp_r = mod8_pattern(c, alpha, beta, n % 8)
                    assert A[n] % 8 == exp_r, f"Mod-8 mismatch at {(c, alpha, beta)}, n={n}: got {A[n]%8}, exp {exp_r}"
                # Strict failure of period 4 mod 8
                assert A[4] % 8 == 5 and A[8] % 8 == 1 and (A[4] % 8 != A[8] % 8)
                count += 1

    # Sharpness counterexample 1: Mod-16 periodicity breakdown
    A_pd, _, _ = ec_3state_table(1, -1, 1, 16)
    assert A_pd[7] == -1 and A_pd[15] == -9 and (A_pd[7] % 16 != A_pd[15] % 16)
    assert hankel_det(ec_seq(1, -1, 1), 7) == -1
    assert hankel_det(ec_seq(1, -1, 1), 15) == -9

    A_sr, _, _ = ec_3state_table(1, 1, 1, 16)
    assert A_sr[1] == 1 and A_sr[9] == 9 and (A_sr[1] % 16 != A_sr[9] % 16)
    assert hankel_det(ec_seq(1, 1, 1), 1) == 1
    assert hankel_det(ec_seq(1, 1, 1), 9) == 9

    # Sharpness counterexample 2: Dropping oddness of c, alpha, or beta breaks non-singularity
    assert hankel_det(ec_seq(0, 1, 1), 1) == 0    # even c
    assert hankel_det(ec_seq(1, 0, 1), 2) == 0    # even alpha
    assert hankel_det(ec_seq(1, -1, 2), 2) == 0   # even beta

    print(f"[PASS] Theorem 2 (Mod-8 Period-8 & Non-Singularity) verified across all {count} odd triples mod 8 up to n={N}")
    print("       + Strict period-4 failure (A_4 = 5 != 1 = A_8 mod 8) verified for all 64 triples")
    print("       + Mod-16 breakdown verified: pd(7)=-1 != -9=pd(15) (mod 16); sr(1)=1 != 9=sr(9) (mod 16)")
    print("       + Parameter-oddness sharpness verified: (0,1,1)->H_1=0, (1,0,1)->H_2=0, (1,-1,2)->H_2=0")


def verify_theorem3_ruler_family():
    N = 128
    for alpha, beta in [(1, 1), (1, -1), (3, 5), (2, 1), (1, 2), (-3, 7)]:
        A, _, _ = ec_3state_table(0, alpha, beta, N)
        for n in range(1, N + 1):
            if n % 2 == 1:
                assert A[n] == 0, f"Ruler odd nonzero at {(alpha, beta)}, n={n}"
            else:
                m = n // 2
                signed_val = alt_sign(m) * A[n]
                root = exact_isqrt(signed_val)
                assert root is not None, f"Ruler even not signed square at {(alpha, beta)}, n={n}"
                if (alpha % 2 == 1) and (beta % 2 == 1):
                    assert A[n] != 0
                    assert A[n] % 8 == alt_sign(m) % 8
    # Also verify ec_seq(0, 1, 1)(n) == v_2(n + 1) directly up to n = 500
    a_r = ec_seq(0, 1, 1)
    for n in range(500):
        assert a_r(n) == v2_nat(n + 1)
    print(f"[PASS] Theorem 3 (Ruler Family c=0) verified up to n={N} + exact v_2(n+1) identity up to 500")


def verify_theorem4_signed_ruler():
    N = 128
    a_sgn = ec_seq(1, -1, 0)
    a_pd = ec_seq(1, -1, 1)
    for n in range(500):
        assert a_sgn(n) == alt_sign(v2_nat(n + 1))
        assert a_sgn(n) == 2 * a_pd(n) - 1

    A_sgn, _, _ = ec_3state_table(1, -1, 0, N)
    A_pd, _, C_pd = ec_3state_table(1, -1, 1, N)
    for n in range(1, N + 1):
        # Operator A exact link: det H_n(2*pd - 1) = 2^{n-1} * (2*A_pd(n) - C_pd(n-1))
        assert A_sgn[n] == int_pow(2, n - 1) * (2 * A_pd[n] - C_pd[n - 1])
        if n % 4 == 2:
            assert A_sgn[n] == 0, f"Signed ruler failed to vanish at n={n}"
        else:
            assert A_sgn[n] != 0, f"Signed ruler unexpectedly vanished at n={n}"
            assert v2_int(A_sgn[n]) == 2 * (n // 2), f"v_2 mismatch at n={n}: got {v2_int(A_sgn[n])}, exp {2*(n//2)}"
    print(f"[PASS] Theorem 4 (Signed Ruler (-1)^v_2(n+1)) verified up to n={N}: exact zeros at 4k+2, exact v_2 = 2*floor(n/2) elsewhere")


def verify_theorem5_cross_family_reuse():
    # 5a. Thue-Morse (-1)^popcount(n) and Gould r^popcount(n) via Operator C
    for r in [-1, 2, 3]:
        u = lambda k, rr=r: int_pow(rr, popcount(k))
        u_sub = lambda k, rr=r: u(k + 1) - rr * rr * u(k)
        for n in range(0, 15):
            assert hankel_det(u, n) == hankel_det(u, (n + 1) // 2) * hankel_det(u_sub, n // 2)

    # 5b. Shifted Paperfolding (a(2k) = (-1)^k, a(2k+1) = a(k)) via Operator B (q = -1)
    pf_cache = {}
    def pf(n):
        if n in pf_cache:
            return pf_cache[n]
        val = alt_sign(n // 2) if (n % 2 == 0) else pf(n // 2)
        pf_cache[n] = val
        return val
    for m in range(0, 7):
        h_e = hankel_det(pf, 2 * (m + 1))
        rhs_e = (alt_sign(m + 1) * hankel_det(pf, m + 1) ** 2
                 - alt_sign(m) * hankel_det(q_diff(-1, q_diff(-1, pf)), m) ** 2)
        assert h_e == rhs_e, f"Paperfolding even decimation failed at m={m}"
        h_o = hankel_det(pf, 2 * m + 1)
        rhs_o = alt_sign(m) * hankel_det(q_diff(-1, pf), m) ** 2
        assert h_o == rhs_o, f"Paperfolding odd decimation failed at m={m}"

    # 5c. Weighted Sparse Lacunary (2^k - 1) sequence: a(0)=c, a(2k)=0 for k>=1, a(2k+1)=b(k) via Operator B (q = 0)
    b_arb = lambda k: (k * 3 + 1) if (k % 2 == 0) else -(k + 2)
    c_val = 5
    lac = lambda k: c_val if k == 0 else (0 if k % 2 == 0 else b_arb(k // 2))
    for m in range(0, 7):
        assert hankel_det(lac, 2 * (m + 1)) == alt_sign(m + 1) * (hankel_det(b_arb, m + 1) ** 2)
        assert hankel_det(lac, 2 * m + 1) == alt_sign(m) * c_val * (hankel_det(lambda k: b_arb(k + 1), m) ** 2)

    print("[PASS] Theorem 5 (Cross-Family Reuse: Thue-Morse, Gould, Paperfolding q=-1, Lacunary q=0) verified vs Bareiss")


def main():
    print("=== Pure-Silicon Bit-Slice Hankel LDU Engine Exact Verification ===")
    verify_bareiss_vs_laplace()
    verify_universal_operators()
    verify_theorem1_closed_system()
    verify_theorem2_mod8_and_sharpness()
    verify_theorem3_ruler_family()
    verify_theorem4_signed_ruler()
    verify_theorem5_cross_family_reuse()
    print("=== ALL EXACT PURE-SILICON CHECKS PASSED (0 FLOATS, 0 FAILURES) ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
