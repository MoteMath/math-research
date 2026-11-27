"""
explore_and_verify.py
Pure-silicon exact-integer exploration, certificate synthesis, independent instance
verification, and sharpness counterexample search for the:
  Carry-Coupled Binary Automaton Correlation & Dual-Krylov L^4-Energy Proof Engine.

Strictly exact arithmetic only (Python int / fractions.Fraction; ZERO floating-point).
CPU-only.
"""

from fractions import Fraction


# =============================================================================
# 1. Pure-Silicon Binary Automaton Representation & Exact Evaluators
# =============================================================================

class BinAuto:
    """Finite-state signed/weighted LSB-first binary automaton."""
    def __init__(self, name, d, del0, del1, sig0, sig1, init):
        self.name = name
        self.d = d
        self.del0 = list(del0)
        self.del1 = list(del1)
        self.sig0 = list(sig0)
        self.sig1 = list(sig1)
        self.init = list(init)
        # Verify the decidable finite zero-invariance certificate:
        for q in range(d):
            assert self.init[q] == self.sig0[q] * self.init[self.del0[q]], (
                f"{name}: zero-invariance failed at state {q}"
            )

    def eval(self, q, n):
        val = 1
        st = q
        x = n
        while x > 0:
            if x & 1:
                val *= self.sig1[st]
                st = self.del1[st]
            else:
                val *= self.sig0[st]
                st = self.del0[st]
            x >>= 1
        return val * self.init[st]


def debruijn_auto(name, m, sig0, sig1):
    """
    Width L = m + 2 De Bruijn shift-register automaton on d = 2^(m+1) states.
    del0(q) = q >> 1, del1(q) = (1 << m) | (q >> 1).
    Requires sig0[0] == 1 so leading zeros are invariant and unique init exists.
    """
    d = 1 << (m + 1)
    assert len(sig0) == d and len(sig1) == d and sig0[0] == 1
    del0 = [q >> 1 for q in range(d)]
    del1 = [(1 << m) | (q >> 1) for q in range(d)]
    # Compute unique consistent init by topological order of q (del0(q) < q for q > 0):
    init = [1] * d
    for q in range(1, d):
        init[q] = sig0[q] * init[del0[q]]
    return BinAuto(name, d, del0, del1, sig0, sig1, init)


def bij_tail_auto(name, m, psi_bits):
    """
    Bijective-Tail Nonlinear Sliding-Window Parity Automaton for arbitrary m >= 0
    and arbitrary Boolean function psi : Fin (2^m) -> {0, 1} (len(psi_bits) = 2^m).
    phi(q) = psi(q >> 1) ^ (q & 1), sig0 = +1, sig1(q) = (-1)^phi(q).
    """
    d = 1 << (m + 1)
    assert len(psi_bits) == (1 << m)
    sig0 = [1] * d
    sig1 = [-1 if (psi_bits[q >> 1] ^ (q & 1)) else 1 for q in range(d)]
    return debruijn_auto(name, m, sig0, sig1)


def paperfolding_auto():
    # Regular paperfolding g(n) = p(n+1):
    # q0 = g(n), q1 = (-1)^n, q2 = 1
    return BinAuto(
        "Paperfolding", 3,
        del0=[1, 2, 2], del1=[0, 2, 2],
        sig0=[1, 1, 1], sig1=[1, -1, 1],
        init=[1, 1, 1],
    )


def baum_sweet_auto():
    # 2-state Baum-Sweet b(n):
    # q0 = b(n), q1 = b(2n); sig1[1] = 0 eliminates the dead state!
    return BinAuto(
        "Baum-Sweet", 2,
        del0=[1, 0], del1=[0, 0],
        sig0=[1, 1], sig1=[1, 0],
        init=[1, 1],
    )


def rudin_shapiro_auto():
    # m = 0, psi = [0]: phi(0)=0, phi(1)=1 -> sig1 = [1, -1]
    return bij_tail_auto("Rudin-Shapiro", 0, [0])


def mask6_101_xor_110_auto():
    # m = 1, psi = [0, 1]: phi = [0, 1, 1, 0] -> sig1 = [1, -1, -1, 1]
    return bij_tail_auto("L3-mask6 (101^110)", 1, [0, 1])


def mask9_100_xor_111_auto():
    # m = 1, psi = [1, 0]: phi = [1, 0, 0, 1] -> sig1 = [-1, 1, 1, -1]
    return bij_tail_auto("L3-mask9 (100^111)", 1, [1, 0])


def cubic_L4_auto():
    # m = 2, psi(b1, b2) = b1 & b2 -> psi_bits = [0, 0, 0, 1]
    # phi(q) = ((q>>1)==3) ^ (q&1) -> [0, 1, 0, 1, 0, 1, 1, 0] (mask = 0b01101010 = 106? let's check!)
    return bij_tail_auto("L4-cubic (111^1**1)", 2, [0, 0, 0, 1])


def broken_111_only_auto():
    # Sharpness counterexample: drop the tail bit b_{j-3}, keeping only pattern '111' (q in {6,7})
    sig0 = [1] * 8
    sig1 = [1, 1, 1, 1, 1, 1, -1, -1]
    return debruijn_auto("L4-broken (111 only)", 2, sig0, sig1)


# =============================================================================
# 2. Direct Bitwise Reference Definitions (Independent Check Against Automata)
# =============================================================================

def popcount(n):
    return n.bit_count()


def direct_rudin_shapiro(n):
    return -1 if (popcount(n & (n << 1)) & 1) else 1


def direct_101_xor_110(n):
    return -1 if (popcount(n & ((n << 1) ^ (n << 2))) & 1) else 1


def direct_100_xor_111(n):
    return -1 if ((popcount(n) + popcount(n & ((n << 1) ^ (n << 2)))) & 1) else 1


def direct_cubic_111_xor_1xx1(n):
    return -1 if (popcount(n & (((n << 1) & (n << 2)) ^ (n << 3))) & 1) else 1


def direct_paperfolding_p_succ(n):
    """Regular paperfolding p(n+1): strip trailing 0s of (n+1), check next bit."""
    m = n + 1
    while (m & 1) == 0:
        m >>= 1
    return -1 if ((m >> 1) & 1) else 1


def direct_baum_sweet(n):
    """b(n) = 1 iff binary representation of n has no block of 0s of odd length."""
    if n == 0:
        return 1
    x = n
    zeros = 0
    while x > 0:
        if x & 1:
            if zeros & 1:
                return 0
            zeros = 0
        else:
            zeros += 1
        x >>= 1
    return 1


# =============================================================================
# 3. Direct Aperiodic Correlation, Sparse Push/Pull QRZ & Dual-Krylov Engine
# =============================================================================

def direct_apcorr(auto, p, q, k, s):
    N = 1 << k
    if s >= N:
        return 0
    return sum(auto.eval(p, n) * auto.eval(q, n + s) for n in range(N - s))


def direct_E4(auto, q, k):
    N = 1 << k
    seq = [auto.eval(q, n) for n in range(N)]
    c0 = sum(x * x for x in seq)
    tot = c0 * c0
    for s in range(1, N):
        cs = sum(seq[n] * seq[n + s] for n in range(N - s))
        tot += 2 * cs * cs
    return tot


def sparse_maps(auto):
    """
    Build the 4 deterministic maps s0, s1, s2, s3 : Fin D -> Fin D and weights c0..c3
    corresponding to T00, T11, T01, T10 on state-pairs u = p*d + q.
    """
    d = auto.d
    D = d * d
    s_maps = [[0] * D for _ in range(4)]
    c_maps = [[0] * D for _ in range(4)]
    for p in range(d):
        for q in range(d):
            u = p * d + q
            s_maps[0][u] = auto.del0[p] * d + auto.del0[q]
            c_maps[0][u] = auto.sig0[p] * auto.sig0[q]
            s_maps[1][u] = auto.del1[p] * d + auto.del1[q]
            c_maps[1][u] = auto.sig1[p] * auto.sig1[q]
            s_maps[2][u] = auto.del0[p] * d + auto.del1[q]
            c_maps[2][u] = auto.sig0[p] * auto.sig1[q]
            s_maps[3][u] = auto.del1[p] * d + auto.del0[q]
            c_maps[3][u] = auto.sig1[p] * auto.sig0[q]
    return D, s_maps, c_maps


def primal_step(auto, state):
    D, s_maps, c_maps = sparse_maps(auto)
    Q, R, Z = state

    def pull(a, b, X, u, v):
        return c_maps[a][u] * c_maps[b][v] * X[s_maps[a][u]][s_maps[b][v]]

    Q1 = [[0] * D for _ in range(D)]
    R1 = [[0] * D for _ in range(D)]
    Z1 = [[0] * D for _ in range(D)]
    QZ = [[Q[u][v] - Z[u][v] for v in range(D)] for u in range(D)]
    RT = [[R[v][u] for v in range(D)] for u in range(D)]
    for u in range(D):
        for v in range(D):
            Q1[u][v] = (
                pull(0, 0, Q, u, v) + pull(0, 1, Q, u, v)
                + pull(1, 0, Q, u, v) + pull(1, 1, Q, u, v)
                + pull(2, 2, Q, u, v) + pull(3, 3, QZ, u, v)
                + pull(2, 3, R, u, v) + pull(3, 2, RT, u, v)
            )
            R1[u][v] = (
                pull(0, 2, Q, u, v) + pull(1, 2, Q, u, v)
                + pull(3, 0, QZ, u, v) + pull(3, 1, QZ, u, v)
                + pull(0, 3, R, u, v) + pull(1, 3, R, u, v)
                + pull(2, 0, R, u, v) + pull(2, 1, R, u, v)
            )
            Z1[u][v] = (
                pull(0, 0, Z, u, v) + pull(0, 1, Z, u, v)
                + pull(1, 0, Z, u, v) + pull(1, 1, Z, u, v)
            )
    return (Q1, R1, Z1)


def dual_step(auto, dual_state):
    """Exact sparse adjoint of primal_step (O(D^2) operations, zero matrix multiplies)."""
    D, s_maps, c_maps = sparse_maps(auto)
    WQ, WR, WZ = dual_state
    WQ1 = [[0] * D for _ in range(D)]
    WR1 = [[0] * D for _ in range(D)]
    WZ1 = [[0] * D for _ in range(D)]

    def push_add(target, a, b, W, sign=1):
        sa, sb = s_maps[a], s_maps[b]
        ca, cb = c_maps[a], c_maps[b]
        for u in range(D):
            wu = W[u]
            su = sa[u]
            cu = ca[u] * sign
            if cu == 0:
                continue
            for v in range(D):
                val = wu[v]
                if val:
                    target[su][sb[v]] += val * cu * cb[v]

    WQ_T = [[WQ[v][u] for v in range(D)] for u in range(D)]

    # Adjoint contributions to WQ1 (from Q terms in Q1 and R1):
    for a, b in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (3, 3)]:
        push_add(WQ1, a, b, WQ, +1)
    for a, b in [(0, 2), (1, 2), (3, 0), (3, 1)]:
        push_add(WQ1, a, b, WR, +1)

    # Adjoint contributions to WR1 (from R terms in Q1 and R1):
    push_add(WR1, 2, 3, WQ, +1)
    # From pull(3, 2, R^T) in Q1: sum W_Q(u,v) c3(u) c2(v) R(s2(v), s3(u)) -> push (2, 3) on WQ^T!
    push_add(WR1, 2, 3, WQ_T, +1)
    for a, b in [(0, 3), (1, 3), (2, 0), (2, 1)]:
        push_add(WR1, a, b, WR, +1)

    # Adjoint contributions to WZ1 (from Z terms in Q1, R1, Z1):
    push_add(WZ1, 3, 3, WQ, -1)
    push_add(WZ1, 3, 0, WR, -1)
    push_add(WZ1, 3, 1, WR, -1)
    for a, b in [(0, 0), (0, 1), (1, 0), (1, 1)]:
        push_add(WZ1, a, b, WZ, +1)

    return (WQ1, WR1, WZ1)


def inner_qrz(A, B):
    D = len(A[0])
    return sum(
        A[t][u][v] * B[t][u][v]
        for t in range(3)
        for u in range(D)
        for v in range(D)
    )


def init_primal(auto):
    d = auto.d
    D = d * d
    v0 = [auto.init[p] * auto.init[q] for p in range(d) for q in range(d)]
    Q0 = [[v0[u] * v0[v] for v in range(D)] for u in range(D)]
    R0 = [[0] * D for _ in range(D)]
    Z0 = [[v0[u] * v0[v] for v in range(D)] for u in range(D)]
    return (Q0, R0, Z0)


def dual_E4_state0(auto):
    D = auto.d * auto.d
    WQ = [[0] * D for _ in range(D)]
    WR = [[0] * D for _ in range(D)]
    WZ = [[0] * D for _ in range(D)]
    WQ[0][0] = 2
    WZ[0][0] = -1
    return (WQ, WR, WZ)


def dual_TotE4(auto):
    d = auto.d
    D = d * d
    WQ = [[0] * D for _ in range(D)]
    WR = [[0] * D for _ in range(D)]
    WZ = [[0] * D for _ in range(D)]
    for q in range(d):
        idx = q * d + q
        WQ[idx][idx] = 2
        WZ[idx][idx] = -1
    return (WQ, WR, WZ)


def check_dual_cert(auto, W0, k0, coeffs):
    """Pure-data exact certificate checker matching Lean's checkDualCert."""
    r = len(coeffs)
    W_list = [W0]
    for _ in range(k0 + r):
        W_list.append(dual_step(auto, W_list[-1]))
    target = W_list[k0 + r]
    D = auto.d * auto.d
    for t in range(3):
        for u in range(D):
            for v in range(D):
                rhs = sum(coeffs[j] * W_list[k0 + j][t][u][v] for j in range(r))
                if target[t][u][v] != rhs:
                    return False
    return True


def verify_all():
    print("=" * 72)
    print("EXACT PURE-SILICON VERIFICATION & CERTIFICATE SYNTHESIS (ZERO FLOAT)")
    print("=" * 72)

    # 1. Verify bitwise equivalences on n = 0 .. 2047
    rs = rudin_shapiro_auto()
    pf = paperfolding_auto()
    bs = baum_sweet_auto()
    m6 = mask6_101_xor_110_auto()
    m9 = mask9_100_xor_111_auto()
    cub = cubic_L4_auto()
    brk = broken_111_only_auto()

    for n in range(2048):
        assert rs.eval(0, n) == direct_rudin_shapiro(n)
        assert pf.eval(0, n) == direct_paperfolding_p_succ(n)
        assert bs.eval(0, n) == direct_baum_sweet(n)
        assert m6.eval(0, n) == direct_101_xor_110(n)
        assert m9.eval(0, n) == direct_100_xor_111(n)
        assert cub.eval(0, n) == direct_cubic_111_xor_1xx1(n)
    print("[PASS] 1. Direct bitwise equivalence verified for all 6 sequences on n = 0..2047.")

    # 2. Verify Universal Bijective-Tail Flat-Spectrum & Polynomial Pythagorean Identities
    #    on ALL 16 L=4 nonlinear functions (m=2), plus cubic witness up to k=6, plus sharpness counterexample!
    for psi_mask in range(16):
        psi = [(psi_mask >> r) & 1 for r in range(4)]
        A = bij_tail_auto(f"bij-m2-{psi_mask}", 2, psi)
        for k in range(1, 5):
            for s in range(1, 1 << k):
                assert sum(direct_apcorr(A, q, q, k, s) for q in range(8)) == 0
    # Verify exact polynomial Pythagorean identity for cubic L=4 at X in {-3, -1, 1, 2, 5}
    for k in range(0, 6):
        N = 1 << k
        for X in (-3, -1, 1, 2, 5):
            lhs = 0
            for q in range(8):
                P = sum(cub.eval(q, n) * (X ** n) for n in range(N))
                Prev = sum(cub.eval(q, n) * (X ** (N - 1 - n)) for n in range(N))
                lhs += P * Prev
            assert lhs == (1 << (k + 3)) * (X ** (N - 1))
    # Sharpness counterexample for broken 111-only:
    brk_sum_1_1 = sum(direct_apcorr(brk, q, q, 1, 1) for q in range(8))
    assert brk_sum_1_1 == 4
    print(f"[PASS] 2. Bijective-Tail flat spectrum verified on ALL 16 m=2 automata + cubic polynomial identity.")
    print(f"          Sharpness counterexample (111-only, non-bijective): sum_q A_{{q,q}}(1,1) = {brk_sum_1_1} != 0.")

    # 3. Verify Exhaustive L=4 Converse (all 256 masks with sig0=1):
    hier_cnt = 0
    non_hier_max_k = 0
    for mask in range(256):
        bits = [(mask >> q) & 1 for q in range(8)]
        is_r3 = all(bits[2*r] != bits[2*r+1] for r in range(4))
        is_r2 = all(bits[2*r] == bits[2*r+1] for r in range(4)) and all(bits[4*r] != bits[4*r+2] for r in range(2))
        is_r1 = all(bits[q] == bits[0] for q in range(4)) and all(bits[q] == bits[4] for q in range(4, 8)) and bits[0] != bits[4]
        if is_r3 or is_r2 or is_r1:
            hier_cnt += 1
        else:
            A = debruijn_auto(f"m{mask}", 2, [1]*8, [-1 if b else 1 for b in bits])
            fail_k = None
            for k in range(1, 5):
                if any(sum(direct_apcorr(A, q, q, k, s) for q in range(8)) != 0 for s in range(1, 1 << k)):
                    fail_k = k
                    break
            assert fail_k is not None
            non_hier_max_k = max(non_hier_max_k, fail_k)
    assert hier_cnt == 22
    print(f"[PASS] 3. Exhaustive L=4 converse check: 22/256 hierarchical bijective; all 234 others fail by k <= {non_hier_max_k}.")

    # 4. Verify Adjointness of sparse dual_step against primal_step + direct E4!
    for A in [rs, pf, bs, m6, m9]:
        S = init_primal(A)
        W = dual_E4_state0(A)
        for k in range(6):
            e4_dir = direct_E4(A, 0, k)
            e4_primal = inner_qrz(W, S)
            assert e4_dir == e4_primal, f"Primal mismatch on {A.name} k={k}"
            S_next = primal_step(A, S)
            W_next = dual_step(A, W)
            assert inner_qrz(W_next, S) == inner_qrz(W, S_next), f"Adjoint mismatch on {A.name} k={k}"
            S = S_next
    print("[PASS] 4. Sparse O(D^2) primal_step / dual_step adjointness & direct E4 match verified for all 5 automata.")

    # 5. Verify ALL FOUR Dual-Krylov Certificates + Mutation Rejection Tests!
    certs = [
        ("Paperfolding E4_0", pf, dual_E4_state0(pf), 3, [-192, 568, -660, 386, -119, 18]),
        ("Baum-Sweet E4_0", bs, dual_E4_state0(bs), 0, [2, -2, -5, 5, 8, 1]),
        ("L3-mask6 (101^110) TotE4", m6, dual_TotE4(m6), 1, [256, 0, 16, 0, 2]),
        ("L3-mask9 (100^111) TotE4", m9, dual_TotE4(m9), 1, [256, 0, 16, 0, 2]),
        ("Rudin-Shapiro E4_0", rs, dual_E4_state0(rs), 2, [-16, 4, 4]),
    ]
    for label, A, W0, k0, coeffs in certs:
        ok = check_dual_cert(A, W0, k0, coeffs)
        assert ok, f"Certificate failed for {label}"
        bad = list(coeffs)
        bad[-1] += 1
        bad_ok = check_dual_cert(A, W0, k0, bad)
        assert not bad_ok, f"Mutation NOT rejected for {label}"
        print(f"[PASS] 5. Dual-Krylov cert [{label}]: k0={k0}, r={len(coeffs)}, coeffs={coeffs} | valid=True, mutated=False")

    # 6. Verify concrete consequences & sharpness boundaries up to k = 15 (via exact QRZ):
    # (a) Paperfolding closed form & mod 8 sharpness
    S_pf = init_primal(pf)
    W_pf = dual_E4_state0(pf)
    pf_vals = []
    for k in range(16):
        val = inner_qrz(W_pf, S_pf)
        pf_vals.append(val)
        rhs = 2 * (8 ** k) + (63 * k * k - 693 * k + 2317) * (2 ** k) - 4440
        if k >= 2:
            assert 21 * val == rhs
        else:
            assert 21 * val != rhs
        if k >= 3:
            assert val % 8 == 0
        S_pf = primal_step(pf, S_pf)
    assert pf_vals[2] == 20 and pf_vals[2] % 8 != 0
    print(f"[PASS] 6a. Paperfolding: 21*E4(k) = 2*8^k + (63k^2-693k+2317)*2^k - 4440 verified k=2..15;")
    print(f"           Sharpness: fails at k=0 (21 != -2121), k=1 (126 != -1050); 8|E4(k) for k>=3, fails k=2 (E4(2)=20).")

    # (b) Baum-Sweet degree-5 recurrence & period-3 parity
    S_bs = init_primal(bs)
    W_bs = dual_E4_state0(bs)
    bs_vals = []
    for k in range(16):
        bs_vals.append(inner_qrz(W_bs, S_bs))
        assert (bs_vals[k] % 2 == 0) == (k % 3 == 1)
        S_bs = primal_step(bs, S_bs)
    for k in range(11):
        assert bs_vals[k+5] == 2*bs_vals[k+4] + 6*bs_vals[k+3] - bs_vals[k+2] - 4*bs_vals[k+1] + 2*bs_vals[k]
    print(f"[PASS] 6b. Baum-Sweet: degree-5 E4 recurrence & period-3 parity (even iff k%3==1) verified k=0..15.")

    # (c) L3 mask6 & mask9 TotE4 recurrence, 4^(k+6) law, exact 2-adic valuation v2(T(k)) = k+2, and isospectrality
    S_m6 = init_primal(m6)
    S_m9 = init_primal(m9)
    W_m6 = dual_TotE4(m6)
    W_m9 = dual_TotE4(m9)
    W0_m6 = dual_E4_state0(m6)
    W0_m9 = dual_E4_state0(m9)
    t6, t9, e6_0, e9_0 = [], [], [], []
    for k in range(15):
        v6 = inner_qrz(W_m6, S_m6)
        v9 = inner_qrz(W_m9, S_m9)
        assert v6 == v9
        assert v6 % (1 << (k + 2)) == 0 and v6 % (1 << (k + 3)) != 0
        t6.append(v6)
        t9.append(v9)
        e6_0.append(inner_qrz(W0_m6, S_m6))
        e9_0.append(inner_qrz(W0_m9, S_m9))
        S_m6 = primal_step(m6, S_m6)
        S_m9 = primal_step(m9, S_m9)
    for k in range(10):
        assert t6[k+5] == 2*t6[k+4] + 16*t6[k+2] + 256*t6[k]
        assert t6[k+4] + 2*t6[k+3] + 8*t6[k+2] + 16*t6[k+1] + 64*t6[k] == 4 ** (k + 6)
    assert e6_0[4] == 464 and e9_0[4] == 528 and e6_0[4] != e9_0[4]
    print(f"[PASS] 6c. L3 (101^110) & (100^111): TotE4 recurrence, 4^(k+6) law, exact v2(T(k))=k+2,")
    print(f"           and TotE4 isospectrality verified k=0..14; sharpness: E4_0(4) = {e6_0[4]} != {e9_0[4]}.")
    print("=" * 72)
    print("ALL EXACT CHECKS PASSED.")


if __name__ == "__main__":
    verify_all()
