#!/usr/bin/env python3
"""
explore_and_verify.py — Pure Silicon Exact Exploration, Certificate Synthesis,
Independent Replay & Sharpness Falsification for:
  Bit-Sliced 1D Cellular Automaton Transducer Composition & Coboundary Engine

Strictly CPU-only, 100% exact integer/boolean arithmetic (ZERO floating point).
"""

from collections import deque


# ============================================================================
# 1. Generic Finite-State Mealy Transducer Engine (Exact Integer/Bool)
# ============================================================================

class Mealy:
    """Synchronous finite-state Mealy transducer over alphabet {0, 1}."""
    def __init__(self, n_states, q0, delta, lam):
        self.n = n_states
        self.q0 = q0
        self.delta = delta  # delta[q][b] -> next state
        self.lam = lam      # lam[q][b] -> output bit in {0, 1}

    def run(self, bits):
        q = self.q0
        out = []
        for b in bits:
            out.append(self.lam[q][b])
            q = self.delta[q][b]
        return out, q

    def reachable_minimize(self):
        vis = {self.q0: 0}
        order = [self.q0]
        idx = 0
        while idx < len(order):
            q = order[idx]
            idx += 1
            for b in (0, 1):
                qn = self.delta[q][b]
                if qn not in vis:
                    vis[qn] = len(order)
                    order.append(qn)
        m = len(order)
        d = [[vis[self.delta[q][b]] for b in (0, 1)] for q in order]
        l = [[self.lam[q][b] for b in (0, 1)] for q in order]

        part = [l[q][0] * 2 + l[q][1] for q in range(m)]
        while True:
            sig_map = {}
            new_part = []
            for q in range(m):
                sig = (part[q], part[d[q][0]], part[d[q][1]])
                if sig not in sig_map:
                    sig_map[sig] = len(sig_map)
                new_part.append(sig_map[sig])
            if new_part == part:
                break
            part = new_part

        k = max(part) + 1
        rep = [0] * k
        for q in range(m):
            rep[part[q]] = q
        md = [[part[d[rep[c]][b]] for b in (0, 1)] for c in range(k)]
        ml = [[l[rep[c]][b] for b in (0, 1)] for c in range(k)]
        return Mealy(k, part[0], md, ml)

    def compose_raw(self, other):
        """Exact unminimized composition (self o other)(x) = self(other(x))."""
        n = other.n * self.n
        q0 = other.q0 * self.n + self.q0
        d = [[0, 0] for _ in range(n)]
        l = [[0, 0] for _ in range(n)]
        for qo in range(other.n):
            for qs in range(self.n):
                idx = qo * self.n + qs
                for b in (0, 1):
                    mid = other.lam[qo][b]
                    d[idx][b] = other.delta[qo][b] * self.n + self.delta[qs][mid]
                    l[idx][b] = self.lam[qs][mid]
        return Mealy(n, q0, d, l)

    def compose(self, other):
        return self.compose_raw(other).reachable_minimize()

    def is_identity(self):
        m = self.reachable_minimize()
        return m.n == 1 and m.lam[0][0] == 0 and m.lam[0][1] == 1

    def synthesize_bisim(self, other):
        """
        Compute the exact reachable product relation R subset Q1 x Q2.
        Returns (True, R_set) iff self and other are bisimilar (equal on all {0,1}*).
        """
        vis = {(self.q0, other.q0)}
        dq = deque([(self.q0, other.q0)])
        while dq:
            q1, q2 = dq.popleft()
            for b in (0, 1):
                if self.lam[q1][b] != other.lam[q2][b]:
                    return False, None
                nxt = (self.delta[q1][b], other.delta[q2][b])
                if nxt not in vis:
                    vis.add(nxt)
                    dq.append(nxt)
        return True, vis

    def is_strongly_connected(self):
        for start in range(self.n):
            vis = {start}
            dq = deque([start])
            while dq:
                q = dq.popleft()
                for b in (0, 1):
                    qn = self.delta[q][b]
                    if qn not in vis:
                        vis.add(qn)
                        dq.append(qn)
            if len(vis) != self.n:
                return False
        return True

    def is_causal_bijective(self):
        vis = {self.q0}
        dq = deque([self.q0])
        while dq:
            q = dq.popleft()
            if self.lam[q][0] == self.lam[q][1]:
                return False
            for b in (0, 1):
                qn = self.delta[q][b]
                if qn not in vis:
                    vis.add(qn)
                    dq.append(qn)
        return True

    def synthesize_coboundary(self, ofn, odel, oq0):
        """
        Synthesize an exact integer coboundary potential phi on reachable (q, s_in, s_out)
        such that:
          ofn[s_out][y] - ofn[s_in][b] = phi[q', s_in', s_out'] - phi[q, s_in, s_out].
        Returns (True, phi_dict) or (False, None).
        """
        start = (self.q0, oq0, oq0)
        phi = {start: 0}
        dq = deque([start])
        while dq:
            q, si, so = dq.popleft()
            for b in (0, 1):
                y = self.lam[q][b]
                qn = self.delta[q][b]
                sin = odel[si][b]
                son = odel[so][y]
                exp = phi[(q, si, so)] + ofn[so][y] - ofn[si][b]
                nxt = (qn, sin, son)
                if nxt in phi:
                    if phi[nxt] != exp:
                        return False, None
                else:
                    phi[nxt] = exp
                    dq.append(nxt)
        return True, phi


# ============================================================================
# 2. Carried-Hybrid 1D Cellular Automaton Constructors
# ============================================================================

def make_chca2(out_rule, carry_rule):
    """
    2-cell Carried-Hybrid 1D CA (CHCA-2):
    State q = 2 * x_{i-1} + c_i in {0,1,2,3}, initial state q0 = 0.
    idx = 4 * x_{i-1} + 2 * x_i + c_i.
    """
    delta = [[0, 0] for _ in range(4)]
    lam = [[0, 0] for _ in range(4)]
    for q in range(4):
        xp, c = q >> 1, q & 1
        for b in (0, 1):
            idx = (xp << 2) | (b << 1) | c
            lam[q][b] = (out_rule >> idx) & 1
            delta[q][b] = (b << 1) | ((carry_rule >> idx) & 1)
    return Mealy(4, 0, delta, lam)


def make_fredkin_router(d):
    """Parametric Carried Fredkin Router F_d (delay d >= 1, 2^(d+1) states)."""
    n = 1 << (d + 1)
    mask = (1 << d) - 1
    delta = [[0, 0] for _ in range(n)]
    lam = [[0, 0] for _ in range(n)]
    for q in range(n):
        hist = q >> 1
        c = q & 1
        xd = (hist >> (d - 1)) & 1
        for b in (0, 1):
            y = xd if b else c
            cn = c if b else xd
            nhist = ((hist << 1) | b) & mask
            lam[q][b] = y
            delta[q][b] = (nhist << 1) | cn
    return Mealy(n, 0, delta, lam)


def make_walk_involution(K):
    """Parametric Bounded-Walk Bijective Involution W_K (capacity K >= 1, 2K+1 states)."""
    n = 2 * K + 1
    delta = [[0, 0] for _ in range(n)]
    lam = [[0, 0] for _ in range(n)]
    for s in range(n):
        if s == 0 or s == 2 * K:
            lam[s] = [0, 1]
            delta[s] = [s, s]
        else:
            lam[s] = [1, 0]
            delta[s] = [s + 1, s - 1]
    return Mealy(n, K, delta, lam)


def nat_to_bits(n):
    bits = []
    while n > 0:
        bits.append(n & 1)
        n >>= 1
    return bits


def bits_to_nat(bits):
    v = 0
    for i, b in enumerate(bits):
        if b:
            v |= (1 << i)
    return v


def alt_sum_bits(bits):
    return sum((1 if i % 2 == 0 else -1) * b for i, b in enumerate(bits))


def popcount_bits(bits):
    return sum(bits)


def step_flushed(T, bits, flush_zeros):
    out, qf = T.run(bits + [0] * flush_zeros)
    assert qf == T.q0, f"Transducer failed to flush in {flush_zeros} zeros (landed at {qf})"
    return out


# ============================================================================
# 3. Exhaustive CHCA-2 Classification (All 65,536 Rules)
# ============================================================================

def run_exhaustive_chca2_scan():
    print("=" * 72)
    print("PHASE 1: Exhaustive Exact Scan of All 65,536 CHCA-2 Rules")
    print("=" * 72)
    obs_defs = {
        "popcount": ([[0, 1]], [[0, 0]], 0),
        "alt_sum": ([[0, 1], [0, -1]], [[1, 1], [0, 0]], 0),
        "domain_walls": ([[0, 1], [1, 0]], [[0, 1], [0, 1]], 0),
        "blocks_11": ([[0, 0], [0, 1]], [[0, 1], [0, 1]], 0),
    }

    total_bij = 0
    bij_min3 = 0
    bij_sc_nonid = 0
    bij_p2_min3 = 0
    bij_p4_min3 = 0
    bij_conserving = {k: 0 for k in obs_defs}
    nonbij_conserving = {k: 0 for k in obs_defs}

    for o in range(256):
        for c in range(256):
            T = make_chca2(o, c)
            Tm = T.reachable_minimize()
            is_bij = T.is_causal_bijective()
            if is_bij:
                total_bij += 1
                if Tm.n >= 3:
                    bij_min3 += 1
                    if Tm.is_strongly_connected():
                        bij_sc_nonid += 1
                    T2 = Tm.compose(Tm)
                    if T2.is_identity():
                        bij_p2_min3 += 1
                    elif T2.compose(T2).is_identity():
                        bij_p4_min3 += 1

            if Tm.n >= 3:
                for name, (ofn, odel, oq0) in obs_defs.items():
                    ok, _ = T.synthesize_coboundary(ofn, odel, oq0)
                    if ok:
                        if is_bij:
                            bij_conserving[name] += 1
                        else:
                            nonbij_conserving[name] += 1

    print(f"Total CHCA-2 rules scanned:                        65,536")
    print(f"Causal bijective (all-width bijections):           {total_bij}")
    print(f"  with minimal states >= 3:                        {bij_min3}")
    print(f"  strongly connected (min states >= 3):            {bij_sc_nonid}")
    print(f"  exact uniform period 2 (min states >= 3):        {bij_p2_min3}")
    print(f"  exact uniform period 4 (min states >= 3):        {bij_p4_min3}")
    print("Conservation laws (|T_min| >= 3):")
    for name in obs_defs:
        print(f"  {name:14s}: bijective = {bij_conserving[name]:4d} | non-bijective = {nonbij_conserving[name]:4d}")
    assert bij_conserving["popcount"] == 0
    assert bij_conserving["alt_sum"] == 0
    print("Verified empirically: ZERO bijective CHCA-2 (|T_min|>=3) conserve popcount or alt_sum!")


# ============================================================================
# 4. Certificate Synthesis & Independent Exact Replay Verification
# ============================================================================

def verify_carried_rule30_and_semigroup():
    print("\n" + "=" * 72)
    print("PHASE 2: Carried Wolfram Rule 30 (T_{30,120}), Semigroup & Dual T_{120,30}")
    print("=" * 72)

    T30 = make_chca2(30, 120)
    T46 = make_chca2(46, 116)
    T120 = make_chca2(120, 30)

    assert T30.is_strongly_connected()
    assert T46.is_strongly_connected()
    assert T120.is_strongly_connected()

    # Synthesize exact coboundary for T30 and T46 on alt_sum
    alt_ofn, alt_odel, alt_q0 = [[0, 1], [0, -1]], [[1, 1], [0, 0]], 0
    ok30, phi30 = T30.synthesize_coboundary(alt_ofn, alt_odel, alt_q0)
    ok46, phi46 = T46.synthesize_coboundary(alt_ofn, alt_odel, alt_q0)
    assert ok30 and ok46
    print("T_{30,120} alt_sum coboundary certificate (xp, c, parity -> phi):")
    for (q, si, so), v in sorted(phi30.items()):
        if si == so:
            xp, c = q >> 1, q & 1
            formula = (1 if si == 0 else -1) * c * (2 * xp - 1)
            assert v == formula
            print(f"  (xp={xp}, c={c}, p={si}) -> phi = {v:+d}")

    # Synthesize exact coboundary for Dual T120 on popcount
    pop_ofn, pop_odel, pop_q0 = [[0, 1]], [[0, 0]], 0
    ok120, phi120 = T120.synthesize_coboundary(pop_ofn, pop_odel, pop_q0)
    assert ok120
    print("Dual T_{120,30} popcount coboundary certificate (xp, c -> phi):")
    for (q, si, so), v in sorted(phi120.items()):
        xp, c = q >> 1, q & 1
        formula = -(xp + (xp ^ c))
        assert v == formula
        print(f"  (xp={xp}, c={c}) -> phi = {v:+d}")

    # Independent replay: all n in 0..4095, iterates t = 1..6, plus mixed semigroup words!
    max_pop_growth = 0
    for n in range(4096):
        bits = nat_to_bits(n)
        a0 = alt_sum_bits(bits)
        m0 = n % 3
        cur = bits
        for _ in range(6):
            cur = step_flushed(T30, cur, 2)
            assert alt_sum_bits(cur) == a0
            assert bits_to_nat(cur) % 3 == m0
            diff_pop = popcount_bits(cur) - popcount_bits(bits)
            if diff_pop > max_pop_growth:
                max_pop_growth = diff_pop
        # Mixed semigroup word: T30 o T46 o T30 o T46
        w = step_flushed(T46, bits, 2)
        w = step_flushed(T30, w, 2)
        w = step_flushed(T46, w, 2)
        w = step_flushed(T30, w, 2)
        assert alt_sum_bits(w) == a0
        assert bits_to_nat(w) % 3 == m0
        # Unflushed defect bound on T30 and T120
        y30, _ = T30.run(bits)
        assert -1 <= alt_sum_bits(y30) - a0 <= 1
        y120, _ = T120.run(bits)
        assert -2 <= popcount_bits(y120) - popcount_bits(bits) <= 0

    print(f"Replay PASSED for all n in [0..4095] x 6 iterates + mixed semigroup words!")
    print(f"  Observed chaotic popcount growth under T30^6 while alt_sum stays invariant: +{max_pop_growth}")

    # SHARPNESS: Test EVERY single-bit perturbation of out=30 or carry=120!
    print("Sharpness check — all 16 single-bit perturbations of T_{30,120}:")
    broken_count = 0
    for bit in range(8):
        for kind, o_pert, c_pert in [("out", 30 ^ (1 << bit), 120), ("carry", 30, 120 ^ (1 << bit))]:
            Tp = make_chca2(o_pert, c_pert)
            ok_p, _ = Tp.synthesize_coboundary(alt_ofn, alt_odel, alt_q0)
            assert not ok_p, f"Perturbation {kind} bit {bit} unexpectedly preserved coboundary!"
            # Find smallest concrete unflushed/flushed violation
            witness = None
            for wlen in range(1, 7):
                for x in range(1 << wlen):
                    bs = [(x >> i) & 1 for i in range(wlen)]
                    ys, _ = Tp.run(bs)
                    if abs(alt_sum_bits(ys) - alt_sum_bits(bs)) > 1:
                        witness = (bs, ys, alt_sum_bits(ys) - alt_sum_bits(bs))
                        break
                if witness:
                    break
            broken_count += 1
    print(f"  ALL {broken_count}/16 single-bit perturbations BREAK alt_sum coboundary conservation!")


def verify_fredkin_router_family():
    print("\n" + "=" * 72)
    print("PHASE 3: Parametric Carried Fredkin Router Family F_d (d = 1..6)")
    print("=" * 72)
    pop_ofn, pop_odel, pop_q0 = [[0, 1]], [[0, 0]], 0
    for d in range(1, 7):
        Fd = make_fredkin_router(d)
        assert Fd.is_strongly_connected()
        ok, phi = Fd.synthesize_coboundary(pop_ofn, pop_odel, pop_q0)
        assert ok
        # Verify closed-form potential phi(hist, c) = -(c + popcount(hist))
        for (q, _, _), val in phi.items():
            hist, c = q >> 1, q & 1
            assert val == -(c + hist.bit_count())
        # Replay on all n in 0..1023 for 3 iterates
        for n in range(1024):
            bits = nat_to_bits(n)
            p0 = popcount_bits(bits)
            y_unflushed, _ = Fd.run(bits)
            assert -(d + 1) <= popcount_bits(y_unflushed) - p0 <= 0
            cur = bits
            for _ in range(3):
                cur = step_flushed(Fd, cur, d + 1)
                assert popcount_bits(cur) == p0
        # Carry-tunneling witness across run of 10 ones
        tunnel_in = [1] * 10 + [0] * (d + 1)
        tunnel_out, qf = Fd.run(tunnel_in)
        assert qf == 0 and popcount_bits(tunnel_out) == 10
        print(f"  F_{d}: states={Fd.n:3d}, strongly_conn=True, exact phi in [{-(d+1)}, 0], flush={d+1}, replay 1024x3 PASSED")


def verify_walk_involution_family():
    print("\n" + "=" * 72)
    print("PHASE 4: Parametric Bounded-Walk Bijective Involution Family W_K (K = 1..8)")
    print("=" * 72)
    pop_ofn, pop_odel, pop_q0 = [[0, 1]], [[0, 0]], 0
    for K in range(1, 9):
        WK = make_walk_involution(K)
        assert WK.is_causal_bijective()
        assert not WK.is_strongly_connected()  # Absorbing walls at s=0, 2K!
        # Verify W_K o W_K = id via bisimulation
        W2 = WK.compose_raw(WK)
        Id = Mealy(1, 0, [[0, 0]], [[0, 1]])
        ok_b, rel = W2.synthesize_bisim(Id)
        assert ok_b
        # Verify exact coboundary phi(s) = s - K
        ok_c, phi = WK.synthesize_coboundary(pop_ofn, pop_odel, pop_q0)
        assert ok_c
        for (s, _, _), v in phi.items():
            assert v == s - K
        # Sharp attainment of +K and -K
        y_pos, _ = WK.run([0] * K)
        y_neg, _ = WK.run([1] * K)
        assert popcount_bits(y_pos) - 0 == K
        assert popcount_bits(y_neg) - K == -K
        # Deep flip witness for K >= 2
        if K >= 2:
            alt = [i % 2 for i in range(40)]
            y_alt, _ = WK.run(alt)
            assert y_alt == [1 - b for b in alt]
        print(f"  W_{K}: states={WK.n:2d}, W_K^2=id (|R|={len(rel):2d}), phi in [{-K:+d},{+K:+d}], sharp +-K attained, deep_flip={'YES' if K>=2 else 'N/A'}")


def verify_period4_carried_ca():
    print("\n" + "=" * 72)
    print("PHASE 5: Deep Nonlinear Period-4 Carried-Hybrid CA (T_{54,105})")
    print("=" * 72)
    T54_105 = make_chca2(54, 105)
    T54_85 = make_chca2(54, 85)
    Tmin = T54_105.reachable_minimize()
    assert T54_105.is_causal_bijective()
    assert Tmin.n == 3 and Tmin.is_strongly_connected()

    # Bisimulation collapse T54_105 ~ T54_85
    ok_eq, rel_eq = T54_105.synthesize_bisim(T54_85)
    assert ok_eq
    print(f"T_{{54,105}} ~ T_{{54,85}} bisimulation VERIFIED (|R| = {len(rel_eq)}): {sorted(rel_eq)}")

    # Exact Period 4 via transducer composition Tmin^4 ~ id
    T2 = Tmin.compose_raw(Tmin)
    T4 = T2.compose_raw(T2)
    Id = Mealy(1, 0, [[0, 0]], [[0, 1]])
    ok_p4, rel_p4 = T4.synthesize_bisim(Id)
    assert ok_p4
    ok_p2, _ = T2.synthesize_bisim(Id)
    assert not ok_p2
    print(f"T_{{54,105}}^4 ~ id VERIFIED (|R| = {len(rel_p4)} reachable pairs in 3^4 = 81 states)")
    print(f"T_{{54,105}}^2 != id VERIFIED (witness [0,1,0] -> T^2 = {T2.run([0,1,0])[0]})")

    # Exhaustive replay on all 12-bit strings
    for x in range(1 << 12):
        bs = [(x >> i) & 1 for i in range(12)]
        cur = bs
        for _ in range(4):
            cur, _ = T54_105.run(cur)
        assert cur == bs
    print("Independent exact replay: T_{54,105}^4(x) = x for ALL 4,096 12-bit vectors PASSED!")

    # Unbounded defect witness (confirming Rigidity Theorem 1 corollary):
    # On [0, 0]^m, T_{54,105} maps [0,0] -> [0,1], so popcount defect = +m (unbounded above!)
    # On [0, 1]^m, let's check both popcount and alt_sum growth!
    for m in (4, 8, 16):
        z2m = [0, 0] * m
        y_z, _ = T54_105.run(z2m)
        o2m = [0, 1] * m
        y_o, _ = T54_105.run(o2m)
        print(f"  m={m:2d}: pop_defect([0,0]^m)={popcount_bits(y_z)-popcount_bits(z2m):+3d}, alt_defect([0,0]^m)={alt_sum_bits(y_z)-alt_sum_bits(z2m):+3d}, alt_defect([0,1]^m)={alt_sum_bits(y_o)-alt_sum_bits(o2m):+3d}")


def verify_sharpness_zero_weight():
    print("\n" + "=" * 72)
    print("PHASE 6: Sharpness of Nowhere-Zero Weight Hypothesis (FlipOdd)")
    print("=" * 72)
    # 2-state strongly connected causal bijective involution FlipOdd:
    # q=0 (even index): id -> q=1; q=1 (odd index): flip -> q=0
    FlipOdd = Mealy(2, 0, [[1, 1], [0, 0]], [[0, 1], [1, 0]])
    assert FlipOdd.is_causal_bijective()
    assert FlipOdd.is_strongly_connected()
    assert not FlipOdd.is_identity()
    # Even-only weight w(2k)=1, w(2k+1)=0: exact zero defect for all x!
    for x in range(1024):
        bs = [(x >> i) & 1 for i in range(10)]
        ys, _ = FlipOdd.run(bs)
        w_in = sum(b for i, b in enumerate(bs) if i % 2 == 0)
        w_out = sum(b for i, b in enumerate(ys) if i % 2 == 0)
        assert w_out == w_in
    print("FlipOdd (strongly connected, causal bijective, non-identity): EXACT ZERO defect on even-only weight w(i)=[i even] PASSED!")


if __name__ == "__main__":
    run_exhaustive_chca2_scan()
    verify_carried_rule30_and_semigroup()
    verify_fredkin_router_family()
    verify_walk_involution_family()
    verify_period4_carried_ca()
    verify_sharpness_zero_weight()
    print("\nALL EXACT EXPLORATION, CERTIFICATE SYNTHESIS, REPLAY & SHARPNESS CHECKS PASSED!")
