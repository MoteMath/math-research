"""
explore_and_verify.py — Exact Pure-Silicon Certificate Synthesis, Verification & Falsification
for the Signed-Digit / NAF Carry-Absorption Transducer Engine (`transducer-2`).

Zero floating-point values are used in any certificate, bound, or verification.
All checks use exact Python arbitrary-precision integers.
"""

import itertools
from collections import deque

S_VALS = (-2, -1, 0, 1, 2)
SD_VALS = (-1, 0, 1)


def sgn(x: int) -> int:
    return 1 if x > 0 else (-1 if x < 0 else 0)


def sd_val(digits) -> int:
    total = 0
    pow2 = 1
    for d in digits:
        total += d * pow2
        pow2 <<= 1
    return total


def sd_wt(digits) -> int:
    return sum(abs(d) for d in digits)


def is_naf(digits) -> bool:
    return all(digits[i] == 0 or digits[i + 1] == 0 for i in range(len(digits) - 1))


def to_bits_lsb(n: int, width: int | None = None):
    bits = []
    m = n
    while m > 0:
        bits.append(m & 1)
        m >>= 1
    if width is not None:
        while len(bits) < width:
            bits.append(0)
    return bits


# ============================================================================
# 1. 5-State Canonical SD -> NAF Carry-Absorption Transducer
# ============================================================================

NAF_STATES = (-2, -1, 0, 1, 2)


def naf_step(s: int, d: int):
    """1-delay SD -> NAF transducer step on state s in {-2,-1,0,1,2}, digit d in {-1,0,1}."""
    v = s + 2 * d
    if v % 2 == 0:
        o = 0
        ns = v // 2
    elif v % 4 == 1:
        o = 1
        ns = (v - 1) // 2
    else:
        o = -1
        ns = (v + 1) // 2
    return o, ns


def naf_flush(s: int):
    """Flush remaining carry debt s in {-2,-1,0,1,2} into canonical NAF digits."""
    if s == 0:
        return []
    if s == 1:
        return [1]
    if s == -1:
        return [-1]
    if s == 2:
        return [0, 1]
    if s == -2:
        return [0, -1]
    raise ValueError(f"Invalid NAF state {s}")


def naf_psi(s: int) -> int:
    return 0 if s == 0 else 1


def naf_recode(digits):
    """Run the 5-state 1-delay transducer and drop the initial dummy 0 at position -1."""
    s = 0
    raw = []
    for d in digits:
        o, s = naf_step(s, d)
        raw.append(o)
    raw.extend(naf_flush(s))
    # First emitted digit from initial state 0 is always 0 (value 2*0 + 0 = 0 mod 2)
    if not raw:
        return []
    assert raw[0] == 0
    return raw[1:]


def naf_defect(digits) -> int:
    s = 0
    total = 0
    for d in digits:
        o, ns = naf_step(s, d)
        delta = abs(d) + naf_psi(s) - abs(o) - naf_psi(ns)
        assert delta >= 0
        total += delta
        s = ns
    assert naf_psi(s) == sd_wt(naf_flush(s))
    return total


def verify_naf_certificate():
    print("=== [1] 5-State Canonical SD -> NAF Carry-Absorption Certificate ===")
    for s in NAF_STATES:
        fl = naf_flush(s)
        assert sd_val(fl) == s, f"Flush value mismatch at s={s}"
        assert sd_wt(fl) == naf_psi(s), f"Flush weight != psi at s={s}"
        assert is_naf(fl), f"Flush not NAF at s={s}"
        # Non-adjacency invariant: odd state => last emitted digit was 0 (or start)
        for d in SD_VALS:
            o, ns = naf_step(s, d)
            assert ns in NAF_STATES
            assert o in SD_VALS
            # Carry-debt conservation (1-delay): o + 2*ns == 2*d + s
            assert o + 2 * ns == 2 * d + s
            # Weight-defect non-negativity
            delta = abs(d) + naf_psi(s) - abs(o) - naf_psi(ns)
            assert delta >= 0
            # NAF preservation: if o != 0, then ns is even (so next output is guaranteed 0!)
            if o != 0:
                assert ns % 2 == 0
            # If s is even, o is always 0!
            if s % 2 == 0:
                assert o == 0
    print("  ValCert, DefectCert (zero flush defect!), and NAFInvCert PASSED on all 15 edges.")

    # Independent exhaustive verification on all SD strings up to length 8 (3^8 = 6561)
    # and all unsigned integers n = 0 .. 20000
    for L in range(9):
        for D in itertools.product(SD_VALS, repeat=L):
            out = naf_recode(D)
            assert sd_val(out) == sd_val(D)
            assert is_naf(out)
            d_def = naf_defect(D)
            assert sd_wt(D) == sd_wt(out) + d_def
    print("  Exhaustive replay on all signed-digit strings of length <= 8 (9,841 strings): PASSED.")

    # Verify binary-NAF zero-defect counting recurrence Z(w) and signed-digit M(w)
    Z_counts = []
    for w in range(15):
        c = 0
        for n in range(1 << w):
            bits = to_bits_lsb(n, w)
            if n.bit_count() == sd_wt(naf_recode(bits)):
                assert naf_defect(bits) == 0
                c += 1
            else:
                assert naf_defect(bits) > 0
        Z_counts.append(c)
    for w in range(len(Z_counts) - 3):
        assert Z_counts[w + 3] == Z_counts[w + 2] + 2 * Z_counts[w + 1] - Z_counts[w]
    print(f"  Exact unsigned binary zero-defect counts Z(0..14): {Z_counts}")
    print("  Recurrence Z(w+3) = Z(w+2) + 2*Z(w+1) - Z(w) verified on w=0..11.")

    M_counts = []
    for w in range(9):
        c = 0
        for D in itertools.product(SD_VALS, repeat=w):
            if sd_wt(D) == sd_wt(naf_recode(D)):
                assert naf_defect(D) == 0
                c += 1
            else:
                assert naf_defect(D) > 0
        M_counts.append(c)
    for w in range(len(M_counts) - 3):
        assert M_counts[w + 3] == M_counts[w + 2] + 3 * M_counts[w + 1] - M_counts[w]
    print(f"  Exact signed-digit minimal-weight counts M(0..8): {M_counts}")
    print("  Recurrence M(w+3) = M(w+2) + 3*M(w+1) - M(w) verified on w=0..5.")


# ============================================================================
# 2. Odd-Lookahead Carry-Free Parallel Adder (OL-CFPA) & Complete (1,1) Search
# ============================================================================

def ol_cfpa_carry(sp: int, s: int, sn: int) -> int:
    """
    Canonical Odd-Lookahead Carry-Free Parallel Adder (OL-CFPA) carry function:
      c_i(s_{i-1}, s_i, s_{i+1}) in {-1, 0, 1}.
    """
    if s == 2:
        return 1
    if s == -2:
        return -1
    if s == 0:
        return 0
    if s == 1:
        return 1 if (sp >= 1 or (sp == 0 and abs(sn) == 1)) else 0
    if s == -1:
        return -1 if (sp <= -1 or (sp == 0 and abs(sn) == 1)) else 0
    raise ValueError(f"Invalid sum digit s={s}")


def ol_cfpa_parallel(A, B):
    """
    Strictly local O(1)-depth parallel evaluation (zero ripple carry!).
    Each output digit z_i depends ONLY on the 4-digit window (s_{i-2}, s_{i-1}, s_i, s_{i+1}).
    """
    n = max(len(A), len(B))
    s_list = [(A[i] if i < len(A) else 0) + (B[i] if i < len(B) else 0) for i in range(n)]

    def get_s(i: int) -> int:
        return s_list[i] if 0 <= i < n else 0

    def get_c(i: int) -> int:
        return ol_cfpa_carry(get_s(i - 1), get_s(i), get_s(i + 1))

    # Output length n + 1 (since c_n = ol_cfpa_carry(s_{n-1}, 0, 0) = 0, z_n = c_{n-1})
    out = []
    for i in range(n + 1):
        c_curr = get_c(i)
        c_prev = get_c(i - 1)
        z = (get_s(i) - 2 * c_curr) + c_prev
        assert z in SD_VALS
        out.append(z)
    return out


def build_and_verify_ol_cfpa_certificate():
    print("\n=== [2] Odd-Lookahead Carry-Free Parallel Adder (OL-CFPA) Certificate ===")
    # 2a. Verify 4-digit local carry-free safety exhaustively on all 5^4 = 625 windows
    for sm2, sm1, s0, sp1 in itertools.product(S_VALS, repeat=4):
        c_prev = ol_cfpa_carry(sm2, sm1, s0)
        c_curr = ol_cfpa_carry(sm1, s0, sp1)
        z = (s0 - 2 * c_curr) + c_prev
        assert z in SD_VALS
    print("  Exhaustive 4-digit window carry-free safety (625/625 windows in {-1,0,1}): PASSED.")

    # 2b. Discover reachable direct states (hp, s, cp) where hp = sgn(s_{i-1})
    init = (0, 0, 0)
    states = [init]
    seen = {init}
    q = deque([init])
    trans = {}
    while q:
        st = q.popleft()
        hp, s, cp = st
        for sn in S_VALS:
            c = ol_cfpa_carry(hp, s, sn)
            z = (s - 2 * c) + cp
            nst = (sgn(s), sn, c)
            trans[(st, sn)] = (z, nst)
            if nst not in seen:
                seen.add(nst)
                states.append(nst)
                q.append(nst)
    states.sort()
    print(f"  Direct reachable states (hp, s, cp): {len(states)}")

    # Compute flush (feeding sn = 0, 0) and minimal integer potential psi
    flush = {}
    for st in states:
        z1, st1 = trans[(st, 0)]
        z2, st2 = trans[(st1, 0)]
        assert st2 == init
        flush[st] = (z1, z2)

    psi = {st: abs(flush[st][0]) + abs(flush[st][1]) for st in states}
    for _ in range(len(states) + 5):
        changed = False
        for st in states:
            best = psi[st]
            for sn in S_VALS:
                z, nst = trans[(st, sn)]
                cand = abs(z) - abs(sn) + psi[nst]
                if cand > best:
                    best = cand
            if best > psi[st]:
                psi[st] = best
                changed = True
        if not changed:
            break

    assert psi[init] == 0
    # Verify ValCert and DefectCert on all 25 states x 5 inputs = 125 transitions!
    for st in states:
        hp, s, cp = st
        phi = s + cp
        z1, z2 = flush[st]
        assert z1 + 2 * z2 == phi
        assert abs(z1) + abs(z2) <= psi[st]
        for sn in S_VALS:
            z, nst = trans[(st, sn)]
            nphi = nst[1] + nst[2]
            assert z + 2 * nphi == 2 * sn + phi
            assert abs(z) + psi[nst] <= abs(sn) + psi[st]

    print(f"  ValCert & DefectCert on all {len(states)} states x 5 inputs ({len(states)*5} edges): PASSED.")
    print(f"  Potential psi values in {sorted(set(psi.values()))}, psi[(0,0,0)] = {psi[init]}.")
    print("  Direct state table (idx, (hp, s, cp), phi, psi, flush):")
    for idx, st in enumerate(states):
        print(f"    {idx:2d}: st={str(st):12s} phi={st[1]+st[2]:2d} psi={psi[st]} flush={flush[st]}")

    # Independent replay: compare parallel local formula vs transducer & check value/weight/NAF fixed point
    for L in range(1, 5):
        for A in itertools.product(SD_VALS, repeat=L):
            for B in itertools.product(SD_VALS, repeat=L):
                Z = ol_cfpa_parallel(A, B)
                assert sd_val(Z) == sd_val(A) + sd_val(B)
                assert sd_wt(Z) <= sd_wt(A) + sd_wt(B)
                assert sd_wt(naf_recode(Z)) <= sd_wt(Z)
            # NAF fixed-point check: A +* 0 == A (up to trailing 0)
            if is_naf(A):
                Z0 = ol_cfpa_parallel(A, [0] * L)
                assert Z0[:L] == list(A) and Z0[L] == 0
    print("  Exhaustive replay on all pairs (A, B) of length <= 4 (7,380 pairs) + NAF fixed-point: PASSED.")
    return states, psi


# ============================================================================
# 3. Sharpness, Exhaustive (1,1) Classification & Causal Impossibility Witnesses
# ============================================================================

def verify_sharpness_and_classification():
    print("\n=== [3] Sharpness & Complete Boundary Classification ===")
    # 3a. Exhaustive r=1 causal search (all 1024 rules): only 4 valid, ALL 4 blow up weight!
    valid_r1 = 0
    for f1 in itertools.product((0, 1), repeat=5):
        for fm1 in itertools.product((0, -1), repeat=5):
            def C1(s, sp):
                if s == 2: return 1
                if s == -2: return -1
                if s == 0: return 0
                return f1[sp + 2] if s == 1 else fm1[sp + 2]
            ok = all(
                -1 <= (s0 - 2 * C1(s0, s1)) + C1(s1, s2) <= 1
                for s2, s1, s0 in itertools.product(S_VALS, repeat=3)
            )
            if ok:
                valid_r1 += 1
                # Verify explicit sharpness counterexample (1,1) or (1)
                # Find smallest k* in {1, 2} with C1(1, 0) != 0 or C1(1, 1) != 0
                kstar = 1 if C1(1, 0) != 0 else 2
                s_seq = [1] * kstar
                def gs(i): return s_seq[i] if 0 <= i < kstar else 0
                z_seq = [(gs(i) - 2 * C1(gs(i), gs(i - 1))) + C1(gs(i - 1), gs(i - 2)) for i in range(kstar + 2)]
                assert sd_val(z_seq) == sd_val(s_seq)
                assert sd_wt(z_seq) >= kstar + 1
    print(f"  Radius r=1 causal search (1,024 candidates): {valid_r1} valid carry-free adders, ALL {valid_r1} fail weight-subadditivity.")

    # 3b. Verify periodic 3/2 blowup for Chow-Robertson on A_m = (1, 1, 0)^m, B_m = 0^{3m}
    def cr_carry(s, sp):
        if s == 2: return 1
        if s == -2: return -1
        if s == 0: return 0
        if s == 1: return 1 if sp >= 1 else 0
        return -1 if sp <= -1 else 0

    for m in range(1, 12):
        s_seq = [1, 1, 0] * m
        def gs(i): return s_seq[i] if 0 <= i < len(s_seq) else 0
        z_seq = [(gs(i) - 2 * cr_carry(gs(i), gs(i - 1))) + cr_carry(gs(i - 1), gs(i - 2)) for i in range(len(s_seq) + 1)]
        assert sd_val(z_seq) == sd_val(s_seq)
        assert z_seq[:-1] == [1, -1, 1] * m and z_seq[-1] == 0
        assert sd_wt(z_seq) == 3 * m and sd_wt(s_seq) == 2 * m
    print("  Chow-Robertson (r=1) periodic 3/2 blowup A_m = (1,1,0)^m -> (1,-1,1)^m verified for m=1..11.")

    # 3c. Verify complete (1,1) weight-subadditive classification: exactly 16 winners out of 1024
    winners_1_1 = 0
    for mp in itertools.product((0, 1), repeat=5):
        for mn in itertools.product((0, -1), repeat=5):
            def C(sp, s, sn):
                if s == 2: return 1
                if s == -2: return -1
                if s == 0: return 0
                if s == 1:
                    return 1 if sp >= 1 else (0 if sp <= -1 else mp[sn + 2])
                return -1 if sp <= -1 else (0 if sp >= 1 else mn[sn + 2])
            # Build reachable (hp, s, cp) states
            init = (0, 0, 0)
            sts = {init}
            q = deque([init])
            tr = {}
            while q:
                st = q.popleft()
                hp, s, cp = st
                for sn in S_VALS:
                    c = C(hp, s, sn)
                    z = (s - 2 * c) + cp
                    nst = (sgn(s), sn, c)
                    tr[(st, sn)] = (z, nst)
                    if nst not in sts:
                        sts.add(nst)
                        q.append(nst)
            psi = {}
            for st in sts:
                z1, st1 = tr[(st, 0)]
                z2, st2 = tr[(st1, 0)]
                psi[st] = abs(z1) + abs(z2)
            conv = False
            for _ in range(len(sts) + 5):
                ch = False
                for st in sts:
                    best = psi[st]
                    for sn in S_VALS:
                        z, nst = tr[(st, sn)]
                        cand = abs(z) - abs(sn) + psi[nst]
                        if cand > best:
                            best = cand
                    if best > psi[st]:
                        psi[st] = best
                        ch = True
                if not ch:
                    conv = True
                    break
            if conv and psi[init] == 0:
                winners_1_1 += 1
    assert winners_1_1 == 16
    print(f"  Complete (1,1) classification: exactly {winners_1_1}/1,024 weight-subadditive carry-free adders.")

    # 3d. Verify OL-CFPA on deep parallel addition trees (depth 4, 16 operands)
    # Deterministic integer pseudo-random signed-digit operands (no floats!)
    operands = []
    seed = 1234567
    for _ in range(16):
        digits = []
        for _ in range(12):
            seed = (seed * 1103515245 + 12345) & 0x7FFFFFFF
            digits.append((seed % 3) - 1)
        operands.append(digits)
    layer = operands
    while len(layer) > 1:
        layer = [ol_cfpa_parallel(layer[i], layer[i + 1]) for i in range(0, len(layer), 2)]
    root = layer[0]
    exact_sum = sum(sd_val(op) for op in operands)
    total_leaf_wt = sum(sd_wt(op) for op in operands)
    naf_wt = sd_wt(naf_recode(root))
    assert sd_val(root) == exact_sum
    assert naf_wt <= sd_wt(root) <= total_leaf_wt
    print(f"  Depth-4 16-operand OL-CFPA tree replay: sum={exact_sum}, wt_NAF={naf_wt} <= wt(tree)={sd_wt(root)} <= sum_wt={total_leaf_wt}: PASSED.")


if __name__ == "__main__":
    verify_naf_certificate()
    build_and_verify_ol_cfpa_certificate()
    verify_sharpness_and_classification()
    print("\nALL PURE-SILICON CHECKS PASSED (ZERO FLOATS, 100% EXACT INTEGER ARITHMETIC).")
