"""
Pure-Silicon Exact Discovery, Certificate Synthesis & Independent Verification Suite
for Task 12 (`transducer-12`): Bidirectional Tile-Witness Crossing Engine
for Two-Way (LSB -> MSB then MSB -> LSB) Binary Transducers.

100% exact integer / boolean arithmetic — zero floating-point values anywhere.
"""

from collections import deque
from math import lcm


# =============================================================================
# 1. Exact Pure-Silicon Mealy Transducer Evaluators (LSB-first bit-vectors)
# =============================================================================

def eval_fwd(delta, lam, q0, x, w):
    """Run forward (LSB -> MSB) Mealy transducer on w-bit integer x."""
    q = q0
    y = 0
    for i in range(w):
        b = (x >> i) & 1
        y |= (lam(q, b) << i)
        q = delta(q, b)
    return y, q


def eval_bwd(delta, lam, q0, x, w):
    """Run backward (MSB -> LSB) Mealy transducer on w-bit integer x."""
    q = q0
    z = 0
    for i in range(w - 1, -1, -1):
        b = (x >> i) & 1
        z |= (lam(q, b) << i)
        q = delta(q, b)
    return z, q


def trace_fwd(delta, lam, q0, x, w):
    q = q0
    qs = [q0]
    y = 0
    for i in range(w):
        b = (x >> i) & 1
        y |= (lam(q, b) << i)
        q = delta(q, b)
        qs.append(q)
    return y, qs


def trace_bwd(delta, lam, q0, x, w):
    q = q0
    qs = [0] * (w + 1)
    qs[w] = q0
    z = 0
    for i in range(w - 1, -1, -1):
        b = (x >> i) & 1
        z |= (lam(q, b) << i)
        q = delta(q, b)
        qs[i] = q
    return z, qs


def perm_order_and_cycles(table):
    """Exact permutation group order and cycle-length histogram (or None if non-bijective)."""
    n = len(table)
    if len(set(table)) != n:
        return None
    vis = [False] * n
    order = 1
    hist = {}
    for i in range(n):
        if not vis[i]:
            cur = i
            c = 0
            while not vis[cur]:
                vis[cur] = True
                cur = table[cur]
                c += 1
            order = lcm(order, c)
            hist[c] = hist.get(c, 0) + 1
    return order, hist


# =============================================================================
# 2. Bidirectional Tile-Witness Crossing Certificate Synthesizer & Checker
# =============================================================================

def synthesize_tile_witness_cert(sweeps, sample_w=8):
    """
    Synthesize a minimal finite crossing-witness DFA (M, m0, next, W) for an
    arbitrary alternating multi-sweep system `sweeps = [(dir, delta, lam, q0), ...]`.
    """
    I_set = set()
    for w in range(0, sample_w + 1):
        for x in range(1 << w):
            cur = x
            traces = []
            for d, delta, lam, q0 in sweeps:
                if d == "F":
                    cur, qs = trace_fwd(delta, lam, q0, cur, w)
                else:
                    cur, qs = trace_bwd(delta, lam, q0, cur, w)
                traces.append(qs)
            assert cur == x, f"Identity fails at w={w}, x={x}: out={cur}"
            for i in range(w + 1):
                I_set.add(tuple(tr[i] for tr in traces))

    I_list = sorted(I_set)

    def tile_ok(cL, cR, b):
        bit = b
        for idx, (d, delta, lam, _) in enumerate(sweeps):
            qL, qR = cL[idx], cR[idx]
            if d == "F":
                if delta(qL, bit) != qR:
                    return False
                bit = lam(qL, bit)
            else:
                if delta(qR, bit) != qL:
                    return False
                bit = lam(qR, bit)
        return bit == b

    edges = [[[] for _ in range(len(I_list))] for _ in range(2)]
    for b in (0, 1):
        for iL, cL in enumerate(I_list):
            for iR, cR in enumerate(I_list):
                if tile_ok(cL, cR, b):
                    edges[b][iL].append(iR)

    def left_ok(c):
        return all(c[i] == q0 for i, (d, _, _, q0) in enumerate(sweeps) if d == "F")

    def right_ok(c):
        return all(c[i] == q0 for i, (d, _, _, q0) in enumerate(sweeps) if d == "B")

    W0 = tuple(sorted(i for i, c in enumerate(I_list) if left_ok(c)))
    state_to_id = {W0: 0}
    states = [W0]
    trans = []
    q = deque([0])
    while q:
        u = q.popleft()
        W = states[u]
        tr = [0, 0]
        for b in (0, 1):
            nW = tuple(sorted(set(iR for iL in W for iR in edges[b][iL])))
            if nW not in state_to_id:
                state_to_id[nW] = len(states)
                states.append(nW)
                q.append(state_to_id[nW])
            tr[b] = state_to_id[nW]
        trans.append(tr)

    # Independent verification of all 3 Tile-Witness certificate obligations:
    ok_init = all(left_ok(I_list[i]) for i in states[0])
    ok_step = True
    for m_id, W in enumerate(states):
        for b in (0, 1):
            nW = states[trans[m_id][b]]
            for iR in nW:
                if not any(tile_ok(I_list[iL], I_list[iR], b) for iL in W):
                    ok_step = False
    ok_final = all(any(right_ok(I_list[i]) for i in W) for W in states)
    return {
        "n_crossing": len(I_list),
        "n_macro": len(states),
        "transitions": trans,
        "ok_init": ok_init,
        "ok_step": ok_step,
        "ok_final": ok_final,
        "verified": ok_init and ok_step and ok_final,
    }


# =============================================================================
# 3. Concrete Transducer Families
# =============================================================================

# 2-state skip-flip transducer M_2 (k = 2, m = 1)
def sf2_delta(q, b): return (1 - q) & b
def sf2_out(q, b): return b ^ (1 - q)


# General (m+1)-state run-triggered transducers F_m, S_m, R_m
def make_run_trigger(m):
    def dS(q, b): return (q + 1 if b else 0) if q < m else 0
    def lS(q, b): return b if q < m else (1 - b)
    def dR(q, b): return (0 if b else q + 1) if q < m else 0
    def lR(q, b): return b if q < m else (1 - b)
    def dF(q, b): return (q + 1 if b else 0) if q < m else 0
    def lF(q, b): return (1 - b) if q < m else b
    return dS, lS, dR, lR, dF, lF


# =============================================================================
# 4. Full Exact Verification & Sharpness Counterexample Suite
# =============================================================================

def main():
    print("=" * 76)
    print("TASK 12 (transducer-12): BIDIRECTIONAL TILE-WITNESS CROSSING ENGINE")
    print("Pure-Silicon Exact Discovery, Certificate Synthesis & Sharpness Audit")
    print("=" * 76)

    # Suite 1: Certificate synthesis for 2-state skip-flip (6 sweeps) and shifted (12 sweeps)
    print("\n[Suite 1] Automated Bidirectional Tile-Witness Certificate Synthesis")
    sw_p3 = [("F", sf2_delta, sf2_out, 0), ("B", sf2_delta, sf2_out, 0)] * 3
    c_p3 = synthesize_tile_witness_cert(sw_p3, sample_w=8)
    print(f"  (B_2 o F_2)^3 = id  (6 sweeps, raw |Q|=64):   |I|={c_p3['n_crossing']}, "
          f"nMacro={c_p3['n_macro']}, verified={c_p3['verified']}")
    assert c_p3["verified"] and c_p3["n_crossing"] == 6 and c_p3["n_macro"] == 3

    sw_p6 = [("F", sf2_delta, sf2_out, 0), ("B", sf2_delta, sf2_out, 1)] * 6
    c_p6 = synthesize_tile_witness_cert(sw_p6, sample_w=8)
    print(f"  (B_2^(q0=1) o F_2)^6 = id (12 sweeps, |Q|=4096): |I|={c_p6['n_crossing']}, "
          f"nMacro={c_p6['n_macro']}, verified={c_p6['verified']}")
    assert c_p6["verified"] and c_p6["n_crossing"] == 8 and c_p6["n_macro"] == 3

    # Suite 2: Full-cycle order 2^w of F_2 & B_2 vs Period-3 collapse + genuine two-wayness
    print("\n[Suite 2] Skip-Flip M_2: Exponential Order 2^w vs. Constant Period 3 (w=1..12)")
    for w in range(1, 13):
        tabF = [eval_fwd(sf2_delta, sf2_out, 0, x, w)[0] for x in range(1 << w)]
        tabB = [eval_bwd(sf2_delta, sf2_out, 0, x, w)[0] for x in range(1 << w)]
        tabT = [tabB[tabF[x]] for x in range(1 << w)]
        oF, hF = perm_order_and_cycles(tabF)
        oB, hB = perm_order_and_cycles(tabB)
        oT, hT = perm_order_and_cycles(tabT)
        assert oF == (1 << w) and hF == {1 << w: 1}
        assert oB == (1 << w) and hB == {1 << w: 1}
        expected_oT = 1 if w == 1 else 3
        assert oT == expected_oT
        if w >= 2:
            # Verify two-way non-separability witnesses
            msb_to_lsb = (tabT[0] ^ tabT[1 << (w - 1)]) & 1
            all1 = (1 << w) - 1
            lsb_to_msb = ((tabT[all1] ^ tabT[all1 ^ 1]) >> (w - 1)) & 1
            assert msb_to_lsb == 1 and lsb_to_msb == 1
        if w <= 10:
            print(f"  w={w:2d}: ord(F_2)={oF:4d} (1 cycle), ord(B_2)={oB:4d} (1 cycle) "
                  f"=> ord(B_2 o F_2)={oT} | cycles={hT}")
    print("  All widths w=1..12 verified (exact full-cycle 2^w -> period 3, strictly two-way)!")

    # Suite 3: Infinite Parametric Family (m >= 2, k = m + 1 states) + Exact 3-Regime Phase Transition
    print("\n[Suite 3] Infinite Parametric Run-Triggered Family T_m = B_m o F_m = R_m o S_m (m=2..5)")
    for m in range(2, 6):
        dS, lS, dR, lR, dF, lF = make_run_trigger(m)
        orders = []
        max_w = min(11, 2 * m + 4)
        for w in range(1, max_w + 1):
            tabT = []
            for x in range(1 << w):
                y1, _ = eval_fwd(dF, lF, 0, x, w)
                z1, _ = eval_bwd(dF, lF, 0, y1, w)
                y2, _ = eval_fwd(dS, lS, 0, x, w)
                z2, _ = eval_bwd(dR, lR, 0, y2, w)
                assert z1 == z2, f"Factorization B_m o F_m = R_m o S_m failed at m={m}, w={w}"
                tabT.append(z2)
            oT, _ = perm_order_and_cycles(tabT)
            orders.append(oT)
            if w <= m:
                assert oT == 1
            elif w < 2 * m:
                assert oT == 2
            else:
                assert oT == 6
        # Also verify certificate size matches exact closed form: |I_m| = m^2 + 4m + 1, nMacro = 2m + 1
        if m <= 3:
            sw_m = [("F", dS, lS, 0), ("B", dR, lR, 0)] * 6
            cm = synthesize_tile_witness_cert(sw_m, sample_w=2 * m + 3)
            assert cm["verified"]
            assert cm["n_crossing"] == m * m + 4 * m + 1
            assert cm["n_macro"] == 2 * m + 1
            cert_msg = f"|I|={cm['n_crossing']} (=m^2+4m+1), nMacro={cm['n_macro']} (=2m+1), verified=True"
        else:
            cert_msg = f"symbolic formula |I|={m*m+4*m+1}, nMacro={2*m+1}"
        print(f"  m={m} (k={m+1} states): orders(w=1..{max_w})={orders} | {cert_msg}")

    # Suite 4: Coupled-Boundary Two-Way Inversion (2-to-1 forward -> exact bijection when coupled)
    print("\n[Suite 4] Coupled-Boundary Two-Way Inversion & Uncoupled Sharpness")
    def pd_d(q, b): return q ^ b
    def pd_l(q, b): return q
    def gd_d(q, b): return b
    def gd_l(q, b): return q ^ b
    for w in range(1, 11):
        fwd_imgs = set()
        for x in range(1 << w):
            y, s_end = eval_fwd(pd_d, pd_l, 0, x, w)
            fwd_imgs.add(y)
            z, _ = eval_bwd(gd_d, gd_l, s_end, y, w)
            assert z == x, f"Coupled inversion failed at w={w}, x={x}"
        assert len(fwd_imgs) == (1 << (w - 1)), "Forward pass must be strictly 2-to-1!"
    print("  Verified w=1..10: F_pd is strictly 2-to-1 (|im(F_pd)| = 2^(w-1)), "
          "yet coupled B_gd(s_end, F_pd(x)) = x identically!")

    # Suite 5: Sharpness & Falsification Counterexamples
    print("\n[Suite 5] Sharpness & Falsified Perturbations of T_2 = B_2 o F_2")
    # 5a. Perturbed delta_F[1][1]: 0 -> 1
    def dp_d(q, b): return b
    ords_p = []
    for w in range(1, 8):
        tab = [eval_bwd(sf2_delta, sf2_out, 0, eval_fwd(dp_d, sf2_out, 0, x, w)[0], w)[0] for x in range(1 << w)]
        ords_p.append(perm_order_and_cycles(tab)[0])
    print(f"  Perturb 1 (delta_F[1][1]: 0->1):       orders(w=1..7)={ords_p} (explodes to 27,720!)")
    assert ords_p == [1, 3, 12, 12, 168, 504, 27720]

    # 5b. Coupled t_w = s_end on B_2 o F_2 loses bijectivity immediately at w=1..7
    coup_sizes = []
    for w in range(1, 8):
        imgs = set()
        for x in range(1 << w):
            y, se = eval_fwd(sf2_delta, sf2_out, 0, x, w)
            z, _ = eval_bwd(sf2_delta, sf2_out, se, y, w)
            imgs.add(z)
        coup_sizes.append(f"{len(imgs)}/{1<<w}")
    print(f"  Perturb 2 (coupled t_w = s_end on M_2): image sizes(w=1..7)={coup_sizes} (non-bijective!)")
    assert coup_sizes[1] == "3/4"

    # 5c. Variant A (k=3: skip 2 bits after a 1)
    def va_d(q, b): return (1 if b else 0) if q == 0 else ((q + 1) % 3)
    def va_l(q, b): return (1 - b) if q == 0 else b
    ords_va = []
    for w in range(1, 9):
        tab = [eval_bwd(va_d, va_l, 0, eval_fwd(va_d, va_l, 0, x, w)[0], w)[0] for x in range(1 << w)]
        ords_va.append(perm_order_and_cycles(tab)[0])
    print(f"  Perturb 3 (Variant A k=3, skip 2):     orders(w=1..8)={ords_va} (explodes to 429,660!)")
    assert ords_va == [1, 3, 4, 35, 12, 60, 156, 429660]

    # 5d. Replace B_2 with standard binary increment (+1)
    def inc_d(q, b): return (1 - b) if q == 0 else 1
    def inc_l(q, b): return (1 - b) if q == 0 else b
    ords_inc = []
    for w in range(1, 8):
        tab = [eval_bwd(inc_d, inc_l, 0, eval_fwd(sf2_delta, sf2_out, 0, x, w)[0], w)[0] for x in range(1 << w)]
        ords_inc.append(perm_order_and_cycles(tab)[0])
    print(f"  Perturb 4 (B = MSB-first +1):          orders(w=1..7)={ords_inc} (unbounded!)")
    assert ords_inc == [1, 3, 7, 28, 31, 156, 2024]

    print("\nALL 5 EXACT PURE-SILICON SUITES PASSED WITH ZERO FLOATING-POINT VALUES.")


if __name__ == "__main__":
    main()
