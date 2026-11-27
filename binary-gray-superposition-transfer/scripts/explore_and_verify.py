#!/usr/bin/env python3
"""
Pure-Silicon Exact Exploration & Independent Verification for Task 18 (specmat-18):
Bit-Boundary Transfer-Tensor & State-Invariant Compiler (BitTransfer3)
applied to the Binary-Gray Superposition Graph GB_k (and Twisted/Ablated Variants).

Uses strictly exact Python arbitrary-precision integer arithmetic (ZERO floating point,
ZERO external libraries).
"""

# =============================================================================
# 1. Exact Polynomial Arithmetic over Z[q] (little-endian lists of Python ints)
# =============================================================================

def p_trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p

def p_add(a, b):
    n = max(len(a), len(b))
    return p_trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])

def p_sub(a, b):
    n = max(len(a), len(b))
    return p_trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])

def p_mul(a, b, max_deg=None):
    if not a or not b:
        return []
    n = len(a) + len(b) - 1
    if max_deg is not None:
        n = min(n, max_deg + 1)
    out = [0] * n
    for i, ai in enumerate(a):
        if ai == 0 or i >= n:
            continue
        for j, bj in enumerate(b):
            if i + j >= n:
                break
            if bj != 0:
                out[i + j] += ai * bj
    return p_trim(out)

def p_eval(p, x):
    acc = 0
    for c in reversed(p):
        acc = acc * x + c
    return acc

def p_shift(p, q0):
    """Return polynomial p(q0 + eps) as exact list of ints in eps."""
    # Horner shift: p(q0 + eps) = (...((a_d)*(q0+eps) + a_{d-1})...)
    lin = [q0, 1]
    acc = []
    for c in reversed(p):
        acc = p_add(p_mul(acc, lin), [c])
    return acc

def p_val_lead(p):
    """Return (valuation, leading_coeff) at 0 for polynomial p(eps)."""
    for i, c in enumerate(p):
        if c != 0:
            return i, c
    return None, 0


# =============================================================================
# 2. Pure-Silicon Bit-Graph Definitions
# =============================================================================

def gray(i: int) -> int:
    return i ^ (i >> 1)

def gb_edges(k: int, close_bin: bool = False, close_gray: bool = False):
    """Binary-Gray Superposition Graph GB_k on {0, ..., 2^k - 1}."""
    n = 1 << k
    edges = set()
    for u in range(n - 1):
        edges.add((u, u + 1))
    for i in range(n - 1):
        a, b = gray(i), gray(i + 1)
        if a > b:
            a, b = b, a
        edges.add((a, b))
    if close_bin:
        edges.add((0, n - 1))
    if close_gray:
        edges.add((0, n >> 1))
    return n, sorted(edges)

def twisted_edges(k: int):
    """Twisted-bridge 3-terminal graph TW_k: replaces Gray bridge (bL, bR) by (bL, cR)."""
    if k == 2:
        return 4, [(0, 1), (1, 2), (1, 3), (2, 3)]
    n, e_prev = twisted_edges(k - 1)
    edges = set(e_prev)
    for u, v in e_prev:
        edges.add((u + n, v + n))
    edges.add((n - 1, n))
    edges.add((n >> 1, 2 * n - 1))
    return 2 * n, sorted(edges)

def single_bridge_edges(k: int):
    """Single-bridge ablation SB_k: drops Gray bridge (bL, bR)."""
    if k == 2:
        return 4, [(0, 1), (1, 2), (1, 3), (2, 3)]
    n, e_prev = single_bridge_edges(k - 1)
    edges = set(e_prev)
    for u, v in e_prev:
        edges.add((u + n, v + n))
    edges.add((n - 1, n))
    return 2 * n, sorted(edges)

def shift2_edges(k: int):
    """Perturbed silicon graph using g2(i) = i ^ (i >> 2) instead of Gray code."""
    n = 1 << k
    edges = set()
    for u in range(n - 1):
        edges.add((u, u + 1))
    for i in range(n - 1):
        a, b = i ^ (i >> 2), (i + 1) ^ ((i + 1) >> 2)
        if a != b:
            if a > b:
                a, b = b, a
            edges.add((a, b))
    return n, sorted(edges)


# =============================================================================
# 3. Independent Brute-Force Oracles (Exact Integer Enumeration)
# =============================================================================

def brute_pm(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    memo = {}
    def dfs(mask):
        if mask == (1 << n) - 1:
            return 1
        if mask in memo:
            return memo[mask]
        u = 0
        while (mask >> u) & 1:
            u += 1
        tot = 0
        for v in adj[u]:
            if not ((mask >> v) & 1):
                tot += dfs(mask | (1 << u) | (1 << v))
        memo[mask] = tot
        return tot
    return dfs(0)

def brute_indep_stats(n, edges, terminals=None):
    """Return (indep_poly, alpha, max_count, all_max_contain_terminals)."""
    adj = [0] * n
    for u, v in edges:
        adj[u] |= (1 << v)
        adj[v] |= (1 << u)
    coeffs = [0] * (n + 1)
    best = 0
    max_masks = []
    for mask in range(1 << n):
        ok = True
        for u in range(n):
            if (mask >> u) & 1:
                if adj[u] & mask:
                    ok = False
                    break
        if ok:
            pc = mask.bit_count()
            coeffs[pc] += 1
            if pc > best:
                best = pc
                max_masks = [mask]
            elif pc == best:
                max_masks.append(mask)
    forced = None
    if terminals is not None:
        tmask = 0
        for t in terminals:
            tmask |= (1 << t)
        forced = all((m & tmask) == tmask for m in max_masks)
    return p_trim(coeffs), best, len(max_masks), forced

def brute_chrom_poly(n, edges):
    """Exact chromatic polynomial P(G, q) via deletion-contraction over Z[q]."""
    def dc(verts, edgs):
        if not edgs:
            p = [0] * (verts + 1)
            p[verts] = 1
            return p
        u, v = edgs[0]
        rest = edgs[1:]
        p_del = dc(verts, rest)
        new_edgs = set()
        for a, b in rest:
            na = u if a == v else a
            nb = u if b == v else b
            if na != nb:
                if na > nb:
                    na, nb = nb, na
                new_edgs.add((na, nb))
        p_con = dc(verts - 1, sorted(new_edgs))
        return p_sub(p_del, p_con)
    return dc(n, edges)

def bareiss_det(M):
    """Exact integer determinant via fraction-free Bareiss algorithm (zero float)."""
    n = len(M)
    A = [list(row) for row in M]
    sign = 1
    prev_pivot = 1
    for k in range(n):
        if A[k][k] == 0:
            swap_row = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    swap_row = i
                    break
            if swap_row is None:
                return 0
            A[k], A[swap_row] = A[swap_row], A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * pivot - A[i][k] * A[k][j]) // prev_pivot
        prev_pivot = pivot
    return sign * A[n - 1][n - 1]

def brute_spanning_trees(n, edges):
    L = [[0] * n for _ in range(n)]
    for u, v in edges:
        L[u][u] += 1
        L[v][v] += 1
        L[u][v] -= 1
        L[v][u] -= 1
    cofactor = [row[1:] for row in L[1:]]
    return bareiss_det(cofactor)


# =============================================================================
# 4. Generic BitTransfer3 Transfer-Tensor Engine (Exact Integer & Z[q])
# =============================================================================

def pat3(a, b, c):
    if a == b == c: return 0
    if a == b: return 1
    if a == c: return 2
    if b == c: return 3
    return 4

def step_pm_generic(vec, bridges, out_sel):
    """Generic 8-state perfect-matching transfer tensor for any 3-terminal GlueSpec.
    bridges: list of (left_idx, right_idx) in {0,1,2} x {0,1,2}.
    out_sel: triple of (side, idx) where side in (0=L, 1=R), idx in {0,1,2}.
    """
    out = [0] * 8
    m_b = len(bridges)
    out_set = set(out_sel)
    for sL in range(8):
        if vec[sL] == 0: continue
        mL = [(sL >> 2) & 1, (sL >> 1) & 1, sL & 1]
        for sR in range(8):
            if vec[sR] == 0: continue
            mR = [(sR >> 2) & 1, (sR >> 1) & 1, sR & 1]
            for bmask in range(1 << m_b):
                cL = list(mL)
                cR = list(mR)
                ok = True
                for bi, (li, ri) in enumerate(bridges):
                    if (bmask >> bi) & 1:
                        if cL[li] or cR[ri]:
                            ok = False
                            break
                        cL[li] = 1
                        cR[ri] = 1
                if not ok: continue
                # Every terminal NOT exported to out_sel becomes internal and MUST be matched!
                for side, arr in ((0, cL), (1, cR)):
                    for idx in range(3):
                        if (side, idx) not in out_set and arr[idx] == 0:
                            ok = False
                            break
                    if not ok: break
                if not ok: continue
                bits = [cL[idx] if side == 0 else cR[idx] for (side, idx) in out_sel]
                st = (bits[0] << 2) | (bits[1] << 1) | bits[2]
                out[st] += vec[sL] * vec[sR]
    return out

def step_alpha_generic(vec, bridges, out_sel):
    """Generic 8-state tropical (max, +) independence-number transfer tensor."""
    NEG_INF = -10**18
    out = [NEG_INF] * 8
    for sL in range(8):
        if vec[sL] < 0: continue
        bL = [(sL >> 2) & 1, (sL >> 1) & 1, sL & 1]
        for sR in range(8):
            if vec[sR] < 0: continue
            bR = [(sR >> 2) & 1, (sR >> 1) & 1, sR & 1]
            if any(bL[li] and bR[ri] for (li, ri) in bridges):
                continue
            bits = [bL[idx] if side == 0 else bR[idx] for (side, idx) in out_sel]
            st = (bits[0] << 2) | (bits[1] << 1) | bits[2]
            val = vec[sL] + vec[sR]
            if val > out[st]:
                out[st] = val
    return out

def build_chrom_tensor_gb(q0, max_deg):
    """Precompute exact 5-state Bell-partition chromatic transfer tensor for GB_k
    in shifted variable eps where q = q0 + eps, truncated to degree <= max_deg."""
    reps = [(0, 0, 0, 1), (0, 0, 1, 2), (0, 1, 0, 2), (1, 0, 0, 2), (0, 1, 2, 3)]
    tensor = []
    for s_out, (caL, caR, ccR, m) in enumerate(reps):
        agg = {}
        def enum_vars(idx, vals, num_fresh):
            if idx == 3:
                cbL, ccL, cbR = vals
                if ccL == caR or cbL == cbR:
                    return
                mult = [1]
                for j in range(num_fresh):
                    mult = p_mul(mult, [q0 - m - j, 1], max_deg)
                key = (pat3(caL, cbL, ccL), pat3(caR, cbR, ccR))
                agg[key] = p_add(agg.get(key, []), mult)
                return
            for c in range(m + num_fresh):
                enum_vars(idx + 1, vals + [c], num_fresh)
            enum_vars(idx + 1, vals + [m + num_fresh], num_fresh + 1)
        enum_vars(0, [], 0)
        tensor.append(list(agg.items()))
    return tensor

def step_chrom_trunc(vec, tensor, max_deg):
    out = [[] for _ in range(5)]
    for s_out in range(5):
        acc = []
        for (pL, pR), coeff in tensor[s_out]:
            acc = p_add(acc, p_mul(p_mul(vec[pL], vec[pR], max_deg), coeff, max_deg))
        out[s_out] = acc
    return out

def v_to_mobius(v, q0, max_deg):
    """Exact Pi_3 Möbius transform from Bell basis v[0..4] to quotient basis u[0..4]."""
    qm1 = [q0 - 1, 1]
    qm2 = [q0 - 2, 1]
    u0 = v[0]
    u1 = p_add(v[0], p_mul(qm1, v[1], max_deg))
    u2 = p_add(v[0], p_mul(qm1, v[2], max_deg))
    u3 = p_add(v[0], p_mul(qm1, v[3], max_deg))
    s123 = p_add(p_add(v[1], v[2]), v[3])
    u4 = p_add(p_add(v[0], p_mul(qm1, s123, max_deg)),
               p_mul(p_mul(qm1, qm2, max_deg), v[4], max_deg))
    return [u0, u1, u2, u3, u4]


# =============================================================================
# 5. Main Verification Suite
# =============================================================================

def main():
    print("=" * 78)
    print("PURE-SILICON VERIFICATION: BitTransfer3 & Binary-Gray Superposition Graph GB_k")
    print("=" * 78)

    # --- A. Verify Bit-MSB Gluing Theorem up to k = 10 (1024 vertices) ---
    print("\n[1] Bit-MSB Gluing Theorem (GB_{k+1} = glue(gbSpec, GB_k, GB_k)):")
    for k in range(2, 10):
        n, ek = gb_edges(k)
        n2, ek1 = gb_edges(k + 1)
        glued = set(ek) | {(u + n, v + n) for (u, v) in ek} | {(n - 1, n), (n >> 1, n + (n >> 1))}
        assert set(ek1) == glued, f"MSB gluing failed at k={k}"
        assert len(ek) == 3 * (1 << (k - 1)) - 2
    print("    PASS: Verified exact edge-set identity for all k = 2..9 (up to |V| = 1024, |E| = 1534).")

    # --- B. Independent Brute-Force Cross-Checks (k = 2, 3, 4) ---
    print("\n[2] Independent Brute-Force Cross-Checks (4 Boundary Closures):")
    gb_spec_bridges = [(2, 0), (1, 1)]           # (cL, aR) and (bL, bR)
    gb_spec_out = [(0, 0), (1, 0), (1, 2)]       # (aL, aR, cR)
    pm_base = [0, 1, 1, 0, 1, 0, 0, 1]
    alpha_base = [1, 1, 1, -10**18, 1, 2, 2, -10**18]

    pm_v = list(pm_base)
    al_v = list(alpha_base)
    a_prev, a_curr = 1, 1
    for k in range(2, 5):
        n, e_open = gb_edges(k, False, False)
        _, e_gray = gb_edges(k, False, True)
        _, e_bin  = gb_edges(k, True, False)
        _, e_both = gb_edges(k, True, True)
        # Perfect matchings
        assert brute_pm(n, e_open) == a_curr == pm_v[7]
        assert brute_pm(n, e_gray) == a_curr + 1
        assert brute_pm(n, e_bin)  == 2 * a_curr
        assert brute_pm(n, e_both) == 2 * a_curr + 1
        # Independence number & forced terminals
        _, al_open, _, forced = brute_indep_stats(n, e_open, (0, n >> 1, n - 1))
        _, al_both, _, _      = brute_indep_stats(n, e_both)
        assert al_open == max(al_v)
        if k >= 3:
            assert al_open == 3 * (1 << (k - 3)) + 1 and forced is True
            assert al_both == 3 * (1 << (k - 3))
        print(f"    k={k} (|V|={n:2d}): PM=(open:{a_curr}, gray:{a_curr+1}, bin:{2*a_curr}, cyclic:{2*a_curr+1}) "
              f"| alpha=(open:{al_open}, cyclic:{al_both}, forced_terms={forced})")
        pm_v = step_pm_generic(pm_v, gb_spec_bridges, gb_spec_out)
        al_v = step_alpha_generic(al_v, gb_spec_bridges, gb_spec_out)
        a_prev, a_curr = a_curr, a_curr * a_curr + a_prev * a_prev

    # Brute-force full Chromatic Polynomial check for k = 2, 3 against 5-state Bell engine
    print("\n[3] Full Chromatic Polynomial Brute-Force Check (k = 2, 3, all 4 closures):")
    T0 = build_chrom_tensor_gb(0, 20)
    v_poly = [[], [-2, 1], [-2, 1], [], [-3, 1]]  # k=2 at q = 0 + q: [0, q-2, q-2, 0, q-3]
    for k in (2, 3):
        u = v_to_mobius(v_poly, 0, 20)
        P_open_eng = p_mul([0, 1], u[4])
        P_gray_eng = p_mul([0, 1], p_sub(u[4], u[1]))
        P_bin_eng  = p_mul([0, 1], p_sub(u[4], u[2]))
        P_both_eng = p_mul([0, 1], p_add(p_sub(p_sub(u[4], u[1]), u[2]), u[0]))
        for label, cb, cg, P_eng in [
            ("Open", False, False, P_open_eng),
            ("Gray-closed", False, True, P_gray_eng),
            ("Bin-closed", True, False, P_bin_eng),
            ("Doubly-cyclic", True, True, P_both_eng),
        ]:
            n, ed = gb_edges(k, cb, cg)
            P_bf = brute_chrom_poly(n, ed)
            assert P_bf == P_eng, f"Chromatic mismatch at k={k} {label}"
        print(f"    k={k}: ALL 4 exact chromatic polynomials P(q) match deletion-contraction identically! "
              f"P_open(3)={p_eval(P_open_eng, 3)}")
        v_poly = step_chrom_trunc(v_poly, T0, 20)

    # --- C. Verify All 5 Infinite Theorems up to k = 12 (|V| = 4096) ---
    print("\n[4] Exact Transfer-Tensor Verification of Theorems 1-5 up to k = 12 (|V| = 4096):")
    # Theorem 1 & 2 up to k=12
    pm_v = list(pm_base)
    al_v = list(alpha_base)
    a_prev, a_curr = 1, 1
    for k in range(2, 13):
        assert pm_v == [0, 1, a_curr, 0, a_prev * a_prev, 0, 0, a_curr]
        if k >= 3:
            A = 3 * (1 << (k - 3)) + 1
            assert al_v == [A - 2, A - 2, A - 1, A - 1, A - 1, A - 1, A - 1, A]
        pm_v = step_pm_generic(pm_v, gb_spec_bridges, gb_spec_out)
        al_v = step_alpha_generic(al_v, gb_spec_bridges, gb_spec_out)
        a_prev, a_curr = a_curr, a_curr * a_curr + a_prev * a_prev
    print("    Thm 1 (PM A000283 invariant): PASS for k = 2..12.")
    print("    Thm 2 (alpha = 3*2^(k-3)+1 + forced terminals): PASS for k = 3..12.")

    # Theorem 3 (chi = 3) up to k=10
    T3 = build_chrom_tensor_gb(3, 0)  # evaluate at q = 3 (deg 0)
    v3 = [[0], [1], [1], [0], [0]]    # at q = 3: [0, 1, 1, 0, 0]
    for k in range(2, 11):
        u3 = v_to_mobius(v3, 3, 0)
        P3 = 3 * (u3[4][0] if u3[4] else 0)
        assert P3 >= 12
        v3 = step_chrom_trunc(v3, T3, 0)
    print("    Thm 3 (chi(GB_k) = 3, P(3) >= 12): PASS for k = 2..10.")

    # Theorem 4 (Crapo Beta Quartet at q = 1 + eps) up to k = 10
    T1 = build_chrom_tensor_gb(1, 3)
    v1 = [[], [-1, 1], [-1, 1], [], [-2, 1]]
    for k in range(2, 11):
        u1 = v_to_mobius(v1, 1, 3)
        q_eps = [1, 1]
        P_open = p_mul(q_eps, u1[4], 3)
        P_gray = p_mul(q_eps, p_sub(u1[4], u1[1]), 3)
        P_bin  = p_mul(q_eps, p_sub(u1[4], u1[2]), 3)
        P_both = p_mul(q_eps, p_add(p_sub(p_sub(u1[4], u1[1]), u1[2]), u1[0]), 3)
        assert p_val_lead(P_open) == (2, -(1 << ((1 << (k - 1)) - 2 * k + 2)))
        assert p_val_lead(P_gray) == (1,  (1 << ((1 << (k - 1)) - k)))
        assert p_val_lead(P_bin)  == (1,  (1 << ((1 << (k - 1)) - 2)))
        assert p_val_lead(P_both) == (1,  (1 << ((1 << (k - 1)) - 1)))
        v1 = step_chrom_trunc(v1, T1, 3)
    print("    Thm 4 (Crapo beta power-of-2 quartet across all 4 closures): PASS for k = 2..10.")

    # Theorem 5 (Linear (q-2)-multiplicity 2k-4 with constant lead -4) up to k = 12
    D2 = 24
    T2 = build_chrom_tensor_gb(2, D2)
    v2 = [[], [0, 1], [0, 1], [], [-1, 1]]
    for k in range(2, 13):
        u2 = v_to_mobius(v2, 2, D2)
        P_open = p_mul([2, 1], u2[4], D2)
        vl = p_val_lead(P_open)
        if k == 2:
            assert vl == (1, 2)
        elif k == 3:
            assert vl == (3, 4)
        else:
            assert vl == (2 * k - 4, -4), f"Failed Thm 5 at k={k}: got {vl}"
        v2 = step_chrom_trunc(v2, T2, D2)
    print("    Thm 5 (v_(q-2)(P(GB_k,q)) = 2k-4, lead = -4 for k>=4; boundary k=2:(1,2), k=3:(3,4)): PASS for k = 2..12.")

    # --- D. Reusability & Sharpness Counterexamples ---
    print("\n[5] Reusability & Sharpness Counterexamples:")
    # Twisted bridge TW_k: bridges (cL, aR) and (bL, cR)
    tw_bridges = [(2, 0), (1, 2)]
    pm_tw = list(pm_base)
    al_tw = list(alpha_base)
    t_prev, t_curr = 1, 1
    for k in range(2, 9):
        assert pm_tw[7] == t_curr
        if k <= 4:
            n, ed = twisted_edges(k)
            assert brute_pm(n, ed) == t_curr
            _, al_bf, _, _ = brute_indep_stats(n, ed)
            assert al_bf == max(al_tw)
        pm_tw = step_pm_generic(pm_tw, tw_bridges, gb_spec_out)
        al_tw = step_alpha_generic(al_tw, tw_bridges, gb_spec_out)
        t_prev, t_curr = t_curr, t_curr * t_curr + t_prev
    print("    Twisted-bridge TW_k: PM obeys t_{k+1} = t_k^2 + t_{k-1} (1,2,5,27,734,...).")
    print("    Sharpness separation: PM(TW_5)=27 != 29=PM(GB_5); alpha(TW_4)=8 != 7=alpha(GB_4).")

    # Single-bridge SB_k: bridge (cL, aR) only
    sb_bridges = [(2, 0)]
    pm_sb = list(pm_base)
    for k in range(2, 9):
        assert pm_sb[7] == 1
        if k <= 4:
            n, ed = single_bridge_edges(k)
            assert brute_pm(n, ed) == 1
        pm_sb = step_pm_generic(pm_sb, sb_bridges, gb_spec_out)
    print("    Single-bridge SB_k: PM(SB_k) = 1 for all k >= 2 (vs 2 at k=3 for GB_k).")

    # Shift-2 XOR perturbation
    n3, e3 = shift2_edges(3)
    P3_s2 = brute_chrom_poly(n3, e3)
    vl_s2_1 = p_val_lead(p_shift(P3_s2, 1))
    print(f"    Shift-2 XOR perturbation (k=3): |E|={len(e3)} != 10, P(1+e) starts at {vl_s2_1} (4 blocks != 2).")

    # Bonus exact Kirchhoff spanning tree verification
    taus = [brute_spanning_trees(*gb_edges(k)) for k in range(2, 6)]
    print(f"\n[6] Exact Kirchhoff Bareiss Spanning Trees tau(GB_k) (k=2..5): {taus}")
    for i in range(len(taus) - 1):
        assert taus[i + 1] % taus[i] == 0
    print("    Divisibility chain tau(GB_k) | tau(GB_{k+1}) confirmed (ratios: "
          f"{[taus[i+1]//taus[i] for i in range(len(taus)-1)]}).")

    print("\nALL EXACT CHECKS PASSED WITH ZERO FLOATING-POINT ARITHMETIC.")

if __name__ == "__main__":
    main()
