"""
Exact Pure-Silicon Exploration, Certificate Synthesis, Independent Replay,
and Sharpness Counterexample Verification for:
  - Bit-Sliced Radix-b Carry-Echo Abelian Sandpile E_{b, w}  (b >= 2, w >= 1)
  - Pure Directed Radix-b Carry Sandpile D_{b, w}            (b >= 2, w >= 1)

Strict pure-silicon arithmetic: Python arbitrary-precision `int` ONLY (zero floats).
"""

from itertools import product


def repunit(b: int, k: int) -> int:
    """Exact repunit R_{b, k} = sum_{j=0}^{k-1} b^j = (b^k - 1) // (b - 1)."""
    val = 0
    for _ in range(k):
        val = val * b + 1
    return val


def stabilize_general(cfg, tau, A, order="asc"):
    """
    Exact deterministic stabilization for an Abelian toppling system (tau, A).
    Returns (stable_cfg, odometer_vec).
    """
    w = len(cfg)
    c = list(cfg)
    f = [0] * w
    indices = list(range(w)) if order == "asc" else list(range(w - 1, -1, -1))
    while True:
        fired = False
        for i in indices:
            if c[i] >= tau[i]:
                k = c[i] // tau[i]
                c[i] -= k * tau[i]
                f[i] += k
                for j in range(w):
                    if A[i][j]:
                        c[j] += k * A[i][j]
                fired = True
        if not fired:
            break
    return tuple(c), tuple(f)


def carry_echo_kernel(b: int, w: int):
    tau = [b + 1] * w
    A = [[0] * w for _ in range(w)]
    for i in range(w):
        if i + 1 < w:
            A[i][i + 1] = 1
        if i > 0:
            A[i][i - 1] = b
    return tau, A


def directed_carry_kernel(b: int, w: int):
    tau = [b] * w
    A = [[0] * w for _ in range(w)]
    for i in range(w):
        if i + 1 < w:
            A[i][i + 1] = 1
    return tau, A


def skew_weight(b: int, cfg) -> int:
    """H_b(c) = sum_{i=0}^{w-1} c_i * R_{b, i+1}."""
    return sum(cfg[i] * repunit(b, i + 1) for i in range(len(cfg)))


def first_moment(cfg) -> int:
    """M_1(c) = sum_{i=0}^{w-1} (i + 1) * c_i."""
    return sum((i + 1) * cfg[i] for i in range(len(cfg)))


def psi_potential(b: int, cfg) -> int:
    """Psi_{b, w}(c) = sum_{i=0}^{w-1} c_i * ((i+1)*R_{b,w+1} - (w+1)*R_{b,i+1})."""
    w = len(cfg)
    M = repunit(b, w + 1)
    return sum(cfg[i] * ((i + 1) * M - (w + 1) * repunit(b, i + 1)) for i in range(w))


def base_value(b: int, cfg) -> int:
    """Phi_b(c) = sum_{i=0}^{w-1} c_i * b^i."""
    return sum(cfg[i] * (b ** i) for i in range(len(cfg)))


def is_dual_skew(b: int, cfg) -> bool:
    """c in {0..b}^w and (i < j and c_j == 0 => c_i == b)."""
    w = len(cfg)
    if any(x < 0 or x > b for x in cfg):
        return False
    for j in range(w):
        if cfg[j] == 0:
            for i in range(j):
                if cfg[i] != b:
                    return False
    return True


def skew_encode(b: int, w: int, n: int):
    """Constructive greedy canonical skew-base-b encoder for 0 <= n < R_{b, w+1}."""
    M = repunit(b, w + 1)
    assert 0 <= n < M
    d = [0] * w
    rem = n
    for i in range(w - 1, -1, -1):
        r = repunit(b, i + 1)
        q = rem // r
        d[i] = q
        rem -= q * r
        if q == b:
            assert rem == 0
            break
    assert rem == 0
    return tuple(d)


def predicted_identity(b: int, w: int):
    """e_{b, w}(i) = b - skew_encode(b, w, H_b(mu_w) mod R_{b, w+1})(i)."""
    M = repunit(b, w + 1)
    H_mu = skew_weight(b, (b,) * w)
    dual = skew_encode(b, w, H_mu % M)
    return tuple(b - x for x in dual)


def verify_carry_echo_exhaustive():
    print("=== 1. Exhaustive Verification of Carry-Echo E_{b, w} ===")
    cases = [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3)]
    for b, w in cases:
        tau, A = carry_echo_kernel(b, w)
        M = repunit(b, w + 1)
        mu = (b,) * w
        beta = (b + 1,) if w == 1 else (1,) + (0,) * (w - 2) + (b,)

        # BFS closure from mu under adding 1 at any bit position (ground-truth recurrent set)
        rec = {mu}
        queue = [mu]
        while queue:
            cur = queue.pop()
            for i in range(w):
                nxt = list(cur)
                nxt[i] += 1
                s_asc, f_asc = stabilize_general(nxt, tau, A, "asc")
                s_desc, f_desc = stabilize_general(nxt, tau, A, "desc")
                # Confluence & odometer uniqueness check
                assert s_asc == s_desc and f_asc == f_desc
                # Exact conservation laws check
                assert skew_weight(b, nxt) == skew_weight(b, s_asc) + M * f_asc[w - 1]
                assert first_moment(nxt) == first_moment(s_asc) + (b - 1) * sum(f_asc) + (w + 1) * f_asc[w - 1]
                assert (b ** (w + 1) - 1) * sum(f_asc) + psi_potential(b, s_asc) == psi_potential(b, nxt)
                if w >= 2:
                    assert base_value(b, nxt) == base_value(b, s_asc) + f_asc[0] + (b ** w) * f_asc[w - 1]
                    assert sum(nxt) == sum(s_asc) + b * f_asc[0] + f_asc[w - 1]
                if s_asc not in rec:
                    rec.add(s_asc)
                    queue.append(s_asc)

        # Check exact count |R| == R_{b, w+1}
        assert len(rec) == M, f"Count mismatch for b={b}, w={w}: {len(rec)} != {M}"

        # Check exact duality: c in R <=> is_dual_skew(b, c) <=> burning test passes
        all_stable = list(product(range(b + 1), repeat=w))
        dual_skew_set = {c for c in all_stable if is_dual_skew(b, c)}
        burn_set = {
            c for c in all_stable
            if stabilize_general([c[i] + beta[i] for i in range(w)], tau, A) == (c, (1,) * w)
        }
        assert rec == dual_skew_set == burn_set

        # Check predicted closed-form identity element e_{b, w}
        e = predicted_identity(b, w)
        assert e in rec
        # Verify e is the identity on EVERY recurrent element!
        for c in rec:
            ce, _ = stabilize_general([c[i] + e[i] for i in range(w)], tau, A)
            assert ce == c
        # Verify exact self-addition avalanche laws for w >= 2
        e2, f2 = stabilize_general([2 * x for x in e], tau, A)
        assert e2 == e
        if w >= 2:
            assert skew_weight(b, e) == M
            assert f2[w - 1] == 1
            assert (b - 1) * sum(f2) == first_moment(e) - (w + 1)
            assert sum(e) == b * f2[0] + 1
            assert base_value(b, e) == b ** w + f2[0]
        else:
            assert e == (0,) and skew_weight(b, e) == 0 and f2 == (0,)

        print(f"  [PASS] b={b}, w={w}: |R|={M:4d}, e={list(e)}, f(2e->e)={list(f2)}, H(e)={skew_weight(b, e)}")


def verify_large_widths():
    print("\n=== 2. Large-Width Exact Identity & Avalanche Replay (up to w=40) ===")
    for b in [2, 3, 4, 8]:
        for w in [10, 20, 32, 40]:
            if b > 2 and w > 24:
                continue
            tau, A = carry_echo_kernel(b, w)
            M = repunit(b, w + 1)
            e = predicted_identity(b, w)
            assert is_dual_skew(b, e)
            e2, f2 = stabilize_general([2 * x for x in e], tau, A)
            assert e2 == e
            assert skew_weight(b, e) == M
            assert f2[w - 1] == 1
            assert (b - 1) * sum(f2) == first_moment(e) - (w + 1)
            assert sum(e) == b * f2[0] + 1
            assert base_value(b, e) == b ** w + f2[0]
            # Also verify burning witness on e
            beta = (1,) + (0,) * (w - 2) + (b,)
            eb, fb = stabilize_general([e[i] + beta[i] for i in range(w)], tau, A)
            assert eb == e and fb == (1,) * w
            print(f"  [PASS] b={b}, w={w:2d}: H(e)=R_{{b,w+1}} ({M.bit_length()} bits), sum(f2)={sum(f2)}, f2[0]={f2[0]}, f2[w-1]={f2[w-1]}")


def verify_directed_carry():
    print("\n=== 3. Second Family Reusability Check: Directed Carry D_{b, w} ===")
    for b, w in [(2, 1), (2, 2), (2, 3), (2, 4), (3, 3), (4, 3)]:
        tau, A = directed_carry_kernel(b, w)
        mu = (b - 1,) * w
        beta = (b,) + (b - 1,) * (w - 1)
        all_stable = list(product(range(b), repeat=w))
        assert len(all_stable) == b ** w
        for c in all_stable:
            cb, fb = stabilize_general([c[i] + beta[i] for i in range(w)], tau, A)
            assert cb == c and fb == (1,) * w
            # Test Legendre/Kummer energy law on c + mu
            inp = [c[i] + mu[i] for i in range(w)]
            s, f = stabilize_general(inp, tau, A)
            assert base_value(b, inp) == base_value(b, s) + (b ** w) * f[w - 1]
            assert sum(inp) == sum(s) + (b - 1) * sum(f) + f[w - 1]
        print(f"  [PASS] D_{{{b},{w}}}: |R|={b**w}, identity=0, Kummer conservation verified on all {b**w} states")


def verify_sharpness_counterexamples():
    print("\n=== 4. Sharpness & Falsification Counterexamples ===")

    # C1: w = 1 boundary breaks H_b(e) = R_{b, w+1} and f_{2e->e}(w-1) = 1
    e1 = predicted_identity(2, 1)
    assert e1 == (0,) and skew_weight(2, e1) == 0 != repunit(2, 2)
    print(f"  [C1] w=1 boundary (b=2): e_1={list(e1)}, H_2(e_1)=0 != R_{{2,2}}=3 (w >= 2 is sharp)")

    # C2: Non-recurrent idempotent 0 at w=2, b=2
    tau, A = carry_echo_kernel(2, 2)
    z = (0, 0)
    z2, _ = stabilize_general([0, 0], tau, A)
    zb, fb = stabilize_general([0 + 1, 0 + 2], tau, A)
    assert z2 == z and fb == (0, 0) != (1, 1)
    print(f"  [C2] Non-recurrent idempotent (b=2, w=2): 0+0->0, but burning odometer={list(fb)} != [1, 1]")

    # C3: Single-bit skew violation c=(1, 0) at w=2, b=2
    c_bad = (1, 0)
    cb, fb_bad = stabilize_general([1 + 1, 0 + 2], tau, A)
    assert not is_dual_skew(2, c_bad) and fb_bad == (0, 0) != (1, 1)
    print(f"  [C3] Single-bit skew violation (b=2, w=2): c=[1, 0] fails burning (odometer={list(fb_bad)})")

    # C4: Cyclic wrap-around (no sink dissipation) -> exact 2-step infinite oscillation
    # On w=2, wrapping 1 up + 2 down mod 2 sends 3 chips to the other site: (3, 0) ->_0 (0, 3) ->_1 (3, 0)
    c_cyc = [3, 0]
    c_cyc[0] -= 3; c_cyc[1] += 3
    assert tuple(c_cyc) == (0, 3)
    c_cyc[1] -= 3; c_cyc[0] += 3
    assert tuple(c_cyc) == (3, 0)
    print("  [C4] Cyclic conservative wrap-around (w=2): (3, 0) ->_0 (0, 3) ->_1 (3, 0) infinite cycle (no StrictPotential)")

    # C5: b = 1 degeneracy (classical symmetric 1D sandpile CB(2; 1, 1)):
    # First-moment M_1(i)=i+1 has zero drop at i=0: 2*1 - 1*2 = 0 (not strictly dissipative)
    drop_b1_i0 = 2 * 1 - 1 * 2
    assert drop_b1_i0 == 0
    print(f"  [C5] b=1 degeneracy (CB(2;1,1)): M_1 drop at i=0 is {drop_b1_i0} (not strictly positive; b >= 2 is sharp)")

    # C6: Non-coprime transfer CB(4; 2, 2) at w=2: group order 2^2 * (2+1) = 12, non-cyclic Z/2 x Z/6!
    tau_nc = [4, 4]
    A_nc = [[0, 2], [2, 0]]
    mu_nc = (3, 3)
    rec_nc = {mu_nc}
    q = [mu_nc]
    while q:
        cur = q.pop()
        for i in range(2):
            nxt = list(cur)
            nxt[i] += 1
            s, _ = stabilize_general(nxt, tau_nc, A_nc)
            if s not in rec_nc:
                rec_nc.add(s)
                q.append(s)
    # Compute max element order in rec_nc
    s2_nc, _ = stabilize_general([2 * x for x in mu_nc], tau_nc, A_nc)
    e_nc, _ = stabilize_general([2 * mu_nc[i] - s2_nc[i] for i in range(2)], tau_nc, A_nc)
    max_ord = 0
    for g in rec_nc:
        cur = g
        k = 1
        while cur != e_nc:
            cur, _ = stabilize_general([cur[i] + g[i] for i in range(2)], tau_nc, A_nc)
            k += 1
        max_ord = max(max_ord, k)
    assert len(rec_nc) == 12 and max_ord == 6 < 12
    print(f"  [C6] Non-coprime CB(4; 2, 2) (w=2): |R|={len(rec_nc)}, max element order={max_ord} < 12 (non-cyclic Z/2 x Z/6)")


if __name__ == "__main__":
    verify_carry_echo_exhaustive()
    verify_large_widths()
    verify_directed_carry()
    verify_sharpness_counterexamples()
    print("\nALL EXACT PURE-SILICON CHECKS PASSED.")
