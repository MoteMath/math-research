"""
Fenwick / Binary-Indexed Low-Bit Transducer Engine:
Exact Pure-Silicon Exploration, Certificate Synthesis, Verification & Sharpness Suite.

Strictly exact Python arbitrary-precision integer arithmetic (ZERO floats anywhere).
"""
from itertools import product

# ==============================================================================
# 1. Primitive Pure-Silicon Low-Bit Jump Operators
# ==============================================================================

def lowbit(x: int) -> int:
    """Lowest set bit of x: 2^{v_2(x)} for x > 0, and 0 for x = 0."""
    return x & -x

def D(x: int) -> int:
    """Fenwick down-jump (interrogation parent): x - (x & -x)."""
    return x - (x & -x)

def U(x: int) -> int:
    """Fenwick up-jump (update parent): x + (x & -x)."""
    return x + (x & -x)

def apply_word(w: str, x: int) -> int:
    """Apply word w in {U, D}* right-to-left: (g_L o ... o g_1)(x)."""
    for ch in reversed(w):
        x = U(x) if ch == 'U' else D(x)
    return x

def dual_word(w: str) -> str:
    """Swap U <-> D in word w."""
    return ''.join('D' if ch == 'U' else 'U' for ch in w)

def ctz(x: int) -> int:
    """Trailing zero count v_2(x) for x > 0."""
    assert x > 0
    return (x & -x).bit_length() - 1

def popcount(x: int) -> int:
    return x.bit_count()


# ==============================================================================
# 2. General Finite-State LSB Mealy Transducer Engine & Moore Minimization
# ==============================================================================

def compose_transducers(T1, T2):
    """Exact product composition (T1 o T2)(x) = T1(T2(x))."""
    init1, tr1 = T1
    init2, tr2 = T2
    init = (init1, init2)
    tr = {}
    queue = [init]
    seen = {init}
    while queue:
        q1, q2 = queue.pop()
        for b in (0, 1):
            q2p, mid = tr2[(q2, b)]
            q1p, out = tr1[(q1, mid)]
            nxt = (q1p, q2p)
            tr[((q1, q2), b)] = (nxt, out)
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return (init, tr)

def minimize_transducer(T):
    """Exact Moore partition refinement minimization."""
    init, tr = T
    states = sorted({q for (q, _) in tr}, key=str)
    part = {q: (tr[(q, 0)][1], tr[(q, 1)][1]) for q in states}
    while True:
        new_part = {}
        for q in states:
            q0, o0 = tr[(q, 0)]
            q1, o1 = tr[(q, 1)]
            new_part[q] = (o0, o1, part[q0], part[q1])
        labels = {v: i for i, v in enumerate(sorted(set(new_part.values())))}
        new_part = {q: labels[v] for q, v in new_part.items()}
        if len(set(new_part.values())) == len(set(part.values())):
            part = new_part
            break
        part = new_part
    rep = {}
    for q, c in part.items():
        if c not in rep:
            rep[c] = q
    q_init = part[init]
    mapping = {q_init: 0}
    bfs = [q_init]
    new_tr = {}
    while bfs:
        c = bfs.pop(0)
        q = rep[c]
        cid = mapping[c]
        for b in (0, 1):
            qn, out = tr[(q, b)]
            cn = part[qn]
            if cn not in mapping:
                mapping[cn] = len(mapping)
                bfs.append(cn)
            new_tr[(cid, b)] = (mapping[cn], out)
    sig = tuple((s, b, new_tr[(s, b)][0], new_tr[(s, b)][1])
                for s in range(len(mapping)) for b in (0, 1))
    return (0, new_tr), sig, len(mapping)

def eval_transducer_mod(T, width: int, x: int) -> int:
    q, tr = T
    out = 0
    for i in range(width):
        b = (x >> i) & 1
        q, ob = tr[(q, b)]
        if ob:
            out |= (1 << i)
    return out

# Primitive 2-state D transducer and 3-state U transducer
T_D = (0, {(0, 0): (0, 0), (0, 1): (1, 0), (1, 0): (1, 0), (1, 1): (1, 1)})
T_U = (0, {(0, 0): (0, 0), (0, 1): (1, 0), (1, 0): (2, 1), (1, 1): (1, 0),
           (2, 0): (2, 0), (2, 1): (2, 1)})


# ==============================================================================
# 3. The Trigger-Chain Transducer Compiler & Decompiler
# ==============================================================================

def compile_word(w: str):
    """
    4-rule algebraic compiler from w in {U, D}* to TriggerChain (triggers, emit).
      compile("")    = ([], False)
      compile(D + v) = (t, False)           if e else (t + [True], False)
      compile(U + v) = (t + [False], True)  if e else (t + [True, False], True)
    """
    if not w:
        return ([], False)
    t, e = compile_word(w[1:])
    if w[0] == 'D':
        return (t, False) if e else (t + [True], False)
    else:
        return (t + [False], True) if e else (t + [True, False], True)

def decompile_tc(t, e):
    """Exact inverse of compile_word on all compiled TriggerChains."""
    if not e:
        if not t:
            return ""
        if t[-1]:
            return "D" + decompile_tc(t[:-1], False)
        return "D" + decompile_tc(t, True)
    else:
        assert len(t) >= 2 and not t[-1]
        if t[-2]:
            return "U" + decompile_tc(t[:-2], False)
        return "U" + decompile_tc(t[:-1], True)

def tc_to_transducer(t, e):
    """Build explicit (len(t) + 1)-state LSB Mealy transducer for TriggerChain(t, e)."""
    m = len(t)
    tr = {}
    for q in range(m):
        for b in (0, 1):
            if bool(b) == t[q]:
                qn = q + 1
                ob = 1 if (e and qn == m) else 0
            else:
                qn = q
                ob = 0
            tr[(q, b)] = (qn, ob)
    tr[(m, 0)] = (m, 0)
    tr[(m, 1)] = (m, 1)
    return (0, tr)

def from_bits(bits) -> int:
    val = 0
    for i, b in enumerate(bits):
        if b:
            val |= (1 << i)
    return val

def separate_words(w1: str, w2: str) -> int:
    """
    Constructive separating witness x in Nat with apply_word(w1, x) != apply_word(w2, x)
    for any distinct w1 != w2 in {U, D}*.
    """
    assert w1 != w2
    t1, e1 = compile_word(w1)
    t2, e2 = compile_word(w2)
    t_short = t1 if len(t1) <= len(t2) else t2
    return from_bits(t_short) + (1 << len(t_short))


# ==============================================================================
# 4. Generalized Odd-Multiplier Jump Transducer T_c(x) = x + c * lowbit(x)
# ==============================================================================

def make_Tc(c: int):
    """Exact minimal LSB transducer for T_c(x) = x + c * lowbit(x) (odd c >= 1)."""
    assert c >= 1 and c % 2 == 1
    init = ('SEEK',)
    tr = {}
    queue = [init]
    seen = {init}
    while queue:
        st = queue.pop()
        for b in (0, 1):
            if st == ('SEEK',):
                if b == 0:
                    nxt, out = ('SEEK',), 0
                else:
                    s = 1 + c
                    nxt, out = ('ADD', s >> 1), s & 1
            else:
                s = b + st[1]
                nxt, out = ('ADD', s >> 1), s & 1
            tr[(st, b)] = (nxt, out)
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return minimize_transducer((init, tr))[0]


# ==============================================================================
# 5. Full Independent Verification & Sharpness Counterexample Suite
# ==============================================================================

def main():
    print("=" * 76)
    print("FENWICK TRIGGER-CHAIN TRANSDUCER ENGINE: EXACT VERIFICATION & SHARPNESS")
    print("=" * 76)

    # --- Verification 1: Compiler soundness, exact linear state complexity & minimality ---
    print("\n[1] Theorem 1: Trigger-Chain Compilation & Exact Minimal State Complexity")
    max_L = 8
    total_words = 0
    for L in range(0, max_L + 1):
        for tup in product('UD', repeat=L):
            w = ''.join(tup)
            total_words += 1
            t, e = compile_word(w)
            expected_states = 1 if L == 0 else (L + 1 if w[0] == 'D' else L + 2)
            assert len(t) + 1 == expected_states

            # Compare compiled TriggerChain directly against Moore-minimized product transducer
            T_tc = tc_to_transducer(t, e)
            _, sig_tc, n_min_tc = minimize_transducer(T_tc)
            assert n_min_tc == expected_states, f"Not minimal for {w}: {n_min_tc} vs {expected_states}"

            # Check against composed primitive transducers for L <= 6
            if L <= 6:
                T_prod = (0, {(0, 0): (0, 0), (0, 1): (0, 1)})
                for ch in reversed(w):
                    T_prod = compose_transducers(T_U if ch == 'U' else T_D, T_prod)
                _, sig_prod, n_min_prod = minimize_transducer(T_prod)
                assert sig_prod == sig_tc and n_min_prod == expected_states

            # Check exact functional equality on x in 0..255 for L <= 6
            if L <= 6:
                width = 16
                for x in range(256):
                    assert apply_word(w, x) == eval_transducer_mod(T_tc, width, x)

            # Check exact decompiler invertibility
            assert decompile_tc(t, e) == w
    print(f"  PASS: Verified {total_words} words (L=0..{max_L}):")
    print(f"    - Exact state count |Q(w)| = |w| + 1 (D-prefix / empty) or |w| + 2 (U-prefix).")
    print(f"    - Moore-minimal signature identically matches compiled TriggerChain (L<=6).")
    print(f"    - Decompiler exact bijection verified for all {total_words} words.")

    # --- Verification 2: Free Monoid Theorem & Constructive Separating Witness ---
    print("\n[2] Theorem 2: Free Monoid <U, D> ~= {U, D}* & Constructive Separator")
    words_L5 = [''.join(tup) for L in range(0, 6) for tup in product('UD', repeat=L)]
    pairs_checked = 0
    for i in range(len(words_L5)):
        for j in range(i + 1, len(words_L5)):
            w1, w2 = words_L5[i], words_L5[j]
            x_sep = separate_words(w1, w2)
            assert apply_word(w1, x_sep) != apply_word(w2, x_sep)
            pairs_checked += 1
    print(f"  PASS: Constructive witness x = fromBits(t_short) + 2^|t_short| separated all {pairs_checked} distinct word pairs (L<=5).")

    # --- Verification 3: Finite-Width Nilpotency & Exact Cardinality |<U_w, D_w>| = 2^w ---
    print("\n[3] Theorem 3: Finite-Width BitVec w Monoid Dichotomy (|<U_w, D_w>| = 2^w)")
    for width in range(1, 9):
        mask = (1 << width) - 1
        id_fn = tuple(range(1 << width))
        seen = {id_fn: ""}
        queue = [id_fn]
        while queue:
            f = queue.pop(0)
            wf = seen[f]
            for ch in ('D', 'U'):
                if ch == 'D':
                    nf = tuple((y - (y & -y)) & mask for y in f)
                else:
                    nf = tuple((y + (y & -y)) & mask for y in f)
                if nf not in seen:
                    seen[nf] = ch + wf
                    queue.append(nf)
        assert len(seen) == (1 << width), f"Expected 2^{width}, got {len(seen)}"
        # Verify sharp collision at length w: U^{w-1}D == U^w == 0 mod 2^w (for w >= 2)
        if width >= 2:
            wA = 'U' * (width - 1) + 'D'
            wB = 'U' * width
            assert all((apply_word(wA, x) & mask) == 0 for x in range(1 << width))
            assert all((apply_word(wB, x) & mask) == 0 for x in range(1 << width))
        print(f"  w={width}: |<U_w, D_w>| = {len(seen)} == 2^{width} (exact; nilpotent index = {width})")

    # --- Verification 4: Universal Fenwick Ancestor-Spine Collapse ---
    print("\n[4] Theorem 4: Universal Fenwick Ancestor-Spine Collapse & Bitwise Projection")
    def is_D_anc(anc, x):
        cur = x
        while cur > anc:
            cur = D(cur)
        return cur == anc

    def is_U_anc(anc, x):
        if anc == 0:
            return True
        return x > 0 and D(anc) < x <= anc

    spine_checks = 0
    for L in range(1, 7):
        for tup in product('UD', repeat=L):
            w = ''.join(tup)
            for x in range(1, 256):
                y = apply_word(w, x)
                if w[0] == 'D':
                    assert is_D_anc(y, x) and (y & x) == y
                else:
                    assert is_U_anc(y, x)
                    if y > 0:
                        assert (y & x) == D(y)
                spine_checks += 1
    print(f"  PASS: All {spine_checks} mixed-word evaluations (1<=L<=6, 1<=x<=255) stay on monotone D/U spines.")
    print(f"  Concrete non-vacuity example: w='UDUD', x=173 (0b10101101) -> w(x)=192 = U^3(173), 192 & 173 = 128 = D(192).")

    # --- Verification 5: Word-Conjugation & Depth Duality ---
    print("\n[5] Theorem 5: Two's-Complement Word-Conjugation & Fenwick Depth Duality")
    for n in range(1, 9):
        mod = 1 << n
        mask = mod - 1
        for x in range(1, mod):
            # Depth duality: depthU(x, 2^n) + popcount(x) == n + 1 - ctz(x)
            steps = 0
            cur = x
            while cur < mod:
                cur = U(cur)
                steps += 1
            assert steps == popcount(mod - x)
            assert steps + popcount(x) == n + 1 - ctz(x)
        # Word conjugation for all words L <= 5
        for L in range(0, 6):
            for tup in product('UD', repeat=L):
                w = ''.join(tup)
                wb = dual_word(w)
                for x in range(mod):
                    lhs = (mod - (apply_word(w, x) & mask)) & mask
                    rhs = apply_word(wb, (mod - x) & mask) & mask
                    assert lhs == rhs
    print("  PASS: Exact word-conjugation (2^n - w(x)) = w_bar(2^n - x) mod 2^n and depth duality verified for n=1..8.")

    # --- Verification 6: Sharpness Counterexamples (Why c = +/-1 and unbounded Nat are Sharp) ---
    print("\n[6] Theorem 6: Sharpness & Falsified Variants (Concrete Counterexamples)")
    # (a) Odd multiplier c >= 3 breaks Ancestor-Spine Containment AND slope-1 state complexity
    x_ce = 3
    y_ce = x_ce + 3 * lowbit(x_ce) # 3 + 3*1 = 6
    print(f"  (a) Perturbed operator T_3(x) = x + 3*lowbit(x) at x = {x_ce}:")
    print(f"      T_3(3) = {y_ce} (0b{y_ce:b}), D(6) = {D(y_ce)}, T_3(3) & 3 = {y_ce & x_ce} != D(6) = {D(y_ce)}.")
    print(f"      U-spine of 3: 3 -> 4 -> 8 -> ...; D-spine of 3: 3 -> 2 -> 0. So 6 is OFF both spines!")
    assert not is_D_anc(y_ce, x_ce) and not is_U_anc(y_ce, x_ce)
    assert (y_ce & x_ce) != D(y_ce)

    print("  (b) Minimal state counts of T_c^k (k = 1..6) for odd c = 1, 3, 5, 7, 9:")
    for c in [1, 3, 5, 7, 9]:
        Tc = make_Tc(c)
        Tcur = (0, {(0, 0): (0, 0), (0, 1): (0, 1)})
        counts = []
        for _ in range(6):
            Tcur = compose_transducers(Tc, Tcur)
            Tcur, _, ns = minimize_transducer(Tcur)
            counts.append(ns)
        diffs = [counts[i + 1] - counts[i] for i in range(len(counts) - 1)]
        print(f"      c={c}: states = {counts}, step-growth = {diffs}")

    # (c) Fixed-width BitVec w breaks Freeness at exact length w
    print("  (c) Finite bit-width BitVec w breaks freeness at exact threshold L = w:")
    print("      For w = 4: w1 = 'UUUD' != w2 = 'UUUU', yet both are identically 0 mod 16 on all x in 0..15.")
    assert all((apply_word('UUUD', x) % 16) == (apply_word('UUUU', x) % 16) == 0 for x in range(16))

    print("\nALL EXACT CHECKS PASSED WITH ZERO ERRORS (PURE INTEGER ARITHMETIC).")

if __name__ == "__main__":
    main()
