#!/usr/bin/env python3
"""
Exact Pure-Silicon Binary Exploration & Verification for Task 11:
Carry-Save Adder (CSA) Tree Confluence, Carry-Defect Transducer Quotient,
Carry-Free Compressor Capacity Dichotomy, and Depth-Invariant Carry-Parity Laws.

Uses ONLY exact Python integers (zero floating-point values anywhere).
"""

from __future__ import annotations
import itertools
import random
from typing import Callable, Dict, List, Optional, Tuple


# ---------------------------------------------------------------------------
# 1. Exact Carry-Free (p : v+1, M) Compressor Cell Exhaustive Enumeration
# ---------------------------------------------------------------------------

def valid_h_intervals(p: int, v: int, M: int) -> List[Tuple[int, int]]:
    """
    For each Hamming weight t in 0..p, compute the exact closed interval [lo, hi]
    of valid horizontal carry values h_out in 0..M such that for ALL h_in in 0..M,
    c = ((t + h_in) // 2) - h_out lies in 0..v.
    """
    intervals = []
    for t in range(p + 1):
        lo = max(0, ((t + M) // 2) - v)
        hi = min(M, t // 2)
        intervals.append((lo, hi))
    return intervals


def count_valid_carry_free_cells(p: int, v: int, M: int) -> int:
    """
    Exact count of valid carry-free horizontal-carry functions h : {0,1}^p -> {0..M}.
    (Once h is fixed, sum bit s and vertical carry sum c are uniquely determined.)
    """
    from math import comb
    intervals = valid_h_intervals(p, v, M)
    total = 1
    for t, (lo, hi) in enumerate(intervals):
        if lo > hi:
            return 0
        choices = hi - lo + 1
        total *= choices ** comb(p, t)
    return total


def verify_capacity_dichotomy() -> None:
    print("=== 1. Carry-Free (p : v+1, M) Compressor Capacity Dichotomy ===")
    for v in range(1, 5):
        for M in range(0, 2 * v + 3):
            for p in range(1, 4 * v + 4):
                cnt = count_valid_carry_free_cells(p, v, M)
                formula_exists = (M <= 2 * v) and (p <= M + 2 * v + 1)
                assert (cnt > 0) == formula_exists, (
                    f"Dichotomy mismatch at p={p}, v={v}, M={M}: cnt={cnt}, formula={formula_exists}"
                )
    print("  [PASS] Dichotomy (exists iff M <= 2v and p <= M + 2v + 1) verified for all v=1..4, M=0..2v+2, p=1..4v+3.")

    # Exact counts for v = 1 (p:2 row compressors)
    c32 = count_valid_carry_free_cells(3, 1, 0)
    c42 = count_valid_carry_free_cells(4, 1, 1)
    c52 = count_valid_carry_free_cells(5, 1, 2)
    c62_any = [count_valid_carry_free_cells(6, 1, M) for M in range(12)]
    c12_m3 = count_valid_carry_free_cells(1, 1, 3)
    assert c32 == 1
    assert c42 == 64
    assert c52 == 1
    assert all(c == 0 for c in c62_any)
    assert c12_m3 == 0
    print(f"  [PASS] Exact v=1 cell counts: 3:2(M=0)={c32}, 4:2(M=1)={c42}, 5:2(M=2)={c52}, 6:2(M=0..11)={c62_any}, 1:2(M=3)={c12_m3}")

    # Exhaustive brute-force verification on all 2^16 Boolean functions for 4:2
    brute_42 = 0
    for mask in range(1 << 16):
        ok = True
        for x in range(16):
            t = x.bit_count()
            h_out = (mask >> x) & 1
            for h_in in (0, 1):
                c = ((t + h_in) >> 1) - h_out
                if c not in (0, 1):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            brute_42 += 1
    assert brute_42 == 64
    print(f"  [PASS] Brute-force over all 65536 4-input Boolean tables confirms exactly {brute_42} valid carry-free 4:2 cells.")


# ---------------------------------------------------------------------------
# 2. Word-Level Compressors with Exact Per-Column Carry Ledger
# ---------------------------------------------------------------------------

def bit_at(x: int, k: int) -> int:
    return (x >> k) & 1


def popcount_w(x: int, w: int) -> int:
    return (x & ((1 << w) - 1)).bit_count()


def make_42_h_func(w2_mask: int) -> Callable[[int, int, int, int], int]:
    """
    Construct the (w2_mask)-th valid carry-free 4:2 horizontal carry function,
    for w2_mask in 0..63.
    The 6 weight-2 4-bit patterns are indexed in ascending numeric order:
    0b0011=3, 0b0101=5, 0b0110=6, 0b1001=9, 0b1010=10, 0b1100=12.
    """
    w2_patterns = [3, 5, 6, 9, 10, 12]
    w2_index = {pat: idx for idx, pat in enumerate(w2_patterns)}

    def h(a: int, b: int, c: int, d: int) -> int:
        pat = a | (b << 1) | (c << 2) | (d << 3)
        t = a + b + c + d
        if t <= 1:
            return 0
        if t >= 3:
            return 1
        return (w2_mask >> w2_index[pat]) & 1

    return h


# Named 4:2 cells:
# Weinberger / two-FA cascade: h(a,b,c,d) = maj(a,b,c)
# Weight-2 patterns where maj(a,b,c)=1: 0b0011 (a=1,b=1), 0b0101 (a=1,c=1), 0b0110 (b=1,c=1) -> indices 0,1,2 -> mask = 0b000111 = 7
WEINBERGER_MASK = 0b000111
SYM_GE2_MASK = 0b111111  # h = [wt >= 2]
SYM_GE3_MASK = 0b000000  # h = [wt >= 3]


def apply_22(a: int, b: int, w: Optional[int] = None) -> Tuple[int, int, Dict[int, int]]:
    """2:2 Half-Adder on words (a, b), returning (S, C, carry_ledger)."""
    if w is not None:
        mask = (1 << w) - 1
        a &= mask
        b &= mask
    s = a ^ b
    raw_c = a & b
    ledger: Dict[int, int] = {}
    lim = w if w is not None else (max(a, b).bit_length() + 1)
    for k in range(lim):
        ck = (raw_c >> k) & 1
        if ck:
            ledger[k] = ck
    c_word = raw_c << 1
    if w is not None:
        s &= mask
        c_word &= mask
    return s, c_word, ledger


def apply_32(a: int, b: int, c: int, w: Optional[int] = None) -> Tuple[int, int, Dict[int, int]]:
    """3:2 Full-Adder (CSA) on words (a, b, c), returning (S, C, carry_ledger)."""
    if w is not None:
        mask = (1 << w) - 1
        a &= mask
        b &= mask
        c &= mask
    s = a ^ b ^ c
    raw_c = (a & b) | (b & c) | (c & a)
    ledger: Dict[int, int] = {}
    lim = w if w is not None else (max(a, b, c).bit_length() + 1)
    for k in range(lim):
        ck = (raw_c >> k) & 1
        if ck:
            ledger[k] = ck
    c_word = raw_c << 1
    if w is not None:
        s &= mask
        c_word &= mask
    return s, c_word, ledger


def apply_42(
    x1: int, x2: int, x3: int, x4: int,
    w2_mask: int,
    w: Optional[int] = None,
) -> Tuple[int, int, Dict[int, int]]:
    """
    4:2 Carry-Free Compressor (any of the 64 valid cells) on 4 words.
    Returns (S, C, carry_ledger) where ledger[k] = h_k + v_k in {0, 1, 2}.
    """
    h_fn = make_42_h_func(w2_mask)
    if w is not None:
        mask = (1 << w) - 1
        x1 &= mask
        x2 &= mask
        x3 &= mask
        x4 &= mask
        lim = w
    else:
        lim = max(x1, x2, x3, x4).bit_length() + 1

    s_word = 0
    c_word = 0
    ledger: Dict[int, int] = {}
    h_in = 0
    for k in range(lim):
        a = (x1 >> k) & 1
        b = (x2 >> k) & 1
        c = (x3 >> k) & 1
        d = (x4 >> k) & 1
        t = a + b + c + d
        h_out = h_fn(a, b, c, d)
        s_bit = (t + h_in) & 1
        v_bit = ((t + h_in) >> 1) - h_out
        assert v_bit in (0, 1)
        s_word |= s_bit << k
        if w is None or k + 1 < w:
            c_word |= v_bit << (k + 1)
        tot_carry = h_out + v_bit
        if tot_carry:
            ledger[k] = tot_carry
        h_in = h_out

    if w is None and h_in:
        # Final horizontal carry enters column lim as sum bit!
        s_word |= h_in << lim
    return s_word, c_word, ledger


def apply_52(
    x1: int, x2: int, x3: int, x4: int, x5: int,
    w: Optional[int] = None,
) -> Tuple[int, int, Dict[int, int]]:
    """Unique extremal carry-free 5:2 compressor (M=2, h_out = wt // 2)."""
    if w is not None:
        mask = (1 << w) - 1
        x1 &= mask; x2 &= mask; x3 &= mask; x4 &= mask; x5 &= mask
        lim = w
    else:
        lim = max(x1, x2, x3, x4, x5).bit_length() + 1

    s_word = 0
    c_word = 0
    ledger: Dict[int, int] = {}
    h_in = 0
    for k in range(lim):
        t = ((x1 >> k) & 1) + ((x2 >> k) & 1) + ((x3 >> k) & 1) + ((x4 >> k) & 1) + ((x5 >> k) & 1)
        h_out = t >> 1
        s_bit = (t + h_in) & 1
        v_bit = ((t + h_in) >> 1) - h_out
        assert v_bit in (0, 1)
        s_word |= s_bit << k
        if w is None or k + 1 < w:
            c_word |= v_bit << (k + 1)
        tot_carry = h_out + v_bit
        if tot_carry:
            ledger[k] = tot_carry
        h_in = h_out

    if w is None and h_in:
        # Drain h_in in {0, 1, 2}: h_in = (h_in & 1) + 2*(h_in >> 1)
        s_word |= (h_in & 1) << lim
        if h_in >= 2:
            c_word |= 1 << (lim + 1)
            ledger[lim] = ledger.get(lim, 0) + 1
    return s_word, c_word, ledger


def add_ledgers(L1: Dict[int, int], L2: Dict[int, int]) -> Dict[int, int]:
    out = dict(L1)
    for k, v in L2.items():
        out[k] = out.get(k, 0) + v
    return out


# ---------------------------------------------------------------------------
# 3. Finite-State Carry-Defect Transducer A_h (2h-1 states: -(h-1)..+(h-1))
# ---------------------------------------------------------------------------

def run_carry_defect_transducer(
    Y1: List[int], Y2: List[int], h: int, width: int
) -> Tuple[bool, List[int]]:
    """
    Runs the (2h-1)-state carry-defect transducer A_h on columns 0..width-1.
    Returns (accepted, trace_of_states [q_0, q_1, ..., q_width]).
    """
    q = 0
    trace = [q]
    for k in range(width):
        u_k = sum(bit_at(y, k) for y in Y1)
        v_k = sum(bit_at(y, k) for y in Y2)
        num = q + u_k - v_k
        if num % 2 != 0:
            return False, trace
        q = num // 2
        if not (-(h - 1) <= q <= h - 1):
            return False, trace
        trace.append(q)
    return True, trace


# ---------------------------------------------------------------------------
# 4. Random / Adversarial Compressor Network Schedules & Full Law Checks
# ---------------------------------------------------------------------------

def lyapunov_psi(words: List[int], w: Optional[int] = None) -> Tuple[int, int]:
    if w is None:
        nz = sum(1 for x in words if x != 0)
        pop = sum(x.bit_count() for x in words)
    else:
        mask = (1 << w) - 1
        nz = sum(1 for x in words if (x & mask) != 0)
        pop = sum((x & mask).bit_count() for x in words)
    return (nz, pop)


def run_random_schedule(
    inputs: List[int],
    rng: random.Random,
    stop_at_height_2: bool,
    allow_52: bool,
    w: Optional[int] = None,
) -> Tuple[List[int], Dict[int, int], int]:
    """
    Applies a random valid sequence of 3:2, random-of-64 4:2, (optional 5:2),
    and (if not stop_at_height_2) 2:2 steps.
    Checks strict Lyapunov descent on every active step!
    """
    if w is not None:
        mask = (1 << w) - 1
        words = [x & mask for x in inputs if (x & mask) != 0]
    else:
        words = [x for x in inputs if x != 0]

    ledger: Dict[int, int] = {}
    steps = 0

    while True:
        # Remove zeros for clean Lyapunov check
        words = [x for x in words if x != 0]
        m = len(words)
        if stop_at_height_2 and m <= 2:
            break
        if (not stop_at_height_2) and m <= 1:
            break

        psi_before = lyapunov_psi(words, w)
        rng.shuffle(words)

        choices = []
        if m >= 3:
            choices.append("32")
        if m >= 4:
            choices.append("42")
        if allow_52 and m >= 5:
            choices.append("52")
        if not stop_at_height_2 and m >= 2:
            choices.append("22")

        op = rng.choice(choices)
        if op == "22":
            a, b = words.pop(), words.pop()
            s, c, l = apply_22(a, b, w)
            words.extend([s, c])
        elif op == "32":
            a, b, c_in = words.pop(), words.pop(), words.pop()
            s, c, l = apply_32(a, b, c_in, w)
            words.extend([s, c])
        elif op == "42":
            x1, x2, x3, x4 = words.pop(), words.pop(), words.pop(), words.pop()
            w2_mask = rng.randrange(64)
            s, c, l = apply_42(x1, x2, x3, x4, w2_mask, w)
            words.extend([s, c])
        else:
            x1, x2, x3, x4, x5 = words.pop(), words.pop(), words.pop(), words.pop(), words.pop()
            s, c, l = apply_52(x1, x2, x3, x4, x5, w)
            words.extend([s, c])

        ledger = add_ledgers(ledger, l)
        steps += 1

        psi_after = lyapunov_psi(words, w)
        assert psi_after < psi_before, (
            f"Lyapunov failed to decrease on op={op}: {psi_before} -> {psi_after}"
        )

    return words, ledger, steps


def check_all_invariants(
    X: List[int], Y: List[int], K: Dict[int, int], w: int
) -> None:
    """Verify per-column balance, carry-parity, and width-w popcount-carry laws."""
    # 1. Exact per-column balance & parity for all k in 0..w-1
    for k in range(w):
        cx = sum(bit_at(x, k) for x in X)
        cy = sum(bit_at(y, k) for y in Y)
        kin = 0 if k == 0 else K.get(k - 1, 0)
        kout = K.get(k, 0)
        assert cx + kin == cy + 2 * kout, f"Balance failed at col {k}"
        assert (cy & 1) == ((cx & 1) ^ (kin & 1)), f"Parity failed at col {k}"

    # 2. Exact width-w popcount-carry conservation (overflow weight = 2)
    pop_x = sum(popcount_w(x, w) for x in X)
    pop_y = sum(popcount_w(y, w) for y in Y)
    internal_k = sum(K.get(k, 0) for k in range(w - 1))
    overflow_k = K.get(w - 1, 0)
    assert pop_y + internal_k + 2 * overflow_k == pop_x
    # 3. Overflow-immune global carry-parity invariant
    assert (pop_y + internal_k) % 2 == pop_x % 2


def verify_networks_stress() -> None:
    print("\n=== 2. Randomized Stress Verification Across (m, w, all 64 4:2 cells, 3:2, 5:2, 2:2) ===")
    rng = random.Random(20261126)

    # Test both unbounded and fixed-width w up to 256, m up to 64
    configs = [
        (4, 8), (7, 16), (16, 32), (32, 64), (64, 128), (25, 256)
    ]
    total_trials = 0
    for m, w in configs:
        for _ in range(15):
            X = [rng.randrange(1 << w) for _ in range(m)]

            # (A) Unbounded width: run two independent schedules to height 1 and two to height 2
            W_full = sum(X).bit_length() + 2
            Y1_full, K1_full, _ = run_random_schedule(X, rng, stop_at_height_2=False, allow_52=True, w=None)
            Y2_full, K2_full, _ = run_random_schedule(X, rng, stop_at_height_2=False, allow_52=True, w=None)
            check_all_invariants(X, Y1_full, K1_full, W_full)
            check_all_invariants(X, Y2_full, K2_full, W_full)

            # Canonical normal form & carry-spectrum confluence
            val1 = Y1_full[0] if Y1_full else 0
            val2 = Y2_full[0] if Y2_full else 0
            assert val1 == val2 == sum(X)
            for k in range(W_full):
                k_star = sum(x & ((1 << (k + 1)) - 1) for x in X) >> (k + 1)
                assert K1_full.get(k, 0) == K2_full.get(k, 0) == k_star

            # Height <= 2 CSA schedules (pure 3:2 / 4:2 / 5:2, NO 2:2!)
            Y1_csa, K1_csa, _ = run_random_schedule(X, rng, stop_at_height_2=True, allow_52=False, w=None)
            Y2_csa, K2_csa, _ = run_random_schedule(X, rng, stop_at_height_2=True, allow_52=True, w=None)
            check_all_invariants(X, Y1_csa, K1_csa, W_full)
            check_all_invariants(X, Y2_csa, K2_csa, W_full)

            # 3-state transducer A_2 acceptance and exact state identity q_k = K2(k-1) - K1(k-1)
            ok, trace = run_carry_defect_transducer(Y1_csa, Y2_csa, h=2, width=W_full)
            assert ok and trace[-1] == 0
            for k in range(W_full):
                expected_q = (0 if k == 0 else K2_csa.get(k - 1, 0) - K1_csa.get(k - 1, 0))
                assert trace[k] == expected_q
                # Check exact CPA carry-bit identity: K*(k) - K1_csa(k) == carry_out_k(S1 + C1)
                s1 = Y1_csa[0] if len(Y1_csa) >= 1 else 0
                c1 = Y1_csa[1] if len(Y1_csa) >= 2 else 0
                cpa_carry_k = ((s1 & ((1 << (k + 1)) - 1)) + (c1 & ((1 << (k + 1)) - 1))) >> (k + 1)
                assert K1_full.get(k, 0) - K1_csa.get(k, 0) == cpa_carry_k

            # (B) Truncated modular width w
            Yw1, Kw1, _ = run_random_schedule(X, rng, stop_at_height_2=False, allow_52=True, w=w)
            Yw2, Kw2, _ = run_random_schedule(X, rng, stop_at_height_2=False, allow_52=False, w=w)
            check_all_invariants(X, Yw1, Kw1, w)
            check_all_invariants(X, Yw2, Kw2, w)
            assert (Yw1[0] if Yw1 else 0) == (Yw2[0] if Yw2 else 0) == (sum(X) & ((1 << w) - 1))
            for k in range(w):
                assert Kw1.get(k, 0) == Kw2.get(k, 0)

            Yw1_csa, Kw1_csa, _ = run_random_schedule(X, rng, stop_at_height_2=True, allow_52=False, w=w)
            Yw2_csa, Kw2_csa, _ = run_random_schedule(X, rng, stop_at_height_2=True, allow_52=False, w=w)
            check_all_invariants(X, Yw1_csa, Kw1_csa, w)
            check_all_invariants(X, Yw2_csa, Kw2_csa, w)
            ok_w, trace_w = run_carry_defect_transducer(Yw1_csa, Yw2_csa, h=2, width=w)
            assert ok_w
            assert trace_w[w] == Kw2_csa.get(w - 1, 0) - Kw1_csa.get(w - 1, 0)

            total_trials += 1

    print(f"  [PASS] All {total_trials} multi-schedule stress trials (up to m=64, w=256) passed every invariant, confluence, Lyapunov, and transducer law.")


# ---------------------------------------------------------------------------
# 5. Sharpness & Falsification Witnesses
# ---------------------------------------------------------------------------

def find_sharpness_witnesses() -> None:
    print("\n=== 3. Sharpness & Falsification Counterexamples ===")

    # Witness A: All-nonzero 4-word input where two pure 3:2 CSA schedules
    # produce DIFFERENT height-2 pairs AND hit BOTH non-zero states -1 and +1 of A_2!
    X = [1, 1, 2, 4]  # all nonzero, sum = 8!
    # Schedule 1: csa32(1, 1, 2) -> (2, 2); then csa32(2, 2, 4) -> (4, 4)
    s1a, c1a, l1a = apply_32(1, 1, 2)
    s1b, c1b, l1b = apply_32(s1a, c1a, 4)
    Y1 = [s1b, c1b]
    K1 = add_ledgers(l1a, l1b)

    # Schedule 2: csa32(1, 2, 4) -> (7, 0); then csa32(7, 0, 1) -> (6, 2)
    s2a, c2a, l2a = apply_32(1, 2, 4)
    s2b, c2b, l2b = apply_32(s2a, c2a, 1)
    Y2 = [s2b, c2b]
    K2 = add_ledgers(l2a, l2b)

    ok_12, trace_12 = run_carry_defect_transducer(Y1, Y2, h=2, width=5)
    ok_21, trace_21 = run_carry_defect_transducer(Y2, Y1, h=2, width=5)
    assert Y1 != Y2 and sorted(Y1) != sorted(Y2)
    assert ok_12 and (-1 in trace_12)
    assert ok_21 and (+1 in trace_21)
    print(f"  [WITNESS A: Height-2 non-confluence & A_2 state minimality]")
    print(f"    X = {X} (all nonzero, sum={sum(X)})")
    print(f"    3:2 Schedule 1 -> Y1 = {Y1}, K1 = {K1}")
    print(f"    3:2 Schedule 2 -> Y2 = {Y2}, K2 = {K2}")
    print(f"    A_2(Y1, Y2) trace = {trace_12} (hits state -1!)")
    print(f"    A_2(Y2, Y1) trace = {trace_21} (hits state +1!)")

    # Witness B: Two DIFFERENT valid 4:2 cells (of the 64) on the SAME 4 nonzero words
    # producing DIFFERENT carry-save pairs AND hitting A_2 states +-1!
    X4 = [3, 1, 2, 4]  # let's search smallest all-nonzero 4-tuple hitting state +-1 between 4:2 cells!
    found_42 = None
    for a in range(1, 8):
        for b in range(1, 8):
            for c in range(1, 8):
                for d in range(1, 8):
                    y_wein = apply_42(a, b, c, d, WEINBERGER_MASK)
                    y_sym3 = apply_42(a, b, c, d, SYM_GE3_MASK)
                    Y_a = [y_wein[0], y_wein[1]]
                    Y_b = [y_sym3[0], y_sym3[1]]
                    ok, tr = run_carry_defect_transducer(Y_a, Y_b, h=2, width=6)
                    if ok and (1 in tr or -1 in tr):
                        found_42 = ([a, b, c, d], Y_a, y_wein[2], Y_b, y_sym3[2], tr)
                        break
                if found_42: break
            if found_42: break
        if found_42: break
    assert found_42 is not None
    inp, Ya, Ka, Yb, Kb, tr = found_42
    print(f"  [WITNESS B: Distinct valid 4:2 cells diverge in (S,C) yet stay in A_2]")
    print(f"    X = {inp} (sum={sum(inp)})")
    print(f"    Weinberger 4:2 (mask=7) -> {Ya}, K={Ka}")
    print(f"    Sym-[wt>=3] 4:2 (mask=0) -> {Yb}, K={Kb}")
    print(f"    A_2 trace = {tr}")

    # Witness C: Minimality of 2h-1 states for arbitrary h >= 1
    for h in range(1, 10):
        for r in range(h):
            w_min = max(1, r.bit_length() + 1)
            Y_hi = [(1 << w_min) - 1] * r + ([r] if r > 0 else [])
            Y_lo = [1 << w_min] * r
            assert len(Y_hi) <= h and len(Y_lo) <= h
            assert sum(Y_hi) == sum(Y_lo)
            ok_pos, tr_pos = run_carry_defect_transducer(Y_hi, Y_lo, h=h, width=w_min + 1)
            ok_neg, tr_neg = run_carry_defect_transducer(Y_lo, Y_hi, h=h, width=w_min + 1)
            assert ok_pos and tr_pos[w_min] == r and tr_pos[w_min + 1] == 0
            assert ok_neg and tr_neg[w_min] == -r and tr_neg[w_min + 1] == 0
    print("  [WITNESS C: Tightness of 2h-1 states] Verified constructive reachability of EVERY q in [-(h-1), +(h-1)] for h=1..9.")

    # Witness D: Necessity of factor 2 on overflow carries K(w-1) in width-w Popcount-Carry law
    # Take w=2, X=[3, 3] (sum=6): 2:2 gives S=0, C=2 (truncated mod 4: (3&3)<<1 = 6 & 3 = 2),
    # K(0)=1, K(1)=1 (overflow!).
    # pop_2(X) = 2+2 = 4; pop_2(Y) = 0+1 = 1; internal K(0) = 1; overflow K(1) = 1.
    # With factor 2: 1 + 1 + 2*1 = 4 == pop_2(X).
    # With naive factor 1: 1 + 1 + 1 = 3 != 4!
    s_ov, c_ov, l_ov = apply_22(3, 3, w=2)
    pop_x = popcount_w(3, 2) + popcount_w(3, 2)
    pop_y = popcount_w(s_ov, 2) + popcount_w(c_ov, 2)
    assert pop_y + l_ov.get(0, 0) + 2 * l_ov.get(1, 0) == pop_x
    assert pop_y + l_ov.get(0, 0) + 1 * l_ov.get(1, 0) != pop_x
    print(f"  [WITNESS D: Overflow factor-2 sharpness] w=2, X=[3,3] -> Y={[s_ov, c_ov]}, K={l_ov}:")
    print(f"    pop_2(Y)+K(0)+2*K(1) = {pop_y}+{l_ov[0]}+2*{l_ov[1]} = {pop_x} (EXACT), whereas weight-1 gives {pop_y+l_ov[0]+l_ov[1]} != {pop_x}.")

    # Witness E: Corrupted 4:2 cell (flipping 1 entry: h(1,1,1,0)=0 instead of 1) breaks CellValid and sum/parity!
    # At (1,1,1,0), h_in=1: t+h_in = 4, so ((4)>>1) - 0 = 2 not in {0, 1}!
    t_bad, h_in_bad, h_out_bad = 3, 1, 0
    v_bad = ((t_bad + h_in_bad) >> 1) - h_out_bad
    assert v_bad == 2  # overflows 1 vertical carry bit!
    print(f"  [WITNESS E: CellValid sharpness] Flipping h(1,1,1,0)=0 forces v={v_bad} > 1 when h_in=1, breaking binary carry conservation.")


# ---------------------------------------------------------------------------
# 6. Universal r-Hop Bounded-Chain Compressor Dichotomy & Heterogeneous Networks
# ---------------------------------------------------------------------------

def apply_rhop_canonical(xs: List[int], v: int, r: int, w: int) -> Tuple[List[int], Dict[int, int]]:
    """
    Exact Python implementation of `canonicalRHopCompressor p v r` (`hOut w = winSum w // 2^r`).
    Works for ANY p <= 2 * v * 2^r + 1.
    """
    p = len(xs)
    assert p <= 2 * v * (1 << r) + 1
    win = [0] * r  # win[0] = most recent column weight, win[r-1] = oldest
    s_word = 0
    c_words = [0] * v
    ledger: Dict[int, int] = {}

    def win_sum(window: List[int]) -> int:
        return sum(window[j] * (1 << (r - 1 - j)) for j in range(r))

    for k in range(w):
        t_k = sum((x >> k) & 1 for x in xs)
        h_in = win_sum(win) >> r if r > 0 else 0
        next_win = ([t_k] + win[:-1]) if r > 0 else []
        h_out = win_sum(next_win) >> r if r > 0 else 0
        s_bit = (t_k + h_in) & 1
        v_cnt = ((t_k + h_in) >> 1) - h_out
        assert 0 <= v_cnt <= v, f"v_cnt={v_cnt} out of [0,{v}] at k={k}"
        s_word |= s_bit << k
        if k + 1 < w:
            for idx in range(v):
                if idx < v_cnt:
                    c_words[idx] |= 1 << (k + 1)
        tot = h_out + v_cnt
        if tot:
            ledger[k] = tot
        win = next_win

    return [s_word] + c_words, ledger


def check_rhop_dp_exact(p: int, v: int, r: int) -> bool:
    """Exact integer interval fixed-point test for existence of an r-hop (p : v+1) compressor."""
    states = list(itertools.product(range(p + 1), repeat=r))
    big = (p + 1) * (1 << (r + 1))
    lo = {s: 0 for s in states}
    hi = {s: big for s in states}
    zero = (0,) * r
    lo[zero] = 0
    hi[zero] = 0
    for _ in range(200):
        changed = False
        for cur in states:
            t_new = cur[0]
            prefix = cur[1:]
            new_lo, new_hi = lo[cur], hi[cur]
            for t_old in range(p + 1):
                prev = prefix + (t_old,)
                cand_lo = ((t_new + lo[prev]) >> 1) - v
                cand_hi = (t_new + hi[prev]) >> 1
                if cand_lo > new_lo:
                    new_lo = cand_lo
                if cand_hi < new_hi:
                    new_hi = cand_hi
            if new_lo > new_hi:
                return False
            if new_lo != lo[cur] or new_hi != hi[cur]:
                lo[cur], hi[cur] = new_lo, new_hi
                changed = True
            for t_old in range(p + 1):
                prev = prefix + (t_old,)
                p_lo = 2 * lo[cur] - t_new
                p_hi = 2 * (hi[cur] + v) + 1 - t_new
                if p_lo > lo[prev]:
                    lo[prev] = p_lo
                    changed = True
                if p_hi < hi[prev]:
                    hi[prev] = p_hi
                    changed = True
                if lo[prev] > hi[prev]:
                    return False
        if not changed:
            break
    for h_cand in (lo, hi):
        ok = True
        for cur in states:
            t_new = cur[0]
            prefix = cur[1:]
            for t_old in range(p + 1):
                prev = prefix + (t_old,)
                c = ((t_new + h_cand[prev]) >> 1) - h_cand[cur]
                if not (0 <= c <= v):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


def verify_rhop_dichotomy_and_mixed() -> None:
    print("\n=== 4. Universal r-Hop Bounded-Chain Dichotomy p_max(v, r) = 2*v*2^r + 1 ===")
    # Exact DP boundary verification at (v, r): test p = p_max (PASS) and p = p_max + 1 (FAIL)
    for v, r in [(1, 1), (1, 2), (2, 1), (2, 2)]:
        p_max = 2 * v * (1 << r) + 1
        assert check_rhop_dp_exact(p_max, v, r) is True
        assert check_rhop_dp_exact(p_max + 1, v, r) is False
        print(f"  [PASS] Exact DP boundary at (v={v}, r={r}): p={p_max} EXISTS, p={p_max+1} IMPOSSIBLE.")

    # Direct constructive stress test of canonical r-hop compressors up to 3-hop 17:2 and 2-hop 17:3
    rng = random.Random(20261127)
    for (p, v, r, w) in [(6, 1, 2, 64), (9, 1, 2, 64), (17, 1, 3, 128), (17, 2, 2, 64), (33, 2, 3, 64)]:
        for _ in range(20):
            X = [rng.randrange(1 << w) for _ in range(p)]
            Y, K = apply_rhop_canonical(X, v=v, r=r, w=w)
            check_all_invariants(X, Y, K, w)
            assert len(Y) == v + 1
    print("  [PASS] Canonical r-hop word compressors verified across 100 trials (2-hop 6:2/9:2/17:3, 3-hop 17:2/33:3, up to w=128).")

    # Witness E (Heterogeneous r-hop confluence: 2-hop 6:2 vs 1-hop 4:2+3:2 on [3, 5, 7, 1, 2, 6], w=6)
    X6 = [3, 5, 7, 1, 2, 6]
    Y_2hop, K_2hop = apply_rhop_canonical(X6, v=1, r=2, w=6)
    s1, c1, l1 = apply_42(3, 5, 7, 1, WEINBERGER_MASK, w=6)
    s2, c2, l2 = apply_32(s1, c1, 2, w=6)
    s3, c3, l3 = apply_32(s2, c2, 6, w=6)
    Y_1hop = [s3, c3]
    K_1hop = add_ledgers(add_ledgers(l1, l2), l3)
    check_all_invariants(X6, Y_2hop, K_2hop, 6)
    check_all_invariants(X6, Y_1hop, K_1hop, 6)
    ok, tr = run_carry_defect_transducer(Y_2hop, Y_1hop, h=2, width=6)
    assert ok and tr[-1] == 0 and sum(Y_2hop) == 24 and sum(Y_1hop) == 24
    print(f"  [WITNESS F: Heterogeneous 2-hop 6:2 vs 1-hop 4:2+3:2 on X={X6}]")
    print(f"    2-hop 6:2 -> Y1={Y_2hop}, K1={K_2hop}")
    print(f"    1-hop 4:2+3:2 -> Y2={Y_1hop}, K2={K_1hop}")
    print(f"    A_2(Y1, Y2) trace = {tr} (accepted, sum=24!)")


if __name__ == "__main__":
    verify_capacity_dichotomy()
    verify_networks_stress()
    find_sharpness_witnesses()
    verify_rhop_dichotomy_and_mixed()
    print("\nALL EXACT PYTHON VERIFICATIONS PASSED (ZERO FLOATS USED).")
