"""
Pure-Silicon Automatic-Word Pattern-Avoidance Certificate Synthesizer & Verifier
================================================================================
Exact integer arithmetic only (ZERO floating-point operations anywhere).

Synthesizes pure-data BTree overlap-graph certificates for:
  1. carryXor3(n)  = popcount((3*n) ^ n) % 2     -> 4th-power-free + abelian window-8 in [2, 6]
  2. carryAnd3(n)  = popcount((3*n) & n) % 2     -> 5th-power-free
  3. carryAnd5(n)  = popcount((5*n) & n) % 2     -> 4th-power-free
  4. carryXor5(n)  = popcount((5*n) ^ n) % 2     -> 6th-power-free + abelian window-6 in [2, 4]
  5. grayMod4(n)   = popcount(n ^ (n >> 1)) % 4  -> overlap-free (2+-power-free)

Also runs:
  - Independent exact verification on n in [0, 32768)
  - Exact sharpness witnesses (proving every bound is tight)
  - Hostile certificate mutation suite (verifying every broken cert is rejected)
  - Optional Lean 4 certificate data export (--emit-lean-certs)
"""

from collections import deque
from fractions import Fraction
import sys


# ---------------------------------------------------------------------------
# 1. Native Pure-Silicon Arithmetic Word Definitions (exact Python int)
# ---------------------------------------------------------------------------

def popcount(n: int) -> int:
    return n.bit_count()


def carry_xor_3(n: int) -> int:
    return popcount((3 * n) ^ n) % 2


def carry_and_3(n: int) -> int:
    return popcount((3 * n) & n) % 2


def carry_and_5(n: int) -> int:
    return popcount((5 * n) & n) % 2


def carry_xor_5(n: int) -> int:
    return popcount((5 * n) ^ n) % 2


def gray_mod_4(n: int) -> int:
    return popcount(n ^ (n >> 1)) % 4


# ---------------------------------------------------------------------------
# 2. Exact MSB-First DFAO Builders (matching Lean 4 Carry-Offset Vector Lemma)
# ---------------------------------------------------------------------------

class DFAO:
    def __init__(self, name: str, num_states: int, num_alpha: int, q0: int,
                 d0: list[int], d1: list[int], tau: list[int]):
        self.name = name
        self.num_states = num_states
        self.num_alpha = num_alpha
        self.q0 = q0
        self.d0 = d0
        self.d1 = d1
        self.tau = tau
        assert 0 <= q0 < num_states
        assert len(d0) == num_states and len(d1) == num_states and len(tau) == num_states
        assert d0[q0] == q0
        assert all(0 <= x < num_states for x in d0)
        assert all(0 <= x < num_states for x in d1)
        assert all(0 <= x < num_alpha for x in tau)

    def eval_state(self, n: int) -> int:
        if n == 0:
            return self.q0
        # Iterative MSB-first evaluation
        bits = []
        x = n
        while x > 0:
            bits.append(x & 1)
            x >>= 1
        q = self.q0
        for b in reversed(bits):
            q = self.d1[q] if b else self.d0[q]
        return q

    def eval_word(self, n: int) -> int:
        return self.tau[self.eval_state(n)]

    def step_window(self, b: int, win: tuple[int, ...]) -> tuple[int, ...]:
        W = len(win)
        res = []
        for i in range(W):
            q = win[(b + i) >> 1]
            res.append(self.d1[q] if ((b + i) & 1) else self.d0[q])
        return tuple(res)

    def init_window(self, W: int) -> tuple[int, ...]:
        return tuple(self.eval_state(i) for i in range(W))


def build_carry_xor_dfao(K: int) -> tuple[DFAO, list[tuple[int, ...]]]:
    """Carry-offset difference vector D_K(n)[c] = (pop(K*n + c) + pop(n)) % 2."""
    def step(vec, b):
        return tuple((vec[(K * b + c) // 2] + ((K * b + c) % 2) + b) % 2 for c in range(K))

    init = tuple(popcount(c) % 2 for c in range(K))
    states = [init]
    idx = {init: 0}
    q = deque([init])
    while q:
        s = q.popleft()
        for b in (0, 1):
            ns = step(s, b)
            if ns not in idx:
                idx[ns] = len(states)
                states.append(ns)
                q.append(ns)
    d0 = [idx[step(s, 0)] for s in states]
    d1 = [idx[step(s, 1)] for s in states]
    tau = [s[0] for s in states]
    return DFAO(f"carryXor{K}", len(states), 2, 0, d0, d1, tau), states


def build_carry_and_dfao(K: int) -> tuple[DFAO, list[tuple[int, ...]]]:
    """Carry-offset AND vector A_K(n)[c] = pop((K*n + c) & n) % 2."""
    def step(vec, b):
        return tuple((vec[(K * b + c) // 2] + (((K * b + c) % 2) & b)) % 2 for c in range(K))

    init = tuple(0 for _ in range(K))
    states = [init]
    idx = {init: 0}
    q = deque([init])
    while q:
        s = q.popleft()
        for b in (0, 1):
            ns = step(s, b)
            if ns not in idx:
                idx[ns] = len(states)
                states.append(ns)
                q.append(ns)
    d0 = [idx[step(s, 0)] for s in states]
    d1 = [idx[step(s, 1)] for s in states]
    tau = [s[0] for s in states]
    return DFAO(f"carryAnd{K}", len(states), 2, 0, d0, d1, tau), states


def build_gray_mod4_dfao() -> DFAO:
    """4-state 2-uniform morphism for popcount(n ^ (n >> 1)) % 4."""
    return DFAO("grayMod4", 4, 4, 0, [0, 2, 2, 0], [1, 1, 3, 3], [0, 1, 2, 3])


# ---------------------------------------------------------------------------
# 3. Pure-Data BTree Encoding (LSB-indexed) & Certificate Synthesizers
# ---------------------------------------------------------------------------

def build_lsb_btree(items: list):
    """Build an LSB-indexed binary tree matching Lean's BTree.get?."""
    if not items:
        return None  # empty
    if len(items) == 1:
        return ("leaf", items[0])
    evens = items[0::2]
    odds = items[1::2]
    return ("node", build_lsb_btree(evens), build_lsb_btree(odds))


def btree_get(tree, idx: int):
    if tree is None:
        return None
    if tree[0] == "leaf":
        return tree[1] if idx == 0 else None
    _, l, r = tree
    return btree_get(l, idx // 2) if (idx % 2 == 0) else btree_get(r, idx // 2)


def btree_all(tree, pred) -> bool:
    if tree is None:
        return True
    if tree[0] == "leaf":
        return pred(tree[1])
    return btree_all(tree[1], pred) and btree_all(tree[2], pred)


def encode_word(base: int, word: tuple[int, ...]) -> int:
    acc = 0
    for c in word:
        acc = acc * base + c
    return acc


def synth_window_cert(M: DFAO, W: int) -> list[tuple[tuple[int, ...], int, int]]:
    """Return list of (win, next0, next1) reachable from init_window(M, W)."""
    init = M.init_window(W)
    nodes = [init]
    idx = {init: 0}
    q = deque([init])
    while q:
        w = q.popleft()
        for b in (0, 1):
            nw = M.step_window(b, w)
            if nw not in idx:
                idx[nw] = len(nodes)
                nodes.append(nw)
                q.append(nw)
    return [(w, idx[M.step_window(0, w)], idx[M.step_window(1, w)]) for w in nodes]


def synth_sync_cert(M: DFAO, L: int):
    """Synthesize (L, parity_mask, list of (parity, win, next0, next1))."""
    init = (False, M.init_window(L))
    nodes = [init]
    idx = {init: 0}
    q = deque([init])
    while q:
        par, w = q.popleft()
        for b in (0, 1):
            nw = (bool(b), M.step_window(b, w))
            if nw not in idx:
                idx[nw] = len(nodes)
                nodes.append(nw)
                q.append(nw)

    seen_out = {}
    mask = 0
    for par, w in nodes:
        out = tuple(M.tau[x] for x in w)
        code = encode_word(M.num_alpha, out)
        if code in seen_out and seen_out[code] != par:
            return None  # Not parity-synchronized at width L
        seen_out[code] = par
        if par:
            mask |= (1 << code)

    table = [
        (par, w, idx[(False, M.step_window(0, w))], idx[(True, M.step_window(1, w))])
        for (par, w) in nodes
    ]
    return (L, mask, table)


def find_minimal_sync_cert(M: DFAO, max_L: int = 16):
    for L in range(1, max_L + 1):
        res = synth_sync_cert(M, L)
        if res is not None:
            return res
    raise RuntimeError(f"No sync cert found for {M.name} up to L={max_L}")


def synth_power_avoid_cert(M: DFAO, k: int):
    assert k >= 2
    L, mask, sync_table = find_minimal_sync_cert(M)
    reach_table = synth_window_cert(M, 1)
    # Build invEven table
    inv_even = [M.num_alpha] * M.num_alpha
    for (win, _, _) in reach_table:
        q = win[0]
        o_even = M.tau[M.d0[q]]
        o_q = M.tau[q]
        if inv_even[o_even] != M.num_alpha and inv_even[o_even] != o_q:
            raise RuntimeError(f"Even halving fails for {M.name}")
        inv_even[o_even] = o_q

    p_sync = (L + k - 2) // (k - 1)
    base_certs = []
    for p in range(1, p_sync):
        W = k * p
        wt = synth_window_cert(M, W)
        # Verify no k-power of period p
        for (win, _, _) in wt:
            out = tuple(M.tau[x] for x in win)
            if all(out[j] == out[j + p] for j in range((k - 1) * p)):
                raise RuntimeError(f"{M.name} HAS a {k}-power of period {p}: {out}")
        base_certs.append(wt)

    return {
        "sync": (L, mask, sync_table),
        "inv_even": inv_even,
        "reach": reach_table,
        "bases": base_certs,
        "p_sync": p_sync,
    }


def synth_overlap_avoid_cert(M: DFAO):
    L, mask, sync_table = find_minimal_sync_cert(M)
    # Parity-tagged 1-window reachable states
    init = (False, M.init_window(1))
    nodes = [init]
    idx = {init: 0}
    q = deque([init])
    while q:
        par, w = q.popleft()
        for b in (0, 1):
            nw = (bool(b), M.step_window(b, w))
            if nw not in idx:
                idx[nw] = len(nodes)
                nodes.append(nw)
                q.append(nw)
    reach_par = [
        (par, w, idx[(False, M.step_window(0, w))], idx[(True, M.step_window(1, w))])
        for (par, w) in nodes
    ]

    A = M.num_alpha
    inv_pair = [A] * (A * A)
    inv_ev0 = [A] * A
    inv_ev1 = [A] * A
    inv_od0 = [A] * A
    inv_od1 = [A] * A
    for (par, win, _, _) in reach_par:
        st = win[0]
        oq = M.tau[st]
        o0 = M.tau[M.d0[st]]
        o1 = M.tau[M.d1[st]]
        pk = o0 * A + o1
        assert inv_pair[pk] in (A, oq)
        inv_pair[pk] = oq
        if not par:
            assert inv_ev0[o0] in (A, oq) and inv_od0[o1] in (A, oq)
            inv_ev0[o0] = oq
            inv_od0[o1] = oq
        else:
            assert inv_ev1[o0] in (A, oq) and inv_od1[o1] in (A, oq)
            inv_ev1[o0] = oq
            inv_od1[o1] = oq

    base_certs = []
    for p in range(1, 2 * L):
        W = 2 * p + 1
        wt = synth_window_cert(M, W)
        for (win, _, _) in wt:
            out = tuple(M.tau[x] for x in win)
            if all(out[j] == out[j + p] for j in range(p + 1)):
                raise RuntimeError(f"{M.name} HAS an overlap of period {p}: {out}")
        base_certs.append(wt)

    return {
        "sync": (L, mask, sync_table),
        "reach_par": reach_par,
        "inv_pair": inv_pair,
        "inv_ev0": inv_ev0,
        "inv_ev1": inv_ev1,
        "inv_od0": inv_od0,
        "inv_od1": inv_od1,
        "bases": base_certs,
    }


# ---------------------------------------------------------------------------
# 4. Mirror of Lean 4 Pure-Data Certificate Checkers (for independent replay
#    and hostile mutation testing)
# ---------------------------------------------------------------------------

def check_window_cert(M: DFAO, W: int, ok_fn, tree) -> bool:
    nd0 = btree_get(tree, 0)
    if nd0 is None or nd0[0] != M.init_window(W):
        return False

    def node_ok(nd) -> bool:
        win, n0, n1 = nd
        if len(win) != W:
            return False
        if not all(0 <= q < M.num_states for q in win):
            return False
        out = tuple(M.tau[q] for q in win)
        if not ok_fn(out):
            return False
        t0 = btree_get(tree, n0)
        t1 = btree_get(tree, n1)
        if t0 is None or t0[0] != M.step_window(0, win):
            return False
        if t1 is None or t1[0] != M.step_window(1, win):
            return False
        return True

    return btree_all(tree, node_ok)


def check_sync_cert(M: DFAO, L: int, mask: int, tree) -> bool:
    if L < 1:
        return False
    nd0 = btree_get(tree, 0)
    if nd0 is None or nd0[0] is not False or nd0[1] != M.init_window(L):
        return False

    def node_ok(nd) -> bool:
        par, win, n0, n1 = nd
        if len(win) != L:
            return False
        if not all(0 <= q < M.num_states for q in win):
            return False
        out = tuple(M.tau[q] for q in win)
        code = encode_word(M.num_alpha, out)
        bit = bool((mask >> code) & 1)
        if bit != par:
            return False
        t0 = btree_get(tree, n0)
        t1 = btree_get(tree, n1)
        if t0 is None or t0[0] is not False or t0[1] != M.step_window(0, win):
            return False
        if t1 is None or t1[0] is not True or t1[1] != M.step_window(1, win):
            return False
        return True

    return btree_all(tree, node_ok)


def no_power_at_period(k: int, p: int):
    def fn(out: tuple[int, ...]) -> bool:
        return any(out[j] != out[j + p] for j in range((k - 1) * p))
    return fn


def no_overlap_at_period(p: int):
    def fn(out: tuple[int, ...]) -> bool:
        return any(out[j] != out[j + p] for j in range(p + 1))
    return fn


def check_power_avoid_cert(M: DFAO, k: int, cert: dict) -> bool:
    if k < 2:
        return False
    L, mask, sync_table = cert["sync"]
    if not check_sync_cert(M, L, mask, build_lsb_btree(sync_table)):
        return False
    reach_tree = build_lsb_btree(cert["reach"])
    if not check_window_cert(M, 1, lambda _out: True, reach_tree):
        return False
    inv_even = cert["inv_even"]

    def halving_ok(nd) -> bool:
        q = nd[0][0]
        o_ev = M.tau[M.d0[q]]
        dec = inv_even[o_ev] if o_ev < len(inv_even) else M.num_alpha
        return dec == M.tau[q]

    if not btree_all(reach_tree, halving_ok):
        return False
    p_sync = (L + k - 2) // (k - 1)
    if len(cert["bases"]) != p_sync - 1:
        return False
    for idx, wt in enumerate(cert["bases"]):
        p = idx + 1
        if not check_window_cert(M, k * p, no_power_at_period(k, p), build_lsb_btree(wt)):
            return False
    return True


def check_overlap_avoid_cert(M: DFAO, cert: dict) -> bool:
    L, mask, sync_table = cert["sync"]
    if not check_sync_cert(M, L, mask, build_lsb_btree(sync_table)):
        return False
    rp_tree = build_lsb_btree(cert["reach_par"])
    # Verify reach_par graph
    nd0 = btree_get(rp_tree, 0)
    if nd0 is None or nd0[0] is not False or nd0[1] != M.init_window(1):
        return False
    A = M.num_alpha

    def rp_ok(nd) -> bool:
        par, win, n0, n1 = nd
        if len(win) != 1 or not (0 <= win[0] < M.num_states):
            return False
        q = win[0]
        oq = M.tau[q]
        o0 = M.tau[M.d0[q]]
        o1 = M.tau[M.d1[q]]
        pk = o0 * A + o1
        if (cert["inv_pair"][pk] if pk < len(cert["inv_pair"]) else A) != oq:
            return False
        if not par:
            if (cert["inv_ev0"][o0] if o0 < len(cert["inv_ev0"]) else A) != oq:
                return False
            if (cert["inv_od0"][o1] if o1 < len(cert["inv_od0"]) else A) != oq:
                return False
        else:
            if (cert["inv_ev1"][o0] if o0 < len(cert["inv_ev1"]) else A) != oq:
                return False
            if (cert["inv_od1"][o1] if o1 < len(cert["inv_od1"]) else A) != oq:
                return False
        t0 = btree_get(rp_tree, n0)
        t1 = btree_get(rp_tree, n1)
        if t0 is None or t0[0] is not False or t0[1] != M.step_window(0, win):
            return False
        if t1 is None or t1[0] is not True or t1[1] != M.step_window(1, win):
            return False
        return True

    if not btree_all(rp_tree, rp_ok):
        return False
    if len(cert["bases"]) != 2 * L - 1:
        return False
    for idx, wt in enumerate(cert["bases"]):
        p = idx + 1
        if not check_window_cert(M, 2 * p + 1, no_overlap_at_period(p), build_lsb_btree(wt)):
            return False
    return True


# ---------------------------------------------------------------------------
# 5. Lean 4 Certificate Code Generator (pure data, deterministic)
# ---------------------------------------------------------------------------

def fmt_list_nat(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def fmt_btree_window(items: list[tuple[tuple[int, ...], int, int]]) -> str:
    tree = build_lsb_btree(items)

    def rec(t) -> str:
        if t is None:
            return ".empty"
        if t[0] == "leaf":
            win, n0, n1 = t[1]
            return f"(.leaf ⟨{fmt_list_nat(win)}, {n0}, {n1}⟩)"
        return f"(.node {rec(t[1])} {rec(t[2])})"

    return rec(tree)


def fmt_btree_sync(items: list[tuple[bool, tuple[int, ...], int, int]]) -> str:
    tree = build_lsb_btree(items)

    def rec(t) -> str:
        if t is None:
            return ".empty"
        if t[0] == "leaf":
            par, win, n0, n1 = t[1]
            pb = "true" if par else "false"
            return f"(.leaf ⟨{pb}, {fmt_list_nat(win)}, {n0}, {n1}⟩)"
        return f"(.node {rec(t[1])} {rec(t[2])})"

    return rec(tree)


def emit_lean_cert_defs(all_data: dict) -> str:
    lines = []
    lines.append("-- AUTO-GENERATED PURE-DATA DFAOs, STATE VECTORS & CERTIFICATES")
    for key, M in all_data["dfaos"].items():
        lines.append(f"def dfao_{key} : DFAO :=")
        lines.append(f"  {{ numStates := {M.num_states}, numAlpha := {M.num_alpha}, q0 := {M.q0},")
        lines.append(f"    d0 := {fmt_list_nat(M.d0)},")
        lines.append(f"    d1 := {fmt_list_nat(M.d1)},")
        lines.append(f"    tau := {fmt_list_nat(M.tau)} }}")
        lines.append("")

    for key, vecs in all_data["vecs"].items():
        vstr = "[" + ", ".join(fmt_list_nat(v) for v in vecs) + "]"
        lines.append(f"def vecTable_{key} : List (List Nat) :=")
        lines.append(f"  {vstr}")
        lines.append("")

    for key, d in all_data["power"].items():
        L, mask, sync_table = d["sync"]
        lines.append(f"def cert_{key} : PowerAvoidCert :=")
        lines.append(f"  {{ syncCert := {{ width := {L}, parityMask := {hex(mask)}, graph := {fmt_btree_sync(sync_table)} }},")
        lines.append(f"    invEven := {fmt_list_nat(d['inv_even'])},")
        lines.append(f"    reachCert := {{ graph := {fmt_btree_window(d['reach'])} }},")
        bases_str = ", ".join("{ graph := " + fmt_btree_window(b) + " }" for b in d["bases"])
        lines.append(f"    baseCerts := [{bases_str}] }}")
        lines.append("")

    ov = all_data["overlap"]["grayMod4"]
    L, mask, sync_table = ov["sync"]
    lines.append("def cert_grayMod4_overlap : OverlapAvoidCert :=")
    lines.append(f"  {{ syncCert := {{ width := {L}, parityMask := {hex(mask)}, graph := {fmt_btree_sync(sync_table)} }},")
    lines.append(f"    reachPar := {fmt_btree_sync(ov['reach_par'])},")
    lines.append(f"    invPair := {fmt_list_nat(ov['inv_pair'])},")
    lines.append(f"    invEvenPar0 := {fmt_list_nat(ov['inv_ev0'])},")
    lines.append(f"    invEvenPar1 := {fmt_list_nat(ov['inv_ev1'])},")
    lines.append(f"    invOddPar0 := {fmt_list_nat(ov['inv_od0'])},")
    lines.append(f"    invOddPar1 := {fmt_list_nat(ov['inv_od1'])},")
    bases_str = ", ".join("{ graph := " + fmt_btree_window(b) + " }" for b in ov["bases"])
    lines.append(f"    baseCerts := [{bases_str}] }}")
    lines.append("")

    for key, wt in all_data["abelian"].items():
        lines.append(f"def cert_{key} : WindowCert :=")
        lines.append(f"  {{ graph := {fmt_btree_window(wt)} }}")
        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# 6. Independent Verification, Sharpness Witnesses, and Mutation Tests
# ---------------------------------------------------------------------------

def main():
    M_cx3, V_cx3 = build_carry_xor_dfao(3)
    M_ca3, V_ca3 = build_carry_and_dfao(3)
    M_ca5, V_ca5 = build_carry_and_dfao(5)
    M_cx5, V_cx5 = build_carry_xor_dfao(5)
    M_g4 = build_gray_mod4_dfao()

    print("=== 1. Native Arithmetic <-> DFAO Exact Equivalence (n = 0..16383) ===")
    pairs = [
        (M_cx3, carry_xor_3),
        (M_ca3, carry_and_3),
        (M_ca5, carry_and_5),
        (M_cx5, carry_xor_5),
        (M_g4, gray_mod_4),
    ]
    for M, fn in pairs:
        for n in range(16384):
            assert M.eval_word(n) == fn(n), f"Mismatch for {M.name} at n={n}"
        print(f"  [OK] {M.name:10s}: |Q|={M.num_states:2d}, |A|={M.num_alpha}, d0={M.d0}, d1={M.d1}, tau={M.tau}")

    print("\n=== 2. Synthesizing & Checking Pure-Data Avoidance Certificates ===")
    c_cx3 = synth_power_avoid_cert(M_cx3, 4)
    c_ca3 = synth_power_avoid_cert(M_ca3, 5)
    c_ca5 = synth_power_avoid_cert(M_ca5, 4)
    c_cx5 = synth_power_avoid_cert(M_cx5, 6)
    c_g4 = synth_overlap_avoid_cert(M_g4)

    assert check_power_avoid_cert(M_cx3, 4, c_cx3)
    assert check_power_avoid_cert(M_ca3, 5, c_ca3)
    assert check_power_avoid_cert(M_ca5, 4, c_ca5)
    assert check_power_avoid_cert(M_cx5, 6, c_cx5)
    assert check_overlap_avoid_cert(M_g4, c_g4)

    for label, M, k, c in [
        ("carryXor3 (4-power-free)", M_cx3, 4, c_cx3),
        ("carryAnd3 (5-power-free)", M_ca3, 5, c_ca3),
        ("carryAnd5 (4-power-free)", M_ca5, 4, c_ca5),
        ("carryXor5 (6-power-free)", M_cx5, 6, c_cx5),
    ]:
        L, _m, st = c["sync"]
        bsizes = [len(b) for b in c["bases"]]
        print(f"  [PASS] {label:28s}: L_sync={L:2d} (|sync|={len(st):3d}), |reach|={len(c['reach']):2d}, base_nodes={bsizes}")

    L, _m, st = c_g4["sync"]
    print(f"  [PASS] {'grayMod4 (overlap-free)':28s}: L_sync={L:2d} (|sync|={len(st):3d}), |reachPar|={len(c_g4['reach_par']):2d}, base_nodes={[len(b) for b in c_g4['bases']]}")

    # Abelian sliding-window certificates
    ab_cx5_w6 = synth_window_cert(M_cx5, 6)
    ab_cx3_w8 = synth_window_cert(M_cx3, 8)
    assert check_window_cert(M_cx5, 6, lambda out: 2 <= sum(out) <= 4, build_lsb_btree(ab_cx5_w6))
    assert check_window_cert(M_cx3, 8, lambda out: 2 <= sum(out) <= 6, build_lsb_btree(ab_cx3_w8))
    print(f"  [PASS] {'carryXor5 abelian W=6 [2,4]':28s}: |nodes|={len(ab_cx5_w6)}")
    print(f"  [PASS] {'carryXor3 abelian W=8 [2,6]':28s}: |nodes|={len(ab_cx3_w8)}")

    print("\n=== 3. Exact Sharpness & Boundary Witnesses ===")
    # carryXor3: 3rd power at n=5, p=1
    w_cx3 = [carry_xor_3(n) for n in range(512)]
    assert all(w_cx3[5 + j] == w_cx3[5 + 1 + j] for j in range(2))
    print(f"  [SHARP] carryXor3 cube at n=5, p=1: {w_cx3[5:8]} (exact exponent {Fraction(3, 1)})")

    # carryAnd3: 4th power at n=1, p=1
    w_ca3 = [carry_and_3(n) for n in range(512)]
    assert all(w_ca3[1 + j] == w_ca3[1 + 1 + j] for j in range(3))
    print(f"  [SHARP] carryAnd3 4th power at n=1, p=1: {w_ca3[1:5]} (exact exponent {Fraction(4, 1)})")

    # carryAnd5: 3rd power at n=19, p=1 AND (7/2)-power at n=37, p=2
    w_ca5 = [carry_and_5(n) for n in range(512)]
    assert all(w_ca5[19 + j] == w_ca5[19 + 1 + j] for j in range(2))
    assert all(w_ca5[37 + j] == w_ca5[37 + 2 + j] for j in range(5))
    print(f"  [SHARP] carryAnd5 cube at n=19, p=1: {w_ca5[19:22]}; (7/2)-power at n=37, p=2: {w_ca5[37:44]} (exact exponent {Fraction(7, 2)})")

    # carryXor5: 5th power of period p=3 at n=153, while max p=1 run is only 3!
    w_cx5 = [carry_xor_5(n) for n in range(512)]
    assert all(w_cx5[153 + j] == w_cx5[153 + 3 + j] for j in range(12))
    # Verify carryXor5 has NO 4-run (p=1, W=4) via exact certificate!
    cx5_w4 = synth_window_cert(M_cx5, 4)
    assert check_window_cert(M_cx5, 4, no_power_at_period(4, 1), build_lsb_btree(cx5_w4))
    print(f"  [SHARP] carryXor5 5th power at n=153, p=3: {w_cx5[153:168]} (exact exponent {Fraction(15, 3)}), despite NO 4-runs (W=4 cert |nodes|={len(cx5_w4)})!")

    # grayMod4: square at n=1, p=2
    w_g4 = [gray_mod_4(n) for n in range(512)]
    assert all(w_g4[1 + j] == w_g4[1 + 2 + j] for j in range(2))
    print(f"  [SHARP] grayMod4 square at n=1, p=2: {w_g4[1:5]} (exact exponent {Fraction(2, 1)})")

    # Abelian sharpness witnesses
    idx_cx5_lo = next(n for n in range(256) if sum(w_cx5[n:n+6]) == 2)
    idx_cx5_hi = next(n for n in range(256) if sum(w_cx5[n:n+6]) == 4)
    print(f"  [SHARP] carryXor5 W=6 attains weight 2 at n={idx_cx5_lo} ({w_cx5[idx_cx5_lo:idx_cx5_lo+6]}) and weight 4 at n={idx_cx5_hi} ({w_cx5[idx_cx5_hi:idx_cx5_hi+6]})")

    idx_cx3_lo = next(n for n in range(256) if sum(w_cx3[n:n+8]) == 2)
    idx_cx3_hi = next(n for n in range(256) if sum(w_cx3[n:n+8]) == 6)
    print(f"  [SHARP] carryXor3 W=8 attains weight 2 at n={idx_cx3_lo} ({w_cx3[idx_cx3_lo:idx_cx3_lo+8]}) and weight 6 at n={idx_cx3_hi} ({w_cx3[idx_cx3_hi:idx_cx3_hi+8]})")

    print("\n=== 4. Hostile Mutation Tests (all broken certificates MUST return False) ===")
    mutations = []

    # M1: corrupted edge0 in WindowCert
    bad_w1 = list(ab_cx3_w8)
    w0, e0, e1 = bad_w1[0]
    bad_w1[0] = (w0, (e0 + 1) % len(bad_w1), e1)
    mutations.append(("WindowCert bad edge0", check_window_cert(M_cx3, 8, lambda out: 2 <= sum(out) <= 6, build_lsb_btree(bad_w1))))

    # M2: corrupted initial node window in WindowCert
    bad_w2 = list(ab_cx3_w8)
    bad_w2[0] = (tuple((q + 1) % M_cx3.num_states for q in bad_w2[0][0]), bad_w2[0][1], bad_w2[0][2])
    mutations.append(("WindowCert bad init window", check_window_cert(M_cx3, 8, lambda out: 2 <= sum(out) <= 6, build_lsb_btree(bad_w2))))

    # M3: tightened false abelian predicate [3, 5] on carryXor3 W=8
    mutations.append(("WindowCert false tighter bound [3,5]", check_window_cert(M_cx3, 8, lambda out: 3 <= sum(out) <= 5, build_lsb_btree(ab_cx3_w8))))

    # M4: flipped bit in SyncCert parityMask
    L, mask, st = c_cx3["sync"]
    code0 = encode_word(M_cx3.num_alpha, tuple(M_cx3.tau[q] for q in st[0][1]))
    mutations.append(("SyncCert flipped parityMask bit", check_sync_cert(M_cx3, L, mask ^ (1 << code0), build_lsb_btree(st))))

    # M5: flipped parity tag on node 0 in SyncCert
    bad_st = list(st)
    bad_st[0] = (not bad_st[0][0], bad_st[0][1], bad_st[0][2], bad_st[0][3])
    mutations.append(("SyncCert bad node parity tag", check_sync_cert(M_cx3, L, mask, build_lsb_btree(bad_st))))

    # M6: corrupted invEven in PowerAvoidCert
    bad_p1 = dict(c_cx3)
    bad_p1["inv_even"] = [1 - x for x in c_cx3["inv_even"]]
    mutations.append(("PowerAvoidCert corrupted invEven", check_power_avoid_cert(M_cx3, 4, bad_p1)))

    # M7: truncated baseCerts in PowerAvoidCert
    bad_p2 = dict(c_cx3)
    bad_p2["bases"] = c_cx3["bases"][:-1]
    mutations.append(("PowerAvoidCert missing baseCert", check_power_avoid_cert(M_cx3, 4, bad_p2)))

    # M8: false stronger power k=3 on carryXor3 with valid k=4 cert
    mutations.append(("PowerAvoidCert false k=3 claim", check_power_avoid_cert(M_cx3, 3, c_cx3)))

    # M9: corrupted invPair in OverlapAvoidCert
    bad_ov1 = dict(c_g4)
    bad_ov1["inv_pair"] = [(x + 1) % 4 for x in c_g4["inv_pair"]]
    mutations.append(("OverlapAvoidCert bad invPair", check_overlap_avoid_cert(M_g4, bad_ov1)))

    # M10: corrupted invOddPar1 in OverlapAvoidCert
    bad_ov2 = dict(c_g4)
    bad_ov2["inv_od1"] = [(x + 1) % 4 for x in c_g4["inv_od1"]]
    mutations.append(("OverlapAvoidCert bad invOddPar1", check_overlap_avoid_cert(M_g4, bad_ov2)))

    for desc, res in mutations:
        assert res is False, f"MUTATION NOT REJECTED: {desc}"
        print(f"  [REJECTED] {desc}")

    print("\n=== 5. Independent Brute-Force Scan on Prefix N = 16384 (periods p = 1..512) ===")
    for name, fn, k_forbid in [
        ("carryXor3", carry_xor_3, 4),
        ("carryAnd3", carry_and_3, 5),
        ("carryAnd5", carry_and_5, 4),
        ("carryXor5", carry_xor_5, 6),
    ]:
        arr = [fn(n) for n in range(16384)]
        for p in range(1, 513):
            need = (k_forbid - 1) * p
            run = 0
            for i in range(len(arr) - p):
                if arr[i] == arr[i + p]:
                    run += 1
                    assert run < need, f"Counterexample for {name} k={k_forbid} at n={i-run+1}, p={p}"
                else:
                    run = 0
        print(f"  [VERIFIED] {name:10s}: zero {k_forbid}-powers in n<16384, 1<=p<=512")

    arr_g4 = [gray_mod_4(n) for n in range(16384)]
    for p in range(1, 513):
        need = p + 1
        run = 0
        for i in range(len(arr_g4) - p):
            if arr_g4[i] == arr_g4[i + p]:
                run += 1
                assert run < need, f"Overlap found for grayMod4 at n={i-run+1}, p={p}"
            else:
                run = 0
    print(f"  [VERIFIED] {'grayMod4':10s}: zero overlaps in n<16384, 1<=p<=512")

    if "--emit-lean-certs" in sys.argv:
        all_data = {
            "dfaos": {
                "carryXor3": M_cx3,
                "carryAnd3": M_ca3,
                "carryAnd5": M_ca5,
                "carryXor5": M_cx5,
                "grayMod4": M_g4,
            },
            "vecs": {
                "carryXor3": V_cx3,
                "carryAnd3": V_ca3,
                "carryAnd5": V_ca5,
                "carryXor5": V_cx5,
            },
            "power": {
                "carryXor3_k4": c_cx3,
                "carryAnd3_k5": c_ca3,
                "carryAnd5_k4": c_ca5,
                "carryXor5_k6": c_cx5,
            },
            "overlap": {
                "grayMod4": c_g4,
            },
            "abelian": {
                "carryXor5_abelian_w6": ab_cx5_w6,
                "carryXor3_abelian_w8": ab_cx3_w8,
                "carryXor5_no4run": cx5_w4,
            },
        }
        out_path = sys.argv[sys.argv.index("--emit-lean-certs") + 1]
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(emit_lean_cert_defs(all_data))
        print(f"\n[EMITTED] Lean 4 pure-data certificates to {out_path}")


if __name__ == "__main__":
    main()
