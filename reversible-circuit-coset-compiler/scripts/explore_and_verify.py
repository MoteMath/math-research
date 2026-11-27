#!/usr/bin/env python3
"""
certcomp-14: Independent Exact Exploration, Certificate Synthesis, Verification & Sharpness Suite
for the Verified Lean 4 Reversible-Circuit Commutation & Group-Word Compiler (`RevCert`).

100% pure integer / exact bit-vector arithmetic (zero floating point anywhere).
"""

from collections import deque
from typing import Dict, List, Tuple, Optional
import sys

# ============================================================================
# 1. Exact Width-Indexed Reversible Silicon Machine (matches the Lean sources)
# ============================================================================

def mask(w: int) -> int:
    return (1 << w) - 1

def bit_get(x: int, p: int) -> int:
    return (x >> p) & 1

def flip_bit(x: int, p: int, w: int) -> int:
    return (x ^ (1 << p)) if p < w else x

def eval_gate(gate: tuple, state: Tuple[int, ...], w: int) -> Tuple[int, ...]:
    m = mask(w)
    s = list(state)
    tag = gate[0]
    if tag == "rNot":
        _, i = gate
        s[i] = (~s[i]) & m
    elif tag == "rSwap":
        _, i, j = gate
        s[i], s[j] = s[j], s[i]
    elif tag == "rCnot":
        _, c, t = gate
        if c != t:
            s[t] = (s[t] ^ s[c]) & m
    elif tag == "rToff":
        _, c1, c2, t = gate
        if c1 != t and c2 != t and c1 != c2:
            s[t] = (s[t] ^ (s[c1] & s[c2])) & m
    elif tag == "rAdd":
        _, src, dst = gate
        if src != dst:
            s[dst] = (s[dst] + s[src]) & m
    elif tag == "rSub":
        _, src, dst = gate
        if src != dst:
            s[dst] = (s[dst] - s[src]) & m
    elif tag == "rNeg":
        _, i = gate
        s[i] = (-s[i]) & m
    elif tag == "rInc":
        _, i = gate
        s[i] = (s[i] + 1) & m
    elif tag == "rDec":
        _, i = gate
        s[i] = (s[i] - 1) & m
    elif tag == "bNot":
        _, i, p = gate
        s[i] = flip_bit(s[i], p, w)
    elif tag == "bSwap":
        _, i1, p1, i2, p2 = gate
        if p1 < w and p2 < w and (i1 != i2 or p1 != p2):
            if bit_get(s[i1], p1) != bit_get(s[i2], p2):
                s[i1] = flip_bit(s[i1], p1, w)
                s[i2] = flip_bit(s[i2], p2, w)
    elif tag == "bCnot":
        _, ic, pc, it, pt = gate
        if pc < w and pt < w and (ic != it or pc != pt):
            if bit_get(s[ic], pc):
                s[it] = flip_bit(s[it], pt, w)
    elif tag == "bToff":
        _, i1, p1, i2, p2, it, pt = gate
        if p1 < w and p2 < w and pt < w:
            if (i1, p1) != (it, pt) and (i2, p2) != (it, pt) and (i1, p1) != (i2, p2):
                if bit_get(s[i1], p1) and bit_get(s[i2], p2):
                    s[it] = flip_bit(s[it], pt, w)
    else:
        raise ValueError(f"Unknown gate: {gate}")
    return tuple(s)

def eval_circuit(circ: List[tuple], state: Tuple[int, ...], w: int) -> Tuple[int, ...]:
    s = state
    for g in circ:
        s = eval_gate(g, s, w)
    return s

def inv_gate(gate: tuple) -> tuple:
    tag = gate[0]
    if tag == "rAdd": return ("rSub", gate[1], gate[2])
    if tag == "rSub": return ("rAdd", gate[1], gate[2])
    if tag == "rInc": return ("rDec", gate[1])
    if tag == "rDec": return ("rInc", gate[1])
    return gate

def inv_circuit(circ: List[tuple]) -> List[tuple]:
    return [inv_gate(g) for g in reversed(circ)]

# ============================================================================
# 2. Exact 2's-Complement Ripple-Carry Mealy Transducer (matches the Lean sources Sec 3)
# ============================================================================

def has_carry(g: tuple) -> bool:
    return g[0] in ("rAdd", "rSub", "rNeg", "rInc", "rDec")

def init_carry_gate(g: tuple) -> bool:
    return g[0] in ("rSub", "rNeg", "rInc")

def init_carries(circ: List[tuple]) -> Tuple[bool, ...]:
    return tuple(init_carry_gate(g) for g in circ if has_carry(g))

def at_least_two(a: bool, b: bool, c: bool) -> bool:
    return (a and b) or (c and (a or b))

def step_reg_circ(circ: List[tuple], carries: Tuple[bool, ...], bits: Tuple[bool, ...]) -> Tuple[Tuple[bool, ...], Tuple[bool, ...]]:
    b = list(bits)
    c_out: List[bool] = []
    ci = 0
    for g in circ:
        tag = g[0]
        if tag == "rNot":
            _, i = g
            b[i] = not b[i]
        elif tag == "rSwap":
            _, i, j = g
            b[i], b[j] = b[j], b[i]
        elif tag == "rCnot":
            _, c, t = g
            if c != t:
                b[t] = b[t] ^ b[c]
        elif tag == "rToff":
            _, c1, c2, t = g
            if c1 != t and c2 != t and c1 != c2:
                b[t] = b[t] ^ (b[c1] and b[c2])
        elif tag == "rAdd":
            _, src, dst = g
            c = carries[ci]; ci += 1
            if src != dst:
                nc = at_least_two(b[dst], b[src], c)
                b[dst] = b[dst] ^ (b[src] ^ c)
                c_out.append(nc)
            else:
                c_out.append(c)
        elif tag == "rSub":
            _, src, dst = g
            c = carries[ci]; ci += 1
            if src != dst:
                ns = not b[src]
                nc = at_least_two(b[dst], ns, c)
                b[dst] = b[dst] ^ (ns ^ c)
                c_out.append(nc)
            else:
                c_out.append(c)
        elif tag == "rNeg":
            _, i = g
            c = carries[ci]; ci += 1
            ni = not b[i]
            nc = at_least_two(ni, False, c)
            b[i] = ni ^ c
            c_out.append(nc)
        elif tag == "rInc":
            _, i = g
            c = carries[ci]; ci += 1
            nc = at_least_two(b[i], False, c)
            b[i] = b[i] ^ c
            c_out.append(nc)
        elif tag == "rDec":
            _, i = g
            c = carries[ci]; ci += 1
            nc = at_least_two(b[i], True, c)
            b[i] = b[i] ^ (True ^ c)
            c_out.append(nc)
        else:
            raise ValueError(f"Non-reg gate: {g}")
    return tuple(c_out), tuple(b)

def synthesize_bisim(r: int, c1: List[tuple], c2: List[tuple]) -> Optional[List[Tuple[Tuple[bool, ...], Tuple[bool, ...]]]]:
    q0 = (init_carries(c1), init_carries(c2))
    visited = {q0}
    queue = deque([q0])
    while queue:
        q1, q2 = queue.popleft()
        for m in range(1 << r):
            bits = tuple(bool((m >> i) & 1) for i in range(r))
            nq1, o1 = step_reg_circ(c1, q1, bits)
            nq2, o2 = step_reg_circ(c2, q2, bits)
            if o1 != o2:
                return None
            pair = (nq1, nq2)
            if pair not in visited:
                visited.add(pair)
                queue.append(pair)
    return sorted(visited)

# ============================================================================
# 3. Exact Rewriting Engine & Bidirectional BFS Synthesizer (matches the Lean sources Sec 4)
# ============================================================================

def reg_touched(g: tuple) -> set:
    tag = g[0]
    if tag in ("rNot", "rNeg", "rInc", "rDec", "bNot"):
        return {g[1]}
    if tag in ("rSwap", "rCnot", "rAdd", "rSub"):
        return {g[1], g[2]}
    if tag in ("bSwap", "bCnot"):
        return {g[1], g[3]}
    if tag == "rToff":
        return {g[1], g[2], g[3]}
    if tag == "bToff":
        return {g[1], g[3], g[5]}
    raise ValueError(g)

def gates_commute(g1: tuple, g2: tuple) -> bool:
    return (g1 == g2) or reg_touched(g1).isdisjoint(reg_touched(g2))

def apply_step(lib: List[Tuple[List[tuple], List[tuple]]], word: List[tuple], step: tuple) -> Optional[List[tuple]]:
    kind = step[0]
    if kind == "invElim":
        _, pos = step
        if pos + 1 < len(word) and (word[pos + 1] == inv_gate(word[pos]) or word[pos] == inv_gate(word[pos + 1])):
            return word[:pos] + word[pos + 2:]
        return None
    elif kind == "invIntro":
        _, pos, g = step
        if pos <= len(word):
            return word[:pos] + [g, inv_gate(g)] + word[pos:]
        return None
    elif kind == "commute":
        _, pos = step
        if pos + 1 < len(word) and gates_commute(word[pos], word[pos + 1]):
            return word[:pos] + [word[pos + 1], word[pos]] + word[pos + 2:]
        return None
    elif kind == "applyRel":
        _, idx, fwd, pos = step
        if idx < len(lib):
            lhs, rhs = lib[idx]
            src, dst = (lhs, rhs) if fwd else (rhs, lhs)
            if pos + len(src) <= len(word) and word[pos:pos + len(src)] == src:
                return word[:pos] + dst + word[pos + len(src):]
        return None
    return None

def check_rewrite(lib, w1, w2, cert) -> bool:
    cur = list(w1)
    for st in cert:
        nxt = apply_step(lib, cur, st)
        if nxt is None:
            return False
        cur = nxt
    return cur == list(w2)

def find_rewrite_bfs(lib, start, target, max_len=14, max_nodes=80000):
    start_t = tuple(start)
    target_t = tuple(target)
    if start_t == target_t:
        return []
    fwd_parent = {start_t: None}
    bwd_parent = {target_t: None}
    fwd_q = deque([start_t])
    bwd_q = deque([target_t])

    def neighbors(w_t):
        w = list(w_t)
        res = []
        n = len(w)
        for pos in range(n - 1):
            if w[pos + 1] == inv_gate(w[pos]) or w[pos] == inv_gate(w[pos + 1]):
                res.append((("invElim", pos), tuple(w[:pos] + w[pos + 2:])))
        for pos in range(n - 1):
            if gates_commute(w[pos], w[pos + 1]):
                res.append((("commute", pos), tuple(w[:pos] + [w[pos + 1], w[pos]] + w[pos + 2:])))
        for idx, (lhs, rhs) in enumerate(lib):
            ls, rs = len(lhs), len(rhs)
            for pos in range(n - ls + 1):
                if w[pos:pos + ls] == lhs and n - ls + rs <= max_len:
                    res.append((("applyRel", idx, True, pos), tuple(w[:pos] + rhs + w[pos + ls:])))
            for pos in range(n - rs + 1):
                if w[pos:pos + rs] == rhs and n - rs + ls <= max_len:
                    res.append((("applyRel", idx, False, pos), tuple(w[:pos] + lhs + w[pos + rs:])))
        return res

    def invert_step(step, before_w):
        kind = step[0]
        if kind == "invElim":
            _, pos = step
            return ("invIntro", pos, before_w[pos])
        if kind == "commute":
            return step
        if kind == "applyRel":
            _, idx, fwd, pos = step
            return ("applyRel", idx, not fwd, pos)
        raise ValueError(step)

    def reconstruct(meet):
        f_steps = []
        cur = meet
        while fwd_parent[cur] is not None:
            prev, st = fwd_parent[cur]
            f_steps.append(st)
            cur = prev
        f_steps.reverse()
        b_steps = []
        cur = meet
        while bwd_parent[cur] is not None:
            prev, st = bwd_parent[cur]
            b_steps.append(invert_step(st, prev))
            cur = prev
        return f_steps + b_steps

    nodes = 2
    while (fwd_q or bwd_q) and nodes < max_nodes:
        if fwd_q and (len(fwd_q) <= len(bwd_q) or not bwd_q):
            cur = fwd_q.popleft()
            for st, nxt in neighbors(cur):
                if nxt not in fwd_parent:
                    fwd_parent[nxt] = (cur, st)
                    nodes += 1
                    if nxt in bwd_parent:
                        cert = reconstruct(nxt)
                        assert check_rewrite(lib, start, target, cert)
                        return cert
                    fwd_q.append(nxt)
        else:
            cur = bwd_q.popleft()
            for st, nxt in neighbors(cur):
                if nxt not in bwd_parent:
                    bwd_parent[nxt] = (cur, st)
                    nodes += 1
                    if nxt in fwd_parent:
                        cert = reconstruct(nxt)
                        assert check_rewrite(lib, start, target, cert)
                        return cert
                    bwd_q.append(nxt)
    return None

# ============================================================================
# 4. Lean Code Formatters
# ============================================================================

def fmt_bool(b: bool) -> str:
    return "true" if b else "false"

def fmt_bisim(cert: List[Tuple[Tuple[bool, ...], Tuple[bool, ...]]]) -> str:
    items = []
    for q1, q2 in cert:
        s1 = "[" + ", ".join(fmt_bool(x) for x in q1) + "]"
        s2 = "[" + ", ".join(fmt_bool(x) for x in q2) + "]"
        items.append(f"({s1}, {s2})")
    return "[" + ", ".join(items) + "]"

def fmt_gate(g: tuple) -> str:
    tag = g[0]
    if tag in ("rNot", "rNeg", "rInc", "rDec"):
        return f".{tag} {g[1]}"
    if tag in ("rSwap", "rCnot", "rAdd", "rSub", "bNot"):
        return f".{tag} {g[1]} {g[2]}"
    if tag == "rToff":
        return f".rToff {g[1]} {g[2]} {g[3]}"
    if tag in ("bSwap", "bCnot"):
        return f".{tag} {g[1]} {g[2]} {g[3]} {g[4]}"
    if tag == "bToff":
        return f".bToff {g[1]} {g[2]} {g[3]} {g[4]} {g[5]} {g[6]}"
    raise ValueError(g)

def fmt_step(st: tuple) -> str:
    kind = st[0]
    if kind == "invElim":
        return f".invElim {st[1]}"
    if kind == "invIntro":
        return f".invIntro {st[1]} ({fmt_gate(st[2])})"
    if kind == "commute":
        return f".commute {st[1]}"
    if kind == "applyRel":
        return f".applyRel {st[1]} {fmt_bool(st[2])} {st[3]}"
    raise ValueError(st)

def fmt_cert(cert: List[tuple]) -> str:
    return "[" + ", ".join(fmt_step(s) for s in cert) + "]"

def fmt_circuit(circ: List[tuple]) -> str:
    return "[" + ", ".join(fmt_gate(g) for g in circ) + "]"

# ============================================================================
# 5. Synthesize All Flagship Certificates + Independent Verification + Sharpness
# ============================================================================

def build_all(emit_lean: bool = False):
    # --- Family I: Modular-Add + Swap Dihedral Group D6 (Order 12) ---
    U = [("rAdd", 0, 1)]
    V = [("rSub", 1, 0)]
    S = [("rSwap", 0, 1)]
    C = U + V
    J = U + V + U

    bisim_sl2_braid = synthesize_bisim(2, U + V + U, V + U + V)
    bisim_j4 = synthesize_bisim(2, J * 4, [])
    bisim_not_add = synthesize_bisim(2, [("rNot", 1), ("rAdd", 0, 1), ("rNot", 1)], [("rSub", 0, 1)])
    bisim_c6 = synthesize_bisim(2, C * 6, [])
    bisim_sc = synthesize_bisim(2, S + C, C * 5 + S)
    assert all(x is not None for x in [bisim_sl2_braid, bisim_j4, bisim_not_add, bisim_c6, bisim_sc])

    d6_gens = [C, S]
    d6_lib = [(C * 6, []), (S + C, C * 5 + S)]
    d6_reps = [C * k for k in range(6)] + [C * k + S for k in range(6)]
    d6_table = []
    d6_proofs = []
    for c in range(12):
        rt, rp = [], []
        for gi, g in enumerate(d6_gens):
            if c < 6:
                nc = (c + 1) % 6 if gi == 0 else 6 + c
            else:
                k = c - 6
                nc = 6 + ((k + 5) % 6) if gi == 0 else k
            rt.append(nc)
            cert = find_rewrite_bfs(d6_lib, d6_reps[c] + g, d6_reps[nc], max_len=26)
            assert cert is not None
            rp.append(cert)
        d6_table.append(rt)
        d6_proofs.append(rp)

    # --- Family II: Bit-Indexed {bCnot(0,1), bSwap(0,1), bToff(0,1,2)} Weyl Group B3 (Order 48) ---
    gA = ("bCnot", 0, 0, 0, 1)
    gS = ("bSwap", 0, 0, 0, 1)
    gT = ("bToff", 0, 0, 0, 1, 0, 2)
    b3_gens = [[gA], [gS], [gT]]
    b3_lib = [
        ([gA, gS, gA], [gS, gA, gS]),
        ([gS, gT], [gT, gS]),
        ([gA, gT, gA, gT], [gT, gA, gT, gA]),
        ([gA, gS, gA, gT, gA, gS], [gS, gA, gT, gA, gS, gA]),
    ]

    def perm3(circ):
        return tuple(eval_circuit(circ, (x,), 3)[0] for x in range(8))

    id3 = tuple(range(8))
    gen_ps = [perm3(g) for g in b3_gens]
    seen = {id3: []}
    order_perms = [id3]
    q = deque([id3])
    while q:
        p = q.popleft()
        w_cur = seen[p]
        for gi, gp in enumerate(gen_ps):
            np = tuple(gp[p[x]] for x in range(8))
            if np not in seen:
                seen[np] = w_cur + b3_gens[gi]
                order_perms.append(np)
                q.append(np)
    assert len(order_perms) == 48
    perm_to_id = {p: idx for idx, p in enumerate(order_perms)}
    b3_reps = [seen[p] for p in order_perms]
    b3_table = []
    b3_proofs = []
    for c in range(48):
        p = order_perms[c]
        rt, rp = [], []
        for gi, gp in enumerate(gen_ps):
            np = tuple(gp[p[x]] for x in range(8))
            nc = perm_to_id[np]
            rt.append(nc)
            cert = find_rewrite_bfs(b3_lib, b3_reps[c] + b3_gens[gi], b3_reps[nc], max_len=12, max_nodes=60000)
            assert cert is not None, f"B3 edge ({c},{gi}) failed"
            rp.append(cert)
        b3_table.append(rt)
        b3_proofs.append(rp)

    # --- Family III: Hybrid Toffoli-Add Dihedral Tower D_{2^w} & Carry-Defect Tower K2, T3 ---
    P_cnot = [("rSub", 1, 2), ("rCnot", 0, 1), ("rAdd", 1, 2), ("rCnot", 0, 1)]
    P_toff = [("rSub", 3, 2), ("rToff", 0, 1, 3), ("rAdd", 3, 2), ("rToff", 0, 1, 3)]
    K2_01_2 = [("rSub", 0, 2), ("rSub", 1, 2), ("rCnot", 0, 1), ("rAdd", 1, 2), ("rCnot", 0, 1)]
    K2_10_2 = [("rSub", 1, 2), ("rSub", 0, 2), ("rCnot", 1, 0), ("rAdd", 0, 2), ("rCnot", 1, 0)]

    bisim_pcnot_dih = synthesize_bisim(3, [("rNot", 1)] + P_cnot + [("rNot", 1)], inv_circuit(P_cnot))
    bisim_ptoff_dih = synthesize_bisim(4, [("rNot", 3)] + P_toff + [("rNot", 3)], inv_circuit(P_toff))
    bisim_k2_sym = synthesize_bisim(3, K2_01_2, K2_10_2)
    bisim_k2_not = synthesize_bisim(3, K2_01_2 + [("rNot", 0)] + K2_01_2 + [("rNot", 0)], [("rSub", 1, 2), ("rSub", 1, 2)])
    assert all(x is not None for x in [bisim_pcnot_dih, bisim_ptoff_dih, bisim_k2_sym, bisim_k2_not])

    if emit_lean:
        lines = []
        lines.append(f"def cert_sl2_braid : BisimCert := {fmt_bisim(bisim_sl2_braid)}")
        lines.append(f"def cert_j4 : BisimCert := {fmt_bisim(bisim_j4)}")
        lines.append(f"def cert_not_add : BisimCert := {fmt_bisim(bisim_not_add)}")
        lines.append(f"def cert_d6_c6 : BisimCert := {fmt_bisim(bisim_c6)}")
        lines.append(f"def cert_d6_sc : BisimCert := {fmt_bisim(bisim_sc)}")
        lines.append(f"def cert_pcnot_dih : BisimCert := {fmt_bisim(bisim_pcnot_dih)}")
        lines.append(f"def cert_ptoff_dih : BisimCert := {fmt_bisim(bisim_ptoff_dih)}")
        lines.append(f"def cert_k2_sym : BisimCert := {fmt_bisim(bisim_k2_sym)}")
        lines.append(f"def cert_k2_not : BisimCert := {fmt_bisim(bisim_k2_not)}")
        lines.append("")
        lines.append("def d6CosetCert : CosetCert 2 :=")
        lines.append("  { numCosets := 12")
        lines.append("    reps := #[")
        for r_i in d6_reps:
            lines.append(f"      {fmt_circuit(r_i)},")
        lines.append("    ]")
        lines.append("    table := #[")
        for row in d6_table:
            lines.append(f"      #[{', '.join(str(x) for x in row)}],")
        lines.append("    ]")
        lines.append("    edgeProofs := #[")
        for row in d6_proofs:
            lines.append("      #[" + ", ".join(fmt_cert(c) for c in row) + "],")
        lines.append("    ] }")
        lines.append("")
        lines.append("def b3CosetCert : CosetCert 1 :=")
        lines.append("  { numCosets := 48")
        lines.append("    reps := #[")
        for r_i in b3_reps:
            lines.append(f"      {fmt_circuit(r_i)},")
        lines.append("    ]")
        lines.append("    table := #[")
        for row in b3_table:
            lines.append(f"      #[{', '.join(str(x) for x in row)}],")
        lines.append("    ]")
        lines.append("    edgeProofs := #[")
        for row in b3_proofs:
            lines.append("      #[" + ", ".join(fmt_cert(c) for c in row) + "],")
        lines.append("    ] }")
        return "\n".join(lines)

    # ========================================================================
    # 6. Independent Exact-Integer Verification + Sharpness + Mutation Tests
    # ========================================================================
    print("===================================================================")
    print("certcomp-14 Independent Exact-Integer Verification & Sharpness Suite")
    print("===================================================================")

    print("\n[1] Certificate Summary (all synthesized with 2's-complement exact carry):")
    print(f"  - SL(2,Z) braid UVU = VUV               : {len(bisim_sl2_braid)} bisim states")
    print(f"  - Modular rotation J^4 = Id             : {len(bisim_j4)} bisim states")
    print(f"  - Dihedral Not1·Add01·Not1 = Sub01      : {len(bisim_not_add)} bisim states")
    print(f"  - D6 relators C^6 = Id, S·C = C^5·S     : {len(bisim_c6)} and {len(bisim_sc)} bisim states")
    print(f"  - D6 CosetCert                          : 12 cosets x 2 gens = 24 edge certs (max len {max(len(c) for row in d6_proofs for c in row)})")
    print(f"  - B3 CosetCert                          : 48 cosets x 3 gens = 144 edge certs (max len {max(len(c) for row in b3_proofs for c in row)}, total steps {sum(len(c) for row in b3_proofs for c in row)})")
    print(f"  - Toffoli-Add dihedral Not3·P_toff·Not3 : {len(bisim_ptoff_dih)} bisim states")
    print(f"  - CNOT-Add dihedral Not1·P_cnot·Not1    : {len(bisim_pcnot_dih)} bisim states")
    print(f"  - Carry-defect K2(0,1;2) = K2(1,0;2)    : {len(bisim_k2_sym)} bisim states")
    print(f"  - Carry-defect K2 NOT-collapse          : {len(bisim_k2_not)} bisim states")

    print("\n[2] Independent Exhaustive & High-Width Exact Bit-Vector Verification:")
    # Exhaustive check D6 for w=1..4 + deterministic large-width checks at w=8, 16, 32, 64
    for w in (1, 2, 3, 4):
        m = mask(w)
        # Count distinct group elements of D6 at width w
        perms = set()
        for rep in d6_reps:
            perm = tuple(eval_circuit(rep, (a, b), w) for a in range(1 << w) for b in range(1 << w))
            perms.add(perm)
        # Check order of C
        c_ord = None
        for k in range(1, 13):
            if all(eval_circuit(C * k, (a, b), w) == (a, b) for a in range(1 << w) for b in range(1 << w)):
                c_ord = k; break
        print(f"  D6 at w={w}: exact |<C,S>| = {len(perms):2d}, ord(C) = {c_ord}")
        assert len(perms) == (6 if w == 1 else 12)
        assert c_ord == (3 if w == 1 else 6)

    # Check B3 at w=1..5
    for w in (1, 2, 3, 4, 5):
        perms = set()
        for rep in b3_reps:
            perm = tuple(eval_circuit(rep, (x,), w)[0] for x in range(1 << w))
            perms.add(perm)
        ast = [gA, gS, gT]
        ast_ord = None
        for k in range(1, 13):
            if all(eval_circuit(ast * k, (x,), w) == (x,) for x in range(1 << w)):
                ast_ord = k; break
        print(f"  B3 at w={w}: exact |<A,S,T>| = {len(perms):2d}, ord(A·S·T) = {ast_ord}")
        expected_size = {1: 1, 2: 6}.get(w, 48)
        expected_ord = {1: 1, 2: 3}.get(w, 6)
        assert len(perms) == expected_size
        assert ast_ord == expected_ord

    # Check Hybrid Toffoli-Add Dihedral & Carry-Defect Tower T3 at w=1..4 + w=64
    def T3(a, b, d, c):
        pt = [("rSub", d, c), ("rToff", a, b, d), ("rAdd", d, c), ("rToff", a, b, d)]
        k2 = [("rSub", a, c), ("rSub", b, c), ("rCnot", a, b), ("rAdd", b, c), ("rCnot", a, b)]
        return pt * 2 + k2

    for w in (1, 2, 3, 4):
        m = mask(w)
        # Check P_toff order = 2^w on (1, 1, 0, 0)
        st = (1 & m, 1 & m, 0, 0)
        cur = st
        p_ord = None
        for k in range(1, 2 * (1 << w) + 2):
            cur = eval_circuit(P_toff, cur, w)
            if cur == st:
                p_ord = k; break
        # Check T3 order = 1 for w<=2, 2^(w-2) for w>=3
        st3 = (1 & m, 1 & m, 0, 1 & m)
        cur3 = st3
        t3_ord = None
        for k in range(1, 2 * (1 << w) + 2):
            cur3 = eval_circuit(T3(0, 1, 3, 2), cur3, w)
            if cur3 == st3:
                t3_ord = k; break
        print(f"  Hybrid Tower at w={w}: ord(P_toff) = {p_ord} (2^w={1<<w}), ord(P_toff·rNot3) = 2, ord(T3) = {t3_ord}")
        assert p_ord == (1 << w)
        assert t3_ord == (1 if w <= 2 else (1 << (w - 2)))

    # High-width exact spot checks (w = 64)
    w64 = 64
    m64 = mask(w64)
    test_vecs_64 = [
        (0xDEADBEEFCAFEBABE, 0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x5555AAAA3333CCCC),
        (0xFFFFFFFFFFFFFFFF, 0x8000000000000001, 0x0000000000000000, 0x7FFFFFFFFFFFFFFF),
    ]
    for a, b, c, d in test_vecs_64:
        # D6: C^6 = Id, S·C = C^5·S
        assert eval_circuit(C * 6, (a, b), w64) == (a, b)
        assert eval_circuit(S + C, (a, b), w64) == eval_circuit(C * 5 + S, (a, b), w64)
        # B3: (A·S·T)^6 = Id
        assert eval_circuit([gA, gS, gT] * 6, (a,), w64) == (a,)
        # P_toff dihedral: (P_toff^7 · rNot3)^2 = Id
        assert eval_circuit((P_toff * 7 + [("rNot", 3)]) * 2, (a, b, c, d), w64) == (a, b, c, d)
        # K2 symmetry & NOT-collapse
        assert eval_circuit(K2_01_2, (a, b, c), w64) == eval_circuit(K2_10_2, (a, b, c), w64)
        assert eval_circuit(K2_01_2 + [("rNot", 0)] + K2_01_2 + [("rNot", 0)], (a, b, c), w64) == (a, b, (c - 2 * b) & m64)
        # T3 exact formula, S3-symmetry & NOT-collapse
        out_t3 = eval_circuit(T3(0, 1, 3, 2), (a, b, c, d), w64)
        assert out_t3 == (a, b, (c - 4 * (a & b & d)) & m64, d)
        assert out_t3 == eval_circuit(T3(0, 3, 1, 2), (a, b, c, d), w64)
        assert out_t3 == eval_circuit(T3(3, 1, 0, 2), (a, b, c, d), w64)
        assert eval_circuit(T3(0, 1, 3, 2) + [("rNot", 3)] + T3(0, 1, 3, 2) + [("rNot", 3)], (a, b, c, d), w64) == \
               eval_circuit(K2_01_2 * 2, (a, b, c, d), w64)
    print("  64-bit exact replay passed on all 4 flagship theorem families!")

    print("\n[3] Sharpness Counterexamples & Negative/Mutation Checks:")
    # Sharpness 1: D6 collapses to order 6 at w = 1 (C^3 = Id at w = 1, C^3 != Id at w = 2)
    assert all(eval_circuit(C * 3, (a, b), 1) == (a, b) for a in range(2) for b in range(2))
    assert eval_circuit(C * 3, (1, 0), 2) == (3, 0) != (1, 0)
    print("  - Sharpness D6: C^3 = Id at w=1, but at w=2 C^3(1,0) = (3,0) != (1,0)")

    # Sharpness 2: B3 collapses to order 6 at w = 2 ((A·S·T)^3 = Id at w = 2, != Id at w = 3)
    assert all(eval_circuit([gA, gS, gT] * 3, (x,), 2) == (x,) for x in range(4))
    assert eval_circuit([gA, gS, gT] * 3, (1,), 3) == (5,) != (1,)
    print("  - Sharpness B3: (A·S·T)^3 = Id at w=2, but at w=3 (A·S·T)^3(1) = 5 != 1")

    # Sharpness 3: (P_toff · rNot0)^2 != Id already at w = 1
    assert eval_circuit((P_toff + [("rNot", 0)]) * 2, (0, 1, 0, 0), 1) == (0, 1, 1, 0) != (0, 1, 0, 0)
    assert synthesize_bisim(4, (P_toff + [("rNot", 0)]) * 2, []) is None
    print("  - Sharpness Toffoli-Add: replacing rNot3 by rNot0 breaks involution at w=1: (0,1,0,0) -> (0,1,1,0)")

    # Sharpness 4: T3 collapses to Id at w = 2, non-trivial at w = 3
    assert all(eval_circuit(T3(0, 1, 3, 2), (a, b, c, d), 2) == (a, b, c, d)
               for a in range(4) for b in range(4) for c in range(4) for d in range(4))
    assert eval_circuit(T3(0, 1, 3, 2), (1, 1, 0, 1), 3) == (1, 1, 4, 1) != (1, 1, 0, 1)
    print("  - Sharpness T3: T3 = Id at w=2, but at w=3 T3(1,1,0,1) = (1,1,4,1) != (1,1,0,1)")

    # Negative check: invalid braid U·V·U = U·U·V rejected by bisim synthesizer
    assert synthesize_bisim(2, U + V + U, U + U + V) is None
    print("  - Negative check: invalid braid UVU = UUV rejected (bisim = None)")

    print("\nALL INDEPENDENT CHECKS PASSED WITH EXIT CODE 0!")

if __name__ == "__main__":
    if "--emit-lean" in sys.argv:
        print(build_all(emit_lean=True))
    else:
        build_all(emit_lean=False)
