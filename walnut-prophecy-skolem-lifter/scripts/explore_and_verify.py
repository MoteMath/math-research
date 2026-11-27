"""
Pure-Silicon Walnut-Style Base-2 Automatic Predicate Decision-Certificate Synthesizer
& Exact Independent Verifier for the Gray-Sum Parity Word:

    w(n) = popcount(n + (n ^ (n >> 1))) mod 2

Strictly exact integer/boolean arithmetic (zero floating-point values anywhere).
"""

from collections import deque
import sys


# =============================================================================
# 1. Exact Binary Word Definitions & Non-Classicality Oracles
# =============================================================================

def popcount(n: int) -> int:
    return n.bit_count()

def gray_add_parity(n: int) -> int:
    """Non-classical 2-automatic binary word: popcount(n + (n ^ (n >> 1))) mod 2."""
    return popcount(n + (n ^ (n >> 1))) & 1

def thue_morse(n: int) -> int:
    return popcount(n) & 1

def rudin_shapiro(n: int) -> int:
    return popcount(n & (n >> 1)) & 1

def baum_sweet(n: int) -> int:
    if n == 0:
        return 1
    zeros = 0
    while n > 0:
        if (n & 1) == 0:
            zeros += 1
        else:
            if zeros % 2 == 1:
                return 0
            zeros = 0
        n >>= 1
    return 1

def period_doubling(n: int) -> int:
    # v_2(n + 1) mod 2
    m = n + 1
    v = 0
    while (m & 1) == 0:
        v += 1
        m >>= 1
    return v & 1

def thue_morse_3n(n: int) -> int:
    return popcount(3 * n) & 1


# =============================================================================
# 2. Exact Multi-Track LSB-First DFA Engine (Matching Proof.lean Semantics)
# =============================================================================

class DFA:
    """
    k-track LSB-first DFA with states 0..n-1 and input slices a in 0..(2^k - 1),
    where bit j of slice a is bit i of track j.
    """
    def __init__(self, k: int, num_states: int, init: int, trans: list[list[int]], accept: list[bool]):
        self.k = k
        self.n = num_states
        self.init = init
        self.trans = trans
        self.accept = accept

    def check_closed(self) -> bool:
        alpha = 1 << self.k
        if not (0 <= self.init < self.n):
            return False
        for q in range(self.n):
            for a in range(alpha):
                if not (0 <= self.trans[q][a] < self.n):
                    return False
        return True

    def check_pad_inv(self) -> bool:
        return all(self.accept[self.trans[q][0]] == self.accept[q] for q in range(self.n))

    def eval_tuple(self, xs: tuple[int, ...]) -> bool:
        assert len(xs) == self.k
        L = max((x.bit_length() for x in xs), default=0)
        q = self.init
        for i in range(L):
            a = 0
            for j, x in enumerate(xs):
                if (x >> i) & 1:
                    a |= (1 << j)
            q = self.trans[q][a]
        return self.accept[q]

    def complement(self) -> "DFA":
        return DFA(self.k, self.n, self.init, [row[:] for row in self.trans], [not b for b in self.accept])

    def reindex(self, new_k: int, mapping: list[int]) -> "DFA":
        assert len(mapping) == self.k
        new_alpha = 1 << new_k
        trans = [[0] * new_alpha for _ in range(self.n)]
        for a_new in range(new_alpha):
            a_old = 0
            for j_old, j_new in enumerate(mapping):
                if (a_new >> j_new) & 1:
                    a_old |= (1 << j_old)
            for q in range(self.n):
                trans[q][a_new] = self.trans[q][a_old]
        return DFA(new_k, self.n, self.init, trans, self.accept[:])

    def cartesian_product(self, other: "DFA", op) -> "DFA":
        """Exact Cartesian product with state index q1 * other.n + q2 (matches Lean dfaProd!)."""
        assert self.k == other.k
        alpha = 1 << self.k
        n2 = other.n
        total = self.n * n2
        init = self.init * n2 + other.init
        trans = [[0] * alpha for _ in range(total)]
        accept = [False] * total
        for q1 in range(self.n):
            for q2 in range(n2):
                q = q1 * n2 + q2
                accept[q] = bool(op(self.accept[q1], other.accept[q2]))
                for a in range(alpha):
                    trans[q][a] = self.trans[q1][a] * n2 + other.trans[q2][a]
        return DFA(self.k, total, init, trans, accept)

    def reachable_mask(self) -> tuple[int, list[int]]:
        alpha = 1 << self.k
        seen = {self.init}
        order = [self.init]
        dq = deque([self.init])
        while dq:
            u = dq.popleft()
            for a in range(alpha):
                v = self.trans[u][a]
                if v not in seen:
                    seen.add(v)
                    order.append(v)
                    dq.append(v)
        mask = 0
        for q in seen:
            mask |= (1 << q)
        return mask, order

    def minimize_with_hom(self) -> tuple["DFA", int, list[int]]:
        """
        Moore minimization of reachable states; returns (M_min, reach_mask, hom_list)
        where hom_list[q] = M_min state for every reachable q of self.
        """
        alpha = 1 << self.k
        reach_mask, reach_order = self.reachable_mask()
        reach_idx = {q: i for i, q in enumerate(reach_order)}
        rn = len(reach_order)
        rtrans = [[reach_idx[self.trans[u][a]] for a in range(alpha)] for u in reach_order]
        racc = [self.accept[u] for u in reach_order]

        cls = [1 if racc[i] else 0 for i in range(rn)]
        while True:
            sig_map = {}
            new_cls = [0] * rn
            for i in range(rn):
                sig = (cls[i], tuple(cls[rtrans[i][a]] for a in range(alpha)))
                if sig not in sig_map:
                    sig_map[sig] = len(sig_map)
                new_cls[i] = sig_map[sig]
            if len(sig_map) == len(set(cls)):
                cls = new_cls
                break
            cls = new_cls

        num_c = max(cls) + 1
        rep = {}
        for i, c in enumerate(cls):
            if c not in rep:
                rep[c] = i
        ctrans = [[cls[rtrans[rep[c]][a]] for a in range(alpha)] for c in range(num_c)]
        cacc = [racc[rep[c]] for c in range(num_c)]

        c0 = cls[0]
        cmap = {c0: 0}
        corder = [c0]
        dq = deque([c0])
        while dq:
            c = dq.popleft()
            for a in range(alpha):
                nc = ctrans[c][a]
                if nc not in cmap:
                    cmap[nc] = len(cmap)
                    corder.append(nc)
                    dq.append(nc)
        final_n = len(corder)
        ftrans = [[cmap[ctrans[c][a]] for a in range(alpha)] for c in corder]
        facc = [cacc[c] for c in corder]
        hom = [cmap[cls[reach_idx[q]]] if q in reach_idx else 0 for q in range(self.n)]
        return DFA(self.k, final_n, 0, ftrans, facc), reach_mask, hom

    def compute_zero_reach_cert(self) -> tuple[int, list[int], list[bool]]:
        """
        Compute BFS shortest-path ZeroReachCert for (k+1)-track DFA:
        returns (zAccMask, zRank, zBit).
        """
        assert self.k >= 1
        rank = [None] * self.n
        bit = [False] * self.n
        dq = deque()
        for q in range(self.n):
            if self.accept[q]:
                rank[q] = 0
                dq.append(q)
        # Reverse edges on slice 0 (b=false) and slice 1 (b=true)
        rev = [[] for _ in range(self.n)]
        for q in range(self.n):
            rev[self.trans[q][0]].append((q, False))
            rev[self.trans[q][1]].append((q, True))
        while dq:
            q_nxt = dq.popleft()
            for q_prev, b in rev[q_nxt]:
                if rank[q_prev] is None:
                    rank[q_prev] = rank[q_nxt] + 1
                    bit[q_prev] = b
                    dq.append(q_prev)
        z_mask = 0
        z_rank = [0] * self.n
        for q in range(self.n):
            if rank[q] is not None:
                z_mask |= (1 << q)
                z_rank[q] = rank[q]
        return z_mask, z_rank, bit

    def exists_track0_with_cert(self) -> tuple["DFA", dict]:
        """
        Forward subset determinization for `exists y, M(y, x)` producing a pure-data ExistsCert.
        """
        assert self.k >= 1
        new_k = self.k - 1
        new_alpha = 1 << new_k
        z_mask, z_rank, z_bit = self.compute_zero_reach_cert()

        init_set = frozenset([self.init])
        idx = {init_set: 0}
        order = [init_set]
        dq = deque([init_set])
        trans = []
        accept = []
        acc_wit = []
        back_wit = {}  # (u * new_alpha + a) -> list of (q, b) for each q' in 0..self.n-1

        while dq:
            S = dq.popleft()
            u = idx[S]
            row = []
            for a_new in range(new_alpha):
                a0 = 2 * a_new
                a1 = 2 * a_new + 1
                nxt = set()
                bw = [(0, False)] * self.n
                for q in sorted(S):
                    q0 = self.trans[q][a0]
                    q1 = self.trans[q][a1]
                    if q0 not in nxt:
                        nxt.add(q0)
                        bw[q0] = (q, False)
                    if q1 not in nxt:
                        nxt.add(q1)
                        bw[q1] = (q, True)
                nxt_f = frozenset(nxt)
                if nxt_f not in idx:
                    idx[nxt_f] = len(order)
                    order.append(nxt_f)
                    dq.append(nxt_f)
                row.append(idx[nxt_f])
                back_wit[u * new_alpha + a_new] = bw
            trans.append(row)
            wit = next((q for q in sorted(S) if (z_mask >> q) & 1), None)
            if wit is not None:
                accept.append(True)
                acc_wit.append(wit)
            else:
                accept.append(False)
                acc_wit.append(0)

        D = DFA(new_k, len(order), 0, trans, accept)
        sub_masks = []
        for S in order:
            m = 0
            for q in S:
                m |= (1 << q)
            sub_masks.append(m)
        cert = {
            "sub_masks": sub_masks,
            "z_mask": z_mask,
            "z_rank": z_rank,
            "z_bit": z_bit,
            "acc_wit": acc_wit,
            "back_wit": back_wit,
        }
        return D, cert


# =============================================================================
# 3. Primitive DFAs (Exact Match to Proof.lean Sections 4, 6, 7)
# =============================================================================

def dfa_le() -> DFA:
    return DFA(2, 2, 0, [[0, 1, 0, 0], [1, 1, 0, 1]], [True, False])

def dfa_lt() -> DFA:
    return DFA(2, 2, 0, [[0, 0, 1, 0], [1, 0, 1, 1]], [False, True])

def dfa_add() -> DFA:
    trans = [[2] * 8 for _ in range(3)]
    for c in (0, 1):
        for a in range(8):
            bx = a & 1
            by = (a >> 1) & 1
            bz = (a >> 2) & 1
            s = bx + by + c
            trans[c][a] = (s >> 1) if (s & 1) == bz else 2
    return DFA(3, 3, 0, trans, [True, False, False])

def dfa_add_one() -> DFA:
    """Tracks (y, x): x + 1 = y. Matches Proof.lean `dfaAddOne` exactly."""
    trans = [[2] * 4 for _ in range(3)]
    for q in (0, 1):
        c = 1 if q == 0 else 0
        for a in range(4):
            by = a & 1
            bx = (a >> 1) & 1
            s = bx + c
            if (s & 1) == by:
                trans[q][a] = 0 if (s >> 1) == 1 else 1
            else:
                trans[q][a] = 2
    return DFA(2, 3, 0, trans, [False, True, False])

def dfa_p_ge_pow2_rev(e: int) -> DFA:
    """Matches Proof.lean `dfaPGePow2Rev e` exactly."""
    n_st = e + 2
    trans = []
    for s in range(n_st):
        row = []
        for a in range(4):
            bp = (a >> 1) & 1
            if s == 0:
                ns = 1 if bp == 1 else 0
            elif s < e + 1:
                ns = s + 1
            else:
                ns = e + 1
            row.append(ns)
        trans.append(row)
    acc = [s == e + 1 for s in range(n_st)]
    return DFA(2, n_st, 0, trans, acc)

def dfa_gray_add() -> DFA:
    """Matches Proof.lean `dfaGrayAdd` exactly (9 states)."""
    trans = []
    acc = []
    for q in range(9):
        row = []
        for b in (0, 1):
            if q == 0:
                row.append(1 + 4 * b)
            else:
                idx = q - 1
                pb = (idx // 4) % 2
                c = (idx // 2) % 2
                p = idx % 2
                s = pb + (pb ^ b) + c
                row.append(1 + 4 * b + 2 * (s // 2) + (p ^ (s % 2)))
        trans.append(row)
        if q == 0:
            acc.append(False)
        else:
            idx = q - 1
            pb = (idx // 4) % 2
            c = (idx // 2) % 2
            p = idx % 2
            acc.append((p ^ c ^ pb) == 1)
    return DFA(1, 9, 0, trans, acc)


# =============================================================================
# 4. Backward-Prophecy Synthesizer + CEGAR Compressor + Sparse Pruner
# =============================================================================

def synthesize_prophecy_cert(M: DFA, P_rev: DFA, max_cegar_splits: int = 200) -> dict:
    """
    Synthesize a compact pure-data ProphecyCert (B, invMask, activeQ, zCert, reachPairs, reachMask)
    certifying: forall x, P_rev(x^rev) -> exists y, M(y, x).
    """
    k = M.k - 1
    alpha = 1 << k
    z_mask, z_rank, z_bit = M.compute_zero_reach_cert()

    # 1. Exact backward winning-set DFA B_raw
    init_T = frozenset(q for q in range(M.n) if (z_mask >> q) & 1)
    idx = {init_T: 0}
    order = [init_T]
    dq = deque([init_T])
    b_trans = []
    b_acc = []
    while dq:
        T = dq.popleft()
        row = []
        for a in range(alpha):
            a0 = 2 * a
            a1 = 2 * a + 1
            nxt = frozenset(q for q in range(M.n) if (M.trans[q][a0] in T) or (M.trans[q][a1] in T))
            if nxt not in idx:
                idx[nxt] = len(order)
                order.append(nxt)
                dq.append(nxt)
            row.append(idx[nxt])
        b_trans.append(row)
        b_acc.append(M.init in T)
    B_raw = DFA(k, len(order), 0, b_trans, b_acc)
    T_sets = order

    # 2. CEGAR Quotient Compression starting from Moore-minimized B_raw
    B_min, _, hom = B_raw.minimize_with_hom()
    cls = hom[:]

    def build_quotient(cls_list: list[int]) -> tuple[DFA, list[int]]:
        c = cls_list[:]
        while True:
            sig_map = {}
            nc = [0] * B_raw.n
            for r in range(B_raw.n):
                sig = (c[r], tuple(c[B_raw.trans[r][a]] for a in range(alpha)))
                if sig not in sig_map:
                    sig_map[sig] = len(sig_map)
                nc[r] = sig_map[sig]
            if len(sig_map) == len(set(c)):
                c = nc
                break
            c = nc
        num_c = max(c) + 1
        rep = {}
        for r, ci in enumerate(c):
            if ci not in rep:
                rep[ci] = r
        # Canonical BFS numbering from init class
        c0 = c[B_raw.init]
        cmap = {c0: 0}
        corder = [c0]
        dq2 = deque([c0])
        while dq2:
            ci = dq2.popleft()
            for a in range(alpha):
                nci = c[B_raw.trans[rep[ci]][a]]
                if nci not in cmap:
                    cmap[nci] = len(cmap)
                    corder.append(nci)
                    dq2.append(nci)
        q_trans = [[cmap[c[B_raw.trans[rep[ci]][a]]] for a in range(alpha)] for ci in corder]
        q_acc = [B_raw.accept[rep[ci]] for ci in corder]
        c_renum = [cmap[ci] for ci in c]
        return DFA(k, len(corder), 0, q_trans, q_acc), c_renum

    def check_gfp(Q: DFA):
        I = [[True] * Q.n for _ in range(M.n)]
        for q in range(M.n):
            I[q][Q.init] = bool((z_mask >> q) & 1)
        rev_edges = [[] for _ in range(Q.n)]
        for rp in range(Q.n):
            for a in range(alpha):
                rev_edges[Q.trans[rp][a]].append((rp, a))
        changed = True
        while changed:
            changed = False
            for q in range(M.n):
                for r in range(Q.n):
                    if I[q][r]:
                        for rp, a in rev_edges[r]:
                            if not (I[M.trans[q][2 * a]][rp] or I[M.trans[q][2 * a + 1]][rp]):
                                I[q][r] = False
                                changed = True
                                break
        vis = {(Q.init, P_rev.init)}
        dq2 = deque([(Q.init, P_rev.init)])
        bad_ci = None
        while dq2:
            r, s = dq2.popleft()
            if P_rev.accept[s] and not I[M.init][r]:
                bad_ci = r
                break
            for a in range(alpha):
                nxt = (Q.trans[r][a], P_rev.trans[s][a])
                if nxt not in vis:
                    vis.add(nxt)
                    dq2.append(nxt)
        return (bad_ci is None), bad_ci, I

    Q_final = None
    I_gfp = None
    cegar_splits = 0
    for step in range(max_cegar_splits):
        Q, c = build_quotient(cls)
        ok, bad_ci, I = check_gfp(Q)
        if ok:
            Q_final = Q
            I_gfp = I
            cegar_splits = step
            break
        members = [[] for _ in range(Q.n)]
        for r, ci in enumerate(c):
            members[ci].append(r)
        rev_q = [[] for _ in range(Q.n)]
        for cp in range(Q.n):
            for a in range(alpha):
                rev_q[Q.trans[cp][a]].append((cp, a))
        seen = {(bad_ci, M.init)}
        fq = deque([(bad_ci, M.init)])
        split_done = False
        while fq and not split_done:
            ci, q = fq.popleft()
            in_t = [r for r in members[ci] if q in T_sets[r]]
            out_t = [r for r in members[ci] if q not in T_sets[r]]
            if in_t and out_t:
                new_id = max(c) + 1
                for r in out_t:
                    c[r] = new_id
                cls = c
                split_done = True
                break
            for cp, a in rev_q[ci]:
                q0 = M.trans[q][2 * a]
                q1 = M.trans[q][2 * a + 1]
                if not I[q0][cp] and not I[q1][cp]:
                    for qn in (q0, q1):
                        if (cp, qn) not in seen:
                            seen.add((cp, qn))
                            fq.append((cp, qn))
        assert split_done, f"CEGAR stuck at step {step}"
    assert Q_final is not None, "CEGAR exceeded max_cegar_splits"

    # 3. Sparse Needed-Set Pruning on Q_final
    vis = {(Q_final.init, P_rev.init)}
    dq3 = deque([(Q_final.init, P_rev.init)])
    while dq3:
        r, s = dq3.popleft()
        for a in range(alpha):
            nxt = (Q_final.trans[r][a], P_rev.trans[s][a])
            if nxt not in vis:
                vis.add(nxt)
                dq3.append(nxt)

    rev_q = [[] for _ in range(Q_final.n)]
    for rp in range(Q_final.n):
        for a in range(alpha):
            rev_q[Q_final.trans[rp][a]].append((rp, a))

    need = [set() for _ in range(Q_final.n)]
    work = deque()
    for r, s in sorted(vis):
        if P_rev.accept[s]:
            assert I_gfp[M.init][r]
            if M.init not in need[r]:
                need[r].add(M.init)
                work.append((r, M.init))
    while work:
        r, q = work.popleft()
        for rp, a in rev_q[r]:
            q0 = M.trans[q][2 * a]
            q1 = M.trans[q][2 * a + 1]
            ok0 = I_gfp[q0][rp]
            ok1 = I_gfp[q1][rp]
            assert ok0 or ok1
            if ok0 and (q0 in need[rp]):
                chosen = q0
            elif ok1 and (q1 in need[rp]):
                chosen = q1
            elif ok0:
                chosen = q0
            else:
                chosen = q1
            if chosen not in need[rp]:
                need[rp].add(chosen)
                work.append((rp, chosen))

    active_q = [sorted(need[r]) for r in range(Q_final.n)]
    inv_mask = []
    for qs in active_q:
        m = 0
        for q in qs:
            m |= (1 << q)
        inv_mask.append(m)

    reach_rows = [0] * Q_final.n
    for r, s in vis:
        reach_rows[r] |= (1 << s)

    return {
        "B": Q_final,
        "B_raw_n": B_raw.n,
        "cegar_splits": cegar_splits,
        "inv_mask": inv_mask,
        "active_q": active_q,
        "z_mask": z_mask,
        "z_rank": z_rank,
        "z_bit": z_bit,
        "reach_rows": reach_rows,
    }


# =============================================================================
# 5. Exact Python Mirrors of Lean Certificate Checkers (Zero Trust Verification)
# =============================================================================

def verify_hom_cert(M1: DFA, M2: DFA, reach_mask: int, hom: list[int]) -> bool:
    alpha = 1 << M1.k
    if not (0 <= M1.init < M1.n and 0 <= M2.init < M2.n):
        return False
    if not ((reach_mask >> M1.init) & 1) or hom[M1.init] != M2.init:
        return False
    for q in range(M1.n):
        if (reach_mask >> q) & 1:
            hq = hom[q]
            if not (0 <= hq < M2.n) or M1.accept[q] != M2.accept[hq]:
                return False
            for a in range(alpha):
                q2 = M1.trans[q][a]
                if not (0 <= q2 < M1.n) or not ((reach_mask >> q2) & 1):
                    return False
                if hom[q2] != M2.trans[hq][a]:
                    return False
    return True

def verify_zero_reach_sound(M: DFA, z_mask: int, z_rank: list[int], z_bit: list[bool]) -> bool:
    for q in range(M.n):
        if (z_mask >> q) & 1:
            if not M.accept[q]:
                b = 1 if z_bit[q] else 0
                q2 = M.trans[q][b]
                if not (0 <= q2 < M.n) or not ((z_mask >> q2) & 1) or not (z_rank[q2] < z_rank[q]):
                    return False
    return True

def verify_zero_reach_complete(M: DFA, z_mask: int) -> bool:
    for q in range(M.n):
        if M.accept[q] and not ((z_mask >> q) & 1):
            return False
        if ((z_mask >> M.trans[q][0]) & 1) and not ((z_mask >> q) & 1):
            return False
        if ((z_mask >> M.trans[q][1]) & 1) and not ((z_mask >> q) & 1):
            return False
    return True

def verify_exists_cert(M: DFA, D: DFA, cert: dict) -> bool:
    alpha = 1 << D.k
    if not (0 <= M.init < M.n and 0 <= D.init < D.n):
        return False
    if not verify_zero_reach_sound(M, cert["z_mask"], cert["z_rank"], cert["z_bit"]):
        return False
    if not verify_zero_reach_complete(M, cert["z_mask"]):
        return False
    if cert["sub_masks"][D.init] != (1 << M.init):
        return False
    for u in range(D.n):
        mu = cert["sub_masks"][u]
        if D.accept[u]:
            q = cert["acc_wit"][u]
            if not (0 <= q < M.n and ((mu >> q) & 1) and ((cert["z_mask"] >> q) & 1)):
                return False
        else:
            for q in range(M.n):
                if ((mu >> q) & 1) and ((cert["z_mask"] >> q) & 1):
                    return False
        for a in range(alpha):
            u2 = D.trans[u][a]
            if not (0 <= u2 < D.n):
                return False
            mu2 = cert["sub_masks"][u2]
            bw = cert["back_wit"][u * alpha + a]
            for q in range(M.n):
                if (mu >> q) & 1:
                    q0 = M.trans[q][2 * a]
                    q1 = M.trans[q][2 * a + 1]
                    if not (0 <= q0 < M.n and 0 <= q1 < M.n and ((mu2 >> q0) & 1) and ((mu2 >> q1) & 1)):
                        return False
            for q2 in range(M.n):
                if (mu2 >> q2) & 1:
                    q, b = bw[q2]
                    if not (0 <= q < M.n and ((mu >> q) & 1) and M.trans[q][(1 if b else 0) + 2 * a] == q2):
                        return False
    return True

def verify_prophecy_cert(M: DFA, P_rev: DFA, cert: dict) -> bool:
    B = cert["B"]
    alpha = 1 << B.k
    np_ = P_rev.n
    if not (0 <= M.init < M.n and 0 <= B.init < B.n and 0 <= P_rev.init < np_):
        return False
    if not verify_zero_reach_sound(M, cert["z_mask"], cert["z_rank"], cert["z_bit"]):
        return False
    for r in range(B.n):
        m = 0
        for q in cert["active_q"][r]:
            if not (0 <= q < M.n):
                return False
            m |= (1 << q)
        if m != cert["inv_mask"][r]:
            return False
    for q in cert["active_q"][B.init]:
        if not ((cert["z_mask"] >> q) & 1):
            return False
    for rp in range(B.n):
        mp = cert["inv_mask"][rp]
        for a in range(alpha):
            r = B.trans[rp][a]
            if not (0 <= r < B.n):
                return False
            for q in cert["active_q"][r]:
                q0 = M.trans[q][2 * a]
                q1 = M.trans[q][2 * a + 1]
                if not (((mp >> q0) & 1) or ((mp >> q1) & 1)):
                    return False
    if not ((cert["reach_rows"][B.init] >> P_rev.init) & 1):
        return False
    for r in range(B.n):
        r_mask = cert["reach_rows"][r]
        for s in range(np_):
            if (r_mask >> s) & 1:
                if P_rev.accept[s] and not ((cert["inv_mask"][r] >> M.init) & 1):
                    return False
                for a in range(alpha):
                    r2 = B.trans[r][a]
                    s2 = P_rev.trans[s][a]
                    if not (0 <= r2 < B.n and 0 <= s2 < np_ and ((cert["reach_rows"][r2] >> s2) & 1)):
                        return False
    return True

def verify_universal_cert(M: DFA, reach_mask: int, target: bool) -> bool:
    alpha = 1 << M.k
    if not (0 <= M.init < M.n and ((reach_mask >> M.init) & 1)):
        return False
    for q in range(M.n):
        if (reach_mask >> q) & 1:
            if M.accept[q] != target:
                return False
            for a in range(alpha):
                q2 = M.trans[q][a]
                if not (0 <= q2 < M.n and ((reach_mask >> q2) & 1)):
                    return False
    return True


# =============================================================================
# 6. Full Pipeline Synthesis + Lean Code Emitter
# =============================================================================

def btree_depth(n: int) -> int:
    d = 0
    while (1 << d) < max(n, 1):
        d += 1
    return d

def emit_btree(values: list[str], depth: int, default: str) -> str:
    """Emit a compressed balanced binary trie matching Lean's `BTree.get` (LSB bit branching!).
    Identical-leaf subtrees collapse to a single `(.leaf v)` because `BTree.get (.leaf v) _ _ = v`."""
    def rec(d: int, base: int, stride: int) -> str:
        if d == 0:
            v = values[base] if base < len(values) else default
            return f"(.leaf {v})"
        l = rec(d - 1, base, stride * 2)
        r = rec(d - 1, base + stride, stride * 2)
        if l == r and l.startswith("(.leaf "):
            return l
        return f"(.node {l} {r})"
    return rec(depth, 0, 1)

def emit_dfa_def(name: str, D: DFA) -> str:
    """Emit a pure-data `DFA k` with bit-packed per-state transition rows (8-bit slots if n <= 255)."""
    alpha = 1 << D.k
    bits = 8 if D.n <= 255 else 16
    mask = (1 << bits) - 1
    row_vals = []
    for q in range(D.n):
        packed = 0
        for a in range(alpha):
            packed |= (D.trans[q][a] << (bits * a))
        row_vals.append(str(packed))
    td = btree_depth(D.n)
    acc_mask = 0
    for q in range(D.n):
        if D.accept[q]:
            acc_mask |= (1 << q)
    lines = []
    lines.append(f"private def {name}_rows : BTree Nat :=")
    lines.append(f"  {emit_btree(row_vals, td, '0')}")
    lines.append(f"def {name} : DFA {D.k} where")
    lines.append(f"  numStates := {D.n}")
    lines.append(f"  init := {D.init}")
    lines.append(f"  step := fun q a => ({name}_rows.get {td} q >>> ({bits} * a)) &&& {mask}")
    lines.append(f"  accept := fun q => ({acc_mask} : Nat).testBit q")
    return "\n".join(lines)

def emit_hom_cert(name: str, reach_mask: int, hom: list[int]) -> str:
    hd = btree_depth(len(hom))
    tree = emit_btree([str(x) for x in hom], hd, "0")
    return "\n".join([
        f"def {name} : HomCert where",
        f"  reachMask := {reach_mask}",
        f"  homTree := {tree}",
        f"  homDepth := {hd}",
    ])

def emit_zcert(z_mask: int, z_rank: list[int], z_bit: list[bool]) -> str:
    d = btree_depth(len(z_rank))
    rt = emit_btree([str(x) for x in z_rank], d, "0")
    bt = emit_btree(["true" if b else "false" for b in z_bit], d, "false")
    return f"{{ zAccMask := {z_mask}, zRank := {rt}, zBit := {bt}, depth := {d} }}"

def emit_exists_cert(name: str, M: DFA, D: DFA, cert: dict) -> str:
    alpha = 1 << D.k
    sd = btree_depth(D.n)
    ed = btree_depth(D.n * alpha)
    sub_tree = emit_btree([str(m) for m in cert["sub_masks"]], sd, "0")
    acc_tree = emit_btree([str(w) for w in cert["acc_wit"]], sd, "0")
    bw_packed = []
    for edge in range(D.n * alpha):
        bw = cert["back_wit"][edge]
        packed = 0
        for q2, (q, b) in enumerate(bw):
            slot = (q << 1) | (1 if b else 0)
            packed |= (slot << (16 * q2))
        bw_packed.append(str(packed))
    bw_tree = emit_btree(bw_packed, ed, "0")
    zc = emit_zcert(cert["z_mask"], cert["z_rank"], cert["z_bit"])
    return "\n".join([
        f"private def {name}_backWit : BTree Nat :=",
        f"  {bw_tree}",
        f"def {name} : ExistsCert where",
        f"  subMask := {sub_tree}",
        f"  subDepth := {sd}",
        f"  zCert := {zc}",
        f"  accWit := {acc_tree}",
        f"  backWit := {name}_backWit",
        f"  edgeDepth := {ed}",
    ])

def emit_prophecy_cert(name: str, M: DFA, cert: dict) -> str:
    B = cert["B"]
    bd = btree_depth(B.n)
    inv_tree = emit_btree([str(m) for m in cert["inv_mask"]], bd, "0")
    act_vals = ["[" + ", ".join(str(q) for q in qs) + "]" for qs in cert["active_q"]]
    act_tree = emit_btree(act_vals, bd, "[]")
    rr_tree = emit_btree([str(m) for m in cert["reach_rows"]], bd, "0")
    zc = emit_zcert(cert["z_mask"], cert["z_rank"], cert["z_bit"])
    return "\n".join([
        emit_dfa_def(f"{name}_B", B),
        f"private def {name}_invMask : BTree Nat :=",
        f"  {inv_tree}",
        f"private def {name}_activeQ : BTree (List Nat) :=",
        f"  {act_tree}",
        f"private def {name}_reachRow : BTree Nat :=",
        f"  {rr_tree}",
        f"def {name} : ProphecyCert {B.k} where",
        f"  B := {name}_B",
        f"  invMask := {name}_invMask",
        f"  activeQ := {name}_activeQ",
        f"  reachRow := {name}_reachRow",
        f"  bDepth := {bd}",
        f"  zCert := {zc}",
    ])


def build_all_certificates():
    """Synthesize and verify every certificate in the complete proof chain."""
    w = dfa_gray_add()
    le = dfa_le()
    lt = dfa_lt()
    add = dfa_add()
    add1 = dfa_add_one()

    # Stage A: E(u, p) := w(u) = w(u + p)
    # Tracks (v, u, p): add(u, p, v) /\ (w(u) == w(v))
    M_eq3_raw = add.reindex(3, [1, 2, 0]).cartesian_product(
        w.reindex(3, [1]).cartesian_product(w.reindex(3, [0]), lambda a, b: a == b),
        lambda a, b: a and b
    )
    M_eq3_min, rm_eq3, hom_eq3 = M_eq3_raw.minimize_with_hom()
    assert verify_hom_cert(M_eq3_raw, M_eq3_min, rm_eq3, hom_eq3)
    D_eqShift_raw, cert_eqShift = M_eq3_min.exists_track0_with_cert()
    assert verify_exists_cert(M_eq3_min, D_eqShift_raw, cert_eqShift)
    # Note: D_eqShift_raw already has 45 states (already minimal!)
    D_eqShift, rm_eqShift, hom_eqShift = D_eqShift_raw.minimize_with_hom()
    assert D_eqShift_raw.n == D_eqShift.n

    # Stage B: LtAdd(u, n, p) := exists m, (n + p = m /\ u < m)
    # Tracks (m, u, n, p)
    M_lt4 = add.reindex(4, [2, 3, 0]).cartesian_product(lt.reindex(4, [1, 0]), lambda a, b: a and b)
    D_ltAdd_raw, cert_ltAdd = M_lt4.exists_track0_with_cert()
    assert verify_exists_cert(M_lt4, D_ltAdd_raw, cert_ltAdd)
    D_ltAdd, rm_ltAdd, hom_ltAdd = D_ltAdd_raw.minimize_with_hom()
    assert verify_hom_cert(D_ltAdd_raw, D_ltAdd, rm_ltAdd, hom_ltAdd)

    # Stage C: LtAdd2(u, n, p) := exists t, (p + p = t /\ u < n + t)
    # Tracks (t, u, n, p)
    M_lt2_4 = add.reindex(4, [3, 3, 0]).cartesian_product(D_ltAdd.reindex(4, [1, 2, 0]), lambda a, b: a and b)
    D_ltAdd2_raw, cert_ltAdd2 = M_lt2_4.exists_track0_with_cert()
    assert verify_exists_cert(M_lt2_4, D_ltAdd2_raw, cert_ltAdd2)
    D_ltAdd2, rm_ltAdd2, hom_ltAdd2 = D_ltAdd2_raw.minimize_with_hom()
    assert verify_hom_cert(D_ltAdd2_raw, D_ltAdd2, rm_ltAdd2, hom_ltAdd2)

    # Stage D: NoSquare (p >= 8)
    # Tracks (u, n, p): (n <= u /\ u < n + p) /\ w(u) != w(u + p)
    M_sq_raw = le.reindex(3, [1, 0]).cartesian_product(D_ltAdd, lambda a, b: a and b).cartesian_product(
        D_eqShift_raw.reindex(3, [0, 2]).complement(), lambda a, b: a and b
    )
    M_sq_min, rm_sq, hom_sq = M_sq_raw.minimize_with_hom()
    assert verify_hom_cert(M_sq_raw, M_sq_min, rm_sq, hom_sq)
    P8 = dfa_p_ge_pow2_rev(3)
    cert_prop_sq8 = synthesize_prophecy_cert(M_sq_min, P8)
    assert verify_prophecy_cert(M_sq_min, P8, cert_prop_sq8)

    # Stage E: NoCube (p >= 2)
    # Tracks (u, n, p): (n <= u /\ u < n + 2*p) /\ w(u) != w(u + p)
    M_cu_raw = le.reindex(3, [1, 0]).cartesian_product(D_ltAdd2, lambda a, b: a and b).cartesian_product(
        D_eqShift_raw.reindex(3, [0, 2]).complement(), lambda a, b: a and b
    )
    M_cu_min, rm_cu, hom_cu = M_cu_raw.minimize_with_hom()
    assert verify_hom_cert(M_cu_raw, M_cu_min, rm_cu, hom_cu)
    P2 = dfa_p_ge_pow2_rev(1)
    cert_prop_cu2 = synthesize_prophecy_cert(M_cu_min, P2)
    assert verify_prophecy_cert(M_cu_min, P2, cert_prop_cu2)

    # Stage F: No5Run (p = 1): w(n) = w(n+1) = w(n+2) = w(n+3) = w(n+4) is impossible!
    # Shift w four times: w_k(n) := exists y, (n + 1 = y /\ w_{k-1}(y))
    shifts = []
    cur_w = w
    for step_idx in range(1, 5):
        raw_pair = add1.cartesian_product(cur_w.reindex(2, [0]), lambda a, b: a and b)
        proj_raw, cert_ex = raw_pair.exists_track0_with_cert()
        assert verify_exists_cert(raw_pair, proj_raw, cert_ex)
        proj_min, rm_sh, hom_sh = proj_raw.minimize_with_hom()
        assert verify_hom_cert(proj_raw, proj_min, rm_sh, hom_sh)
        shifts.append((raw_pair, proj_raw, cert_ex, proj_min, rm_sh, hom_sh))
        cur_w = proj_min

    # Intersect w(n) == w(n+k) for k = 1, 2, 3, 4 with intermediate HomCert compressions
    w0 = w
    w1, w2, w3, w4 = [s[3] for s in shifts]
    # R1 = (w0 == w1)
    R1_raw = w0.cartesian_product(w1, lambda a, b: a == b)
    R1_min, rm_r1, hom_r1 = R1_raw.minimize_with_hom()
    assert verify_hom_cert(R1_raw, R1_min, rm_r1, hom_r1)
    # E02 = (w0 == w2) -> R2 = R1_min /\ E02
    E02_raw = w0.cartesian_product(w2, lambda a, b: a == b)
    E02_min, rm_e02, hom_e02 = E02_raw.minimize_with_hom()
    assert verify_hom_cert(E02_raw, E02_min, rm_e02, hom_e02)
    R2_raw = R1_min.cartesian_product(E02_min, lambda a, b: a and b)
    R2_min, rm_r2, hom_r2 = R2_raw.minimize_with_hom()
    assert verify_hom_cert(R2_raw, R2_min, rm_r2, hom_r2)
    # E03 = (w0 == w3) -> R3 = R2_min /\ E03
    E03_raw = w0.cartesian_product(w3, lambda a, b: a == b)
    E03_min, rm_e03, hom_e03 = E03_raw.minimize_with_hom()
    assert verify_hom_cert(E03_raw, E03_min, rm_e03, hom_e03)
    R3_raw = R2_min.cartesian_product(E03_min, lambda a, b: a and b)
    R3_min, rm_r3, hom_r3 = R3_raw.minimize_with_hom()
    assert verify_hom_cert(R3_raw, R3_min, rm_r3, hom_r3)
    # E04 = (w0 == w4) -> R4 = R3_min /\ E04 -> UniversalCert(target=False)!
    E04_raw = w0.cartesian_product(w4, lambda a, b: a == b)
    E04_min, rm_e04, hom_e04 = E04_raw.minimize_with_hom()
    assert verify_hom_cert(E04_raw, E04_min, rm_e04, hom_e04)
    R4_raw = R3_min.cartesian_product(E04_min, lambda a, b: a and b)
    rm_r4, _ = R4_raw.reachable_mask()
    assert verify_universal_cert(R4_raw, rm_r4, False)

    return {
        "M_eq3_raw": M_eq3_raw, "M_eq3_min": M_eq3_min, "rm_eq3": rm_eq3, "hom_eq3": hom_eq3,
        "D_eqShift": D_eqShift_raw, "cert_eqShift": cert_eqShift,
        "M_lt4": M_lt4, "D_ltAdd_raw": D_ltAdd_raw, "cert_ltAdd": cert_ltAdd,
        "D_ltAdd": D_ltAdd, "rm_ltAdd": rm_ltAdd, "hom_ltAdd": hom_ltAdd,
        "M_lt2_4": M_lt2_4, "D_ltAdd2_raw": D_ltAdd2_raw, "cert_ltAdd2": cert_ltAdd2,
        "D_ltAdd2": D_ltAdd2, "rm_ltAdd2": rm_ltAdd2, "hom_ltAdd2": hom_ltAdd2,
        "M_sq_raw": M_sq_raw, "M_sq_min": M_sq_min, "rm_sq": rm_sq, "hom_sq": hom_sq,
        "cert_prop_sq8": cert_prop_sq8,
        "M_cu_raw": M_cu_raw, "M_cu_min": M_cu_min, "rm_cu": rm_cu, "hom_cu": hom_cu,
        "cert_prop_cu2": cert_prop_cu2,
        "shifts": shifts,
        "R1_min": R1_min, "rm_r1": rm_r1, "hom_r1": hom_r1,
        "E02_min": E02_min, "rm_e02": rm_e02, "hom_e02": hom_e02,
        "R2_min": R2_min, "rm_r2": rm_r2, "hom_r2": hom_r2,
        "E03_min": E03_min, "rm_e03": rm_e03, "hom_e03": hom_e03,
        "R3_min": R3_min, "rm_r3": rm_r3, "hom_r3": hom_r3,
        "E04_min": E04_min, "rm_e04": rm_e04, "hom_e04": hom_e04,
        "R4_raw": R4_raw, "rm_r4": rm_r4,
    }


def run_independent_replay(bundle: dict):
    """Independent exact integer verification of all laws, witnesses, and non-classicality."""
    print("=== 1. Exact DFAO Equivalence Check (n in 0..8191) ===")
    w_dfa = dfa_gray_add()
    assert w_dfa.check_closed() and w_dfa.check_pad_inv()
    vals = [gray_add_parity(n) for n in range(8192)]
    for n in range(8192):
        assert int(w_dfa.eval_tuple((n,))) == vals[n], f"DFA mismatch at {n}"
    print(f"  PASS: dfaGrayAdd matches gray_add_parity on all 8,192 inputs (ones={sum(vals)}/8192).")
    print(f"  Prefix[0..47]: {''.join(str(v) for v in vals[:48])}")

    print("\n=== 2. Non-Classicality Separation Witnesses ===")
    classicals = [
        ("Thue-Morse", thue_morse),
        ("comp(Thue-Morse)", lambda n: 1 - thue_morse(n)),
        ("Rudin-Shapiro", rudin_shapiro),
        ("comp(Rudin-Shapiro)", lambda n: 1 - rudin_shapiro(n)),
        ("Baum-Sweet", baum_sweet),
        ("comp(Baum-Sweet)", lambda n: 1 - baum_sweet(n)),
        ("Period-Doubling", period_doubling),
        ("comp(Period-Doubling)", lambda n: 1 - period_doubling(n)),
        ("Thue-Morse(3n)", thue_morse_3n),
        ("comp(Thue-Morse(3n))", lambda n: 1 - thue_morse_3n(n)),
    ]
    for cname, cfn in classicals:
        n0 = next(n for n in range(100) if gray_add_parity(n) != cfn(n))
        print(f"  Differs from {cname:22s} at n={n0}: w({n0})={gray_add_parity(n0)} != {cfn(n0)}")

    print("\n=== 3. Exact Certificate Summary (All Python-Mirror Checks PASSED) ===")
    sq = bundle["cert_prop_sq8"]
    cu = bundle["cert_prop_cu2"]
    print(f"  Stage A E(u,p)   : M_eq3 {bundle['M_eq3_raw'].n}->{bundle['M_eq3_min'].n} states, ExistsCert -> {bundle['D_eqShift'].n} states")
    print(f"  Stage B LtAdd    : M_lt4 {bundle['M_lt4'].n} -> ExistsCert {bundle['D_ltAdd_raw'].n} -> HomCert {bundle['D_ltAdd'].n} states")
    print(f"  Stage C LtAdd2   : M_lt2_4 {bundle['M_lt2_4'].n} -> ExistsCert {bundle['D_ltAdd2_raw'].n} -> HomCert {bundle['D_ltAdd2'].n} states")
    sq_edges = sum(len(sq["active_q"][sq["B"].trans[rp][a]]) for rp in range(sq["B"].n) for a in range(4))
    cu_edges = sum(len(cu["active_q"][cu["B"].trans[rp][a]]) for rp in range(cu["B"].n) for a in range(4))
    print(f"  Stage D NoSq(>=8): M_sq {bundle['M_sq_raw'].n}->{bundle['M_sq_min'].n}, Prophecy B {sq['B_raw_n']}->{sq['B'].n} states ({sq['cegar_splits']} CEGAR splits, {sq_edges} sparse checks)")
    print(f"  Stage E NoCu(>=2): M_cu {bundle['M_cu_raw'].n}->{bundle['M_cu_min'].n}, Prophecy B {cu['B_raw_n']}->{cu['B'].n} states ({cu['cegar_splits']} CEGAR splits, {cu_edges} sparse checks)")
    print(f"  Stage F No5Run   : w1..w4 states={[s[3].n for s in bundle['shifts']]}, R4_raw={bundle['R4_raw'].n} -> UniversalCert(false)")

    print("\n=== 4. Independent Empirical Verification & Sharpness Witnesses ===")
    # Check no square of period p in [8..256] for n in [0..4096)
    for p in range(8, 257):
        for n in range(4096):
            if all(vals[n + i] == vals[n + i + p] for i in range(p)):
                raise AssertionError(f"Unexpected square at n={n}, p={p}")
    print("  PASS: Zero squares of period 8 <= p <= 256 in n < 4096.")

    # Sharpness: exact square witnesses for p = 1..7
    sq_wits = {}
    for p in range(1, 8):
        n0 = next(n for n in range(1000) if all(vals[n + i] == vals[n + i + p] for i in range(p)))
        sq_wits[p] = n0
        u = "".join(str(vals[n0 + i]) for i in range(p))
        print(f"  Sharpness Square p={p}: n={n0}, factor={u}|{u}")

    # Check no cube of period p in [2..128] for n in [0..4096)
    for p in range(2, 129):
        for n in range(4096):
            if all(vals[n + i] == vals[n + i + p] for i in range(2 * p)):
                raise AssertionError(f"Unexpected cube at n={n}, p={p}")
    print("  PASS: Zero cubes of period 2 <= p <= 128 in n < 4096.")

    # Check no 5-run for n in [0..8187)
    for n in range(8187):
        if vals[n] == vals[n + 1] == vals[n + 2] == vals[n + 3] == vals[n + 4]:
            raise AssertionError(f"Unexpected 5-run at n={n}")
    print("  PASS: Zero 5-runs (5th powers of p=1) in n < 8187.")
    print(f"  Sharpness 4th power p=1: n=2, factor={''.join(str(vals[2+i]) for i in range(4))}")

    # Negative / mutation verification
    assert not verify_hom_cert(bundle["M_eq3_raw"], bundle["M_eq3_min"], bundle["rm_eq3"] ^ 1, bundle["hom_eq3"])
    bad_ex = dict(bundle["cert_ltAdd"])
    bad_ex["sub_masks"] = list(bad_ex["sub_masks"])
    bad_ex["sub_masks"][0] ^= 1
    assert not verify_exists_cert(bundle["M_lt4"], bundle["D_ltAdd_raw"], bad_ex)
    bad_pr = dict(cu)
    bad_pr["reach_rows"] = [0] * cu["B"].n
    assert not verify_prophecy_cert(bundle["M_cu_min"], dfa_p_ge_pow2_rev(1), bad_pr)
    assert not verify_universal_cert(bundle["R4_raw"], bundle["rm_r4"], True)
    print("  PASS: All 4 adversarial certificate mutation tests rejected.")


def emit_lean_certificates_file(bundle: dict, out_path: str):
    """Emit Sections 8-11 of Proof.lean (pure-data certificates + theorems + sharpness + mutations)."""
    chunks = []
    chunks.append("\n/-! ## Section 8: Pure-Data Certificates for the Gray-Sum Parity Word -/\n")

    # Stage A
    chunks.append("-- Stage A: E(u, p) := (grayAddParity u = grayAddParity (u + p))")
    chunks.append("private def idx_120 : Fin 3 → Fin 3 | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨0, by decide⟩")
    chunks.append("private def idx_1_3 : Fin 1 → Fin 3 | ⟨0, _⟩ => ⟨1, by decide⟩")
    chunks.append("private def idx_0_3 : Fin 1 → Fin 3 | ⟨0, _⟩ => ⟨0, by decide⟩")
    chunks.append("def dfaEq3Raw : DFA 3 :=")
    chunks.append("  dfaProd (· && ·) (dfaReindex idx_120 dfaAdd)")
    chunks.append("    (dfaProd (· == ·) (dfaReindex idx_1_3 dfaGrayAdd) (dfaReindex idx_0_3 dfaGrayAdd))")
    chunks.append(emit_dfa_def("dfaEq3Min", bundle["M_eq3_min"]))
    chunks.append(emit_hom_cert("certHom_eq3", bundle["rm_eq3"], bundle["hom_eq3"]))
    chunks.append(emit_dfa_def("dfaEqShift", bundle["D_eqShift"]))
    chunks.append(emit_exists_cert("certExists_eqShift", bundle["M_eq3_min"], bundle["D_eqShift"], bundle["cert_eqShift"]))

    # Stage B
    chunks.append("\n-- Stage B: LtAdd(u, n, p) := (u < n + p)")
    chunks.append("private def idx_230_4 : Fin 3 → Fin 4 | ⟨0, _⟩ => ⟨2, by decide⟩ | ⟨1, _⟩ => ⟨3, by decide⟩ | ⟨2, _⟩ => ⟨0, by decide⟩")
    chunks.append("private def idx_10_4 : Fin 2 → Fin 4 | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨0, by decide⟩")
    chunks.append("def dfaLt4Raw : DFA 4 :=")
    chunks.append("  dfaProd (· && ·) (dfaReindex idx_230_4 dfaAdd) (dfaReindex idx_10_4 dfaLt)")
    chunks.append(emit_dfa_def("dfaLtAddRaw", bundle["D_ltAdd_raw"]))
    chunks.append(emit_exists_cert("certExists_ltAdd", bundle["M_lt4"], bundle["D_ltAdd_raw"], bundle["cert_ltAdd"]))
    chunks.append(emit_dfa_def("dfaLtAdd", bundle["D_ltAdd"]))
    chunks.append(emit_hom_cert("certHom_ltAdd", bundle["rm_ltAdd"], bundle["hom_ltAdd"]))

    # Stage C
    chunks.append("\n-- Stage C: LtAdd2(u, n, p) := (u < n + 2 * p)")
    chunks.append("private def idx_330_4 : Fin 3 → Fin 4 | ⟨0, _⟩ => ⟨3, by decide⟩ | ⟨1, _⟩ => ⟨3, by decide⟩ | ⟨2, _⟩ => ⟨0, by decide⟩")
    chunks.append("private def idx_120_4 : Fin 3 → Fin 4 | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨0, by decide⟩")
    chunks.append("def dfaLt2_4Raw : DFA 4 :=")
    chunks.append("  dfaProd (· && ·) (dfaReindex idx_330_4 dfaAdd) (dfaReindex idx_120_4 dfaLtAdd)")
    chunks.append(emit_dfa_def("dfaLtAdd2Raw", bundle["D_ltAdd2_raw"]))
    chunks.append(emit_exists_cert("certExists_ltAdd2", bundle["M_lt2_4"], bundle["D_ltAdd2_raw"], bundle["cert_ltAdd2"]))
    chunks.append(emit_dfa_def("dfaLtAdd2", bundle["D_ltAdd2"]))
    chunks.append(emit_hom_cert("certHom_ltAdd2", bundle["rm_ltAdd2"], bundle["hom_ltAdd2"]))

    # Stage D
    chunks.append("\n-- Stage D: NoSquare (p >= 8) Backward-Prophecy Certificate")
    chunks.append("private def idx_10_3 : Fin 2 → Fin 3 | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨0, by decide⟩")
    chunks.append("private def idx_02_3 : Fin 2 → Fin 3 | ⟨0, _⟩ => ⟨0, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩")
    chunks.append("def dfaSqRaw : DFA 3 :=")
    chunks.append("  dfaProd (· && ·) (dfaProd (· && ·) (dfaReindex idx_10_3 dfaLe) dfaLtAdd)")
    chunks.append("    (dfaNot (dfaReindex idx_02_3 dfaEqShift))")
    chunks.append(emit_dfa_def("dfaSqMin", bundle["M_sq_min"]))
    chunks.append(emit_hom_cert("certHom_sq", bundle["rm_sq"], bundle["hom_sq"]))
    chunks.append(emit_prophecy_cert("certProphecy_noSq8", bundle["M_sq_min"], bundle["cert_prop_sq8"]))

    # Stage E
    chunks.append("\n-- Stage E: NoCube (p >= 2) Backward-Prophecy Certificate")
    chunks.append("def dfaCuRaw : DFA 3 :=")
    chunks.append("  dfaProd (· && ·) (dfaProd (· && ·) (dfaReindex idx_10_3 dfaLe) dfaLtAdd2)")
    chunks.append("    (dfaNot (dfaReindex idx_02_3 dfaEqShift))")
    chunks.append(emit_dfa_def("dfaCuMin", bundle["M_cu_min"]))
    chunks.append(emit_hom_cert("certHom_cu", bundle["rm_cu"], bundle["hom_cu"]))
    chunks.append(emit_prophecy_cert("certProphecy_noCu2", bundle["M_cu_min"], bundle["cert_prop_cu2"]))

    # Stage F: Shifts w1..w4 and No5Run UniversalCert
    chunks.append("\n-- Stage F: Shifts w(n+1)..w(n+4) and No5Run (p = 1) UniversalCert")
    chunks.append("private def idx_0_2 : Fin 1 → Fin 2 | ⟨0, _⟩ => ⟨0, by decide⟩")
    prev_name = "dfaGrayAdd"
    for i, (raw_pair, proj_raw, cert_ex, proj_min, rm_sh, hom_sh) in enumerate(bundle["shifts"], start=1):
        chunks.append(f"def dfaShiftPair{i} : DFA 2 := dfaProd (· && ·) dfaAddOne (dfaReindex idx_0_2 {prev_name})")
        chunks.append(emit_dfa_def(f"dfaW{i}Raw", proj_raw))
        chunks.append(emit_exists_cert(f"certExists_w{i}", raw_pair, proj_raw, cert_ex))
        chunks.append(emit_dfa_def(f"dfaW{i}", proj_min))
        chunks.append(emit_hom_cert(f"certHom_w{i}", rm_sh, hom_sh))
        prev_name = f"dfaW{i}"

    chunks.append("def dfaR1Raw : DFA 1 := dfaProd (· == ·) dfaGrayAdd dfaW1")
    chunks.append(emit_dfa_def("dfaR1", bundle["R1_min"]))
    chunks.append(emit_hom_cert("certHom_r1", bundle["rm_r1"], bundle["hom_r1"]))
    chunks.append("def dfaE02Raw : DFA 1 := dfaProd (· == ·) dfaGrayAdd dfaW2")
    chunks.append(emit_dfa_def("dfaE02", bundle["E02_min"]))
    chunks.append(emit_hom_cert("certHom_e02", bundle["rm_e02"], bundle["hom_e02"]))
    chunks.append("def dfaR2Raw : DFA 1 := dfaProd (· && ·) dfaR1 dfaE02")
    chunks.append(emit_dfa_def("dfaR2", bundle["R2_min"]))
    chunks.append(emit_hom_cert("certHom_r2", bundle["rm_r2"], bundle["hom_r2"]))
    chunks.append("def dfaE03Raw : DFA 1 := dfaProd (· == ·) dfaGrayAdd dfaW3")
    chunks.append(emit_dfa_def("dfaE03", bundle["E03_min"]))
    chunks.append(emit_hom_cert("certHom_e03", bundle["rm_e03"], bundle["hom_e03"]))
    chunks.append("def dfaR3Raw : DFA 1 := dfaProd (· && ·) dfaR2 dfaE03")
    chunks.append(emit_dfa_def("dfaR3", bundle["R3_min"]))
    chunks.append(emit_hom_cert("certHom_r3", bundle["rm_r3"], bundle["hom_r3"]))
    chunks.append("def dfaE04Raw : DFA 1 := dfaProd (· == ·) dfaGrayAdd dfaW4")
    chunks.append(emit_dfa_def("dfaE04", bundle["E04_min"]))
    chunks.append(emit_hom_cert("certHom_e04", bundle["rm_e04"], bundle["hom_e04"]))
    chunks.append("def dfaR4Raw : DFA 1 := dfaProd (· && ·) dfaR3 dfaE04")
    chunks.append(f"def certUniv_no5Run : UniversalCert := {{ reachMask := {bundle['rm_r4']}, target := false }}")

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(chunks) + "\n")
    print(f"\nWrote pure-data Lean certificate block to {out_path} ({len(chunks)} chunks).")


def main():
    bundle = build_all_certificates()
    run_independent_replay(bundle)
    if "--emit-certs" in sys.argv:
        idx = sys.argv.index("--emit-certs")
        out_path = sys.argv[idx + 1]
        emit_lean_certificates_file(bundle, out_path)


if __name__ == "__main__":
    main()
