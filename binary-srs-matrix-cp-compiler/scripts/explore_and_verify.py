"""
certcomp-16 (v2): Exact Certificate Synthesizer, Verifier, and Sharpness Tester
for the Verified Lean 4 Confluent Binary-Word Rewriting (Critical-Pair + Matrix-Weight) Engine.

Pure-silicon exact integer arithmetic only (no floating point anywhere).
"""

from __future__ import annotations
from typing import List, Tuple, Optional

Word = Tuple[int, ...]
Rule = Tuple[Word, Word]
Matrix = List[List[int]]
StepCert = Tuple[int, int]  # (rule_idx, pos)
JoinWitness = Tuple[List[StepCert], List[StepCert]]


def w_from_str(s: str) -> Word:
    return tuple(int(c) for c in s)


def w_to_str(w: Word) -> str:
    return "".join(str(b) for b in w) if w else "ε"


def to_bits(x: int, m: int) -> Word:
    return tuple((x >> (m - 1 - i)) & 1 for i in range(m))


def bin_val(w: Word) -> int:
    v = 0
    for b in w:
        v = 2 * v + b
    return v


# --- Exact Matrix Operations over Nat ---

def mat_id(d: int) -> Matrix:
    return [[1 if i == j else 0 for j in range(d)] for i in range(d)]


def mat_mul(A: Matrix, B: Matrix) -> Matrix:
    d = len(A)
    return [
        [sum(A[i][k] * B[k][j] for k in range(d)) for j in range(d)]
        for i in range(d)
    ]


def mat_eval(M0: Matrix, M1: Matrix, w: Word) -> Matrix:
    d = len(M0)
    acc = mat_id(d)
    for b in w:
        acc = mat_mul(acc, M1 if b else M0)
    return acc


def mat_ge(A: Matrix, B: Matrix) -> bool:
    d = len(A)
    return all(A[i][j] >= B[i][j] for i in range(d) for j in range(d))


def mat_gt_tr(A: Matrix, B: Matrix) -> bool:
    d = len(A)
    return mat_ge(A, B) and A[0][d - 1] > B[0][d - 1]


def check_layer_valid(dim: int, M0: Matrix, M1: Matrix) -> bool:
    if dim < 1 or len(M0) != dim or len(M1) != dim:
        return False
    if any(len(row) != dim for row in M0) or any(len(row) != dim for row in M1):
        return False
    if any(x < 0 for row in M0 for x in row) or any(x < 0 for row in M1 for x in row):
        return False
    return (
        M0[0][0] >= 1
        and M0[dim - 1][dim - 1] >= 1
        and M1[0][0] >= 1
        and M1[dim - 1][dim - 1] >= 1
    )


def check_termination(rules: List[Rule], layers: List[Tuple[int, Matrix, Matrix]]) -> bool:
    if not layers:
        return False
    for dim, M0, M1 in layers:
        if not check_layer_valid(dim, M0, M1):
            return False
    for lhs, rhs in rules:
        if len(lhs) == 0:
            return False
        strict_found = False
        for dim, M0, M1 in layers:
            ml = mat_eval(M0, M1, lhs)
            mr = mat_eval(M0, M1, rhs)
            if mat_gt_tr(ml, mr):
                strict_found = True
                break
            elif mat_ge(ml, mr):
                continue
            else:
                return False
        if not strict_found:
            return False
    return True


# --- Complete Critical-Pair Enumeration & Trace Replay ---

def critical_pairs(rules: List[Rule]) -> List[Tuple[Word, Word]]:
    cps: List[Tuple[Word, Word]] = []
    for l1, r1 in rules:
        n1 = len(l1)
        for l2, r2 in rules:
            n2 = len(l2)
            for k in range(n1):
                a = l1[:k]
                c = l1[k:]
                if k + n2 <= n1:
                    if c[:n2] == l2:
                        b = c[n2:]
                        cps.append((r1, a + r2 + b))
                else:
                    nc = len(c)
                    if l2[:nc] == c:
                        d = l2[nc:]
                        cps.append((r1 + d, a + r2))
    return cps


def apply_step(rules: List[Rule], w: Word, rule_idx: int, pos: int) -> Optional[Word]:
    if rule_idx < 0 or rule_idx >= len(rules):
        return None
    lhs, rhs = rules[rule_idx]
    if pos < 0 or pos + len(lhs) > len(w):
        return None
    if w[pos : pos + len(lhs)] != lhs:
        return None
    return w[:pos] + rhs + w[pos + len(lhs) :]


def replay_trace(rules: List[Rule], w: Word, trace: List[StepCert]) -> Optional[Word]:
    cur = w
    for ri, pos in trace:
        nxt = apply_step(rules, cur, ri, pos)
        if nxt is None:
            return None
        cur = nxt
    return cur


def check_joinability(rules: List[Rule], witnesses: List[JoinWitness]) -> bool:
    cps = critical_pairs(rules)
    if len(witnesses) != len(cps):
        return False
    for (x, y), (tx, ty) in zip(cps, witnesses):
        rx = replay_trace(rules, x, tx)
        ry = replay_trace(rules, y, ty)
        if rx is None or ry is None or rx != ry:
            return False
    return True


def check_cert(
    rules: List[Rule],
    layers: List[Tuple[int, Matrix, Matrix]],
    witnesses: List[JoinWitness],
) -> bool:
    return check_termination(rules, layers) and check_joinability(rules, witnesses)


def normalize_with_trace(
    rules: List[Rule], w: Word, max_steps: int = 20000
) -> Tuple[Word, List[StepCert]]:
    cur = w
    trace: List[StepCert] = []
    for _ in range(max_steps):
        moved = False
        for ri, (lhs, rhs) in enumerate(rules):
            n = len(lhs)
            for pos in range(len(cur) - n + 1):
                if cur[pos : pos + n] == lhs:
                    cur = cur[:pos] + rhs + cur[pos + n :]
                    trace.append((ri, pos))
                    moved = True
                    break
            if moved:
                break
        if not moved:
            return cur, trace
    raise RuntimeError(f"Exceeded max_steps={max_steps} on {w_to_str(w)}")


def normalize_rightmost(rules: List[Rule], w: Word, max_steps: int = 20000) -> Word:
    cur = w
    for _ in range(max_steps):
        moved = False
        for lhs, rhs in reversed(rules):
            n = len(lhs)
            for pos in range(len(cur) - n, -1, -1):
                if cur[pos : pos + n] == lhs:
                    cur = cur[:pos] + rhs + cur[pos + n :]
                    moved = True
                    break
            if moved:
                break
        if not moved:
            return cur
    raise RuntimeError(f"Exceeded max_steps={max_steps} on {w_to_str(w)}")


def synthesize_witnesses(rules: List[Rule]) -> Optional[List[JoinWitness]]:
    cps = critical_pairs(rules)
    wits: List[JoinWitness] = []
    for x, y in cps:
        if x == y:
            wits.append(([], []))
            continue
        nx, tx = normalize_with_trace(rules, x)
        ny, ty = normalize_with_trace(rules, y)
        if nx != ny:
            return None
        wits.append((tx, ty))
    return wits


# --- Parametric Binary SRS Families ---

def amp_sys(b: int, r: int, s: int, k: int, d: int) -> List[Rule]:
    return [
        ((1, 0), (0,) * b + (1,)),
        ((0,) * (k + d), (0,) * k),
        ((1,) * r, (1,) * s),
    ]


def amp_layers(b: int) -> List[Tuple[int, Matrix, Matrix]]:
    return [(2, [[1, 1], [0, 1]], [[b + 1, 1], [0, 1]])]


def binval_layers() -> List[Tuple[int, Matrix, Matrix]]:
    return [(2, [[1, 0], [0, 2]], [[1, 1], [0, 2]])]


def mersenne_srs(m: int) -> List[Rule]:
    rules: List[Rule] = [((1,) * m, (0,) * m)]
    for x in range(0, (1 << m) - 2):
        rules.append(((1,) + to_bits(x, m), (0,) + to_bits(x + 1, m)))
    return rules


def fermat_mod_srs(m: int) -> List[Rule]:
    rules: List[Rule] = []
    for x in range(1, 1 << m):
        rules.append(((1,) + to_bits(x, m), (0,) + to_bits(x - 1, m)))
    rules.append(((1,) + (0,) * m + (0,), (0, 0) + (1,) * m))
    rules.append(((1,) + (0,) * m + (1,), (0, 1) + (0,) * m))
    return rules


def main():
    print("=" * 74)
    print("PART 1: Six Concrete Binary Rewriting Systems & Certificate Synthesis")
    print("=" * 74)

    systems = [
        (
            "mod3",
            "Irredundant 3-Rule Mod-3 Normalizer (2-Layer: 2x2 + 3x3)",
            [(w_from_str("101"), w_from_str("010")),
             (w_from_str("11"), w_from_str("00")),
             (w_from_str("100"), w_from_str("001"))],
            [
                (2, [[1, 0], [0, 1]], [[1, 1], [0, 1]]),
                (3, [[1, 0, 0], [0, 1, 1], [0, 0, 1]], [[1, 1, 0], [0, 1, 0], [0, 0, 1]]),
            ],
        ),
        (
            "mod5",
            "Irredundant 5-Rule Fermat Mod-5 Normalizer fermatModSRS(2) (binValLayer 2x2)",
            fermat_mod_srs(2),
            binval_layers(),
        ),
        (
            "mod7",
            "Irredundant 7-Rule Mersenne Mod-7 Normalizer mersenneSRS(3) (binValLayer 2x2)",
            mersenne_srs(3),
            binval_layers(),
        ),
        (
            "fermat7",
            "Fermat-Order Doubling Mod-7 S(2,4,1,1,7) (1-Layer 2x2, Length-Increasing)",
            amp_sys(2, 4, 1, 1, 7),
            amp_layers(2),
        ),
        (
            "affineEmit",
            "Affine Emission Doubling {10->001, 0000->00, 111->001} (1-Layer 2x2, c=2)",
            [(w_from_str("10"), w_from_str("001")),
             (w_from_str("0000"), w_from_str("00")),
             (w_from_str("111"), w_from_str("001"))],
            [(2, [[1, 1], [0, 1]], [[3, 3], [0, 1]])],
        ),
        (
            "bubbleEmit",
            "Mixed Inc/Pres/Dec {11->010, 10->01, 0000->00} (2-Layer: 2x2 + 3x3)",
            [(w_from_str("11"), w_from_str("010")),
             (w_from_str("10"), w_from_str("01")),
             (w_from_str("0000"), w_from_str("00"))],
            [
                (2, [[1, 0], [0, 1]], [[1, 1], [0, 1]]),
                (3, [[1, 0, 1], [0, 1, 1], [0, 0, 1]], [[1, 1, 0], [0, 1, 0], [0, 0, 1]]),
            ],
        ),
    ]

    synthesized = {}
    for key, desc, rules, layers in systems:
        wits = synthesize_witnesses(rules)
        assert wits is not None, f"Failed to synthesize witnesses for {key}"
        assert check_cert(rules, layers, wits), f"Certificate check failed for {key}"
        cps = critical_pairs(rules)
        non_triv = sum(1 for x, y in cps if x != y)
        total_steps = sum(len(tx) + len(ty) for tx, ty in wits)
        print(f"[PASS] {key}: {desc}")
        print(f"       rules={len(rules)}, layers={len(layers)} (dims={[d for d,_,_ in layers]}), "
              f"CPs={len(cps)} (non-triv={non_triv}), total_trace_steps={total_steps}")
        synthesized[key] = (rules, layers, wits)

    print("\n" + "=" * 74)
    print("PART 2: Parametric Mersenne (2^m - 1) & Fermat (2^m + 1) Exhaustive Checks")
    print("=" * 74)
    for m in [2, 3, 4]:
        M = (1 << m) - 1
        rules = mersenne_srs(m)
        assert check_termination(rules, binval_layers())
        # Verify exact irredundancy: no LHS is a subword of any other rule's LHS
        for i, (li, _) in enumerate(rules):
            for j, (lj, _) in enumerate(rules):
                if i != j:
                    for pos in range(len(lj) - len(li) + 1):
                        assert lj[pos : pos + len(li)] != li, f"Redundant LHS in mersenneSRS({m})"
        checked = 0
        for n in range(0, 11):
            for mask in range(1 << n):
                w = to_bits(mask, n)
                nf, _ = normalize_with_trace(rules, w)
                assert len(nf) == n
                assert bin_val(nf) < M
                assert bin_val(nf) % M == bin_val(w) % M
                checked += 1
        print(f"[PASS] mersenneSRS({m}) (mod {M}, {len(rules)} irredundant rules): "
              f"exact canonical NF on all {checked} bit-strings (|w| <= 10).")

    for m in [1, 2, 3]:
        M = (1 << m) + 1
        rules = fermat_mod_srs(m)
        assert check_termination(rules, binval_layers())
        for i, (li, _) in enumerate(rules):
            for j, (lj, _) in enumerate(rules):
                if i != j:
                    for pos in range(len(lj) - len(li) + 1):
                        assert lj[pos : pos + len(li)] != li, f"Redundant LHS in fermatModSRS({m})"
        checked = 0
        for n in range(0, 11):
            for mask in range(1 << n):
                w = to_bits(mask, n)
                nf, _ = normalize_with_trace(rules, w)
                assert len(nf) == n
                assert bin_val(nf) < M
                assert bin_val(nf) % M == bin_val(w) % M
                checked += 1
        print(f"[PASS] fermatModSRS({m}) (mod {M}, {len(rules)} irredundant rules): "
              f"exact canonical NF on all {checked} bit-strings (|w| <= 10).")

    print("\n" + "=" * 74)
    print("PART 3: Exhaustive Verification of Parametric Dichotomy S(b, r, s, k, d)")
    print("=" * 74)
    tested_tuples = 0
    confluent_count = 0
    non_confluent_count = 0
    for b in range(2, 5):
        for r in range(1, 5):
            for s in range(0, r):
                for k in range(1, 5):
                    for d in range(1, 10):
                        rules = amp_sys(b, r, s, k, d)
                        layers = amp_layers(b)
                        assert check_termination(rules, layers)
                        pred = (k <= b ** s) and ((b ** r - b ** s) % d == 0)
                        wits = synthesize_witnesses(rules)
                        actual = wits is not None
                        assert actual == pred
                        if actual:
                            assert check_cert(rules, layers, wits)
                            confluent_count += 1
                        else:
                            w_left = (1,) * s + (0,)
                            w_right = (1,) * (r - 1) + (0,) * b + (1,)
                            nf_l, _ = normalize_with_trace(rules, w_left)
                            nf_r, _ = normalize_with_trace(rules, w_right)
                            assert nf_l != nf_r
                            non_confluent_count += 1
                        tested_tuples += 1
    print(
        f"[PASS] Verified exact Euler-Fermat dichotomy across all {tested_tuples} parameter tuples "
        f"({confluent_count} confluent certified, {non_confluent_count} non-confluent separated by 1^r 0)."
    )

    print("\n" + "=" * 74)
    print("PART 4: Independent Multi-Strategy Confluence Verification (|w| <= 9)")
    print("=" * 74)
    for key in ["mod3", "mod5", "mod7", "fermat7", "affineEmit", "bubbleEmit"]:
        rules = synthesized[key][0]
        count = 0
        for n in range(0, 10):
            for mask in range(1 << n):
                w = to_bits(mask, n)
                nf_left, _ = normalize_with_trace(rules, w)
                nf_right = normalize_rightmost(rules, w)
                assert nf_left == nf_right
                count += 1
        print(f"[PASS] {key}: leftmost-first == rightmost-reverse-rule NF on all {count} bit-strings (|w| <= 9).")

    print("\n" + "=" * 74)
    print("PART 5: Negative / Mutation Tests (10/10) & 3-Rule Minimality of mod3SRS")
    print("=" * 74)
    f_rules, f_layers, f_wits = synthesized["fermat7"]
    m_rules, m_layers, m_wits = synthesized["mod3"]
    mutations = [
        ("zero_tl_corner", f_rules, [(2, [[0, 1], [0, 1]], [[3, 1], [0, 1]])], f_wits),
        ("zero_br_corner", f_rules, [(2, [[1, 1], [0, 1]], [[3, 1], [0, 0]])], f_wits),
        ("non_strict_entry", f_rules, [(2, [[1, 1], [0, 1]], [[2, 1], [0, 1]])], f_wits),
        ("weak_only_layer", f_rules, [(2, [[1, 0], [0, 1]], [[1, 0], [0, 1]])], f_wits),
        ("bad_trace_step", f_rules, f_layers, [([(0, 99)], [])] + f_wits[1:]),
        ("missing_witness", f_rules, f_layers, f_wits[:-1]),
        ("empty_layers", f_rules, [], f_wits),
        ("ragged_matrix", f_rules, [(2, [[1, 1], [0]], [[3, 1], [0, 1]])], f_wits),
        ("mod3_single_layer", m_rules, m_layers[1:], m_wits),
        ("mismatch_join", f_rules, f_layers, [([], []) for _ in f_wits]),
    ]
    for mname, mrules, mlayers, mwits in mutations:
        assert check_cert(mrules, mlayers, mwits) is False
        print(f"[PASS] Mutation '{mname}' rejected (check_cert = False).")

    # 3-Rule Minimality of mod3SRS
    r0, r1, r2 = m_rules
    drop0 = [r1, r2]
    assert synthesize_witnesses(drop0) is not None
    nf_101, _ = normalize_with_trace(drop0, w_from_str("101"))
    nf_010, _ = normalize_with_trace(drop0, w_from_str("010"))
    assert nf_101 == w_from_str("101") and nf_010 == w_from_str("010") and nf_101 != nf_010
    print("[PASS] mod3_drop0 (no 101->010): confluent yet incomplete (NFs 101 != 010 both == 2 mod 3).")

    drop1 = [r0, r2]
    assert synthesize_witnesses(drop1) is None
    print("[PASS] mod3_drop1 (no 11->00): non-confluent (10101 -> 00011 != 00110).")

    drop2 = [r0, r1]
    assert synthesize_witnesses(drop2) is None
    print("[PASS] mod3_drop2 (no 100->001): non-confluent (10101 -> 01001 != 10010).")

    # Sharpness counterexamples for ampSys
    f5_rules = amp_sys(2, 4, 1, 1, 5)
    assert check_termination(f5_rules, amp_layers(2)) and synthesize_witnesses(f5_rules) is None
    th_rules = amp_sys(2, 4, 1, 3, 7)
    assert check_termination(th_rules, amp_layers(2)) and synthesize_witnesses(th_rules) is None
    print("[PASS] Sharpness neighbors S(2,4,1,1,5) and S(2,4,1,3,7) confirmed terminating & non-confluent.")

    print("\n" + "=" * 74)
    print("PART 6: All v2 Verification Suites Passed (Zero Floats Used)")
    print("=" * 74)


if __name__ == "__main__":
    main()
