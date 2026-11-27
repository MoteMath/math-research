"""
Pure-Silicon Binary Partition & Restricted-Power-of-Two Congruence Automaton Engine
===================================================================================
Exact integer exploration, finite-state window DFA synthesis, Lean 4 certificate export,
independent verification of the Universal 2-Adic Carry-Valuation Law and Complete
v_2(r+1) Parity Dichotomy, and boundary sharpness counterexample verification.

Zero floating-point arithmetic is used anywhere in this script.
"""

from collections import deque


# ---------------------------------------------------------------------------
# 1. Exact Pure-Silicon Bit-Shift Recurrence Evaluators
# ---------------------------------------------------------------------------

def bin_part(D: list[int], N: int) -> list[int]:
    """Compute B_D(n) for 0 <= n <= N via exact bit-shift recurrence."""
    assert 0 in D and len(D) == len(set(D)), "Digit set D must be duplicate-free and contain 0."
    B = [0] * (N + 1)
    B[0] = 1
    for n in range(1, N + 1):
        acc = 0
        for d in D:
            if d <= n and ((n - d) & 1) == 0:
                acc += B[(n - d) >> 1]
        B[n] = acc
    return B


def br_seq(r: int, N: int) -> list[int]:
    """Compute r-restricted binary partition function b_r(n) = B_{0..r}(n)."""
    return bin_part(list(range(r + 1)), N)


def v2(x: int) -> int:
    """Exact 2-adic valuation (trailing zero count ctz) for x > 0."""
    assert x > 0
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c


def phi_universal(t: int, q: int) -> int:
    """Exact universal mod-4 carry-valuation law Phi_t(q) for 0 <= q < 2^t, t >= 1."""
    assert t >= 1 and 0 <= q < (1 << t)
    half = 1 << (t - 1)
    if q == 0:
        return 1
    if q < half:
        return 2 if (v2(q) % 2 == 0) else 0
    if q == half:
        return 3 if (t % 2 == 0) else 1
    return 0


# ---------------------------------------------------------------------------
# 2. Finite-State Window Congruence Automaton Synthesizer
# ---------------------------------------------------------------------------

def build_window_automaton(D: list[int], M: int):
    """
    Construct the exact reachable finite-state window DFA for V_{D,M}(n):
      V_{D,M}(n)[j] = B_D(n - j) mod M   for 0 <= j < L = max(D),
    with bit-shift transitions V(2n + b) = T_b(V(n)).
    """
    L = max(D)
    assert L >= 1 and M >= 1 and 0 in D
    v0 = (1 % M,) + (0,) * (L - 1)

    def step(v: tuple[int, ...], b: int) -> tuple[int, ...]:
        out = []
        for j in range(L):
            s = 0
            for d in D:
                num = j + d - b
                if num >= 0 and (num & 1) == 0:
                    idx = num >> 1
                    if idx < L:
                        s += v[idx]
            out.append(s % M)
        return tuple(out)

    assert step(v0, 0) == v0, "Initial window v0 must be a fixed point of T_0."

    state_to_id = {v0: 0}
    states = [v0]
    d0: list[int] = []
    d1: list[int] = []
    queue = deque([0])

    # Expand in deterministic BFS order
    while queue:
        sid = queue.popleft()
        v = states[sid]
        n0 = step(v, 0)
        if n0 not in state_to_id:
            state_to_id[n0] = len(states)
            states.append(n0)
            queue.append(state_to_id[n0])
        n1 = step(v, 1)
        if n1 not in state_to_id:
            state_to_id[n1] = len(states)
            states.append(n1)
            queue.append(state_to_id[n1])

    # Build transition arrays indexed by state id
    d0 = [state_to_id[step(v, 0)] for v in states]
    d1 = [state_to_id[step(v, 1)] for v in states]
    return L, states, d0, d1


def run_bits_dfa(d0: list[int], d1: list[int], q: int, a: int, c: int) -> int:
    """Feed the a-bit binary expansion of c (MSB first) starting from state q."""
    for shift in range(a - 1, -1, -1):
        bit = (c >> shift) & 1
        q = d1[q] if bit else d0[q]
    return q


def verify_dfa_affine_self(states, d0, d1, M, a, c, alpha) -> bool:
    """Check finite-state certificate for B_D(2^a n + c) == alpha * B_D(n) (mod M)."""
    return all(
        states[run_bits_dfa(d0, d1, q, a, c)][0] == (alpha * states[q][0]) % M
        for q in range(len(states))
    )


def verify_dfa_coupled(states, d0, d1, M, a, c1, c2, alpha) -> bool:
    """Check finite-state certificate for B_D(2^a n + c1) == alpha * B_D(2^a n + c2) (mod M)."""
    return all(
        states[run_bits_dfa(d0, d1, q, a, c1)][0]
        == (alpha * states[run_bits_dfa(d0, d1, q, a, c2)][0]) % M
        for q in range(len(states))
    )


def to_btree_lean(items: list[str]) -> str:
    """Build an LSB-indexed balanced binary tree literal for instant Lean kernel lookup."""
    assert len(items) >= 1
    if len(items) == 1:
        return f".leaf {items[0]}"
    evens = [items[i] for i in range(0, len(items), 2)]
    odds = [items[i] for i in range(1, len(items), 2)]
    return f".node ({to_btree_lean(evens)}) ({to_btree_lean(odds)})"


def format_lean_cert(name: str, D: list[int], M: int) -> str:
    L, states, d0, d1 = build_window_automaton(D, M)
    S = len(states)
    lines = []
    lines.append(f"-- Auto-synthesized exact window DFA for D = {D}, L = {L}, M = {M}, S = {S}")
    lines.append(f"def {name}_d0 : BTree Nat := {to_btree_lean([str(x) for x in d0])}")
    lines.append(f"def {name}_d1 : BTree Nat := {to_btree_lean([str(x) for x in d1])}")
    emb_strs = ["[" + ", ".join(map(str, v)) + "]" for v in states]
    lines.append(f"def {name}_emb : BTree (List Nat) := {to_btree_lean(emb_strs)}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# 3. Main Verification & Reporting Suite
# ---------------------------------------------------------------------------

def main():
    print("=" * 78)
    print("PURE-SILICON BINARY PARTITION CONGRUENCE AUTOMATON ENGINE — EXACT VERIFICATION")
    print("=" * 78)

    # --- Part A: Concrete Window-Automaton Certificates ---
    print("\n[PART A] Synthesizing & Checking Finite-State Window Automaton Certificates")

    # 1. b_5(n) mod 4 (24 states)
    D_b5 = [0, 1, 2, 3, 4, 5]
    L5, st5, d0_5, d1_5 = build_window_automaton(D_b5, 4)
    forbids3_b5 = all(v[0] != 3 for v in st5)
    B5 = bin_part(D_b5, 4096)
    replay_b5 = all(B5[n] % 4 != 3 for n in range(len(B5)))
    assert forbids3_b5 and replay_b5
    print(f"  1) b_5 mod 4: S={len(st5)} states, L={L5}")
    print(f"     DFA forbids 3 mod 4: {forbids3_b5} | Replay (n<=4096): {replay_b5}")

    # 2. b_4(n) mod 4 (80 states)
    D_b4 = [0, 1, 2, 3, 4]
    L4, st4, d0_4, d1_4 = build_window_automaton(D_b4, 4)
    b4_laws = [
        (4, 0, 1),   # b_4(16n)      ==  b_4(n) mod 4
        (4, 5, 3),   # b_4(16n + 5)  == -b_4(n) mod 4
        (4, 15, 1),  # b_4(16n + 15) ==  b_4(n) mod 4
    ]
    B4 = bin_part(D_b4, 4096)
    print(f"  2) b_4 mod 4: S={len(st4)} states, L={L4}")
    for a, c, alpha in b4_laws:
        cert_ok = verify_dfa_affine_self(st4, d0_4, d1_4, 4, a, c, alpha)
        step = 1 << a
        rep_ok = all(B4[step * n + c] % 4 == (alpha * B4[n]) % 4 for n in range(4096 // step))
        assert cert_ok and rep_ok
        print(f"     b_4({step}n + {c:2d}) == {alpha}*b_4(n) (mod 4): DFA={cert_ok} | Replay={rep_ok}")
    coupled_b4 = verify_dfa_coupled(st4, d0_4, d1_4, 4, 3, 5, 0, 3)
    rep_coupled_b4 = all(B4[8 * n + 5] % 4 == (3 * B4[8 * n]) % 4 for n in range(512))
    assert coupled_b4 and rep_coupled_b4
    print(f"     b_4(8n + 5)  == 3*b_4(8n) (mod 4): DFA={coupled_b4} | Replay={rep_coupled_b4}")

    # 3. Gapped digit set D = {0, 2, 3} mod 4 (56 states)
    D_gap = [0, 2, 3]
    Lg, stg, d0_g, d1_g = build_window_automaton(D_gap, 4)
    gap_laws = [
        (5, 16, 3),  # B(32n + 16) == -B(n) mod 4
        (5, 30, 1),  # B(32n + 30) ==  B(n) mod 4
        (6, 35, 3),  # B(64n + 35) == -B(n) mod 4
    ]
    Bg = bin_part(D_gap, 4096)
    print(f"  3) B_{{0,2,3}} mod 4 (gapped, digit 1 omitted): S={len(stg)} states, L={Lg}")
    for a, c, alpha in gap_laws:
        cert_ok = verify_dfa_affine_self(stg, d0_g, d1_g, 4, a, c, alpha)
        step = 1 << a
        rep_ok = all(Bg[step * n + c] % 4 == (alpha * Bg[n]) % 4 for n in range(4096 // step))
        assert cert_ok and rep_ok
        print(f"     B({step}n + {c:2d}) == {alpha}*B(n) (mod 4): DFA={cert_ok} | Replay={rep_ok}")

    # --- Part B: Parametric Symbolic Theorem Verification ---
    print("\n[PART B] Verifying Universal Carry-Valuation Law & v_2(r+1) Parity Dichotomy")

    # 1. Universal mod-2 periodicity for all r in 1..40, n <= 1000
    for r in range(1, 41):
        B = br_seq(r, 1000)
        m = r + 1
        assert all((B[n] % 2 == 1) == (n % m <= 1) for n in range(1001))
    print("  1) Universal mod-2 law b_r(n) odd <=> n mod (r+1) <= 1: PASS (r=1..40, n<=1000)")

    # 2. Universal mod-4 carry-valuation law for r = 2^t * u - 1
    checked_pairs = 0
    for t in range(1, 7):
        for u in [1, 3, 5, 7]:
            r = (1 << t) * u - 1
            if r > 200:
                continue
            max_j = min((1 << (t + 1)) + 8, 3000 // u)
            B = br_seq(r, 2 * u * max_j + 2)
            for j in range(max_j):
                assert B[2 * u * j] % 4 == phi_universal(t, j % (1 << t))
            checked_pairs += 1
    print(f"  2) Universal mod-4 carry-valuation law b_{{2^t u - 1}}(2uj) == Phi_t(j mod 2^t): PASS ({checked_pairs} (t,u) pairs)")

    # 3. Complete v_2(r+1) parity dichotomy for r = 1..65
    odd_v2_rs = []
    even_v2_ge2_rs = []
    even_r_rs = []
    for r in range(1, 66):
        N = 2000 if r <= 40 else 1000
        B = br_seq(r, N)
        t = v2(r + 1)
        if t % 2 == 1:
            assert all(x % 4 != 3 for x in B)
            odd_v2_rs.append(r)
        elif t >= 2:
            assert B[r + 1] % 4 == 3
            even_v2_ge2_rs.append(r)
        else:
            # r = 2k >= 2 even: exact sum identity b_{2k}(2k+1) + b_{2k}(4k+2) == 0 mod 4
            assert (B[r + 1] + B[2 * r + 2]) % 4 == 0
            assert B[r + 1] % 2 == 1 and B[2 * r + 2] % 2 == 1
            assert (B[r + 1] % 4 == 3) ^ (B[2 * r + 2] % 4 == 3)
            even_r_rs.append(r)
    print(f"  3) Complete v_2(r+1) Parity Dichotomy (r=1..65): PASS")
    print(f"     - Odd v_2(r+1) (forbids 3 mod 4): {len(odd_v2_rs)} values, e.g. {odd_v2_rs[:10]}")
    print(f"     - Even v_2(r+1) >= 2 (witness n=r+1): {len(even_v2_ge2_rs)} values, e.g. {even_v2_ge2_rs}")
    print(f"     - Even r (v_2=0, witness in {{r+1, 2r+2}}): {len(even_r_rs)} values, e.g. {even_r_rs[:8]}")

    # --- Part C: Explicit Sharpness Counterexamples ---
    print("\n[PART C] Boundary Sharpness Counterexamples (Exact Integer)")
    print(f"  1) Even v_2(r+1)=2: b_3(4) = {br_seq(3, 4)[4]} (== {br_seq(3, 4)[4] % 4} mod 4), "
          f"b_11(12) = {br_seq(11, 12)[12]} (== {br_seq(11, 12)[12] % 4} mod 4)")
    print(f"  2) Even v_2(r+1)=4: b_15(16) = {br_seq(15, 16)[16]} (== {br_seq(15, 16)[16] % 4} mod 4)")
    print(f"  3) Even r (v_2=0):  b_2(6) = {br_seq(2, 6)[6]} (== 3 mod 4), b_4(5) = {br_seq(4, 5)[5]} (== 3 mod 4)")
    print(f"  4) Modulus 4 -> 8 sharpness:")
    print(f"     - b_5(6) = {B5[6]} (== 1 mod 4, but == {B5[6] % 8} != 1 mod 8)")
    print(f"     - b_4(16*0+5) = b_4(5) = {B4[5]} (== {B4[5] % 8} mod 8) vs -b_4(0) = -{B4[0]} (== {(-B4[0]) % 8} mod 8)")
    print(f"     - B_{{0,2,3}}(32*1+16) = B(48) = {Bg[48]} (== {Bg[48] % 8} mod 8) vs -B(1) = -{Bg[1]} (== {(-Bg[1]) % 8} mod 8)")
    print(f"     - B_{{0,2,3}}(32*0+16) = B(16) = {Bg[16]} (== {Bg[16] % 8} mod 8) vs -B(0) = -{Bg[0]} (== {(-Bg[0]) % 8} mod 8)")
    print(f"  5) Offset sharpness:")
    print(f"     - b_4(16*0+10) = b_4(10) = {B4[10]} (== {B4[10] % 4} mod 4) != -b_4(0) (== 3 mod 4)")
    print(f"     - B_{{0,2,3}}(32*0+17) = B(17) = {Bg[17]} (== {Bg[17] % 4} mod 4) != -B(0) (== 3 mod 4)")

    # Print Lean certificate snippet summary
    print("\n[PART D] Lean 4 Certificate Sizes Ready for Kernel Verification")
    for label, D in [("b5_mod4", D_b5), ("b4_mod4", D_b4), ("gap023_mod4", D_gap)]:
        L, st, d0, d1 = build_window_automaton(D, 4)
        print(f"  {label:12s}: D={D}, L={L}, S={len(st)}, total_table_entries={len(st)*(2+L)}")


if __name__ == "__main__":
    main()
