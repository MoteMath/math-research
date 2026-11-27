#!/usr/bin/env python3
"""
F_2[x] <-> Z Carry-Defect Classification Engine: Exact Discovery & Verification.

Pure-silicon binary math (exact Python arbitrary-precision int only; zero floats).
Computes the exact Residual Carry-Defect Transducer T_c for any multiplier c,
synthesizes backward-potential certificates (A, B) via exact value iteration,
verifies all infinite classification theorems on concrete ranges, finds sharpness
counterexamples, and emits Lean 4 BinTree certificate definitions.
"""

from collections import deque
import sys


def clmul(c: int, x: int) -> int:
    """Exact F_2[x] carryless multiplication over nonnegative integers."""
    res = 0
    shift = 0
    while x > 0:
        if x & 1:
            res ^= (c << shift)
        x >>= 1
        shift += 1
    return res


def defect(c: int, x: int) -> int:
    """Exact binary discrepancy between Z-multiplication and F_2[x]-multiplication."""
    return (c * x) ^ clmul(c, x)


def defect_weight(c: int, x: int) -> int:
    """Hamming weight of the multiplicative carry-defect word."""
    return defect(c, x).bit_count()


def build_residual_transducer(c: int):
    """
    Build the exact reachable Residual Carry-Defect Transducer T_c on states (u, v)
    with transition:
      stepU(c, u, b) = (u + b * c) >> 1
      stepV(c, v, b) = (v ^ (b * c)) >> 1
      emit(u, v)     = (u ^ v) & 1
    and solve for exact backward potentials A[i], B[i]:
      A[i] = min_{x >= 0} popcount(genDefect(c, u_i, v_i, x))
      B[i] = min_{x >= 0, genDefect != 0} popcount(genDefect(c, u_i, v_i, x))
    """
    start = (0, 0)
    states = [start]
    idx = {start: 0}
    dq = deque([start])
    while dq:
        u, v = dq.popleft()
        for b in (0, 1):
            nu = (u + b * c) >> 1
            nv = (v ^ (b * c)) >> 1
            if (nu, nv) not in idx:
                idx[(nu, nv)] = len(states)
                states.append((nu, nv))
                dq.append((nu, nv))

    n = len(states)
    nxt0 = [0] * n
    nxt1 = [0] * n
    emit = [0] * n
    INF = 10**9
    A = [0] * n
    B = [0] * n
    for i, (u, v) in enumerate(states):
        emit[i] = (u ^ v) & 1
        p = (u ^ v).bit_count()
        A[i] = p
        B[i] = p if u != v else INF
        nxt0[i] = idx[(u >> 1, v >> 1)]
        nxt1[i] = idx[((u + c) >> 1, (v ^ c) >> 1)]

    # Exact Bellman-Ford / value iteration (monotone decreasing on finite lattice)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            e = emit[i]
            for j in (nxt0[i], nxt1[i]):
                na = e + A[j]
                if na < A[i]:
                    A[i] = na
                    changed = True
                nb = (1 + A[j]) if e == 1 else B[j]
                if nb < B[i]:
                    B[i] = nb
                    changed = True

    # Independent certificate verification (identical to Lean PotentialCert.checkTree)
    for i, (u, v) in enumerate(states):
        assert v <= u < c, f"State invariant violated for c={c}: {(u, v)}"
        p = (u ^ v).bit_count()
        assert A[i] <= p
        if u != v:
            assert B[i] <= p
        e = (u ^ v) & 1
        for b, j in ((0, nxt0[i]), (1, nxt1[i])):
            uj, vj = states[j]
            assert uj == ((u + b * c) >> 1)
            assert vj == ((v ^ (b * c)) >> 1)
            assert A[i] <= e + A[j]
            if e == 1:
                assert B[i] <= 1 + A[j]
            else:
                assert B[i] <= B[j]

    return states, nxt0, nxt1, A, B


def transducer_sim(c: int, x: int) -> int:
    """Compute defectWeight(c, x) purely via the residual (u, v) transducer."""
    u, v = 0, 0
    acc = 0
    while x > 0:
        b = x & 1
        acc += (u ^ v) & 1
        u = (u + b * c) >> 1
        v = (v ^ (b * c)) >> 1
        x >>= 1
    return acc + (u ^ v).bit_count()


def format_bintree_lean(entries, depth: int) -> str:
    """
    Build a compact Lean 4 BinTree StateEntry expression indexed by the lowest `depth` bits
    (using short open constructors: e = empty, l = leaf, n = node).
    """
    if depth == 0:
        if 0 in entries:
            u, v, n0, n1, a, b = entries[0]
            return f"l ⟨{u},{v},{n0},{n1},{a},{b}⟩"
        return "e"
    left_entries = {k >> 1: val for k, val in entries.items() if (k & 1) == 0}
    right_entries = {k >> 1: val for k, val in entries.items() if (k & 1) == 1}
    if not left_entries and not right_entries:
        return "e"
    ls = format_bintree_lean(left_entries, depth - 1)
    rs = format_bintree_lean(right_entries, depth - 1)
    return f"n ({ls}) ({rs})"


def emit_lean_cert(name: str, c: int) -> str:
    states, nxt0, nxt1, A, B = build_residual_transducer(c)
    n = len(states)
    depth = max(1, (n - 1).bit_length())
    entries = {
        i: (states[i][0], states[i][1], nxt0[i], nxt1[i], A[i], B[i])
        for i in range(n)
    }
    tree_str = format_bintree_lean(entries, depth)
    return (
        f"-- Auto-synthesized exact backward-potential certificate for c = {c} "
        f"({n} reachable states, depth = {depth}, B[0] = {B[0]})\n"
        f"open BinTree in\n"
        f"def {name} : BinTree StateEntry :=\n  {tree_str}\n"
    )


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == "--emit-lean":
        for name, c in [("certTree23", 23), ("certTree175", 175)]:
            print(emit_lean_cert(name, c))
        return

    print("=== 1. Residual Transducer Exact Equivalence Check ===")
    for c in [1, 2, 3, 5, 7, 11, 15, 23, 27, 47, 175, 211]:
        for x in range(1000):
            assert transducer_sim(c, x) == defect_weight(c, x), (c, x)
    print("PASS: transducer_sim(c, x) == defect_weight(c, x) on 12,000 exact pairs.")

    print("\n=== 2. Complete Classification of Odd c in [3, 255] ===")
    by_mu = {}
    for c in range(3, 256, 2):
        states, _, _, A, B = build_residual_transducer(c)
        assert A[0] == 0
        by_mu.setdefault(B[0], []).append((c, len(states)))
    for mu in sorted(by_mu):
        items = by_mu[mu]
        print(f"  mu(c) = {mu}: count = {len(items)}, smallest = {items[:8]}")
    assert by_mu[3][0][0] == 175, "175 must be the smallest odd c with mu(c) = 3"
    print("PASS: c = 175 (0b10101111, 302 states) is the unique smallest multiplier with mu(c) = 3.")

    print("\n=== 3. Theorem 1 Verification: c == 1 (mod 4), c >= 5 ===")
    for c in range(5, 2002, 4):
        L = c.bit_length()
        x = 1 + (1 << (L - 1))
        d = defect(c, x)
        assert d == (1 << L), (c, L, d)
        assert d.bit_count() == 1
    print("PASS: defect(c, 1 + 2^(L-1)) = 2^L (weight 1) for all 500 values c == 1 (mod 4), 5 <= c <= 2001.")
    print("  Sharpness: c = 1 gives defect(1, x) = 0 for all x; c = 3 (3 mod 4) has mu(3) = 2.")

    print("\n=== 4. Theorem 2 Verification: Mersenne Family c = 2^m - 1 ===")
    for m in range(2, 11):
        c = (1 << m) - 1
        states, _, _, A, B = build_residual_transducer(c)
        assert B[0] == 2, (m, B[0])
        assert len(states) == 3 * (1 << (m - 1)) - 2
        if m >= 3:
            assert defect(c, 7) == (1 << (m + 2)) + 4
            assert defect_weight(c, 7) == 2
        if m >= 4:
            x3 = 11 * (1 << (m - 3)) + 1
            assert defect(c, x3) == (1 << (2 * m)) + (1 << (2 * m - 1)) + (1 << (m - 2))
            assert defect_weight(c, x3) == 3
    # Zero-defect m-Fibbinary check
    for m in range(1, 7):
        c = (1 << m) - 1
        for x in range(2048):
            zd = (defect(c, x) == 0)
            # m-sparse: no two 1-bits within distance < m
            sparse = all(((x & (x << d)) == 0) for d in range(1, m))
            assert zd == sparse, (m, x, zd, sparse)
    print("PASS: Mersenne family verified for m = 2..10 (B[0]=2, |S|=3*2^(m-1)-2, exact w=2,3 witnesses, m-Fibbinary zero-defect).")
    print("  Sharpness: c = 2^m + 1 (m >= 2) has c == 1 (mod 4), so mu(2^m + 1) = 1.")

    print("\n=== 5. Theorem 3 Verification: c = 23 and c = 175 ===")
    for c, expected_mu, wits in [
        (23, 2, [(2, 9), (3, 5)]),
        (175, 3, [(3, 17), (4, 11), (5, 5)]),
    ]:
        states, _, _, A, B = build_residual_transducer(c)
        assert B[0] == expected_mu
        for w, x in wits:
            assert defect_weight(c, x) == w, (c, w, x, defect_weight(c, x))
        print(f"  c = {c} ({bin(c)}): {len(states)} states, B[0] = {B[0]}, witnesses = {wits}")
    # Sharpness for c = 175: c = 47 = 0b101111 (one fewer '10' prefix) has weight 2!
    x47 = next(x for x in range(1, 1000) if defect_weight(47, x) == 2)
    print(f"  Sharpness for 175: c = 47 (0b101111) achieves weight 2 at x = {x47} ({bin(x47)}), defect = {bin(defect(47, x47))}.")

    print("\n=== 6. Stealth Weight-1 Falsification Witness: c = 211 (0b11010011) ===")
    c = 211
    L = c.bit_length()
    two_bit_min = min(defect_weight(c, 1 + (1 << d)) for d in range(1, L))
    assert two_bit_min == 2
    first_w1 = next(x for x in range(1, 20000) if defect_weight(c, x) == 1)
    assert first_w1 == 17125
    assert defect(c, first_w1) == (1 << 17)
    print(f"  c = 211: every 2-bit input x = 1 + 2^d has weight >= {two_bit_min};")
    print(f"           all x < {first_w1} have weight != 1;")
    print(f"           yet x = {first_w1} ({bin(first_w1)}) gives defect = 2^17 (EXACT weight 1)!")
    print("\nALL EXACT CHECKS PASSED.")


if __name__ == "__main__":
    main()
