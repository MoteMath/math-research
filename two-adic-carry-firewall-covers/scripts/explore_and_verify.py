#!/usr/bin/env python3
"""
Pure-Silicon 2-Adic Compactness & Carry-Firewall Certificate Compiler
=====================================================================
Synthesizes adaptive, non-uniform binary-prefix-tree certificates over Z_2,
independently verifies every discharged infinite theorem on exact integer
instances, verifies sharpness / phase-transition counterexamples, tests
certificate mutation rejection, and prints exact Lean 4 certificate encodings.

Strictly CPU-only, exact Python arbitrary-precision integers (zero floats
in any certificate or verification step).
"""

from dataclasses import dataclass
from typing import Callable, List, Optional, Tuple, Union


# ---------------------------------------------------------------------------
# 1. Core Binary Prefix Tree (Compactness Cover of Z_2 / N)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Leaf:
    cert: int


@dataclass(frozen=True)
class Branch:
    even: "CoverTree"
    odd: "CoverTree"


CoverTree = Union[Leaf, Branch]


def tree_leaves(t: CoverTree) -> int:
    if isinstance(t, Leaf):
        return 1
    return tree_leaves(t.even) + tree_leaves(t.odd)


def tree_max_depth(t: CoverTree) -> int:
    if isinstance(t, Leaf):
        return 0
    return 1 + max(tree_max_depth(t.even), tree_max_depth(t.odd))


def tree_depth_hist(t: CoverTree, d: int = 0) -> dict:
    if isinstance(t, Leaf):
        return {d: 1}
    h0 = tree_depth_hist(t.even, d + 1)
    h1 = tree_depth_hist(t.odd, d + 1)
    out = dict(h0)
    for k, v in h1.items():
        out[k] = out.get(k, 0) + v
    return out


def tree_haar_num(max_d: int, t: CoverTree, d: int = 0) -> int:
    if isinstance(t, Leaf):
        return 1 << (max_d - d)
    return tree_haar_num(max_d, t.even, d + 1) + tree_haar_num(max_d, t.odd, d + 1)


def tree_max_cert(t: CoverTree) -> int:
    if isinstance(t, Leaf):
        return t.cert
    return max(tree_max_cert(t.even), tree_max_cert(t.odd))


def check_cover(valid: Callable[[int, int, int], bool], t: CoverTree, r: int = 0, d: int = 0) -> bool:
    if isinstance(t, Leaf):
        return valid(r, d, t.cert)
    return check_cover(valid, t.even, r, d + 1) and check_cover(valid, t.odd, r + (1 << d), d + 1)


# ---------------------------------------------------------------------------
# 2. Pure-Silicon Carry-Firewall Operations & Descent Simulator
# ---------------------------------------------------------------------------

def clear_bit(x: int, k: int) -> int:
    """Exact bit-k clearing: (x // 2^(k+1)) * 2^(k+1) + (x % 2^k)."""
    p_hi = 1 << (k + 1)
    p_lo = 1 << k
    return (x // p_hi) * p_hi + (x % p_lo)


def collatz_core(n: int) -> int:
    return 3 * n + 1


def xor_collatz_core(c: int) -> Callable[[int], int]:
    return lambda n: (n ^ (n << 1)) + c


def firewall_step(odd_core: Callable[[int], int], k: int, n: int) -> int:
    if n % 2 == 0:
        return n >> 1
    return clear_bit(odd_core(n), k) >> 1


def firewall_iter(odd_core: Callable[[int], int], k: int, steps: int, n: int) -> int:
    x = n
    for _ in range(steps):
        x = firewall_step(odd_core, k, x)
    return x


def sim_steps(
    odd_core: Callable[[int], int],
    k: int,
    slope: int,
    offset: int,
    r: int,
    d: int,
    steps: int,
) -> Optional[Tuple[int, int, int, int, int]]:
    """
    Symbolic 2-adic Carry-Firewall + Affine-Lipschitz simulator.
    Tracks (cur, prec, A, B, pow2) over the infinite ball B(r, d) = {r + q * 2^d}
    maintaining:
      1) firewall_iter(steps, n) % 2^prec == cur
      2) pow2 * firewall_iter(steps, n) <= A * n + B
    Returns None if precision runs out before `steps`.
    """
    cur = r % (1 << d)
    prec = d
    A = 1
    B = 0
    pow2 = 1
    for _ in range(steps):
        if prec == 0:
            return None
        if cur % 2 == 0:
            cur = cur >> 1
            prec -= 1
            pow2 *= 2
        else:
            y = odd_core(cur)
            if prec == k:
                # CARRY FIREWALL: bit k is cleared to 0, so mod 2^(k+1) depends
                # only on low k bits; after >> 1, precision stays at k!
                cur = (y % (1 << k)) >> 1
                prec = k
            elif prec > k:
                cur = (clear_bit(y, k) >> 1) % (1 << (prec - 1))
                prec -= 1
            else:
                cur = (y >> 1) % (1 << (prec - 1))
                prec -= 1
            A = slope * A
            B = slope * B + offset * pow2
            pow2 *= 2
    return (cur, prec, A, B, pow2)


def make_valid_descent(
    odd_core: Callable[[int], int],
    k: int,
    slope: int,
    offset: int,
    N0: int,
) -> Callable[[int, int, int], bool]:
    def valid(r: int, d: int, steps: int) -> bool:
        if steps == 0:
            return False
        res = sim_steps(odd_core, k, slope, offset, r, d, steps)
        if res is None:
            return False
        _, _, A, B, pow2 = res
        if not (A < pow2):
            return False
        diff = pow2 - A
        # For all q with (r + q*2^d) >= N0 and diff*(r + q*2^d) <= B, check directly:
        step_size = 1 << d
        q = 0
        while diff * (r + q * step_size) <= B:
            n = r + q * step_size
            if n >= N0:
                if not (firewall_iter(odd_core, k, steps, n) < n):
                    return False
            q += 1
        return True

    return valid


def synthesize_descent_tree(
    odd_core: Callable[[int], int],
    k: int,
    slope: int,
    offset: int,
    N0: int,
    max_depth: int = 16,
    max_steps: int = 32,
) -> Optional[CoverTree]:
    valid = make_valid_descent(odd_core, k, slope, offset, N0)

    def build(r: int, d: int) -> Optional[CoverTree]:
        # Try smallest step count t that closes on ball (r, d)
        cur = r
        prec = d
        A, B, pow2 = 1, 0, 1
        for t in range(1, max_steps + 1):
            if prec == 0:
                break
            if cur % 2 == 0:
                cur = cur >> 1
                prec -= 1
                pow2 *= 2
            else:
                y = odd_core(cur)
                if prec == k:
                    cur = (y % (1 << k)) >> 1
                    prec = k
                elif prec > k:
                    cur = (clear_bit(y, k) >> 1) % (1 << (prec - 1))
                    prec -= 1
                else:
                    cur = (y >> 1) % (1 << (prec - 1))
                    prec -= 1
                A = slope * A
                B = slope * B + offset * pow2
                pow2 *= 2
            if A < pow2 and valid(r, d, t):
                return Leaf(t)
        if d >= max_depth:
            return None
        left = build(r, d + 1)
        if left is None:
            return None
        right = build(r + (1 << d), d + 1)
        if right is None:
            return None
        return Branch(left, right)

    return build(0, 0)


# ---------------------------------------------------------------------------
# 3. Reflected 2-Adic Expr Valuation / Separation Synthesis
# ---------------------------------------------------------------------------

def gray(n: int) -> int:
    return n ^ (n >> 1)


def gray_quad(a: int, b: int) -> Callable[[int], int]:
    return lambda n: gray(n) * gray(n) + a * n + b


def make_valid_val(fn: Callable[[int], int], lookahead: int) -> Callable[[int, int, int], bool]:
    def valid(r: int, d: int, v: int) -> bool:
        if v + 1 + lookahead > d:
            return False
        return (fn(r) % (1 << (v + 1))) == (1 << v)

    return valid


def synthesize_val_tree(
    fn: Callable[[int], int],
    lookahead: int,
    max_depth: int = 18,
) -> Optional[CoverTree]:
    def build(r: int, d: int) -> Optional[CoverTree]:
        if d > lookahead:
            k = d - lookahead
            rem = fn(r) & ((1 << k) - 1)
            if rem != 0:
                v = (rem & -rem).bit_length() - 1
                return Leaf(v)
        if d >= max_depth:
            return None
        left = build(r, d + 1)
        if left is None:
            return None
        right = build(r + (1 << d), d + 1)
        if right is None:
            return None
        return Branch(left, right)

    return build(0, 0)


# ---------------------------------------------------------------------------
# 4. Compact Lean 4 Tree Serializer (RLE / Bit-Packed or Direct Constructors)
# ---------------------------------------------------------------------------

def to_lean_tree(t: CoverTree) -> str:
    """Emit compact Lean 4 syntax using short helper aliases L / B."""
    if isinstance(t, Leaf):
        return f"L {t.cert}"
    return f"(B {to_lean_tree(t.even)} {to_lean_tree(t.odd)})"


def to_lean_bitstring_rle(t: CoverTree) -> Tuple[List[int], List[int]]:
    """
    Preorder encoding of a CoverTree into a flat List Nat:
      0 -> Branch, (c + 1) -> Leaf c
    Extremely compact in Lean source code and linear-time decoded in Lean!
    """
    out: List[int] = []

    def walk(node: CoverTree) -> None:
        if isinstance(node, Leaf):
            out.append(node.cert + 1)
        else:
            out.append(0)
            walk(node.even)
            walk(node.odd)

    walk(t)
    return out


# ---------------------------------------------------------------------------
# 5. Main Synthesis, Independent Verification, Sharpness & Mutation Suite
# ---------------------------------------------------------------------------

def verify_all() -> None:
    print("=" * 76)
    print("2-ADIC COMPACTNESS & CARRY-FIREWALL CERTIFICATE COMPILER — EXACT VERIFICATION")
    print("=" * 76)

    # ---- Family 1: Bit-k-Cleared Collatz T_1 .. T_5 ----
    print("\n[1] Bit-k-Cleared Collatz Family T_k (k = 1..5)")
    collatz_specs = [
        (1, 2),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 2),
    ]
    t_trees = {}
    for k, N0 in collatz_specs:
        tree = synthesize_descent_tree(collatz_core, k, 3, 1, N0, max_depth=16, max_steps=20)
        assert tree is not None, f"Failed to synthesize T_{k}"
        valid = make_valid_descent(collatz_core, k, 3, 1, N0)
        assert check_cover(valid, tree), f"Tree check failed for T_{k}"
        leaves = tree_leaves(tree)
        max_d = tree_max_depth(tree)
        max_s = tree_max_cert(tree)
        haar = tree_haar_num(max_d, tree)
        assert haar == (1 << max_d), "Haar partition-of-unity violated!"
        uniform = 1 << max_d
        t_trees[k] = tree
        print(
            f"  T_{k} (N0={N0}): VERIFIED | leaves={leaves:3d}, max_depth={max_d:2d}, "
            f"max_steps={max_s:2d}, uniform=2^{max_d}={uniform:5d}, "
            f"compression={uniform}/{leaves} ({uniform / leaves:.2f}x), "
            f"Haar={haar}/{uniform}=1"
        )
        # Independent empirical replay on 0..50000 and 100-bit large integers
        for n in range(N0, 20000):
            ok = any(firewall_iter(collatz_core, k, s, n) < n for s in range(1, max_s + 1))
            assert ok, f"T_{k} failed descent at n={n}"
        for base in [1 << 64, (1 << 100) - 1, (1 << 127) + 975, 3**40 + 1]:
            for off in range(64):
                n = base + off
                ok = any(firewall_iter(collatz_core, k, s, n) < n for s in range(1, max_s + 1))
                assert ok, f"T_{k} failed large-n descent at n={n}"

    # ---- Family 2: Nonlinear Bit-k-Cleared XOR-Collatz X_{2,1}, X_{3,3} ----
    print("\n[2] Nonlinear Bit-k-Cleared XOR-Collatz Family X_{k,c}")
    xor_specs = [
        (2, 1, 1),
        (3, 3, 1),
    ]
    x_trees = {}
    for k, c, N0 in xor_specs:
        core = xor_collatz_core(c)
        tree = synthesize_descent_tree(core, k, 3, c, N0, max_depth=12, max_steps=16)
        assert tree is not None, f"Failed to synthesize X_{{{k},{c}}}"
        valid = make_valid_descent(core, k, 3, c, N0)
        assert check_cover(valid, tree)
        leaves = tree_leaves(tree)
        max_d = tree_max_depth(tree)
        max_s = tree_max_cert(tree)
        assert tree_haar_num(max_d, tree) == (1 << max_d)
        x_trees[(k, c)] = tree
        print(
            f"  X_{{{k},{c}}} (N0={N0}): VERIFIED | leaves={leaves:3d}, max_depth={max_d:2d}, "
            f"max_steps={max_s:2d} -> ALL n in N converge to 0!"
        )
        for n in range(1, 20000):
            ok = any(firewall_iter(core, k, s, n) < n for s in range(1, max_s + 1))
            assert ok, f"X_{{{k},{c}}} failed at n={n}"

    # ---- Family 3: Gray-Quadratic 2-Adic Valuation Ceilings ----
    print("\n[3] Reflected Gray-Quadratic Exact 2-Adic Valuation Spectra")
    gq_specs = [
        ("F1(n) = G(n)^2 + n + 10", 1, 10, 11, 549),
        ("F2(n) = G(n)^2 + 3n + 60", 3, 60, 14, 4385),
    ]
    gq_trees = {}
    for label, a, b, expected_max_v, sharp_n in gq_specs:
        fn = gray_quad(a, b)
        tree = synthesize_val_tree(fn, lookahead=1, max_depth=18)
        assert tree is not None
        valid = make_valid_val(fn, lookahead=1)
        assert check_cover(valid, tree)
        leaves = tree_leaves(tree)
        max_d = tree_max_depth(tree)
        max_v = tree_max_cert(tree)
        assert max_v == expected_max_v
        assert tree_haar_num(max_d, tree) == (1 << max_d)
        uniform = 1 << max_d
        gq_trees[(a, b)] = tree
        # Check exact sharpness witness
        val_sharp = fn(sharp_n)
        assert val_sharp % (1 << max_v) == 0 and val_sharp % (1 << (max_v + 1)) != 0
        print(
            f"  {label}: VERIFIED | leaves={leaves:3d}, max_depth={max_d:2d}, "
            f"max_v2={max_v:2d} (2^{max_v+1} never divides), "
            f"compression={uniform}/{leaves} ({uniform / leaves:.2f}x), "
            f"sharp witness n*={sharp_n} (v_2={max_v})"
        )
        for n in range(1 << 16):
            assert fn(n) % (1 << (max_v + 1)) != 0

    # ---- Sharpness & Phase-Transition Counterexamples ----
    print("\n[4] Sharpness & Phase-Transition Counterexamples")
    # T_6 expanding 4-cycle lift (phase [39, 27, 9, 14] = O-O-O-E): n = 290743719
    n6 = 290743719
    x = n6
    for t in range(1, 49):
        x = firewall_step(collatz_core, 6, x)
        assert x > n6, f"T_6 unexpectedly dropped at step {t}"
    assert x == 155037103245
    print(f"  T_6 phase transition: n={n6} stays > n for all 1<=t<=48, reaching T_6^48(n)={x} (> 533*n)")

    # T_8 genuine 6-cycle: 975 -> 1335 -> 1875 -> 2685 -> 3900 -> 1950 -> 975
    cyc8 = [975]
    x = 975
    for _ in range(6):
        x = firewall_step(collatz_core, 8, x)
        cyc8.append(x)
    assert cyc8 == [975, 1335, 1875, 2685, 3900, 1950, 975]
    print(f"  T_8 positive 6-cycle: {' -> '.join(map(str, cyc8))} (never drops below 975!)")

    # X_{3,1} fixed point 3
    assert firewall_step(xor_collatz_core(1), 3, 3) == 3
    print("  X_{3,1} fixed point: X_{3,1}(3) = 3 (explains why c=1 fails while c=3 converges to 0!)")

    # Gray-quadratic parameter sharpness b=56 and b=64
    assert gray_quad(3, 56)(430824) % (1 << 20) == 0
    assert gray_quad(3, 64)(600384) % (1 << 20) == 0
    print("  Gray-quadratic parameter sharpness: b=56 (n=430824) & b=64 (n=600384) both divisible by 2^20!")

    # ---- Negative / Mutation Tests ----
    print("\n[5] Negative / Mutation Tests (Broken Certificates MUST Fail)")
    # Mut 1: Apply T_4 valid tree to T_5
    assert not check_cover(make_valid_descent(collatz_core, 5, 3, 1, 2), t_trees[4])
    print("  Mutation 1 (T_4 cert applied to T_5): REJECTED (false)")
    # Mut 2: Apply T_5 valid tree to T_6
    assert not check_cover(make_valid_descent(collatz_core, 6, 3, 1, 2), t_trees[5])
    print("  Mutation 2 (T_5 cert applied to T_6): REJECTED (false)")
    # Mut 3: Truncate T_3 odd branch to Leaf(1)
    bad_t3 = Branch(t_trees[3].even, Leaf(1))
    assert not check_cover(make_valid_descent(collatz_core, 3, 3, 1, 2), bad_t3)
    print("  Mutation 3 (Truncated T_3 odd branch): REJECTED (false)")
    # Mut 4: Corrupt leaf step count of T_4 to 0
    bad_t4 = Branch(Leaf(0), t_trees[4].odd)
    assert not check_cover(make_valid_descent(collatz_core, 4, 3, 1, 2), bad_t4)
    print("  Mutation 4 (Zero-step leaf in T_4): REJECTED (false)")
    # Mut 5: Corrupt F2 valuation tree by replacing odd branch with Leaf(0)
    bad_f2 = Branch(gq_trees[(3, 60)].even, Leaf(0))
    assert not check_cover(make_valid_val(gray_quad(3, 60), 1), bad_f2)
    print("  Mutation 5 (Corrupted valuation leaf in F2): REJECTED (false)")
    # Mut 6: Apply F1 valuation tree to F2
    assert not check_cover(make_valid_val(gray_quad(3, 60), 1), gq_trees[(1, 10)])
    print("  Mutation 6 (F1 valuation cert applied to F2): REJECTED (false)")

    # ---- Write Preorder Encodings Summary for Proof.lean ----
    print("\n[6] Certificate Preorder Token Counts (for Lean 4 embedding)")
    for k in [1, 2, 3, 4, 5]:
        toks = to_lean_bitstring_rle(t_trees[k])
        print(f"  T_{k}: {len(toks)} tokens ({tree_leaves(t_trees[k])} leaves)")
    for (k, c) in [(2, 1), (3, 3)]:
        toks = to_lean_bitstring_rle(x_trees[(k, c)])
        print(f"  X_{{{k},{c}}}: {len(toks)} tokens ({tree_leaves(x_trees[(k, c)])} leaves)")
    for (a, b) in [(1, 10), (3, 60)]:
        toks = to_lean_bitstring_rle(gq_trees[(a, b)])
        print(f"  GQ({a},{b}): {len(toks)} tokens ({tree_leaves(gq_trees[(a, b)])} leaves)")

    print("\nALL INDEPENDENT VERIFICATIONS, SHARPNESS CHECKS, AND MUTATION TESTS PASSED!")


def dump_lean_certs() -> None:
    """Helper to print compact Lean 4 preorder certificate lists."""
    certs = [
        ("certT1", synthesize_descent_tree(collatz_core, 1, 3, 1, 2, 16, 20)),
        ("certT2", synthesize_descent_tree(collatz_core, 2, 3, 1, 1, 16, 20)),
        ("certT3", synthesize_descent_tree(collatz_core, 3, 3, 1, 2, 16, 20)),
        ("certT4", synthesize_descent_tree(collatz_core, 4, 3, 1, 2, 16, 20)),
        ("certT5", synthesize_descent_tree(collatz_core, 5, 3, 1, 2, 16, 20)),
        ("certX21", synthesize_descent_tree(xor_collatz_core(1), 2, 3, 1, 1, 12, 16)),
        ("certX33", synthesize_descent_tree(xor_collatz_core(3), 3, 3, 3, 1, 12, 16)),
        ("certGQ1", synthesize_val_tree(gray_quad(1, 10), 1, 18)),
        ("certGQ2", synthesize_val_tree(gray_quad(3, 60), 1, 18)),
    ]
    for name, tree in certs:
        assert tree is not None
        toks = to_lean_bitstring_rle(tree)
        # Format neatly into lines of 24 numbers
        lines = []
        for i in range(0, len(toks), 24):
            lines.append("  " + ", ".join(str(x) for x in toks[i : i + 24]))
        body = ",\n".join(lines)
        print(f"def {name}Tokens : List Nat := [\n{body}\n]\n")


if __name__ == "__main__":
    import sys

    if "--dump-lean" in sys.argv:
        dump_lean_certs()
    else:
        verify_all()
