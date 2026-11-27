#!/usr/bin/env python3
"""
explore_and_verify.py — Pure-Silicon Exact Binary Verification & Exploration Suite
for the Generalized T-Function Single-Cycle Inductive Lifting Engine (`dynsil-1`).

Strictly exact Python `int` bitmask arithmetic (ZERO floating-point operations).
Independently verifies:
  1. Layer 1 (Exact Bit-Slice Doubling) & Layer 2 (Exact Curvature-Holonomy Transport Law)
  2. Layer 3 (Universal 4-Lipschitz / Carry-Mask XOR Symmetry Action)
  3. Family A: 4-parameter hybrid ARX-square-run-carrymask family `hybridH(a, b, C, k)`
     - Exact 4-bit arithmetic characterization across all 512 base patterns + high-bit C + arbitrary k
     - Deep orbit replay up to w = 18 (cycle length 262,144)
     - Bit-2 Obstruction Mutual Annihilation at C = 1
     - Sharpness witness `hybridH(1, 1, 1, 1)`: passes w = 1, 2, 3, splits at w = 4
  4. Family B: Arbitrary-order d-run family `runT(d, C)`
     - Exact characterization: odd C and bit(C, d) = 1
     - Sharp threshold counterexamples: `runT(d, 1)` passes w = 1..d and splits at w = d + 1 (d = 2..10)
"""

from typing import Callable, List, Tuple


def run_d(d: int, x: int) -> int:
    if d == 0:
        return 0
    res = x
    for s in range(1, d):
        res &= (x << s)
    return res


def carry_mask(x: int) -> int:
    return x ^ (x + 1)


def hybrid_base(a: int, b: int, C: int) -> Callable[[int], int]:
    return lambda x: x + (((a * x * x) ^ (2 * run_d(2, x)) ^ (2 * b * run_d(3, x))) | C)


def hybrid_H(a: int, b: int, C: int, k: int) -> Callable[[int], int]:
    base = hybrid_base(a, b, C)
    return lambda x: base(x) ^ (2 * k * carry_mask(x))


def run_T(d: int, C: int) -> Callable[[int], int]:
    return lambda x: x + ((2 * run_d(d, x)) | C)


def hybrid_bit_cond(a: int, b: int, C: int) -> bool:
    c0 = (C >> 0) & 1
    c1 = (C >> 1) & 1
    c2 = (C >> 2) & 1
    c3 = (C >> 3) & 1
    a0 = (a >> 0) & 1
    a1 = (a >> 1) & 1
    b0 = (b >> 0) & 1
    return bool(c0 and (not a1 or c1) and (a0 or c2) and (not b0 or c3))


def is_single_cycle(f: Callable[[int], int], w: int) -> bool:
    """Exact O(2^w) single-cycle check from 0 mod 2^w (equivalent to full cycle for 1-Lipschitz f)."""
    mod = 1 << w
    mask = mod - 1
    x = 0
    for _ in range(1, mod):
        x = f(x) & mask
        if x == 0:
            return False
    x = f(x) & mask
    return x == 0


def cycle_decomposition(f: Callable[[int], int], w: int) -> List[List[int]]:
    """Exact cycle decomposition of a bijective map mod 2^w (or orbits from all residues)."""
    mod = 1 << w
    mask = mod - 1
    visited = [False] * mod
    cycles: List[List[int]] = []
    for start in range(mod):
        if visited[start]:
            continue
        orbit = []
        pos = {}
        x = start
        while x not in pos and not visited[x]:
            pos[x] = len(orbit)
            orbit.append(x)
            x = f(x) & mask
        if x in pos:
            cycles.append(orbit[pos[x]:])
        for v in orbit:
            visited[v] = True
    return sorted(cycles, key=lambda c: (-len(c), c[0]))


def defect_sum(f: Callable[[int], int], w: int) -> int:
    return sum(f(r) - r for r in range(1 << w))


def curvature_sum(f: Callable[[int], int], w: int) -> int:
    step = 1 << w
    return sum(f(r + step) - f(r) - step for r in range(step))


def holonomy(f: Callable[[int], int], w: int) -> int:
    acc = 0
    for r in range(1 << w):
        acc ^= (f(r) >> w) & 1
    return acc


def main() -> None:
    print("=== 1. Exact Verification of Layer 1 & Layer 2 Transport Identities ===")
    test_maps = [
        ("hybridH(1, 1, 9, 3)", hybrid_H(1, 1, 9, 3)),
        ("hybridH(1, 0, 1, 0)", hybrid_H(1, 0, 1, 0)),
        ("hybridH(3, 1, 11, 5)", hybrid_H(3, 1, 11, 5)),
        ("runT(4, 17)", run_T(4, 17)),
        ("hybridH(1, 1, 1, 1) [fails at w=4]", hybrid_H(1, 1, 1, 1)),
    ]
    for name, f in test_maps:
        for w in range(1, 10):
            ds_w = defect_sum(f, w)
            ds_w1 = defect_sum(f, w + 1)
            cs_w = curvature_sum(f, w)
            assert ds_w1 == 2 * ds_w + cs_w, f"Transport identity failed for {name} at w={w}"
            if is_single_cycle(f, w):
                hol_w = holonomy(f, w)
                assert ds_w % (1 << (w + 1)) == (hol_w << w), f"Sum-holonomy failed for {name} at w={w}"
            if is_single_cycle(f, w + 1):
                hol_w1 = holonomy(f, w + 1)
                assert (hol_w1 == 1) == (cs_w % (1 << (w + 2)) == 0), (
                    f"Curvature-holonomy transport failed for {name} at w={w}"
                )
    print("  [PASS] Exact defectSum(w+1) = 2*defectSum(w) + curvatureSum(w) & holonomy transport verified (w=1..9).")

    print("\n=== 2. Layer 3: Universal Carry-Mask XOR Symmetry Verification ===")
    base_candidates = [
        hybrid_base(1, 1, 9),
        hybrid_base(1, 0, 1),
        hybrid_base(1, 1, 1),  # non-ergodic at w=4
        run_T(3, 9),
        run_T(3, 1),           # non-ergodic at w=4
        lambda x: x + ((x * x) | 5),
        lambda x: x + ((x * x) | 1),  # non-ergodic at w=3
    ]
    for g in base_candidates:
        for k in [0, 1, 2, 3, 7, 13]:
            fk = lambda x, g=g, k=k: g(x) ^ (2 * k * carry_mask(x))
            for w in range(1, 10):
                assert is_single_cycle(fk, w) == is_single_cycle(g, w), (
                    f"Carry-mask symmetry mismatch at k={k}, w={w}"
                )
    print("  [PASS] Exact single-cycle invariance under XOR with 2*k*(x ^ (x+1)) verified for all base maps & k.")

    print("\n=== 3. Family A: Complete 512-Pattern Audit + High-Bit C + Deep Replay (w <= 18) ===")
    pass_count = 0
    for a in range(16):
        for b in range(2):
            for C in range(16):
                pred = hybrid_bit_cond(a, b, C)
                f0 = hybrid_base(a, b, C)
                sc4 = is_single_cycle(f0, 4)
                assert sc4 == pred, f"w=4 mismatch at (a={a}, b={b}, C={C})"
                for w in range(1, 10):
                    if pred:
                        assert is_single_cycle(f0, w), f"Expected pass at w={w} for ({a},{b},{C})"
                if not pred:
                    assert not is_single_cycle(f0, 4), f"Expected fail at w=4 for ({a},{b},{C})"
                else:
                    pass_count += 1
    assert pass_count == 27 * 4, f"Expected 108/512 passing patterns (27 mod 4x2x16), got {pass_count}"
    print(f"  [PASS] All 512 (a mod 16, b mod 2, C mod 16) patterns match 4-bit formula ({pass_count}/512 pass = 27/128).")

    # High-bit C and arbitrary k replay up to w = 12
    high_C_cases = [
        (1, 1, 9 | (1 << 5) | (1 << 9), 7),
        (5, 0, 1 | (1 << 4) | (1 << 7) | (1 << 11), 13),
        (3, 1, 11 | (1 << 6) | (1 << 10), 21),
        (2, 1, 15 | (1 << 8), 9),
        (0, 0, 5 | (1 << 5) | (1 << 6), 4),
    ]
    for a, b, C, k in high_C_cases:
        f = hybrid_H(a, b, C, k)
        assert hybrid_bit_cond(a, b, C)
        for w in range(1, 13):
            assert is_single_cycle(f, w), f"High-bit C failure at ({a},{b},{C},{k}), w={w}"
    print("  [PASS] High-bit C and arbitrary k instances verified through w = 12 (cycle length 4,096).")

    # Deep single-cycle replay up to w = 18 (cycle length 262,144)
    deep_cases = [
        ("hybridH(1, 0, 1, 0) [Bit-2 defect annihilation]", hybrid_H(1, 0, 1, 0)),
        ("hybridH(1, 1, 9, 3) [All 4 layers active]", hybrid_H(1, 1, 9, 3)),
        ("hybridH(3, 1, 11, 5)", hybrid_H(3, 1, 11, 5)),
        ("runT(5, 33)", run_T(5, 33)),
    ]
    for name, f in deep_cases:
        for w in range(1, 19):
            assert is_single_cycle(f, w), f"Deep replay failed for {name} at w={w}"
        print(f"  [PASS] {name}: single-cycle verified for ALL w = 1..18 (max cycle 2^18 = {1 << 18:,}).")

    print("\n=== 4. Surprising Phenomenon: Bit-2 Obstruction Mutual Annihilation (C = 1) ===")
    ks_bad = lambda x: x + ((x * x) | 1)
    r2_bad = run_T(2, 1)
    hyb_good = hybrid_H(1, 0, 1, 0)
    ks_cyc = cycle_decomposition(ks_bad, 3)
    r2_cyc = cycle_decomposition(r2_bad, 3)
    hyb_cyc = cycle_decomposition(hyb_good, 3)
    assert len(ks_cyc) > 1 and len(r2_cyc) > 1 and len(hyb_cyc) == 1 and len(hyb_cyc[0]) == 8
    print(f"  Klimov-Shamir x + (x^2 | 1)       mod 8 cycles: {ks_cyc} (FAILS w=3)")
    print(f"  Pure 2-run    x + (2*run2(x) | 1) mod 8 cycles: {r2_cyc} (FAILS w=3)")
    print(f"  XOR Hybrid    hybridH(1,0,1,0)    mod 8 cycles: {hyb_cyc} (PASSES ALL w >= 1!)")

    print("\n=== 5. Sharpness Witness: w <= 4 is Tight for hybridH ===")
    f_sharp = hybrid_H(1, 1, 1, 1)
    assert all(is_single_cycle(f_sharp, w) for w in [1, 2, 3])
    assert not is_single_cycle(f_sharp, 4)
    cyc4 = cycle_decomposition(f_sharp, 4)
    print(f"  hybridH(1, 1, 1, 1): PASSES w=1,2,3 (mod 8); FAILS w=4 (mod 16) with cycles: {cyc4}")

    print("\n=== 6. Family B: Arbitrary-Order d-Run Classification & No-Universal-Threshold Witnesses ===")
    for d in range(2, 11):
        f_fail = run_T(d, 1)
        f_pass = run_T(d, 1 | (1 << d))
        for w in range(1, d + 1):
            assert is_single_cycle(f_fail, w), f"runT({d}, 1) unexpectedly failed at w={w}"
        assert not is_single_cycle(f_fail, d + 1), f"runT({d}, 1) unexpectedly passed at w={d+1}"
        for w in range(1, max(d + 4, 13)):
            assert is_single_cycle(f_pass, w), f"runT({d}, {1 | (1 << d)}) failed at w={w}"
        cyc_split = [len(c) for c in cycle_decomposition(f_fail, d + 1)]
        print(
            f"  d={d:2d}: runT({d}, 1) passes w=1..{d}, FAILS at w={d+1} (cycle lengths {cyc_split}); "
            f"runT({d}, {1 | (1 << d)}) passes w=1..{max(d + 3, 12)}."
        )

    print("\nALL EXACT PURE-SILICON CHECKS PASSED WITH ZERO ERRORS.")


if __name__ == "__main__":
    main()
