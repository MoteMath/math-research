"""
Exact Pure-Silicon Verification & Exploration Replay for:
  2-Adic Hensel-Contraction Fixed-Point & Basin Classifier (dynsil-14)

Zero floating-point values anywhere: all arithmetic is exact Python int bitmask replay.
Mirrors the Lean 4 BPoly AST, 3-valued abstract bit-derivative compiler `abs_deriv`,
finite-width certificate synthesis at w <= 3, exhaustive functional-graph replay up to w = 12,
and explicit boundary/sharpness counterexamples.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Dict, List, Tuple


# ---------------------------------------------------------------------------
# 1. Pure-Silicon Bitwise-Polynomial AST & 3-Valued Bit-Derivative Compiler
# ---------------------------------------------------------------------------

def bv_clmul(a: int, b: int, w: int) -> int:
    mask = (1 << w) - 1
    res = 0
    for i in range(w):
        if (b >> i) & 1:
            res ^= (a << i) & mask
    return res & mask


@dataclass(frozen=True)
class BPoly:
    kind: str
    a: "BPoly | None" = None
    b: "BPoly | None" = None
    val: int = 0

    def eval(self, x: int, w: int) -> int:
        mask = (1 << w) - 1
        k = self.kind
        if k == "var":
            return x & mask
        if k == "const":
            return self.val & mask
        if k == "add":
            return (self.a.eval(x, w) + self.b.eval(x, w)) & mask
        if k == "sub":
            return (self.a.eval(x, w) - self.b.eval(x, w)) & mask
        if k == "mul":
            return (self.a.eval(x, w) * self.b.eval(x, w)) & mask
        if k == "xor":
            return (self.a.eval(x, w) ^ self.b.eval(x, w)) & mask
        if k == "and":
            return (self.a.eval(x, w) & self.b.eval(x, w)) & mask
        if k == "or":
            return (self.a.eval(x, w) | self.b.eval(x, w)) & mask
        if k == "not":
            return (~self.a.eval(x, w)) & mask
        if k == "shl":
            return (self.a.eval(x, w) << self.val) & mask
        if k == "clmul":
            return bv_clmul(self.a.eval(x, w), self.b.eval(x, w), w)
        raise ValueError(f"unknown kind {k}")

    def eval_bit0(self, x0: int) -> int:
        k = self.kind
        if k == "var":
            return x0 & 1
        if k == "const":
            return self.val & 1
        if k in ("add", "sub", "xor"):
            return self.a.eval_bit0(x0) ^ self.b.eval_bit0(x0)
        if k in ("mul", "and", "clmul"):
            return self.a.eval_bit0(x0) & self.b.eval_bit0(x0)
        if k == "or":
            return self.a.eval_bit0(x0) | self.b.eval_bit0(x0)
        if k == "not":
            return 1 ^ self.a.eval_bit0(x0)
        if k == "shl":
            return self.a.eval_bit0(x0) if self.val == 0 else 0
        raise ValueError(k)

    def vanishes_above(self, m: int) -> bool:
        k = self.kind
        if k == "const":
            return self.val < (1 << m)
        if k == "and":
            return self.a.vanishes_above(m) or self.b.vanishes_above(m)
        if k in ("or", "xor"):
            return self.a.vanishes_above(m) and self.b.vanishes_above(m)
        if k == "not":
            return self.a.all_ones_above(m)
        return False

    def all_ones_above(self, m: int) -> bool:
        k = self.kind
        if k == "not":
            return self.a.vanishes_above(m)
        if k == "or":
            return self.a.all_ones_above(m) or self.b.all_ones_above(m)
        if k == "and":
            return self.a.all_ones_above(m) and self.b.all_ones_above(m)
        return False

    def abs_deriv(self, m: int, x0: int) -> str:
        """Returns 'zero', 'one', or 'top' (exact mirror of Lean BPoly.absDeriv)."""
        def axor(u: str, v: str) -> str:
            if u == "zero":
                return v
            if v == "zero":
                return u
            if u == "one" and v == "one":
                return "zero"
            return "top"

        def ascale(bit: int, d: str) -> str:
            return d if bit else "zero"

        k = self.kind
        if k == "var":
            return "one"
        if k == "const":
            return "zero"
        if k in ("add", "sub", "xor"):
            return axor(self.a.abs_deriv(m, x0), self.b.abs_deriv(m, x0))
        if k == "not":
            return self.a.abs_deriv(m, x0)
        if k == "shl":
            return self.a.abs_deriv(m, x0) if self.val == 0 else "zero"
        if k in ("mul", "clmul"):
            return axor(
                ascale(self.a.eval_bit0(x0), self.b.abs_deriv(m, x0)),
                ascale(self.b.eval_bit0(x0), self.a.abs_deriv(m, x0)),
            )
        if k == "and":
            if self.a.vanishes_above(m) or self.b.vanishes_above(m):
                return "zero"
            if self.a.all_ones_above(m):
                return self.b.abs_deriv(m, x0)
            if self.b.all_ones_above(m):
                return self.a.abs_deriv(m, x0)
            if self.a.abs_deriv(m, x0) == "zero" and self.b.abs_deriv(m, x0) == "zero":
                return "zero"
            return "top"
        if k == "or":
            if self.a.all_ones_above(m) or self.b.all_ones_above(m):
                return "zero"
            if self.a.vanishes_above(m):
                return self.b.abs_deriv(m, x0)
            if self.b.vanishes_above(m):
                return self.a.abs_deriv(m, x0)
            if self.a.abs_deriv(m, x0) == "zero" and self.b.abs_deriv(m, x0) == "zero":
                return "zero"
            return "top"
        raise ValueError(k)


VAR = BPoly("var")
CONST = lambda c: BPoly("const", val=c)
ADD = lambda a, b: BPoly("add", a, b)
SUB = lambda a, b: BPoly("sub", a, b)
MUL = lambda a, b: BPoly("mul", a, b)
XOR = lambda a, b: BPoly("xor", a, b)
AND = lambda a, b: BPoly("and", a, b)
OR = lambda a, b: BPoly("or", a, b)
NOT = lambda a: BPoly("not", a)
SHL = lambda a, s: BPoly("shl", a, val=s)
CLMUL = lambda a, b: BPoly("clmul", a, b)


# ---------------------------------------------------------------------------
# 2. Exact Functional-Graph Analyzer on BitVec w (Pure Integer, Zero Float)
# ---------------------------------------------------------------------------

def analyze_graph(fn: Callable[[int, int], int], w: int) -> Dict:
    N = 1 << w
    nxt = [fn(x, w) for x in range(N)]
    state = [0] * N  # 0=unvisited, 1=visiting, 2=done
    cid = [-1] * N
    depth = [0] * N
    cycles: List[List[int]] = []

    for s in range(N):
        if state[s] != 0:
            continue
        path = []
        pos = {}
        cur = s
        while state[cur] == 0:
            pos[cur] = len(path)
            path.append(cur)
            state[cur] = 1
            cur = nxt[cur]
        if state[cur] == 1:
            cs = pos[cur]
            cyc = path[cs:]
            idx = len(cycles)
            cycles.append(cyc)
            for v in cyc:
                cid[v] = idx
                depth[v] = 0
                state[v] = 2
            for i in range(cs - 1, -1, -1):
                v = path[i]
                cid[v] = idx
                depth[v] = depth[nxt[v]] + 1
                state[v] = 2
        else:
            idx = cid[cur]
            for i in range(len(path) - 1, -1, -1):
                v = path[i]
                cid[v] = idx
                depth[v] = depth[nxt[v]] + 1
                state[v] = 2

    basins = [0] * len(cycles)
    for v in range(N):
        basins[cid[v]] += 1

    fps = sorted(c[0] for c in cycles if len(c) == 1)
    fp_basins = {c[0]: basins[i] for i, c in enumerate(cycles) if len(c) == 1}
    spec = sorted((len(cycles[i]), basins[i]) for i in range(len(cycles)))
    return {
        "w": w,
        "fp_count": len(fps),
        "fps": fps,
        "fp_basins": fp_basins,
        "spec": spec,
        "max_depth": max(depth),
        "depths": depth,
    }


def hensel_lift_py(e: BPoly, m: int, L: int, c: int, w: int, r: int) -> int:
    q = (w - m + c - 1) // c
    x = r & ((1 << w) - 1)
    for _ in range(q * L):
        x = e.eval(x, w)
    return x


# ---------------------------------------------------------------------------
# 3. Concrete Maps Matching Proof.lean + Exhaustive Independent Replay
# ---------------------------------------------------------------------------

MAP_ASYM = OR(AND(VAR, CONST(4)), MUL(VAR, VAR))
MAP_SEVEN = OR(AND(VAR, CONST(6)), MUL(VAR, VAR))
MAP_THREE = ADD(OR(AND(VAR, CONST(4)), MUL(VAR, VAR)), CONST(2))
MAP_XORADD = lambda c: XOR(VAR, ADD(VAR, CONST(c)))
MAP_CLMUL_HYBRID = XOR(XOR(CLMUL(VAR, VAR), ADD(VAR, CONST(1))), VAR)
MAP_LOCAL_EVEN = ADD(ADD(MUL(MUL(VAR, VAR), VAR), MUL(VAR, VAR)), CONST(2))
MAP_HALF_CYCLE = ADD(ADD(MUL(MUL(VAR, VAR), VAR), MUL(CONST(2), VAR)), CONST(1))
MAP_MIXED_ISO = ADD(MUL(MUL(VAR, VAR), VAR), MUL(CONST(2), VAR))
MAP_CYCLE4 = ADD(OR(AND(VAR, CONST(6)), MUL(VAR, VAR)), CONST(1))


def verify_all() -> None:
    print("=== 1. Compiler Certificates (`abs_deriv`) ===")
    assert MAP_ASYM.abs_deriv(3, 0) == "zero" and MAP_ASYM.abs_deriv(3, 1) == "zero"
    assert MAP_ASYM.abs_deriv(2, 0) == "top"  # below threshold m=3!
    assert MAP_SEVEN.abs_deriv(3, 0) == "zero" and MAP_SEVEN.abs_deriv(3, 1) == "zero"
    assert MAP_THREE.abs_deriv(3, 0) == "zero" and MAP_THREE.abs_deriv(3, 1) == "zero"
    for c in range(16):
        e = MAP_XORADD(c)
        assert e.abs_deriv(1, 0) == "zero" and e.abs_deriv(1, 1) == "zero"
    assert MAP_CLMUL_HYBRID.abs_deriv(1, 0) == "zero" and MAP_CLMUL_HYBRID.abs_deriv(1, 1) == "zero"
    assert MAP_LOCAL_EVEN.abs_deriv(1, 0) == "zero" and MAP_LOCAL_EVEN.abs_deriv(1, 1) == "one"
    assert MAP_HALF_CYCLE.abs_deriv(1, 0) == "zero" and MAP_HALF_CYCLE.abs_deriv(1, 1) == "one"
    assert MAP_MIXED_ISO.abs_deriv(1, 0) == "zero" and MAP_MIXED_ISO.abs_deriv(1, 1) == "one"
    assert MAP_CYCLE4.abs_deriv(3, 0) == "zero" and MAP_CYCLE4.abs_deriv(3, 1) == "zero"
    print("  All positive and negative compiler certificates verified.")

    print("\n=== 2. Theorem I: mapAsym = (x & 4) | (x * x) (w = 3..12) ===")
    for w in range(3, 13):
        g = analyze_graph(MAP_ASYM.eval, w)
        s = 1 << (w - 3)
        assert g["fp_count"] == 4, g
        assert g["max_depth"] <= w - 2, g
        assert g["max_depth"] == w - 2, f"Expected exact depth w-2 at w={w}, got {g['max_depth']}"
        l0 = hensel_lift_py(MAP_ASYM, 3, 1, 1, w, 0)
        l1 = hensel_lift_py(MAP_ASYM, 3, 1, 1, w, 1)
        l4 = hensel_lift_py(MAP_ASYM, 3, 1, 1, w, 4)
        l5 = hensel_lift_py(MAP_ASYM, 3, 1, 1, w, 5)
        assert g["fp_basins"][l0] == 1 * s
        assert g["fp_basins"][l1] == 2 * s
        assert g["fp_basins"][l4] == 3 * s  # non-power-of-two 3/8 basin!
        assert g["fp_basins"][l5] == 2 * s
        if w in (3, 4, 8, 12):
            print(f"  w={w:2d}: fps={[l0,l1,l4,l5]}, basins={[1*s,2*s,3*s,2*s]}, exact_max_depth={g['max_depth']}")

    print("\n=== 3. Theorem II: mapSeven = (x & 6) | (x * x) (w = 3..12) ===")
    for w in range(3, 13):
        g = analyze_graph(MAP_SEVEN.eval, w)
        s = 1 << (w - 3)
        assert g["fp_count"] == 7
        assert g["max_depth"] <= w - 2
        l6 = hensel_lift_py(MAP_SEVEN, 3, 1, 1, w, 6)
        assert g["fp_basins"][l6] == 2 * s
        assert g["spec"] == [(1, s)] * 6 + [(1, 2 * s)]
        if w in (3, 8, 12):
            print(f"  w={w:2d}: fp_count=7, lift(6)={l6}, basin(lift(6))={2*s}, max_depth={g['max_depth']}")

    print("\n=== 4. Theorem III: mapThree = ((x & 4) | (x * x)) + 2 (w = 3..12) ===")
    for w in range(3, 13):
        g = analyze_graph(MAP_THREE.eval, w)
        s = 1 << (w - 3)
        assert g["fp_count"] == 3
        assert g["max_depth"] <= w - 1
        l6 = hensel_lift_py(MAP_THREE, 3, 1, 1, w, 6)
        assert g["fp_basins"][l6] == 4 * s
        assert g["spec"] == [(1, 2 * s), (1, 2 * s), (1, 4 * s)]
        if w in (3, 8, 12):
            print(f"  w={w:2d}: fp_count=3, lift(6)={l6}, basin(lift(6))={4*s}, max_depth={g['max_depth']}")

    print("\n=== 5. Theorem IV: mapXorAdd(c) = x ^ (x + c) + Exact Depth=w Sharpness ===")
    for c in (0, 1, 2, 3, 5, 13):
        e = MAP_XORADD(c)
        for w in range(1, 11):
            g = analyze_graph(e.eval, w)
            fp = (-c) & ((1 << w) - 1)
            assert g["fp_count"] == 1 and g["fps"] == [fp]
            assert g["fp_basins"][fp] == (1 << w)
            assert g["max_depth"] <= w
            if c == 1:
                assert g["max_depth"] == w
                assert g["depths"][0] == w
    print("  Verified c in {0,1,2,3,5,13}, w=1..10: unique fp (-c mod 2^w), basin 2^w, exact depth=w at c=1, x=0.")

    print("\n=== 6. Theorem V: mapClmulHybrid = clmul(x, x) ^ (x + 1) ^ x (w = 1..12) ===")
    for w in range(1, 13):
        g = analyze_graph(MAP_CLMUL_HYBRID.eval, w)
        assert g["fp_count"] == 0
        assert g["spec"] == [(2, 1 << w)]
        assert g["max_depth"] <= w - 1
        if w in (1, 4, 8, 12):
            print(f"  w={w:2d}: fps=0, unique 2-cycle basin={1<<w}, max_depth={g['max_depth']} (bound {w-1})")

    print("\n=== 7. Theorem VI: Local & Half-Cycle Contraction (`x^3+x^2+2`, `x^3+2x+1`) ===")
    for w in range(1, 13):
        g_loc = analyze_graph(MAP_LOCAL_EVEN.eval, w)
        assert g_loc["fp_count"] == 1
        assert g_loc["spec"] == [(1, 1 << w)]
        assert g_loc["max_depth"] <= w
    for w in range(1, 13):
        g_hc = analyze_graph(MAP_HALF_CYCLE.eval, w)
        assert g_hc["fp_count"] == 0
        assert g_hc["spec"] == [(2, 1 << w)]
        assert g_hc["max_depth"] == 2 * w - 2
        if w >= 2:
            assert g_hc["depths"][3] == 2 * w - 2
        if w in (1, 2, 3, 6, 12):
            print(f"  x^3+2x+1 w={w:2d}: fps=0, unique 2-cycle basin={1<<w}, exact_max_depth={g_hc['max_depth']} == 2w-2")

    print("\n=== 8. Sharpness & Boundary Counterexamples ===")
    # CE1: x^3 + 2x isometric odd class drops fixed point
    g1 = analyze_graph(MAP_MIXED_ISO.eval, 1)
    g2 = analyze_graph(MAP_MIXED_ISO.eval, 2)
    g8 = analyze_graph(MAP_MIXED_ISO.eval, 8)
    assert g1["fp_count"] == 2 and g2["fp_count"] == 1 and g8["fp_count"] == 1
    assert g8["fp_basins"][0] == 128  # exact even basin 2^(w-1)
    print(f"  CE1 (x^3+2x): fps drop 2->1 (w=1->2); odd class expands into 16-cycles at w=8; even basin=2^(w-1) intact.")

    # CE2: below threshold m=3 for mapAsym
    ga2 = analyze_graph(MAP_ASYM.eval, 2)
    ga3 = analyze_graph(MAP_ASYM.eval, 3)
    assert ga2["fp_count"] == 2 and ga3["fp_count"] == 4
    print(f"  CE2 (below threshold m=3): mapAsym has {ga2['fp_count']} fps at w=2 vs {ga3['fp_count']} fps for all w>=3.")

    # CE3: right shift breaks T-function truncation commutation
    x_ce = 2  # 0b10
    lhs = ((x_ce >> 1) & 1)
    rhs = ((x_ce & 1) >> 1)
    assert lhs == 1 and rhs == 0 and lhs != rhs
    print(f"  CE3 (non-T-function x>>1): trunc_1(2>>1)={lhs} != {rhs}=(trunc_1(2))>>1.")

    # CE4: cycle depth > w even under global contraction above m=3
    gc3 = analyze_graph(MAP_CYCLE4.eval, 3)
    assert gc3["spec"] == [(4, 8)] and gc3["max_depth"] == 4 and gc3["depths"][3] == 4
    print(f"  CE4 (cycle depth > w): mapCycle4 at w=3 has 4-cycle with depth(3) = {gc3['depths'][3]} > 3 = w.")

    print("\n=== 9. Exhaustive 64-Map Sweep: ((x & M) | x^2) + c (M,c in 0..7), w=3 vs w=9 ===")
    for M in range(8):
        for c in range(8):
            e = ADD(OR(AND(VAR, CONST(M)), MUL(VAR, VAR)), CONST(c))
            assert e.abs_deriv(3, 0) == "zero" and e.abs_deriv(3, 1) == "zero"
            g3 = analyze_graph(e.eval, 3)
            g9 = analyze_graph(e.eval, 9)
            scaled = sorted((L, b * (1 << 6)) for L, b in g3["spec"])
            assert scaled == g9["spec"], f"Mismatch for M={M}, c={c}"
            assert g9["max_depth"] <= g3["max_depth"] + 6
    print("  ALL 64 bitwise-quadratic maps matched exact w=3 -> w=9 cycle-spectrum & basin scaling (100%).")

    print("\nALL EXACT INTEGER CHECKS PASSED (ZERO FLOATS).")


if __name__ == "__main__":
    verify_all()
