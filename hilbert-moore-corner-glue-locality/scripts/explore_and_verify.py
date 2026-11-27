"""
Pure-Silicon Exact Integer & Rational Discovery, Certificate Synthesis,
Independent Instance Replay, and Sharpness Counterexample Suite for:

  Task 16 (dynsil-16): Hilbert-Curve Bit-State-Machine Bijection & Locality Engine
  (The Finite-State Corner-Glue & Product-Automaton Lifting Engine)

STRICT ZERO-FLOAT POLICY:
  All arithmetic uses exact Python `int` and `fractions.Fraction`.
  No floating-point values appear in any computation, certificate, or output.
  CPU-only deterministic execution.
"""

from collections import Counter
from fractions import Fraction
from math import comb, lcm


# ---------------------------------------------------------------------------
# 0. Pure-Integer Primitives (matching the Lean sources definitions exactly)
# ---------------------------------------------------------------------------
def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def popcount(n: int) -> int:
    return n.bit_count()


def val_base(B: int, n: int) -> int:
    assert B >= 2 and n >= 1
    c = 0
    while n % B == 0:
        n //= B
        c += 1
    return c


def bit_at(n: int, i: int) -> int:
    return (n >> i) & 1


# ---------------------------------------------------------------------------
# 1. General d-Dimensional Finite-State Bit-Block Transducer & Finite Certs
# ---------------------------------------------------------------------------
class BitBlockTransducer:
    def __init__(self, d, states, delta, omega, name):
        self.d = d
        self.states = list(states)
        self.delta = delta
        self.omega = omega
        self.name = name

    def eval_interleaved(self, w: int, s, t: int) -> int:
        mask = (1 << self.d) - 1
        out = 0
        for i in range(w - 1, -1, -1):
            q = (t >> (self.d * i)) & mask
            y = self.omega(s, q)
            out = (out << self.d) | y
            s = self.delta(s, q)
        return out

    def eval_coords(self, w: int, s, t: int) -> tuple:
        mask = (1 << self.d) - 1
        coords = [0] * self.d
        for i in range(w - 1, -1, -1):
            q = (t >> (self.d * i)) & mask
            y = self.omega(s, q)
            for j in range(self.d):
                coords[j] = (coords[j] << 1) | ((y >> j) & 1)
            s = self.delta(s, q)
        return tuple(coords)

    def check_step_bijection_cert(self):
        M = 1 << self.d
        inv = {}
        for s in self.states:
            outs = [self.omega(s, q) for q in range(M)]
            if sorted(outs) != list(range(M)):
                return False, None
            inv[s] = {self.omega(s, q): q for q in range(M)}
        return True, inv

    def check_corner_glue_cert(self):
        M = 1 << self.d
        entry = {s: self.omega(s, 0) for s in self.states}
        exit_ = {s: self.omega(s, M - 1) for s in self.states}
        for s in self.states:
            if entry[self.delta(s, 0)] != entry[s]:
                return False, f"entry stability failed at s={s}"
            if exit_[self.delta(s, M - 1)] != exit_[s]:
                return False, f"exit stability failed at s={s}"
        for s in self.states:
            for q in range(M - 1):
                a, b = self.omega(s, q), self.omega(s, q + 1)
                ex, en = exit_[self.delta(s, q)], entry[self.delta(s, q + 1)]
                if popcount(a ^ b) != 1:
                    return False, f"non-unit step at s={s}, q={q}"
                for i in range(self.d):
                    if bit_at(b, i) + bit_at(en, i) != bit_at(a, i) + bit_at(ex, i):
                        return False, f"glue equation failed at s={s}, q={q}, i={i}"
        return True, (entry, exit_)

    def check_mirror_cert(self, phi, flip_axis):
        M = 1 << self.d
        for s in self.states:
            for q in range(M):
                if self.delta(phi(s), M - 1 - q) != phi(self.delta(s, q)):
                    return False
                for i in range(self.d):
                    lhs = bit_at(self.omega(phi(s), M - 1 - q), i)
                    rhs = 1 - bit_at(self.omega(s, q), i) if flip_axis(i) else bit_at(self.omega(s, q), i)
                    if lhs != rhs:
                        return False
        return True


# ---------------------------------------------------------------------------
# 2. Concrete Transducers: 2D Hilbert, D4-Hilbert/Moore, 3D Hamilton-Hilbert
# ---------------------------------------------------------------------------
H2_BASE = (0, 2, 3, 1)


def h2_apply_v4(s: int, y: int) -> int:
    inv, sw = s >> 1, s & 1
    bx, by = y & 1, (y >> 1) & 1
    if sw:
        bx, by = by, bx
    if inv:
        bx, by = 1 - bx, 1 - by
    return bx | (by << 1)


def h2_omega(s: int, q: int) -> int:
    return h2_apply_v4(s, H2_BASE[q])


def h2_delta(s: int, q: int) -> int:
    inv, sw = s >> 1, s & 1
    if q == 0:
        return (inv << 1) | (1 - sw)
    if q == 3:
        return ((1 - inv) << 1) | (1 - sw)
    return s


def h2_mirror_phi(s: int) -> int:
    return (0, 3, 2, 1)[s]


hilbert2d = BitBlockTransducer(2, range(4), h2_delta, h2_omega, "Hilbert2D")


# D4-Hilbert (8 states) + Moore root wrapper
def d4_apply(s: int, y: int) -> int:
    fx, fy, sw = (s >> 2) & 1, (s >> 1) & 1, s & 1
    bx, by = y & 1, (y >> 1) & 1
    if sw:
        bx, by = by, bx
    bx ^= fx
    by ^= fy
    return bx | (by << 1)


def d4_omega(s: int, q: int) -> int:
    return d4_apply(s, H2_BASE[q])


def d4_delta(s: int, q: int) -> int:
    fx, fy, sw = (s >> 2) & 1, (s >> 1) & 1, s & 1
    if q == 0:
        return (fx << 2) | (fy << 1) | (1 - sw)
    if q == 3:
        return ((1 - fx) << 2) | ((1 - fy) << 1) | (1 - sw)
    return s


d4_hilbert = BitBlockTransducer(2, range(8), d4_delta, d4_omega, "D4-Hilbert2D")
MOORE_ROOT_DELTA = (5, 5, 3, 3)


def eval_moore_coords(w_plus_1: int, t: int) -> tuple:
    assert w_plus_1 >= 1
    w = w_plus_1 - 1
    q = t >> (2 * w)
    r = t & ((1 << (2 * w)) - 1)
    top = H2_BASE[q]
    lo = d4_hilbert.eval_coords(w, MOORE_ROOT_DELTA[q], r)
    return (((top & 1) << w) + lo[0], (((top >> 1) & 1) << w) + lo[1])


# 3D Hamilton-Hilbert (24 states)
def rotl3(x: int, r: int) -> int:
    r %= 3
    return ((x << r) | (x >> (3 - r))) & 7


def gray3(q: int) -> int:
    return q ^ (q >> 1)


H3_ENTRY_SUB = (0, 0, 0, 3, 3, 6, 6, 5)
H3_ROT_SUB = (1, 2, 2, 0, 0, 2, 2, 1)


def h3_omega(s: int, q: int) -> int:
    e, r = s // 3, s % 3
    return rotl3(gray3(q), r) ^ e


def h3_delta(s: int, q: int) -> int:
    e, r = s // 3, s % 3
    ne = (e ^ rotl3(H3_ENTRY_SUB[q], r)) & 7
    nr = (r + H3_ROT_SUB[q]) % 3
    return ne * 3 + nr


def h3_mirror_phi(s: int) -> int:
    e, r = s // 3, s % 3
    ne = (e ^ rotl3(4, r) ^ 4) & 7
    return ne * 3 + r


hilbert3d = BitBlockTransducer(3, range(24), h3_delta, h3_omega, "Hilbert3D-Hamilton")


# Counterexample transducers
z_order = BitBlockTransducer(2, [0], lambda s, q: 0, lambda s, q: q, "Z-Order2D")
bad_glue = BitBlockTransducer(
    2,
    range(4),
    lambda s, q: 0 if (s == 0 and q == 0) else h2_delta(s, q),
    h2_omega,
    "BadGlue2D",
)


# ---------------------------------------------------------------------------
# 3. Run Exact Verification & Counterexample Suite
# ---------------------------------------------------------------------------
def main():
    print("=== 1. Finite Certificate Synthesis & Verification ===")
    for T, mirror in [
        (hilbert2d, (h2_mirror_phi, lambda i: i == 0)),
        (d4_hilbert, None),
        (hilbert3d, (h3_mirror_phi, lambda i: i == 2)),
    ]:
        ok_bij, _ = T.check_step_bijection_cert()
        ok_glue, _ = T.check_corner_glue_cert()
        assert ok_bij and ok_glue, f"Certificate failed for {T.name}"
        ok_mir = T.check_mirror_cert(*mirror) if mirror else None
        if mirror:
            assert ok_mir, f"Mirror cert failed for {T.name}"
        print(
            f"  [PASS] {T.name} (d={T.d}, |S|={len(T.states)}): "
            f"StepBijectionCert={ok_bij}, CornerGlueCert={ok_glue}, MirrorSymCert={ok_mir}"
        )

    print("\n=== 2. Independent Exact Replay: 2D Hilbert (w = 1..6) ===")
    for w in range(1, 7):
        N = 1 << (2 * w)
        pts = [hilbert2d.eval_coords(w, 0, t) for t in range(N)]
        perm = [hilbert2d.eval_interleaved(w, 0, t) for t in range(N)]
        # Bijectivity
        assert len(set(pts)) == N and len(set(perm)) == N
        # Unit L1 adjacency, contiguous XOR mask, and pointwise Hamming law
        total_ham = 0
        for t in range(N - 1):
            dx = abs(pts[t + 1][0] - pts[t][0])
            dy = abs(pts[t + 1][1] - pts[t][1])
            assert dx + dy == 1
            k = val_base(4, t + 1)
            xor_x = pts[t][0] ^ pts[t + 1][0]
            xor_y = pts[t][1] ^ pts[t + 1][1]
            mask = (1 << (k + 1)) - 1
            assert (xor_x == mask and xor_y == 0) or (xor_x == 0 and xor_y == mask)
            ham = popcount(xor_x) + popcount(xor_y)
            assert ham == 1 + k
            total_ham += ham
        # Total switching-energy conservation: 3 * S + 3 * w == 4 * (4^w - 1)
        assert 3 * total_ham + 3 * w == 4 * (N - 1)
        # Mirror-reversal symmetry: H_w(4^w - 1 - t) = (2^w - 1 - x, y)
        M2 = (1 << w) - 1
        assert all(pts[N - 1 - t] == (M2 - pts[t][0], pts[t][1]) for t in range(N))
        # Exact Fibonacci Fixed-Point & Fibonacci-Square & 2-Cycle Binomial Laws!
        fix1 = sum(1 for t in range(N) if perm[t] == t)
        fix2 = sum(1 for t in range(N) if perm[perm[t]] == t)
        c2 = (fix2 - fix1) // 2
        assert fix1 == fib(w + 1)
        assert fix2 == fib(w + 1) ** 2
        assert c2 == comb(fib(w + 1), 2)
        # Verify ALL 16 pairs (s1, s2) of Fix(Pi_{w, s2} o Pi_{w, s1}) at w <= 5
        if w <= 5:
            perms_all = [[hilbert2d.eval_interleaved(w, s, t) for t in range(N)] for s in range(4)]
            F1, F2 = fib(w + 1), fib(w + 2)
            expected_mat = [
                [F1 * F1, F2, F1, 0],
                [F2, F2 * F2, F1 * F2, 0],
                [F1, F1 * F2, 1, 0],
                [0, 0, 0, 0],
            ]
            for a in range(4):
                for b in range(4):
                    cnt = sum(1 for t in range(N) if perms_all[b][perms_all[a][t]] == t)
                    assert cnt == expected_mat[a][b]
        # Verify exact 3-smoothness (all cycle lengths divide 12^w)
        vis = [False] * N
        order = 1
        for t in range(N):
            if not vis[t]:
                c = 0
                cur = t
                while not vis[cur]:
                    vis[cur] = True
                    cur = perm[cur]
                    c += 1
                assert (12 ** w) % c == 0
                order = lcm(order, c)
        # Verify universal L1^2 <= 16 * dt (exhaustive for w <= 5) and exact witness family
        if w <= 5:
            for u in range(N):
                xu, yu = pts[u]
                for v in range(u + 1, N):
                    xv, yv = pts[v]
                    l1 = abs(xv - xu) + abs(yv - yu)
                    assert l1 * l1 <= 16 * (v - u)
        if w >= 2:
            k = w - 1
            uw = ((1 << (2 * k)) - 1) // 3
            vw = ((1 << (2 * w)) - 1) // 3
            l1_wit = abs(pts[vw][0] - pts[uw][0]) + abs(pts[vw][1] - pts[uw][1])
            assert vw - uw == 4 ** k and l1_wit == 3 * (2 ** k) - 2
            ratio_wit = Fraction(l1_wit * l1_wit, vw - uw)
        else:
            ratio_wit = Fraction(2, 1)
        print(
            f"  [PASS] w={w} (N={N:4d}): Fix={fix1:2d}=F_{w+1}, Fix2={fix2:3d}=F_{w+1}^2, "
            f"c2={c2:2d}=C(F_{w+1},2), ord={order:3d} | 12^{w}, sum_ham={total_ham:4d}, "
            f"L1_wit^2/dt={ratio_wit}"
        )

    print("\n=== 3. Independent Exact Replay: 2D Moore Closed Hamiltonian Cycle (w = 1..5) ===")
    for w in range(1, 6):
        N = 1 << (2 * w)
        pts = [eval_moore_coords(w, t) for t in range(N)]
        assert len(set(pts)) == N
        for t in range(N):
            nxt = (t + 1) % N
            assert abs(pts[nxt][0] - pts[t][0]) + abs(pts[nxt][1] - pts[t][1]) == 1
        print(f"  [PASS] Moore w={w} (N={N:4d}): bijective=True, cyclic L1=1 (wrap {pts[N-1]} -> {pts[0]})")

    print("\n=== 4. Independent Exact Replay: 3D Hamilton-Hilbert (w = 1..3) ===")
    for w in range(1, 4):
        N = 1 << (3 * w)
        pts = [hilbert3d.eval_coords(w, 0, t) for t in range(N)]
        perm = [hilbert3d.eval_interleaved(w, 0, t) for t in range(N)]
        assert len(set(pts)) == N and len(set(perm)) == N
        total_ham = 0
        for t in range(N - 1):
            l1 = sum(abs(pts[t + 1][j] - pts[t][j]) for j in range(3))
            assert l1 == 1
            k = val_base(8, t + 1)
            xors = [pts[t][j] ^ pts[t + 1][j] for j in range(3)]
            ham = sum(popcount(x) for x in xors)
            assert ham == 1 + k
            total_ham += ham
        assert 7 * total_ham + 7 * w == 8 * (N - 1)
        M3 = (1 << w) - 1
        assert all(pts[N - 1 - t] == (pts[t][0], pts[t][1], M3 - pts[t][2]) for t in range(N))
        fix1 = sum(1 for t in range(N) if perm[t] == t)
        fix2 = sum(1 for t in range(N) if perm[perm[t]] == t)
        assert fix1 == fib(w + 2)
        print(
            f"  [PASS] 3D w={w} (N={N:3d}): bijective=True, L1=1, mirror(x,y,~z)=True, "
            f"sum_ham={total_ham:3d}, Fix={fix1}=F_{w+2}, Fix2={fix2}"
        )

    print("\n=== 5. Sharpness & Falsification Counterexamples ===")
    # CE 1: Z-order fails CornerGlueCert & has L1 jump = 2^w (L1^2/dt = 4^w)
    ok_z_bij, _ = z_order.check_step_bijection_cert()
    ok_z_glue, reason_z = z_order.check_corner_glue_cert()
    assert ok_z_bij and not ok_z_glue
    for w in range(1, 6):
        t = (1 << (2 * w - 1)) - 1
        p1, p2 = z_order.eval_coords(w, 0, t), z_order.eval_coords(w, 0, t + 1)
        l1 = abs(p2[0] - p1[0]) + abs(p2[1] - p1[1])
        assert l1 == (1 << w) and l1 * l1 == (4 ** w)
    print(f"  [CE-1] Z-Order2D: StepBijectionCert=True, CornerGlueCert=False ({reason_z}); "
          f"L1(2^(2w-1)-1, 2^(2w-1)) = 2^w => L1^2/dt = 4^w (unbounded)")

    # CE 2: Single-transition perturbation BadGlue2D
    ok_b_bij, _ = bad_glue.check_step_bijection_cert()
    ok_b_glue, reason_b = bad_glue.check_corner_glue_cert()
    assert ok_b_bij and not ok_b_glue
    p3, p4 = bad_glue.eval_coords(2, 0, 3), bad_glue.eval_coords(2, 0, 4)
    l1_bad = abs(p4[0] - p3[0]) + abs(p4[1] - p3[1])
    assert l1_bad == 3 and (p3[1] ^ p4[1]) == 2
    print(f"  [CE-2] BadGlue2D: StepBijectionCert=True, CornerGlueCert=False ({reason_b}); "
          f"at w=2, t=3->4: {p3}->{p4}, L1={l1_bad} != 1, y-XOR={p3[1] ^ p4[1]} != 3")

    # CE 3 & CE 4: 3D Hilbert at w=2 breaks BOTH 3-smoothness (7-cycle at t=1) and Fibonacci-square (5 != 9)
    cur = 1
    orbit = [cur]
    for _ in range(7):
        cur = hilbert3d.eval_interleaved(2, 0, cur)
        orbit.append(cur)
    assert orbit[0] == orbit[7] == 1 and 1 not in orbit[1:7]
    # Verify 144th iterate != 1
    cur144 = 1
    for _ in range(144):
        cur144 = hilbert3d.eval_interleaved(2, 0, cur144)
    assert cur144 != 1
    perm3_2 = [hilbert3d.eval_interleaved(2, 0, t) for t in range(64)]
    fix3_1 = sum(1 for t in range(64) if perm3_2[t] == t)
    fix3_2 = sum(1 for t in range(64) if perm3_2[perm3_2[t]] == t)
    assert fix3_1 == 3 == fib(4) and fix3_2 == 5 != 9 == fib(4) ** 2
    print(f"  [CE-3] Hilbert3D (d=3, w=2): explicit 7-cycle orbit at t=1: {orbit[:-1]} (iter^144(1)={cur144} != 1)")
    print(f"  [CE-4] Hilbert3D (d=3, w=2): Fix(Pi3)={fix3_1}=F_4, yet Fix(Pi3^2)={fix3_2} != 9=F_4^2")

    print("\nALL EXACT REPLAYS, CERTIFICATES, AND SHARPNESS COUNTEREXAMPLES PASSED (ZERO FLOATS).")


if __name__ == "__main__":
    main()
