"""
Independent Pure-Silicon Exact-Integer Explorer, Certificate Synthesizer,
and Verification Replay Suite for:

  Task 1: Binary Carry-Defect Bisimulation Compiler
          & Universal 2^m-Operand Hypercube Carry-Shadow Collapse Theorem

Strictly pure integer arithmetic (Python `int` only, ZERO floating-point operations).
Independently reproduces every finite certificate (including the exact 32-bit
bisimulation bitmask `domAbsCert = 2223046689` verified in `Proof.lean`),
all exhaustive & high-bitwidth checks up to n = 64 operands (m = 6), and
every sharpness / mutation counterexample.
"""

from itertools import permutations, product
import random


# =============================================================================
# 1. Pure-Integer Silicon Primitives
# =============================================================================

def bit_int(b: bool) -> int:
    return 1 if b else 0


def bdiff(a: int, b: int) -> int:
    return (a | b) ^ b


def carry_mask(a: int, b: int) -> int:
    return (a + b) ^ a ^ b


def bsub(a: int, b: int) -> bool:
    return bdiff(a, b) == 0


def is_cs(a: int, b: int) -> bool:
    return bsub(b, a) and ((bdiff(a, b) & (2 * b)) == 0)


def phi(a: int, b: int) -> tuple[int, int]:
    return (a + b, a ^ b)


def phi_iter(k: int, a: int, b: int) -> tuple[int, int]:
    for _ in range(k):
        a, b = phi(a, b)
    return a, b


def eval_base(B: int, n: int) -> int:
    """Exact base-B binary digit evaluation: sum_j bit_j(n) * B^j."""
    total = 0
    weight = 1
    while n > 0:
        if n & 1:
            total += weight
        weight *= B
        n >>= 1
    return total


def popcount(n: int) -> int:
    return n.bit_count()


# =============================================================================
# 2. Independent Transducer Compiler & Guarded Bisimulation Certificate Engine
#    (Mirrors `Proof.lean` Sections 3-5 identically to synthesize `R : int`.)
# =============================================================================

class Transducer:
    def __init__(self, k: int, num_states: int, init: int, next_fn, out_fn, flush_fn):
        self.k = k
        self.num_states = num_states
        self.init = init
        self.next = next_fn
        self.out = out_fn
        self.flush = flush_fn
        # Independently check flush consistency on every state!
        for s in range(num_states):
            expected = bit_int(out_fn(s, 0)) + 2 * flush_fn(next_fn(s, 0))
            assert flush_fn(s) == expected, f"Flush mismatch at state {s}: {flush_fn(s)} != {expected}"


def t_var(k: int, i: int) -> Transducer:
    return Transducer(k, 1, 0, lambda s, u: 0, lambda s, u: bool((u >> i) & 1), lambda s: 0)


def t_zero(k: int) -> Transducer:
    return Transducer(k, 1, 0, lambda s, u: 0, lambda s, u: False, lambda s: 0)


def t_binbit(bop, nop, T1: Transducer, T2: Transducer) -> Transducer:
    k = T1.k
    n2 = T2.num_states
    return Transducer(
        k,
        T1.num_states * n2,
        T1.init * n2 + T2.init,
        lambda s, u: T1.next(s // n2, u) * n2 + T2.next(s % n2, u),
        lambda s, u: bop(T1.out(s // n2, u), T2.out(s % n2, u)),
        lambda s: nop(T1.flush(s // n2), T2.flush(s % n2)),
    )


def t_carry(T1: Transducer, T2: Transducer) -> Transducer:
    k = T1.k
    n2 = T2.num_states

    def nxt(s: int, u: int) -> int:
        p, c = s // 2, bool(s % 2)
        s1, s2 = p // n2, p % n2
        b1, b2 = T1.out(s1, u), T2.out(s2, u)
        c_next = (b1 and b2) or ((b1 ^ b2) and c)
        p_next = T1.next(s1, u) * n2 + T2.next(s2, u)
        return p_next * 2 + bit_int(c_next)

    def fl(s: int) -> int:
        p, c = s // 2, s % 2
        s1, s2 = p // n2, p % n2
        f1, f2 = T1.flush(s1), T2.flush(s2)
        return (f1 + f2 + c) ^ f1 ^ f2

    return Transducer(
        k,
        T1.num_states * n2 * 2,
        (T1.init * n2 + T2.init) * 2,
        nxt,
        lambda s, u: bool(s % 2),
        fl,
    )


def t_shl1(T: Transducer) -> Transducer:
    return Transducer(
        T.k,
        T.num_states * 2,
        T.init * 2,
        lambda s, u: T.next(s // 2, u) * 2 + bit_int(T.out(s // 2, u)),
        lambda s, u: bool(s % 2),
        lambda s: (s % 2) + 2 * T.flush(s // 2),
    )


def triple_idx(n1: int, n2: int, sG: int, s1: int, s2: int) -> int:
    return (sG * n1 + s1) * n2 + s2


def synthesize_guarded_certificate(G: Transducer, T1: Transducer, T2: Transducer) -> int:
    """BFS reachable bitmask in S_G x S_1 x S_2 along G.out == False."""
    n1, n2 = T1.num_states, T2.num_states
    init_bit = triple_idx(n1, n2, G.init, T1.init, T2.init)
    R = 1 << init_bit
    queue = [(G.init, T1.init, T2.init)]
    while queue:
        sG, s1, s2 = queue.pop()
        for u in range(1 << G.k):
            if not G.out(sG, u):
                nsG, ns1, ns2 = G.next(sG, u), T1.next(s1, u), T2.next(s2, u)
                idx = triple_idx(n1, n2, nsG, ns1, ns2)
                if not ((R >> idx) & 1):
                    R |= (1 << idx)
                    queue.append((nsG, ns1, ns2))
    return R


def check_guarded_bisim_witness(G: Transducer, T1: Transducer, T2: Transducer, R: int) -> bool:
    nG, n1, n2 = G.num_states, T1.num_states, T2.num_states
    if not ((R >> triple_idx(n1, n2, G.init, T1.init, T2.init)) & 1):
        return False
    for sG in range(nG):
        for s1 in range(n1):
            for s2 in range(n2):
                if (R >> triple_idx(n1, n2, sG, s1, s2)) & 1:
                    if G.flush(sG) == 0 and T1.flush(s1) != T2.flush(s2):
                        return False
                    for u in range(1 << G.k):
                        if not G.out(sG, u):
                            if T1.out(s1, u) != T2.out(s2, u):
                                return False
                            idx = triple_idx(n1, n2, G.next(sG, u), T1.next(s1, u), T2.next(s2, u))
                            if not ((R >> idx) & 1):
                                return False
    return True


# =============================================================================
# 3. 2^m-Operand Hypercube Silicon-Hadamard Operators
# =============================================================================

def stage_cube(vec: tuple[int, ...], stride: int) -> tuple[int, ...]:
    a = list(vec)
    n = len(a)
    for i in range(0, n, stride * 2):
        for j in range(i, i + stride):
            u, v = a[j], a[j + stride]
            a[j] = u + v
            a[j + stride] = u ^ v
    return tuple(a)


def stage_sq_cube(vec: tuple[int, ...], stride: int) -> tuple[int, ...]:
    return stage_cube(stage_cube(vec, stride), stride)


def Q_m(vec: tuple[int, ...], m: int, order: tuple[int, ...] | None = None) -> tuple[int, ...]:
    if order is None:
        order = tuple(range(m))
    v = vec
    for r in order:
        v = stage_sq_cube(v, 1 << r)
    return v


def is_dom_cube(vec: tuple[int, ...], m: int) -> bool:
    n = 1 << m
    for r in range(m):
        s = 1 << r
        for i in range(0, n, 2 * s):
            for j in range(i, i + s):
                if not bsub(vec[j + s], vec[j]):
                    return False
    return True


def Q_m_bv(vec: tuple[int, ...], m: int, w: int) -> tuple[int, ...]:
    mask = (1 << w) - 1
    a = list(vec)
    n = len(a)
    for r in range(m):
        stride = 1 << r
        for _ in range(2):
            for i in range(0, n, stride * 2):
                for j in range(i, i + stride):
                    u, v = a[j], a[j + stride]
                    a[j] = (u + v) & mask
                    a[j + stride] = (u ^ v) & mask
    return tuple(a)


# =============================================================================
# 4. Verification Suites
# =============================================================================

def suite_1_certificate_synthesis():
    print("[Suite 1] Guarded Carry-Mealy Bisimulation Certificate Synthesis & Mutation Tests")
    a0, a1, a2, a3 = t_var(4, 0), t_var(4, 1), t_var(4, 2), t_var(4, 3)
    t_bdiff = lambda x, y: t_binbit(lambda p, q: p and (not q), bdiff, x, y)
    t_bor = lambda x, y: t_binbit(lambda p, q: p or q, lambda p, q: p | q, x, y)

    G_dom = t_bor(
        t_bdiff(a1, a0),
        t_bor(t_bdiff(a2, a0), t_bor(t_bdiff(a3, a1), t_bdiff(a3, a2))),
    )
    LHS_dom = t_carry(t_carry(a0, a1), t_carry(a2, a3))
    RHS_dom = t_shl1(t_carry(a0, a3))

    cert = synthesize_guarded_certificate(G_dom, LHS_dom, RHS_dom)
    assert cert == 2223046689, f"Certificate mismatch: got {cert}, expected 2223046689"
    assert popcount(cert) == 6
    assert check_guarded_bisim_witness(G_dom, LHS_dom, RHS_dom, cert) is True

    # Hostile mutation tests (must ALL return False!)
    assert check_guarded_bisim_witness(G_dom, LHS_dom, RHS_dom, cert ^ 1) is False
    assert check_guarded_bisim_witness(t_zero(4), LHS_dom, RHS_dom, cert) is False
    for bit_idx in range(32):
        if (cert >> bit_idx) & 1:
            assert check_guarded_bisim_witness(G_dom, LHS_dom, RHS_dom, cert ^ (1 << bit_idx)) is False

    print(f"  PASS: Synthesized exact certificate domAbsCert = {cert} (0x{cert:08x}, {popcount(cert)}/32 states reachable).")
    print("  PASS: All 6 single-bit deletion mutations and unguarded mutation rejected.")


def suite_2_exhaustive_core_laws():
    print("[Suite 2] Exhaustive Verification of Core Stateful Laws (Laws 1-8)")
    for x, y in product(range(64), repeat=2):
        a1, b1 = phi(x, y)
        a2, b2 = phi(a1, b1)
        assert a2 == 2 * (x | y) and b2 == carry_mask(x, y)
        assert carry_mask(a1, b1) == 2 * (a1 & b1)
        assert carry_mask(x, y) + carry_mask(a1, b1) == 2 * (x | y)
        assert (carry_mask(x, y) & carry_mask(a1, b1)) == 0
        assert is_cs(a2, b2)
        # Exact sandwich iff
        lhs = (carry_mask(x, y) == 2 * y)
        rhs = bsub(x & (2 * y), y) and bsub(y, x | (2 * y))
        assert lhs == rhs
        if is_cs(x, y):
            assert phi_iter(2, x, y) == (2 * x, 2 * y)
        # Phi^{k+2} = 2 * Phi^k for k = 2, 3, 4
        for k in (2, 3, 4):
            uk, vk = phi_iter(k, x, y)
            assert phi_iter(k + 2, x, y) == (2 * uk, 2 * vk)

    dom_count = 0
    for a, b, c, d in product(range(16), repeat=4):
        if bsub(b, a) and bsub(c, a) and bsub(d, b) and bsub(d, c):
            dom_count += 1
            assert carry_mask(carry_mask(a, b), carry_mask(c, d)) == 2 * carry_mask(a, d)
            assert carry_mask(carry_mask(a, b), carry_mask(c, d)) == carry_mask(carry_mask(a, c), carry_mask(b, d))
    print(f"  PASS: Exhaustive [0..63]^2 (4,096 pairs) and [0..15]^4 ({dom_count} dominated quadruples) verified.")


def suite_3_baseB_coboundary():
    print("[Suite 3] Universal Base-B Carry-Defect Coboundary Law (B in {-5,-2,-1,0,1,2,3,7})")
    rng = random.Random(20261126)
    pairs = [(rng.randrange(1 << 40), rng.randrange(1 << 40)) for _ in range(200)]
    for B in (-5, -2, -1, 0, 1, 2, 3, 7):
        for x, y in pairs:
            lhs = eval_base(B, x) + eval_base(B, y) - eval_base(B, x + y)
            rhs = (2 - B) * eval_base(B, carry_mask(x, y) // 2)
            assert lhs == rhs
    for x, y in pairs:
        assert popcount(x) + popcount(y) == popcount(x + y) + popcount(carry_mask(x, y))
        assert eval_base(-1, x) + eval_base(-1, y) - eval_base(-1, x + y) == 3 * eval_base(-1, carry_mask(x, y) // 2)
    print("  PASS: Base-B Coboundary Law, Kummer Popcount (B=1), and Mod-3 Alternating Sum (B=-1) verified on 40-bit pairs.")


def suite_4_hypercube_collapse():
    print("[Suite 4] Universal 2^m-Operand Hypercube Collapse (m = 1..6, n = 2..64 operands, up to 128-bit)")
    # Exhaustive [0..15]^4 for m=2
    fails_k1 = 0
    for x in product(range(16), repeat=4):
        q1 = Q_m(x, 2)
        assert is_dom_cube(q1, 2)
        q2 = Q_m(q1, 2)
        q3 = Q_m(q2, 2)
        if q2 != tuple(4 * v for v in q1):
            fails_k1 += 1
        assert q3 == tuple(4 * v for v in q2)
        assert q2[0] == 4 * q1[0]
        for I in range(1, 4):
            assert q2[I] == 2 * carry_mask(q1[0], q1[I])
    assert fails_k1 == 10800

    # High-dimensional & 128-bit stress test for m = 1..6 (up to 64 operands!)
    rng = random.Random(20261127)
    for m in range(1, 7):
        n = 1 << m
        trials = 40 if m <= 4 else 12
        for _ in range(trials):
            x = tuple(rng.randrange(1 << 128) for _ in range(n))
            y = Q_m(x, m)
            assert is_dom_cube(y, m)
            z = Q_m(y, m)
            # Closed form on dominated cube y = Q_m(x)
            assert z[0] == (1 << m) * y[0]
            for I in range(1, n):
                assert z[I] == (1 << (m - 1)) * carry_mask(y[0], y[I])
            # Collapse Q_m^3 = 2^m * Q_m^2 and Q_m^4 = 2^{2m} * Q_m^2
            z3 = Q_m(z, m)
            z4 = Q_m(z3, m)
            assert z3 == tuple((1 << m) * v for v in z)
            assert z4 == tuple((1 << (2 * m)) * v for v in z)
            # Base-B spectral scaling (B = -1, 1, 2) & popcount invariance
            for I in range(n):
                assert popcount(z3[I]) == popcount(z[I])
                assert eval_base(-1, z3[I]) == ((-1) ** m) * eval_base(-1, z[I])
            # Nonlinear axis commutation on dominated cube y (reverse axis order matches forward!)
            z_rev = Q_m(y, m, tuple(reversed(range(m))))
            assert z_rev == z
    print("  PASS: Exhaustive m=2 [0..15]^4 (10,800/65,536 fail k=1; 0/65,536 fail k=2).")
    print("  PASS: 128-bit random stress tests verified for m=1..6 (n=2,4,8,16,32,64 operands).")


def suite_5_bitvec_nilpotency():
    print("[Suite 5] Universal BitVec w Modular Nilpotency (m = 1..4, w in {1, 4, 7, 16, 32})")
    rng = random.Random(314159)
    for m in range(1, 5):
        n = 1 << m
        for w in (1, 4, 7, 16, 32):
            k = (w + m - 1) // m
            assert m * k >= w
            for _ in range(25):
                x = tuple(rng.randrange(1 << w) for _ in range(n))
                v = x
                for _ in range(k + 2):
                    v = Q_m_bv(v, m, w)
                assert v == (0,) * n
    print("  PASS: Universal nilpotency Q_m^{k+2}(x) = 0 (m*k >= w) verified across all tested (m, w).")


def suite_6_sharpness_counterexamples():
    print("[Suite 6] Sharpness Counterexamples (All Thresholds & Hypotheses Tight)")
    # 1. m=1, k=1 fails
    assert phi_iter(3, 1, 3) == (12, 0) != (8, 4) == tuple(2 * c for c in phi_iter(1, 1, 3))
    # 2. m=2, k=1 fails
    x_k1 = (0, 2, 1, 1)
    q1, q2 = Q_m(x_k1, 2), Q_m(Q_m(x_k1, 2), 2)
    assert q1 == (12, 4, 0, 0) and q2 == (48, 48, 0, 0) != tuple(4 * c for c in q1)
    # 3. Non-commutativity of S_0^2 and S_1^2 on N^4
    x_nc = (0, 1, 1, 0)
    assert Q_m(x_nc, 2, (0, 1)) == (4, 0, 4, 0) != (4, 4, 0, 0) == Q_m(x_nc, 2, (1, 0))
    # 4. Consecutive axis squaring S_1^4 o S_0^4 fails scaling
    y_consec = stage_sq_cube(stage_sq_cube(stage_sq_cube(stage_sq_cube(x_k1, 1), 1), 2), 2)
    assert y_consec == (48, 16, 0, 0) and Q_m(y_consec, 2) == (192, 192, 0, 0) != tuple(4 * c for c in y_consec)
    # 5a-5d. All 4 individual dominance guards in Dominated Carry-Absorption are strictly necessary
    assert bsub(1, 1) and bsub(1, 3) and bsub(1, 1) and not bsub(3, 1)
    assert carry_mask(carry_mask(1, 3), carry_mask(1, 1)) == 12 != 4 == 2 * carry_mask(1, 1)
    assert carry_mask(carry_mask(1, 1), carry_mask(3, 1)) == 12 != 4 == 2 * carry_mask(1, 1)
    assert carry_mask(carry_mask(1, 0), carry_mask(1, 1)) == 0 != 4 == 2 * carry_mask(1, 1)
    assert carry_mask(carry_mask(1, 1), carry_mask(0, 1)) == 0 != 4 == 2 * carry_mask(1, 1)
    # 6. Sandwich Theorem strictly sharper than subset
    assert carry_mask(3947, 65146) == 2 * 65146 and not bsub(65146, 3947)
    # 7. Replacing XOR by OR breaks butterfly collapse
    a, b = 1, 3
    traj = [(a, b)]
    for _ in range(4):
        a, b = a + b, a | b
        traj.append((a, b))
    assert traj[4] != (2 * traj[2][0], 2 * traj[2][1])
    print("  PASS: All 10 sharpness counterexamples independently verified.")


if __name__ == "__main__":
    suite_1_certificate_synthesis()
    suite_2_exhaustive_core_laws()
    suite_3_baseB_coboundary()
    suite_4_hypercube_collapse()
    suite_5_bitvec_nilpotency()
    suite_6_sharpness_counterexamples()
    print("\nALL 6 PURE-SILICON EXACT-INTEGER VERIFICATION SUITES PASSED (0 FLOATS).")
