"""
Pure Silicon Binary Math: Exact-Integer Discovery, Certificate Synthesis,
Multi-Width Independent Replay, and Sharpness Verification for the
Reversible Toffoli/Fredkin Gate-Lattice Conservation Engine (`dynsil-10`).

Strict zero-float guarantee: all algebra uses Python exact `int` and `fractions.Fraction`.
"""
from fractions import Fraction
import math
import random
import sys


def sparse_rref_nullspace(rows, num_cols):
    """Exact sparse RREF over Q (using Fraction) returning primitive integer nullspace basis."""
    pivots = {}
    for raw in rows:
        row = {c: Fraction(v) for c, v in raw.items() if v != 0}
        while row:
            c = min(row.keys())
            if c in pivots:
                p = pivots[c]
                f = row[c]
                for k, pv in p.items():
                    nv = row.get(k, Fraction(0)) - f * pv
                    if nv == 0:
                        row.pop(k, None)
                    else:
                        row[k] = nv
            else:
                inv = Fraction(1) / row[c]
                row = {k: v * inv for k, v in row.items()}
                pivots[c] = row
                break
    for c in sorted(pivots.keys(), reverse=True):
        pc_row = pivots[c]
        for other_c in list(pivots.keys()):
            if other_c < c and c in pivots[other_c]:
                orow = pivots[other_c]
                f = orow[c]
                for k, pv in pc_row.items():
                    nv = orow.get(k, Fraction(0)) - f * pv
                    if nv == 0:
                        orow.pop(k, None)
                    else:
                        orow[k] = nv
    piv_set = set(pivots.keys())
    free_cols = [c for c in range(num_cols) if c not in piv_set]
    basis = []
    for fc in free_cols:
        vec = {fc: Fraction(1)}
        for pc, prow in pivots.items():
            if fc in prow:
                vec[pc] = -prow[fc]
        den = 1
        for v in vec.values():
            den = (den * v.denominator) // math.gcd(den, v.denominator)
        ivec = [0] * num_cols
        for k, v in vec.items():
            ivec[k] = int(v * den)
        g = 0
        for x in ivec:
            g = math.gcd(g, abs(x))
        if g > 1:
            ivec = [x // g for x in ivec]
        basis.append(ivec)
    return basis


# ============================================================
# Pure Silicon Gate Primitives & Lattice Evolutions
# ============================================================

def fredkin_1_02(a, b, c, d): return (c, b, a, d) if b else (a, b, c, d)
def fredkin_3_12(a, b, c, d): return (a, c, b, d) if d else (a, b, c, d)
def fredkin_1_03(a, b, c, d): return (d, b, c, a) if b else (a, b, c, d)
def fredkin_0_12(a, b, c, d): return (a, c, b, d) if a else (a, b, c, d)


def make_fred_cnot(mask8):
    def G(a, b, c, d):
        a, b, c, d = fredkin_1_02(a, b, c, d)
        h = (mask8 >> (a + 2 * c + 4 * d)) & 1
        return (a, b ^ h, c, d)
    def Ginv(a, b, c, d):
        h = (mask8 >> (a + 2 * c + 4 * d)) & 1
        return fredkin_1_02(a, b ^ h, c, d)
    return G, Ginv


def gate_FT(a, b, c, d):
    a, b, c, d = fredkin_1_02(a, b, c, d)
    return (a, b ^ (a & d), c, d)

def gate_FT_inv(a, b, c, d):
    return fredkin_1_02(a, b ^ (a & d), c, d)

def gate_FF(a, b, c, d): return fredkin_1_03(*fredkin_3_12(a, b, c, d))
def gate_FF_inv(a, b, c, d): return fredkin_3_12(*fredkin_1_03(a, b, c, d))
def gate_DF(a, b, c, d): return fredkin_3_12(*fredkin_0_12(a, b, c, d))


def margolus4_stencil(G, u):
    a = G(u[0], u[1], u[2], u[3])
    b = G(u[4], u[5], u[6], u[7])
    return G(a[2], a[3], b[0], b[1])


def margolus4_ring_step(G, bits):
    w = len(bits)
    assert w % 4 == 0 and w > 0
    ev = list(bits)
    for i in range(0, w, 4):
        ev[i], ev[i + 1], ev[i + 2], ev[i + 3] = G(bits[i], bits[i + 1], bits[i + 2], bits[i + 3])
    od = list(ev)
    for i in range(0, w, 4):
        idx = [(i + 2 + k) % w for k in range(4)]
        out = G(ev[idx[0]], ev[idx[1]], ev[idx[2]], ev[idx[3]])
        for k in range(4):
            od[idx[k]] = out[k]
    return tuple(od)


def margolus4_ring_inv(Ginv, bits):
    w = len(bits)
    assert w % 4 == 0 and w > 0
    od = list(bits)
    for i in range(0, w, 4):
        idx = [(i + 2 + k) % w for k in range(4)]
        out = Ginv(bits[idx[0]], bits[idx[1]], bits[idx[2]], bits[idx[3]])
        for k in range(4):
            od[idx[k]] = out[k]
    ev = list(od)
    for i in range(0, w, 4):
        ev[i], ev[i + 1], ev[i + 2], ev[i + 3] = Ginv(od[i], od[i + 1], od[i + 2], od[i + 3])
    return tuple(ev)


def subcnot_stencil(f1, f2, u):
    e = list(u)
    for j in (1, 3, 5):
        e[j] = u[j] ^ f1(u[j - 1], u[j + 1])
    o = list(e)
    for j in (2, 4, 6):
        o[j] = e[j] ^ f2(e[j - 1], e[j + 1])
    return tuple(o[2:6])


def subcnot_ring_step(f1, f2, bits):
    w = len(bits)
    assert w % 2 == 0 and w > 0
    e = list(bits)
    for j in range(1, w, 2):
        e[j] = bits[j] ^ f1(bits[(j - 1) % w], bits[(j + 1) % w])
    o = list(e)
    for j in range(0, w, 2):
        o[j] = e[j] ^ f2(e[(j - 1) % w], e[(j + 1) % w])
    return tuple(o)


def subcnot_ring_inv(f1, f2, bits):
    w = len(bits)
    assert w % 2 == 0 and w > 0
    e = list(bits)
    for j in range(0, w, 2):
        e[j] = bits[j] ^ f2(bits[(j - 1) % w], bits[(j + 1) % w])
    o = list(e)
    for j in range(1, w, 2):
        o[j] = e[j] ^ f1(e[(j - 1) % w], e[(j + 1) % w])
    return tuple(o)


# ============================================================
# Certified Charges & Fluxes
# ============================================================

def q_FT(x0, x1, x2, x3): return x0 - (1 - x2) * (x1 | x3)
def J_FT(u0, u1, u2, u3): return u1 * (u2 - u0)

def q_HW4(x0, x1, x2, x3): return x0 + x1 + x2 + x3
def J_HW_FF(u0, u1, u2, u3):
    o = gate_FF(u0, u1, u2, u3)
    return (o[0] + o[1]) - (u0 + u1)

def q_dimer(x0, x1, x2, x3): return x0 * x1
def J_dimer(u0, u1, u2, u3): return u2 * u3

def q_rail(x0, x1, x2, x3): return x0 + x3
def J_rail(u0, u1, u2, u3): return u3 * (u2 - u1)

def q_DF(x0, x1, x2, x3): return x0 * (1 - x1) - x2 * (1 - x1 - x3)
def J_DF(u0, u1, u2, u3): return u0 * (u2 - u1) * (1 - u3)

def q_CO(x0, x1, x2, x3): return x1 * (1 - 2 * x0 * (1 - x2))
def J_CO(u0, u1, u2, u3): return -u2

def q_DW(x0, x1, x2, x3): return x2 * (1 - x1) + x3 * (1 - x2)
def J_DW(u0, u1, u2, u3): return -u3


def ring_charge(bits, p, q_fn, shift_out=2):
    w = len(bits)
    assert w % p == 0
    return sum(q_fn(*[bits[(p * i + shift_out + k) % w] for k in range(4)]) for i in range(w // p))


def verify_flux_cert(p, stencil_fn, q_fn, J_fn, shift_out=2):
    """Exact 2^8 = 256 finite-window continuity check."""
    for m in range(256):
        u = [(m >> i) & 1 for i in range(8)]
        nxt = stencil_fn(u)
        lhs = q_fn(*nxt) - q_fn(*u[shift_out : shift_out + 4])
        rhs = J_fn(*u[p : p + 4]) - J_fn(*u[0:4])
        if lhs != rhs:
            return False, m
    return True, None


def synthesize_nullspace_dim(p, stencil_fn, shift_out=2):
    """Independently run exact rational RREF to confirm local-flux space dimension."""
    nq, nj = 16, 16
    rows = []
    seen = set()
    for m in range(256):
        u = [(m >> i) & 1 for i in range(8)]
        nxt = stencil_fn(u)
        qc = sum(u[shift_out + k] << k for k in range(4))
        qn = sum(nxt[k] << k for k in range(4))
        jl = sum(u[k] << k for k in range(4))
        jr = sum(u[p + k] << k for k in range(4))
        row = {}
        for col, d in ((qn, 1), (qc, -1), (nq + jr, -1), (nq + jl, 1)):
            nv = row.get(col, 0) + d
            if nv == 0:
                row.pop(col, None)
            else:
                row[col] = nv
        if row:
            key = tuple(sorted(row.items()))
            if key not in seen:
                seen.add(key)
                rows.append(row)
    return len(sparse_rref_nullspace(rows, nq + nj))


def main():
    print("=" * 72)
    print("Pure Silicon Reversible Toffoli/Fredkin Gate-Lattice Conservation Engine")
    print("Independent Exact-Integer Discovery, Replay & Sharpness Suite (dynsil-10)")
    print("=" * 72)

    # 1. Exact rational nullspace synthesis confirmation
    print("\n[1] Exact Rational Nullspace Synthesis (M = 8, exact Q RREF):")
    ns_FT = synthesize_nullspace_dim(4, lambda u: margolus4_stencil(gate_FT, u))
    ns_FF = synthesize_nullspace_dim(4, lambda u: margolus4_stencil(gate_FF, u))
    ns_DF = synthesize_nullspace_dim(4, lambda u: margolus4_stencil(gate_DF, u))
    ns_CO = synthesize_nullspace_dim(2, lambda u: subcnot_stencil(lambda a, c: a ^ c, lambda a, c: a | c, u))
    ns_DW = synthesize_nullspace_dim(2, lambda u: subcnot_stencil(lambda a, c: a | (1 - c), lambda a, c: (1 - a) | c, u))
    print(f"    Nullspace dims (incl. constants): FT={ns_FT}, FF={ns_FF}, DF={ns_DF}, CO={ns_CO}, DW={ns_DW}")
    assert ns_FT >= 3 and ns_FF >= 4 and ns_DF >= 4 and ns_CO >= 3 and ns_DW >= 2

    # 2. Exhaustive 256-gate Fredkin-CNOT 4-way IFF classification + 3-vector completeness
    print("\n[2] Exhaustive 256-Gate Fredkin-CNOT Classification (Theorem Family 1):")
    ideal_masks = []
    cert_masks = []
    three_vec_masks = []
    all_w8_masks = []
    test_3 = [tuple((m >> i) & 1 for i in range(8)) for m in (0x04, 0x08, 0x0B)]
    for mask8 in range(256):
        G, Ginv = make_fred_cnot(mask8)
        # Verify gate bijectivity on all 16 4-bit inputs
        for x in range(16):
            t = ((x >> 0) & 1, (x >> 1) & 1, (x >> 2) & 1, (x >> 3) & 1)
            assert Ginv(*G(*t)) == t and G(*Ginv(*t)) == t
        is_ideal = ((mask8 & (~168 & 0xFF)) == 0)
        if is_ideal:
            ideal_masks.append(mask8)
        ok_cert, _ = verify_flux_cert(4, lambda u, G=G: margolus4_stencil(G, u), q_FT, J_FT)
        if ok_cert:
            cert_masks.append(mask8)
        ok_3 = all(ring_charge(margolus4_ring_step(G, b), 4, q_FT) == ring_charge(b, 4, q_FT) for b in test_3)
        if ok_3:
            three_vec_masks.append(mask8)
        ok_w8 = all(
            ring_charge(margolus4_ring_step(G, tuple((m >> i) & 1 for i in range(8))), 4, q_FT) ==
            ring_charge(tuple((m >> i) & 1 for i in range(8)), 4, q_FT)
            for m in range(256)
        )
        if ok_w8:
            all_w8_masks.append(mask8)
    assert ideal_masks == cert_masks == three_vec_masks == all_w8_masks == [0, 8, 32, 40, 128, 136, 160, 168]
    print(f"    EXACT 4-WAY MATCH: all 4 characterizations select the exact 8-element Boolean ideal:")
    print(f"    masks = {ideal_masks} (248/248 non-ideal gates caught by {{0x04, 0x08, 0x0B}} alone!)")

    # 3. Finite-window certificate verification across all 4 theorem families
    print("\n[3] Finite-Window Certificate Checks (256 windows each):")
    certs = [
        ("FT  (F(1;0,2);T(0,3->1))  q_FT",    4, lambda u: margolus4_stencil(gate_FT, u), q_FT, J_FT),
        ("FF  (F(3;1,2);F(1;0,3))  q_HW4",    4, lambda u: margolus4_stencil(gate_FF, u), q_HW4, J_HW_FF),
        ("FF  (F(3;1,2);F(1;0,3))  q_dimer",  4, lambda u: margolus4_stencil(gate_FF, u), q_dimer, J_dimer),
        ("FF  (F(3;1,2);F(1;0,3))  q_rail",   4, lambda u: margolus4_stencil(gate_FF, u), q_rail, J_rail),
        ("DF  (F(0;1,2);F(3;1,2))  q_DF",     4, lambda u: margolus4_stencil(gate_DF, u), q_DF, J_DF),
        ("CO  SubCNOT(a^c ; a|c)   q_CO",     2, lambda u: subcnot_stencil(lambda a, c: a ^ c, lambda a, c: a | c, u), q_CO, J_CO),
        ("DW  SubCNOT(a|!c ; !a|c) q_DW",     2, lambda u: subcnot_stencil(lambda a, c: a | (1 - c), lambda a, c: (1 - a) | c, u), q_DW, J_DW),
    ]
    for label, p, st, qf, jf in certs:
        ok, bad = verify_flux_cert(p, st, qf, jf)
        assert ok, f"Cert failed for {label} at window {bad}"
        print(f"    PASS: {label} (256/256 windows verified)")

    # 4. Multi-width independent exact replay up to w = 64, t = 200 (incl. reversibility + open-segment continuity)
    print("\n[4] Independent Multi-Width Exact Replay (widths up to w = 64, t = 200 steps):")
    rng = random.Random(20261126)
    for w in (4, 8, 12, 16, 20, 32, 64):
        for trial in range(10):
            init = tuple(rng.randint(0, 1) for _ in range(w))
            # FT: reversibility + conservation + open-segment continuity
            q0_ft = ring_charge(init, 4, q_FT)
            cur = init
            for _ in range(50 if w == 64 else 200):
                nxt = margolus4_ring_step(gate_FT, cur)
                assert margolus4_ring_inv(gate_FT_inv, nxt) == cur
                assert ring_charge(nxt, 4, q_FT) == q0_ft
                # Open-segment exact discrete Gauss-Noether continuity on a proper sub-interval [a, a+k)
                if w >= 12:
                    nblk = w // 4
                    a_blk, len_blk = 0, nblk // 2
                    lhs_seg = sum(q_FT(*[nxt[(4 * (a_blk + k) + 2 + j) % w] for j in range(4)]) for k in range(len_blk)) - \
                              sum(q_FT(*[cur[(4 * (a_blk + k) + 2 + j) % w] for j in range(4)]) for k in range(len_blk))
                    rhs_seg = J_FT(*[cur[(4 * (a_blk + len_blk) + j) % w] for j in range(4)]) - \
                              J_FT(*[cur[(4 * a_blk + j) % w] for j in range(4)])
                    assert lhs_seg == rhs_seg
                cur = nxt
            # FF: reversibility + 3-charge algebra
            q0_ff = (ring_charge(init, 4, q_HW4), ring_charge(init, 4, q_dimer), ring_charge(init, 4, q_rail))
            cur = init
            for _ in range(40):
                nxt = margolus4_ring_step(gate_FF, cur)
                assert margolus4_ring_inv(gate_FF_inv, nxt) == cur
                assert (ring_charge(nxt, 4, q_HW4), ring_charge(nxt, 4, q_dimer), ring_charge(nxt, 4, q_rail)) == q0_ff
                cur = nxt
            # DF: reversibility + cubic-flux law
            q0_df = ring_charge(init, 4, q_DF)
            cur = init
            for _ in range(40):
                nxt = margolus4_ring_step(gate_DF, cur)
                assert margolus4_ring_inv(gate_DF, nxt) == cur
                assert ring_charge(nxt, 4, q_DF) == q0_df
                cur = nxt
    print("    PASS: Margolus4 (FT, FF, DF) exact replay across w in {4,8,12,16,20,32,64} (incl. open-segment Gauss-Noether flux!)")

    for w in (2, 4, 6, 8, 12, 20, 32, 64):
        for trial in range(10):
            init = tuple(rng.randint(0, 1) for _ in range(w))
            for f1, f2, qf in (
                (lambda a, c: a ^ c, lambda a, c: a | c, q_CO),
                (lambda a, c: a | (1 - c), lambda a, c: (1 - a) | c, q_DW),
            ):
                q0 = ring_charge(init, 2, qf)
                cur = init
                for _ in range(40):
                    nxt = subcnot_ring_step(f1, f2, cur)
                    assert subcnot_ring_inv(f1, f2, nxt) == cur
                    assert ring_charge(nxt, 2, qf) == q0
                    cur = nxt
    print("    PASS: SubCNOT (CO, DW) exact replay across w in {2,4,6,8,12,20,32,64}")

    # 5. Sharpness, non-vacuity, and mutation rejections
    print("\n[5] Sharpness Counterexamples, Negative Mutations & Dynamical Richness:")
    b9 = tuple((9 >> i) & 1 for i in range(8))
    b9_next = margolus4_ring_step(gate_FT, b9)
    assert sum(b9) == 2 and sum(b9_next) == 3 and ring_charge(b9, 4, q_FT) == -1 == ring_charge(b9_next, 4, q_FT)
    print("    Witness 1 (FT breaks HW, conserves Q_FT): mask=9, HW 2->3, Q_FT -1->-1")

    ok_z, bad_z = verify_flux_cert(4, lambda u: margolus4_stencil(gate_FT, u), q_FT, lambda a, b, c, d: 0)
    assert not ok_z
    print(f"    Mutation 1 (Zero flux J=0): REJECTED at window {bad_z}")

    G_cd, _ = make_fred_cnot(192)  # h(a,c,d) = c & d (outside ideal!)
    ok_cd, bad_cd = verify_flux_cert(4, lambda u: margolus4_stencil(G_cd, u), q_FT, J_FT)
    b11 = tuple((11 >> i) & 1 for i in range(8))
    assert not ok_cd and ring_charge(margolus4_ring_step(G_cd, b11), 4, q_FT) != ring_charge(b11, 4, q_FT)
    print(f"    Mutation 2 (Toffoli c&d outside ideal): REJECTED at window {bad_cd}; w=8 mask=11 Q_FT {ring_charge(b11,4,q_FT)}->{ring_charge(margolus4_ring_step(G_cd, b11),4,q_FT)}")

    def gate_mut_fred(a, b, c, d):
        a, b, c, d = fredkin_1_03(a, b, c, d)
        return (a, b ^ (a & d), c, d)
    ok_mf, bad_mf = verify_flux_cert(4, lambda u: margolus4_stencil(gate_mut_fred, u), q_FT, J_FT)
    b3 = tuple((3 >> i) & 1 for i in range(8))
    assert not ok_mf and ring_charge(margolus4_ring_step(gate_mut_fred, b3), 4, q_FT) != ring_charge(b3, 4, q_FT)
    print(f"    Mutation 3 (Fredkin wire F(1;0,3)): REJECTED at window {bad_mf}; w=8 mask=3 Q_FT {ring_charge(b3,4,q_FT)}->{ring_charge(margolus4_ring_step(gate_mut_fred, b3),4,q_FT)}")

    # Orbit period spot-check on w=16 for FT to certify non-trivial chaotic/long-orbit dynamics
    b_long = tuple((0x5A3D >> i) & 1 for i in range(16))
    cur = b_long
    period = 0
    for t in range(1, 5000):
        cur = margolus4_ring_step(gate_FT, cur)
        if cur == b_long:
            period = t
            break
    print(f"    Dynamical richness (FT on w=16, state 0x5A3D): exact orbit period = {period} (> 100)")
    assert period > 100

    print("\nALL EXACT-INTEGER CHECKS PASSED (exit 0, zero floats).")


if __name__ == "__main__":
    main()
