#!/usr/bin/env python3
"""
Exact Pure-Silicon Verification & Falsification Suite for:
  The 2-Group Ryser Bitmask Orbit-Collapse & Mod-2^(k+2) Involution-Defect Engine

Zero floating-point arithmetic anywhere; all computations use exact Python `int`.
"""

import itertools
import random


def perm_naive(A):
    """Exact permanent by summing over all n! permutations."""
    n = len(A)
    total = 0
    for p in itertools.permutations(range(n)):
        prod = 1
        for i in range(n):
            prod *= A[i][p[i]]
        total += prod
    return total


def perm_ryser(A):
    """Exact permanent via Gray-code Ryser bitmask formula."""
    n = len(A)
    if n == 0:
        return 1
    row_sums = [0] * n
    total = 0
    prev_gray = 0
    for step in range(1, 1 << n):
        gray = step ^ (step >> 1)
        diff = gray ^ prev_gray
        j = (diff & -diff).bit_length() - 1
        if gray & diff:
            for i in range(n):
                row_sums[i] += A[i][j]
        else:
            for i in range(n):
                row_sums[i] -= A[i][j]
        prod = 1
        for x in row_sums:
            prod *= x
        if (n - gray.bit_count()) & 1:
            total -= prod
        else:
            total += prod
        prev_gray = gray
    return total


def count_odd_sols_gf2(A):
    """Exact count N_odd(A) = #{S subset Fin n : A * 1_S == 1 (mod 2)} via GF(2) elimination."""
    n = len(A)
    M = [[(A[i][j] & 1) for j in range(n)] + [1] for i in range(n)]
    row = 0
    for col in range(n):
        piv = None
        for r in range(row, n):
            if M[r][col] == 1:
                piv = r
                break
        if piv is None:
            continue
        M[row], M[piv] = M[piv], M[row]
        for r in range(n):
            if r != row and M[r][col] == 1:
                for c in range(col, n + 1):
                    M[r][c] ^= M[row][c]
        row += 1
    for r in range(row, n):
        if M[r][n] == 1:
            return 0
    return 1 << (n - row)


def gf2_inv_col0(A):
    """Exact solution T_0 in GF(2)^n to A * T_0 == e_0 (mod 2)."""
    n = len(A)
    M = [[(A[i][j] & 1) for j in range(n)] + [1 if i == 0 else 0] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] == 1)
        M[col], M[piv] = M[piv], M[col]
        for r in range(n):
            if r != col and M[r][col] == 1:
                for c in range(col, n + 1):
                    M[r][c] ^= M[col][c]
    return [M[i][n] for i in range(n)]


def v2(x):
    if x == 0:
        return None
    return (x & -x).bit_length() - 1


def xor_circ_matrix(vals):
    n = len(vals)
    return [[vals[i ^ j] for j in range(n)] for i in range(n)]


def cyc_circ_matrix(vals):
    n = len(vals)
    return [[vals[(i - j) % n] for j in range(n)] for i in range(n)]


def anti_circ_matrix(vals):
    n = len(vals)
    return [[vals[(i + j) % n] for j in range(n)] for i in range(n)]


def predict_xor_mod_2kp2(vals):
    """Exact closed-form prediction for XOR-circulant 2^k x 2^k with odd row sum mod 2^(k+2)."""
    n = len(vals)
    k = n.bit_length() - 1
    n_odd = sum(1 for v in vals if (v & 1) == 1)
    s_even = sum(v for v in vals if (v & 1) == 0)
    assert n_odd % 2 == 1, "Row sum must be odd"
    return (1 + (1 << k) * ((n_odd - 1) + s_even)) % (1 << (k + 2))


def q8_table():
    def mul(a, b):
        s = (a & 1) ^ (b & 1)
        x, y = a >> 1, b >> 1
        if x == 0:
            return (y << 1) | s
        if y == 0:
            return (x << 1) | s
        if x == y:
            return s ^ 1
        cyc = {
            (1, 2): (3, 0), (2, 3): (1, 0), (3, 1): (2, 0),
            (2, 1): (3, 1), (3, 2): (1, 1), (1, 3): (2, 1),
        }
        z, s2 = cyc[(x, y)]
        return (z << 1) | (s ^ s2)
    inv = [next(b for b in range(8) if mul(a, b) == 0) for a in range(8)]
    return mul, inv


def d4_table():
    def mul(a, b):
        r1, f1 = a >> 1, a & 1
        r2, f2 = b >> 1, b & 1
        r = (r1 + (r2 if f1 == 0 else -r2)) % 4
        return (r << 1) | (f1 ^ f2)
    inv = [next(b for b in range(8) if mul(a, b) == 0) for a in range(8)]
    return mul, inv


def main():
    print("=" * 72)
    print("1. CROSS-CHECK RYSER VS NAIVE PERMUTATION SUM (n = 1..5)")
    print("=" * 72)
    rng = random.Random(20261127)
    for n in range(1, 6):
        for _ in range(10):
            A = [[rng.randint(-4, 4) for _ in range(n)] for _ in range(n)]
            assert perm_naive(A) == perm_ryser(A)
    print("  PASS: perm_ryser == perm_naive on 50 random integer matrices (n=1..5).")

    print("\n" + "=" * 72)
    print("2. EXHAUSTIVE BINARY VERIFICATION (k = 1, 2, 3 -> 2 + 16 + 256 matrices each)")
    print("=" * 72)
    for k in [1, 2, 3]:
        n = 1 << k
        mod1 = 1 << (k + 1)
        mod2 = 1 << (k + 2)
        cnt_xor = cnt_cyc = cnt_anti = 0
        cnt_xor_odd = cnt_xor_even = 0
        for bits in range(1 << n):
            vals = [(bits >> z) & 1 for z in range(n)]
            # XOR-circulant
            Ax = xor_circ_matrix(vals)
            px = perm_ryser(Ax)
            cx = count_odd_sols_gf2(Ax)
            assert (px - cx) % mod1 == 0
            cnt_xor += 1
            if sum(vals) % 2 == 1:
                assert px % mod2 == predict_xor_mod_2kp2(vals)
                cnt_xor_odd += 1
            else:
                if k >= 3:
                    assert px % mod1 == 0
                cnt_xor_even += 1
            # Cyclic circulant
            Ac = cyc_circ_matrix(vals)
            pc = perm_ryser(Ac)
            cc = count_odd_sols_gf2(Ac)
            assert (pc - cc) % mod1 == 0
            cnt_cyc += 1
            # Anti-circulant f((i + j) mod 2^k)
            Aa = anti_circ_matrix(vals)
            pa = perm_ryser(Aa)
            ca = count_odd_sols_gf2(Aa)
            assert (pa - ca) % mod1 == 0
            cnt_anti += 1
        print(
            f"  k={k} (n={n}): XOR={cnt_xor}/{1<<n} (odd mod {mod2}: {cnt_xor_odd}, "
            f"even: {cnt_xor_even}), CYC={cnt_cyc}/{1<<n}, ANTI={cnt_anti}/{1<<n} -> ALL EXACT!"
        )

    print("\n" + "=" * 72)
    print("3. INTEGER MATRICES: XOR, CYCLIC, ANTI-CIRCULANT, BLOCK-XOR, NON-ABELIAN Q8 & D4")
    print("=" * 72)
    # Integer XOR-circulant k=1..4
    for k in [1, 2, 3, 4]:
        n = 1 << k
        trials = 40 if k <= 3 else 10
        for t in range(trials):
            vals = [rng.randint(-7, 7) for _ in range(n)]
            Ax = xor_circ_matrix(vals)
            px = perm_ryser(Ax)
            cx = count_odd_sols_gf2(Ax)
            assert (px - cx) % (1 << (k + 1)) == 0
            if sum(vals) % 2 == 1:
                assert px % (1 << (k + 2)) == predict_xor_mod_2kp2(vals)
            elif k >= 3:
                assert px % (1 << (k + 1)) == 0
        print(f"  Integer XOR-circulant k={k} (n={n}): {trials}/{trials} PASS mod 2^{k+1} & mod 2^{k+2}!")

    # Block XOR-circulant m=3, k=2 (n=12, mod 8)
    for _ in range(12):
        blocks = [[[rng.randint(-3, 3) for _ in range(3)] for _ in range(3)] for _ in range(4)]
        A = [[blocks[(i // 3) ^ (j // 3)][i % 3][j % 3] for j in range(12)] for i in range(12)]
        assert (perm_ryser(A) - count_odd_sols_gf2(A)) % 8 == 0
    print("  Block XOR-circulant m=3, k=2 (12x12, mod 8): 12/12 PASS!")

    # Non-abelian Quaternion Q_8 (8x8, mod 16 & mod 32)
    qmul, qinv = q8_table()
    for _ in range(30):
        vals = [rng.randint(-5, 5) for _ in range(8)]
        A = [[vals[qmul(qinv[g], h)] for h in range(8)] for g in range(8)]
        p = perm_ryser(A)
        c = count_odd_sols_gf2(A)
        assert (p - c) % 16 == 0
        if sum(vals) % 2 == 1:
            T0 = gf2_inv_col0(A)
            r0_S0 = sum(A[0][j] for j in range(8) if T0[j] == 0)
            r0_Sh = sum(A[0][j] for j in range(8) if (T0[j] ^ T0[qmul(1, j)]) == 0)
            bit = (1 if r0_S0 % 4 == 2 else 0) ^ (1 if r0_Sh % 4 == 2 else 0)
            assert p % 32 == (1 + (bit << 4)) % 32
    print("  Non-abelian Quaternion Q_8 (8x8): 30/30 PASS mod 16 & 2-term mod 32 formula!")

    # Non-abelian Dihedral D_4 (8x8, mod 16)
    dmul, dinv = d4_table()
    for _ in range(30):
        vals = [rng.randint(-5, 5) for _ in range(8)]
        A = [[vals[dmul(dinv[g], h)] for h in range(8)] for g in range(8)]
        assert (perm_ryser(A) - count_odd_sols_gf2(A)) % 16 == 0
    print("  Non-abelian Dihedral D_4 (8x8): 30/30 PASS mod 16!")

    print("\n" + "=" * 72)
    print("4. STRUCTURED INFINITE FAMILIES: HYPERCUBES Q_k, MATCHINGS B_k, POPCOUNT P_k + I")
    print("=" * 72)
    for k in range(1, 5):
        n = 1 << k
        vals = [1 if z.bit_count() == 1 else 0 for z in range(n)]
        A = xor_circ_matrix(vals)
        p = perm_ryser(A)
        if k % 2 == 1:
            pred = (1 + (1 << k) * (k - 1)) % (1 << (k + 2))
            assert p % (1 << (k + 2)) == pred
            print(f"  Q_{k} (n={n}, odd k): perm = {p}, mod 2^{k+2}={1<<(k+2)} -> {p % (1<<(k+2))} (predicted {pred})")
        else:
            if k >= 4:
                assert p % (1 << (2 * k)) == 0
            print(f"  Q_{k} (n={n}, even k): perm = {p}, v2(perm) = {v2(p)}")

    for k in range(1, 6):
        m = k - 1
        n = 1 << m
        supp = {0} | {1 << b for b in range(m)}
        vals = [1 if z in supp else 0 for z in range(n)]
        B = xor_circ_matrix(vals)
        M = perm_ryser(B)
        if k % 2 == 1 and k >= 3:
            pred = (1 + (1 << (k - 1)) * (k - 1)) % (1 << (k + 1))
            assert M % (1 << (k + 1)) == pred
            print(f"  B_{k} (n={n}, odd k): M_{k} = {M}, mod 2^{k+1}={1<<(k+1)} -> {M % (1<<(k+1))} (predicted {pred})")
        elif k % 2 == 0 and k >= 4:
            assert M % (1 << k) == 0
            print(f"  B_{k} (n={n}, even k): M_{k} = {M}, v2(M_{k}) = {v2(M)} >= {k}")
        else:
            print(f"  B_{k} (n={n}): M_{k} = {M}")

    for k in range(2, 5):
        n = 1 << k
        vals = [z.bit_count() + (1 if z == 0 else 0) for z in range(n)]
        A = xor_circ_matrix(vals)
        p = perm_ryser(A)
        pred = predict_xor_mod_2kp2(vals)
        assert p % (1 << (k + 2)) == pred
        print(f"  P_{k}+I (n={n}): perm = {p}, mod 2^{k+2}={1<<(k+2)} -> {p % (1<<(k+2))} (predicted {pred})")

    print("\n" + "=" * 72)
    print("5. SHARPNESS & BOUNDARY COUNTEREXAMPLES")
    print("=" * 72)
    # S1: Modulus 2^(k+1) is sharp for general odd-det 2-group matrices (D_4 = J_4 - I_4, k=2)
    D4 = xor_circ_matrix([0, 1, 1, 1])
    p_d4 = perm_ryser(D4)
    assert p_d4 == 9 and p_d4 % 8 == 1 and p_d4 % 16 == 9
    print(f"  [S1] Mod 2^(k+1) sharpness (k=2, D_4 = J_4-I_4): perm={p_d4}, = 1 mod 8, = 9 != 1 mod 16.")

    # S2: Modulus 2^(k+2) is sharp for integer entry-histogram formula (k=2)
    p_a = perm_ryser(xor_circ_matrix([1, 0, 0, 0]))
    p_b = perm_ryser(xor_circ_matrix([3, 0, 0, 0]))
    assert p_a == 1 and p_b == 81 and p_a % 16 == p_b % 16 == 1 and p_a % 32 != p_b % 32
    print(f"  [S2] Mod 2^(k+2) integer sharpness (k=2): [1,0,0,0] -> perm={p_a} (1 mod 32) vs [3,0,0,0] -> perm={p_b} (17 mod 32).")

    # S3: Modulus 2^(k+2) is sharp EVEN FOR BINARY {0,1} XOR-circulant matrices (k=4, weight 5)
    vals_noflat = [1 if z in {0, 1, 2, 4, 8} else 0 for z in range(16)]
    vals_flat = [1 if z in {0, 1, 2, 3, 4} else 0 for z in range(16)]
    p_nf = perm_ryser(xor_circ_matrix(vals_noflat))
    p_fl = perm_ryser(xor_circ_matrix(vals_flat))
    assert p_nf == 589185 and p_fl == 1723969
    assert p_nf % 64 == 1 and p_fl % 64 == 1 and p_nf % 128 == 1 and p_fl % 128 == 65
    print(f"  [S3] Mod 2^(k+2) BINARY sharpness (k=4, d=5): no-flat -> {p_nf} (1 mod 128) vs 2-flat -> {p_fl} (65 mod 128).")

    # S4: Even-row-sum threshold k >= 3 is sharp (k=2, Q_2)
    p_q2 = perm_ryser(xor_circ_matrix([0, 1, 1, 0]))
    assert p_q2 == 4 and p_q2 % 8 == 4
    print(f"  [S4] Even-row-sum k >= 3 sharpness (k=2, Q_2): perm={p_q2}, 8 does not divide 4.")

    # S5: Equivariance is sharp (single-entry +2 perturbation on D_4 leaves A mod 2 unchanged)
    D4_pert = [row[:] for row in D4]
    D4_pert[0][0] = 2
    p_pert = perm_ryser(D4_pert)
    assert p_pert == 13 and p_pert % 8 == 5
    print(f"  [S5] Single-entry +2 perturbation on D_4: perm={p_pert} (= 5 != 1 mod 8).")

    # S6: 2-group order is sharp (odd-order Z/3Z cyclic circulant [3, 2, 0], odd det)
    p_z3 = perm_ryser(cyc_circ_matrix([3, 2, 0]))
    assert p_z3 == 35 and p_z3 % 4 == 3
    print(f"  [S6] Odd-order Z/3Z circulant [3,2,0]: perm={p_z3} (= 3 != 1 mod 4).")

    # S7: Freeness of 2-group action is sharp (Q_3 has non-free Sylow-2 of order 16, yet perm = 81 != 1 mod 32)
    p_q3 = perm_ryser(xor_circ_matrix([1 if z.bit_count() == 1 else 0 for z in range(8)]))
    assert p_q3 == 81 and p_q3 % 16 == 1 and p_q3 % 32 == 17
    print(f"  [S7] Freeness sharpness (Q_3, non-free |Syl_2|=16): perm={p_q3} (= 17 != 1 mod 32).")

    print("\nALL VERIFICATIONS AND SHARPNESS COUNTEREXAMPLES PASSED!")


if __name__ == "__main__":
    main()
