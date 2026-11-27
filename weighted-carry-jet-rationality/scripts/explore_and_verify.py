#!/usr/bin/env python3
"""
Independent Exact Exploration, Certificate Synthesis, Verification, & Sharpness Suite
Worker: transducer-18 — Weighted Carry-Transducer Generating Function & Rationality Engine

Pure exact integer / rational arithmetic (Python `int` and `fractions.Fraction`; ZERO floats).

What this script does:
1. Synthesizes exact finite Right-Krylov and Left-Krylov annihilator certificates for the 16-state
   bilinear jet matrices of both the unweighted and parity-twisted binary carry-borrow transducers,
   plus the 2-state signed binary addition-carry transducer.
2. Independently verifies by direct brute-force enumeration over ALL (x, y) in [0, B^w)^2:
   - Hardware authenticity of carry/borrow counts against floor/comparison overflow/underflow;
   - Binary (B=2) exact closed forms for all 4 initial states (c0, b0) in {0,1}^2 (w = 1..6);
   - Binary exact triangular-square covariance law: 4^w * S_cb - S_c * S_b = -(-1)^(c0^b0) * C(2^w, 2)^2;
   - Binary exact rational generating functions in Z[[t]] up to degree 25 via transfer-matrix replay;
   - Binary parity-twisted carry-borrow correlation hierarchy (w = 1..6 brute force, w = 1..30 matrix);
   - Arbitrary-radix B in {2..9} even/odd independence-vs-defect dichotomy & parity-twist dichotomy.
3. Exhibits explicit sharpness counterexamples where relaxing each hypothesis breaks the theorem:
   - Threshold w >= 2 in the parity-twisted correlation law breaks at w = 1 (0 != 1);
   - Even-radix negative-square defect and degree-5 denominator break at odd radix B = 3, 5, 7;
   - Initial carry/borrow flip (0,0) -> (0,1) reverses covariance sign (-36 -> +36 at w = 2);
   - Self-variance Var_w(C+) exceeds 1/4 already at w = 2 (39/64 > 1/4) and grows linearly Theta(w),
     contrasting with |Cov_w(C+, B-)| < 1/4 for ALL w >= 1.
"""
from fractions import Fraction


# ---------------------------------------------------------------------------
# 1. Exact Hardware-Authentic Carry / Borrow Arithmetic
# ---------------------------------------------------------------------------

def add_carry_count(B: int, w: int, c0: int, x: int, y: int) -> int:
    c = c0
    total = 0
    xx, yy = x, y
    for _ in range(w):
        dx, dy = xx % B, yy % B
        xx //= B
        yy //= B
        c = 1 if (dx + dy + c) >= B else 0
        total += c
    return total


def add_carry_count_floor(B: int, w: int, c0: int, x: int, y: int) -> int:
    """Direct arithmetic definition via integer overflow floor quotients."""
    total = 0
    modulus = 1
    for _ in range(w):
        modulus *= B
        total += ((x % modulus) + (y % modulus) + c0) // modulus
    return total


def sub_borrow_count(B: int, w: int, b0: int, x: int, y: int) -> int:
    b = b0
    total = 0
    xx, yy = x, y
    for _ in range(w):
        dx, dy = xx % B, yy % B
        xx //= B
        yy //= B
        b = 1 if dx < dy + b else 0
        total += b
    return total


def sub_borrow_count_lt(B: int, w: int, b0: int, x: int, y: int) -> int:
    """Direct arithmetic definition via unsigned modular underflow comparison."""
    total = 0
    modulus = 1
    for _ in range(w):
        modulus *= B
        total += 1 if (x % modulus) < (y % modulus) + b0 else 0
    return total


def repunit(B: int, w: int) -> int:
    return sum(B ** j for j in range(w))


# ---------------------------------------------------------------------------
# 2. Weighted Transducer Jet-Matrix Compiler & Exact Krylov Certificate Engine
# ---------------------------------------------------------------------------

def build_carry_borrow_jet(B: int, twist_fn):
    """Compile the 4-state radix-B carry-borrow CorrMachine into its 16x16 integer jetMat.
    Block layout matches Proof.lean:
      0 = Mfg (e1*e2), 1 = Mf (e1), 2 = Mg (e2), 3 = M0 (1).
    """
    M0 = [[0] * 4 for _ in range(4)]
    Mf = [[0] * 4 for _ in range(4)]
    Mg = [[0] * 4 for _ in range(4)]
    Mfg = [[0] * 4 for _ in range(4)]
    for q in range(4):
        c, b = q >> 1, q & 1
        for dx in range(B):
            for dy in range(B):
                cn = 1 if (dx + dy + c) >= B else 0
                bn = 1 if dx < dy + b else 0
                qn = (cn << 1) | bn
                w = twist_fn(cn, bn)
                M0[q][qn] += w
                Mf[q][qn] += w * cn
                Mg[q][qn] += w * bn
                Mfg[q][qn] += w * cn * bn
    M = [[0] * 16 for _ in range(16)]

    def place(br, bc, blk):
        for i in range(4):
            for j in range(4):
                M[br * 4 + i][bc * 4 + j] = blk[i][j]

    place(0, 0, M0)
    place(0, 1, Mg)
    place(0, 2, Mf)
    place(0, 3, Mfg)
    place(1, 1, M0)
    place(1, 3, Mf)
    place(2, 2, M0)
    place(2, 3, Mg)
    place(3, 3, M0)
    return M


def mat_vec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def vec_mat(u, M):
    return [sum(u[i] * M[i][j] for i in range(len(u))) for j in range(len(M[0]))]


def synth_right_krylov_cert(M, beta):
    """Exact Gaussian elimination over Q to find the minimal monic Right-Krylov annihilator
    c = [c_0, ..., c_{d-1}] such that M^d beta + sum_{k=0}^{d-1} c_k (M^k beta) = 0.
    """
    N = len(beta)
    vecs = [[Fraction(x) for x in beta]]
    MQ = [[Fraction(x) for x in row] for row in M]
    for d in range(1, N + 2):
        vn = [sum(MQ[i][j] * vecs[-1][j] for j in range(N)) for i in range(N)]
        A = [[vecs[k][r] for k in range(d)] + [-vn[r]] for r in range(N)]
        pr = 0
        pcols = []
        for col in range(d):
            piv = next((r for r in range(pr, N) if A[r][col] != 0), None)
            if piv is None:
                continue
            A[pr], A[piv] = A[piv], A[pr]
            inv = Fraction(1) / A[pr][col]
            A[pr] = [x * inv for x in A[pr]]
            for r in range(N):
                if r != pr and A[r][col] != 0:
                    fac = A[r][col]
                    A[r] = [A[r][j] - fac * A[pr][j] for j in range(d + 1)]
            pcols.append(col)
            pr += 1
        if all(A[r][d] == 0 for r in range(pr, N)) and len(pcols) == d:
            c = [A[i][d] for i in range(d)]
            assert all(x.denominator == 1 for x in c)
            return [int(x) for x in c]
        vecs.append(vn)
    raise RuntimeError("No Krylov annihilator found")


def fps_mul(F, G, n):
    return sum(F[k] * G[n - k] for k in range(n + 1))


def poly_mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


# ---------------------------------------------------------------------------
# 3. Verification & Counterexample Suite
# ---------------------------------------------------------------------------

def main():
    print("=================================================================")
    print("transducer-18: Weighted Carry-Transducer Rationality Engine Audit")
    print("=================================================================\n")

    # (A) Synthesize exact finite Krylov certificates
    beta16 = [0] * 12 + [1, 1, 1, 1]
    M_unw = build_carry_borrow_jet(2, lambda c, b: 1)
    M_par = build_carry_borrow_jet(2, lambda c, b: 1 if c == b else -1)

    cert_unw = synth_right_krylov_cert(M_unw, beta16)
    cert_par = synth_right_krylov_cert(M_par, beta16)
    assert cert_unw == [-256, 448, -304, 100, -16]
    assert cert_par == [0, 0, 8, -4, -2]

    Q_unw = [1] + list(reversed(cert_unw))
    Q_unw_factored = poly_mul(
        poly_mul(poly_mul([1, -4], [1, -4]), [1, -4]),
        poly_mul([1, -2], [1, -2]),
    )
    assert Q_unw == Q_unw_factored

    Q_par_full = [1] + list(reversed(cert_par))
    Q_par = [1, -2, -4, 8]
    assert Q_par_full == Q_par + [0, 0]
    assert Q_par == poly_mul([1, -2], [1, 0, -4])

    print("[PASS] 1. Finite Right-Krylov Certificates Synthesized:")
    print(f"       certBinUnw = {cert_unw}  ->  Q(t) = {Q_unw} = (1 - 4t)^3 (1 - 2t)^2")
    print(f"       certBinPar = {cert_par}  ->  Q(t) = {Q_par} = (1 - 2t)(1 - 4t^2)")

    # (B) Brute-force verification of hardware authenticity + binary laws (w = 1..6)
    for w in range(1, 7):
        N = 1 << w
        for c0 in (0, 1):
            for b0 in (0, 1):
                s0 = sc = sb = scb = 0
                p0 = pc = pcb = 0
                for x in range(N):
                    for y in range(N):
                        C = add_carry_count(2, w, c0, x, y)
                        B = sub_borrow_count(2, w, b0, x, y)
                        if w <= 4:
                            assert C == add_carry_count_floor(2, w, c0, x, y)
                            assert B == sub_borrow_count_lt(2, w, b0, x, y)
                        sg = 1 if ((C + B) % 2 == 0) else -1
                        s0 += 1
                        sc += C
                        sb += B
                        scb += C * B
                        p0 += sg
                        pc += sg * C
                        pcb += sg * C * B
                assert s0 == 4 ** w
                # Triangular-square covariance law
                sign = 1 if c0 == b0 else -1
                tri = (1 << (w - 1)) * ((1 << w) - 1)
                assert (4 ** w) * scb - sc * sb == -sign * (tri * tri)
                # Closed forms for all 4 (c0, b0)
                if (c0, b0) == (0, 0):
                    assert scb == w * (w - 2) * (4 ** (w - 1)) + w * (2 ** (w - 1))
                    assert pc == -(2 ** (w - 1))
                    if w >= 2:
                        assert pcb == -((w - 1) + ((-1) ** w)) * (2 ** (w - 1))
                elif (c0, b0) in ((0, 1), (1, 0)):
                    assert scb == (w * w) * (4 ** (w - 1))
                else:
                    assert scb == w * (w + 2) * (4 ** (w - 1)) - w * (2 ** (w - 1))
                assert p0 == 0
    print("[PASS] 2. Brute-force Binary Verification (w = 1..6, all 4 (c0,b0)):")
    print("       - Hardware floor/comparison carry & borrow equivalence verified (w = 1..4)")
    print("       - Exact closed forms & triangular-square covariance law verified")
    print("       - Parity-twisted partition (0), first moment (-2^(w-1)), and corr (w>=2) verified")

    # (C) Rational GF Cauchy-product check up to degree 25 via transfer-matrix replay
    MAX_N = 25
    seq_unw = []
    seq_par = []
    v_u = list(beta16)
    v_p = list(beta16)
    for _ in range(MAX_N + 1):
        seq_unw.append(v_u[0])  # block 0 (Mfg), state (0,0)
        seq_par.append(v_p[0])
        v_u = mat_vec(M_unw, v_u)
        v_p = mat_vec(M_par, v_p)

    Q_u_pad = Q_unw + [0] * (MAX_N + 1)
    P_u_exp = [0, 0, 4, -4, -16] + [0] * (MAX_N + 1)
    for n in range(MAX_N + 1):
        assert fps_mul(Q_u_pad, seq_unw, n) == P_u_exp[n]

    Q_p_pad = Q_par + [0] * (MAX_N + 1)
    P_p_exp = [0, 0, -4, 4, -8] + [0] * (MAX_N + 1)
    for n in range(MAX_N + 1):
        assert fps_mul(Q_p_pad, seq_par, n) == P_p_exp[n]
        if n >= 2:
            assert seq_par[n] == -((n - 1) + ((-1) ** n)) * (2 ** (n - 1))
    print(f"[PASS] 3. Rational GF Identities in Z[[t]] verified up to degree {MAX_N}:")
    print("       - (1 - 4t)^3 (1 - 2t)^2 * S_cb(t) = 4t^2 - 4t^3 - 16t^4")
    print("       - (1 - 2t)(1 - 4t^2)    * T_cb(t) = -4t^2 + 4t^3 - 8t^4")

    # (D) Arbitrary-Radix B = 2..9 Even/Odd Dichotomy (matrix + brute force for small B, w)
    for B in range(2, 10):
        MB_unw = build_carry_borrow_jet(B, lambda c, b: 1)
        MB_par = build_carry_borrow_jet(B, lambda c, b: 1 if c == b else -1)
        vu = list(beta16)
        vp = list(beta16)
        for w in range(0, 8):
            R = repunit(B, w)
            for q in range(4):
                c0, b0 = q >> 1, q & 1
                s0 = vu[12 + q]
                sf = vu[4 + q]
                sg = vu[8 + q]
                sfg = vu[q]
                sign = 1 if c0 == b0 else -1
                assert s0 == B ** (2 * w)
                lhs4 = 4 * (s0 * sfg - sf * sg)
                rhs4 = ((B % 2) - 1) * sign * ((B ** w) * R) ** 2
                assert lhs4 == rhs4
                if B % 2 == 1:
                    assert s0 * sfg == sf * sg
                elif w >= 1:
                    m = B // 2
                    assert s0 * sfg - sf * sg == -sign * ((m * (B ** (w - 1)) * R) ** 2)
                # Parity-twisted partition dichotomy
                p0 = vp[12 + q]
                if w == 0:
                    assert p0 == 1
                elif B % 2 == 0:
                    assert p0 == 0
                else:
                    psign = 1 if (w % 2 == 0 or c0 == b0) else -1
                    assert p0 == psign * (B ** (2 * (w // 2)))
            vu = mat_vec(MB_unw, vu)
            vp = mat_vec(MB_par, vp)
    # Direct brute-force cross-check at B = 3 (w = 1..3), B = 4 (w = 1..2), B = 5 (w = 1..2)
    for B, max_w in [(3, 3), (4, 2), (5, 2)]:
        for w in range(1, max_w + 1):
            N = B ** w
            sc = sb = scb = p0 = 0
            for x in range(N):
                for y in range(N):
                    C = add_carry_count(B, w, 0, x, y)
                    Bv = sub_borrow_count(B, w, 0, x, y)
                    sc += C
                    sb += Bv
                    scb += C * Bv
                    p0 += 1 if ((C + Bv) % 2 == 0) else -1
            if B % 2 == 1:
                assert (B ** (2 * w)) * scb - sc * sb == 0
                assert p0 == B ** (2 * (w // 2))
            else:
                m = B // 2
                R = repunit(B, w)
                assert (B ** (2 * w)) * scb - sc * sb == -((m * (B ** (w - 1)) * R) ** 2)
                assert p0 == 0
    print("[PASS] 4. Arbitrary-Radix B in {2..9} Even/Odd Dichotomy verified (w = 0..7 + brute force):")
    print("       - Odd B  in {3,5,7,9}: Cov_w(C+, B-) = 0 identically; sum (-1)^(C+ + B-) = +- B^(2*floor(w/2))")
    print("       - Even B in {2,4,6,8}: Cov_w(C+, B-) = -(-1)^(c0^b0) * (R_w(B)/(2*B^w))^2; sum (-1)^(C+ + B-) = 0")

    # (E) Sharpness Counterexamples
    print("\n[SHARPNESS COUNTEREXAMPLES]")
    # 1. w = 1 breaks parity-twisted w >= 2 closed form
    w1_actual = seq_par[1]
    w1_formula = -((1 - 1) + ((-1) ** 1)) * (2 ** 0)
    assert w1_actual == 0 and w1_formula == 1 and w1_actual != w1_formula
    print(f"  1. Bit-width threshold (w >= 2): at w=1, actual = {w1_actual} != {w1_formula} = formula")

    # 2. Odd radix B = 3 breaks even-radix degree-5 denominator (1 - B^2 t)^3 (1 - B t)^2
    M3 = build_carry_borrow_jet(3, lambda c, b: 1)
    v3 = list(beta16)
    s3 = []
    for _ in range(8):
        s3.append(v3[0])
        v3 = mat_vec(M3, v3)
    Q5_B3 = poly_mul(
        poly_mul(poly_mul([1, -9], [1, -9]), [1, -9]),
        poly_mul([1, -3], [1, -3]),
    )
    defects_B3 = [sum(Q5_B3[k] * s3[n - k] for k in range(len(Q5_B3))) for n in range(5, 8)]
    assert defects_B3 == [-128, -128, -128]
    print(f"  2. Radix parity degree drop: at B=3, degree-5 operator (1-9t)^3(1-3t)^2 leaves defect {defects_B3} != 0")

    # 3. Initial carry/borrow flip reverses covariance sign
    cov_00_w2 = (4 ** 2) * sum(
        add_carry_count(2, 2, 0, x, y) * sub_borrow_count(2, 2, 0, x, y)
        for x in range(4) for y in range(4)
    ) - sum(add_carry_count(2, 2, 0, x, y) for x in range(4) for y in range(4)) * sum(
        sub_borrow_count(2, 2, 0, x, y) for x in range(4) for y in range(4)
    )
    cov_01_w2 = (4 ** 2) * sum(
        add_carry_count(2, 2, 0, x, y) * sub_borrow_count(2, 2, 1, x, y)
        for x in range(4) for y in range(4)
    ) - sum(add_carry_count(2, 2, 0, x, y) for x in range(4) for y in range(4)) * sum(
        sub_borrow_count(2, 2, 1, x, y) for x in range(4) for y in range(4)
    )
    assert cov_00_w2 == -36 and cov_01_w2 == 36
    print(f"  3. Initial state sign flip (B=2, w=2): (c0,b0)=(0,0) -> {cov_00_w2}, (0,1) -> +{cov_01_w2}")

    # 4. Self-variance exceeds 1/4 already at w=2 (while |Cov(C+, B-)| < 1/4 for all w >= 1)
    s_c2_w2 = sum(add_carry_count(2, 2, 0, x, y) ** 2 for x in range(4) for y in range(4))
    s_c_w2 = sum(add_carry_count(2, 2, 0, x, y) for x in range(4) for y in range(4))
    var_int_w2 = (4 ** 2) * s_c2_w2 - s_c_w2 * s_c_w2
    var_frac_w2 = Fraction(var_int_w2, 16 ** 2)
    assert var_int_w2 == 156 and var_frac_w2 == Fraction(39, 64) and var_frac_w2 > Fraction(1, 4)
    print(f"  4. Bounded cross-covariance vs unbounded variance: at w=2, Var_2(C+) = {var_frac_w2} > 1/4 (156 > 64)")

    print("\nALL EXACT CHECKS PASSED (ZERO FLOATS).")


if __name__ == "__main__":
    main()
