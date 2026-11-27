#!/usr/bin/env python3
r"""
Exact Pure-Silicon Exploration, Certificate Synthesis, and Independent Replay
for the Kronecker-Woodbury Schur-Tower Riccati Engine (specmat-11).

All arithmetic uses exact Python `int` and `fractions.Fraction` (zero floats).
Verifies:
  1. Bit-serial affine transducer equivalence:
       M_k(i, j) = m0 * prod_{r=0}^{k-1} C[i_r, j_r]
                 + sum_{s=0}^{k-1} (prod_{r=s+1}^{k-1} C[i_r, j_r]) * B[i_s, j_s]
     equals the Kronecker-plus-low-rank recursion:
       M_{k+1} = (C \otimes M_k) + (B \otimes J_k).
  2. Exact determinant, exact recursive Woodbury inverse M_k^{-1} (checking M_k * M_k^{-1} = I),
     and exact capacitance S_k = 1_k^T M_k^{-1} 1_k for ALL FOUR qualitative regimes:
       - Theorem 1 (Fixed-Point):   Carry-Generate Perturbed Walsh-Hadamard W_k^(lam)
       - Theorem 2 (Period-2 Cycle): Skew-Borrow Perturbed Walsh-Hadamard B_k
       - Theorem 3 (Zero Absorption): Bit-Equality Perturbed Walsh-Hadamard E_k
       - Theorem 4 (Harmonic Decay): Prefix-Summed Walsh-Hadamard P_k^(m0, lam)
  3. Exact Singularity Converse & Sharpness Counterexamples:
       - W_k^(2) singular for all k >= 1 with explicit nonzero null vector
       - P_k^(N, -1) invertible for all k < N and singular at k = N with explicit null vector
       - Non-Walsh Hamming & Asymmetric Carry-Lookahead demonstrations of engine generality
       - Boundary counterexamples showing where relaxing hypotheses breaks each law.
r"""

from fractions import Fraction
import sys


def popcount(x: int) -> int:
    return bin(x).count("1")


def mat_mul(A, B):
    m, p, n = len(A), len(B), len(B[0])
    return [
        [sum(A[i][k] * B[k][j] for k in range(p)) for j in range(n)]
        for i in range(m)
    ]


def mat_vec(A, v):
    return [sum(A[i][j] * v[j] for j in range(len(v))) for i in range(len(A))]


def is_identity(M) -> bool:
    n = len(M)
    for i in range(n):
        for j in range(n):
            if M[i][j] != (Fraction(1) if i == j else Fraction(0)):
                return False
    return True


def mat_det_exact(M) -> Fraction:
    r"""Exact Gaussian-elimination determinant over Q (Fraction).r"""
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    det = Fraction(1)
    for col in range(n):
        pivot = None
        for row in range(col, n):
            if A[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            det = -det
        pv = A[col][col]
        det *= pv
        for row in range(col + 1, n):
            f = A[row][col] / pv
            if f != 0:
                for c in range(col + 1, n):
                    A[row][c] -= f * A[col][c]
    return det


def mat2_inv(A):
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    if det == 0:
        return None
    return [
        [A[1][1] / det, -A[0][1] / det],
        [-A[1][0] / det, A[0][0] / det],
    ]


def kron(A, B):
    ma, na = len(A), len(A[0])
    mb, nb = len(B), len(B[0])
    out = [[Fraction(0)] * (na * nb) for _ in range(ma * mb)]
    for ia in range(ma):
        for ja in range(na):
            a = A[ia][ja]
            for ib in range(mb):
                for jb in range(nb):
                    out[ia * mb + ib][ja * nb + jb] = a * B[ib][jb]
    return out


def build_transducer_entrywise(C, B, m0: Fraction, k: int):
    r"""Pure-silicon bit-serial affine transducer evaluated directly bit-by-bit.r"""
    N = 1 << k
    M = [[Fraction(0)] * N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            acc = Fraction(m0)
            for r in range(k):
                ir = (i >> r) & 1
                jr = (j >> r) & 1
                acc = C[ir][jr] * acc + B[ir][jr]
            M[i][j] = acc
    return M


def build_tower_recursive(C, B, m0: Fraction, k: int):
    r"""Kronecker-plus-low-rank tower M_{k+1} = (C \\otimes M_k) + (B \\otimes J_k).r"""
    M = [[Fraction(m0)]]
    for _ in range(k):
        n = len(M)
        M_next = [[Fraction(0)] * (2 * n) for _ in range(2 * n)]
        for a in range(2):
            for b in range(2):
                for i in range(n):
                    for j in range(n):
                        M_next[a * n + i][b * n + j] = C[a][b] * M[i][j] + B[a][b]
        M = M_next
    return M


def woodbury_tower_inv(C, B, m0: Fraction, k: int):
    r"""
    Constructs M_k^{-1} purely via the Kronecker-Woodbury Schur-Tower recursion:
      W_0 = [[1 / m0]], S_0 = 1 / m0
      Q_j = (C + S_j * B)^{-1}
      W_{j+1} = (C^{-1} \\otimes W_j) - (C^{-1} B Q_j) \\otimes (W_j J W_j)
      S_{j+1} = S_j * (1^T Q_j 1)
    Returns (W_k, S_k) or (None, None) if singular at some step.
    r"""
    Cinv = mat2_inv(C)
    if Cinv is None or m0 == 0:
        return None, None
    W = [[Fraction(1) / Fraction(m0)]]
    S = Fraction(1) / Fraction(m0)
    for _ in range(k):
        CB = [[C[a][b] + S * B[a][b] for b in range(2)] for a in range(2)]
        Q = mat2_inv(CB)
        if Q is None:
            return None, None
        # Compute K2 = Cinv * B * Q
        K2 = mat_mul(mat_mul(Cinv, B), Q)
        # Compute W * 1_n and 1_n^T * W
        n = len(W)
        row_sums = [sum(W[i]) for i in range(n)]
        col_sums = [sum(W[i][j] for i in range(n)) for j in range(n)]
        # W_next = kron(Cinv, W) - kron(K2, outer(row_sums, col_sums))
        W_next = [[Fraction(0)] * (2 * n) for _ in range(2 * n)]
        for a in range(2):
            for b in range(2):
                ci = Cinv[a][b]
                k2 = K2[a][b]
                for i in range(n):
                    rs = row_sums[i]
                    for j in range(n):
                        W_next[a * n + i][b * n + j] = ci * W[i][j] - k2 * rs * col_sums[j]
        W = W_next
        S = S * (Q[0][0] + Q[0][1] + Q[1][0] + Q[1][1])
    return W, S


def verify_all():
    H2 = [[Fraction(1), Fraction(1)], [Fraction(1), Fraction(-1)]]
    print("=========================================================================")
    print("  specmat-11: Kronecker-Woodbury Schur-Tower Riccati Engine Replay")
    print("=========================================================================")

    # ------------------------------------------------------------------
    # Theorem 1: Carry-Generate Perturbed Walsh-Hadamard (Fixed-Point Regime)
    # ------------------------------------------------------------------
    print("\n[Theorem 1] Carry-Generate Perturbed Walsh-Hadamard W_k^(lam)")
    for lam in [-3, -1, 0, 1, 3, 5]:
        B = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(lam)]]
        for k in range(0, 6):
            M_bit = build_transducer_entrywise(H2, B, Fraction(1), k)
            M_rec = build_tower_recursive(H2, B, Fraction(1), k)
            assert M_bit == M_rec, f"Transducer != Tower at lam={lam}, k={k}"

            # Also check explicit bitwise popcount/shiftRight formula:
            N = 1 << k
            for i in range(N):
                for j in range(N):
                    val = Fraction((-1) ** popcount(i & j))
                    for s in range(k):
                        if ((i >> s) & 1) and ((j >> s) & 1):
                            val += Fraction(lam) * ((-1) ** popcount((i >> (s + 1)) & (j >> (s + 1))))
                    assert M_bit[i][j] == val

            det_exact = mat_det_exact(M_bit)
            if k == 0:
                det_pred = Fraction(1)
            elif k == 1:
                det_pred = Fraction(lam - 2)
            else:
                det_pred = Fraction(2 ** ((k - 2) * (1 << (k - 1)) + 1)) * Fraction(2 - lam) ** ((1 << k) - 1)
            assert det_exact == det_pred, f"Det mismatch lam={lam}, k={k}: {det_exact} != {det_pred}"

            W, S = woodbury_tower_inv(H2, B, Fraction(1), k)
            assert W is not None and is_identity(mat_mul(M_bit, W))
            assert S == Fraction(1)
            assert sum(sum(row) for row in W) == Fraction(1)
        print(f"  lam={lam:2d}: k=0..5 EXACT MATCH (det, W*M=I, S_k=1 fixed point)")

    # Sharpness 1b: lam = 2 singular for all k >= 1 with explicit null vector
    B_sing = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(2)]]
    for k in range(1, 6):
        M_k = build_transducer_entrywise(H2, B_sing, Fraction(1), k)
        assert mat_det_exact(M_k) == 0
        # Explicit nonzero null vector: at k=1, H2 + 1*B_sing = [[1,1],[1,1]] has kernel w = [1, -1].
        # For k >= 1, since M_1 is already singular, w_k = [1,-1] \otimes e_0 \otimes ... or directly
        # for k=1: v = [1, -1]; for general k >= 1: e_0^{k-1} \otimes [1, -1] (i.e. i=0 vs i=1? Let's check!)
        # Actually row(0) and row(1) in bit-0? No, at bit k-1: M_k = [[M_{k-1}, M_{k-1}], [M_{k-1}, -M_{k-1}+2J]].
        # At k=1, M_1 = [[1,1],[1,1]], so M_1 * [1, -1]^T = 0.
        # In general for any k >= 1: M_k(i, j) for j=0 vs j=1:
        # Wait: LSB bit 0 is identical for j=0 (0) and j=1 (1): wait at r=0, (0,0)->1, (0,1)->1, (1,0)->1, (1,1)->-1+2=1!
        # EVERY bit-0 output of M_1 is 1! So column 0 == column 1 for ALL k >= 1!
        # Hence v = e_0 - e_1 is ALWAYS in ker(M_k) for EVERY k >= 1!
        v = [Fraction(0)] * (1 << k)
        v[0] = Fraction(1)
        v[1] = Fraction(-1)
        assert mat_vec(M_k, v) == [Fraction(0)] * (1 << k)
    print("  Sharpness 1b (lam=2): k=1..5 ALL SINGULAR, det=0, explicit null vector e_0 - e_1 verified!")

    # ------------------------------------------------------------------
    # Theorem 2: Skew-Borrow Perturbed Walsh-Hadamard (Period-2 Limit Cycle)
    # ------------------------------------------------------------------
    print("\n[Theorem 2] Skew-Borrow Perturbed Walsh-Hadamard B_k")
    B_skew = [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(0)]]
    for k in range(0, 6):
        M_bit = build_transducer_entrywise(H2, B_skew, Fraction(1), k)
        M_rec = build_tower_recursive(H2, B_skew, Fraction(1), k)
        assert M_bit == M_rec
        N = 1 << k
        for i in range(N):
            for j in range(N):
                val = Fraction((-1) ** popcount(i & j))
                for s in range(k):
                    js = (j >> s) & 1
                    is_ = (i >> s) & 1
                    val += Fraction(js - is_) * ((-1) ** popcount((i >> (s + 1)) & (j >> (s + 1))))
                assert M_bit[i][j] == val

        det_exact = mat_det_exact(M_bit)
        det_pred = Fraction(1) if k == 0 else Fraction(-(2 ** ((k - 1) * (1 << (k - 1)))))
        assert det_exact == det_pred, f"Skew det mismatch k={k}: {det_exact} != {det_pred}"

        W, S = woodbury_tower_inv(H2, B_skew, Fraction(1), k)
        assert W is not None and is_identity(mat_mul(M_bit, W))
        S_pred = Fraction(1) if k == 0 else (Fraction(2) if k % 2 == 1 else Fraction(-2))
        assert S == S_pred and sum(sum(row) for row in W) == S_pred
        print(f"  k={k}: det = {det_exact}, S_k = {S} (period-2 cycle), M*W = I verified")

    # ------------------------------------------------------------------
    # Theorem 3: Bit-Equality Perturbed Walsh-Hadamard (Zero-Absorption Regime)
    # ------------------------------------------------------------------
    print("\n[Theorem 3] Bit-Equality Perturbed Walsh-Hadamard E_k")
    B_eq = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
    for k in range(0, 6):
        M_bit = build_transducer_entrywise(H2, B_eq, Fraction(1), k)
        M_rec = build_tower_recursive(H2, B_eq, Fraction(1), k)
        assert M_bit == M_rec
        N = 1 << k
        for i in range(N):
            for j in range(N):
                val = Fraction((-1) ** popcount(i & j))
                for s in range(k):
                    if ((i >> s) & 1) == ((j >> s) & 1):
                        val += Fraction((-1) ** popcount((i >> (s + 1)) & (j >> (s + 1))))
                assert M_bit[i][j] == val

        det_exact = mat_det_exact(M_bit)
        if k == 0:
            det_pred = Fraction(1)
        elif k == 1:
            det_pred = Fraction(-1)
        else:
            det_pred = Fraction(2 ** ((k - 1) * (1 << (k - 1))))
        assert det_exact == det_pred

        W, S = woodbury_tower_inv(H2, B_eq, Fraction(1), k)
        assert W is not None and is_identity(mat_mul(M_bit, W))
        S_pred = Fraction(1) if k == 0 else Fraction(0)
        assert S == S_pred and sum(sum(row) for row in W) == S_pred
        print(f"  k={k}: det = {det_exact}, S_k = {S} (zero-sum inverse), M*W = I verified")

    # ------------------------------------------------------------------
    # Theorem 4: Prefix-Summed Walsh-Hadamard (Harmonic Mobius Decay)
    # ------------------------------------------------------------------
    print("\n[Theorem 4] Prefix-Summed Walsh-Hadamard P_k^(m0, lam)")
    for m0, lam in [(1, 1), (1, 2), (3, 2)]:
        B_j = [[Fraction(lam), Fraction(lam)], [Fraction(lam), Fraction(lam)]]
        for k in range(0, 6):
            M_bit = build_transducer_entrywise(H2, B_j, Fraction(m0), k)
            M_rec = build_tower_recursive(H2, B_j, Fraction(m0), k)
            assert M_bit == M_rec
            N = 1 << k
            for i in range(N):
                for j in range(N):
                    val = Fraction(m0) * ((-1) ** popcount(i & j))
                    for s in range(1, k + 1):
                        val += Fraction(lam) * ((-1) ** popcount((i >> s) & (j >> s)))
                    assert M_bit[i][j] == val

            det_exact = mat_det_exact(M_bit)
            sign = -1 if k == 1 else 1
            prod_term = Fraction(m0 + k * lam)
            for j in range(k):
                prod_term *= Fraction(m0 + j * lam) ** (1 << (k - 1 - j))
            det_pred = Fraction(sign) * Fraction(2 ** (k * (1 << (k - 1)) if k > 0 else 0)) * prod_term
            assert det_exact == det_pred, f"Prefix det mismatch m0={m0}, lam={lam}, k={k}: {det_exact} != {det_pred}"

            W, S = woodbury_tower_inv(H2, B_j, Fraction(m0), k)
            assert W is not None and is_identity(mat_mul(M_bit, W))
            assert S == Fraction(1, m0 + k * lam)
            assert sum(sum(row) for row in W) == Fraction(1, m0 + k * lam)
        print(f"  (m0={m0}, lam={lam}): k=0..5 EXACT MATCH (det, W*M=I, S_k=1/(m0+k*lam))")

    # Sharpness 4b: Programmable Depth-N Singularity for P_k^(N, -1)
    print("\n[Sharpness 4b] Programmable Depth-N Singularity P_k^(N, -1)")
    B_neg = [[Fraction(-1), Fraction(-1)], [Fraction(-1), Fraction(-1)]]
    for N_target in range(1, 6):
        # Verify invertible for all k < N_target
        for k in range(N_target):
            M_k = build_transducer_entrywise(H2, B_neg, Fraction(N_target), k)
            assert mat_det_exact(M_k) != 0
        # Verify singular at k = N_target with explicit Woodbury-lifted null vector!
        M_prev = build_transducer_entrywise(H2, B_neg, Fraction(N_target), N_target - 1)
        W_prev, S_prev = woodbury_tower_inv(H2, B_neg, Fraction(N_target), N_target - 1)
        assert S_prev == Fraction(1)
        # At k = N_target, H2 + 1 * (-J_2) = [[0, 0], [0, -2]] has kernel w = [1, 0]!
        # So v = [1, 0] \otimes (W_prev * 1_{N_target - 1}) is a nonzero null vector of M_{N_target}!
        u_prev = [sum(row) for row in W_prev]
        assert any(x != 0 for x in u_prev)
        v_null = u_prev + [Fraction(0)] * len(u_prev)
        M_sing = build_transducer_entrywise(H2, B_neg, Fraction(N_target), N_target)
        assert mat_det_exact(M_sing) == 0
        assert mat_vec(M_sing, v_null) == [Fraction(0)] * (1 << N_target)
        print(f"  N={N_target}: invertible for k=0..{N_target-1}, SINGULAR at k={N_target} with explicit kernel vector verified!")

    # ------------------------------------------------------------------
    # Generality Demonstration: Non-Walsh Cores (Hamming & Asymmetric Carry-Lookahead)
    # ------------------------------------------------------------------
    print("\n[Generality Check] Non-Walsh Cores via the SAME Schur-Tower Engine")
    for name, C_core, B_pert, m0 in [
        ("Hamming C=[[1,2],[2,1]] + CarryGen [[0,0],[0,1]]",
         [[Fraction(1), Fraction(2)], [Fraction(2), Fraction(1)]],
         [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(1)]],
         Fraction(1)),
        ("Asymmetric Carry-Lookahead C=[[1,2],[3,1]] + Borrow [[0,1],[-1,2]]",
         [[Fraction(1), Fraction(2)], [Fraction(3), Fraction(1)]],
         [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(2)]],
         Fraction(2)),
    ]:
        det_C = C_core[0][0] * C_core[1][1] - C_core[0][1] * C_core[1][0]
        S = Fraction(1) / m0
        det_pred = m0
        for k in range(1, 5):
            M_k = build_transducer_entrywise(C_core, B_pert, m0, k)
            CB = [[C_core[a][b] + S * B_pert[a][b] for b in range(2)] for a in range(2)]
            det_CB = CB[0][0] * CB[1][1] - CB[0][1] * CB[1][0]
            det_pred = (det_C ** ((1 << (k - 1)) - 1)) * det_CB * (det_pred ** 2)
            assert mat_det_exact(M_k) == det_pred
            W, S_next = woodbury_tower_inv(C_core, B_pert, m0, k)
            assert W is not None and is_identity(mat_mul(M_k, W))
            S = S_next
        print(f"  {name}: k=1..4 EXACT MATCH (det, Woodbury inverse, capacitance)!")

    # ------------------------------------------------------------------
    # Sharpness Counterexamples (Relaxing Engine Hypotheses)
    # ------------------------------------------------------------------
    print("\n[Sharpness Counterexamples]")
    # 1. Singular core C = [[1,1],[1,1]] (det(C)=0):
    #    Even with B = I_2 and m0 = 1, M_1 = [[2,1],[1,2]] is invertible (det=3),
    #    but M_2 has rank <= 4? Wait: M_2 = (J_2 \otimes M_1) + (I_2 \otimes J_2) is singular!
    C_sing = [[Fraction(1), Fraction(1)], [Fraction(1), Fraction(1)]]
    M1_cs = build_transducer_entrywise(C_sing, B_eq, Fraction(1), 1)
    M2_cs = build_transducer_entrywise(C_sing, B_eq, Fraction(1), 2)
    assert mat_det_exact(M1_cs) == 3 and mat_det_exact(M2_cs) == 0
    print(f"  1. Singular core C=J_2, B=I_2: det(M_1)={mat_det_exact(M1_cs)} != 0, but det(M_2)={mat_det_exact(M2_cs)} (tower breaks when C is singular!)")

    # 2. Breaking bit-constancy of perturbation (non-low-rank diagonal perturbation):
    #    Replacing J_k by I_k in M_{k+1} = (H_2 \otimes M_k) + (B \otimes I_k) leaves the low-rank tower class:
    #    for B = [[0,0],[0,1]], det(M_2) = 1 != 2 (predicted by Theorem 1).
    M1_diag = [[Fraction(1), Fraction(1)], [Fraction(1), Fraction(0)]]
    M2_diag = [[Fraction(0)] * 4 for _ in range(4)]
    for a in range(2):
        for b in range(2):
            for i in range(2):
                for j in range(2):
                    M2_diag[2 * a + i][2 * b + j] = H2[a][b] * M1_diag[i][j] + (1 if (a == 1 and b == 1 and i == j) else 0)
    d_diag = mat_det_exact(M2_diag)
    assert d_diag != 2
    print(f"  2. Full-rank perturbation (B \\otimes I_k instead of B \\otimes J_k): det(M_2)={d_diag} != 2 (Theorem 1 breaks)")

    print("\nALL EXACT CHECKS PASSED WITH ZERO ERRORS (100% EXACT Q/Z ARITHMETIC).")


if __name__ == "__main__":
    verify_all()
