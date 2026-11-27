"""
explore_and_verify.py — Exact Pure-Silicon Carry-Valuation Automaton (CVA) Engine
Worker: adic-4 (Thread 4: 2-Adic, Nimber, Carry-Arithmetic & Number-Theoretic Infinite Mechanisms)

Zero floating-point arithmetic anywhere: all synthesis, tropical cycle-ratio bounds,
Bellman-Ford sub/super-potentials, exact coboundaries, instance verification, and
boundary counterexample searches use exact Python `int` and `fractions.Fraction`.
"""
from collections import deque
from fractions import Fraction
import math

# =============================================================================
# 1. Exact Arithmetic Primitives (Pure Integer)
# =============================================================================

def popcount(n: int) -> int:
    assert n >= 0
    return n.bit_count()

def v2_nat(n: int) -> int:
    """Exact 2-adic valuation of positive integer n (0 for n == 0)."""
    if n <= 0:
        return 0
    return (n & -n).bit_length() - 1

def v2_binom_exact(n: int, k: int) -> int:
    """Direct 2-adic valuation of C(n, k) via math.comb (independent of Kummer)."""
    return v2_nat(math.comb(n, k))

def v2_trinom_exact(a: int, b: int, c: int) -> int:
    """Direct 2-adic valuation of (a+b+c)! / (a! b! c!) (independent of Kummer)."""
    val = math.comb(a + b + c, a) * math.comb(b + c, b)
    return v2_nat(val)

def v2_binom_kummer(n: int, k: int) -> int:
    assert 0 <= k <= n
    return popcount(k) + popcount(n - k) - popcount(n)

def v2_trinom_kummer(a: int, b: int, c: int) -> int:
    return popcount(a) + popcount(b) + popcount(c) - popcount(a + b + c)

def gray(n: int) -> int:
    return n ^ (n >> 1)

# =============================================================================
# 2. Generic Finite-State Carry-Valuation Automaton (CVA) & Exact Solvers
# =============================================================================

class CVA:
    """Finite-state Carry-Valuation Automaton over binary input stream (Sigma = {0, 1})."""
    def __init__(self, num_states, q0, delta_table, w_table, tau_table):
        self.S = num_states
        self.q0 = q0
        self.delta = delta_table   # list of length S, each [d0, d1]
        self.w = w_table           # list of length S, each [w0, w1]
        self.tau = tau_table       # list of length S

    def eval(self, n: int, q: int = None) -> int:
        if q is None:
            q = self.q0
        total = 0
        while n > 0:
            b = n & 1
            total += self.w[q][b]
            q = self.delta[q][b]
            n >>= 1
        return total + self.tau[q]

    def solve_lower_potential(self):
        """Maximum sub-potential phi : Fin S -> Z with phi[q] <= tau[q] and phi[q] <= w[q][b] + phi[delta[q][b]]."""
        phi = list(self.tau)
        for _ in range(self.S + 2):
            changed = False
            for q in range(self.S):
                best = phi[q]
                for b in (0, 1):
                    cand = self.w[q][b] + phi[self.delta[q][b]]
                    if cand < best:
                        best = cand
                if best < phi[q]:
                    phi[q] = best
                    changed = True
            if not changed:
                # Independent verification of every inequality
                for q in range(self.S):
                    assert phi[q] <= self.tau[q]
                    for b in (0, 1):
                        assert phi[q] <= self.w[q][b] + phi[self.delta[q][b]]
                return phi
        return None

    def solve_upper_potential(self):
        """Minimum super-potential psi : Fin S -> Z with psi[q] >= tau[q] and psi[q] >= w[q][b] + psi[delta[q][b]]."""
        psi = list(self.tau)
        for _ in range(self.S + 2):
            changed = False
            for q in range(self.S):
                best = psi[q]
                for b in (0, 1):
                    cand = self.w[q][b] + psi[self.delta[q][b]]
                    if cand > best:
                        best = cand
                if best > psi[q]:
                    psi[q] = best
                    changed = True
            if not changed:
                for q in range(self.S):
                    assert psi[q] >= self.tau[q]
                    for b in (0, 1):
                        assert psi[q] >= self.w[q][b] + psi[self.delta[q][b]]
                return psi
        return None

    def verify_coboundary(self, phi):
        for q in range(self.S):
            if phi[q] != self.tau[q]:
                return False
            for b in (0, 1):
                if phi[q] != self.w[q][b] + phi[self.delta[q][b]]:
                    return False
        return True

# =============================================================================
# 3. Exact CVA Constructions Matching Proof.lean Encodings 1-to-1
# =============================================================================

# --- Family I: Shifted-Bitwise Kummer Collapse CVAs (4 states: (prev, c) in {0,1}x{0,1}) ---
# State encoding: idx = 2 * prev + c in Fin 4 (reachable subset has 3 states; all 4 satisfy coboundary? Let's check!)

def build_sxor_cva():
    """
    2 * v2(binom(n + (n ^ 2n), n)) - (2 * s2(n) + s2(n ^ 2n))
    State (prev, c) encoded as 2*prev + c in Fin 4.
    check if state (prev=1, c=0) is reachable?
    From (0,0) on b=1: xb=1, s=2 -> (1, 1).
    From (1,1) on b=0: xb=1, s=2 -> (0, 1). On b=1: xb=0, s=2 -> (1, 1).
    From (0,1) on b=0: xb=0, s=1 -> (0, 0). On b=1: xb=1, s=3 -> (1, 1).
    So (1, 0) is unreachable! Still let's check if phi works on all 4 states OR on Fin 3!
    Let's check both Fin 4 (with reachability mask) and direct Fin 3!
    for (1,0): on b=0, xb=1, s=1 -> (0,0), w = 1 - 2*1 = -1. tau = 1 - 2*pop(1) = -1.
    On b=1, xb=0, s=1 -> (1,0), w = 0 - 2*1 = -2 != 0! So (1,0) does NOT satisfy coboundary —
    that's a great demonstration of why reachability masks / Fin 3 reachable encoding matters!
    """
    # Exact 3-state encoding: 0 -> (0,0), 1 -> (1,1), 2 -> (0,1)
    states = [(0, 0), (1, 1), (0, 1)]
    idx = {st: i for i, st in enumerate(states)}
    delta, w, tau = [], [], []
    for prev, c in states:
        drow, wrow = [], []
        for b in (0, 1):
            xb = b ^ prev
            s = b + xb + c
            drow.append(idx[(b, s >> 1)])
            # 2*(b + xb - (s&1)) - (2*b + xb) = xb - 2*(s&1)
            wrow.append(xb - 2 * (s & 1))
        delta.append(drow)
        w.append(wrow)
        tau.append(prev - 2 * popcount(prev + c))
    return CVA(3, 0, delta, w, tau), states

def build_sor_cva():
    """
    v2(binom(n + (n | 2n), n)) - s2(n | 2n) = s2(n) - s2(n + (n | 2n))
    States (prev, c):
      (0,0) --0--> (0,0), --1--> (1,1)
      (1,1) --0--> (0,1), --1--> (1,1)
      (0,1) --0--> (0,0), --1--> (1,1)
    Same 3 reachable states: 0 -> (0,0), 1 -> (1,1), 2 -> (0,1)!
    """
    states = [(0, 0), (1, 1), (0, 1)]
    idx = {st: i for i, st in enumerate(states)}
    delta, w, tau = [], [], []
    for prev, c in states:
        drow, wrow = [], []
        for b in (0, 1):
            ob = b | prev
            s = b + ob + c
            drow.append(idx[(b, s >> 1)])
            wrow.append(b - (s & 1))
        delta.append(drow)
        w.append(wrow)
        tau.append(-popcount(prev + c))
    return CVA(3, 0, delta, w, tau), states

def build_sand_cva():
    """
    v2(binom(n + (n & 2n), n)) - s2(n & 2n) = s2(n) - s2(n + (n & 2n))
    States (prev, c):
      (0,0) --0--> (0,0), --1--> (1,0)
      (1,0) --0--> (0,0), --1--> (1,1)
      (1,1) --0--> (0,0), --1--> (1,1)
    3 reachable states: 0 -> (0,0), 1 -> (1,0), 2 -> (1,1)!
    """
    states = [(0, 0), (1, 0), (1, 1)]
    idx = {st: i for i, st in enumerate(states)}
    delta, w, tau = [], [], []
    for prev, c in states:
        drow, wrow = [], []
        for b in (0, 1):
            ab = b & prev
            s = b + ab + c
            drow.append(idx[(b, s >> 1)])
            wrow.append(b - (s & 1))
        delta.append(drow)
        w.append(wrow)
        tau.append(-popcount(c))
    return CVA(3, 0, delta, w, tau), states

# --- Family II: Gray-Code Binomial CVA (5 states: init + (prev, c) in {0,1}x{0,1}) ---
# State encoding in Fin 5: 0=init, 1=(0,0), 2=(1,0), 3=(0,1), 4=(1,1)

def build_gray_cvas():
    states = [("init", 0, 0), ("run", 0, 0), ("run", 1, 0), ("run", 0, 1), ("run", 1, 1)]
    idx = {st: i for i, st in enumerate(states)}
    delta = []
    w_lo, tau_lo = [], []  # 2*v2(binom(n+G(n), n)) - s2(G(n))
    w_hi, tau_hi = [], []  # 2*v2(binom(n+G(n), n)) - (2*s2(n) + s2(G(n)))
    for tag, prev, c in states:
        drow, wlrow, whrow = [], [], []
        for b in (0, 1):
            if tag == "init":
                drow.append(idx[("run", b, 0)])
                wlrow.append(0)
                whrow.append(0)
            else:
                gb = prev ^ b
                s = prev + gb + c
                drow.append(idx[("run", b, s >> 1)])
                v2_step = prev + gb - (s & 1)
                wlrow.append(2 * v2_step - gb)
                whrow.append(2 * v2_step - 2 * prev - gb)
        delta.append(drow)
        w_lo.append(wlrow)
        w_hi.append(whrow)
        if tag == "init":
            tau_lo.append(0)
            tau_hi.append(0)
        else:
            v2_t = 2 * prev - popcount(2 * prev + c)
            tau_lo.append(2 * v2_t - prev)
            tau_hi.append(2 * v2_t - 3 * prev)
    return CVA(5, 0, delta, w_lo, tau_lo), CVA(5, 0, delta, w_hi, tau_hi), states

# --- Family III: Generic k-Binomial CVA on 2*(k-1) states (c1 in Fin (k-1), d in {0,1}) ---
# State encoding: idx = 2 * c1 + d, where c2 = c1 + d < k.

def build_kbinom_cva(k: int, p: int, q: int):
    assert k >= 3 and k % 2 == 1
    S = 2 * (k - 1)
    delta, w, tau = [], [], []
    for idx in range(S):
        c1 = idx // 2
        d = idx % 2
        c2 = c1 + d
        drow, wrow = [], []
        for b in (0, 1):
            s1 = (k - 1) * b + c1
            s2 = k * b + c2
            c1p = s1 >> 1
            c2p = s2 >> 1
            dp = c2p - c1p
            assert 0 <= c1p < k - 1 and dp in (0, 1)
            drow.append(2 * c1p + dp)
            v_w = b + (s1 & 1) - (s2 & 1)
            wrow.append(q * v_w - p * b)
        delta.append(drow)
        w.append(wrow)
        tau.append(q * (popcount(c1) - popcount(c2)))
    # Odd-start state after reading LSB = 1 from (0, 0): c1 = (k-1)//2, d = 0
    q_odd = 2 * ((k - 1) // 2)
    return CVA(S, q_odd, delta, w, tau)

# =============================================================================
# 4. Run Complete Synthesis, Exact Replay Verification, and Counterexample Audit
# =============================================================================

def main():
    print("=========================================================================")
    print("  PURE-SILICON CARRY-VALUATION AUTOMATON (CVA) SYNTHESIS & AUDIT REPORT  ")
    print("=========================================================================\n")

    # -------------------------------------------------------------------------
    # Family I: Shifted-Bitwise Kummer Collapse Laws
    # -------------------------------------------------------------------------
    print("--- FAMILY I: Shifted-Bitwise Kummer Collapse Laws (Exact Coboundaries) ---")
    cva_sxor, st_sxor = build_sxor_cva()
    phi_sxor = cva_sxor.solve_lower_potential()
    assert cva_sxor.verify_coboundary(phi_sxor) and phi_sxor[0] == 0
    print(f"  [CERT] Shifted-XOR 3-state exact coboundary phi = {phi_sxor}")

    cva_sor, st_sor = build_sor_cva()
    phi_sor = cva_sor.solve_lower_potential()
    assert cva_sor.verify_coboundary(phi_sor) and phi_sor[0] == 0
    print(f"  [CERT] Shifted-OR  3-state exact coboundary phi = {phi_sor}")

    cva_sand, st_sand = build_sand_cva()
    phi_sand = cva_sand.solve_lower_potential()
    assert cva_sand.verify_coboundary(phi_sand) and phi_sand[0] == 0
    print(f"  [CERT] Shifted-AND 3-state exact coboundary phi = {phi_sand}")

    # Direct verification against math.comb (independent of Kummer!) for 0 <= n <= 200
    for n in range(201):
        v_sx = v2_binom_exact(n + (n ^ (2 * n)), n)
        v_so = v2_binom_exact(n + (n | (2 * n)), n)
        v_sa = v2_binom_exact(n + (n & (2 * n)), n)
        v_tr = v2_trinom_exact(n, 2 * n, n ^ (2 * n))
        assert v_sx == popcount(n | (2 * n))
        assert 2 * v_sx == 2 * popcount(n) + popcount(n ^ (2 * n))
        assert v_so == popcount(n | (2 * n))
        assert v_sa == popcount(n & (2 * n))
        assert v_tr == popcount(n | (2 * n))
    # Extended Kummer verification for 0 <= n < 100000
    for n in range(100000):
        assert v2_binom_kummer(n + (n ^ (2 * n)), n) == popcount(n | (2 * n))
        assert v2_binom_kummer(n + (n | (2 * n)), n) == popcount(n | (2 * n))
        assert v2_binom_kummer(n + (n & (2 * n)), n) == popcount(n & (2 * n))
        assert v2_trinom_kummer(n, 2 * n, n ^ (2 * n)) == popcount(n | (2 * n))
    print("  [PASS] Independently verified via math.comb (n <= 200) and Kummer (n < 100,000).")

    # Sharpness counterexamples (shift k=2 and general (a, b))
    assert v2_binom_exact(1 + (1 ^ 4), 1) == 1 != 2 == popcount(1 | 4)
    assert v2_binom_exact(1 + (1 | 4), 1) == 1 != 2 == popcount(1 | 4)
    assert v2_binom_exact(13 + (13 & 52), 13) == 2 != 1 == popcount(13 & 52)
    assert v2_binom_exact(3 + (3 & 1), 3) == 2 != 1 == popcount(3 & 1)
    print("  [SHARP] Counterexamples verified: shift k=2 fails at n=1 (^,|) and n=13 (&); general (a,b) fails at (1,4) and (3,1).\n")

    # -------------------------------------------------------------------------
    # Family II: Gray-Code Binomial Two-Sided Sharp Valuation Sandwich
    # -------------------------------------------------------------------------
    print("--- FAMILY II: Gray-Code Binomial Sandwich (5-state Tropical Potentials) ---")
    cva_glo, cva_ghi, st_g = build_gray_cvas()
    phi_glo = cva_glo.solve_lower_potential()
    psi_ghi = cva_ghi.solve_upper_potential()
    assert phi_glo[0] == 0 and psi_ghi[0] == 0
    print(f"  [CERT] Gray lower sub-potential   phi = {phi_glo}  => 2*v2(C(n+G(n),n)) >= s2(G(n))")
    print(f"  [CERT] Gray upper super-potential psi = {psi_ghi}  => 2*v2(C(n+G(n),n)) <= 2*s2(n) + s2(G(n))")

    # Independent verification via math.comb (n <= 300) and Kummer (n < 100000)
    for n in range(301):
        v = v2_binom_exact(n + gray(n), n)
        assert 2 * v >= popcount(gray(n))
        assert 2 * v <= 2 * popcount(n) + popcount(gray(n))
        if n >= 1:
            assert v >= 1
            assert v + 1 <= popcount(n | (2 * n))
    for n in range(1, 100000):
        v = v2_binom_kummer(n + gray(n), n)
        assert 2 * v >= popcount(gray(n))
        assert v + 1 <= popcount(n | (2 * n))

    # Infinite sharpness family (lower): n_m = 6 * (16^m - 1) / 15
    for m in range(1, 25):
        nm = 6 * (16**m - 1) // 15
        v = v2_binom_kummer(nm + gray(nm), nm)
        sg = popcount(gray(nm))
        assert sg == 2 * m and v == m and 2 * v == sg
    # Infinite sharpness family (upper): n_m = (4^m - 1) / 3
    for m in range(1, 25):
        nm = (4**m - 1) // 3
        v = v2_binom_kummer(nm + gray(nm), nm)
        s_or = popcount(nm | (2 * nm))
        assert s_or == 2 * m and v == 2 * m - 1 and v + 1 == s_or
    print("  [PASS] Verified via math.comb (n <= 300) and Kummer (n < 100,000).")
    print("  [SHARP] Lower attainment n_m = 6*(16^m-1)/15 (m=1..24): 2*v2 = s2(G(n_m)) = 2m.")
    print("  [SHARP] Upper attainment n_m = (4^m-1)/3     (m=1..24): v2 = s2(n_m|2n_m) - 1 = 2m - 1.\n")

    # -------------------------------------------------------------------------
    # Family III: Non-Integer Tropical Carry-Valuation Slope Laws for C(k*n, n)
    # -------------------------------------------------------------------------
    print("--- FAMILY III: Non-Integer Tropical Carry-Valuation Slopes for C(k*n, n) ---")
    cases = [
        (11, 5, 2, -2, lambda m: 3 * (32**m - 1) // 31, lambda m: 2 * m, lambda m: 5 * m - 1),
        (25, 8, 3, -3, lambda m: 41 * (1024**m - 1) // 1023, lambda m: 3 * m, lambda m: 8 * m - 1),
        (55, 13, 4, -8, lambda m: 149 * (8192**m - 1) // 8191, lambda m: 4 * m, lambda m: 13 * m - 2),
    ]

    for k, p, q, expected_bound, fam_fn, s2_fn, v2_fn in cases:
        cva = build_kbinom_cva(k, p, q)
        psi = cva.solve_upper_potential()
        actual_bound = -p + psi[cva.q0]
        assert actual_bound == expected_bound, f"k={k}: got {actual_bound}, expected {expected_bound}"
        print(f"  [CERT] k={k:2d} ({cva.S:3d} states): {q}*v2(C({k}n, n)) <= {p}*s2(n) + ({actual_bound}) for ALL n >= 1")
        if k in (11, 25):
            print(f"         psi_{k} = {psi}")
        # Independent math.comb verification for small n
        limit_comb = 40 if k == 55 else (80 if k == 25 else 120)
        for n in range(1, limit_comb + 1):
            v = v2_binom_exact(k * n, n)
            assert q * v <= p * popcount(n) + actual_bound
        # Extended Kummer verification for 1 <= n < 100000
        for n in range(1, 100000):
            v = v2_binom_kummer(k * n, n)
            assert q * v <= p * popcount(n) + actual_bound
        # Infinite attainment family check
        if fam_fn is not None:
            for m in range(1, 20):
                nm = fam_fn(m)
                s = popcount(nm)
                v = v2_binom_kummer(k * nm, nm)
                assert s == s2_fn(m) and v == v2_fn(m)
                assert q * v == p * s + actual_bound
            print(f"  [SHARP] Infinite attainment verified for m=1..19: {q}*v2(n_m) == {p}*s2(n_m) + ({actual_bound})")

    # Explicit boundary counterexamples showing slope & offset cannot be tightened
    # k=11: tightening -2 to -3 fails at n=3 (2*4 = 8 > 5*2 - 3 = 7); slope 2 fails at n=99 (v2=9 > 8)
    assert 2 * v2_binom_exact(33, 3) == 8 and 5 * popcount(3) - 3 == 7
    assert v2_binom_exact(11 * 99, 99) == 9 and 2 * popcount(99) == 8
    # k=25: tightening -3 to -4 fails at n=41 (3*7 = 21 > 8*3 - 4 = 20); slope 5/2 fails at n=43033641 (v2=23, s2=9 -> 46 > 45)
    assert 3 * v2_binom_exact(25 * 41, 41) == 21 and 8 * popcount(41) - 4 == 20
    n_k25_m3 = 41 * (1024**3 - 1) // 1023
    assert 2 * v2_binom_kummer(25 * n_k25_m3, n_k25_m3) == 46 > 45 == 5 * popcount(n_k25_m3)
    print("  [SHARP] Boundary counterexamples verified for k=11 (n=3, n=99) and k=25 (n=41, n=43033641).")
    print("\nALL CERTIFICATES, EXACT REPLAYS, INFINITE ATTAINMENT FAMILIES, AND COUNTEREXAMPLES PASSED!")

if __name__ == "__main__":
    main()
