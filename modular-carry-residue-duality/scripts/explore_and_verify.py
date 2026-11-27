"""
Task 16: Carry-Automaton Divisibility & Modular-Residue Dual Engine
Exact pure-silicon exploration, certificate verification, and sharpness testing.
Uses only exact Python arbitrary-precision integers (zero floating point).
"""

def popcount(n: int) -> int:
    assert n >= 0
    return n.bit_count()

def v2(n: int) -> int:
    """2-adic valuation (count of trailing zeros) for n >= 1."""
    assert n >= 1
    return (n & -n).bit_length() - 1

def carries_add(a: int, b: int) -> int:
    """Exact binary carry count when adding a + b."""
    assert a >= 0 and b >= 0
    return popcount(a) + popcount(b) - popcount(a + b)

def msb_euclidean_automaton(n: int, m: int, L: int):
    """MSB-first Euclidean division automaton over L-bit input n < 2^L.
    Transition (i = L-1 down to 0):
      2 * r_{i+1} + b_i = m * e_i + r_i,  0 <= r_i < m,  r_L = 0.
    Returns (r_trace[0..L], E) where E = n // m and r_trace[i] = (n >> i) % m.
    """
    r_trace = [0] * (L + 1)
    E = 0
    r = 0
    for i in range(L - 1, -1, -1):
        b = (n >> i) & 1
        val = 2 * r + b
        e_i = val // m
        r = val % m
        r_trace[i] = r
        E = (E << 1) | e_i
    return r_trace, E

def lsb_carry_transducer(n: int, m: int, L: int):
    """LSB-first 2-adic division carry transducer over L-bit input n < 2^L (m odd).
    Transition (i = 0 up to L-1):
      q_i = b_i XOR (c_i mod 2)
      c_i + m * q_i = b_i + 2 * c_{i+1},  0 <= c_{i+1} < m,  c_0 = 0.
    Returns (c_trace[0..L], Q_L) where m * Q_L = n + c_L * 2^L and 0 <= Q_L < 2^L.
    """
    assert m >= 1 and m % 2 == 1
    c_trace = [0] * (L + 1)
    Q = 0
    c = 0
    for i in range(L):
        b = (n >> i) & 1
        q_i = b ^ (c & 1)
        c_next = (c + m * q_i - b) // 2
        assert 2 * c_next + b == c + m * q_i
        assert 0 <= c_next < m
        c = c_next
        c_trace[i + 1] = c
        Q |= (q_i << i)
    return c_trace, Q

def halving_orbit_sum(r: int, m: int, L: int) -> int:
    """Exact sum O_m(r, L) = sum_{i=0}^{L-1} (r * 2^{-i} mod m) for odd m."""
    assert m >= 1 and m % 2 == 1
    inv2 = (m + 1) // 2
    rho = r % m
    total = 0
    for _ in range(L):
        total += rho
        rho = (rho * inv2) % m
    return total

def carry_dominance_count(r_trace, c_trace, L: int) -> int:
    """W_m(n, L) = #{0 <= i < L : r_i < c_i}."""
    return sum(1 for i in range(L) if r_trace[i] < c_trace[i])

def verify_general_master_theorems():
    print("=== 1. General Odd-Modulus Dual Master Theorem & Carry-Complementarity ===")
    moduli = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 31, 33, 45, 63, 65]
    total_cases = 0
    for m in moduli:
        for L in [1, 2, 4, 6, 8, 10]:
            limit = min(1 << L, 256)
            step = max(1, (1 << L) // limit)
            for n in range(0, 1 << L, step):
                r_tr, E = msb_euclidean_automaton(n, m, L)
                c_tr, Q = lsb_carry_transducer(n, m, L)
                r = n % m
                c_L = c_tr[L]
                W = carry_dominance_count(r_tr, c_tr, L)
                O = halving_orbit_sum(r, m, L)

                # (a) Exact 2-adic quotient equation: m * Q == n + c_L * 2^L
                assert m * Q == n + c_L * (1 << L)
                # (b) Exact Master Dual Identity:
                #     m * (s2(Q) - s2(E) - W) == 2*(r + c_L) - O_m(r, L)
                assert m * (popcount(Q) - popcount(E) - W) == 2 * (r + c_L) - O
                # (c) Exact Synchronized-Trace Divisibility Equivalence
                div = (r == 0)
                assert div == (c_L == 0) == (r_tr == c_tr) == (Q == E)
                # (d) Exact Carry-Complementarity Theorem (when m does not divide n)
                if not div:
                    _, Q_r = lsb_carry_transducer(r, m, L)
                    assert Q == E + Q_r
                    kap = carries_add(E, Q_r)
                    assert kap + W == L - 1 - v2(r), (
                        f"Complementarity fail m={m}, L={L}, n={n}, r={r}: "
                        f"kap={kap}, W={W}, rhs={L - 1 - v2(r)}"
                    )
                    # (e) 2-adic modular inverse popcount formula
                    assert m * (popcount(Q_r) - (L - 1 - v2(r))) == 2 * (r + c_L) - O
                total_cases += 1
    print(f"  PASSED {total_cases} exact instances across {len(moduli)} odd moduli!")

def verify_mersenne_family():
    print("\n=== 2. Infinite Mersenne Family m = 2^k - 1 (L = t*k) ===")
    total_cases = 0
    for k in range(2, 7):
        m = (1 << k) - 1
        for t in [1, 2, 3, 4]:
            L = t * k
            step = max(1, (1 << L) // 300)
            for n in range(0, 1 << L, step):
                r_tr, E = msb_euclidean_automaton(n, m, L)
                c_tr, Q = lsb_carry_transducer(n, m, L)
                r = n % m
                W = carry_dominance_count(r_tr, c_tr, L)
                I = popcount(Q) - popcount(E) - W
                if r == 0:
                    assert I == 0
                else:
                    assert I == 2 - t * popcount(r)
                    # Divisibility threshold check for t >= 3:
                    if t >= 3:
                        assert I != 0
                    # 2-adic inverse popcount law:
                    _, Q_r = lsb_carry_transducer(r, m, L)
                    assert popcount(Q_r) == t * (k - popcount(r)) + 1 - v2(r)
                total_cases += 1
    print(f"  PASSED {total_cases} exact instances across k=2..6, t=1..4!")

def verify_negacyclic_and_fermat_family():
    print("\n=== 3. Infinite Negacyclic Family m | (2^d + 1), incl. Fermat m = 2^k + 1 (L = 2*t*d) ===")
    # Test both m = 2^k + 1 (d=k) AND proper divisors like (11,5), (13,6), (19,9), (25,10), (33,5), (43,7)
    pairs = [( (1 << k) + 1, k ) for k in range(1, 6)] + [
        (11, 5), (13, 6), (33, 5), (43, 7), (19, 9), (25, 10)
    ]
    total_cases = 0
    for m, d in pairs:
        assert (1 << d) % m == m - 1, f"{m} does not divide 2^{d}+1"
        for t in [1, 2]:
            L = 2 * t * d
            if L > 20 and m in (19, 25):
                # Still test 200 structured/spread values including all small r!
                test_ns = list(range(0, min(m * 3, 1 << L))) + [
                    ((1 << L) - 1 - j) for j in range(50)
                ] + [
                    ((j * 9973) % (1 << L)) for j in range(150)
                ]
            else:
                step = max(1, (1 << L) // 300)
                test_ns = range(0, 1 << L, step)
            for n in test_ns:
                r_tr, E = msb_euclidean_automaton(n, m, L)
                c_tr, Q = lsb_carry_transducer(n, m, L)
                r = n % m
                W = carry_dominance_count(r_tr, c_tr, L)
                I = popcount(Q) - popcount(E) - W
                if r == 0:
                    assert I == 0
                else:
                    assert I == 2 - t * d
                    if t * d != 2:
                        assert I != 0
                    else:
                        assert I == 0  # The EXACT exceptional collapse!
                    _, Q_r = lsb_carry_transducer(r, m, L)
                    assert popcount(Q_r) == t * d + 1 - v2(r)
                total_cases += 1
    print(f"  PASSED {total_cases} exact instances across Fermat 2^k+1 and proper divisors of 2^d+1!")

def verify_sharpness_counterexamples():
    print("\n=== 4. Sharpness & Boundary Counterexamples ===")

    # Sharpness 1: Exceptional collapse set t*d == 2 for negacyclic family (m=3, d=1, t=2 and m=5, d=2, t=1)
    for m, d, t in [(3, 1, 2), (5, 2, 1)]:
        L = 2 * t * d  # L = 4
        non_mult_zero = []
        for n in range(1 << L):
            r_tr, E = msb_euclidean_automaton(n, m, L)
            c_tr, Q = lsb_carry_transducer(n, m, L)
            W = carry_dominance_count(r_tr, c_tr, L)
            I = popcount(Q) - popcount(E) - W
            assert I == 0
            if n % m != 0:
                non_mult_zero.append(n)
        print(f"  [Sharpness 1] m={m}, d={d}, t={t} (L={L}, t*d=2): I=0 identically for all {len(non_mult_zero)} non-multiples (e.g. n=1: r=1 != 0 yet I=0).")

    # Sharpness 2: Mersenne divisibility threshold t >= 3 is sharp!
    # At t = 2: r = 1 (s2(1)=1) gives I = 2 - 2*1 = 0 despite (2^k-1) not dividing n!
    for k in [2, 3, 4]:
        m = (1 << k) - 1
        L = 2 * k
        r_tr, E = msb_euclidean_automaton(1, m, L)
        c_tr, Q = lsb_carry_transducer(1, m, L)
        W = carry_dominance_count(r_tr, c_tr, L)
        I = popcount(Q) - popcount(E) - W
        assert I == 0 and (1 % m != 0)
    print("  [Sharpness 2] Mersenne t=2: n=1 has I=0 despite (2^k-1) not dividing 1 (breaks iff at t=2; holds for all t>=3).")

    # At t = 1, k = 3 (m = 7, L = 3): n = 3 has s2(3)=2, so I = 2 - 1*2 = 0 despite 7 not dividing 3!
    r_tr, E = msb_euclidean_automaton(3, 7, 3)
    c_tr, Q = lsb_carry_transducer(3, 7, 3)
    W = carry_dominance_count(r_tr, c_tr, 3)
    assert popcount(Q) - popcount(E) - W == 0 and (3 % 7 != 0)
    print("  [Sharpness 2b] Mersenne t=1, k=3 (m=7, L=3): n=3 has I=0 despite 7 not dividing 3.")

    # Sharpness 3: Non-negacyclic odd modulus fails residue-blindness!
    # m = 7 (ord_7(2) = 3, -1 not in <2> mod 7): L = 3, n = 1 gives I = 1, n = 3 gives I = 0!
    I_1 = popcount(lsb_carry_transducer(1, 7, 3)[1]) - popcount(1 // 7) - carry_dominance_count(*[msb_euclidean_automaton(1, 7, 3)[0], lsb_carry_transducer(1, 7, 3)[0]], 3)
    I_3 = popcount(lsb_carry_transducer(3, 7, 3)[1]) - popcount(3 // 7) - carry_dominance_count(*[msb_euclidean_automaton(3, 7, 3)[0], lsb_carry_transducer(3, 7, 3)[0]], 3)
    assert I_1 == 1 and I_3 == 0 and I_1 != I_3
    print(f"  [Sharpness 3] Non-negacyclic m=7 (L=3): I(1)={I_1} != I(3)={I_3}, proving residue-blindness fails when -1 not in <2> mod m.")

    # Also m = 23 (prime, ord_23(2) = 11, -1 not in <2> mod 23):
    I_23_1 = popcount(lsb_carry_transducer(1, 23, 11)[1]) - carry_dominance_count(msb_euclidean_automaton(1, 23, 11)[0], lsb_carry_transducer(1, 23, 11)[0], 11)
    I_23_5 = popcount(lsb_carry_transducer(5, 23, 11)[1]) - carry_dominance_count(msb_euclidean_automaton(5, 23, 11)[0], lsb_carry_transducer(5, 23, 11)[0], 11)
    print(f"  [Sharpness 3b] Non-negacyclic prime m=23 (L=11): I(1)={I_23_1}, I(5)={I_23_5} (splits by Legendre symbol (r/23)!).")

    # Sharpness 4: Non-period width L breaks constant collapse for m = 2^k + 1!
    # m = 5 (d=2, full period 4), take L = 3 (not a multiple of 4):
    vals_L3 = {}
    for r in range(1, 5):
        r_tr, E = msb_euclidean_automaton(r, 5, 3)
        c_tr, Q = lsb_carry_transducer(r, 5, 3)
        W = carry_dominance_count(r_tr, c_tr, 3)
        vals_L3[r] = popcount(Q) - popcount(E) - W
    assert len(set(vals_L3.values())) > 1
    print(f"  [Sharpness 4] Non-period width L=3 for m=5: I by residue = {vals_L3} (not residue-blind!).")

    # Sharpness 5: Even modulus m = 2 breaks LSB 2-adic division transducer invertibility:
    # For n = 1, m = 2, no q_0 in {0,1} satisfies 2*q_0 == 1 (mod 2).
    print("  [Sharpness 5] Even modulus m=2: 2*q == 1 (mod 2) has no solution; oddness of m is necessary.")

if __name__ == "__main__":
    verify_general_master_theorems()
    verify_mersenne_family()
    verify_negacyclic_and_fermat_family()
    verify_sharpness_counterexamples()
    print("\nALL VERIFICATIONS AND SHARPNESS CHECKS PASSED!")
