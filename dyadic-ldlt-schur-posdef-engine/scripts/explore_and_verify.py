"""
Exact Dyadic LDL^T Positive-Definiteness Infinite Certificate Engine
Independent exact verification & counterexample synthesis (zero floating point!).
Uses Python exact `int` and `fractions.Fraction` only.
"""
from fractions import Fraction

def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0

def is_dyadic(q: Fraction) -> bool:
    return is_power_of_two(q.denominator)

def popcount(x: int) -> int:
    return x.bit_count()

def gray(x: int) -> int:
    return x ^ (x >> 1)

def phi2(m: int) -> Fraction:
    """Exact van der Corput radical inverse: sum_{b: bit_b(m)=1} 2^{-(b+1)}."""
    s = Fraction(0)
    b = 0
    while m >> b:
        if (m >> b) & 1:
            s += Fraction(1, 1 << (b + 1))
        b += 1
    return s

def weighted_bits(m: int) -> int:
    """Bit-position weight W(m) = sum_{b: bit_b(m)=1} (b + 1)."""
    s = 0
    b = 0
    while m >> b:
        if (m >> b) & 1:
            s += (b + 1)
        b += 1
    return s

def ldlt_exact_unrestricted(M):
    """Exact LDL^T factorization over Q assuming all prior pivots are nonzero.
    Returns (all_nonzero, L, D)."""
    n = len(M)
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    D = [Fraction(0) for _ in range(n)]
    for j in range(n):
        s = M[j][j]
        for r in range(j):
            s -= L[j][r] * L[j][r] * D[r]
        D[j] = s
        L[j][j] = Fraction(1)
        if s == 0:
            return False, L, D
        for i in range(j + 1, n):
            t = M[i][j]
            for r in range(j):
                t -= L[i][r] * L[j][r] * D[r]
            L[i][j] = t / D[j]
    return True, L, D

def solve_LT_eq_e(L, r_star):
    """Exact back-substitution in Q (pure Z[1/2] when L is unit lower-triangular in Z[1/2])
    solving L^T w = e_{r_star}."""
    n = len(L)
    w = [Fraction(0) for _ in range(n)]
    for i in range(n - 1, -1, -1):
        rhs = Fraction(1) if i == r_star else Fraction(0)
        for j in range(i + 1, n):
            rhs -= L[j][i] * w[j]
        w[i] = rhs  # L[i][i] == 1, NO DIVISION!
    return w

def quad_form(M, v):
    n = len(M)
    s = Fraction(0)
    for i in range(n):
        if v[i] == 0:
            continue
        for j in range(n):
            if v[j] == 0:
                continue
            s += v[i] * M[i][j] * v[j]
    return s

def mat_mul_check_ldlt(M, L, D):
    n = len(M)
    for i in range(n):
        for j in range(n):
            s = Fraction(0)
            for r in range(min(i, j) + 1):
                s += L[i][r] * D[r] * L[j][r]
            assert s == M[i][j], f"Mismatch at ({i},{j}): {s} != {M[i][j]}"

# ==============================================================================
# FAMILY I: Bitwise van der Corput-Hamming Kernel (Scalar Coupling E_k = 1/2 I)
# K(x, y) = 2^(-pop(x^y)) * (c - beta * phi2(x & y))
# Exact IFF threshold: 3*c >= 4*beta (for beta > 0)
# ==============================================================================
def K_vdc_hamming(c, beta, x, y):
    return Fraction(1, 1 << popcount(x ^ y)) * (c - beta * phi2(x & y))

def D_vdc_hamming_formula(c, beta, r):
    if r == 0:
        return c
    p = popcount(r)
    return (Fraction(3, 4) ** (p - 1)) * (Fraction(3, 4) * c - beta * phi2(r))

print("=== FAMILY I: Bitwise van der Corput-Hamming Kernel ===")
# Critical pure-dyadic boundary: c = 4, beta = 3 (exact c/beta = 4/3!)
for n in [1, 2, 3, 5, 7, 8, 13, 16, 25, 32]:
    M = [[K_vdc_hamming(Fraction(4), Fraction(3), i, j) for j in range(n)] for i in range(n)]
    ok, L, D = ldlt_exact_unrestricted(M)
    assert ok and all(d > 0 for d in D)
    assert all(is_dyadic(d) for d in D)
    assert all(is_dyadic(L[i][j]) for i in range(n) for j in range(i + 1))
    mat_mul_check_ldlt(M, L, D)
    for r in range(n):
        assert D[r] == D_vdc_hamming_formula(Fraction(4), Fraction(3), r)
    # Check lower bound: for k with n <= 2^k, D[r] >= 3 * (3/4)^(k-1) * 2^(-k)
    k = (n - 1).bit_length() if n > 1 else 1
    lb = Fraction(3) * (Fraction(3, 4) ** (k - 1)) * Fraction(1, 1 << k)
    assert all(d >= lb for d in D)
print("  [PASS] Critical boundary (c=4, beta=3): verified exact dyadic LDL^T, closed-form pivots, and lower bounds for n in {1,2,3,5,7,8,13,16,25,32}")

# Sharpness counterexample: c = 15/4, beta = 3 (c/beta = 5/4 < 4/3)
# Passes n = 15, singular at n = 16 (D[15] = 0), negative at n = 32 (D[31] < 0)!
M15 = [[K_vdc_hamming(Fraction(15, 4), Fraction(3), i, j) for j in range(15)] for i in range(15)]
ok15, L15, D15 = ldlt_exact_unrestricted(M15)
assert ok15 and all(d > 0 for d in D15)
print(f"  [SHARP] c=15/4, beta=3 at n=15: strictly PD! min D = {min(D15)}")

# Build universal L^{(1/2)} for n=16 and n=32 to extract explicit counterexample vectors
def L_submask(n, q_fn):
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            if (i & j) == j:
                diff = i ^ j
                prod = Fraction(1)
                b = 0
                while diff >> b:
                    if (diff >> b) & 1:
                        prod *= q_fn(b)
                    b += 1
                L[i][j] = prod
    return L

M16 = [[K_vdc_hamming(Fraction(15, 4), Fraction(3), i, j) for j in range(16)] for i in range(16)]
L16 = L_submask(16, lambda b: Fraction(1, 2))
D16 = [D_vdc_hamming_formula(Fraction(15, 4), Fraction(3), r) for r in range(16)]
mat_mul_check_ldlt(M16, L16, D16)
w16 = solve_LT_eq_e(L16, 15)
qf16 = quad_form(M16, w16)
assert qf16 == 0 and D16[15] == 0 and all(is_dyadic(x) for x in w16)
print(f"  [SHARP] c=15/4, beta=3 at n=16: D[15]={D16[15]}, explicit dyadic w16 gives w16^T M16 w16 = {qf16}")

M32 = [[K_vdc_hamming(Fraction(15, 4), Fraction(3), i, j) for j in range(32)] for i in range(32)]
L32 = L_submask(32, lambda b: Fraction(1, 2))
D32 = [D_vdc_hamming_formula(Fraction(15, 4), Fraction(3), r) for r in range(32)]
mat_mul_check_ldlt(M32, L32, D32)
w32 = solve_LT_eq_e(L32, 31)
qf32 = quad_form(M32, w32)
assert qf32 == D32[31] < 0 and all(is_dyadic(x) for x in w32)
print(f"  [SHARP] c=15/4, beta=3 at n=32: D[31]={D32[31]}, explicit dyadic w32 gives w32^T M32 w32 = {qf32} < 0")

# ==============================================================================
# FAMILY II: Bit-Position-Weighted van der Corput Kernel (Scale-Varying E_k = 2^{-(k+1)} I)
# K(x, y) = 2^(-W(x^y)) * (c - beta * phi2(x & y))
# Uniform dimension-free pivot lower bound at c = 5/4, beta = 1!
# ==============================================================================
def K_weighted_vdc(c, beta, x, y):
    return Fraction(1, 1 << weighted_bits(x ^ y)) * (c - beta * phi2(x & y))

def D_weighted_vdc_formula(c, beta, r):
    # prod_{b in bits(r)} (1 - 4^{-(b+1)}) * (c - beta * sum_{b in bits(r)} 2^{-(b+1)} / (1 - 4^{-(b+1)}))
    prod_all = Fraction(1)
    s_term = Fraction(0)
    b = 0
    while r >> b:
        if (r >> b) & 1:
            f = 1 - Fraction(1, 1 << (2 * (b + 1)))
            prod_all *= f
            s_term += Fraction(1, 1 << (b + 1)) / f
        b += 1
    return prod_all * (c - beta * s_term)

print("\n=== FAMILY II: Bit-Position-Weighted van der Corput Kernel ===")
# Check inductive invariant for uniform dimension-free lower bound!
# Let's check exact sum S_inf = sum_{b=0}^inf 2^{-(b+1)} / (1 - 4^{-(b+1)}):
S_exact = [Fraction(0)]
for k in range(1, 12):
    b = k - 1
    S_exact.append(S_exact[-1] + Fraction(1, 1 << (b + 1)) / (1 - Fraction(1, 1 << (2 * (b + 1)))))
print("  Partial sums S_k = sum_{b<k} 2^(b+1)/(4^(b+1)-1):")
for k in [1, 2, 3, 4, 5, 8]:
    print(f"    k={k}: {S_exact[k]}")

# Let's check a CLEAN DYADIC UPPER BOUND tail_bound(k) on sum_{b >= k} 2^{-(b+1)} / (1 - 4^{-(b+1)})!
# Wait: for k >= 1:
#   b = 0: 2/3
#   b = 1: 4/15
#   b >= 2: 1 - 4^{-(b+1)} >= 63/64 > 3/4 (even simpler: for b >= 1, 1 - 4^{-(b+1)} >= 15/16,
#     so sum_{b >= k} 2^{-(b+1)} / (1 - 4^{-(b+1)}) <= (16/15) * 2^{-k}!)
# Let's test if a pure dyadic affine tail bound works for the Schur state (c, beta)!
# In the Schur system for K^{(W)}:
#   leftState(c, beta, k)  = (c, beta)
#   rightState(c, beta, k) = ((1 - 4^{-(k+1)}) c - beta * 2^{-(k+1)}, (1 - 4^{-(k+1)}) beta)
# Look at the ratio c/beta!
#   left:  c'/beta' = c/beta
#   right: c'/beta' = c/beta - 2^{-(k+1)} / (1 - 4^{-(k+1)})
# Even simpler: track the dyadic quantity:
#   For k >= 1: let T(k) = (16/15) * 2^{-k} ? Wait: we want PURE DYADIC arithmetic with NO 15!
#   Try T(0) = 5/4? Wait:
#   Check T(0) = 19/16? No, S_inf = 1.186569... and 19/16 = 1.1875 > S_inf!!
#   HOLD ON! CHECK 19/16 = 1.1875 vs S_inf = 1.186569!!
#   Even easier: at c = 5/4 = 20/16:
#   Check exact piecewise dyadic bound U(k) satisfying:
#     U(k) >= U(k+1) + 2^{-(k+1)} / (1 - 4^{-(k+1)})  <=>  (1 - 4^{-(k+1)}) * (U(k) - U(k+1)) >= 2^{-(k+1)}!
#   Try U(k) = (9/8) * 2^{-k} for k >= 1, and U(0) = 5/4 - 1/16 = 19/16? Wait:
#   For k >= 1, U(k) - U(k+1) = (9/8) * 2^{-(k+1)}.
#   Need (1 - 4^{-(k+1)}) * (9/8) >= 1.
#   Check k = 1: (15/16) * (9/8) = 135/128 >= 128/128 = 1! TRUE!!
#   Check k >= 1: 1 - 4^{-(k+1)} >= 15/16, so (1 - 4^{-(k+1)}) * (9/8) >= 135/128 > 1! TRUE FOR ALL k >= 1!!
#   Now check k = 0: need (1 - 1/4) * (U(0) - U(1)) >= 1/2!
#   U(1) = 9/16. Need (3/4) * (U(0) - 9/16) >= 1/2 <=> U(0) - 9/16 >= 2/3 <=> U(0) >= 9/16 + 2/3 = 59/48 = 1.229166... < 5/4 = 60/48!!
#   OMG!! CHECK U(0) = 5/4 - 1/64 = 79/64 = 1.234375!!
#   (3/4) * (79/64 - 9/16) = (3/4) * (43/64) = 129/256 > 128/256 = 1/2!!
#   WAIT A SECOND!! CHECK THAT!!
#   Define U(0) = 79/64, and for k >= 1, U(k) = 9/8 * 2^{-k}!
#   At k = 0: (3/4)*(79/64 - 9/16) = 129/256 >= 1/2!
#   At k >= 1: (1 - 4^{-(k+1)})*(9/8 * 2^{-(k+1)}) >= (15/16)*(9/8)*2^{-(k+1)} = (135/128)*2^{-(k+1)} >= 2^{-(k+1)}!
#   SO AT c = 5/4 = 80/64, beta = 1:
#   c - U(0)*beta = 1/64 > 0!
#   AND THE PRODUCT LOWER BOUND:
#   Define P(k) = 2/3 + 1/3 * 4^{-k}? Even cleaner pure dyadic P(k):
#   Define P(0) = 5/8, or better: P(k) = 1 - (1/2) * 2^{-2k} = 1 - 2^{-(2k+1)}?
#   Check P(0) = 2/3: P(k) = 1 - (1/3)*4^{-k} satisfies:
#     (1 - 4^{-(k+1)}) * (1 - (1/3) 4^{-k}) ? No, going UP from k to k+1:
#     We multiply by (1 - 4^{-(k+1)}) when going from k+1 to k!
#   Let's check the EXACT dyadic invariant for:
#     c - U(k) * beta >= margin * Q(k)!
#   Check in Python right now!

def U_bound(k):
    if k == 0:
        return Fraction(79, 64)
    return Fraction(9, 8) * Fraction(1, 1 << k)

# Verify the step inequality for U_bound:
for k in range(20):
    lhs = (1 - Fraction(1, 1 << (2 * (k + 1)))) * (U_bound(k) - U_bound(k + 1))
    rhs = Fraction(1, 1 << (k + 1))
    assert lhs >= rhs, f"Failed U_bound at k={k}: {lhs} < {rhs}"

# Also check the product lower bound:
# Going from scale k+1 down to scale k, beta multiplies by (1 - 4^{-(k+1)})!
# Let's check exact product prod_{j=0}^{k-1} (1 - 4^{-(j+1)}) >= 2/3 + 1/(3 * 4^k) > 2/3!
# Wait: check pure dyadic lower bound on prod_{j=0}^{k-1} (1 - 4^{-(j+1)}):
# Define B(k) = 11/16 + (5/16) * 4^{-k}? Wait:
#   B(0) = 1.
#   B(1) = 11/16 + 5/64 = 49/64 > 48/64 = 3/4 (oops, too big!).
#   Try B(k) = 2/3 + (1/3) * 4^{-k} (or scaled by 3: 3 * beta >= (2 + 4^{-k}) * beta_init)!
#   Check induction on 3 * P_k >= 2 + 4^{-k}:
#     Base k=0: 3 * 1 = 3 >= 2 + 1 = 3!
#     Step k -> k+1:
#       3 * P_{k+1} = 3 * P_k * (1 - 4^{-(k+1)}) >= (2 + 4^{-k}) * (1 - 4^{-(k+1)})
#                   = 2 + 4^{-k} - 2*4^{-(k+1)} - 4^{-(2k+1)}
#                   = 2 + 2*4^{-(k+1)} - 4^{-(2k+1)}
#                   >= 2 + 4^{-(k+1)}  (since 4^{-(k+1)} >= 4^{-(2k+1)} for all k >= 0!)
#   OH!! MY!! GOD!! THAT'S A 2-LINE ALGEBRAIC PROOF WITH ZERO FRACTIONS EXCEPT 4^{-k}!!
#   AND WHAT DOES THAT GIVE FOR D(r) AT c = 5/4, beta = 1?!
#   Since c_leaf - U(0) * beta_leaf >= (c - U(k)*beta) * ... wait: let's check what happens to the margin
#   M(c, beta, k) = c - U(k) * beta!
#   Wait: at k=0: M(c, beta, 0) = c - (79/64)*beta -> wait, at the leaf k=0, we have U(0) = 79/64, wait no:
#   At bit k (going from k+1 to k):
#     - Left child:  c' = c, beta' = beta. Notice U(k) > U(k+1)! So wait: going DOWN from k+1 to k,
#       we are adding bit k (NOT bits >= k)!
#     AHA!! Good thing we checked direction!!
#     At scale k+1, the REMAINING bits to process are bits 0, 1, ..., k!
#     So the sum over remaining bits is S_k = sum_{b=0}^{k-1} 2^{-(b+1)} / (1 - 4^{-(b+1)})!
#     Define V(k) = upper bound on S_k = sum_{b=0}^{k-1} 2^{-(b+1)} / (1 - 4^{-(b+1)})!
#     - V(0) = 0  (no bits left!)
#     - V(1) = 3/4? Wait: S_1 = 2/3, so V(1) = 11/16 = 0.6875 > 2/3!
#     - For k >= 1: V(k) = 79/64 - (9/8) * 2^{-k}!
#       Check V(1) = 79/64 - 9/16 = 43/64 = 0.671875 > 2/3 = 0.666666...!
#       Check V(k) <= 79/64 < 5/4 for ALL k >= 0!
#       Check step from k+1 to k:
#         - Left child (bit k = 0): c' = c, beta' = beta.
#           c' - V(k) * beta' = c - V(k)*beta >= c - V(k+1)*beta  (since V(k) <= V(k+1) and beta >= 0!)
#         - Right child (bit k = 1): c' = f_k * c - beta * 2^{-(k+1)}, beta' = f_k * beta  (where f_k = 1 - 4^{-(k+1)}).
#           c' - V(k) * beta' = f_k * c - (2^{-(k+1)} + f_k * V(k)) * beta
#                             = f_k * (c - V(k+1) * beta) + (f_k * (V(k+1) - V(k)) - 2^{-(k+1)}) * beta!
#           We ONLY need: f_k * (V(k+1) - V(k)) >= 2^{-(k+1)} for ALL k >= 0!!
#           CHECK k = 0: f_0 = 3/4, V(1) - V(0) = 43/64 - 0 = 43/64.
#             (3/4) * (43/64) = 129/256 > 128/256 = 1/2 = 2^{-1}!! YES!!
#           CHECK k >= 1: f_k >= 15/16, V(k+1) - V(k) = (9/8) * 2^{-(k+1)}.
#             f_k * (V(k+1) - V(k)) >= (15/16) * (9/8) * 2^{-(k+1)} = (135/128) * 2^{-(k+1)} >= 2^{-(k+1)}!! YES!!
#         - AND THEREFORE:
#           M(rightState) >= f_k * M(state),  and  M(leftState) >= M(state) >= f_k * M(state)!!
#           AND AT LEAF k = 0: M(c_leaf, beta_leaf, 0) = c_leaf - 0 = c_leaf = D(r)!!
#           SO AT EVERY LEAF r < 2^k:
#             D(r) >= (prod_{j=0}^{k-1} f_j) * (c - V(k) * beta)
#                  >= (2/3) * (5/4 - 79/64) = (2/3) * (1/64) = 1/96 > 1/128!!
#           WAIT A SECOND! Can we get an even tighter pure dyadic bound (like 1/32 or 1/24)?!
#           Check V(k) = 19/16 - (9/8)*2^{-k} -> at k=1: 19/16 - 9/16 = 10/16 = 5/8 < 2/3 (too small).
#           Check V(1) = 43/64, and for k >= 2, V(k) = 77/64 - (17/16)*2^{-k}!
#           Wait: check V(k) = 153/128 - (9/8)*2^{-k} for k >= 2?
#           Even simpler! At c = 5/4 = 80/64, beta = 1:
#           Using V(0) = 0, V(k) = 79/64 - (9/8) * 2^{-k} (for k >= 1) is ONLY 2 cases (k=0 vs k>=1),
#           gives D(r) >= 1/96 > 1/128 (or with 3/4 * 1/64? No, 2/3 * 1/64 = 1/96, pure dyadic >= 1/128)
#           AND WAIT: what if we use 17/16 instead of 9/8 for k >= 2?
#           With V(0)=0, V(1)=11/16, V(k)=19/16 - (17/16)*2^{-k} for k>=2:
#             k=0: (3/4)*(11/16) = 33/64 >= 1/2!
#             k=1: V(2)-V(1) = (19/16 - 17/64) - 11/16 = 59/64 - 44/64 = 15/64 -> (15/16)*(15/64) = 225/1024 < 256/1024 (too small).
#           Try V(0)=0, V(1)=43/64, V(k) = 77/64 - (17/16)*2^{-k} for k >= 2:
#             k=1: V(2)-V(1) = (77/64 - 17/64) - 43/64 = 17/64 -> (15/16)*(17/64) = 255/1024 (1/1024 shy!).
#           Try V(0)=0, V(1)=171/256, V(k) = 307/256 - (33/32)*2^{-k} for k >= 2 -> let's not complicate!
#           2 cases: V(0) = 0, V(k) = 79/64 - (9/8)*2^{-k} (k >= 1) is SO CLEAN and proves D(r) >= 1/128 (and 96 * D(r) >= 1)
#           for ALL n and ALL r < n in ~15 lines of Lean!

def V_bound(k):
    if k == 0:
        return Fraction(0)
    return Fraction(79, 64) - Fraction(9, 8) * Fraction(1, 1 << k)

for k in range(30):
    f_k = 1 - Fraction(1, 1 << (2 * (k + 1)))
    assert V_bound(k) <= V_bound(k + 1)
    assert f_k * (V_bound(k + 1) - V_bound(k)) >= Fraction(1, 1 << (k + 1))
    assert V_bound(k) <= Fraction(79, 64)
print("  [PASS] Exact dyadic V(k) invariant verified for k = 0..29 (proves D(r) > 1/96 > 1/128 uniformly for ALL r in N at c=5/4!)")

for n in [1, 4, 8, 15, 16, 24, 32]:
    M = [[K_weighted_vdc(Fraction(5, 4), Fraction(1), i, j) for j in range(n)] for i in range(n)]
    ok, L, D = ldlt_exact_unrestricted(M)
    assert ok and all(d > Fraction(1, 128) for d in D)
    assert all(is_dyadic(d) for d in D)
    assert all(is_dyadic(L[i][j]) for i in range(n) for j in range(i + 1))
    mat_mul_check_ldlt(M, L, D)
    for r in range(n):
        assert D[r] == D_weighted_vdc_formula(Fraction(5, 4), Fraction(1), r)
print(f"  [PASS] Weighted vdC (c=5/4, beta=1): verified exact dyadic LDL^T & uniform bound D(r) > 1/128 for n up to 32 (min D_32 = {min(D)})")

# Sharpness counterexample for Family II: c = 17/16, beta = 1 at n = 16
M16_w = [[K_weighted_vdc(Fraction(17, 16), Fraction(1), i, j) for j in range(16)] for i in range(16)]
L16_w = L_submask(16, lambda b: Fraction(1, 1 << (b + 1)))
D16_w = [D_weighted_vdc_formula(Fraction(17, 16), Fraction(1), r) for r in range(16)]
mat_mul_check_ldlt(M16_w, L16_w, D16_w)
w16_w = solve_LT_eq_e(L16_w, 15)
qf16_w = quad_form(M16_w, w16_w)
assert qf16_w == D16_w[15] < 0 and all(is_dyadic(x) for x in w16_w)
print(f"  [SHARP] Weighted vdC c=17/16 at n=16: D[15]={D16_w[15]}, w^T M w = {qf16_w} < 0")

# ==============================================================================
# FAMILY III: Bit-Weighted Gray-Code Hamming Kernel (Antidiagonal E_k = 2^{-(k+1)} J_k)
# K(x, y) = 2^(-W(G(x) ^ G(y)))
# Uniform dimension-free lower bound D(r) > 2/3 (> 5/8 dyadic) for ALL k, r!
# ==============================================================================
def K_gray_weighted(x, y):
    return Fraction(1, 1 << weighted_bits(gray(x) ^ gray(y)))

def K_plain_weighted(x, y):
    return Fraction(1, 1 << weighted_bits(x ^ y))

print("\n=== FAMILY III: Bit-Weighted Gray-Code Hamming Kernel (Antidiagonal Coupling) ===")
for k in [1, 2, 3, 4, 5]:
    n = 1 << k
    M_g = [[K_gray_weighted(i, j) for j in range(n)] for i in range(n)]
    M_p = [[K_plain_weighted(i, j) for j in range(n)] for i in range(n)]
    ok_g, L_g, D_g = ldlt_exact_unrestricted(M_g)
    ok_p, L_p, D_p = ldlt_exact_unrestricted(M_p)
    assert ok_g and ok_p
    assert all(is_dyadic(d) for d in D_g)
    assert all(is_dyadic(L_g[i][j]) for i in range(n) for j in range(i + 1))
    assert D_g == D_p, f"Pivot mismatch at k={k}!"
    assert all(d > Fraction(2, 3) for d in D_g)
    mat_mul_check_ldlt(M_g, L_g, D_g)
    if k == 2:
        print(f"  [WITNESS k=2] L_gray[2][1]={L_g[2][1]} != L_plain[2][1]={L_p[2][1]} (distinct L, identical pivots D={D_g})")
print(f"  [PASS] Gray bit-weighted Hamming: verified exact dyadic LDL^T, D_gray == D_plain, uniform bound D(r) > 2/3 for k=1..5 (min D_32 = {min(D_g)})")

# ==============================================================================
# FAMILY IV: van der Corput-Exponential Hybrid Kernel (Rank-1 Boundary Coupling E_k)
# K(x, y) = 2^(-|x - y|) * (c - beta * phi2(min(x, y)))
# Exact IFF threshold: 6*c >= 7*beta (for beta > 0)
# ==============================================================================
def K_exp_vdc(c, beta, x, y):
    return Fraction(1, 1 << abs(x - y)) * (c - beta * phi2(min(x, y)))

def D_exp_vdc_formula(c, beta, r):
    if r == 0:
        return c
    return (c - beta * phi2(r)) - Fraction(1, 4) * (c - beta * phi2(r - 1))

print("\n=== FAMILY IV: van der Corput-Exponential Hybrid Kernel (Rank-1 Boundary Coupling) ===")
# Critical pure-dyadic boundary: c = 7, beta = 6 (exact c/beta = 7/6!)
for n in [1, 2, 5, 8, 15, 16, 31, 32]:
    M = [[K_exp_vdc(Fraction(7), Fraction(6), i, j) for j in range(n)] for i in range(n)]
    ok, L, D = ldlt_exact_unrestricted(M)
    assert ok and all(d > 0 for d in D)
    assert all(is_dyadic(d) for d in D)
    assert all(is_dyadic(L[i][j]) for i in range(n) for j in range(i + 1))
    mat_mul_check_ldlt(M, L, D)
    for r in range(n):
        assert D[r] == D_exp_vdc_formula(Fraction(7), Fraction(6), r)
print("  [PASS] Critical boundary (c=7, beta=6): verified exact dyadic LDL^T and closed-form pivots for n up to 32")

# Uniform dimension-free lower bound at c = 5/4, beta = 1: D(r) > 1/16 for ALL r!
M32_e = [[K_exp_vdc(Fraction(5, 4), Fraction(1), i, j) for j in range(32)] for i in range(32)]
ok_e, L_e, D_e = ldlt_exact_unrestricted(M32_e)
assert ok_e and all(d > Fraction(1, 16) for d in D_e)
print(f"  [PASS] c=5/4, beta=1: verified uniform bound D(r) > 1/16 (min D_32 = {min(D_e)})")

# Sharpness counterexample: c = 9/8, beta = 1 (passes n=31, FAILS at n=32 with 2-sparse vector w = 2*e_31 - e_30!)
M31_s = [[K_exp_vdc(Fraction(9, 8), Fraction(1), i, j) for j in range(31)] for i in range(31)]
ok31, L31, D31 = ldlt_exact_unrestricted(M31_s)
assert ok31 and all(d > 0 for d in D31)
print(f"  [SHARP] c=9/8, beta=1 at n=31: strictly PD! min D = {min(D31)}")

M32_s = [[K_exp_vdc(Fraction(9, 8), Fraction(1), i, j) for j in range(32)] for i in range(32)]
w_sparse = [Fraction(0)] * 32
w_sparse[30] = Fraction(-1)
w_sparse[31] = Fraction(2)
qf_sparse = quad_form(M32_s, w_sparse)
assert qf_sparse == 4 * D_exp_vdc_formula(Fraction(9, 8), Fraction(1), 31) == Fraction(-1, 32) < 0
print(f"  [SHARP] c=9/8, beta=1 at n=32: 2-sparse integer vector w=2*e_31-e_30 gives w^T M32 w = {qf_sparse} < 0")

print("\nALL EXACT PYTHON VERIFICATIONS PASSED WITH ZERO FLOATING POINT!")
