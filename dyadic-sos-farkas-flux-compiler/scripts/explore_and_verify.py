"""
explore_and_verify.py — Exact Z[1/2] Dyadic SOS / Schmüdgen-Farkas / Telescoping-Flux
Certificate Synthesizer, Independent Exact Verifier, Sharpness Counterexample Finder,
and Lean 4 Certificate Exporter for Task 5 (certcomp-5).

Rules honored:
- Floating point (numpy/scipy) is used ONLY as an untrusted search hint to locate
  candidate SDP points inside the PSD cone.
- Every exported certificate, every polynomial identity, every Gram LDL^T factorization,
  every concrete instance check, and every sharpness counterexample is verified 100%
  EXACTLY using Python arbitrary-precision `int` and `fractions.Fraction` with strict
  power-of-2 (Z[1/2]) denominator enforcement.
- CPU-only.
"""
from fractions import Fraction
import itertools
import json
import os
import numpy as np
from scipy.optimize import minimize
import sympy as sp

# ===========================================================================
# Part 1: Exact Z[1/2] Sparse Polynomial & Dyadic Gram Data Model
#         (mirrors the Lean sources 1-to-1)
# ===========================================================================
def mono_mul(m1, m2):
    """Multiply two sorted monomials: tuple of (var_idx, exp)."""
    d = {}
    for v, e in m1:
        d[v] = d.get(v, 0) + e
    for v, e in m2:
        d[v] = d.get(v, 0) + e
    return tuple(sorted((v, e) for v, e in d.items() if e > 0))

def mono_shift_from(k, delta, m):
    return tuple(sorted((v if v < k else v + delta, e) for v, e in m))

def poly_norm(terms):
    """Canonical sorted sparse integer polynomial: list of (mono, int_coeff)."""
    acc = {}
    for m, c in terms:
        if c != 0:
            acc[m] = acc.get(m, 0) + c
    return sorted(((m, c) for m, c in acc.items() if c != 0), key=lambda x: x[0])

def poly_scale(k, p):
    if k == 0:
        return []
    return poly_norm([(m, k * c) for m, c in p])

def poly_add(p, q):
    return poly_norm(list(p) + list(q))

def poly_sub(p, q):
    return poly_norm(list(p) + [(m, -c) for m, c in q])

def poly_mul(p, q):
    out = []
    for m1, c1 in p:
        for m2, c2 in q:
            out.append((mono_mul(m1, m2), c1 * c2))
    return poly_norm(out)

def poly_shift_from(k, delta, p):
    return poly_norm([(mono_shift_from(k, delta, m), c) for m, c in p])

class DyadicPoly:
    """Exact polynomial in Z[1/2][x]: represents 2^(-shift) * poly."""
    def __init__(self, shift, poly):
        assert isinstance(shift, int) and shift >= 0
        self.shift = shift
        self.poly = poly_norm(poly)

    @staticmethod
    def zero():
        return DyadicPoly(0, [])

    @staticmethod
    def const(mant, shift=0):
        return DyadicPoly(shift, [((), mant)] if mant != 0 else [])

    @staticmethod
    def var(v):
        return DyadicPoly(0, [(((v, 1),), 1)])

    def __add__(self, other):
        m = max(self.shift, other.shift)
        p1 = poly_scale(1 << (m - self.shift), self.poly)
        p2 = poly_scale(1 << (m - other.shift), other.poly)
        return DyadicPoly(m, poly_add(p1, p2))

    def __neg__(self):
        return DyadicPoly(self.shift, [(m, -c) for m, c in self.poly])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return DyadicPoly(self.shift + other.shift, poly_mul(self.poly, other.poly))

    def shift_from(self, k, delta):
        return DyadicPoly(self.shift, poly_shift_from(k, delta, self.poly))

    def eq(self, other):
        p1 = poly_scale(1 << other.shift, self.poly)
        p2 = poly_scale(1 << self.shift, other.poly)
        return p1 == p2

    def eval_frac(self, env):
        tot = Fraction(0)
        for m, c in self.poly:
            term = Fraction(c)
            for v, e in m:
                term *= env[v] ** e
            tot += term
        return tot / Fraction(1 << self.shift)

def sympy_to_dpoly(expr, var_map):
    """Convert a SymPy polynomial with dyadic rational coefficients to DyadicPoly."""
    vars_sorted = [v for v, _ in sorted(var_map.items(), key=lambda kv: kv[1])]
    p = sp.Poly(sp.expand(expr), *vars_sorted)
    max_shift = 0
    raw = []
    for mon_exps, coeff in p.terms():
        f = Fraction(int(coeff.p), int(coeff.q))
        den = f.denominator
        assert den & (den - 1) == 0, f"Non-dyadic denominator {den} in {expr}"
        max_shift = max(max_shift, den.bit_length() - 1)
        m = tuple((var_map[vars_sorted[i]], e) for i, e in enumerate(mon_exps) if e > 0)
        raw.append((m, f))
    terms = [(m, int(f * (1 << max_shift))) for m, f in raw]
    return DyadicPoly(max_shift, terms)

class DyadicGram:
    """Pure-data exact dyadic Gram + LDL^T certificate."""
    def __init__(self, basis, shift, G, scale, diag, L):
        self.basis = basis
        self.shift = shift
        self.G = G
        self.scale = scale
        self.diag = diag
        self.L = L

    def check_psd(self):
        r = len(self.basis)
        if len(self.G) != r or any(len(row) != r for row in self.G):
            return False
        if len(self.diag) != len(self.L) or any(len(row) != r for row in self.L):
            return False
        if any(d < 0 for d in self.diag):
            return False
        # Symmetry
        for i in range(r):
            for j in range(r):
                if self.G[i][j] != self.G[j][i]:
                    return False
        # Exact 2^scale * G = L^T * diag(d) * L
        sf = 1 << self.scale
        for i in range(r):
            for j in range(r):
                rhs = sum(self.diag[k] * self.L[k][i] * self.L[k][j] for k in range(len(self.diag)))
                if sf * self.G[i][j] != rhs:
                    return False
        return True

    def to_dpoly(self):
        r = len(self.basis)
        terms = []
        for i in range(r):
            for j in range(r):
                if self.G[i][j] != 0:
                    terms.append((mono_mul(self.basis[i], self.basis[j]), self.G[i][j]))
        return DyadicPoly(self.shift, terms)

def const_gram(mant, shift=0):
    """1x1 constant dyadic Gram representing mant / 2^shift >= 0."""
    assert mant >= 0
    return DyadicGram(basis=[()], shift=shift, G=[[mant]], scale=0, diag=[mant], L=[[1]])

def rank1_gram(basis, coeffs, weight=1, shift=0):
    """Exact rank-1 dyadic Gram representing (weight / 2^shift) * (sum_i coeffs[i] * basis[i])^2."""
    r = len(basis)
    G = [[weight * coeffs[i] * coeffs[j] for j in range(r)] for i in range(r)]
    return DyadicGram(basis=basis, shift=shift, G=G, scale=0, diag=[weight], L=[list(coeffs)])

class FarkasSOSCert:
    """
    Exact Dyadic Schmüdgen-Farkas Positivstellensatz certificate:
      target == mainGram + sum_{(idxs, gram)} gram * prod_{i in idxs} ineqs[i]
                         + sum_{j} eqCofacts[j] * eqs[j]
    """
    def __init__(self, main_gram, ineq_prods, eq_cofacts):
        self.main_gram = main_gram
        self.ineq_prods = ineq_prods   # list of (list_of_ineq_indices, DyadicGram)
        self.eq_cofacts = eq_cofacts   # list of DyadicPoly matching len(eqs)

    def check(self, target, ineqs, eqs):
        if len(self.eq_cofacts) != len(eqs):
            return False
        if not self.main_gram.check_psd():
            return False
        rhs = self.main_gram.to_dpoly()
        for idxs, gram in self.ineq_prods:
            if not gram.check_psd():
                return False
            prod = DyadicPoly.const(1, 0)
            for idx in idxs:
                if idx < 0 or idx >= len(ineqs):
                    return False
                prod = prod * ineqs[idx]
            rhs = rhs + gram.to_dpoly() * prod
        for q, h in zip(self.eq_cofacts, eqs):
            rhs = rhs + q * h
        return target.eq(rhs)

class CyclicFluxCert:
    def __init__(self, flux, sos_cert):
        self.flux = flux
        self.sos_cert = sos_cert

    def check(self, param_count, stencil, local_ineqs, local_eqs):
        shifted = stencil + self.flux - self.flux.shift_from(param_count, 1)
        return self.sos_cert.check(shifted, local_ineqs, local_eqs)

class OpenFluxCert:
    def __init__(self, flux, bulk_cert, left_cert, right_cert):
        self.flux = flux
        self.bulk_cert = bulk_cert
        self.left_cert = left_cert
        self.right_cert = right_cert

    def check(self, param_count, stencil, b_left, b_right, local_ineqs, local_eqs):
        shifted = stencil + self.flux - self.flux.shift_from(param_count, 1)
        ok_bulk = self.bulk_cert.check(shifted, local_ineqs, local_eqs)
        ok_left = self.left_cert.check(b_left - self.flux, local_ineqs, local_eqs)
        ok_right = self.right_cert.check(b_right + self.flux, local_ineqs, local_eqs)
        return ok_bulk and ok_left and ok_right

# ===========================================================================
# Part 2: Pure-Silicon Dyadic Cholesky + Diagonally-Dominant Remainder Engine
# ===========================================================================
def dd_decompose_int(D):
    """Exact zero-denominator SOS decomposition of symmetric diagonally dominant int matrix."""
    r = len(D)
    d_weights, L_rows = [], []
    rem = [D[i][i] for i in range(r)]
    for i in range(r):
        for j in range(i + 1, r):
            val = D[i][j]
            assert val == D[j][i]
            if val != 0:
                av = abs(val)
                row = [0] * r
                row[i] = 1
                row[j] = 1 if val > 0 else -1
                d_weights.append(av)
                L_rows.append(row)
                rem[i] -= av
                rem[j] -= av
    for i in range(r):
        assert rem[i] >= 0
        if rem[i] > 0:
            row = [0] * r
            row[i] = 1
            d_weights.append(rem[i])
            L_rows.append(row)
    return d_weights, L_rows

def dyadic_cholesky_dd(G_int):
    """
    Pure-silicon binary Cholesky + DD remainder:
    Given strictly PD symmetric integer matrix G_int, find minimal b >= 0 such that
      2^(2b) * G_int = L^T * diag(d) * L
    with exact integers, d_k > 0, and ZERO odd denominators.
    """
    r = len(G_int)
    M = np.array(G_int, dtype=float)
    lmin = float(np.linalg.eigvalsh(M)[0])
    assert lmin > 0, f"Not strictly PD: lmin={lmin}"
    for b in range(0, 17):
        for frac in (0.5, 0.7, 0.3, 0.85, 0.15):
            eta = frac * lmin
            try:
                R = np.linalg.cholesky(M - eta * np.eye(r)).T
            except np.linalg.LinAlgError:
                continue
            L_chol = [[int(round(R[i, j] * (1 << b))) for j in range(r)] for i in range(r)]
            scale = 2 * b
            D = [[(1 << scale) * G_int[i][j] - sum(L_chol[k][i] * L_chol[k][j] for k in range(r))
                  for j in range(r)] for i in range(r)]
            if all(D[i][i] >= sum(abs(D[i][j]) for j in range(r) if j != i) for i in range(r)):
                d_dd, L_dd = dd_decompose_int(D)
                diag_all, L_all = [], []
                for row in L_chol:
                    if any(x != 0 for x in row):
                        diag_all.append(1)
                        L_all.append(row)
                diag_all.extend(d_dd)
                L_all.extend(L_dd)
                return scale, diag_all, L_all
    raise RuntimeError("dyadic_cholesky_dd failed")

def poly_from_sympy_frac(expr, vars_list):
    p = sp.Poly(sp.expand(expr), *vars_list)
    return {mon: Fraction(int(c.p), int(c.q)) for mon, c in p.terms()}

def synthesize_quartic_w3_cert(p_expr_fn, cv):
    """Synthesize exact Z[1/2] CyclicFluxCert for a 3-point quartic stencil."""
    a, b, c = sp.symbols('a b c')
    vlist = (a, b, c)
    vmap = {a: 0, b: 1, c: 2}
    basis_sp = [a**2, a*b, b**2, b*c, c**2, a*c]
    basis_m = [((0, 2),), ((0, 1), (1, 1)), ((1, 2),), ((1, 1), (2, 1)), ((2, 2),), ((0, 1), (2, 1))]
    flux_sp = [a**4, a**3*b, a**2*b**2, a*b**3, b**4]
    r = 6

    mon_set = set()
    for m1 in basis_sp:
        for m2 in basis_sp:
            mon_set.update(poly_from_sympy_frac(m1 * m2, vlist).keys())
    all_mons = sorted(mon_set)
    mon_idx = {m: i for i, m in enumerate(all_mons)}
    g_pairs = [(i, j) for i in range(r) for j in range(i, r)]
    n_g, n_f = len(g_pairs), len(flux_sp)

    A_eq = np.zeros((len(all_mons), n_g + n_f))
    A_ex = [[Fraction(0)] * (n_g + n_f) for _ in range(len(all_mons))]
    for col, (i, j) in enumerate(g_pairs):
        dd = poly_from_sympy_frac(basis_sp[i] * basis_sp[j] * (1 if i == j else 2), vlist)
        for m, val in dd.items():
            A_eq[mon_idx[m], col] += float(val)
            A_ex[mon_idx[m]][col] += val
    for k, fm in enumerate(flux_sp):
        fm_s = fm.subs({a: b, b: c}, simultaneous=True)
        dd = poly_from_sympy_frac(-(fm - fm_s), vlist)
        for m, val in dd.items():
            A_eq[mon_idx[m], n_g + k] += float(val)
            A_ex[mon_idx[m]][n_g + k] += val

    p_expr = p_expr_fn(a, b, c, sp.Rational(cv.numerator, cv.denominator))
    d_p = poly_from_sympy_frac(p_expr, vlist)
    b_eq = np.zeros(len(all_mons))
    b_ex = [Fraction(0)] * len(all_mons)
    for m, val in d_p.items():
        b_eq[mon_idx[m]] = float(val)
        b_ex[mon_idx[m]] = val

    # Untrusted float hint via smooth softmin SDP
    U, S, Vt = np.linalg.svd(A_eq)
    rank = int(np.sum(S > 1e-10))
    null_basis = Vt[rank:].T
    x0, _, _, _ = np.linalg.lstsq(A_eq, b_eq, rcond=None)

    def unpack_G(x):
        G = np.zeros((r, r))
        for col, (i, j) in enumerate(g_pairs):
            G[i, j] = G[j, i] = x[col]
        return G

    def smooth_loss(z, beta=60.0):
        x = x0 + null_basis @ z
        eigs = np.linalg.eigvalsh(unpack_G(x))
        m = np.min(eigs)
        softmin = m - np.log(np.sum(np.exp(-beta * (eigs - m)))) / beta
        return -softmin + 1e-5 * np.sum(x**2)

    z = np.zeros(null_basis.shape[1])
    for beta in (10.0, 40.0, 150.0, 500.0):
        res = minimize(lambda zz: smooth_loss(zz, beta), z, method='BFGS', options={'maxiter': 500})
        z = res.x
    x_opt = x0 + null_basis @ z

    # Exact RREF projection to pure dyadic Z[1/2]
    M_sp = sp.Matrix([[sp.Rational(v.numerator, v.denominator) for v in row] +
                      [sp.Rational(b_ex[i].numerator, b_ex[i].denominator)]
                      for i, row in enumerate(A_ex)])
    rref_M, pivots = M_sp.rref()
    free_cols = [j for j in range(n_g + n_f) if j not in pivots]

    for bits in range(2, 11):
        sf = 1 << bits
        x_ex = [Fraction(0)] * (n_g + n_f)
        for j in free_cols:
            x_ex[j] = Fraction(int(round(x_opt[j] * sf)), sf)
        for ridx, pcol in enumerate(pivots):
            val = Fraction(int(rref_M[ridx, -1].p), int(rref_M[ridx, -1].q))
            for j in free_cols:
                coeff = Fraction(int(rref_M[ridx, j].p), int(rref_M[ridx, j].q))
                val -= coeff * x_ex[j]
            x_ex[pcol] = val

        if not all((v.denominator & (v.denominator - 1)) == 0 for v in x_ex):
            continue
        max_shift = max(v.denominator.bit_length() - 1 for v in x_ex)
        G_int = [[0] * r for _ in range(r)]
        for col, (i, j) in enumerate(g_pairs):
            G_int[i][j] = G_int[j][i] = int(x_ex[col] * (1 << max_shift))
        if float(np.linalg.eigvalsh(np.array(G_int, dtype=float))[0]) <= 0:
            continue

        ldlt_scale, diag_all, L_all = dyadic_cholesky_dd(G_int)
        gram = DyadicGram(basis_m, max_shift, G_int, ldlt_scale, diag_all, L_all)
        phi_expr = sum(sp.Rational(x_ex[n_g + k].numerator, x_ex[n_g + k].denominator) * flux_sp[k]
                       for k in range(n_f))
        flux_dp = sympy_to_dpoly(phi_expr, vmap)
        stencil_dp = sympy_to_dpoly(p_expr, vmap)
        cert = CyclicFluxCert(flux_dp, FarkasSOSCert(gram, [], []))
        assert cert.check(0, stencil_dp, [], []), "Exact certificate check failed!"
        return stencil_dp, cert
    raise RuntimeError("Failed to synthesize exact dyadic quartic certificate")

# ===========================================================================
# Part 3: Synthesize & Independently Verify All Six Flagship Theorem Families
# ===========================================================================
def build_all_certificates():
    a, b, c, t = sp.symbols('a b c t')
    v3 = {a: 0, b: 1, c: 2}
    v4t = {t: 0, a: 1, b: 2, c: 3}

    certs = {}

    # --- Theorem 1: Infinite-Dimensional Asymmetric-Skew Quartic Cyclic (c = 13/8) ---
    #   sum_{i in Z/nZ} ( x_i^4 + x_i^2 x_{i+1}^2 - (13/8)*(x_i^3 x_{i+1} - x_i x_{i+1}^2 x_{i+2}) ) >= 0
    s1, c1 = synthesize_quartic_w3_cert(
        lambda x, y, z, cv: x**4 + x**2*y**2 - cv*(x**3*y - x*y**2*z),
        Fraction(13, 8)
    )
    certs["thm1_asym_skew"] = (0, s1, [], [], c1)

    # --- Theorem 2: Infinite-Dimensional Mixed 3-Point Quartic Cyclic (c = 7/4) ---
    #   sum_{i in Z/nZ} ( x_i^4 + x_i^2 x_{i+1}^2 - (7/4)*(x_i^3 x_{i+1} + x_i x_{i+1}^2 x_{i+2} - x_i^2 x_{i+1} x_{i+2}) ) >= 0
    s2, c2 = synthesize_quartic_w3_cert(
        lambda x, y, z, cv: x**4 + x**2*y**2 - cv*(x**3*y + x*y**2*z - x**2*y*z),
        Fraction(7, 4)
    )
    certs["thm2_mixed_quartic"] = (0, s2, [], [], c2)

    # --- Theorem 3A: Continuous Dyadic Hypercube [0,1]^n Symmetric 3-Pattern Density (>= n/2, SHARP) ---
    #   local ineqs: [x0, 1-x0, x1, 1-x1, x2, 1-x2]
    cube_ineqs = [
        sympy_to_dpoly(a, v3), sympy_to_dpoly(1 - a, v3),
        sympy_to_dpoly(b, v3), sympy_to_dpoly(1 - b, v3),
        sympy_to_dpoly(c, v3), sympy_to_dpoly(1 - c, v3),
    ]
    s3a = sympy_to_dpoly((1-a)*(1-b) + a*b + a*(1-b)*c + (1-a)*b*(1-c) - sp.Rational(1, 2), v3)
    flux3a = sympy_to_dpoly(sp.Rational(1, 2)*a + sp.Rational(1, 2)*b - a*b, v3)
    # shifted = (1/2)*(1 - a - c)^2 + (1/2)*a*(1-a) + (1/2)*c*(1-c)
    gram3a_main = rank1_gram([(), ((0, 1),), ((2, 1),)], [1, -1, -1], weight=1, shift=1)
    c3a = CyclicFluxCert(
        flux3a,
        FarkasSOSCert(
            main_gram=gram3a_main,
            ineq_prods=[
                ([0, 1], const_gram(1, 1)),  # (1/2) * a * (1 - a)
                ([4, 5], const_gram(1, 1)),  # (1/2) * c * (1 - c)
            ],
            eq_cofacts=[]
        )
    )
    assert c3a.check(0, s3a, cube_ineqs, [])
    certs["thm3a_hypercube_sym_3pat"] = (0, s3a, cube_ineqs, [], c3a)

    # --- Theorem 3B: Continuous Dyadic Hypercube [0,1]^n Genuinely-Cubic Asymmetric 3-Pattern (>= n, SHARP) ---
    #   p(a,b,c) = 3*(1-a)*(1-b) + 3*a*b + 2*a*(1-b)*c - 1
    #   flux(a,b) = a + 2*b - 2*a*b
    #   shifted = (1-b)*((1-a-c)^2 + a*(1-a) + c*(1-c)) + (1-b)*(1-a)*(1-c) - 
    #   Earlier: shifted = 2*(1-b)*(1-a)*(1-c) + 2*a*b!
    #   Check: (1-b)*(1-a)*(1-c) uses idxs [1, 3, 5] with const_gram(2, 0), and a*b uses idxs [0, 2] with const_gram(2, 0)!
    #   Even nicer: write 2*(1-b)*(1-a)*(1-c) = (1-b)*(1-a-c)^2 + (1-b)*a*(1-a) + (1-b)*c*(1-c) - (1-b)*a*c + (1-b)*(1-a)*(1-c) ->
    #   keeping it pure Schmüdgen: 2*(1-a)*(1-b)*(1-c) + 2*a*b is exact and minimal!
    s3b = sympy_to_dpoly(3*(1-a)*(1-b) + 3*a*b + 2*a*(1-b)*c - 1, v3)
    flux3b = sympy_to_dpoly(a + 2*b - 2*a*b, v3)
    c3b = CyclicFluxCert(
        flux3b,
        FarkasSOSCert(
            main_gram=const_gram(0, 0),
            ineq_prods=[
                ([1, 3, 5], const_gram(2, 0)),  # 2 * (1-a) * (1-b) * (1-c)
                ([0, 2],    const_gram(2, 0)),  # 2 * a * b
            ],
            eq_cofacts=[]
        )
    )
    assert c3b.check(0, s3b, cube_ineqs, [])
    certs["thm3b_hypercube_asym_3pat"] = (0, s3b, cube_ineqs, [], c3b)

    # --- Theorem 4: Boolean {0,1}^n Frustrated Triangle (>= n/2, SHARP; FALSIFIED on [0,1]^n at 1/2!) ---
    bool_eqs = [
        sympy_to_dpoly(a**2 - a, v3),
        sympy_to_dpoly(b**2 - b, v3),
        sympy_to_dpoly(c**2 - c, v3),
    ]
    s4 = sympy_to_dpoly((a + b - 1)**2 + (a + c - 1)**2 - sp.Rational(1, 2), v3)
    flux4 = sympy_to_dpoly(sp.Rational(1, 2)*a + sp.Rational(1, 2)*b - a*b, v3)
    c4 = CyclicFluxCert(
        flux4,
        FarkasSOSCert(
            main_gram=rank1_gram([(), ((0, 1),), ((2, 1),)], [1, -1, -1], weight=1, shift=1),
            ineq_prods=[
                ([0, 1],    const_gram(1, 1)),  # (1/2) * a * (1-a)
                ([4, 5],    const_gram(1, 1)),  # (1/2) * c * (1-c)
                ([1, 3, 5], const_gram(1, 0)),  # (1-a)*(1-b)*(1-c)
                ([0, 2, 4], const_gram(1, 0)),  # a*b*c
            ],
            eq_cofacts=[
                DyadicPoly.const(2, 0),         # 2 * (a^2 - a)
                DyadicPoly.const(1, 0),         # 1 * (b^2 - b)
                DyadicPoly.const(1, 0),         # 1 * (c^2 - c)
            ]
        )
    )
    assert c4.check(0, s4, cube_ineqs, bool_eqs)
    certs["thm4_boolean_frustrated_tri"] = (0, s4, cube_ineqs, bool_eqs, c4)

    # --- Theorem 5A: Doubly-Infinite Parametric Discrete Biharmonic-Sobolev (forall n>=1, forall t in Z[1/2]) ---
    #   param var 0 = t; site vars 1,2,3 = x_i, x_{i+1}, x_{i+2}
    s5a = sympy_to_dpoly((c - 2*b + a)**2 - 2*t*(b - a)**2 + t**2 * a**2, v4t)
    flux5a = sympy_to_dpoly(2*t*(a**2 - a*b) - t**2 * a**2, v4t)
    # shifted == (c - 2*b + a + t*b)^2
    gram5a = rank1_gram(
        [((1, 1),), ((2, 1),), ((3, 1),), ((0, 1), (2, 1))],
        [1, -2, 1, 1],
        weight=1, shift=0
    )
    c5a = CyclicFluxCert(flux5a, FarkasSOSCert(gram5a, [], []))
    assert c5a.check(1, s5a, [], [])
    certs["thm5a_parametric_biharmonic"] = (1, s5a, [], [], c5a)

    # --- Theorem 5B: Open-Boundary Discrete Biharmonic-Sobolev Stabilization (t=2, OpenFluxCert, SHARP!) ---
    s5b = sympy_to_dpoly((c - 2*b + a)**2 - 4*(b - a)**2 + 4*a**2, v3)
    bL5b = sympy_to_dpoly(2*a**2 + 2*b**2, v3)
    bR5b = sympy_to_dpoly(2*a**2 + 2*b**2, v3)
    flux5b = sympy_to_dpoly(-4*a*b, v3)
    # bulk shifted: (c - 2*b + a + 2*b)^2 = (a + c)^2
    gram5b_bulk = rank1_gram([((0, 1),), ((2, 1),)], [1, 1], weight=1, shift=0)
    gram5b_left = rank1_gram([((0, 1),), ((1, 1),)], [1, 1], weight=2, shift=0)
    gram5b_right = rank1_gram([((0, 1),), ((1, 1),)], [1, -1], weight=2, shift=0)
    c5b = OpenFluxCert(
        flux5b,
        bulk_cert=FarkasSOSCert(gram5b_bulk, [], []),
        left_cert=FarkasSOSCert(gram5b_left, [], []),
        right_cert=FarkasSOSCert(gram5b_right, [], []),
    )
    assert c5b.check(0, s5b, bL5b, bR5b, [], [])
    certs["thm5b_open_biharmonic"] = (0, s5b, bL5b, bR5b, [], [], c5b)

    # --- Theorem 6: Fixed-Dimension Nonlinear Dyadic Positivstellensatz Refutation (Disk vs Half-Plane) ---
    #   g0 = 1 - x^2 - y^2 >= 0, g1 = x + y - 23/16 >= 0  ==>  False!
    #   Identity: -17/256 == (x - y)^2 + (x + y - 23/16)^2 + 2*(1 - x^2 - y^2) + (23/8)*(x + y - 23/16)
    #   Expanding: 2*(1 - x^2 - y^2) + (23/8)*(x + y - 23/16) + (x - y)^2 + (x + y - 23/16)^2
    #     = 2 - (x+y)^2 + (23/8)(x+y) - 529/128 + (x+y)^2 - (23/8)(x+y) + 529/256 = 2 - 529/256 = -17/256.
    #   If g0 >= 0 and g1 >= 0 the right-hand side is >= 0, so -17/256 >= 0: a contradiction.
    x_s, y_s = sp.symbols('x y')
    v2 = {x_s: 0, y_s: 1}
    g0_ref = sympy_to_dpoly(1 - x_s**2 - y_s**2, v2)
    g1_ref = sympy_to_dpoly(x_s + y_s - sp.Rational(23, 16), v2)
    # Main Gram: (x - y)^2 + (x + y - 23/16)^2 on basis [1, x, y] with shift = 8 (1/256):
    #   256*(x - y)^2 + (16*x + 16*y - 23)^2
    #   basis = [1, x, y]:
    #   row1 = [0, 16, -16] (weight 1) -> 256*(x-y)^2
    #   row2 = [-23, 16, 16] (weight 1) -> (16x + 16y - 23)^2
    L_ref = [[0, 16, -16], [-23, 16, 16]]
    d_ref = [1, 1]
    G_ref = [[sum(d_ref[k] * L_ref[k][i] * L_ref[k][j] for k in range(2)) for j in range(3)] for i in range(3)]
    gram6_main = DyadicGram([(), ((0, 1),), ((1, 1),)], shift=8, G=G_ref, scale=0, diag=d_ref, L=L_ref)
    c6 = FarkasSOSCert(
        main_gram=gram6_main,
        ineq_prods=[
            ([0], const_gram(2, 0)),   # 2 * (1 - x^2 - y^2)
            ([1], const_gram(23, 3)),  # (23/8) * (x + y - 23/16)
        ],
        eq_cofacts=[]
    )
    target6 = DyadicPoly.const(-17, 8)
    assert c6.check(target6, [g0_ref, g1_ref], [])
    certs["thm6_nonlinear_farkas_refutation"] = (target6, [g0_ref, g1_ref], [], c6)

    return certs

# ===========================================================================
# Part 4: Independent Exact Replay, Sharpness Counterexamples, & Mutation Suite
# ===========================================================================
def run_independent_verification(certs):
    print("=== Independent Exact Replay & Sharpness Verification ===")

    # 1. Theorem 1: Asym-Skew Quartic (c = 13/8)
    _, s1, _, _, c1 = certs["thm1_asym_skew"]
    # Local indefiniteness witness (and 1-var flux impossibility!)
    local_val = s1.eval_frac({0: Fraction(1), 1: Fraction(1), 2: Fraction(-1)})
    assert local_val == Fraction(-5, 4) < 0
    print(f"[Thm 1] Local stencil at (1,1,-1) = {local_val} < 0 (proves 0-flux & ANY 1-var flux impossible!)")
    # Check 500 random integer/dyadic cycles across n = 1..16
    rng = np.random.default_rng(2026)
    for n in [1, 2, 3, 4, 5, 7, 12, 16]:
        for _ in range(50):
            xs = [Fraction(int(v), 4) for v in rng.integers(-8, 9, size=n)]
            tot = sum(s1.eval_frac({0: xs[i], 1: xs[(i+1)%n], 2: xs[(i+2)%n]}) for i in range(n))
            assert tot >= 0, f"Thm 1 violated at n={n}, xs={xs}: {tot}"
    # Sharpness counterexample at c = 27/16 (just 1/16 tighter!): x = (-3, -2, 3, 2)
    x_ce1 = [Fraction(-3), Fraction(-2), Fraction(3), Fraction(2)]
    val_ce1 = sum(x_ce1[i]**4 + x_ce1[i]**2 * x_ce1[(i+1)%4]**2
                  - Fraction(27, 16) * (x_ce1[i]**3 * x_ce1[(i+1)%4] - x_ce1[i] * x_ce1[(i+1)%4]**2 * x_ce1[(i+2)%4])
                  for i in range(4))
    assert val_ce1 == Fraction(-25, 4) < 0
    print(f"[Thm 1] Verified 400 exact dyadic cycles (n=1..16). Sharpness at c=27/16: x=[-3,-2,3,2] -> {val_ce1} < 0.")

    # 2. Theorem 2: Mixed 3-Point Quartic (c = 7/4)
    _, s2, _, _, c2 = certs["thm2_mixed_quartic"]
    local_val2 = s2.eval_frac({0: Fraction(1), 1: Fraction(2), 2: Fraction(3)})
    assert local_val2 == Fraction(-9, 1) < 0
    for n in [1, 2, 3, 4, 5, 8, 12]:
        for _ in range(50):
            xs = [Fraction(int(v), 4) for v in rng.integers(-8, 9, size=n)]
            tot = sum(s2.eval_frac({0: xs[i], 1: xs[(i+1)%n], 2: xs[(i+2)%n]}) for i in range(n))
            assert tot >= 0
    x_ce2 = [Fraction(v) for v in [0, -1, -2, -4, -4, -2, 1, -1]]
    val_ce2 = sum(x_ce2[i]**4 + x_ce2[i]**2 * x_ce2[(i+1)%8]**2
                  - Fraction(15, 8) * (x_ce2[i]**3 * x_ce2[(i+1)%8] + x_ce2[i] * x_ce2[(i+1)%8]**2 * x_ce2[(i+2)%8]
                                       - x_ce2[i]**2 * x_ce2[(i+1)%8] * x_ce2[(i+2)%8])
                  for i in range(8))
    assert val_ce2 == Fraction(-25, 8) < 0
    print(f"[Thm 2] Local stencil at (1,2,3) = {local_val2} < 0. Verified 350 dyadic cycles. Sharpness at c=15/8: n=8 -> {val_ce2} < 0.")

    # 3. Theorem 3A & 3B: Continuous Hypercube [0,1]^n 3-Pattern Densities
    _, s3a, _, _, _ = certs["thm3a_hypercube_sym_3pat"]
    _, s3b, _, _, _ = certs["thm3b_hypercube_asym_3pat"]
    for n in range(1, 11):
        for bits in itertools.product((Fraction(0), Fraction(1)), repeat=n):
            t3a = sum(s3a.eval_frac({0: bits[i], 1: bits[(i+1)%n], 2: bits[(i+2)%n]}) for i in range(n))
            t3b = sum(s3b.eval_frac({0: bits[i], 1: bits[(i+1)%n], 2: bits[(i+2)%n]}) for i in range(n))
            assert t3a >= 0 and t3b >= 0
    # Equality witnesses (EXACT sharpness!)
    eq3a = sum(s3a.eval_frac({0: [0,0,1,1][i], 1: [0,0,1,1][(i+1)%4], 2: [0,0,1,1][(i+2)%4]}) for i in range(4))
    eq3b_p2 = sum(s3b.eval_frac({0: [0,1][i], 1: [0,1][(i+1)%2], 2: [0,1][(i+2)%2]}) for i in range(2))
    eq3b_p3 = sum(s3b.eval_frac({0: [0,0,1][i], 1: [0,0,1][(i+1)%3], 2: [0,0,1][(i+2)%3]}) for i in range(3))
    assert eq3a == 0 and eq3b_p2 == 0 and eq3b_p3 == 0
    print(f"[Thm 3A/3B] Exhaustively verified all binary cycles n=1..10. Exact equality 0 on 0011 (3A) and 01 & 001 (3B).")

    # 4. Theorem 4: Boolean Frustrated Triangle & Integrality Gap
    _, s4, _, _, _ = certs["thm4_boolean_frustrated_tri"]
    for n in range(1, 11):
        for bits in itertools.product((Fraction(0), Fraction(1)), repeat=n):
            t4 = sum(s4.eval_frac({0: bits[i], 1: bits[(i+1)%n], 2: bits[(i+2)%n]}) for i in range(n))
            assert t4 >= 0
    eq4 = sum(s4.eval_frac({0: [0,0,1,1][i], 1: [0,0,1,1][(i+1)%4], 2: [0,0,1,1][(i+2)%4]}) for i in range(4))
    gap4 = s4.eval_frac({0: Fraction(1, 2), 1: Fraction(1, 2), 2: Fraction(1, 2)})
    assert eq4 == 0 and gap4 == Fraction(-1, 2) < 0
    print(f"[Thm 4] Exhaustively verified Boolean cycles n=1..10. Exact 0 on 0011; continuous gap at x=1/2 -> {gap4} < 0.")

    # 5. Theorem 5A & 5B: Doubly-Infinite Parametric & Open-Boundary Biharmonic-Sobolev
    _, s5a, _, _, _ = certs["thm5a_parametric_biharmonic"]
    for t_val in [Fraction(-3, 2), Fraction(0), Fraction(1, 2), Fraction(2), Fraction(7, 4)]:
        for n in [1, 2, 3, 4, 6]:
            for _ in range(20):
                xs = [Fraction(int(v), 2) for v in rng.integers(-6, 7, size=n)]
                tot = sum(s5a.eval_frac({0: t_val, 1: xs[i], 2: xs[(i+1)%n], 3: xs[(i+2)%n]}) for i in range(n))
                assert tot >= 0
    # Open boundary exact equality on period-4 wave (1, -1, -1, 1, 1, -1, -1, ...) for n=1, 5, 9!
    _, s5b, bL5b, bR5b, _, _, _ = certs["thm5b_open_biharmonic"]
    wave = [Fraction(1), Fraction(-1), Fraction(-1), Fraction(1)]
    for n in [1, 5, 9]:
        seq = [wave[i % 4] for i in range(n + 2)]
        tot = (bL5b.eval_frac({0: seq[0], 1: seq[1]})
               + sum(s5b.eval_frac({0: seq[i], 1: seq[i+1], 2: seq[i+2]}) for i in range(n))
               + bR5b.eval_frac({0: seq[n], 1: seq[n+1]}))
        assert tot == 0
    # Unstabilized open chain fails: n=1, x=(0,1,2) -> -4 < 0
    assert s5b.eval_frac({0: Fraction(0), 1: Fraction(1), 2: Fraction(2)}) == Fraction(-4)
    print(f"[Thm 5A/5B] Parametric & Open Biharmonic verified. Exact 0 on open period-4 wave (n=1,5,9); unstabilized (0,1,2) -> -4.")

    # 6. Theorem 6: Nonlinear Farkas Refutation & Sharpness at 45/32
    x_feas, y_feas = Fraction(45, 64), Fraction(45, 64)
    assert 1 - x_feas**2 - y_feas**2 == Fraction(46, 4096) > 0
    assert x_feas + y_feas == Fraction(45, 32)
    print(f"[Thm 6] Nonlinear Positivstellensatz refutation (23/16) verified; perturbed 45/32 feasible at (45/64, 45/64) with 1-x^2-y^2 = 46/4096 > 0.")

    # 7. Adversarial Mutation Suite (all MUST return False!)
    print("\n=== Adversarial Mutation Rejection Tests ===")
    g1 = c1.sos_cert.main_gram
    mutations = []

    # Mut 1: negative diagonal weight
    g_neg = DyadicGram(g1.basis, g1.shift, g1.G, g1.scale, [-1] + g1.diag[1:], g1.L)
    mutations.append(("neg_diag", g_neg.check_psd()))

    # Mut 2: 1-bit flip in factor matrix L
    L_bad = [list(row) for row in g1.L]
    L_bad[0][0] += 1
    g_lbad = DyadicGram(g1.basis, g1.shift, g1.G, g1.scale, g1.diag, L_bad)
    mutations.append(("ldlt_1bit_flip", g_lbad.check_psd()))

    # Mut 3: asymmetric Gram matrix
    G_asym = [list(row) for row in g1.G]
    G_asym[0][1] += 1
    g_asym = DyadicGram(g1.basis, g1.shift, G_asym, g1.scale, g1.diag, g1.L)
    mutations.append(("asymmetric_gram", g_asym.check_psd()))

    # Mut 4: wrong dyadic scale exponent
    g_scale = DyadicGram(g1.basis, g1.shift, g1.G, g1.scale + 1, g1.diag, g1.L)
    mutations.append(("wrong_ldlt_scale", g_scale.check_psd()))

    # Mut 5: valid PSD Gram with perturbed polynomial match
    g_match = DyadicGram(g1.basis, g1.shift + 1, g1.G, g1.scale, g1.diag, g1.L)
    assert g_match.check_psd()  # still valid PSD!
    c_match = CyclicFluxCert(c1.flux, FarkasSOSCert(g_match, [], []))
    mutations.append(("valid_psd_wrong_poly_match", c_match.check(0, s1, [], [])))

    # Mut 6: negative Farkas multiplier on Thm 3A
    _, s3a, cube_ineqs, _, c3a = certs["thm3a_hypercube_sym_3pat"]
    bad_farkas_gram = DyadicGram([()], 1, [[-1]], 0, [-1], [[1]])
    c_neg_f = CyclicFluxCert(c3a.flux, FarkasSOSCert(c3a.sos_cert.main_gram, [([0, 1], bad_farkas_gram), c3a.sos_cert.ineq_prods[1]], []))
    mutations.append(("neg_farkas_multiplier", c_neg_f.check(0, s3a, cube_ineqs, [])))

    # Mut 7: corrupted flux potential
    bad_flux = c1.flux + DyadicPoly.const(1, 6) * DyadicPoly.var(0) * DyadicPoly.var(0) * DyadicPoly.var(0) * DyadicPoly.var(0)
    c_bad_flux = CyclicFluxCert(bad_flux, c1.sos_cert)
    mutations.append(("corrupted_flux", c_bad_flux.check(0, s1, [], [])))

    # Mut 8: over-tight target constant (c = 27/16 with c = 13/8 certificate)
    a, b, c = sp.symbols('a b c')
    s1_tight = sympy_to_dpoly(a**4 + a**2*b**2 - sp.Rational(27, 16)*(a**3*b - a*b**2*c), {a: 0, b: 1, c: 2})
    mutations.append(("overtight_target_27_16", c1.check(0, s1_tight, [], [])))

    # Mut 9: weakened open boundary (constant 1 instead of 2)
    _, s5b, bL5b, bR5b, _, _, c5b = certs["thm5b_open_biharmonic"]
    bL_weak = sympy_to_dpoly(a**2 + b**2, {a: 0, b: 1, c: 2})
    mutations.append(("weakened_open_boundary", c5b.check(0, s5b, bL_weak, bR5b, [], [])))

    for name, res in mutations:
        assert res is False, f"Mutation {name} was NOT rejected!"
        print(f"  [REJECTED OK] {name} -> {res}")

# ===========================================================================
# Part 5: Lean 4 Code Printer for Exact Certificates
# ===========================================================================
def fmt_mono(m):
    return "[" + ", ".join(f"({v}, {e})" for v, e in m) + "]"

def fmt_poly(p):
    return "[" + ", ".join(f"({fmt_mono(m)}, ({c}))" for m, c in p) + "]"

def fmt_dpoly(dp):
    return f"{{ shift := {dp.shift}, poly := {fmt_poly(dp.poly)} }}"

def fmt_int_mat(M):
    return "[" + ", ".join("[" + ", ".join(f"({x})" for x in row) + "]" for row in M) + "]"

def fmt_gram(g):
    basis_s = "[" + ", ".join(fmt_mono(m) for m in g.basis) + "]"
    diag_s = "[" + ", ".join(f"({d})" for d in g.diag) + "]"
    return (
        f"{{ basis := {basis_s},\n"
        f"    shift := {g.shift},\n"
        f"    G := {fmt_int_mat(g.G)},\n"
        f"    scale := {g.scale},\n"
        f"    diag := {diag_s},\n"
        f"    L := {fmt_int_mat(g.L)} }}"
    )

def export_lean_certs(certs, out_path):
    lines = ["-- Auto-generated exact Z[1/2] certificates from explore_and_verify.py\n"]
    for key in ["thm1_asym_skew", "thm2_mixed_quartic"]:
        _, stencil, _, _, c = certs[key]
        lines.append(f"def {key}_stencil : DyadicPoly := {fmt_dpoly(stencil)}")
        lines.append(f"def {key}_flux : DyadicPoly := {fmt_dpoly(c.flux)}")
        lines.append(f"def {key}_gram : DyadicGram :=\n  {fmt_gram(c.sos_cert.main_gram)}")
        lines.append("")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    print(f"\nExported exact Lean quartic certificates to {out_path}")

if __name__ == "__main__":
    certs = build_all_certificates()
    run_independent_verification(certs)
    print("\nALL EXACT CHECKS PASSED!")
