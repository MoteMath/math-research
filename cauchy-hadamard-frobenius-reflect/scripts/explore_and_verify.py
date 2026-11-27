"""
explore_and_verify.py — Pure-Silicon Cauchy-Hadamard-Frobenius Reflection Compiler,
Independent Exact BitVec Verifier, Sharpness Counterexample Finder, and Certificate Mutation Suite.

Exact integer arithmetic only (zero floating-point values anywhere).
Mirrors the standalone Lean 4.34.1 reflection engine in the Lean sources.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple, List, Optional, Dict
import random

# ============================================================================
# 1. Exact Hardware BitVec w Semantics (Independent Oracle)
# ============================================================================

def bv_mask(w: int) -> int:
    return (1 << w) - 1

def bv_clmul(w: int, a: int, b: int) -> int:
    """Exact hardware shift-and-XOR carryless multiplication mod x^w."""
    m = bv_mask(w)
    a &= m
    b &= m
    res = 0
    for i in range(w):
        if (b >> i) & 1:
            res ^= (a << i) & m
    return res

def bv_shl(w: int, a: int, s: int) -> int:
    return (a << s) & bv_mask(w)

def bv_shr(w: int, a: int, s: int) -> int:
    return (a & bv_mask(w)) >> s

def bv_frob(w: int, a: int, r: int) -> int:
    res = a & bv_mask(w)
    for _ in range(r):
        res = bv_clmul(w, res, res)
    return res

def bv_E(w: int, r: int) -> int:
    return bv_frob(w, bv_mask(w), r)

def bv_Pr(w: int, r: int, a: int) -> int:
    return bv_clmul(w, a, bv_E(w, r))

# ============================================================================
# 2. Object Expression AST (Pure (^, &, clmul, <<<, 0, 1, allOnes))
# ============================================================================

@dataclass(frozen=True)
class Expr:
    kind: str
    a: object = None
    b: object = None

ZERO = Expr("zero")
ONE = Expr("one")
ALL_ONES = Expr("allOnes")
def Var(i: int) -> Expr: return Expr("var", i)
def Xor(a: Expr, b: Expr) -> Expr: return Expr("xor", a, b)
def And(a: Expr, b: Expr) -> Expr: return Expr("and", a, b)
def Clmul(a: Expr, b: Expr) -> Expr: return Expr("clmul", a, b)
def Shl(a: Expr, s: int) -> Expr: return Expr("shl", a, s)

def Frob(r: int, e: Expr) -> Expr:
    res = e
    for _ in range(r):
        res = Clmul(res, res)
    return res

def E_expr(r: int) -> Expr:
    return Frob(r, ALL_ONES)

def P_expr(r: int, e: Expr) -> Expr:
    return Clmul(e, E_expr(r))

def Delta_expr(r: int, e: Expr) -> Expr:
    return Xor(e, Shl(e, 1 << r))

def eval_bv(w: int, env: Dict[int, int], e: Expr) -> int:
    m = bv_mask(w)
    k = e.kind
    if k == "zero": return 0
    if k == "one": return 1 & m
    if k == "allOnes": return m
    if k == "var": return env.get(e.a, 0) & m
    if k == "xor": return eval_bv(w, env, e.a) ^ eval_bv(w, env, e.b)
    if k == "and": return eval_bv(w, env, e.a) & eval_bv(w, env, e.b)
    if k == "clmul": return bv_clmul(w, eval_bv(w, env, e.a), eval_bv(w, env, e.b))
    if k == "shl": return bv_shl(w, eval_bv(w, env, e.a), e.b)
    raise ValueError(k)

# ============================================================================
# 3. Syntactic Lane-Safety & Dyadic Dilation (Base r=0 -> All r : Nat)
# ============================================================================

def is_const(e: Expr) -> bool:
    k = e.kind
    if k in ("zero", "one", "allOnes"): return True
    if k == "var": return False
    if k == "shl": return is_const(e.a)
    return is_const(e.a) and is_const(e.b)

def is_lane_safe(e: Expr) -> bool:
    """True iff every clmul has at least one constant operand (so dyadic dilation commutes with Cartier split)."""
    k = e.kind
    if k in ("zero", "one", "allOnes", "var"): return True
    if k == "shl": return is_lane_safe(e.a)
    if k in ("xor", "and"): return is_lane_safe(e.a) and is_lane_safe(e.b)
    if k == "clmul":
        return (is_lane_safe(e.a) and is_const(e.b)) or (is_const(e.a) and is_lane_safe(e.b))
    return False

def dilate_expr(r: int, e: Expr) -> Expr:
    """Stride-2^r SIMD lane-replication functor: replicates every bit-lane 0..2^r-1 independently."""
    k = e.kind
    if k == "zero": return ZERO
    if k == "one": return Xor(ALL_ONES, Shl(ALL_ONES, 1 << r))
    if k == "allOnes": return ALL_ONES
    if k == "var": return e
    if k == "xor": return Xor(dilate_expr(r, e.a), dilate_expr(r, e.b))
    if k == "and": return And(dilate_expr(r, e.a), dilate_expr(r, e.b))
    if k == "shl": return Shl(dilate_expr(r, e.a), e.b << r)
    if k == "clmul":
        if is_const(e.b):
            return Clmul(dilate_expr(r, e.a), Frob(r, e.b))
        elif is_const(e.a):
            return Clmul(Frob(r, e.a), dilate_expr(r, e.b))
        else:
            return Clmul(dilate_expr(r, e.a), dilate_expr(r, e.b))
    raise ValueError(k)

# ============================================================================
# 4. Cartier 2-Splitting (Exact Stream Homomorphism (ev, od))
# ============================================================================

def cartier_split(e: Expr) -> Tuple[Expr, Expr]:
    """Returns (ev(e), od(e)) with var i mapped to (var (2*i), var (2*i+1))."""
    k = e.kind
    if k == "zero": return (ZERO, ZERO)
    if k == "one": return (ONE, ZERO)
    if k == "allOnes": return (ALL_ONES, ALL_ONES)
    if k == "var": return (Var(2 * e.a), Var(2 * e.a + 1))
    if k == "xor":
        a0, a1 = cartier_split(e.a)
        b0, b1 = cartier_split(e.b)
        return (Xor(a0, b0), Xor(a1, b1))
    if k == "and":
        a0, a1 = cartier_split(e.a)
        b0, b1 = cartier_split(e.b)
        return (And(a0, b0), And(a1, b1))
    if k == "shl":
        a0, a1 = cartier_split(e.a)
        s = e.b
        q, rem = divmod(s, 2)
        if rem == 0:
            return (Shl(a0, q), Shl(a1, q))
        else:
            return (Shl(a1, q + 1), Shl(a0, q))
    if k == "clmul":
        if e.a == e.b:
            # Exact Frobenius shortcut: ev(a ⊗ a) = unsplit(a) = F(a0) ^ (F(a1) <<< 1), od(a ⊗ a) = 0
            a0, a1 = cartier_split(e.a)
            return (Xor(Clmul(a0, a0), Shl(Clmul(a1, a1), 1)), ZERO)
        a0, a1 = cartier_split(e.a)
        b0, b1 = cartier_split(e.b)
        ev = Xor(Clmul(a0, b0), Shl(Clmul(a1, b1), 1))
        od = Xor(Clmul(a0, b1), Clmul(a1, b0))
        return (ev, od)
    raise ValueError(k)

# ============================================================================
# 5. Canonical Cauchy-Hadamard-Frobenius Normal Form (NF)
# ============================================================================
# NF = sorted, duplicate-free tuple of Monos (XOR-sum; () = 0)
# Mono = sorted, duplicate-free tuple of Atoms (AND-product; () = allOnes)
# Atom:
#   ("bitAt", s)                    = 1 <<< s
#   ("var", idx, s)                 = x_idx <<< s
#   ("frob", k, mono, s)            = F^(k+1)(mono) <<< s   (k >= 0, s < 2^k if mono==() else any s)
#   ("conv", factors_tuple, s)      = (clmul of >=2 canonical Poly factors) <<< s
#     where each factor is a canonical non-zero, non-one, shift-0 Poly (with no E_k shiftable when s>=half)

def xor_insert(m, poly):
    out = []
    inserted = False
    for h in poly:
        if not inserted:
            if m == h:
                inserted = True  # cancel!
                continue
            elif m < h:
                out.append(m)
                out.append(h)
                inserted = True
            else:
                out.append(h)
        else:
            out.append(h)
    if not inserted:
        out.append(m)
    return tuple(out)

def xor_poly(p1, p2):
    res = p2
    for m in p1:
        res = xor_insert(m, res)
    return res

def shl_atom_to_poly(a, s: int):
    if s == 0:
        return ((a,),)
    tag = a[0]
    if tag == "bitAt":
        return ((("bitAt", a[1] + s),),)
    if tag == "var":
        return ((("var", a[1], a[2] + s),),)
    if tag == "frob":
        k, m, s0 = a[1], a[2], a[3]
        tot = s0 + s
        # If m == () (this is E_{k+1}), reduce shift >= 2^k via E_{k+1} <<< 2^k = E_k ^ E_{k+1}
        if m == ():
            half = 1 << k
            if tot >= half:
                rem = tot - half
                p1 = ((),) if k == 0 else ((("frob", k - 1, (), 0),),)
                p1_shifted = shl_poly(p1, rem)
                p2_shifted = shl_atom_to_poly(("frob", k, (), 0), rem)
                return xor_poly(p1_shifted, p2_shifted)
        return ((("frob", k, m, tot),),)
    if tag == "conv":
        factors, s0 = a[1], a[2]
        tot = s0 + s
        # Check if any factor is allOnes ( ((),) ) or E_{k+1} ( ((("frob", k, (), 0),),) ) with tot >= half
        for idx, fac in enumerate(factors):
            if fac == ((),) and tot >= 1:
                rest = factors[:idx] + factors[idx+1:]
                rest_poly = conv_factors_poly(rest, 0)
                # (rest ⊗ allOnes) <<< tot = ((rest ⊗ allOnes) ^ rest) <<< (tot - 1)
                p_keep = shl_poly(clmul_poly(rest_poly, ((),)), tot - 1)
                p_drop = shl_poly(rest_poly, tot - 1)
                return xor_poly(p_keep, p_drop)
            if len(fac) == 1 and len(fac[0]) == 1 and fac[0][0][0] == "frob" and fac[0][0][2] == () and fac[0][0][3] == 0:
                k = fac[0][0][1]
                half = 1 << k
                if tot >= half:
                    rest = factors[:idx] + factors[idx+1:]
                    rest_poly = conv_factors_poly(rest, 0)
                    prev_E = ((),) if k == 0 else ((("frob", k - 1, (), 0),),)
                    p1 = shl_poly(clmul_poly(rest_poly, prev_E), tot - half)
                    p2 = shl_poly(clmul_poly(rest_poly, fac), tot - half)
                    return xor_poly(p1, p2)
        return ((("conv", factors, tot),),)
    raise ValueError(tag)

def shl_mono_to_poly(m, s: int):
    if s == 0:
        return (m,)
    if m == ():
        # allOnes <<< s = allOnes ^ bitAt 0 ^ ... ^ bitAt (s-1)
        res = ((),)
        for j in range(s):
            res = xor_insert((("bitAt", j),), res)
        return res
    res = ((),)
    for a in m:
        res = and_poly(res, shl_atom_to_poly(a, s))
    return res

def shl_poly(p, s: int):
    if s == 0:
        return p
    res = ()
    for m in p:
        res = xor_poly(res, shl_mono_to_poly(m, s))
    return res

def atom_min_shift(a) -> int:
    tag = a[0]
    if tag == "bitAt": return a[1]
    if tag == "var": return a[2]
    if tag == "frob": return a[3]
    if tag == "conv": return a[2]
    return 0

def frob_poly(k: int, p):
    """Apply F^(k+1) to a normalized Poly."""
    res = ()
    for m in p:
        res = xor_poly(res, frob_mono(k, m))
    return res

def frob_mono(k: int, m):
    """Apply F^(k+1) to a single Mono, simplifying Frobenius-homomorphic atoms."""
    if m == ():
        return ((("frob", k, (), 0),),)
    # Single atom shortcuts
    if len(m) == 1:
        a = m[0]
        if a[0] == "bitAt":
            return ((("bitAt", a[1] << (k + 1)),),)
        if a[0] == "frob":
            # F^(k+1)(F^(k0+1)(m0) <<< s0) = F^(k+k0+2)(m0) <<< (s0 * 2^(k+1))
            return shl_atom_to_poly(("frob", k + a[1] + 1, a[2], 0), a[3] << (k + 1))
    # Pull out minimum shift common to all atoms if convenient, else wrap directly
    return ((("frob", k, m, 0),),)

def insert_atom_into_mono_poly(a, m):
    """Return Poly representing a & m, applying bitAt collisions & Frobenius-Hadamard fusion."""
    # Check bitAt collision with any atom in m
    if a[0] == "bitAt":
        t = a[1]
        for b in m:
            if b[0] == "bitAt" and b[1] != t:
                return ()
            if atom_min_shift(b) > t:
                return ()
            if b[0] == "frob":
                k, bm, bs = b[1], b[2], b[3]
                if t < bs or ((t - bs) & ((1 << (k + 1)) - 1)) != 0:
                    return ()
    for idx, b in enumerate(m):
        if b[0] == "bitAt":
            t = b[1]
            if atom_min_shift(a) > t:
                return ()
            if a[0] == "frob":
                k, am, as_ = a[1], a[2], a[3]
                if t < as_ or ((t - as_) & ((1 << (k + 1)) - 1)) != 0:
                    return ()
        # Frobenius-Hadamard fusion / residue-class annihilation!
        if a[0] == "frob" and b[0] == "frob":
            k1, m1, s1 = a[1], a[2], a[3]
            k2, m2, s2 = b[1], b[2], b[3]
            kmin = min(k1, k2)
            mod = 1 << (kmin + 1)
            r1 = s1 % mod
            r2 = s2 % mod
            if r1 != r2:
                return ()  # Orthogonal residue classes -> ANNIHILATE TO 0!
            q1, q2 = s1 // mod, s2 // mod
            p1 = shl_mono_to_poly(m1, q1) if k1 == kmin else shl_poly(frob_mono(k1 - kmin - 1, m1), q1)
            p2 = shl_mono_to_poly(m2, q2) if k2 == kmin else shl_poly(frob_mono(k2 - kmin - 1, m2), q2)
            merged_inner = and_poly(p1, p2)
            fused = shl_poly(frob_poly(kmin, merged_inner), r1)
            rest_m = m[:idx] + m[idx+1:]
            return and_poly(fused, (rest_m,))
    # Standard sorted deduplicated insertion (Boolean idempotence a & a = a)
    out = []
    inserted = False
    for b in m:
        if not inserted:
            if a == b:
                inserted = True
                out.append(b)
            elif a < b:
                out.append(a)
                out.append(b)
                inserted = True
            else:
                out.append(b)
        else:
            out.append(b)
    if not inserted:
        out.append(a)
    return (tuple(out),)

def and_mono(m1, m2):
    res = (m2,)
    for a in m1:
        next_res = ()
        for cur_m in res:
            next_res = xor_poly(next_res, insert_atom_into_mono_poly(a, cur_m))
        res = next_res
    return res

def and_poly(p1, p2):
    res = ()
    for m1 in p1:
        for m2 in p2:
            res = xor_poly(res, and_mono(m1, m2))
    return res

def extract_mono_clmul_parts(m):
    """Decompose a single Mono into (shift, list_of_canonical_clmul_factors).
    Returns None if m is 0 (never happens for a Mono)."""
    if len(m) == 1:
        a = m[0]
        if a[0] == "bitAt":
            return (a[1], [])
        if a[0] == "var":
            return (a[2], [((("var", a[1], 0),),)])
        if a[0] == "conv":
            return (a[2], list(a[1]))
        if a[0] == "frob":
            return (a[3], [((("frob", a[1], a[2], 0),),)])
    return (0, [(m,)])

def conv_factors_poly(factors: Tuple, s: int):
    if len(factors) == 0:
        return ((("bitAt", s),),)
    if len(factors) == 1:
        return shl_poly(factors[0], s)
    return shl_atom_to_poly(("conv", tuple(factors), 0), s)

def extract_E_level(fac) -> Optional[int]:
    """Return k if fac is E_k (E_0 = allOnes, E_{k+1} = frob k () 0), else None."""
    if fac == ((),):
        return 0
    if len(fac) == 1 and len(fac[0]) == 1 and fac[0][0][0] == "frob" and fac[0][0][2] == () and fac[0][0][3] == 0:
        return fac[0][0][1] + 1
    return None

def make_E_poly(k: int):
    return ((),) if k == 0 else ((("frob", k - 1, (), 0),),)

def clmul_mono(m1, m2):
    s1, f1 = extract_mono_clmul_parts(m1)
    s2, f2 = extract_mono_clmul_parts(m2)
    s = s1 + s2
    # Merge sorted factors; duplicate factors collapse via Frobenius squaring: f ⊗ f = F(f)!
    all_f = sorted(f1 + f2)
    dedup = []
    squared = []
    i = 0
    while i < len(all_f):
        if i + 1 < len(all_f) and all_f[i] == all_f[i + 1]:
            squared.append(all_f[i])
            i += 2
        else:
            dedup.append(all_f[i])
            i += 1
    if squared:
        res = conv_factors_poly(tuple(dedup), s)
        for sf in squared:
            res = clmul_poly(res, frob_poly(0, sf))
        return res
    # Adjacent E-mask collapse: E_k ⊗ E_{k+1} = E_{k+2} ⊕ (E_{k+2} <<< 2^k)
    e_levels = {extract_E_level(fac): idx for idx, fac in enumerate(dedup) if extract_E_level(fac) is not None}
    for k, idx1 in e_levels.items():
        if (k + 1) in e_levels:
            idx2 = e_levels[k + 1]
            hi, lo = max(idx1, idx2), min(idx1, idx2)
            rest = dedup[:lo] + dedup[lo+1:hi] + dedup[hi+1:]
            base_poly = conv_factors_poly(tuple(rest), s)
            ek2 = make_E_poly(k + 2)
            merged_E = xor_poly(ek2, shl_poly(ek2, 1 << k))
            return clmul_poly(base_poly, merged_E)
    return conv_factors_poly(tuple(dedup), s)

def clmul_poly(p1, p2):
    res = ()
    for m1 in p1:
        for m2 in p2:
            res = xor_poly(res, clmul_mono(m1, m2))
    return res

def norm(e: Expr):
    k = e.kind
    if k == "zero": return ()
    if k == "one": return ((("bitAt", 0),),)
    if k == "allOnes": return ((),)
    if k == "var": return ((("var", e.a, 0),),)
    if k == "xor": return xor_poly(norm(e.a), norm(e.b))
    if k == "and": return and_poly(norm(e.a), norm(e.b))
    if k == "clmul": return clmul_poly(norm(e.a), norm(e.b))
    if k == "shl": return shl_poly(norm(e.a), e.b)
    raise ValueError(k)

# ============================================================================
# 6. Binary Proof Certificate & Verified Checker (checkCert)
# ============================================================================

@dataclass(frozen=True)
class Cert:
    kind: str
    a: object = None
    b: object = None
    c: object = None

def check_cert(e1: Expr, e2: Expr, cert: Cert) -> bool:
    k = cert.kind
    if k == "normEq":
        return norm(e1) == norm(e2)
    if k == "cartierSplit":
        ev1, od1 = cartier_split(e1)
        ev2, od2 = cartier_split(e2)
        return check_cert(ev1, ev2, cert.a) and check_cert(od1, od2, cert.b)
    if k == "cancelDelta":
        r = cert.a
        return check_cert(Delta_expr(r, e1), Delta_expr(r, e2), cert.b)
    if k == "symm":
        return check_cert(e2, e1, cert.a)
    if k == "trans":
        mid = cert.a
        return check_cert(e1, mid, cert.b) and check_cert(mid, e2, cert.c)
    if k == "congXor":
        if e1.kind != "xor" or e2.kind != "xor": return False
        return check_cert(e1.a, e2.a, cert.a) and check_cert(e1.b, e2.b, cert.b)
    if k == "congAnd":
        if e1.kind != "and" or e2.kind != "and": return False
        return check_cert(e1.a, e2.a, cert.a) and check_cert(e1.b, e2.b, cert.b)
    if k == "congClmul":
        if e1.kind != "clmul" or e2.kind != "clmul": return False
        return check_cert(e1.a, e2.a, cert.a) and check_cert(e1.b, e2.b, cert.b)
    if k == "congShl":
        if e1.kind != "shl" or e2.kind != "shl" or e1.b != e2.b: return False
        return check_cert(e1.a, e2.a, cert.a)
    return False

def compile_cartier_cert(depth: int) -> Cert:
    if depth == 0:
        return Cert("normEq")
    sub = compile_cartier_cert(depth - 1)
    return Cert("cartierSplit", sub, sub)

# ============================================================================
# 7. Theorem Family Synthesis, Certificate Compilation, Independent Checks
# ============================================================================

def build_residue_conv_split(r: int, t: int) -> Tuple[Expr, Expr]:
    a, b = Var(0), Var(1)
    Er = E_expr(r)
    lhs = And(Clmul(a, b), Shl(Er, t))
    rhs = ZERO
    mod = 1 << r
    for u in range(mod):
        v = (t - u) & (mod - 1)
        term = Clmul(And(a, Shl(Er, u)), And(b, Shl(Er, v)))
        rhs = term if rhs == ZERO else Xor(rhs, term)
    return lhs, rhs

def build_ito_n(n: int, r: int = 0) -> Tuple[Expr, Expr]:
    """n-variable Stride-2^r Binary Ito-Leibniz / Quasi-Shuffle Identity."""
    ps = [P_expr(r, Var(i)) for i in range(n)]
    lhs = ps[0]
    for p in ps[1:]:
        lhs = And(lhs, p)
    body = None
    for mask_bits in range(1, 1 << n):
        term = None
        for i in range(n):
            fac = Var(i) if ((mask_bits >> i) & 1) else ps[i]
            term = fac if term is None else And(term, fac)
        body = term if body is None else Xor(body, term)
    rhs = P_expr(r, body)
    return lhs, rhs

def build_self_scale_ladder(r: int = 0) -> Tuple[Expr, Expr]:
    a = Var(0)
    pr = P_expr(r, a)
    pr1 = P_expr(r + 1, a)
    lhs = And(pr, pr1)
    rhs = Xor(pr1, P_expr(r, And(a, Xor(pr, pr1))))
    return lhs, rhs

def build_two_scale_ladder(r: int = 0) -> Tuple[Expr, Expr]:
    """P_r(a) & P_{r+2}(a) = P_r( (a & P_{r+2}(a)) ^ ((a ^ P_r(a)) & P_r(P_{r+1}(a))) )."""
    a = Var(0)
    pr = P_expr(r, a)
    pr2 = P_expr(r + 2, a)
    q = P_expr(r, P_expr(r + 1, a))
    lhs = And(pr, pr2)
    rhs = P_expr(r, Xor(And(a, pr2), And(Xor(a, pr), q)))
    return lhs, rhs

def build_res_mask_conv(r: int, s1: int, s2: int) -> Tuple[Expr, Expr]:
    a, b = Var(0), Var(1)
    Er = E_expr(r)
    fa = Shl(Frob(r, a), s1)
    lhs = Clmul(fa, And(b, Shl(Er, s2)))
    rhs = And(Clmul(fa, b), Shl(Er, s1 + s2))
    return lhs, rhs

def build_sierpinski_inv(d: int) -> Tuple[Expr, Expr]:
    """clmul(allOnes^d, (1 ^ (1<<<1))^d) = 1."""
    lhs_a = ONE
    lhs_b = ONE
    delta1 = Xor(ONE, Shl(ONE, 1))
    for _ in range(d):
        lhs_a = Clmul(lhs_a, ALL_ONES)
        lhs_b = Clmul(lhs_b, delta1)
    return Clmul(lhs_a, lhs_b), ONE

def independent_check(name: str, e1: Expr, e2: Expr, nvars: int, max_w: int = 24) -> bool:
    rng = random.Random(12345)
    # Exhaustive for small widths w=0..3
    for w in range(4):
        m = bv_mask(w)
        if (1 << (w * nvars)) <= 256:
            for code in range(1 << (w * nvars)):
                env = {i: (code >> (w * i)) & m for i in range(nvars)}
                if eval_bv(w, env, e1) != eval_bv(w, env, e2):
                    print(f"  [ORACLE FAIL] {name} at w={w}, env={env}")
                    return False
    # Seeded stress tests up to max_w
    for w in [4, 5, 7, 8, 11, 16, max_w]:
        m = bv_mask(w)
        for _ in range(40):
            env = {i: rng.randint(0, m) for i in range(nvars)}
            if eval_bv(w, env, e1) != eval_bv(w, env, e2):
                print(f"  [ORACLE FAIL] {name} at w={w}, env={env}")
                return False
    return True

def main():
    print("=" * 76)
    print("CAUCHY-HADAMARD-FROBENIUS REFLECTION COMPILER & INDEPENDENT VERIFIER")
    print("=" * 76)

    cases = []

    # Family A: Z/2^r Z-Graded Carryless-Hadamard Convolution Splitting (r=1,2,3)
    for r in (1, 2, 3):
        for t in range(1 << r):
            e1, e2 = build_residue_conv_split(r, t)
            cert = compile_cartier_cert(r)
            cases.append((f"ResidueConvSplit(r={r}, t={t})", e1, e2, cert, 2, False))

    # Family B: Dyadic Rota-Baxter / Binary Ito-Leibniz Tower (base r=0, lane-safe -> ALL r, ALL w!)
    for n in (2, 3, 4):
        e1, e2 = build_ito_n(n, r=0)
        cert = Cert("cancelDelta", 0, Cert("normEq"))
        cases.append((f"BinaryIto(n={n}, base r=0 -> all r)", e1, e2, cert, n, True))

    # Direct higher-r Ito checks (r=1, 2)
    for r in (1, 2):
        e1, e2 = build_ito_n(2, r=r)
        cert = Cert("cancelDelta", r, Cert("normEq"))
        cases.append((f"BinaryIto(n=2, direct r={r})", e1, e2, cert, 2, False))

    # Dyadic Scale-Ladder & Two-Scale Ladder (base r=0, lane-safe -> ALL r, ALL w!)
    e1, e2 = build_self_scale_ladder(0)
    cases.append(("SelfScaleLadder(base r=0 -> all r)", e1, e2, Cert("cancelDelta", 0, Cert("normEq")), 1, True))

    e1, e2 = build_two_scale_ladder(0)
    cases.append(("TwoScaleLadder(base r=0 -> all r)", e1, e2, Cert("cancelDelta", 0, Cert("normEq")), 1, True))

    # Residue-Filtered Convolution Law (r=1,2; s2 < 2^r)
    for r, s1, s2 in [(1, 0, 0), (1, 0, 1), (1, 1, 1), (2, 1, 3)]:
        e1, e2 = build_res_mask_conv(r, s1, s2)
        cases.append((f"ResMaskConv(r={r}, s1={s1}, s2={s2})", e1, e2, compile_cartier_cert(r), 2, False))

    # Sierpinski / Pascal Inverse Cancellation (d=1..6)
    for d in range(1, 7):
        e1, e2 = build_sierpinski_inv(d)
        cases.append((f"SierpinskiInverse(d={d})", e1, e2, Cert("normEq"), 0, False))

    # Partition of Unity (r=1,2,3)
    for r in (1, 2, 3):
        Er = E_expr(r)
        lhs = ZERO
        for s in range(1 << r):
            term = Shl(Er, s)
            lhs = term if lhs == ZERO else Xor(lhs, term)
        cases.append((f"PartitionOfUnity(r={r})", lhs, ALL_ONES, Cert("normEq"), 0, False))

    passed = 0
    for name, e1, e2, cert, nvars, check_lane in cases:
        ok_cert = check_cert(e1, e2, cert)
        ok_oracle = independent_check(name, e1, e2, nvars)
        lane_msg = ""
        if check_lane:
            ls1, ls2 = is_lane_safe(e1), is_lane_safe(e2)
            assert ls1 and ls2, f"Expected lane-safe: {name}"
            # Also verify dilated instances r=1, 2, 3 against exact BitVec oracle!
            for rr in (1, 2, 3):
                assert independent_check(f"{name}@dilate({rr})", dilate_expr(rr, e1), dilate_expr(rr, e2), nvars)
            lane_msg = " + laneSafe -> ALL r"
        assert ok_cert and ok_oracle, f"FAILED {name}: cert={ok_cert}, oracle={ok_oracle}"
        passed += 1
        print(f"  [VERIFIED] {name:38s} | checkCert=True | oracle=PASS{lane_msg}")

    print(f"\nAll {passed}/{len(cases)} theorem certificates compiled & independently verified.\n")

    # ========================================================================
    # 8. Negative / Mutation Testing (Broken Certificates MUST Be Rejected!)
    # ========================================================================
    print("-" * 76)
    print("MUTATION & REJECTION TESTS (EVERY MUTANT MUST RETURN checkCert = False)")
    print("-" * 76)

    mutants = []
    # M1: Insufficient Cartier depth (depth 1 instead of 2 for r=2)
    e1, e2 = build_residue_conv_split(2, 1)
    mutants.append(("M1: Under-depth CartierSplit (d=1 for r=2)", e1, e2, compile_cartier_cert(1)))
    # M2: Insufficient cancelDelta stride (r=0 instead of r=1 for BinaryIto2 r=1)
    e1, e2 = build_ito_n(2, r=1)
    mutants.append(("M2: Insufficient cancelDelta stride (r=0 for r=1)", e1, e2, Cert("cancelDelta", 0, Cert("normEq"))))
    # M3: Dropped quadratic correction term (a & b) in Binary Ito-Leibniz
    a, b = Var(0), Var(1)
    bad_ito = P_expr(0, Xor(And(a, P_expr(0, b)), And(b, P_expr(0, a))))
    mutants.append(("M3: Classical Leibniz (missing a&b term)", And(P_expr(0, a), P_expr(0, b)), bad_ito, Cert("cancelDelta", 0, Cert("normEq"))))
    # M4: Sharpness violation s2 = 2^r in ResMaskConv (r=1, s1=0, s2=2)
    e1, e2 = build_res_mask_conv(1, 0, 2)
    mutants.append(("M4: ResMaskConv sharpness violation s2=2^r", e1, e2, compile_cartier_cert(2)))
    # M5: Corrupted transitivity midpoint
    e1, e2 = build_self_scale_ladder(0)
    mutants.append(("M5: Corrupted transitivity midpoint", e1, e2, Cert("trans", Var(0), Cert("normEq"), Cert("normEq"))))
    # M6: Non-orthogonal Frobenius shift collision (claiming F(a) & F(b) = 0)
    mutants.append(("M6: False Frobenius annihilation F(a)&F(b)=0", And(Frob(1, a), Frob(1, b)), ZERO, Cert("normEq")))
    # M7: Dropped term in ResidueConvSplit(r=1, t=0)
    mutants.append(("M7: Missing odd*odd term in ResidueConvSplit", And(Clmul(a, b), E_expr(1)), Clmul(And(a, E_expr(1)), And(b, E_expr(1))), compile_cartier_cert(1)))
    # M8: Non-lane-safe expression rejected by is_lane_safe
    non_lane = Clmul(a, b)
    assert not is_lane_safe(non_lane), "clmul(a, b) must NOT be lane-safe!"
    print(f"  [REJECTED] M0: is_lane_safe(clmul(a, b)) = False (exact safety gate)")

    for mname, me1, me2, mcert in mutants:
        res = check_cert(me1, me2, mcert)
        assert res is False, f"MUTANT NOT REJECTED: {mname}"
        print(f"  [REJECTED] {mname:48s} | checkCert=False")

    # ========================================================================
    # 9. Explicit Sharpness Counterexamples (Exact BitVec Witnesses)
    # ========================================================================
    print("\n" + "-" * 76)
    print("SHARPNESS COUNTEREXAMPLES (EXACT BITVEC WITNESSES OUTSIDE HYPOTHESES)")
    print("-" * 76)

    # S1: Binary Ito without quadratic (a & b) correction fails at w=1, a=1, b=1
    w, a_v, b_v = 1, 1, 1
    lhs = bv_Pr(w, 0, a_v) & bv_Pr(w, 0, b_v)
    rhs_no_ab = bv_Pr(w, 0, (a_v & bv_Pr(w, 0, b_v)) ^ (b_v & bv_Pr(w, 0, a_v)))
    assert lhs == 1 and rhs_no_ab == 0
    print(f"  [SHARP S1] Dropping (a&b) from BinaryIto fails at w={w}, a={a_v}, b={b_v}: LHS={lhs} != RHS={rhs_no_ab}")

    # S2: ResMaskConv fails when s2 = 2^r (r=1, s1=0, s2=2) at w=3, a=0b010, b=0b001
    w, a_v, b_v = 3, 0b010, 0b001
    E1 = bv_E(w, 1)
    lhs = bv_clmul(w, bv_frob(w, a_v, 1), b_v & bv_shl(w, E1, 2))
    rhs = bv_clmul(w, bv_frob(w, a_v, 1), b_v) & bv_shl(w, E1, 2)
    assert lhs == 0 and rhs == 0b100
    print(f"  [SHARP S2] ResMaskConv with s2=2^r (r=1,s2=2) fails at w={w}, a={bin(a_v)}, b={bin(b_v)}: LHS={bin(lhs)} != RHS={bin(rhs)}")

    # S3: ResidueConvSplit fails if clmul is replaced by ordinary carried multiplication *
    w, a_v, b_v = 4, 0b0011, 0b0011  # 3 * 3 = 9 = 0b1001; odd*odd carries into bit 1!
    E1 = bv_E(w, 1)
    O1 = bv_shl(w, E1, 1)
    m = bv_mask(w)
    lhs_mul = ((a_v * b_v) & m) & E1
    rhs_mul = (((a_v & E1) * (b_v & E1)) & m) ^ (((a_v & O1) * (b_v & O1)) & m)
    assert lhs_mul == 0b0001 and rhs_mul == 0b0101
    print(f"  [SHARP S3] Carried '*' breaks ResidueConvSplit(r=1,t=0) at w={w}, a=3, b=3: LHS={bin(lhs_mul)} != RHS={bin(rhs_mul)}")

    # S4: Right-Shift Frobenius Truncation Law fails without mask &&& (allOnes >>> (s*2^r))
    w, a_v = 4, 0b0100
    lhs_shr = bv_shr(w, bv_frob(w, a_v, 1), 2)
    rhs_nomask = bv_frob(w, bv_shr(w, a_v, 1), 1)
    rhs_masked = rhs_nomask & bv_shr(w, bv_mask(w), 2)
    assert lhs_shr == 0b0000 and rhs_nomask == 0b0100 and rhs_masked == 0b0000
    print(f"  [SHARP S4] ShrFrobTrunc without mask fails at w={w}, a={bin(a_v)}: LHS={bin(lhs_shr)} != unmasked={bin(rhs_nomask)} (masked={bin(rhs_masked)})")

    # S5: Non-power-of-2 period-3 mask breaks ResidueConvSplit (characteristic 2 requires 2^r)
    # Period-3 masks M0 = ...1001001, M1 = ...010010, M2 = ...100100
    w, a_v, b_v = 4, 0b1001, 0b0011
    M0 = sum((1 << k) for k in range(w) if k % 3 == 0)
    M1 = sum((1 << k) for k in range(w) if k % 3 == 1)
    M2 = sum((1 << k) for k in range(w) if k % 3 == 2)
    # Check Frob-Hadamard: clmul(M0, M0) != M0 for period 3!
    frob_M0 = bv_clmul(w, M0, M0)
    assert frob_M0 != M0
    print(f"  [SHARP S5] Period-3 mask M0={bin(M0)} is NOT Frobenius-closed: clmul(M0,M0)={bin(frob_M0)} != M0")

    # S6: Non-lane-safe identity fails naive dyadic dilation!
    # At r=0: clmul(a, b) ^ clmul(b, a) = 0 holds, wait that's still true;
    # Use: clmul(a, a) & (1 <<< 1) = 0 vs naive shift: what about clmul(a, b) & 1 = a & b & 1?
    # Better: at r=0, clmul(a, b) = clmul(a, b) — what about (clmul(a, allOnes) & clmul(b, allOnes))? That IS lane-safe.
    # Take: clmul(a, 1 ^ (1<<<1)) & 1 = a & 1 (lane-safe).
    # Take a NON-lane-safe identity that holds at r=0 ONLY because allOnes=1+x+..., namely:
    # (clmul(a, b) & (allOnes ^ 1)) vs ... clmul(a, b) <<< 1 = clmul(a <<< 1, b): still holds!
    # Take: clmul(a, b) & allOnes = clmul(a, b)! If you naively dilate allOnes -> E_1 without dilating clmul(a, b),
    # you get clmul(a, b) & E_1 = clmul(a, b), which FAILS at w=2, a=0b10, b=0b01!
    w, a_v, b_v = 2, 0b10, 0b01
    lhs_nl = bv_clmul(w, a_v, b_v) & bv_E(w, 1)
    rhs_nl = bv_clmul(w, a_v, b_v)
    assert lhs_nl == 0b00 and rhs_nl == 0b10
    print(f"  [SHARP S6] Naive dilation of non-lane-safe (clmul(a,b)&allOnes = clmul(a,b)) fails at w={w}, a={bin(a_v)}, b={bin(b_v)}: LHS={bin(lhs_nl)} != RHS={bin(rhs_nl)}")

    print("\nALL CHECKS PASSED WITH ZERO FLOATING-POINT VALUES.")

if __name__ == "__main__":
    main()
