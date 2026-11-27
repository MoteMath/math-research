#!/usr/bin/env python3
"""
Exact Pure-Silicon Dyadic Ball-Arithmetic & Contraction Enclosure Compiler
(Zero floating-point values anywhere — uses Python arbitrary-precision int & Fraction only.)

Synthesizes finite binary subdivision + contraction certificates for:
  1. Universal Binary-Scaled Halley Square-Root Map:
       H_a(x) = x - 2x(x^2 - a)/(3x^2 + a) = x(x^2 + 3a)/(3x^2 + a)
     certified on (a, x) in [1, 4] x [15/16, 17/8] with q = 7/8,
     lifting via exact binary exponent normalization A = 4^k * a to ALL A in Q_{>0} and ALL n in Nat!
  2. Parametric Bring Radical Quintic Newton Map (unsolvable by radicals!):
       F_p(x) = x - (x^5 + (1 + p)x - 1)/(1 + p + 5x^4) = (1 + 4x^5)/(1 + p + 5x^4)
     certified on p in [0, 1/2], x in [1/2, 1] with q = 7/8 (covers p = 0 and all p = 2^-k, k >= 1),
     PLUS a tight 2^(-20) Bring radical enclosure at p = 0 with q = 1/65536!
  3. Non-Monotone Parametric Logistic Band across the turning point x = 1/2:
       F_mu(x) = mu * x * (1 - x)
     certified on mu in [19/8, 41/16], x in [15/32, 21/32] with q = 7/8,
     discharging exact convergence to x*(mu) = 1 - 1/mu for all mu in the band and all n in Nat!
  4. Oscillatory Alternating Direct Bring Map near the |G'| = 1 stability boundary:
       G(x) = 1 / (1 + x^4)
     certified on [772/1024, 774/1024] with q = 63/64 (negative slope G'(alpha) ≈ -0.9804).

Also runs:
  - Independent exact rational (Fraction) replay of orbits and residual decay
  - Sharpness / boundary falsification witnesses (exact rational counterexamples)
  - Negative / mutation test suite verifying broken certificates are rejected
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Optional, Tuple, Union


# ============================================================================
# 1. Exact Dyadic Ball: [(m - r) / 2^e, (m + r) / 2^e]
# ============================================================================

def floor_div(a: int, b: int) -> int:
    """Exact Euclidean floor division (matches Lean Int.ediv for b > 0)."""
    assert b > 0
    return a // b


def ceil_div(a: int, b: int) -> int:
    """Exact ceiling division for b > 0: floor_div(a + b - 1, b)."""
    assert b > 0
    return (a + b - 1) // b


@dataclass(frozen=True)
class DyadicBall:
    m: int  # center mantissa: center = m / 2^e
    e: int  # binary exponent >= 0
    r: int  # radius mantissa >= 0: radius = r / 2^e

    def __post_init__(self):
        assert self.e >= 0 and self.r >= 0

    @property
    def lo(self) -> Fraction:
        return Fraction(self.m - self.r, 1 << self.e)

    @property
    def hi(self) -> Fraction:
        return Fraction(self.m + self.r, 1 << self.e)

    @property
    def mid(self) -> Fraction:
        return Fraction(self.m, 1 << self.e)

    @property
    def rad(self) -> Fraction:
        return Fraction(self.r, 1 << self.e)

    def contains(self, q: Fraction) -> bool:
        scale = 1 << self.e
        lhs = (self.m - self.r) * q.denominator
        mid = q.numerator * scale
        rhs = (self.m + self.r) * q.denominator
        return lhs <= mid <= rhs

    def round_to(self, p: int) -> DyadicBall:
        """Exact outward rounding to exponent p (matches Lean DyadicBall.roundTo)."""
        assert p >= 0
        if self.e <= p:
            k = p - self.e
            return DyadicBall(self.m << k, p, self.r << k)
        else:
            k = self.e - p
            s = 1 << k
            lo_int = floor_div(self.m - self.r, s)
            hi_int = ceil_div(self.m + self.r, s)
            m_new = floor_div(lo_int + hi_int, 2)
            r_new = hi_int - m_new
            assert r_new >= 0
            return DyadicBall(m_new, p, r_new)

    def bisect_left(self) -> DyadicBall:
        return DyadicBall(2 * self.m - self.r, self.e + 1, self.r)

    def bisect_right(self) -> DyadicBall:
        return DyadicBall(2 * self.m + self.r, self.e + 1, self.r)

    def midpoint_ball(self) -> DyadicBall:
        return DyadicBall(self.m, self.e, 0)

    def radius_ball(self) -> DyadicBall:
        return DyadicBall(0, self.e, self.r)

    def subset(self, other: DyadicBall) -> bool:
        """Decidable exact containment: self ⊆ other."""
        if self.e <= other.e:
            k = other.e - self.e
            s = 1 << k
            return ((other.m - other.r) <= (self.m - self.r) * s and
                    (self.m + self.r) * s <= (other.m + other.r))
        else:
            k = self.e - other.e
            s = 1 << k
            return ((other.m - other.r) * s <= (self.m - self.r) and
                    (self.m + self.r) <= (other.m + other.r) * s)

    def max_abs_le(self, q_num: int, q_exp: int) -> bool:
        """Check |x| <= q_num / 2^q_exp for all x in self."""
        max_m = abs(self.m) + self.r
        if self.e <= q_exp:
            return max_m * (1 << (q_exp - self.e)) <= q_num
        else:
            return max_m <= q_num * (1 << (self.e - q_exp))

    def to_lean(self) -> str:
        m_str = f"({self.m})" if self.m < 0 else str(self.m)
        return f"⟨{m_str}, {self.e}, {self.r}⟩"


def ball_from_interval(lo_num: int, hi_num: int, e: int) -> DyadicBall:
    assert lo_num <= hi_num and e >= 0
    m = floor_div(lo_num + hi_num, 2)
    r = hi_num - m
    return DyadicBall(m, e, r)


def ball_const_int(z: int) -> DyadicBall:
    return DyadicBall(z, 0, 0)


def ball_const_dyadic(m: int, e: int) -> DyadicBall:
    return DyadicBall(m, e, 0)


def ball_neg(a: DyadicBall) -> DyadicBall:
    return DyadicBall(-a.m, a.e, a.r)


def ball_add(a: DyadicBall, b: DyadicBall, prec: int) -> DyadicBall:
    if a.e <= b.e:
        k = b.e - a.e
        raw = DyadicBall((a.m << k) + b.m, b.e, (a.r << k) + b.r)
    else:
        k = a.e - b.e
        raw = DyadicBall(a.m + (b.m << k), a.e, a.r + (b.r << k))
    return raw.round_to(prec)


def ball_sub(a: DyadicBall, b: DyadicBall, prec: int) -> DyadicBall:
    return ball_add(a, ball_neg(b), prec)


def ball_mul(a: DyadicBall, b: DyadicBall, prec: int) -> DyadicBall:
    m_new = a.m * b.m
    r_new = abs(a.m) * b.r + abs(b.m) * a.r + a.r * b.r
    return DyadicBall(m_new, a.e + b.e, r_new).round_to(prec)


def ball_sqr(a: DyadicBall, prec: int) -> DyadicBall:
    lo = a.m - a.r
    hi = a.m + a.r
    if lo >= 0:
        sq_lo, sq_hi = lo * lo, hi * hi
    elif hi <= 0:
        sq_lo, sq_hi = hi * hi, lo * lo
    else:
        sq_lo = 0
        sq_hi = max(lo * lo, hi * hi)
    return ball_from_interval(sq_lo, sq_hi, 2 * a.e).round_to(prec)


def ball_inv_pos(a: DyadicBall, prec: int) -> Optional[DyadicBall]:
    lo = a.m - a.r
    hi = a.m + a.r
    if lo <= 0:
        return None
    num = 1 << (a.e + prec)
    inv_lo = floor_div(num, hi)
    inv_hi = ceil_div(num, lo)
    return ball_from_interval(inv_lo, inv_hi, prec)


# ============================================================================
# 2. Expression AST + Exact Rational Semantics + Algebraic Jet/Centered Balls
# ============================================================================

class Expr:
    def to_lean(self) -> str:
        raise NotImplementedError


@dataclass(frozen=True)
class Var(Expr):
    def to_lean(self) -> str:
        return ".var"


@dataclass(frozen=True)
class Param(Expr):
    def to_lean(self) -> str:
        return ".param"


@dataclass(frozen=True)
class ConstInt(Expr):
    z: int
    def to_lean(self) -> str:
        z_str = f"({self.z})" if self.z < 0 else str(self.z)
        return f"(.constInt {z_str})"


@dataclass(frozen=True)
class ConstDyadic(Expr):
    m: int
    e: int
    def to_lean(self) -> str:
        m_str = f"({self.m})" if self.m < 0 else str(self.m)
        return f"(.constDyadic {m_str} {self.e})"


@dataclass(frozen=True)
class Add(Expr):
    a: Expr
    b: Expr
    def to_lean(self) -> str:
        return f"(.add {self.a.to_lean()} {self.b.to_lean()})"


@dataclass(frozen=True)
class Sub(Expr):
    a: Expr
    b: Expr
    def to_lean(self) -> str:
        return f"(.sub {self.a.to_lean()} {self.b.to_lean()})"


@dataclass(frozen=True)
class Neg(Expr):
    a: Expr
    def to_lean(self) -> str:
        return f"(.neg {self.a.to_lean()})"


@dataclass(frozen=True)
class Mul(Expr):
    a: Expr
    b: Expr
    def to_lean(self) -> str:
        return f"(.mul {self.a.to_lean()} {self.b.to_lean()})"


@dataclass(frozen=True)
class Sqr(Expr):
    a: Expr
    def to_lean(self) -> str:
        return f"(.sqr {self.a.to_lean()})"


@dataclass(frozen=True)
class Inv(Expr):
    a: Expr
    def to_lean(self) -> str:
        return f"(.inv {self.a.to_lean()})"


def eval_q(expr: Expr, p: Fraction, x: Fraction) -> Optional[Fraction]:
    if isinstance(expr, Var):
        return x
    if isinstance(expr, Param):
        return p
    if isinstance(expr, ConstInt):
        return Fraction(expr.z, 1)
    if isinstance(expr, ConstDyadic):
        return Fraction(expr.m, 1 << expr.e)
    if isinstance(expr, Neg):
        v = eval_q(expr.a, p, x)
        return None if v is None else -v
    if isinstance(expr, Add):
        va, vb = eval_q(expr.a, p, x), eval_q(expr.b, p, x)
        return None if (va is None or vb is None) else va + vb
    if isinstance(expr, Sub):
        va, vb = eval_q(expr.a, p, x), eval_q(expr.b, p, x)
        return None if (va is None or vb is None) else va - vb
    if isinstance(expr, Mul):
        va, vb = eval_q(expr.a, p, x), eval_q(expr.b, p, x)
        return None if (va is None or vb is None) else va * vb
    if isinstance(expr, Sqr):
        va = eval_q(expr.a, p, x)
        return None if va is None else va * va
    if isinstance(expr, Inv):
        va = eval_q(expr.a, p, x)
        if va is None or va <= 0:
            return None
        return Fraction(1, 1) / va
    raise ValueError(expr)


def eval_ball(prec: int, expr: Expr, P: DyadicBall, X: DyadicBall) -> Optional[DyadicBall]:
    if isinstance(expr, Var):
        return X.round_to(prec)
    if isinstance(expr, Param):
        return P.round_to(prec)
    if isinstance(expr, ConstInt):
        return ball_const_int(expr.z)
    if isinstance(expr, ConstDyadic):
        return ball_const_dyadic(expr.m, expr.e)
    if isinstance(expr, Neg):
        v = eval_ball(prec, expr.a, P, X)
        return None if v is None else ball_neg(v)
    if isinstance(expr, Add):
        va = eval_ball(prec, expr.a, P, X)
        vb = eval_ball(prec, expr.b, P, X)
        return None if (va is None or vb is None) else ball_add(va, vb, prec)
    if isinstance(expr, Sub):
        va = eval_ball(prec, expr.a, P, X)
        vb = eval_ball(prec, expr.b, P, X)
        return None if (va is None or vb is None) else ball_sub(va, vb, prec)
    if isinstance(expr, Mul):
        va = eval_ball(prec, expr.a, P, X)
        vb = eval_ball(prec, expr.b, P, X)
        return None if (va is None or vb is None) else ball_mul(va, vb, prec)
    if isinstance(expr, Sqr):
        va = eval_ball(prec, expr.a, P, X)
        return None if va is None else ball_sqr(va, prec)
    if isinstance(expr, Inv):
        va = eval_ball(prec, expr.a, P, X)
        return None if va is None else ball_inv_pos(va, prec)
    raise ValueError(expr)


def eval_jet_ball(prec: int, expr: Expr, P: DyadicBall, X: DyadicBall) -> Optional[Tuple[DyadicBall, DyadicBall]]:
    if isinstance(expr, Var):
        return (X.round_to(prec), ball_const_int(1))
    if isinstance(expr, Param):
        return (P.round_to(prec), ball_const_int(0))
    if isinstance(expr, ConstInt):
        return (ball_const_int(expr.z), ball_const_int(0))
    if isinstance(expr, ConstDyadic):
        return (ball_const_dyadic(expr.m, expr.e), ball_const_int(0))
    if isinstance(expr, Neg):
        res = eval_jet_ball(prec, expr.a, P, X)
        if res is None:
            return None
        va, sa = res
        return (ball_neg(va), ball_neg(sa))
    if isinstance(expr, Add):
        ra = eval_jet_ball(prec, expr.a, P, X)
        rb = eval_jet_ball(prec, expr.b, P, X)
        if ra is None or rb is None:
            return None
        (va, sa), (vb, sb) = ra, rb
        return (ball_add(va, vb, prec), ball_add(sa, sb, prec))
    if isinstance(expr, Sub):
        ra = eval_jet_ball(prec, expr.a, P, X)
        rb = eval_jet_ball(prec, expr.b, P, X)
        if ra is None or rb is None:
            return None
        (va, sa), (vb, sb) = ra, rb
        return (ball_sub(va, vb, prec), ball_sub(sa, sb, prec))
    if isinstance(expr, Mul):
        ra = eval_jet_ball(prec, expr.a, P, X)
        rb = eval_jet_ball(prec, expr.b, P, X)
        if ra is None or rb is None:
            return None
        (va, sa), (vb, sb) = ra, rb
        v = ball_mul(va, vb, prec)
        s = ball_add(ball_mul(sa, vb, prec), ball_mul(va, sb, prec), prec)
        return (v, s)
    if isinstance(expr, Sqr):
        ra = eval_jet_ball(prec, expr.a, P, X)
        if ra is None:
            return None
        va, sa = ra
        v = ball_sqr(va, prec)
        two_va = ball_mul(ball_const_int(2), va, prec)
        s = ball_mul(two_va, sa, prec)
        return (v, s)
    if isinstance(expr, Inv):
        ra = eval_jet_ball(prec, expr.a, P, X)
        if ra is None:
            return None
        va, sa = ra
        inv_v = ball_inv_pos(va, prec)
        if inv_v is None:
            return None
        inv_prod = ball_mul(inv_v, inv_v, prec)
        s = ball_neg(ball_mul(sa, inv_prod, prec))
        return (inv_v, s)
    raise ValueError(expr)


def eval_centered_ball(prec: int, expr: Expr, P: DyadicBall, X: DyadicBall) -> Optional[Tuple[DyadicBall, DyadicBall]]:
    jet = eval_jet_ball(prec, expr, P, X)
    if jet is None:
        return None
    _, s = jet
    v_mid = eval_ball(prec, expr, P, X.midpoint_ball())
    if v_mid is None:
        return None
    delta = ball_mul(s, X.radius_ball(), prec)
    v_centered = ball_add(v_mid, delta, prec)
    return (v_centered, s)


# ============================================================================
# 3. Subdivision Trees & Parametric Contraction Certificate Checker + Synthesizer
# ============================================================================

@dataclass(frozen=True)
class StateLeaf:
    prec: int
    use_centered: bool

    def to_lean(self) -> str:
        uc = "true" if self.use_centered else "false"
        return f"(.leaf {self.prec} {uc})"

    def leaf_count(self) -> int:
        return 1


@dataclass(frozen=True)
class StateSplit:
    left: StateTree
    right: StateTree

    def to_lean(self) -> str:
        return f"(.split {self.left.to_lean()} {self.right.to_lean()})"

    def leaf_count(self) -> int:
        return self.left.leaf_count() + self.right.leaf_count()


StateTree = Union[StateLeaf, StateSplit]


@dataclass(frozen=True)
class ParamLeaf:
    state_tree: StateTree

    def to_lean(self) -> str:
        return f"(.pleaf {self.state_tree.to_lean()})"

    def total_leaves(self) -> int:
        return self.state_tree.leaf_count()


@dataclass(frozen=True)
class ParamSplit:
    left: ParamTree
    right: ParamTree

    def to_lean(self) -> str:
        return f"(.psplit {self.left.to_lean()} {self.right.to_lean()})"

    def total_leaves(self) -> int:
        return self.left.total_leaves() + self.right.total_leaves()


ParamTree = Union[ParamLeaf, ParamSplit]


@dataclass(frozen=True)
class ParamContractionCert:
    expr: Expr
    p0: DyadicBall
    b0: DyadicBall
    q_num: int
    q_exp: int
    tree: ParamTree


def check_state_leaf(expr: Expr, P: DyadicBall, B0: DyadicBall, B: DyadicBall,
                     q_num: int, q_exp: int, prec: int, use_centered: bool) -> bool:
    res = eval_centered_ball(prec, expr, P, B) if use_centered else eval_jet_ball(prec, expr, P, B)
    if res is None:
        return False
    v, s = res
    return v.subset(B0) and s.max_abs_le(q_num, q_exp)


def check_state_tree(expr: Expr, P: DyadicBall, B0: DyadicBall, B: DyadicBall,
                     q_num: int, q_exp: int, tree: StateTree) -> bool:
    if isinstance(tree, StateLeaf):
        return check_state_leaf(expr, P, B0, B, q_num, q_exp, tree.prec, tree.use_centered)
    return (check_state_tree(expr, P, B0, B.bisect_left(), q_num, q_exp, tree.left) and
            check_state_tree(expr, P, B0, B.bisect_right(), q_num, q_exp, tree.right))


def check_param_tree(expr: Expr, P: DyadicBall, B0: DyadicBall,
                     q_num: int, q_exp: int, tree: ParamTree) -> bool:
    if isinstance(tree, ParamLeaf):
        return check_state_tree(expr, P, B0, B0, q_num, q_exp, tree.state_tree)
    return (check_param_tree(expr, P.bisect_left(), B0, q_num, q_exp, tree.left) and
            check_param_tree(expr, P.bisect_right(), B0, q_num, q_exp, tree.right))


def check_param_contraction(cert: ParamContractionCert) -> bool:
    if not (cert.q_num < (1 << cert.q_exp)):
        return False
    return check_param_tree(cert.expr, cert.p0, cert.b0, cert.q_num, cert.q_exp, cert.tree)


def synth_state_tree(expr: Expr, P: DyadicBall, B0: DyadicBall, B: DyadicBall,
                     q_num: int, q_exp: int, prec: int, max_depth: int) -> Optional[StateTree]:
    if check_state_leaf(expr, P, B0, B, q_num, q_exp, prec, False):
        return StateLeaf(prec, False)
    if check_state_leaf(expr, P, B0, B, q_num, q_exp, prec, True):
        return StateLeaf(prec, True)
    if max_depth <= 0:
        return None
    left = synth_state_tree(expr, P, B0, B.bisect_left(), q_num, q_exp, prec, max_depth - 1)
    if left is None:
        return None
    right = synth_state_tree(expr, P, B0, B.bisect_right(), q_num, q_exp, prec, max_depth - 1)
    if right is None:
        return None
    return StateSplit(left, right)


def synth_param_tree(expr: Expr, P: DyadicBall, B0: DyadicBall,
                     q_num: int, q_exp: int, prec: int,
                     max_param_depth: int, max_state_depth: int) -> Optional[ParamTree]:
    st = synth_state_tree(expr, P, B0, B0, q_num, q_exp, prec, max_state_depth)
    if st is not None:
        return ParamLeaf(st)
    if max_param_depth <= 0:
        return None
    left = synth_param_tree(expr, P.bisect_left(), B0, q_num, q_exp, prec, max_param_depth - 1, max_state_depth)
    if left is None:
        return None
    right = synth_param_tree(expr, P.bisect_right(), B0, q_num, q_exp, prec, max_param_depth - 1, max_state_depth)
    if right is None:
        return None
    return ParamSplit(left, right)


# ============================================================================
# 4. Target Nonlinear Maps (Residual-Update Forms for Tight Slope Cancellation)
# ============================================================================

def expr_halley_res() -> Expr:
    """
    Halley's cubic square-root map in residual-update form:
      H_a(x) = x - 2*x*(x^2 - a) / (3*x^2 + a)  [= x*(x^2 + 3a)/(3*x^2 + a)]
    """
    x, a = Var(), Param()
    x2 = Sqr(x)
    num = Mul(ConstInt(2), Mul(x, Sub(x2, a)))
    den = Add(Mul(ConstInt(3), x2), a)
    return Sub(x, Mul(num, Inv(den)))


def expr_bring_newton_res() -> Expr:
    """
    Newton's map for the parametric Bring quintic x^5 + (1 + p)*x - 1 = 0:
      F_p(x) = x - (x^5 + (1 + p)*x - 1) / (1 + p + 5*x^4)  [= (1 + 4x^5)/(1 + p + 5x^4)]
    """
    x, p = Var(), Param()
    x2 = Sqr(x)
    x4 = Sqr(x2)
    x5 = Mul(x, x4)
    poly = Sub(Add(x5, Mul(Add(ConstInt(1), p), x)), ConstInt(1))
    den = Add(Add(ConstInt(1), p), Mul(ConstInt(5), x4))
    return Sub(x, Mul(poly, Inv(den)))


def expr_logistic() -> Expr:
    """Non-monotone logistic map F_mu(x) = mu * x * (1 - x)."""
    x, mu = Var(), Param()
    return Mul(mu, Mul(x, Sub(ConstInt(1), x)))


def expr_bring_direct() -> Expr:
    """Direct alternating fixed-point map for x^5 + x - 1 = 0: G(x) = 1 / (1 + x^4)."""
    x = Var()
    x4 = Sqr(Sqr(x))
    return Inv(Add(ConstInt(1), x4))


# ============================================================================
# 5. Synthesis, Exact Rational Replay, Sharpness & Mutation Suite
# ============================================================================

def exact_bit_log2(frac: Fraction) -> int:
    """Integer floor(log2(frac)) for frac > 0 using exact bit lengths."""
    assert frac > 0
    # Find k such that 2^k <= frac < 2^(k+1)
    k = frac.numerator.bit_length() - frac.denominator.bit_length()
    if k >= 0:
        if frac.numerator < (frac.denominator << k):
            k -= 1
    else:
        if (frac.numerator << (-k)) < frac.denominator:
            k -= 1
    return k


def synthesize_all():
    halley = expr_halley_res()
    P_halley = DyadicBall(5, 1, 3)     # [1, 4]
    B_halley = DyadicBall(49, 5, 19)   # [15/16, 17/8], strictly contains [1, 2]
    tree_h = synth_param_tree(halley, P_halley, B_halley, 7, 3, prec=14, max_param_depth=5, max_state_depth=5)
    assert tree_h is not None
    cert_halley = ParamContractionCert(halley, P_halley, B_halley, 7, 3, tree_h)
    assert check_param_contraction(cert_halley)

    bring = expr_bring_newton_res()
    P_bring = DyadicBall(1, 2, 1)      # [0, 1/2]
    B_bring = DyadicBall(3, 2, 1)      # [1/2, 1]
    tree_b = synth_param_tree(bring, P_bring, B_bring, 7, 3, prec=14, max_param_depth=4, max_state_depth=5)
    assert tree_b is not None
    cert_bring = ParamContractionCert(bring, P_bring, B_bring, 7, 3, tree_b)
    assert check_param_contraction(cert_bring)

    P_zero = DyadicBall(0, 0, 0)
    B_bring_tight = DyadicBall(791547, 20, 1)  # radius 2^(-20) around Bring radical
    tree_bt = synth_param_tree(bring, P_zero, B_bring_tight, 1, 16, prec=32, max_param_depth=0, max_state_depth=2)
    assert tree_bt is not None
    cert_bring_tight = ParamContractionCert(bring, P_zero, B_bring_tight, 1, 16, tree_bt)
    assert check_param_contraction(cert_bring_tight)

    logistic = expr_logistic()
    P_log = DyadicBall(79, 5, 3)       # [19/8, 41/16]
    B_log = DyadicBall(18, 5, 3)       # [15/32, 21/32], contains turning point x = 1/2
    tree_l = synth_param_tree(logistic, P_log, B_log, 7, 3, prec=12, max_param_depth=3, max_state_depth=5)
    assert tree_l is not None
    cert_log = ParamContractionCert(logistic, P_log, B_log, 7, 3, tree_l)
    assert check_param_contraction(cert_log)

    bring_dir = expr_bring_direct()
    B_alt = DyadicBall(773, 10, 1)     # [772/1024, 774/1024]
    tree_a = synth_param_tree(bring_dir, P_zero, B_alt, 63, 6, prec=18, max_param_depth=0, max_state_depth=4)
    assert tree_a is not None
    cert_alt = ParamContractionCert(bring_dir, P_zero, B_alt, 63, 6, tree_a)
    assert check_param_contraction(cert_alt)

    return {
        "halley": cert_halley,
        "bring": cert_bring,
        "bring_tight": cert_bring_tight,
        "logistic": cert_log,
        "bring_alt": cert_alt,
    }


def main():
    print("=" * 72)
    print("PURE-SILICON DYADIC BALL & CONTRACTION ENCLOSURE COMPILER (ZERO FLOAT)")
    print("=" * 72)

    certs = synthesize_all()

    print("\n--- 1. Synthesized Finite Binary Certificates ---")
    for name, c in certs.items():
        naive_dir = check_state_leaf(c.expr, c.p0, c.b0, c.b0, c.q_num, c.q_exp, 14, False)
        naive_cen = check_state_leaf(c.expr, c.p0, c.b0, c.b0, c.q_num, c.q_exp, 14, True)
        print(f"  {name:12s} | P0=[{c.p0.lo}, {c.p0.hi}] | B0=[{c.b0.lo}, {c.b0.hi}] "
              f"| q={c.q_num}/{1<<c.q_exp} | leaves={c.tree.total_leaves():2d} "
              f"| naive1(dir/cen)=({naive_dir}/{naive_cen})")

    print("\n--- 2. Independent Exact Rational (Fraction) Replay ---")
    # Halley binary-scaled square root across arbitrary positive rationals A > 0
    for A_val, k_shift in [(Fraction(2, 1), 0), (Fraction(12, 1), 1), (Fraction(3, 8), -1), (Fraction(1000, 7), 3)]:
        scale = Fraction(4, 1) ** k_shift if k_shift >= 0 else Fraction(1, 4 ** (-k_shift))
        a = A_val / scale
        assert 1 <= a <= 4
        two_k = Fraction(2, 1) ** k_shift if k_shift >= 0 else Fraction(1, 2 ** (-k_shift))
        x = Fraction(3, 2) * two_k
        for _ in range(5):
            x = x - (2 * x * (x * x - A_val)) / (3 * x * x + A_val)
        err = abs(x * x - A_val)
        print(f"  Halley A={str(A_val):7s} (k={k_shift:2d}, a={str(a):7s}): after 5 steps |x_5^2 - A| < 2^{exact_bit_log2(err)+1}")

    # Bring quintic family for p = 0, 1/2, 1/4, 1/8, 1/16, 1/32
    bring = certs["bring"].expr
    for p_val in [Fraction(0), Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 32)]:
        x = Fraction(3, 4)
        for _ in range(4):
            x = eval_q(bring, p_val, x)
            assert certs["bring"].b0.contains(x)
        res = abs(x**5 + (1 + p_val) * x - 1)
        print(f"  Bring  p={str(p_val):5s}: after 4 steps |x_4^5 + (1+p)x_4 - 1| < 2^{exact_bit_log2(res)+1}")

    # Logistic band convergence to exact fixed point x*(mu) = 1 - 1/mu
    logistic = certs["logistic"].expr
    for mu_val in [Fraction(19, 8), Fraction(5, 2), Fraction(41, 16)]:
        x_star = 1 - Fraction(1, 1) / mu_val
        assert certs["logistic"].b0.contains(x_star)
        assert eval_q(logistic, mu_val, x_star) == x_star
        x = Fraction(1, 2)  # starts right at the turning point!
        d0 = abs(x - x_star)
        for step in range(1, 16):
            x = eval_q(logistic, mu_val, x)
            assert certs["logistic"].b0.contains(x)
            assert abs(x - x_star) <= (Fraction(7, 8) ** step) * d0
        print(f"  Logistic mu={str(mu_val):5s} (x*={x_star}): 15 iterates from x0=1/2 strictly obey (7/8)^n decay")

    # Direct Bring alternating oscillation
    bring_dir = certs["bring_alt"].expr
    x = Fraction(772, 1024)
    diffs = []
    for _ in range(6):
        x_next = eval_q(bring_dir, Fraction(0), x)
        assert certs["bring_alt"].b0.contains(x_next)
        diffs.append(x_next - x)
        x = x_next
    # Verify genuine sign alternation!
    for i in range(len(diffs) - 1):
        assert diffs[i] * diffs[i + 1] < 0
    print(f"  Direct Bring G(x)=1/(1+x^4): 6 iterates strictly alternate signs inside [772/1024, 774/1024]!")

    print("\n--- 3. Sharpness / Boundary Falsification Witnesses (Exact Rational) ---")
    # Sharpness 1: Halley derivative at (a=4, x=1) is 27/49 > 1/2
    h4_1 = eval_q(certs["halley"].expr, Fraction(4), Fraction(1))
    h4_eps = eval_q(certs["halley"].expr, Fraction(4), Fraction(101, 100))
    sec_h4 = abs(h4_eps - h4_1) / Fraction(1, 100)
    assert sec_h4 > Fraction(1, 2)
    print(f"  [Sharpness 1] Halley (a=4): exact secant on [1, 101/100] = {sec_h4} > 1/2 (true max 27/49)")

    # Sharpness 2: Logistic at mu = 7/2 has EXACT rational 2-cycle {3/7, 6/7}
    mu_sharp = Fraction(7, 2)
    c1, c2 = Fraction(3, 7), Fraction(6, 7)
    assert eval_q(logistic, mu_sharp, c1) == c2 and eval_q(logistic, mu_sharp, c2) == c1
    print(f"  [Sharpness 2] Logistic (mu=7/2): exact rational 2-cycle F(3/7) = {c2}, F(6/7) = {c1}")

    # Sharpness 3: Direct Bring G(x) = 1/(1+x^4) expands on [4/5, 81/100]
    g_a = eval_q(bring_dir, Fraction(0), Fraction(4, 5))
    g_b = eval_q(bring_dir, Fraction(0), Fraction(81, 100))
    sec_g = abs(g_b - g_a) / Fraction(1, 100)
    assert sec_g > 1
    print(f"  [Sharpness 3] Direct Bring G(x)=1/(1+x^4): exact secant on [4/5, 81/100] = {sec_g} > 1 (expands)")

    print("\n--- 4. Negative / Mutation Certificate Rejection Tests ---")
    bad_tests = [
        ("Halley q=1/2 (below true max 27/49)",
         ParamContractionCert(certs["halley"].expr, certs["halley"].p0, certs["halley"].b0, 1, 1, certs["halley"].tree)),
        ("Halley q=1 (not strict contraction)",
         ParamContractionCert(certs["halley"].expr, certs["halley"].p0, certs["halley"].b0, 1, 0, certs["halley"].tree)),
        ("Halley coarse 1-leaf tree (fails without subdivision)",
         ParamContractionCert(certs["halley"].expr, certs["halley"].p0, certs["halley"].b0, 7, 3, ParamLeaf(StateLeaf(14, True)))),
        ("Logistic at mu=7/2 (period-2 cycle breaks contraction)",
         ParamContractionCert(logistic, DyadicBall(7, 1, 0), certs["logistic"].b0, 7, 3, certs["logistic"].tree)),
        ("Bring Newton escaped domain [1/4, 1/2] (not self-mapped)",
         ParamContractionCert(bring, certs["bring"].p0, DyadicBall(3, 3, 1), 7, 3, certs["bring"].tree)),
        ("Singular denominator 1/(x - 3/4) on [1/2, 1]",
         ParamContractionCert(Inv(Sub(Var(), ConstDyadic(3, 2))), DyadicBall(0, 0, 0), certs["bring"].b0, 1, 1, ParamLeaf(StateLeaf(12, False)))),
        ("Direct Bring on expanding region [4/5, 9/10]",
         ParamContractionCert(bring_dir, DyadicBall(0, 0, 0), DyadicBall(17, 5, 1), 63, 6, certs["bring_alt"].tree)),
    ]
    for label, bad_cert in bad_tests:
        res = check_param_contraction(bad_cert)
        print(f"  REJECT={not res!s:5s} | {label}")
        assert res is False

    print("\nALL SYNTHESIS, EXACT REPLAY, SHARPNESS, AND MUTATION TESTS PASSED (ZERO FLOAT)!")


if __name__ == "__main__":
    main()
