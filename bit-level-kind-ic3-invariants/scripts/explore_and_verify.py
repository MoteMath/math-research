#!/usr/bin/env python3
"""
Exact Pure-Silicon Bit-Level k-Induction & IC3/PDR Certificate Synthesizer,
Independent Exact-Integer Verifier, CTI Finder, and Sharpness / Mutation Test Suite.

Matches the standalone Lean 4.36.0 compiler in Proof.lean bit-for-bit.
Strictly CPU-only, exact integer arithmetic (zero floating-point values anywhere).
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple
import time

# ============================================================================
# 1. Width-Uniform Bit-Vector AST (exact mirror of BVExpr / BVPred in Proof.lean)
# ============================================================================

@dataclass(frozen=True)
class BVExpr:
    op: str
    args: Tuple[Any, ...] = ()

def E_zero() -> BVExpr: return BVExpr("zero")
def E_one() -> BVExpr: return BVExpr("one")
def E_allOnes() -> BVExpr: return BVExpr("allOnes")
def E_reg(i: int) -> BVExpr: return BVExpr("reg", (i,))
def E_inp(j: int) -> BVExpr: return BVExpr("inp", (j,))
def E_not(e: BVExpr) -> BVExpr: return BVExpr("not", (e,))
def E_and(a: BVExpr, b: BVExpr) -> BVExpr: return BVExpr("and", (a, b))
def E_or(a: BVExpr, b: BVExpr) -> BVExpr: return BVExpr("or", (a, b))
def E_xor(a: BVExpr, b: BVExpr) -> BVExpr: return BVExpr("xor", (a, b))
def E_add(a: BVExpr, b: BVExpr) -> BVExpr: return BVExpr("add", (a, b))
def E_sub(a: BVExpr, b: BVExpr) -> BVExpr: return BVExpr("sub", (a, b))
def E_shl1(e: BVExpr) -> BVExpr: return BVExpr("shl1", (e,))
def E_shr1(e: BVExpr) -> BVExpr: return BVExpr("shr1", (e,))

@dataclass(frozen=True)
class BVPred:
    op: str
    args: Tuple[Any, ...] = ()

def P_true() -> BVPred: return BVPred("pTrue")
def P_false() -> BVPred: return BVPred("pFalse")
def P_eq(a: BVExpr, b: BVExpr) -> BVPred: return BVPred("eq", (a, b))
def P_ule(a: BVExpr, b: BVExpr) -> BVPred: return BVPred("ule", (a, b))
def P_ult(a: BVExpr, b: BVExpr) -> BVPred: return BVPred("ult", (a, b))
def P_lsbEq(e: BVExpr, b: bool) -> BVPred: return BVPred("lsbEq", (e, b))
def P_msbEq(e: BVExpr, b: bool) -> BVPred: return BVPred("msbEq", (e, b))
def P_not(p: BVPred) -> BVPred: return BVPred("pNot", (p,))
def P_and(a: BVPred, b: BVPred) -> BVPred: return BVPred("pAnd", (a, b))
def P_or(a: BVPred, b: BVPred) -> BVPred: return BVPred("pOr", (a, b))
def P_imp(a: BVPred, b: BVPred) -> BVPred: return BVPred("pImp", (a, b))

@dataclass(frozen=True)
class BVSystem:
    name: str
    r: int
    m: int
    init: BVPred
    next: Tuple[BVExpr, ...]  # length r

def fold_and(preds: Sequence[BVPred]) -> BVPred:
    """Matches Proof.lean's right-nested foldAnd."""
    if not preds:
        return P_true()
    if len(preds) == 1:
        return preds[0]
    return P_and(preds[0], fold_and(preds[1:]))

# ============================================================================
# 2. Exact BitVec w Semantics (for independent replay & counterexample check)
# ============================================================================

def eval_expr_bv(w: int, regs: Sequence[int], inps: Sequence[int], e: BVExpr) -> int:
    mask = (1 << w) - 1
    op = e.op
    if op == "zero": return 0
    if op == "one": return 1 & mask
    if op == "allOnes": return mask
    if op == "reg": return regs[e.args[0]] & mask
    if op == "inp": return inps[e.args[0]] & mask
    if op == "not": return (~eval_expr_bv(w, regs, inps, e.args[0])) & mask
    if op == "and": return eval_expr_bv(w, regs, inps, e.args[0]) & eval_expr_bv(w, regs, inps, e.args[1])
    if op == "or":  return eval_expr_bv(w, regs, inps, e.args[0]) | eval_expr_bv(w, regs, inps, e.args[1])
    if op == "xor": return eval_expr_bv(w, regs, inps, e.args[0]) ^ eval_expr_bv(w, regs, inps, e.args[1])
    if op == "add": return (eval_expr_bv(w, regs, inps, e.args[0]) + eval_expr_bv(w, regs, inps, e.args[1])) & mask
    if op == "sub": return (eval_expr_bv(w, regs, inps, e.args[0]) - eval_expr_bv(w, regs, inps, e.args[1])) & mask
    if op == "shl1": return (eval_expr_bv(w, regs, inps, e.args[0]) << 1) & mask
    if op == "shr1": return (eval_expr_bv(w, regs, inps, e.args[0]) >> 1) & mask
    raise ValueError(f"Unknown expr op: {op}")

def eval_pred_bv(w: int, regs: Sequence[int], inps: Sequence[int], p: BVPred) -> bool:
    op = p.op
    if op == "pTrue": return True
    if op == "pFalse": return False
    if op == "eq": return eval_expr_bv(w, regs, inps, p.args[0]) == eval_expr_bv(w, regs, inps, p.args[1])
    if op == "ule": return eval_expr_bv(w, regs, inps, p.args[0]) <= eval_expr_bv(w, regs, inps, p.args[1])
    if op == "ult": return eval_expr_bv(w, regs, inps, p.args[0]) < eval_expr_bv(w, regs, inps, p.args[1])
    if op == "lsbEq": return bool(eval_expr_bv(w, regs, inps, p.args[0]) & 1) == p.args[1]
    if op == "msbEq": return bool((eval_expr_bv(w, regs, inps, p.args[0]) >> (w - 1)) & 1) == p.args[1]
    if op == "pNot": return not eval_pred_bv(w, regs, inps, p.args[0])
    if op == "pAnd": return eval_pred_bv(w, regs, inps, p.args[0]) and eval_pred_bv(w, regs, inps, p.args[1])
    if op == "pOr":  return eval_pred_bv(w, regs, inps, p.args[0]) or eval_pred_bv(w, regs, inps, p.args[1])
    if op == "pImp": return (not eval_pred_bv(w, regs, inps, p.args[0])) or eval_pred_bv(w, regs, inps, p.args[1])
    raise ValueError(f"Unknown pred op: {op}")

# ============================================================================
# 3. Bit-Slice Compiler (bit-for-bit identical to Proof.lean Sections 4 & 6)
# ============================================================================

def expr_bits(e: BVExpr) -> int:
    op = e.op
    if op in ("zero", "allOnes", "reg", "inp"): return 0
    if op == "one": return 1
    if op == "not": return expr_bits(e.args[0])
    if op in ("and", "or", "xor"): return expr_bits(e.args[0]) + expr_bits(e.args[1])
    if op in ("add", "sub"): return expr_bits(e.args[0]) + expr_bits(e.args[1]) + 1
    if op == "shl1": return expr_bits(e.args[0]) + 1
    if op == "shr1": return expr_bits(e.args[0]) + 2
    raise ValueError(op)

def expr_guesses(e: BVExpr) -> int:
    op = e.op
    if op in ("zero", "one", "allOnes", "reg", "inp"): return 0
    if op in ("not", "shl1"): return expr_guesses(e.args[0])
    if op in ("and", "or", "xor", "add", "sub"): return expr_guesses(e.args[0]) + expr_guesses(e.args[1])
    if op == "shr1": return expr_guesses(e.args[0]) + 1
    raise ValueError(op)

def expr_init_code(e: BVExpr) -> int:
    op = e.op
    if op in ("zero", "allOnes", "reg", "inp"): return 0
    if op == "one": return 1
    if op == "not": return expr_init_code(e.args[0])
    if op in ("and", "or", "xor", "add", "sub"):
        k1 = expr_bits(e.args[0])
        return expr_init_code(e.args[0]) + expr_init_code(e.args[1]) * (1 << k1)
    if op in ("shl1", "shr1"):
        return expr_init_code(e.args[0])
    raise ValueError(op)

def step_expr_code(r_bits: int, u_bits: int, e: BVExpr, code: int, gm: int) -> Tuple[int, bool, bool]:
    op = e.op
    if op == "zero": return (0, True, False)
    if op == "one": return (0, True, (code % 2) == 1)
    if op == "allOnes": return (0, True, True)
    if op == "reg": return (0, True, ((r_bits >> e.args[0]) & 1) == 1)
    if op == "inp": return (0, True, ((u_bits >> e.args[0]) & 1) == 1)
    if op == "not":
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e.args[0], code, gm)
        return (c1, v1, not b1)
    if op in ("and", "or", "xor"):
        e1, e2 = e.args
        k1, g1 = expr_bits(e1), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        c2, v2, b2 = step_expr_code(r_bits, u_bits, e2, code >> k1, gm >> g1)
        out = (b1 and b2) if op == "and" else ((b1 or b2) if op == "or" else (b1 != b2))
        return (c1 + (c2 << k1), v1 and v2, out)
    if op == "add":
        e1, e2 = e.args
        k1, k2, g1 = expr_bits(e1), expr_bits(e2), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        rest = code >> k1
        c2, v2, b2 = step_expr_code(r_bits, u_bits, e2, rest & ((1 << k2) - 1), gm >> g1)
        cin = ((rest >> k2) & 1) == 1
        out = (b1 != b2) != cin
        cout = (b1 and b2) or (cin and (b1 != b2))
        return (c1 + ((c2 + ((1 if cout else 0) << k2)) << k1), v1 and v2, out)
    if op == "sub":
        e1, e2 = e.args
        k1, k2, g1 = expr_bits(e1), expr_bits(e2), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        rest = code >> k1
        c2, v2, b2 = step_expr_code(r_bits, u_bits, e2, rest & ((1 << k2) - 1), gm >> g1)
        brw = ((rest >> k2) & 1) == 1
        out = (b1 != b2) != brw
        brw_next = ((not b1) and b2) or ((not b1) and brw) or (b2 and brw)
        return (c1 + ((c2 + ((1 if brw_next else 0) << k2)) << k1), v1 and v2, out)
    if op == "shl1":
        e1 = e.args[0]
        k1 = expr_bits(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm)
        prev = ((code >> k1) & 1) == 1
        return (c1 + ((1 if b1 else 0) << k1), v1, prev)
    if op == "shr1":
        e1 = e.args[0]
        k1, g1 = expr_bits(e1), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        exp_code = (code >> k1) & 3
        if exp_code == 0: ok = True
        elif exp_code == 1: ok = not b1
        elif exp_code == 2: ok = b1
        else: ok = False
        guess_bit = ((gm >> g1) & 1) == 1
        next_exp = 2 if guess_bit else 1
        return (c1 + (next_exp << k1), v1 and ok, guess_bit)
    raise ValueError(op)

def expr_final_valid(e: BVExpr, code: int) -> bool:
    op = e.op
    if op in ("zero", "one", "allOnes", "reg", "inp"): return True
    if op == "not": return expr_final_valid(e.args[0], code)
    if op in ("and", "or", "xor"):
        e1, e2 = e.args
        k1 = expr_bits(e1)
        return expr_final_valid(e1, code & ((1 << k1) - 1)) and expr_final_valid(e2, code >> k1)
    if op in ("add", "sub"):
        e1, e2 = e.args
        k1, k2 = expr_bits(e1), expr_bits(e2)
        rest = code >> k1
        return expr_final_valid(e1, code & ((1 << k1) - 1)) and expr_final_valid(e2, rest & ((1 << k2) - 1))
    if op == "shl1":
        e1 = e.args[0]
        return expr_final_valid(e1, code & ((1 << expr_bits(e1)) - 1))
    if op == "shr1":
        e1 = e.args[0]
        k1 = expr_bits(e1)
        return expr_final_valid(e1, code & ((1 << k1) - 1)) and (((code >> k1) & 3) == 1)
    raise ValueError(op)

def pred_bits(p: BVPred) -> int:
    op = p.op
    if op in ("pTrue", "pFalse"): return 0
    if op in ("eq", "ule", "ult"): return expr_bits(p.args[0]) + expr_bits(p.args[1]) + 1
    if op == "lsbEq": return expr_bits(p.args[0]) + 2
    if op == "msbEq": return expr_bits(p.args[0]) + 1
    if op == "pNot": return pred_bits(p.args[0])
    if op in ("pAnd", "pOr", "pImp"): return pred_bits(p.args[0]) + pred_bits(p.args[1])
    raise ValueError(op)

def pred_guesses(p: BVPred) -> int:
    op = p.op
    if op in ("pTrue", "pFalse"): return 0
    if op in ("eq", "ule", "ult"): return expr_guesses(p.args[0]) + expr_guesses(p.args[1])
    if op in ("lsbEq", "msbEq"): return expr_guesses(p.args[0])
    if op == "pNot": return pred_guesses(p.args[0])
    if op in ("pAnd", "pOr", "pImp"): return pred_guesses(p.args[0]) + pred_guesses(p.args[1])
    raise ValueError(op)

def pred_init_code(p: BVPred) -> int:
    op = p.op
    if op in ("pTrue", "pFalse"): return 0
    if op == "eq":
        e1, e2 = p.args
        k1, k2 = expr_bits(e1), expr_bits(e2)
        return expr_init_code(e1) + ((expr_init_code(e2) + (1 << k2)) << k1)
    if op == "ule":
        e1, e2 = p.args
        k1 = expr_bits(e1)
        return expr_init_code(e1) + (expr_init_code(e2) << k1)
    if op == "ult":
        e1, e2 = p.args
        k1, k2 = expr_bits(e1), expr_bits(e2)
        return expr_init_code(e1) + ((expr_init_code(e2) + (1 << k2)) << k1)
    if op in ("lsbEq", "msbEq"):
        return expr_init_code(p.args[0])
    if op == "pNot": return pred_init_code(p.args[0])
    if op in ("pAnd", "pOr", "pImp"):
        k1 = pred_bits(p.args[0])
        return pred_init_code(p.args[0]) + (pred_init_code(p.args[1]) << k1)
    raise ValueError(op)

def step_pred_code(r_bits: int, u_bits: int, p: BVPred, code: int, gm: int) -> Tuple[int, bool]:
    op = p.op
    if op in ("pTrue", "pFalse"): return (0, True)
    if op == "eq":
        e1, e2 = p.args
        k1, k2, g1 = expr_bits(e1), expr_bits(e2), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        rest = code >> k1
        c2, v2, b2 = step_expr_code(r_bits, u_bits, e2, rest & ((1 << k2) - 1), gm >> g1)
        ok = ((rest >> k2) & 1) == 1
        ok_next = ok and (b1 == b2)
        return (c1 + ((c2 + ((1 if ok_next else 0) << k2)) << k1), v1 and v2)
    if op in ("ule", "ult"):
        e1, e2 = p.args
        k1, k2, g1 = expr_bits(e1), expr_bits(e2), expr_guesses(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        rest = code >> k1
        c2, v2, b2 = step_expr_code(r_bits, u_bits, e2, rest & ((1 << k2) - 1), gm >> g1)
        brw = ((rest >> k2) & 1) == 1
        brw_next = ((not b2) and b1) or ((not b2) and brw) or (b1 and brw)
        return (c1 + ((c2 + ((1 if brw_next else 0) << k2)) << k1), v1 and v2)
    if op == "lsbEq":
        e1, target = p.args
        k1 = expr_bits(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm)
        st = (code >> k1) & 3
        st_next = (2 if (b1 == target) else 1) if st == 0 else st
        return (c1 + (st_next << k1), v1)
    if op == "msbEq":
        e1, _ = p.args
        k1 = expr_bits(e1)
        c1, v1, b1 = step_expr_code(r_bits, u_bits, e1, code & ((1 << k1) - 1), gm)
        return (c1 + ((1 if b1 else 0) << k1), v1)
    if op == "pNot":
        return step_pred_code(r_bits, u_bits, p.args[0], code, gm)
    if op in ("pAnd", "pOr", "pImp"):
        p1, p2 = p.args
        k1, g1 = pred_bits(p1), pred_guesses(p1)
        c1, v1 = step_pred_code(r_bits, u_bits, p1, code & ((1 << k1) - 1), gm & ((1 << g1) - 1))
        c2, v2 = step_pred_code(r_bits, u_bits, p2, code >> k1, gm >> g1)
        return (c1 + (c2 << k1), v1 and v2)
    raise ValueError(op)

def pred_final_valid(p: BVPred, code: int) -> bool:
    op = p.op
    if op in ("pTrue", "pFalse"): return True
    if op in ("eq", "ule", "ult"):
        e1, e2 = p.args
        k1, k2 = expr_bits(e1), expr_bits(e2)
        rest = code >> k1
        return expr_final_valid(e1, code & ((1 << k1) - 1)) and expr_final_valid(e2, rest & ((1 << k2) - 1))
    if op in ("lsbEq", "msbEq"):
        e1 = p.args[0]
        return expr_final_valid(e1, code & ((1 << expr_bits(e1)) - 1))
    if op == "pNot": return pred_final_valid(p.args[0], code)
    if op in ("pAnd", "pOr", "pImp"):
        p1, p2 = p.args
        k1 = pred_bits(p1)
        return pred_final_valid(p1, code & ((1 << k1) - 1)) and pred_final_valid(p2, code >> k1)
    raise ValueError(op)

def pred_accept(p: BVPred, code: int) -> bool:
    op = p.op
    if op == "pTrue": return True
    if op == "pFalse": return False
    if op == "eq":
        k1, k2 = expr_bits(p.args[0]), expr_bits(p.args[1])
        return (((code >> k1) >> k2) & 1) == 1
    if op in ("ule", "ult"):
        k1, k2 = expr_bits(p.args[0]), expr_bits(p.args[1])
        return (((code >> k1) >> k2) & 1) == 0
    if op == "lsbEq":
        k1 = expr_bits(p.args[0])
        return ((code >> k1) & 3) == 2
    if op == "msbEq":
        k1 = expr_bits(p.args[0])
        return (((code >> k1) & 1) == 1) == p.args[1]
    if op == "pNot": return not pred_accept(p.args[0], code)
    if op == "pAnd":
        k1 = pred_bits(p.args[0])
        return pred_accept(p.args[0], code & ((1 << k1) - 1)) and pred_accept(p.args[1], code >> k1)
    if op == "pOr":
        k1 = pred_bits(p.args[0])
        return pred_accept(p.args[0], code & ((1 << k1) - 1)) or pred_accept(p.args[1], code >> k1)
    if op == "pImp":
        k1 = pred_bits(p.args[0])
        return (not pred_accept(p.args[0], code & ((1 << k1) - 1))) or pred_accept(p.args[1], code >> k1)
    raise ValueError(op)

def pred_alive_hyp(p: BVPred, code: int) -> bool:
    op = p.op
    if op == "pFalse": return False
    if op == "eq":
        k1, k2 = expr_bits(p.args[0]), expr_bits(p.args[1])
        return (((code >> k1) >> k2) & 1) == 1
    if op == "lsbEq":
        k1 = expr_bits(p.args[0])
        return ((code >> k1) & 3) != 1
    if op == "pAnd":
        k1 = pred_bits(p.args[0])
        return pred_alive_hyp(p.args[0], code & ((1 << k1) - 1)) and pred_alive_hyp(p.args[1], code >> k1)
    return True

# ---- Recursive Obligation Compiler (matches Proof.lean Section 6 bit-for-bit!) ----

def next_bits(sys: BVSystem) -> int:
    return sum(expr_bits(e) for e in sys.next)

def next_guesses(sys: BVSystem) -> int:
    return sum(expr_guesses(e) for e in sys.next)

def next_init_code(sys: BVSystem) -> int:
    acc = 0
    shift = 0
    for e in sys.next:
        acc += expr_init_code(e) << shift
        shift += expr_bits(e)
    return acc

def step_next_code(sys: BVSystem, r_bits: int, u_bits: int, code: int, gm: int) -> Tuple[int, bool, int]:
    acc = 0
    ok_all = True
    out_r = 0
    b_shift = 0
    g_shift = 0
    for idx, e in enumerate(sys.next):
        eb = expr_bits(e)
        eg = expr_guesses(e)
        c, v, ob = step_expr_code(r_bits, u_bits, e, (code >> b_shift) & ((1 << eb) - 1), (gm >> g_shift) & ((1 << eg) - 1))
        if not v:
            ok_all = False
        acc += c << b_shift
        if ob:
            out_r |= (1 << idx)
        b_shift += eb
        g_shift += eg
    return (acc, ok_all, out_r)

def next_final_valid(sys: BVSystem, code: int) -> bool:
    shift = 0
    for e in sys.next:
        eb = expr_bits(e)
        if not expr_final_valid(e, (code >> shift) & ((1 << eb) - 1)):
            return False
        shift += eb
    return True

def ob_guesses(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred) -> int:
    if steps == 0:
        return pred_guesses(hyps[0]) + pred_guesses(conc)
    return next_guesses(sys) + pred_guesses(hyps[0]) + ob_guesses(sys, steps - 1, hyps[1:], conc)

def ob_init_code(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred) -> int:
    if steps == 0:
        return pred_init_code(hyps[0]) + (pred_init_code(conc) << pred_bits(hyps[0]))
    kn = next_bits(sys)
    kh = pred_bits(hyps[0])
    c_rest = ob_init_code(sys, steps - 1, hyps[1:], conc)
    return next_init_code(sys) + ((pred_init_code(hyps[0]) + (c_rest << kh)) << kn)

def ob_step_code(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred,
                 r_bits: int, u_mask: int, code: int, gm: int) -> Optional[int]:
    if steps == 0:
        h0 = hyps[0]
        kh, gh = pred_bits(h0), pred_guesses(h0)
        hc, hv = step_pred_code(r_bits, 0, h0, code & ((1 << kh) - 1), gm & ((1 << gh) - 1))
        if (not hv) or (not pred_alive_hyp(h0, hc)):
            return None
        cc, cv = step_pred_code(r_bits, 0, conc, code >> kh, gm >> gh)
        if not cv:
            return None
        return hc + (cc << kh)
    h0 = hyps[0]
    kn, gn = next_bits(sys), next_guesses(sys)
    kh, gh = pred_bits(h0), pred_guesses(h0)
    u0 = u_mask & ((1 << sys.m) - 1)
    nc, nv, r_next = step_next_code(sys, r_bits, u0, code & ((1 << kn) - 1), gm & ((1 << gn) - 1))
    if not nv:
        return None
    rest_c, rest_g = code >> kn, gm >> gn
    hc, hv = step_pred_code(r_bits, 0, h0, rest_c & ((1 << kh) - 1), rest_g & ((1 << gh) - 1))
    if (not hv) or (not pred_alive_hyp(h0, hc)):
        return None
    rc = ob_step_code(sys, steps - 1, hyps[1:], conc, r_next, u_mask >> sys.m, rest_c >> kh, rest_g >> gh)
    if rc is None:
        return None
    return nc + ((hc + (rc << kh)) << kn)

def ob_is_bad_accept(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred, code: int) -> bool:
    if steps == 0:
        h0 = hyps[0]
        kh = pred_bits(h0)
        hc, cc = code & ((1 << kh) - 1), code >> kh
        return pred_final_valid(h0, hc) and pred_accept(h0, hc) and pred_final_valid(conc, cc) and (not pred_accept(conc, cc))
    h0 = hyps[0]
    kn, kh = next_bits(sys), pred_bits(h0)
    nc = code & ((1 << kn) - 1)
    rest = code >> kn
    hc, rc = rest & ((1 << kh) - 1), rest >> kh
    return (next_final_valid(sys, nc) and pred_final_valid(h0, hc) and pred_accept(h0, hc)
            and ob_is_bad_accept(sys, steps - 1, hyps[1:], conc, rc))

def synthesize_oblig(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred,
                     max_states: int = 50000) -> Tuple[bool, List[int], Optional[Dict[str, Any]]]:
    init = ob_init_code(sys, steps, hyps, conc)
    n_r = 1 << sys.r
    n_u = 1 << (steps * sys.m)
    n_g = 1 << ob_guesses(sys, steps, hyps, conc)

    visited: Dict[int, Tuple[Optional[int], int, int]] = {}
    queue: List[int] = []

    def reconstruct(bad_code: int) -> Dict[str, Any]:
        path: List[Tuple[int, int]] = []
        cur: Optional[int] = bad_code
        while cur is not None:
            prev, rb, um = visited[cur]
            path.append((rb, um))
            cur = prev
        path.reverse()
        w = len(path)
        s0 = [0] * sys.r
        inputs = [[0] * sys.m for _ in range(steps)]
        for bit_i, (rb, um) in enumerate(path):
            for idx in range(sys.r):
                if (rb >> idx) & 1:
                    s0[idx] |= (1 << bit_i)
            for j in range(steps):
                for m_idx in range(sys.m):
                    if (um >> (j * sys.m + m_idx)) & 1:
                        inputs[j][m_idx] |= (1 << bit_i)
        trace = [s0]
        for j in range(steps):
            nxt = [eval_expr_bv(w, trace[-1], inputs[j], e) for e in sys.next]
            trace.append(nxt)
        for j, h in enumerate(hyps):
            assert eval_pred_bv(w, trace[j], [], h), f"CTI replay failed at hyp {j}"
        assert not eval_pred_bv(w, trace[steps], [], conc), "CTI replay failed: conc true"
        return {"w": w, "s0": s0, "inputs": inputs, "trace": trace}

    for rb in range(n_r):
        for um in range(n_u):
            for gm in range(n_g):
                nxt = ob_step_code(sys, steps, hyps, conc, rb, um, init, gm)
                if nxt is None:
                    continue
                if nxt not in visited:
                    visited[nxt] = (None, rb, um)
                    queue.append(nxt)
                    if ob_is_bad_accept(sys, steps, hyps, conc, nxt):
                        return (False, [], reconstruct(nxt))

    head = 0
    while head < len(queue):
        cur = queue[head]
        head += 1
        for rb in range(n_r):
            for um in range(n_u):
                for gm in range(n_g):
                    nxt = ob_step_code(sys, steps, hyps, conc, rb, um, cur, gm)
                    if nxt is None:
                        continue
                    if nxt not in visited:
                        visited[nxt] = (cur, rb, um)
                        queue.append(nxt)
                        if ob_is_bad_accept(sys, steps, hyps, conc, nxt):
                            return (False, [], reconstruct(nxt))
                        if len(visited) > max_states:
                            raise RuntimeError(f"State limit {max_states} exceeded")

    return (True, sorted(visited.keys()), None)

def check_oblig_cert(sys: BVSystem, steps: int, hyps: Sequence[BVPred], conc: BVPred,
                     cert_codes: Sequence[int]) -> bool:
    """Independent Python replay of Proof.lean's checkOblig."""
    cset = set(cert_codes)
    n_r = 1 << sys.r
    n_u = 1 << (steps * sys.m)
    n_g = 1 << ob_guesses(sys, steps, hyps, conc)
    init = ob_init_code(sys, steps, hyps, conc)

    for rb in range(n_r):
        for um in range(n_u):
            for gm in range(n_g):
                nxt = ob_step_code(sys, steps, hyps, conc, rb, um, init, gm)
                if nxt is not None and nxt not in cset:
                    return False
    for c in cert_codes:
        if ob_is_bad_accept(sys, steps, hyps, conc, c):
            return False
        for rb in range(n_r):
            for um in range(n_u):
                for gm in range(n_g):
                    nxt = ob_step_code(sys, steps, hyps, conc, rb, um, c, gm)
                    if nxt is not None and nxt not in cset:
                        return False
    return True

def synthesize_kind_ic3(sys: BVSystem, prop: BVPred, k: int, ic3_clauses: Sequence[BVPred]) -> Dict[str, Any]:
    """
    Synthesizes finite binary certificates for IC3-strengthened k-induction:
      - Base_j (j = 0 .. k-1): Init(s_0) -> Inv(s_j)
      - Step_k: Inv(s_0) and ... and Inv(s_{k-1}) -> Inv(s_k)
      - Safety: Inv(s_0) -> Prop(s_0)
    """
    inv = fold_and(ic3_clauses) if ic3_clauses else prop
    res: Dict[str, Any] = {
        "k": k, "inv_clauses": list(ic3_clauses),
        "bases": [], "step": None, "safety": None,
        "ok": True, "failed_at": None, "cti": None,
    }
    for j in range(k):
        hyps = [sys.init] + [P_true()] * j
        ok, cert, cti = synthesize_oblig(sys, j, hyps, inv)
        res["bases"].append((ok, cert, cti))
        if not ok:
            res["ok"] = False
            res["failed_at"] = f"Base_{j}"
            res["cti"] = cti
            return res
        assert check_oblig_cert(sys, j, hyps, inv, cert)

    hyps_step = [inv] * k + [P_true()]
    ok, cert, cti = synthesize_oblig(sys, k, hyps_step, inv)
    res["step"] = (ok, cert, cti)
    if not ok:
        res["ok"] = False
        res["failed_at"] = f"Step_{k}"
        res["cti"] = cti
        return res
    assert check_oblig_cert(sys, k, hyps_step, inv, cert)

    ok, cert, cti = synthesize_oblig(sys, 0, [inv], prop)
    res["safety"] = (ok, cert, cti)
    if not ok:
        res["ok"] = False
        res["failed_at"] = "Safety"
        res["cti"] = cti
        return res
    assert check_oblig_cert(sys, 0, [inv], prop, cert)
    return res

def to_lean_natset(sorted_codes: Sequence[int]) -> str:
    """Emit a balanced binary search tree `NatSet` literal for Proof.lean."""
    if not sorted_codes:
        return ".empty"
    mid = len(sorted_codes) // 2
    v = sorted_codes[mid]
    left = to_lean_natset(sorted_codes[:mid])
    right = to_lean_natset(sorted_codes[mid + 1:])
    if left == ".empty" and right == ".empty":
        return f"(.node {v} .empty .empty)"
    return f"(.node {v} {left} {right})"

# ============================================================================
# 4. Five Flagship Infinite Bitwise Transition Systems (T1 - T5)
# ============================================================================

def build_suite():
    # T1: Wrap-Safe Incremental Gray-Code Counter
    x, g = E_reg(0), E_reg(1)
    xp1 = E_add(x, E_one())
    d = E_xor(x, xp1)
    t1_sys = BVSystem(
        name="T1_WrapSafeGrayCounter",
        r=2, m=0,
        init=P_and(P_eq(x, E_zero()), P_eq(g, E_zero())),
        next=(xp1, E_xor(g, E_xor(d, E_shr1(d))))
    )
    t1_prop = P_and(
        P_imp(P_eq(x, E_zero()), P_eq(g, E_zero())),
        P_and(P_imp(P_msbEq(x, True), P_msbEq(g, True)),
              P_imp(P_msbEq(g, True), P_msbEq(x, True)))
    )
    t1_inv = [P_eq(g, E_xor(x, E_shr1(x)))]

    # T2: Nondeterministic Carry-Save Accumulator
    S, C, A, u = E_reg(0), E_reg(1), E_reg(2), E_inp(0)
    maj = E_or(E_and(S, C), E_or(E_and(S, u), E_and(C, u)))
    t2_sys = BVSystem(
        name="T2_CarrySaveAccumulator",
        r=3, m=1,
        init=P_and(P_eq(S, E_zero()), P_and(P_eq(C, E_zero()), P_eq(A, E_zero()))),
        next=(E_xor(E_xor(S, C), u), E_shl1(maj), E_add(A, u))
    )
    SplusC = E_add(S, C)
    t2_prop = P_and(
        P_and(P_imp(P_lsbEq(S, True), P_lsbEq(A, True)),
              P_imp(P_lsbEq(A, True), P_lsbEq(S, True))),
        P_and(P_imp(P_msbEq(SplusC, True), P_msbEq(A, True)),
              P_imp(P_msbEq(A, True), P_msbEq(SplusC, True)))
    )
    t2_inv = [P_eq(SplusC, A), P_lsbEq(C, False)]

    # T3: 3-Stage Autonomous 3p+1 Carry-Defect Zero-Accumulator (PURE k=3 induction!)
    p, a, b = E_reg(0), E_reg(1), E_reg(2)
    q = E_add(E_add(p, E_shl1(p)), E_xor(b, E_one()))
    t3_sys = BVSystem(
        name="T3_CarryDefectPipeline_k3",
        r=3, m=0,
        init=P_and(P_eq(p, E_zero()), P_and(P_eq(a, E_zero()), P_eq(b, E_zero()))),
        next=(
            E_and(q, E_not(E_shl1(q))),
            E_xor(E_add(p, E_shl1(p)), E_xor(p, E_shl1(p))),
            E_add(b, a)
        )
    )
    t3_prop = P_eq(b, E_zero())
    t3_ic3 = [P_eq(E_and(p, E_shl1(p)), E_zero()), P_eq(a, E_zero()), P_eq(b, E_zero())]

    # T4: Hybrid Sparse-Shift vs 3x-Adder Accumulator (Combined IC3 + k=2)
    p4, x4, y4 = E_reg(0), E_reg(1), E_reg(2)
    xu = E_xor(x4, u)
    t4_sys = BVSystem(
        name="T4_HybridSparseAdder_IC3_k2",
        r=3, m=1,
        init=P_and(P_eq(p4, E_zero()), P_and(P_eq(x4, E_zero()), P_eq(y4, E_zero()))),
        next=(
            E_and(xu, E_not(E_shl1(xu))),
            E_add(x4, E_xor(p4, E_shl1(p4))),
            E_add(y4, E_add(p4, E_shl1(p4)))
        )
    )
    t4_prop = P_and(P_imp(P_msbEq(x4, True), P_msbEq(y4, True)),
                    P_imp(P_msbEq(y4, True), P_msbEq(x4, True)))
    t4_inv = [P_eq(x4, y4)]

    # T5: Overflow-Free Fixed-Point Averaging Filter Exact 1-ULP Bound
    L, M = E_reg(0), E_reg(1)
    t5_sys = BVSystem(
        name="T5_OverflowFreeAvgFilter_1ULP",
        r=2, m=1,
        init=P_and(P_eq(L, E_zero()), P_eq(M, E_zero())),
        next=(
            E_add(E_shr1(L), E_shr1(u)),
            E_add(E_and(M, u), E_shr1(E_xor(M, u)))
        )
    )
    t5_prop = P_and(P_ule(L, M), P_ule(E_sub(M, L), E_one()))
    t5_prop_ulp_only = P_ule(E_sub(M, L), E_one())
    t5_inv = [P_ule(L, M), P_ule(E_sub(M, L), E_one())]

    return [
        ("t1Cert",     t1_sys, t1_prop,          1, t1_inv, "IC3 (k=1)"),
        ("t2Cert",     t2_sys, t2_prop,          1, t2_inv, "Multi-Clause IC3 (k=1)"),
        ("t3Cert_k3",  t3_sys, t3_prop,          3, [],     "Pure k=3 Induction (no IC3)"),
        ("t3Cert_ic3", t3_sys, t3_prop,          1, t3_ic3, "IC3 Comparison on T3 (k=1)"),
        ("t4Cert",     t4_sys, t4_prop,          2, t4_inv, "Combined IC3 + k=2 Induction"),
        ("t5Cert",     t5_sys, t5_prop,          1, t5_inv, "IC3 on ule/sub/shr1 (k=1)"),
    ]

# ============================================================================
# 5. Independent Brute-Force Reachable-Graph Verification on Concrete Widths
# ============================================================================

def brute_force_verify(sys: BVSystem, prop: BVPred, max_w: int = 4) -> Dict[int, int]:
    """Exhaustively explores ALL reachable states across ALL nondeterministic inputs for w = 1..max_w."""
    counts: Dict[int, int] = {}
    for w in range(1, max_w + 1):
        lim = 1 << w
        # Find initial states
        # For our 5 systems, init uniquely forces all registers to 0; check exhaustively for small w
        init_states = []
        if sys.r == 2:
            for a in range(lim):
                for b in range(lim):
                    if eval_pred_bv(w, (a, b), (), sys.init):
                        init_states.append((a, b))
        elif sys.r == 3 and w <= 3:
            for a in range(lim):
                for b in range(lim):
                    for c in range(lim):
                        if eval_pred_bv(w, (a, b, c), (), sys.init):
                            init_states.append((a, b, c))
        else:
            z = tuple([0] * sys.r)
            assert eval_pred_bv(w, z, (), sys.init)
            init_states.append(z)
        assert len(init_states) > 0, f"Vacuous init at w={w} for {sys.name}"
        seen = set(init_states)
        q = list(init_states)
        u_lim = 1 << (sys.m * w)
        while q:
            st = q.pop()
            assert eval_pred_bv(w, st, (), prop), f"Safety VIOLATION at w={w}, state={st} in {sys.name}!"
            for um in range(u_lim):
                inps = [(um >> (j * w)) & (lim - 1) for j in range(sys.m)]
                nxt = tuple(eval_expr_bv(w, st, inps, e) for e in sys.next)
                if nxt not in seen:
                    seen.add(nxt)
                    q.append(nxt)
        counts[w] = len(seen)
    return counts

# ============================================================================
# 6. Sharpness & Mutation Suite
# ============================================================================

def run_sharpness_and_mutations(suite, synth_results):
    print("\n=== 2. Independent Exhaustive Reachable-Graph Verification (w = 1..4) ===")
    checked = set()
    for name, sys, prop, _, _, _ in suite:
        key = (sys.name, prop)
        if key in checked:
            continue
        checked.add(key)
        max_w = 4 if sys.r == 2 else 3
        counts = brute_force_verify(sys, prop, max_w=max_w)
        print(f"  [OK] {sys.name}: exhaustive reachable states verified = {counts}")

    print("\n=== 3. Sharpness & Perturbed-System Counterexamples ===")
    # S1: Buggy Gray Counter (missing wraparound fix: g' = g ^ ((x+1) & -(x+1)))
    x, g = E_reg(0), E_reg(1)
    xp1 = E_add(x, E_one())
    lowbit = E_and(xp1, E_sub(E_zero(), xp1))
    buggy_gray = BVSystem("BuggyGray", 2, 0, P_and(P_eq(x, E_zero()), P_eq(g, E_zero())), (xp1, E_xor(g, lowbit)))
    for w in (1, 2, 3, 4):
        st = [0, 0]
        for t in range(1, (1 << w) + 1):
            st = [eval_expr_bv(w, st, [], e) for e in buggy_gray.next]
        assert st[0] == 0 and st[1] == (1 << (w - 1)), f"Unexpected buggy gray at w={w}: {st}"
    print("  [SHARP S1] Buggy Gray (lowbit without wraparound fix) FAILS at t=2^w for w=1,2,3,4: x=0, g=2^(w-1) != 0")

    # S2: T5 tighter bound M - L <= 0 fails at w=2, t=2 with u0=3, u1=3
    t5_sys = suite[5][1]
    st = [0, 0]
    for ut in (3, 3):
        st = [eval_expr_bv(2, st, [ut], e) for e in t5_sys.next]
    assert st == [1, 2] and ((st[1] - st[0]) & 3) == 1
    print(f"  [SHARP S2] T5 tighter bound M-L<=0 FAILS at w=2, t=2 (u=[3,3]): (L,M)={st}, M-L=1 > 0")

    # S3: T5 naive overflowing average M' = (M + u) >>> 1 fails at w=2, t=2 with u0=3, u1=3
    L, M, u = E_reg(0), E_reg(1), E_inp(0)
    buggy_avg = BVSystem("BuggyAvg", 2, 1, t5_sys.init, (E_add(E_shr1(L), E_shr1(u)), E_shr1(E_add(M, u))))
    st = [0, 0]
    for ut in (3, 3):
        st = [eval_expr_bv(2, st, [ut], e) for e in buggy_avg.next]
    assert st == [1, 0] and not (st[0] <= st[1])
    print(f"  [SHARP S3] T5 overflowing avg ((M+u)>>>1) FAILS at w=2, t=2 (u=[3,3]): (L,M)={st}, L=1 > M=0")

    # S4: CTI verification for weakening k or dropping IC3 clauses
    _, s1, p1, _, _, _ = suite[0]
    for kk in (1, 2):
        r = synthesize_kind_ic3(s1, p1, kk, [])
        assert not r["ok"]
        print(f"  [CTI T1] pure k={kk} (no IC3) fails at {r['failed_at']}: w={r['cti']['w']}, trace={r['cti']['trace']}")

    _, s2, p2, _, inv2, _ = suite[1]
    for desc, cl in [("no IC3", []), ("drop lsb(C)=0", [inv2[0]]), ("drop S+C=A", [inv2[1]])]:
        r = synthesize_kind_ic3(s2, p2, 1, cl)
        assert not r["ok"]
        print(f"  [CTI T2] ({desc}) fails at {r['failed_at']}: w={r['cti']['w']}, trace={r['cti']['trace']}")

    _, s3, p3, _, _, _ = suite[2]
    for kk in (1, 2):
        r = synthesize_kind_ic3(s3, p3, kk, [])
        assert not r["ok"]
        print(f"  [CTI T3] pure k={kk} (no IC3) fails at {r['failed_at']}: w={r['cti']['w']}, trace={r['cti']['trace']}")

    _, s4, p4, _, inv4, _ = suite[4]
    for desc, kk, cl in [("pure k=1", 1, []), ("pure k=2", 2, []), ("IC3 {x=y} at k=1", 1, inv4)]:
        r = synthesize_kind_ic3(s4, p4, kk, cl)
        assert not r["ok"]
        print(f"  [CTI T4] ({desc}) fails at {r['failed_at']}: w={r['cti']['w']}, trace={r['cti']['trace']}")

    _, s5, _, _, _, _ = suite[5]
    p5_ulp = P_ule(E_sub(E_reg(1), E_reg(0)), E_one())
    r = synthesize_kind_ic3(s5, p5_ulp, 1, [])
    assert not r["ok"]
    print(f"  [CTI T5] pure k=1 on M-L<=1 fails at {r['failed_at']}: w={r['cti']['w']}, trace={r['cti']['trace']}")

    print("\n=== 4. Hostile Certificate Mutation Tests (All Must Be Rejected) ===")
    for name, sys, prop, k, inv_cl, _ in suite:
        res = synth_results[name]
        inv = fold_and(inv_cl) if inv_cl else prop
        hyps_step = [inv] * k + [P_true()]
        step_codes = res["step"][1]
        # Mutation 1: delete one reachable state from stepCert
        mut_del = step_codes[:-1]
        assert not check_oblig_cert(sys, k, hyps_step, inv, mut_del), f"Delete mutation not rejected on {name}!"
        # Mutation 2: flip LSB of one state code in stepCert
        mut_flip = list(step_codes)
        mut_flip[0] = mut_flip[0] ^ 1
        if mut_flip[0] in set(step_codes):
            mut_flip[0] = (1 << 30) + 1
        assert not check_oblig_cert(sys, k, hyps_step, inv, mut_flip), f"Flip mutation not rejected on {name}!"
        # Mutation 3: empty certificate
        assert not check_oblig_cert(sys, k, hyps_step, inv, []), f"Empty cert not rejected on {name}!"
        print(f"  [REJECTED] {name}: delete-state, bit-flip, and empty-cert mutations all return False")

def main(emit_lean: bool = False):
    suite = build_suite()
    synth_results = {}
    print("=== 1. Synthesizing Exact Width-Uniform Bit-Level k-Induction / IC3 Certificates ===")
    for name, sys, prop, k, inv_cl, label in suite:
        t0 = time.perf_counter_ns()
        res = synthesize_kind_ic3(sys, prop, k, inv_cl)
        dt_ms = (time.perf_counter_ns() - t0) // 1_000_000
        assert res["ok"], f"{name} failed at {res['failed_at']}: {res['cti']}"
        synth_results[name] = res
        b_sizes = [len(c) for _, c, _ in res["bases"]]
        s_size = len(res["step"][1])
        sf_size = len(res["safety"][1])
        print(f"  [PASS] {name:11s} | {sys.name:30s} | {label:28s} | bases={b_sizes}, step={s_size}, safety={sf_size} ({dt_ms} ms)")

    run_sharpness_and_mutations(suite, synth_results)

    if emit_lean:
        print("\n=== LEAN CERTIFICATE EXPORTS ===")
        for name, _, _, k, _, _ in suite:
            res = synth_results[name]
            print(f"-- {name} (k={k})")
            for j, (_, c, _) in enumerate(res["bases"]):
                print(f"def {name}_base{j} : NatSet := {to_lean_natset(c)}")
            print(f"def {name}_step : NatSet := {to_lean_natset(res['step'][1])}")
            print(f"def {name}_safety : NatSet := {to_lean_natset(res['safety'][1])}")

if __name__ == "__main__":
    import sys as _sys
    main(emit_lean=("--emit-lean" in _sys.argv))
