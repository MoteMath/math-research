"""
Pure-Silicon Sprague-Grundy Bitwise-Game Periodicity Compiler & Independent Verifier.
Exact integer arithmetic only (zero floating point anywhere).

Covers all three regimes:
  Regime I  : Dyadic Borrow-Wall Theorem (pure borrow-bounded / Hamming-delta games)
  Regime II : Verified Periodicity & Winning-Strategy Bitmask Compiler (hybrid games)
  Regime III: Aperiodic Sharpness Boundary (borrow-parity game + modulus sharpness)
"""

from __future__ import annotations
from dataclasses import dataclass
from math import gcd
import sys


# ---------------------------------------------------------------------------
# 1. Exact Pure-Silicon Bitwise / Carry-Borrow Primitives
# ---------------------------------------------------------------------------

def popcount(n: int) -> int:
    assert n >= 0
    return n.bit_count()

def bit_len(n: int) -> int:
    assert n >= 0
    return n.bit_length()

def ctz(n: int) -> int:
    """2-adic valuation v_2(n) for n > 0; 0 for n == 0."""
    if n == 0:
        return 0
    return (n & -n).bit_length() - 1

def borrow_mask(n: int, s: int) -> int:
    assert 0 <= s <= n
    return n ^ (n - s) ^ s

def borrow_count(n: int, s: int) -> int:
    return popcount(borrow_mask(n, s))


# ---------------------------------------------------------------------------
# 2. BitGuard DSL & BitGame Semantics (exact 1-to-1 mirror of Proof.lean)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class GuardAlways:
    pass

@dataclass(frozen=True)
class GuardMaskEq:
    mask: int
    pattern: int

@dataclass(frozen=True)
class GuardBorrowFree:
    pass

@dataclass(frozen=True)
class GuardBorrowDepthLe:
    d: int

@dataclass(frozen=True)
class GuardBorrowCountLe:
    B: int

@dataclass(frozen=True)
class GuardBorrowCountEq:
    B: int

@dataclass(frozen=True)
class GuardPopcountDeltaLe:
    delta: int

@dataclass(frozen=True)
class GuardAnd:
    g1: BitGuard
    g2: BitGuard

@dataclass(frozen=True)
class GuardOr:
    g1: BitGuard
    g2: BitGuard

@dataclass(frozen=True)
class GuardNot:
    g: BitGuard

BitGuard = (
    GuardAlways | GuardMaskEq | GuardBorrowFree | GuardBorrowDepthLe |
    GuardBorrowCountLe | GuardBorrowCountEq | GuardPopcountDeltaLe |
    GuardAnd | GuardOr | GuardNot
)

@dataclass(frozen=True)
class BitRule:
    step: int
    guard: BitGuard


def eval_guard(s: int, g: BitGuard, n: int) -> bool:
    if isinstance(g, GuardAlways):
        return True
    if isinstance(g, GuardMaskEq):
        return (n & g.mask) == g.pattern
    if isinstance(g, GuardBorrowFree):
        return (n & s) == s
    if isinstance(g, GuardBorrowDepthLe):
        return (n % (1 << g.d)) >= s
    if isinstance(g, GuardBorrowCountLe):
        return borrow_count(n, s) <= g.B
    if isinstance(g, GuardBorrowCountEq):
        return borrow_count(n, s) == g.B
    if isinstance(g, GuardPopcountDeltaLe):
        return popcount(n - s) <= popcount(n) + g.delta
    if isinstance(g, GuardAnd):
        return eval_guard(s, g.g1, n) and eval_guard(s, g.g2, n)
    if isinstance(g, GuardOr):
        return eval_guard(s, g.g1, n) or eval_guard(s, g.g2, n)
    if isinstance(g, GuardNot):
        return not eval_guard(s, g.g, n)
    raise TypeError(g)


def guard_shift_bits(s: int, g: BitGuard) -> int:
    if isinstance(g, GuardAlways):
        return 0
    if isinstance(g, GuardMaskEq):
        return bit_len(g.mask)
    if isinstance(g, GuardBorrowFree):
        return bit_len(s)
    if isinstance(g, GuardBorrowDepthLe):
        return g.d
    if isinstance(g, GuardBorrowCountLe):
        return bit_len(s) + g.B
    if isinstance(g, GuardBorrowCountEq):
        return bit_len(s) + g.B
    if isinstance(g, GuardPopcountDeltaLe):
        return bit_len(s) + popcount(s) + g.delta
    if isinstance(g, GuardAnd):
        return max(guard_shift_bits(s, g.g1), guard_shift_bits(s, g.g2))
    if isinstance(g, GuardOr):
        return max(guard_shift_bits(s, g.g1), guard_shift_bits(s, g.g2))
    if isinstance(g, GuardNot):
        return guard_shift_bits(s, g.g)
    raise TypeError(g)


def is_wall_guard(g: BitGuard) -> bool:
    if isinstance(g, (GuardBorrowFree, GuardBorrowDepthLe, GuardBorrowCountLe,
                      GuardBorrowCountEq, GuardPopcountDeltaLe)):
        return True
    if isinstance(g, GuardAnd):
        return is_wall_guard(g.g1) or is_wall_guard(g.g2)
    return False


def game_shift_bits(G: list[BitRule]) -> int:
    return max((guard_shift_bits(r.step, r.guard) for r in G), default=0)


def max_step(G: list[BitRule]) -> int:
    return max((r.step for r in G), default=0)


def legal_move(G: list[BitRule], n: int, s: int) -> bool:
    return any(r.step == s and r.step > 0 and r.step <= n and eval_guard(r.step, r.guard, n) for r in G)


def legal_moves(G: list[BitRule], n: int) -> list[int]:
    return [r.step for r in G if r.step > 0 and r.step <= n and eval_guard(r.step, r.guard, n)]


def mex(vals: list[int]) -> int:
    s = set(vals)
    m = 0
    while m in s:
        m += 1
    return m


def compute_grundy(G: list[BitRule], limit: int) -> list[int]:
    g = [0] * limit
    for n in range(limit):
        g[n] = mex([g[n - s] for s in legal_moves(G, n)])
    return g


# ---------------------------------------------------------------------------
# 3. Finite Certificate & Checker (exact mirror of Proof.lean)
# ---------------------------------------------------------------------------

@dataclass
class PeriodWinCert:
    preperiod: int
    period: int
    min_period: int
    table: list[int]
    pre_win_mask: int
    per_win_mask: int
    pre_moves: list[int]
    per_moves: list[int]


def eval_periodic(c: PeriodWinCert, n: int) -> int:
    if n < c.preperiod:
        return c.table[n]
    return c.table[c.preperiod + ((n - c.preperiod) % c.period)]


def eval_win_move(G: list[BitRule], c: PeriodWinCert, n: int) -> int:
    ms = max_step(G)
    if n < c.preperiod + ms:
        return c.pre_moves[n]
    return c.per_moves[(n - (c.preperiod + ms)) % c.period]


def check_cert(G: list[BitRule], c: PeriodWinCert) -> bool:
    if not all(r.step > 0 for r in G):
        return False
    if c.period <= 0 or c.min_period <= 0:
        return False
    if c.period % c.min_period != 0:
        return False
    if len(c.table) != c.preperiod + c.period:
        return False
    shift_mod = 1 << game_shift_bits(G)
    if c.period % shift_mod != 0:
        return False
    ms = max_step(G)
    # Check Grundy recurrence on [0, preperiod + period + ms)
    for n in range(c.preperiod + c.period + ms):
        expected = mex([eval_periodic(c, n - s) for s in legal_moves(G, n)])
        if eval_periodic(c, n) != expected:
            return False
    # Check minimal-period compression
    for r in range(c.period):
        if c.table[c.preperiod + r] != c.table[c.preperiod + (r % c.min_period)]:
            return False
    # Check preWinMask & perWinMask
    for i in range(c.preperiod):
        if ((c.pre_win_mask >> i) & 1 == 1) != (c.table[i] != 0):
            return False
    for r in range(c.min_period):
        if ((c.per_win_mask >> r) & 1 == 1) != (c.table[c.preperiod + r] != 0):
            return False
    # Check winning move tables
    if len(c.pre_moves) != c.preperiod + ms:
        return False
    if len(c.per_moves) != c.period:
        return False
    for n in range(c.preperiod + ms):
        if eval_periodic(c, n) != 0:
            s = c.pre_moves[n]
            if not (legal_move(G, n, s) and eval_periodic(c, n - s) == 0):
                return False
    for r in range(c.period):
        m = c.preperiod + ms + r
        if eval_periodic(c, m) != 0:
            s = c.per_moves[r]
            if not (legal_move(G, m, s) and eval_periodic(c, m - s) == 0):
                return False
    return True


def synthesize_cert(G: list[BitRule], search_limit: int = 4096) -> PeriodWinCert:
    ms = max_step(G)
    shift_mod = 1 << game_shift_bits(G)
    g = compute_grundy(G, search_limit)
    # Find smallest min_period
    min_p = None
    n0 = None
    for p in range(1, 300):
        bad = -1
        for n in range(search_limit - p - 1, -1, -1):
            if g[n] != g[n + p]:
                bad = n
                break
        cand_n0 = bad + 1
        if cand_n0 + p + ms <= search_limit and (search_limit - p - cand_n0) >= max(ms, p, 128):
            min_p = p
            n0 = cand_n0
            break
    assert min_p is not None and n0 is not None, "No period found within search limit"
    # Dyadic-aligned certificate period = lcm(min_p, shift_mod)
    cert_p = (min_p * shift_mod) // gcd(min_p, shift_mod)
    table = g[: n0 + cert_p]
    pre_win_mask = sum((1 << i) for i in range(n0) if table[i] != 0)
    per_win_mask = sum((1 << r) for r in range(min_p) if table[n0 + r] != 0)
    pre_moves = []
    for n in range(n0 + ms):
        if g[n] == 0:
            pre_moves.append(0)
        else:
            mv = next(s for s in legal_moves(G, n) if g[n - s] == 0)
            pre_moves.append(mv)
    per_moves = []
    for r in range(cert_p):
        m = n0 + ms + r
        if g[m] == 0:
            per_moves.append(0)
        else:
            mv = next(s for s in legal_moves(G, m) if g[m - s] == 0)
            per_moves.append(mv)
    cert = PeriodWinCert(
        preperiod=n0,
        period=cert_p,
        min_period=min_p,
        table=table,
        pre_win_mask=pre_win_mask,
        per_win_mask=per_win_mask,
        pre_moves=pre_moves,
        per_moves=per_moves,
    )
    assert check_cert(G, cert), "Synthesized cert failed check_cert!"
    return cert


# ---------------------------------------------------------------------------
# 4. Showcase Family of 6 Novel Bitwise/Carry Subtraction Games
# ---------------------------------------------------------------------------

SHOWCASE_GAMES: list[tuple[str, str, list[BitRule]]] = [
    (
        "G_pop136",
        "Popcount-Nonincreasing {1, 3, 6} (Regime I Dyadic Borrow-Wall)",
        [
            BitRule(1, GuardPopcountDeltaLe(0)),
            BitRule(3, GuardPopcountDeltaLe(0)),
            BitRule(6, GuardPopcountDeltaLe(0)),
        ],
    ),
    (
        "G_wallbreach_24",
        "Borrow-Free Phase B=0 of {1(B=0), 3(always), 4(B=0)}",
        [
            BitRule(1, GuardBorrowCountLe(0)),
            BitRule(3, GuardAlways()),
            BitRule(4, GuardBorrowCountLe(0)),
        ],
    ),
    (
        "G_wallbreach_48",
        "Single-Borrow Phase B=1 of {1(B<=1), 3(always), 4(B<=1)}",
        [
            BitRule(1, GuardBorrowCountLe(1)),
            BitRule(3, GuardAlways()),
            BitRule(4, GuardBorrowCountLe(1)),
        ],
    ),
    (
        "G_coprime_p5",
        "Dyadic-Gated Coprime-Period Surprise {2(borrowFree), 3(always), 7(always)}",
        [
            BitRule(2, GuardBorrowFree()),
            BitRule(3, GuardAlways()),
            BitRule(7, GuardAlways()),
        ],
    ),
    (
        "G_hybrid_40",
        "Five-Fold Carry-Resonance {1(borrowFree), 2(B<=1), 5(always)}",
        [
            BitRule(1, GuardBorrowFree()),
            BitRule(2, GuardBorrowCountLe(1)),
            BitRule(5, GuardAlways()),
        ],
    ),
    (
        "G_compound",
        "Full-DSL Compound Guard {1(bc==1), 2(not(mask 3 0) & B<=2), 5(depth<=3 | mask 7 2)}",
        [
            BitRule(1, GuardBorrowCountEq(1)),
            BitRule(2, GuardAnd(GuardNot(GuardMaskEq(3, 0)), GuardBorrowCountLe(2))),
            BitRule(5, GuardOr(GuardBorrowDepthLe(3), GuardMaskEq(7, 2))),
        ],
    ),
]


def lean_guard(g: BitGuard) -> str:
    if isinstance(g, GuardAlways):
        return ".always"
    if isinstance(g, GuardMaskEq):
        return f"(.maskEq {g.mask} {g.pattern})"
    if isinstance(g, GuardBorrowFree):
        return ".borrowFree"
    if isinstance(g, GuardBorrowDepthLe):
        return f"(.borrowDepthLe {g.d})"
    if isinstance(g, GuardBorrowCountLe):
        return f"(.borrowCountLe {g.B})"
    if isinstance(g, GuardBorrowCountEq):
        return f"(.borrowCountEq {g.B})"
    if isinstance(g, GuardPopcountDeltaLe):
        return f"(.popcountDeltaLe {g.delta})"
    if isinstance(g, GuardAnd):
        return f"(.and {lean_guard(g.g1)} {lean_guard(g.g2)})"
    if isinstance(g, GuardOr):
        return f"(.or {lean_guard(g.g1)} {lean_guard(g.g2)})"
    if isinstance(g, GuardNot):
        return f"(.not {lean_guard(g.g)})"
    raise TypeError(g)


def emit_lean_cert(name: str, cert: PeriodWinCert) -> str:
    tbl = ", ".join(str(x) for x in cert.table)
    pm = ", ".join(str(x) for x in cert.pre_moves)
    qm = ", ".join(str(x) for x in cert.per_moves)
    return (
        f"def cert_{name} : PeriodWinCert := {{\n"
        f"  preperiod  := {cert.preperiod}\n"
        f"  period     := {cert.period}\n"
        f"  minPeriod  := {cert.min_period}\n"
        f"  table      := #[{tbl}]\n"
        f"  preWinMask := {cert.pre_win_mask}\n"
        f"  perWinMask := {cert.per_win_mask}\n"
        f"  preMoves   := #[{pm}]\n"
        f"  perMoves   := #[{qm}]\n"
        f"}}"
    )


def verify_all(emit_lean: bool = False) -> None:
    print("=== 1. Synthesizing & Independently Verifying 6 Showcase Bitwise/Carry Games (N = 10,000) ===")
    certs: dict[str, PeriodWinCert] = {}
    for name, desc, G in SHOWCASE_GAMES:
        cert = synthesize_cert(G)
        certs[name] = cert
        N = 10000
        g = compute_grundy(G, N)
        # Verify Grundy, winning bitmask, winning move, and losing closure on [0, N)
        for n in range(N):
            assert g[n] == eval_periodic(cert, n), f"{name} Grundy mismatch at n={n}"
            win = (g[n] != 0)
            if n < cert.preperiod:
                mask_win = ((cert.pre_win_mask >> n) & 1) == 1
            else:
                mask_win = ((cert.per_win_mask >> ((n - cert.preperiod) % cert.min_period)) & 1) == 1
            assert win == mask_win, f"{name} winMask mismatch at n={n}"
            if win:
                mv = eval_win_move(G, cert, n)
                assert legal_move(G, n, mv) and g[n - mv] == 0, f"{name} bad winMove at n={n}"
            else:
                for s in legal_moves(G, n):
                    assert g[n - s] != 0, f"{name} losing closure failed at n={n}"
        # Verify 2-heap disjunctive sum Sprague-Grundy XOR on 64x64 grid
        M2 = 48
        win2 = [[False] * M2 for _ in range(M2)]
        for a in range(M2):
            for b in range(M2):
                w = any(not win2[a - s][b] for s in legal_moves(G, a)) or \
                    any(not win2[a][b - s] for s in legal_moves(G, b))
                win2[a][b] = w
                assert w == ((g[a] ^ g[b]) != 0), f"{name} 2-heap mismatch at ({a},{b})"
        win_cnt = popcount(cert.per_win_mask)
        print(
            f"  [OK] {name:16s} | shift=2^{game_shift_bits(G):d} | "
            f"n0={cert.preperiod:2d}, p_min={cert.min_period:2d} (cert_p={cert.period:2d}) | "
            f"max_g={max(cert.table)} | win_density={win_cnt}/{cert.min_period} | "
            f"perWinMask=0x{cert.per_win_mask:x}"
        )

    # Verify sharp preperiod on G_coprime_p5
    g_cp5 = compute_grundy(SHOWCASE_GAMES[3][2], 64)
    assert g_cp5[14] == 3 and g_cp5[19] == 2
    print(f"  [SHARP] G_coprime_p5 preperiod sharp: g(14)={g_cp5[14]} != g(19)={g_cp5[19]} (n0=15 minimal)")

    # Verify sharp preperiod on G_wallbreach_24
    g_wb24 = compute_grundy(SHOWCASE_GAMES[1][2], 64)
    assert g_wb24[4] != g_wb24[4 + 24]
    print(f"  [SHARP] G_wallbreach_24 preperiod sharp: g(4)={g_wb24[4]} != g(28)={g_wb24[28]} (n0=5 minimal)")

    print("\n=== 2. Independent Verification of Regime I (Dyadic Borrow-Wall Theorem) ===")
    wall_games = [
        [BitRule(1, GuardPopcountDeltaLe(0)), BitRule(3, GuardPopcountDeltaLe(0)), BitRule(6, GuardPopcountDeltaLe(0))],
        [BitRule(1, GuardPopcountDeltaLe(1)), BitRule(4, GuardPopcountDeltaLe(0)), BitRule(5, GuardPopcountDeltaLe(0))],
        [BitRule(1, GuardBorrowCountLe(0)), BitRule(2, GuardBorrowCountLe(1)), BitRule(5, GuardBorrowCountLe(1))],
        [BitRule(2, GuardBorrowCountEq(1)), BitRule(3, GuardBorrowFree()), BitRule(6, GuardBorrowDepthLe(3))],
        [BitRule(1, GuardBorrowCountLe(2)), BitRule(3, GuardBorrowCountLe(1)), BitRule(7, GuardBorrowCountLe(0))],
    ]
    for idx, WG in enumerate(wall_games):
        assert all(is_wall_guard(r.guard) for r in WG)
        L = game_shift_bits(WG)
        M = 1 << L
        g = compute_grundy(WG, 8 * M)
        # Check zero boundary crossings and exact pure periodicity g(n + M) == g(n) from n = 0
        for q in range(1, 8):
            for r in range(max_step(WG)):
                for s in legal_moves(WG, q * M + r):
                    assert s <= r, f"Wall crossed at q={q}, r={r}, s={s}"
        for n in range(7 * M):
            assert g[n + M] == g[n], f"Wall game {idx} not purely {M}-periodic at n={n}"
        print(f"  [OK] Wall game #{idx+1}: L={L} (2^L={M:3d}), zero crossings across 7 walls, exact g(n+2^L)=g(n) for all n < {7*M}")

    print("\n=== 3. Independent Verification of Regime III (Aperiodic Borrow-Parity Boundary) ===")
    N_par = 20000
    g_par = [0] * N_par
    for n in range(N_par):
        nxt = []
        if n >= 1 and (borrow_count(n, 1) % 2 == 0):
            nxt.append(g_par[n - 1])
        if n >= 2:
            nxt.append(g_par[n - 2])
        g_par[n] = mex(nxt)
    for k in range(3, N_par // 4):
        exp = 2 if (ctz(k) % 2 == 0) else 1
        assert g_par[4 * k] == exp and g_par[4 * k + 1] == 0 and g_par[4 * k + 2] == 0 and g_par[4 * k + 3] == 1
    # Confirm no period 1 <= p <= 1000 holds from any n0 <= 4000
    for p in range(1, 1001):
        # Construct explicit witness n >= 4000 with g_par[n + p] != g_par[n]
        if p % 4 != 0:
            n_wit = 4 * 1024  # 4096, ctz(1024)=10 (even) -> g=2; 4096+p not 0 mod 4 -> g in {0,1}
            assert g_par[n_wit] == 2 and g_par[n_wit + p] != 2
        else:
            q = p // 4
            a = ctz(q)
            b = a + 1
            while 4 * (1 << b) < 4000:
                b += 2
            k = 1 << b
            assert 4 * k + p < N_par
            assert g_par[4 * k] != g_par[4 * k + p]
    # Also verify modulus sharpness for Borrow-Count Localization
    assert (borrow_count(2, 1) <= 1) is True and (borrow_count(2 + 2, 1) <= 1) is False
    print(f"  [OK] G_parity closed form verified for all 3 <= k < {N_par // 4}; constructive aperiodicity witness verified for all 1 <= p <= 1000")
    print(f"  [SHARP] Borrow-count localization modulus sharp: bc(2,1)=1<=1 (True) vs bc(4,1)=2<=1 (False)")

    print("\n=== 4. Negative / Mutation Testing (8 Adversarial Broken Certificates) ===")
    c_cp5 = certs["G_coprime_p5"]
    g_cp5_rules = SHOWCASE_GAMES[3][2]
    c_wb48 = certs["G_wallbreach_48"]
    g_wb48_rules = SHOWCASE_GAMES[2][2]

    # Mut 1: Corrupted table entry
    m1 = PeriodWinCert(c_cp5.preperiod, c_cp5.period, c_cp5.min_period,
                       c_cp5.table[:15] + [c_cp5.table[15] ^ 1] + c_cp5.table[16:],
                       c_cp5.pre_win_mask, c_cp5.per_win_mask, c_cp5.pre_moves[:], c_cp5.per_moves[:])
    # Mut 2: Unaligned period (period=5 instead of 20, missing dyadic factor 4)
    m2 = PeriodWinCert(15, 5, 5, c_cp5.table[:20],
                       c_cp5.pre_win_mask, c_cp5.per_win_mask, c_cp5.pre_moves[:], c_cp5.per_moves[:5])
    # Mut 3: Fake minimal-period compression (claim minPeriod=16 on G_wallbreach_48)
    m3 = PeriodWinCert(c_wb48.preperiod, c_wb48.period, 16, c_wb48.table[:],
                       c_wb48.pre_win_mask, c_wb48.per_win_mask & ((1 << 16) - 1),
                       c_wb48.pre_moves[:], c_wb48.per_moves[:])
    # Mut 4: Flipped bit in perWinMask
    m4 = PeriodWinCert(c_cp5.preperiod, c_cp5.period, c_cp5.min_period, c_cp5.table[:],
                       c_cp5.pre_win_mask, c_cp5.per_win_mask ^ 1, c_cp5.pre_moves[:], c_cp5.per_moves[:])
    # Mut 5: Flipped bit in preWinMask
    m5 = PeriodWinCert(c_cp5.preperiod, c_cp5.period, c_cp5.min_period, c_cp5.table[:],
                       c_cp5.pre_win_mask ^ 4, c_cp5.per_win_mask, c_cp5.pre_moves[:], c_cp5.per_moves[:])
    # Mut 6: Bad winning move in perMoves (lands on non-zero Grundy)
    bad_pm = c_cp5.per_moves[:]
    win_idx = next(i for i, mv in enumerate(bad_pm) if mv != 0)
    bad_pm[win_idx] = 3 if bad_pm[win_idx] != 3 else 7
    m6 = PeriodWinCert(c_cp5.preperiod, c_cp5.period, c_cp5.min_period, c_cp5.table[:],
                       c_cp5.pre_win_mask, c_cp5.per_win_mask, c_cp5.pre_moves[:], bad_pm)
    # Mut 7: Truncated preperiod n0=14 on G_coprime_p5 (misses peak g(14)=3!)
    m7 = PeriodWinCert(14, 20, 5, c_cp5.table[:34],
                       c_cp5.pre_win_mask & ((1 << 14) - 1), c_cp5.per_win_mask,
                       c_cp5.pre_moves[:21], c_cp5.per_moves[:])
    # Mut 8: Zero-step rule smuggling
    bad_game = [BitRule(0, GuardAlways())] + g_cp5_rules

    mutants = [
        ("Mut1_corrupt_table", g_cp5_rules, m1),
        ("Mut2_unaligned_period", g_cp5_rules, m2),
        ("Mut3_fake_minPeriod", g_wb48_rules, m3),
        ("Mut4_corrupt_perWinMask", g_cp5_rules, m4),
        ("Mut5_corrupt_preWinMask", g_cp5_rules, m5),
        ("Mut6_bad_winMove", g_cp5_rules, m6),
        ("Mut7_truncated_preperiod", g_cp5_rules, m7),
        ("Mut8_zero_step_rule", bad_game, c_cp5),
    ]
    for mname, mgame, mcert in mutants:
        res = check_cert(mgame, mcert)
        assert res is False, f"Mutant {mname} was NOT rejected!"
        print(f"  [REJECTED] {mname:26s} -> check_cert = {res}")

    if emit_lean:
        print("\n=== LEAN 4 GENERATED CERTIFICATES ===")
        for name, _, G in SHOWCASE_GAMES:
            rules_str = ", ".join(f"⟨{r.step}, {lean_guard(r.guard)}⟩" for r in G)
            print(f"def {name} : BitGame := [{rules_str}]")
            print(emit_lean_cert(name, certs[name]))
            print()


if __name__ == "__main__":
    verify_all(emit_lean=("--emit-lean" in sys.argv))
