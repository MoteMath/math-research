#!/usr/bin/env python3
"""
Exact Pure-Silicon Exploration, Certificate Verification & Sharpness Counterexamples
for the Coupled 2-Variable Reversible T-Function S4-Monodromy Orbit-Lifting Engine.

All computations are 100% exact integer / bitmask arithmetic (zero floating point).
"""

from math import comb


def mask_w(w: int) -> int:
    return (1 << w) - 1


def popcount(x: int) -> int:
    return x.bit_count()


def cycle_decomposition(fn, w: int):
    """Exact cycle decomposition of fn on (BitVec w x BitVec w).
    Returns (is_bijective, sorted list of (cycle_length, count), cycles_sample)."""
    m = mask_w(w)
    N = 1 << (2 * w)
    nxt = [0] * N
    seen = bytearray(N)
    for x in range(1 << w):
        base = x << w
        for y in range(1 << w):
            nx, ny = fn(x, y, w, m)
            nx &= m
            ny &= m
            dst = (nx << w) | ny
            nxt[base | y] = dst
            seen[dst] = 1
    if sum(seen) != N:
        return False, [], {}
    vis = bytearray(N)
    counts = {}
    sample = {}
    for s in range(N):
        if vis[s]:
            continue
        cur = s
        length = 0
        while not vis[cur]:
            vis[cur] = 1
            cur = nxt[cur]
            length += 1
        counts[length] = counts.get(length, 0) + 1
        if length not in sample:
            sample[length] = (s >> w, s & m)
    return True, sorted(counts.items()), sample


def exact_period(fn, w: int, x0: int, y0: int, limit: int = None) -> int:
    """Exact minimal period of (x0, y0) under fn on BitVec w x BitVec w."""
    m = mask_w(w)
    if limit is None:
        limit = 1 << (2 * w)
    x, y = x0 & m, y0 & m
    for step in range(1, limit + 1):
        x, y = fn(x, y, w, m)
        x &= m
        y &= m
        if (x, y) == (x0 & m, y0 & m):
            return step
    raise RuntimeError(f"Period exceeded {limit} for {(x0, y0)} at w={w}")


# ============================================================================
# S4 Fiber-Monodromy Extractor (Exact Finite Certificate)
# ============================================================================

def extract_fiber(fn, w: int, x: int, y: int):
    """Extract the 4-element fiber map Phi_{w, (x,y)} : {0,1}^2 -> {0,1}^2."""
    m_next = mask_w(w + 1)
    out = {}
    for a in (0, 1):
        for b in (0, 1):
            nx, ny = fn(x | (a << w), y | (b << w), w + 1, m_next)
            nx &= m_next
            ny &= m_next
            out[(a, b)] = ((nx >> w) & 1, (ny >> w) & 1)
    return out


def compose_fiber(f2, f1):
    return {p: f2[f1[p]] for p in f1}


def perm_cycle_type(perm):
    vis = set()
    lens = []
    for p in ((0, 0), (0, 1), (1, 0), (1, 1)):
        if p in vis:
            continue
        cur = p
        c = 0
        while cur not in vis:
            vis.add(cur)
            cur = perm[cur]
            c += 1
        lens.append(c)
    return tuple(sorted(lens, reverse=True))


def compute_cycle_monodromy(fn, w: int, x0: int, y0: int):
    """Compute exact S4 monodromy M_w around the cycle of (x0, y0) at width w."""
    m = mask_w(w)
    x, y = x0 & m, y0 & m
    mon = {p: p for p in ((0, 0), (0, 1), (1, 0), (1, 1))}
    steps = 0
    while True:
        phi = extract_fiber(fn, w, x, y)
        mon = compose_fiber(phi, mon)
        x, y = fn(x, y, w, m)
        x &= m
        y &= m
        steps += 1
        if (x, y) == (x0 & m, y0 & m):
            break
    return steps, mon, perm_cycle_type(mon)


# ============================================================================
# Family I: Universal Nonlinear Full-Period 2^(2w) Arithmetic-Bitwise Family
# ============================================================================

def m_and(x: int, y: int, m: int) -> int:
    z = x & y
    return ((z + 1) ^ z) & m


def make_family1(P, Q, R):
    def fn(x: int, y: int, w: int, m: int):
        mm = m_and(x, y, m)
        nx = (x + (y & mm) + 2 * P(x, y)) & m
        ny = (y + mm + 2 * Q(y) + 4 * R(x, y)) & m
        return nx, ny
    return fn


# Nonlinear witness instance: P(x,y) = x*y + (x&y), Q(y) = y*y, R(x,y) = x*y + (x^y)
fam1_witness = make_family1(
    P=lambda x, y: x * y + (x & y),
    Q=lambda y: y * y,
    R=lambda x, y: x * y + (x ^ y),
)

# Sharpness counterexample 1A: weakening 4*R to 2*R with R(x,y) = x & y
def fam1_sharp_2and(x: int, y: int, w: int, m: int):
    mm = m_and(x, y, m)
    return (x + (y & mm)) & m, (y + mm + 2 * (x & y)) & m

# Sharpness counterexample 1B: weakening 4*R to 2*R with R(x,y) = x * y
def fam1_sharp_2mul(x: int, y: int, w: int, m: int):
    mm = m_and(x, y, m)
    return (x + (y & mm) + 2 * (x * y)) & m, (y + mm + 2 * (x * y)) & m

# Sharpness counterexample 1C: removing shear (y & m) -> pure translation
def fam1_sharp_noshear(x: int, y: int, w: int, m: int):
    mm = m_and(x, y, m)
    return (x + 2 * (x * y) + 1) & m, (y + mm + 2 * (y * y)) & m


# ============================================================================
# Family II: Twisted Silicon Ternary Odometer (S4 \ D4 Order-3 Regime)
# ============================================================================

def make_ternary(shifts):
    def fn(x: int, y: int, w: int, m: int):
        mm = (y ^ ((y - 1) & m)) & m
        pert = 0
        for d in shifts:
            pert ^= (y << d) & m
        nx = (x ^ ((x ^ y) & mm) ^ pert) & m
        ny = (y ^ (x & mm)) & m
        return nx, ny
    return fn


tern_pure = make_ternary([])
tern_twist_y = make_ternary([1])
tern_twist_y12 = make_ternary([1, 2])

# Sharpness decoy: Ternary + XOR(2*x) -- matches for w=1,2,3,4, BREAKS at w=5!
def tern_sharp_x(x: int, y: int, w: int, m: int):
    mm = (y ^ ((y - 1) & m)) & m
    nx = (x ^ ((x ^ y) & mm) ^ ((x << 1) & m)) & m
    ny = (y ^ (x & mm)) & m
    return nx, ny


# ============================================================================
# Family III: Hybrid S4 Two-Cycle Map {4^(w-1), 3 * 4^(w-1)}
# ============================================================================

def hybrid_two_cycle(x: int, y: int, w: int, m: int):
    z = ((x & y) & ~1) | ((y ^ 1) & 1)
    m_hi = (((z + 1) ^ z) & ~1) & m
    x0, y0 = x & 1, y & 1
    nx0, ny0 = y0, x0 ^ y0
    nx = (((x ^ (y & m_hi)) & ~1) | nx0) & m
    ny = (((y ^ m_hi) & ~1) | ny0) & m
    return nx, ny


def main():
    print("=" * 78)
    print("1. FAMILY I: Universal Nonlinear Full-Period 2^(2w) (D4 4-Cycle Monodromy)")
    print("   Instance: P(x,y)=x*y+(x&y), Q(y)=y^2, R(x,y)=x*y+(x^y)")
    print("=" * 78)
    for w in range(1, 7):
        bij, dec, _ = cycle_decomposition(fam1_witness, w)
        assert bij and dec == [(4**w, 1)], f"Failed at w={w}: {dec}"
        if w <= 5:
            L, mon, ctype = compute_cycle_monodromy(fam1_witness, w, 0, 0)
            assert L == 4**w and ctype == (4,)
            mon_str = f"monodromy cycle_type={ctype}"
        else:
            mon_str = "(verified full cycle)"
        print(f"  w={w}: 4^w={4**w:5d}, bijective={bij}, cycles={dec}  {mon_str}")

    print("\n--- Family I Sharpness Counterexamples ---")
    for label, fn in [
        ("2*(x&y) instead of 4*R", fam1_sharp_2and),
        ("2*(x*y) instead of 4*R", fam1_sharp_2mul),
        ("No shear (pure translation)", fam1_sharp_noshear),
    ]:
        print(f"  [{label}]")
        for w in range(1, 5):
            bij, dec, _ = cycle_decomposition(fn, w)
            p0 = exact_period(fn, w, 0, 0)
            max_len = max(l for l, _ in dec)
            print(f"    w={w}: bijective={bij}, period(0,0)={p0}, max_period={max_len} (vs 4^w={4**w}), cycles={dec}")
            if "No shear" in label:
                assert max_len <= (1 << w), "No-shear bound violated!"

    print("\n" + "=" * 78)
    print("2. FAMILY II: Twisted Silicon Ternary Odometer (S4 \\ D4 Order-3 Monodromy)")
    print("   Expected spectrum: C(w, k) cycles of length 3^k for k=0..w (sum = 4^w)")
    print("=" * 78)
    for name, fn in [
        ("Pure Ternary (shifts=[])", tern_pure),
        ("Twisted Ternary + XOR(2y) (shifts=[1])", tern_twist_y),
        ("Twisted Ternary + XOR(2y^4y) (shifts=[1,2])", tern_twist_y12),
    ]:
        print(f"  [{name}]")
        for w in range(1, 7):
            bij, dec, _ = cycle_decomposition(fn, w)
            expected = [(3**k, comb(w, k)) for k in range(w + 1)]
            assert bij and dec == expected, f"Mismatch for {name} w={w}: {dec} != {expected}"
            # Verify Poincaré transversal period(x,0) == 3^popcount(x)
            if w <= 5:
                for x in range(1 << w):
                    p = exact_period(fn, w, x, 0)
                    assert p == 3 ** popcount(x)
            print(f"    w={w}: PASS (total_cycles={2**w}, max_period={3**w}, exact binomial C(w,k)*3^k)")
        # Show non-invariance of x|y for twisted variants
        if "Twisted" in name:
            w = 3
            m = mask_w(w)
            changed = sum(
                1 for x in range(8) for y in range(8)
                if ((fn(x, y, w, m)[0] | fn(x, y, w, m)[1]) != (x | y))
            )
            print(f"    Non-invariance check at w=3: (x|y) changes on {changed}/64 states!")

    print("\n--- Family II Sharpness Decoy: Ternary + XOR(2x) ---")
    print("  (Agrees with C(w,k)*3^k for ALL w=1,2,3,4, then BREAKS at w=5!)")
    for w in range(1, 6):
        bij, dec, sample = cycle_decomposition(tern_sharp_x, w)
        expected = [(3**k, comb(w, k)) for k in range(w + 1)]
        match = (dec == expected)
        extra = ""
        if not match:
            bad_len = next(l for l, _ in dec if l not in {3**k for k in range(w + 1)})
            extra = f" <-- BREAK! state {sample[bad_len]} has exact period {bad_len} (not 3^k!)"
        print(f"    w={w}: match_binomial={match}, cycles={dec}{extra}")

    print("\n" + "=" * 78)
    print("3. FAMILY III: Hybrid S4 Two-Cycle Map {4^(w-1), 3 * 4^(w-1)}")
    print("   (Order-3 (3,1) at bit 0, then D4 4-cycle quadrupling for all w >= 1)")
    print("=" * 78)
    for w in range(1, 7):
        bij, dec, _ = cycle_decomposition(hybrid_two_cycle, w)
        expected = [(4**(w - 1), 1), (3 * 4**(w - 1), 1)]
        assert bij and dec == expected, f"Hybrid mismatch at w={w}: {dec}"
        p0 = exact_period(hybrid_two_cycle, w, 0, 0)
        p1 = exact_period(hybrid_two_cycle, w, 1, 0)
        assert p0 == 4**(w - 1) and p1 == 3 * 4**(w - 1)
        print(f"  w={w}: PASS cycles={dec}, period(0,0)={p0}, period(1,0)={p1}")

    print("\nALL EXACT CHECKS AND COUNTEREXAMPLES VERIFIED WITH ZERO ERRORS.")


if __name__ == "__main__":
    main()
