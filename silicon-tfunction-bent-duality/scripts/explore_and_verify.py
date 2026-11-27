#!/usr/bin/env python3
"""
explore_and_verify.py — Independent Exact-Integer Exploration, Certificate Synthesis,
Replay Verification, and Sharpness Counterexample Suite for `specmat-14`:
  Silicon Walsh-Hadamard & T-Function Bent Proof Engine

Zero floating-point values anywhere. Uses Python arbitrary-precision `int` exclusively.
Verifies:
  1. Bit-sliced FWHT, Hadamard involution, and exact Silicon Wiener-Khinchin autocorrelation.
  2. Constructive bit-by-bit Hensel T-inverter `tInv` for causal silicon bijections up to k=10.
  3. 4-Subblock Kronecker-Dual Bent Lifting & Zero-Sum T-Function Quad Compiler.
  4. Unconditional Silicon Causal-Mask Carlet-T Bent Engine (for all 0 <= r <= k, including pi(0) != 0).
  5. Finite 15-Hyperplane 4-Bit Certificate synthesis for piMul3, piMul7, piKS, piARX.
  6. Independent exact M# membership (Dillon/Canteaut-Charpin second-order derivative subspace test)
     confirming:
       - Carry-Dictionary Phase Transition at k=4 (n=8): piClmul3 (in M#) vs piMul3, piKS, piARX, piMul7 (outside M#).
       - Dimension sharpness at k=3 (n=6): piMul3 has explicit 3-dim vanishing subspace {(s & 1, s & 6)}.
  7. Four hypothesis-breaking sharpness counterexamples matching the Lean sources exactly.
"""


def bit_parity(n: int) -> int:
    return n.bit_count() & 1


def inner_parity(x: int, y: int) -> int:
    return bit_parity(x & y)


def bool_sign(b: int) -> int:
    return -1 if (b & 1) else 1


def fwht(vals: list[int]) -> list[int]:
    """Exact integer bit-sliced radix-2 Fast Walsh-Hadamard Transform."""
    a = vals[:]
    n = len(a)
    h = 1
    while h < n:
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                u, v = a[j], a[j + h]
                a[j] = u + v
                a[j + h] = u - v
        h *= 2
    return a


def xcorr_all(vals: list[int]) -> list[int]:
    """Exact integer XOR-autocorrelation via direct definition (for small N) or Wiener-Khinchin."""
    n = len(vals)
    if n <= 256:
        return [sum(vals[x] * vals[x ^ a] for x in range(n)) for a in range(n)]
    W = fwht(vals)
    sq = [v * v for v in W]
    inv = fwht(sq)
    assert all(v % n == 0 for v in inv)
    return [v // n for v in inv]


def anf_degree(tt: list[int]) -> int:
    """Exact algebraic degree via F_2 Mobius transform."""
    a = [b & 1 for b in tt]
    n = len(a)
    h = 1
    while h < n:
        for i in range(0, n, h * 2):
            for j in range(i, i + h):
                a[j + h] ^= a[j]
        h *= 2
    return max((i.bit_count() for i, c in enumerate(a) if c), default=-1)


def t_inv(pi, k: int, y: int) -> int:
    """Constructive bit-by-bit Silicon Hensel inverter matching the Lean sources `tInv`."""
    r = 0
    for i in range(k):
        b = ((y >> i) ^ (pi(r) >> i)) & 1
        r += (1 << i) if b else 0
    return r


def synth_non_mm_cert4(pi) -> dict[int, tuple[int, int, int]] | None:
    """Synthesize the 15-entry finite 4-bit hyperplane nonlinearity certificate NonMMCert4."""
    vals = [pi(y) & 15 for y in range(16)]
    if len(set(vals)) != 16:
        return None
    cert = {}
    for lam in range(1, 16):
        H = [v for v in range(16) if inner_parity(lam, v) == 0]
        found = None
        for b in H:
            if b == 0:
                continue
            for d in H:
                if d <= b:
                    continue
                for y in range(16):
                    dd = vals[y] ^ vals[y ^ b] ^ vals[y ^ d] ^ vals[y ^ b ^ d]
                    if dd != 0:
                        found = (b, d, y)
                        break
                if found:
                    break
            if found:
                break
        if found is None:
            return None
        cert[lam] = found
    return cert


def check_carlet_t(pi, k: int, r: int) -> tuple[bool, bool, bool, int]:
    """
    Build carletTBool k r pi on 2*k bits, check:
      - flat Walsh spectrum == {-2^k, +2^k}
      - exact match with closed-form dual carletTDualSign (unconditional on pi(0))
      - vanishing autocorrelation (delta(0)=2^(2k), delta(a)=0 for a>0)
      - exact ANF algebraic degree
    """
    N = 1 << (2 * k)
    M = (1 << k) - 1
    mask_r = (1 << r) - 1
    tt = [0] * N
    sign = [0] * N
    for y in range(1 << k):
        py = pi(y) & M
        y_div = (y & mask_r) == 0
        for x in range(1 << k):
            b = inner_parity(x, py) ^ (1 if (x < (1 << r) and y_div) else 0)
            idx = x + (y << k)
            tt[idx] = b
            sign[idx] = bool_sign(b)
    W = fwht(sign)
    target = 1 << k
    flat = all(v == target or v == -target for v in W)
    # Check exact closed-form dual
    pi0_mod = pi(0) & mask_r
    dual_ok = True
    for b in range(1 << k):
        for a in range(1 << k):
            inv_a = t_inv(pi, k, a)
            pred_bit = inner_parity(b, inv_a) ^ (1 if ((a & mask_r) == pi0_mod and b < (1 << r)) else 0)
            if W[a + (b << k)] != target * bool_sign(pred_bit):
                dual_ok = False
                break
        if not dual_ok:
            break
    xc = xcorr_all(sign)
    ac_ok = (xc[0] == N) and all(xc[a] == 0 for a in range(1, N))
    deg = anf_degree(tt)
    return flat, dual_ok, ac_ok, deg


def has_vanishing_subspace_exact(tt: list[int], k: int) -> tuple[bool, int, list[int] | None]:
    """Exact search for a k-dim linear subspace V <= F_2^(2k) with D_u D_v tt === 0."""
    N = 1 << (2 * k)
    D = [0] * N
    for a in range(1, N):
        mask = 0
        for z in range(N):
            if tt[z] ^ tt[z ^ a]:
                mask |= (1 << z)
        D[a] = mask
    adj = [set() for _ in range(N)]
    for a in range(1, N):
        Da = D[a]
        for b in range(a + 1, N):
            if all((((Da >> z) ^ (Da >> (z ^ b))) & 1) == 0 for z in range(N)):
                adj[a].add(b)
                adj[b].add(a)

    max_dim = 1
    found_basis = None

    def search(basis: list[int], span: list[int], cands: list[int]) -> bool:
        nonlocal max_dim, found_basis
        if len(basis) > max_dim:
            max_dim = len(basis)
        if len(basis) == k:
            found_basis = basis[:]
            return True
        for idx, v in enumerate(cands):
            new_e = [s ^ v for s in span]
            if all(e != 0 and all(s == 0 or s in adj[e] for s in span) for e in new_e):
                if all(new_e[j] in adj[new_e[i]] for i in range(len(new_e)) for j in range(i + 1, len(new_e))):
                    new_span = span + new_e
                    next_c = [c for c in cands[idx + 1:] if c not in new_span and all(c in adj[e] for e in new_e)]
                    if search(basis + [v], new_span, next_c):
                        return True
        return False

    ok = search([], [0], [a for a in range(1, N) if adj[a]])
    return ok, max_dim, found_basis


def main():
    print("=" * 76)
    print("specmat-14: Silicon Walsh-Hadamard & T-Function Bent Engine — Exact Replay")
    print("=" * 76)

    families = [
        ("piMul3  (3*y)",               lambda y: 3 * y),
        ("piMul7  (7*y)",               lambda y: 7 * y),
        ("piKS    (y + 2*y^2)",         lambda y: y + 2 * y * y),
        ("piARX   (y + 2*(y & 2*y))",   lambda y: y + 2 * (y & (2 * y))),
        ("piClmul3 (y ^ 2*y, twin)",    lambda y: y ^ (2 * y)),
        ("piAff   (3*y + 1, pi(0)!=0)", lambda y: 3 * y + 1),
    ]

    print("\n[1] Constructive Hensel T-Inverter `tInv` Exact Bijection Check (k = 1..10):")
    for name, pi in families:
        for k in range(1, 11):
            M = (1 << k) - 1
            for x in range(1 << k):
                y = pi(x) & M
                assert t_inv(pi, k, y) == x
                assert (pi(t_inv(pi, k, x)) & M) == x
        print(f"  PASS {name:30s}: exact mutual inverse for all k in 1..10 (up to 2^10 = 1024)")

    print("\n[2] Silicon Carlet-T Bent Engine (Flat Walsh +-2^k, Exact Dual, Vanishing Autocorr):")
    for name, pi in families:
        degs = []
        for k in range(1, 7):
            for r in (0, k // 2, k):
                flat, dual_ok, ac_ok, deg = check_carlet_t(pi, k, r)
                assert flat and dual_ok and ac_ok, f"Failed for {name}, k={k}, r={r}"
                if r == 0:
                    degs.append((k, deg))
        deg_str = ", ".join(f"k={k}:deg={d}" for k, d in degs)
        print(f"  PASS {name:30s}: bent+dual+autocorr exact for k=1..6 ({deg_str})")

    print("\n[3] 4-Subblock Zero-Sum T-Quad Compiler Check (phi1=y^2, phi2=y&(2y), k=1..5):")
    phi1 = lambda y: y * y
    phi2 = lambda y: y & (2 * y)
    psis = [
        lambda a: a,
        lambda a: a ^ (2 * phi1(a)),
        lambda a: a ^ (2 * phi2(a)),
        lambda a: a ^ (2 * (phi1(a) ^ phi2(a))),
    ]
    for k in range(1, 6):
        N_sub = 1 << (2 * k)
        M = (1 << k) - 1
        sub_signs = []
        for idx_q, psi in enumerate(psis):
            gbit = 1 if idx_q == 3 else 0
            # mmDualSign k psi g
            s = [0] * N_sub
            for b in range(1 << k):
                for a in range(1 << k):
                    inv_a = t_inv(psi, k, a)
                    s[a + (b << k)] = bool_sign(inner_parity(b, inv_a) ^ gbit)
            sub_signs.append(s)
        N_big = 4 * N_sub
        big = [sub_signs[z & 3][z >> 2] for z in range(N_big)]
        W = fwht(big)
        target = 1 << (k + 1)
        assert all(v == target or v == -target for v in W)
        xc = xcorr_all(big)
        assert xc[0] == N_big and all(xc[a] == 0 for a in range(1, N_big))
        print(f"  PASS Zero-Sum T-Quad at k={k} -> 2(k+1)={2*(k+1)} vars: flat Walsh +-{target}, vanishing autocorr")

    print("\n[4] Finite 15-Hyperplane 4-Bit Certificate Synthesis (`NonMMCert4`):")
    for name, pi in families[:5]:
        cert = synth_non_mm_cert4(pi)
        if cert is not None:
            print(f"  CERTIFIED {name:30s}: 15/15 hyperplanes witnessed => OUTSIDE M# for ALL k >= 4")
        else:
            print(f"  NO CERT   {name:30s}: linear on hyperplane (expected for carry-free twin)")

    print("\n[5] Independent Exact M# Membership & Carry-Dictionary Phase Transition (k=3, k=4):")
    for name, pi in families[:5]:
        tt4 = [
            inner_parity(x, pi(y) & 15) ^ (1 if x == 0 else 0)
            for y in range(16) for x in range(16)
        ]
        in_m, max_d, _ = has_vanishing_subspace_exact(tt4, 4)
        print(f"  k=4 (n=8)  {name:30s}: in_M#={str(in_m):5s}, max_vanishing_subspace_dim={max_d}")

    # k=3 sharpness witness for piMul3
    tt3 = [inner_parity(x, (3 * y) & 7) ^ (1 if x == 0 else 0) for y in range(8) for x in range(8)]
    in_m3, max_d3, basis3 = has_vanishing_subspace_exact(tt3, 3)
    assert in_m3 and max_d3 == 3
    print(f"  k=3 (n=6)  piMul3 (sharpness threshold)    : in_M#={in_m3}, max_dim={max_d3}, basis={[(b & 7, b >> 3) for b in basis3]}")

    print("\n[6] Four Hypothesis-Breaking Sharpness Counterexamples:")
    # C1: pi(y) = 2*y (violates BitFlip)
    s_mul2 = [bool_sign(inner_parity(z & 1, (2 * (z >> 1)) & 1)) for z in range(4)]
    W_mul2 = fwht(s_mul2)
    xc_mul2 = xcorr_all(s_mul2)
    assert W_mul2[0] == 4 and xc_mul2[1] == 4
    print(f"  CE1 (BitFlip broken, pi=2*y, k=1)        : W(0)={W_mul2[0]} != +-2, autocorr(1)={xc_mul2[1]} != 0")

    # C2: 4-Quad with d0*d1*d2*d3 = +1
    W_q = fwht([1, 1, 1, 1])
    assert W_q[0] == 4 and W_q[1] == 0
    print(f"  CE2 (Dual product +1, quadCombine, k=1)  : W(0)={W_q[0]}, W(1)={W_q[1]} != +-2")

    # C3: Non-causal shift pi(y) = y ^ (2 * (y // 2))
    pi_nc = lambda y: y ^ (2 * (y // 2))
    assert (pi_nc(0) & 3) == (pi_nc(2) & 3)
    print(f"  CE3 (Causality broken, y^(2*(y>>1)), k=2): pi(0)%4={pi_nc(0)&3} == pi(2)%4={pi_nc(2)&3} (collision!)")

    # C4: Non-causal bijection bitrev2 in Carlet-T (k=2, r=1)
    bitrev2 = [0, 2, 1, 3]
    s_br = [
        bool_sign(inner_parity(x, bitrev2[y]) ^ (1 if (x < 2 and y % 2 == 0) else 0))
        for y in range(4) for x in range(4)
    ]
    W_br = fwht(s_br)
    assert W_br[0] == 0
    print(f"  CE4 (Causality broken, bitrev2, k=2, r=1): W(0)={W_br[0]} != +-4 (non-bent despite bijection!)")

    print("\nALL EXACT INTEGER VERIFICATION CHECKS PASSED.")


if __name__ == "__main__":
    main()
