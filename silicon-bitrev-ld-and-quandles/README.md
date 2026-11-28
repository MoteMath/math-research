# Pure-Silicon Bit-Reversal LD-Systems and Non-Alexander XOR-Carry Knot Quandles

Zero-dependency Lean 4.34.1 formalization of two non-classical, non-associative algebraic structures discovered by bare-metal RDNA3 GPU mining (`track_b_alien_algebra.hsaco`, zero FP ISA ops) over $\mathbb{Z}/2^w\mathbb{Z}$ and validated bit-for-bit on CPU.

## Why These Confuse Classical Paper Algebra

1. **Shifted Bit-Reversal Left Self-Distributive (LD) Algebras (for ALL bit-widths $w$ and shifts $s$):**
   Mixing word-level **bit-reversal** (`bitrev`), **left-shift** (`<<< s`), and **carry-free bitwise addition / OR** looks wildly non-algebraic to classical paper intuition. Yet for **every** set $\alpha$ and **every** partial involution $\tau : \alpha \rightharpoonup \alpha$ ($\tau(a) = \mathrm{some}\,b \implies \tau(b) = \mathrm{some}\,a$), the operation
   ```math
   X \star_\tau Y = X \cup \tau(Y \setminus X)
   ```
   is **idempotent**, **left self-distributive** ($X \star (Y \star Z) = (X \star Y) \star (X \star Z)$, an LD-system / Laver-type algebra), **flexible** ($(X \star Y) \star X = X \star (Y \star X)$), and **neither associative nor commutative** whenever $\tau$ has any non-fixed pair.
   On `BitVec w`, the concrete GPU-discovered instruction sequence
   ```math
   x \star_{w,s} y \;=\; x \;\|\;\bigl(\mathrm{bitrev}_w(y \mathbin{\&} \lnot x) \ll s\bigr)
     \;=\; x + \Bigl(\bigl(\mathrm{bitrev}_w(y \mathbin{\&} \lnot x) \ll s\bigr) \mathbin{\&} \lnot x\Bigr)
   ```
   realizes $\star _ {\tau _ {w,s}}$ for the partial involution $\tau _ {w,s}(i) = w - 1 - (i - s)$ ($s \le i < w$) and satisfies all LD-system laws for **every** $w, s \in \mathbb{N}$!

2. **Non-Alexander, Non-Involutive Pure-Silicon Both-Sided Knot Quandles (for ALL bit-widths $w$):**
   Classical finite knot quandles on $\mathbb{Z}/2^w\mathbb{Z}$ are linear Alexander quandles $x \star y = (1 - t)x + t y$. Our GPU sweep unearthed a raw mixed **subtraction + XOR + addition** operation:
   ```math
   x \star_c y \;=\; (2x - y) - \bigl((2(y - x)) \oplus c\bigr) + c \pmod{2^w}
   ```
   which reduces via the exact bitwise identity $a + b = (a \oplus b) + 2(a \mathbin{\&} b)$ to
   ```math
   x \star_c y \;=\; y - 2\bigl((2(y - x)) \mathbin{\&} \lnot c\bigr) \pmod{2^w}.
   ```
   Whenever the effective inverted mask $\lnot c$ in bit positions $[1, w - 2]$ has **2-bit span** (contained in $\{a, a+1\}$ for any $a \ge 1$), the perturbation $g(d) = -2((2d) \mathbin{\&} \lnot c)$ lands in $2^{a+1}\mathbb{Z}/2^w\mathbb{Z}$ while depending **only** on $d \bmod 2^{a+1}$. By our general **Coset-Jump Knot Quandle Theorem**, any (completely non-linear!) function $g : \mathbb{Z}/2^k\mathbb{Z} \to 2^k\mathbb{Z}/2^w\mathbb{Z}$ with $g(0) = 0$ defines a **both-sided knot quandle** $x \star _ g y = y + g(y - x)$ (idempotent, left & right self-distributive, flexible, and left-bijective with explicit inverse $x \star _ g ^ {-1} z = z - g(z - x)$). At the GPU-discovered instance $w = 6, c = 51$ (`0b110011`), we certify that `xorCarryOp 6 51#6` is **neither Alexander/additive nor involutive**.

## Headline Theorems (All 10 Verified in Pure-Init Lean 4.34.1)

| Theorem | Statement Summary |
|---|---|
| `partialInvLD_idemp` | Idempotence $X \star _ \tau X = X$ for any partial involution $\tau$ |
| `partialInvLD_left_distrib` | Left self-distributivity $X \star _ \tau (Y \star _ \tau Z) = (X \star _ \tau Y) \star _ \tau (X \star _ \tau Z)$ |
| `partialInvLD_flexible` | Flexibility $(X \star _ \tau Y) \star _ \tau X = X \star _ \tau (Y \star _ \tau X)$ |
| `partialInvLD_non_assoc_non_comm` | Non-associativity and non-commutativity whenever $\tau$ has a 2-cycle |
| `bitrevShiftOp_eq_add` | Carry-free addition equivalence on `BitVec w` for all $w, s$ |
| `bitrevShiftOp_ld_laws` | All LD-system laws + non-assoc/non-comm for `bitrevShiftOp w s` ($w \ge s + 2$) |
| `cosetJump_quandle_laws` | Universal both-sided knot quandle + explicit inverse for any coset-jump map $g$ |
| `xorCarryOp_eq_and_not` | Exact reduction $(2x - y) - ((2(y - x)) \oplus c) + c = y - 2((2(y - x)) \mathbin{\&} \lnot c)$ |
| `xorCarryQuandle_twoBitMask` | Both-sided knot quandle laws for all $w$, $a \ge 1$, and 2-bit-span inverted masks |
| `xorCarryQuandle_nonAlexander_nonInvolutive` | Certified non-Alexander, non-involutive witness at $w = 6, c = 51$ |

## Building and Checking

```sh
lake build
lake build Challenge
lake env lean PrintAxioms.lean
```
