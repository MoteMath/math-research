# Gray-Code Carry Whitening and Balanced-Fiber Transducer Lifts (`gray-carry-whitening-transducer`)

## Synthetic Score

| Novelty (30%) | Surprise / Depth (20%) | Generality (20%) | Usefulness (20%) | Verification (10%) | Composite |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **8 / 10** | **9 / 10** | **9 / 10** | **8 / 10** | **10 / 10** | **86 / 100** |

*Heuristic self-rating (see the [root scoring rubric](../README.md#synthetic-score-matrix)): exact fiber counts $3 ^ {w - |z|}$ for the Gray-coded carry word of binary addition at every width, a carry-borrow orthogonality law with bijection, a radix-$B$ generalization and a Gaussian-norm impossibility for three or more operands, via a reusable finite-state balanced-fiber lifting engine, formalized in pure Lean 4 `Init` (zero Mathlib).*

## For Mathematicians

Let $G(n) = n \oplus (n \gg 1)$ be the reflected Gray code and $C$ the carry word of $a + b + c _ 0$. We prove the exact **whitening law**: for every width $w$ and every target $z < 2 ^ w$, the number of pairs $(a, b) \in [0, 2 ^ w) ^ 2$ with $G(C) \bmod 2 ^ w = z$ is $3 ^ {w - |z|}$, where $|z|$ is the popcount; the same count holds for the carry defect of Gray-code addition in Gray coordinates, and the untruncated parity-closed law on $[0, 2 ^ {w + 1})$ is `gray_carry_full_fiber_count`. For subtraction, the Gray carry and borrow words are **orthogonal**, $G(C) \mathbin{\&} G(B) = 0$ whenever $b + b _ 0 \le a$, with exact mask separation, an explicit bijection $\Phi _ {w, c _ 0, b _ 0}$ with a four-state inverse transducer, and the joint fiber law $[u \mathbin{\&} v = 0] \cdot 2 ^ {w - |u| - |v|}$.

All counts come from one reusable engine: a finite-state transducer whose one-bit slice counts are balanced (`transducer_balanced_fiber_lift`, `radix_balanced_fiber_lift`) has product-form fiber counts at every width. In base $B$ the carry-difference word has fiber count $\binom{B + 1}{2} ^ {w - |z|} \binom{B}{2} ^ {|z|}$ (`radix_carry_whitening_law`); orthogonality of carry and borrow fails in every base $B \ge 3$ so $B = 2$ is unique, and for $k \ge 3$ operands the Gaussian-integer norm identity $D(k, 0) ^ 2 + D(k, 1) ^ 2 = 2 ^ {k + 1}$ shows balanced whitening is impossible (`k_operand_whitening_impossibility`).

## For Non-Mathematicians

When you add two binary numbers, carries pop up in some columns and not others, and the pattern of carries looks random. Written in Gray code (the code used in rotary encoders, where consecutive numbers differ in one bit), we show it is perfectly even in a precise sense: out of all $4 ^ w$ pairs of $w$-bit numbers, each carry pattern $z$ occurs exactly $3 ^ {w - |z|}$ times. We also show that carries and borrows can never overlap in Gray code for binary, that this fails in every other number base, and that the evenness breaks for three or more operands.

---

A complete, sorry-free **pure Lean 4 `Init`** (zero Mathlib, no `native_decide`, no custom axioms) formalization. Full proofs live in `GrayCarryWhiteningTransducer/Theorems.lean`, definitions in `GrayCarryWhiteningTransducer/Defs.lean`; `Challenge.lean` states the headline theorems with `sorry` and `Solution.lean` proves the identical statements by delegation.

**Scope of the formal statement.** `k_operand_whitening_impossibility` is only the inequality of slice counts for the one transducer `multiCarrySlice1` defined in `Defs.lean`; it is not a proof that no multi-operand carry word is balanced, so the words "impossibility for three or more operands" in the summary above mean only this inequality.

## Main Theorems

| Theorem (in `Challenge.lean`) | Statement |
|---|---|
| `gray_carry_whitening_binary` | For every $w$, $c _ 0$ and $z < 2 ^ w$, exactly $3 ^ {w - \lvert z \rvert}$ pairs of $w$-bit operands have Gray-coded carry word equal to $z$ modulo $2 ^ w$. |
| `gray_carry_whitening_gray_coords` | The same count $3 ^ {w - \lvert z \rvert}$ holds for the carry defect of Gray-code addition, computed in Gray coordinates. |
| `gray_carry_full_fiber_count` | For $z < 2 ^ {w + 1}$ the number of pairs with Gray-coded carry word exactly $z$ is $3 ^ {w - \lvert z \bmod 2 ^ w \rvert}$ if the parity of $z$ equals $c _ 0$, and $0$ otherwise. |
| `gray_joint_carry_borrow_fiber_count` | For $u, v < 2 ^ w$ the number of pairs with Gray carry word $u$ and Gray borrow word $v$ (mod $2 ^ w$) is $2 ^ {w - \lvert u \rvert - \lvert v \rvert}$ if $u \mathbin{\&} v = 0$ and $0$ otherwise. |
| `gray_carry_borrow_orthogonal` | If $b + b _ 0 \le a$ then the Gray-coded carry word of $a + b + c _ 0$ and the Gray-coded borrow word of $a - b - b _ 0$ have disjoint bits. |
| `radix_carry_whitening_law` | For every base $B \ge 2$, width $w$ and $z < 2 ^ w$, the carry-difference word has fiber count $\binom{B + 1}{2} ^ {w - \lvert z \rvert} \binom{B}{2} ^ {\lvert z \rvert}$. |
| `k_operand_whitening_impossibility` | For every arity $k \ge 3$ the one-bit slice counts `multiCarrySlice1 k 0`, `multiCarrySlice1 k 1`, `multiCarrySlice1 k 2` of the multi-operand carry transducer are not all equal; this blocks the balanced-fiber lifting argument used for $k = 2$, but the statement does not itself compute the fiber counts of $k$-operand addition. |
| `radix_carry_borrow_orthogonality_binary_unique` | For every base $B \ge 3$ there are digits $d _ 1, d _ 2 < B$ producing a carry and a borrow at the same position, so $B = 2$ is the unique radix of carry-borrow orthogonality. |

## Proof Architecture

1. **Balanced-fiber lifting (`transducer_balanced_fiber_lift`, `radix_balanced_fiber_lift`):** if every state's one-bit slice count equals a fixed multiplicity function, the width-$w$ fiber count is the product of multiplicities along the target.
2. **Bijection and bisimulation (`transducer_bijection_lift`, `transducer_quotient_bisim`, `phiMap_bijection`):** a finite check lifts to an exact bijection $\Phi _ {w, c _ 0, b _ 0}$ with an explicit four-state inverse and to a quotient bisimulation for Gray addition.
3. **Gray bridge (`testBit_gray_carryWord`, `gray_carry_borrow_mask_separation`):** the Gray code of the carry word is expressed bitwise through $\mathrm{gray}(a + b) \oplus \mathrm{gray}(a - b)$, separating carry and borrow masks.
4. **Radix generalization (`radix_carry_whitening_law`, `radix_carry_borrow_orthogonality_binary_unique`):** the same lift in base $B$ gives binomial fiber counts and shows orthogonality is special to $B = 2$.
5. **Impossibility (`carrySumBias_norm_sq`, `k_operand_whitening_impossibility`):** the norm identity $D(k, 0) ^ 2 + D(k, 1) ^ 2 = 2 ^ {k + 1}$ rules out balanced slices for $k \ge 3$ operands.

## Prior-Art Context

- **Classical background:** the reflected Gray code and its unit-step property (Gray 1953; Knuth, TAOCP Vol. 4A, 7.2.1.1). The four-state serial Gray-code adder already appears in **Lucal (1959)** and **Doran (2007, *The Gray Code*)**; `grayAddWith_eq_transducer4` is a Lean quotient-bisimulation mechanization of that adder generalized to carry-in, not a new state reduction. The single zero-carry count $3 ^ w$ is folklore (the $z = 0$ case).
- **Contents (not independently reviewed; no prior-art search is recorded):** the balanced-fiber and bijection lifting engine, carry-borrow Gray orthogonality with the bijection $\Phi$, the joint fiber law, the hypercube whitening law $3 ^ {w - |z|}$, its radix-$B$ generalization and the $k \ge 3$ impossibility.

## Build & Verification

```bash
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

See [`AUDIT.md`](AUDIT.md) for the verbatim build and `#print axioms` receipts and [`comparator.json`](comparator.json) for the Palomar Comparator / `nanoda` manifest. `scripts/explore_and_verify.py` replays the finite exact checks (integers only, zero floats).
