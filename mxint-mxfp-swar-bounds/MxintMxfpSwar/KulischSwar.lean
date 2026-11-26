/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MxintMxfpSwar.Defs

/-!
# Theorems 3 & 6: Exact Signed Kulisch Accumulator Bit-Width Laws & Exact Integer Associativity

Proves:
3. `kulisch_mxint_zero_overflow_swar_exact`: Exact signed Kulisch accumulator bounds for
   symmetric and asymmetric `MXINT_w × MXINT_w` dot products, zero-overflow `int12` (`MXINT4`)
   and 2-lane `int16` SWAR (`MXINT6`) at OCP `B = 32`, and exact `+1` overflow of asymmetric
   `MXINT6 [-32, 31]` (`32 * (-32) * (-32) = 32768 > 32767`).
6. `mxint_exact_integer_associativity`: Unconditional associativity, block-split additivity,
   and bijection / permutation invariance of exact signed Kulisch `Int` dot products.
-/

namespace MxintMxfpSwar

/-! ### `intFinSum` Helper Lemmas -/

theorem intFinSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    intFinSum f = intFinSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [intFinSum]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

theorem intFinSum_const {n : Nat} (c : Int) :
    intFinSum (fun _ : Fin n => c) = (n : Int) * c := by
  induction n with
  | zero => simp [intFinSum]
  | succ n ih =>
    simp only [intFinSum]
    rw [ih]
    grind

theorem intFinSum_add {n : Nat} (f g : Fin n → Int) :
    intFinSum (fun i => f i + g i) = intFinSum f + intFinSum g := by
  induction n with
  | zero => simp [intFinSum]
  | succ n ih =>
    simp only [intFinSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem intFinSum_le_intFinSum {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    intFinSum f ≤ intFinSum g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [intFinSum]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last n)
    omega

theorem intFinSum_single {n : Nat} (i0 : Fin n) (c : Int) :
    intFinSum (fun j : Fin n => if j = i0 then c else 0) = c := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    simp only [intFinSum]
    by_cases hlast : i0 = Fin.last n
    · subst hlast
      have h1 : intFinSum (fun i : Fin n => if i.castSucc = Fin.last n then c else 0) = 0 := by
        have hc : intFinSum (fun i : Fin n => if i.castSucc = Fin.last n then c else 0) =
            intFinSum (fun _ : Fin n => (0 : Int)) := by
          apply intFinSum_congr
          intro i
          have hne : i.castSucc ≠ Fin.last n := by
            intro heq
            have hv : i.val = n := by simpa [Fin.val_castSucc, Fin.val_last] using congrArg Fin.val heq
            omega
          simp [hne]
        rw [hc, intFinSum_const]; omega
      rw [h1]; simp
    · have hlt : i0.val < n := by
        have hval : i0.val ≠ n := by
          intro h0; apply hlast; exact Fin.ext (by simpa [Fin.val_last] using h0)
        have := i0.isLt; omega
      let i0' : Fin n := ⟨i0.val, hlt⟩
      have hi0eq : i0 = i0'.castSucc := Fin.ext rfl
      have h1 : intFinSum (fun i : Fin n => if i.castSucc = i0 then c else 0) = c := by
        have hc : intFinSum (fun i : Fin n => if i.castSucc = i0 then c else 0) =
            intFinSum (fun i : Fin n => if i = i0' then c else 0) := by
          apply intFinSum_congr
          intro i
          rw [hi0eq]
          by_cases h : i = i0'
          · subst h; simp
          · have h2 : i.castSucc ≠ i0'.castSucc := by
              intro heq; apply h; exact Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val heq)
            simp [h, h2]
        rw [hc]; exact ih i0'
      have h2 : (if Fin.last n = i0 then c else 0) = 0 := by
        have hne : Fin.last n ≠ i0 := Ne.symm hlast
        simp [hne]
      rw [h1, h2]; omega

/-! ### Theorem 3: Kulisch Signed Accumulator Bounds -/

private theorem int_mul_bounds_sym {M x y : Int}
    (hx : -M ≤ x ∧ x ≤ M) (hy : -M ≤ y ∧ y ≤ M) :
    -(M * M) ≤ x * y ∧ x * y ≤ M * M := by
  have h1 : 0 ≤ (M - x) * (M - y) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (M + x) * (M + y) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0 ≤ (M - x) * (M + y) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0 ≤ (M + x) * (M - y) := Int.mul_nonneg (by omega) (by omega)
  have hlo : 0 ≤ (M - x) * (M - y) + (M + x) * (M + y) := Int.add_nonneg h1 h2
  have hhi : 0 ≤ (M - x) * (M + y) + (M + x) * (M - y) := Int.add_nonneg h3 h4
  have heq1 : (M - x) * (M - y) + (M + x) * (M + y) = 2 * (M * M + x * y) := by grind
  have heq2 : (M - x) * (M + y) + (M + x) * (M - y) = 2 * (M * M - x * y) := by grind
  rw [heq1] at hlo
  rw [heq2] at hhi
  constructor <;> omega

private theorem int_mul_bounds_asym {A x y : Int} (hA : 1 ≤ A)
    (hx : -A ≤ x ∧ x ≤ A - 1) (hy : -A ≤ y ∧ y ≤ A - 1) :
    -(A * (A - 1)) ≤ x * y ∧ x * y ≤ A * A := by
  constructor
  · have hAnn : 0 ≤ A * (A - 1) := Int.mul_nonneg (by omega) (by omega)
    by_cases hx0 : 0 ≤ x
    · by_cases hy0 : 0 ≤ y
      · have hxy : 0 ≤ x * y := Int.mul_nonneg hx0 hy0
        omega
      · have h1 : 0 ≤ (A - 1 - x) * A := Int.mul_nonneg (by omega) (by omega)
        have h2 : 0 ≤ x * (A + y) := Int.mul_nonneg hx0 (by omega)
        have hsum : 0 ≤ (A - 1 - x) * A + x * (A + y) := Int.add_nonneg h1 h2
        have heq : (A - 1 - x) * A + x * (A + y) = A * (A - 1) + x * y := by grind
        rw [heq] at hsum; omega
    · by_cases hy0 : 0 ≤ y
      · have h1 : 0 ≤ (A - 1 - y) * A := Int.mul_nonneg (by omega) (by omega)
        have h2 : 0 ≤ y * (A + x) := Int.mul_nonneg hy0 (by omega)
        have hsum : 0 ≤ (A - 1 - y) * A + y * (A + x) := Int.add_nonneg h1 h2
        have heq : (A - 1 - y) * A + y * (A + x) = A * (A - 1) + x * y := by grind
        rw [heq] at hsum; omega
      · have hxy : 0 ≤ (-x) * (-y) := Int.mul_nonneg (by omega) (by omega)
        have heq : (-x) * (-y) = x * y := by grind
        rw [heq] at hxy; omega
  · exact (int_mul_bounds_sym ⟨hx.1, by omega⟩ ⟨hy.1, by omega⟩).2

theorem kulisch_sym_bounds {w B : Nat} (x y : Fin B → Int)
    (hx : InSymRange w x) (hy : InSymRange w y) :
    -kulischSymMax w B ≤ intDot x y ∧ intDot x y ≤ kulischSymMax w B := by
  unfold kulischSymMax intDot
  let M : Int := (mxintMax w : Int)
  constructor
  · have hle : intFinSum (fun _ : Fin B => -(M * M)) ≤ intFinSum (fun i => x i * y i) :=
      intFinSum_le_intFinSum (fun i => (int_mul_bounds_sym (hx i) (hy i)).1)
    rw [intFinSum_const] at hle
    have heq : (B : Int) * -(M * M) = -((B : Int) * (M * M)) := by grind
    rw [heq] at hle; exact hle
  · have hle : intFinSum (fun i => x i * y i) ≤ intFinSum (fun _ : Fin B => M * M) :=
      intFinSum_le_intFinSum (fun i => (int_mul_bounds_sym (hx i) (hy i)).2)
    rw [intFinSum_const] at hle; exact hle

theorem kulisch_asym_bounds {w B : Nat} (x y : Fin B → Int)
    (hx : InAsymRange w x) (hy : InAsymRange w y) :
    kulischAsymMin w B ≤ intDot x y ∧ intDot x y ≤ kulischAsymMax w B := by
  unfold kulischAsymMin kulischAsymMax intDot
  let A : Int := ((2 ^ (w - 1) : Nat) : Int)
  have hA : 1 ≤ A := by
    have h1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  constructor
  · have hle : intFinSum (fun _ : Fin B => -(A * (A - 1))) ≤ intFinSum (fun i => x i * y i) :=
      intFinSum_le_intFinSum (fun i => (int_mul_bounds_asym hA (hx i) (hy i)).1)
    rw [intFinSum_const] at hle
    have heq : (B : Int) * -(A * (A - 1)) = -((B : Int) * (A * (A - 1))) := by grind
    rw [heq] at hle; exact hle
  · have hle : intFinSum (fun i => x i * y i) ≤ intFinSum (fun _ : Fin B => A * A) :=
      intFinSum_le_intFinSum (fun i => (int_mul_bounds_asym hA (hx i) (hy i)).2)
    rw [intFinSum_const] at hle; exact hle

/-- **Theorem 3 (`kulisch_mxint_zero_overflow_swar_exact`)**:
    Universal signed Kulisch dot-product range bounds for symmetric and asymmetric `MXINT_w`,
    plus exact OCP `B = 32` SWAR bit-width laws:
    - Symmetric `MXINT4` (`[-7, 7]`) fits in `int12` (`[-1568, 1568] ⊂ [-2048, 2047]`), not `int11`;
    - Symmetric `MXINT6` (`[-31, 31]`) fits in `int16` (`[-30752, 30752] ⊂ [-32768, 32767]`),
      enabling 2-lane 32-bit SWAR with zero overflow, and does not fit in `int15`;
    - Asymmetric `MXINT6` (`[-32, 31]`) attains exact `32 * (-32) * (-32) = 32768 = 32767 + 1`,
      overflowing `int16` by exact 1 and requiring `int17`. -/
theorem kulisch_mxint_zero_overflow_swar_exact :
    (∀ (w B : Nat) (x y : Fin B → Int), InSymRange w x → InSymRange w y →
      -kulischSymMax w B ≤ intDot x y ∧ intDot x y ≤ kulischSymMax w B) ∧
    (∀ (w B : Nat), ∃ (x y : Fin B → Int),
      InSymRange w x ∧ InSymRange w y ∧ intDot x y = kulischSymMax w B) ∧
    (∀ (w B : Nat), 1 ≤ w → ∀ (x y : Fin B → Int), InAsymRange w x → InAsymRange w y →
      kulischAsymMin w B ≤ intDot x y ∧ intDot x y ≤ kulischAsymMax w B) ∧
    (kulischSymMax 4 32 = 1568 ∧
     (∀ (x y : Fin 32 → Int), InSymRange 4 x → InSymRange 4 y →
       fitsSignedWidth 12 (intDot x y)) ∧
     ¬ fitsSignedWidth 11 (kulischSymMax 4 32)) ∧
    (kulischSymMax 6 32 = 30752 ∧
     (∀ (x y : Fin 32 → Int), InSymRange 6 x → InSymRange 6 y →
       fitsSignedWidth 16 (intDot x y)) ∧
     ¬ fitsSignedWidth 15 (kulischSymMax 6 32) ∧
     32 / 16 = 2) ∧
    (kulischAsymMax 6 32 = 32768 ∧
     (∃ (x y : Fin 32 → Int), InAsymRange 6 x ∧ InAsymRange 6 y ∧
       intDot x y = 32768 ∧ intDot x y = (2 ^ 15 - 1 : Int) + 1 ∧
       ¬ fitsSignedWidth 16 (intDot x y)) ∧
     (∀ (x y : Fin 32 → Int), InAsymRange 6 x → InAsymRange 6 y →
       fitsSignedWidth 17 (intDot x y)) ∧
     32 / 17 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w B x y hx hy; exact kulisch_sym_bounds x y hx hy
  · intro w B
    refine ⟨fun _ => (mxintMax w : Int), fun _ => (mxintMax w : Int), ?_, ?_, ?_⟩
    · intro _; dsimp only; have : (0 : Int) ≤ (mxintMax w : Int) := Int.natCast_nonneg _; omega
    · intro _; dsimp only; have : (0 : Int) ≤ (mxintMax w : Int) := Int.natCast_nonneg _; omega
    · unfold intDot kulischSymMax; exact intFinSum_const _
  · intro w B _ x y hx hy; exact kulisch_asym_bounds x y hx hy
  · refine ⟨by decide, ?_, by unfold fitsSignedWidth kulischSymMax mxintMax; decide⟩
    intro x y hx hy
    have hb := kulisch_sym_bounds x y hx hy
    have hm : kulischSymMax 4 32 = 1568 := by decide
    rw [hm] at hb
    unfold fitsSignedWidth
    omega
  · refine ⟨by decide, ?_, by unfold fitsSignedWidth kulischSymMax mxintMax; decide, by decide⟩
    intro x y hx hy
    have hb := kulisch_sym_bounds x y hx hy
    have hm : kulischSymMax 6 32 = 30752 := by decide
    rw [hm] at hb
    unfold fitsSignedWidth
    omega
  · refine ⟨by decide, ?_, ?_, by decide⟩
    · refine ⟨fun _ => (-32 : Int), fun _ => (-32 : Int), ?_, ?_, ?_, ?_, ?_⟩
      · intro _; dsimp only; decide
      · intro _; dsimp only; decide
      · unfold intDot; rw [intFinSum_const]; decide
      · unfold intDot; rw [intFinSum_const]; decide
      · unfold intDot fitsSignedWidth; rw [intFinSum_const]; decide
    · intro x y hx hy
      have hb := kulisch_asym_bounds (w := 6) x y hx hy
      have hmin : kulischAsymMin 6 32 = -31744 := by decide
      have hmax : kulischAsymMax 6 32 = 32768 := by decide
      rw [hmin, hmax] at hb
      unfold fitsSignedWidth
      omega

/-! ### Theorem 6: Exact Integer Associativity & Permutation Invariance -/

theorem intFinSum_append {B1 B2 : Nat} (f : Fin B1 → Int) (g : Fin B2 → Int) :
    intFinSum (appendVec f g) = intFinSum f + intFinSum g := by
  induction B2 with
  | zero =>
    simp only [intFinSum, Int.add_zero]
    apply intFinSum_congr
    intro i
    unfold appendVec
    simp
  | succ n ih =>
    simp only [intFinSum]
    have hstep : intFinSum (fun i : Fin (B1 + n) => appendVec f g i.castSucc) =
        intFinSum (appendVec f (fun j : Fin n => g j.castSucc)) := by
      apply intFinSum_congr
      intro i
      unfold appendVec
      by_cases h : i.val < B1
      · simp [h]
      · simp [h]
    have hlast : appendVec f g (Fin.last (B1 + n)) = g (Fin.last n) := by
      unfold appendVec
      have hnot : ¬ (B1 + n < B1) := by omega
      simp only [Fin.val_last, hnot, ↓reduceDIte]
      congr 1; apply Fin.ext; simp [Fin.val_last]
    change intFinSum (fun i : Fin (B1 + n) => appendVec f g i.castSucc) +
        appendVec f g (Fin.last (B1 + n)) =
      intFinSum f + (intFinSum (fun i : Fin n => g i.castSucc) + g (Fin.last n))
    rw [hstep, ih (fun j => g j.castSucc), hlast]
    omega

theorem intDot_append {B1 B2 : Nat} (x1 y1 : Fin B1 → Int) (x2 y2 : Fin B2 → Int) :
    intDot (appendVec x1 x2) (appendVec y1 y2) = intDot x1 y1 + intDot x2 y2 := by
  unfold intDot
  have hc : intFinSum (fun i => appendVec x1 x2 i * appendVec y1 y2 i) =
      intFinSum (appendVec (fun i => x1 i * y1 i) (fun j => x2 j * y2 j)) := by
    apply intFinSum_congr
    intro i
    unfold appendVec
    by_cases h : i.val < B1 <;> simp [h]
  rw [hc, intFinSum_append]

private theorem intFinSum_swap_last {n : Nat} (f : Fin (n + 1) → Int) (k : Fin (n + 1)) :
    intFinSum f = f k + intFinSum (fun i : Fin n =>
      f (if i.castSucc = k then Fin.last n else i.castSucc)) := by
  by_cases hk : k = Fin.last n
  · subst hk
    simp only [intFinSum]
    have hc : intFinSum (fun i : Fin n =>
        f (if i.castSucc = Fin.last n then Fin.last n else i.castSucc)) =
        intFinSum (fun i : Fin n => f i.castSucc) := by
      apply intFinSum_congr
      intro i
      have hne : i.castSucc ≠ Fin.last n := by
        intro heq
        have hv : i.val = n := by simpa [Fin.val_castSucc, Fin.val_last] using congrArg Fin.val heq
        omega
      simp [hne]
    rw [hc]; omega
  · simp only [intFinSum]
    have hlt : k.val < n := by
      have hval : k.val ≠ n := by
        intro h0; apply hk; exact Fin.ext (by simpa [Fin.val_last] using h0)
      have := k.isLt; omega
    let k' : Fin n := ⟨k.val, hlt⟩
    have hkeq : k = k'.castSucc := Fin.ext rfl
    have hdiff : intFinSum (fun i : Fin n =>
        f (if i.castSucc = k then Fin.last n else i.castSucc)) -
        intFinSum (fun i : Fin n => f i.castSucc) = f (Fin.last n) - f k := by
      have hsub : intFinSum (fun i : Fin n =>
          f (if i.castSucc = k then Fin.last n else i.castSucc)) =
          intFinSum (fun i : Fin n => f i.castSucc +
            (if i = k' then f (Fin.last n) - f k else 0)) := by
        apply intFinSum_congr
        intro i
        rw [hkeq]
        by_cases h : i = k'
        · subst h; simp; omega
        · have h2 : i.castSucc ≠ k'.castSucc := by
            intro heq; apply h; exact Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val heq)
          simp [h, h2]
      rw [hsub, intFinSum_add, intFinSum_single]
      omega
    omega

theorem intFinSum_bijection {n : Nat} (f : Fin n → Int) (σ : Fin n → Fin n)
    (hBij : IsBijective σ) :
    intFinSum (fun i => f (σ i)) = intFinSum f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hBij with ⟨hInj, hSurj⟩
    rcases hSurj (Fin.last n) with ⟨k, hk⟩
    let g : Fin n → Fin (n + 1) := fun i =>
      if i.castSucc = k then Fin.last n else i.castSucc
    have hg_ne : ∀ i : Fin n, σ (g i) ≠ Fin.last n := by
      intro i heq
      have hgk : g i = k := hInj (g i) k (by rw [heq, hk])
      unfold g at hgk
      by_cases hi : i.castSucc = k
      · simp only [hi, ↓reduceIte] at hgk
        have h1 : n = k.val := by simpa [Fin.val_last] using congrArg Fin.val hgk
        have h2 : i.val = k.val := by simpa [Fin.val_castSucc] using congrArg Fin.val hi
        have := i.isLt
        omega
      · simp only [hi, ↓reduceIte] at hgk
    let τ : Fin n → Fin n := fun i => ⟨(σ (g i)).val, by
      have hlt := (σ (g i)).isLt
      have hne := hg_ne i
      have hval : (σ (g i)).val ≠ n := by
        intro h0; apply hne; exact Fin.ext (by simpa [Fin.val_last] using h0)
      omega⟩
    have hτ_cast : ∀ i : Fin n, (τ i).castSucc = σ (g i) := by
      intro i; exact Fin.ext rfl
    have hτ_bij : IsBijective τ := by
      constructor
      · intro a b hab
        have hcast : σ (g a) = σ (g b) := by
          rw [← hτ_cast a, ← hτ_cast b, hab]
        have hgab : g a = g b := hInj (g a) (g b) hcast
        unfold g at hgab
        by_cases ha : a.castSucc = k <;> by_cases hb : b.castSucc = k
        · apply Fin.ext
          have h1 : a.val = k.val := by simpa [Fin.val_castSucc] using congrArg Fin.val ha
          have h2 : b.val = k.val := by simpa [Fin.val_castSucc] using congrArg Fin.val hb
          omega
        · simp only [ha, hb, ↓reduceIte] at hgab
          have hv : n = b.val := by simpa [Fin.val_last, Fin.val_castSucc] using congrArg Fin.val hgab
          have := b.isLt; omega
        · simp only [ha, hb, ↓reduceIte] at hgab
          have hv : a.val = n := by simpa [Fin.val_last, Fin.val_castSucc] using congrArg Fin.val hgab
          have := a.isLt; omega
        · simp only [ha, hb, ↓reduceIte] at hgab
          exact Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val hgab)
      · intro b
        rcases hSurj b.castSucc with ⟨a, ha⟩
        have hne_k : a ≠ k := by
          intro heq; subst heq
          rw [hk] at ha
          have hv : n = b.val := by simpa [Fin.val_last, Fin.val_castSucc] using congrArg Fin.val ha
          have := b.isLt; omega
        by_cases ha_last : a = Fin.last n
        · have hk_lt : k.val < n := by
            have hne_last : k ≠ Fin.last n := by
              intro hkl; exact hne_k (by rw [ha_last, hkl])
            have hval : k.val ≠ n := by
              intro h0; apply hne_last; exact Fin.ext (by simpa [Fin.val_last] using h0)
            have := k.isLt; omega
          refine ⟨⟨k.val, hk_lt⟩, ?_⟩
          apply Fin.ext
          change (σ (g ⟨k.val, hk_lt⟩)).val = b.val
          have hg_eq : g ⟨k.val, hk_lt⟩ = Fin.last n := by
            unfold g
            have heq : (⟨k.val, hk_lt⟩ : Fin n).castSucc = k := Fin.ext rfl
            simp [heq]
          rw [hg_eq, ← ha_last, ha]; rfl
        · have ha_lt : a.val < n := by
            have hval : a.val ≠ n := by
              intro h0; apply ha_last; exact Fin.ext (by simpa [Fin.val_last] using h0)
            have := a.isLt; omega
          refine ⟨⟨a.val, ha_lt⟩, ?_⟩
          apply Fin.ext
          change (σ (g ⟨a.val, ha_lt⟩)).val = b.val
          have hg_eq : g ⟨a.val, ha_lt⟩ = a := by
            unfold g
            have hne : (⟨a.val, ha_lt⟩ : Fin n).castSucc ≠ k := by
              intro heq; apply hne_k
              exact Fin.ext (by simpa [Fin.val_castSucc] using congrArg Fin.val heq)
            simp only [hne, ↓reduceIte]
            exact Fin.ext rfl
          rw [hg_eq, ha]; rfl
    rw [intFinSum_swap_last (fun i => f (σ i)) k, hk]
    simp only [intFinSum]
    have hrec := ih (fun i => f i.castSucc) τ hτ_bij
    have hc : intFinSum (fun i : Fin n => f (σ (g i))) = intFinSum (fun i : Fin n => f (τ i).castSucc) := by
      apply intFinSum_congr; intro i; rw [hτ_cast i]
    change f (Fin.last n) + intFinSum (fun i : Fin n => f (σ (g i))) =
      intFinSum (fun i : Fin n => f i.castSucc) + f (Fin.last n)
    rw [hc, hrec]
    omega

/-- **Theorem 6 (`mxint_exact_integer_associativity`)**:
    Exact signed Kulisch accumulation of `B`-element `MXINT_w` dot products in `Int` is
    unconditionally associative, block-split additive, and invariant under arbitrary permutations. -/
theorem mxint_exact_integer_associativity :
    (∀ a b c : Int, (a + b) + c = a + (b + c)) ∧
    (∀ (B1 B2 : Nat) (x1 y1 : Fin B1 → Int) (x2 y2 : Fin B2 → Int),
      intDot (appendVec x1 x2) (appendVec y1 y2) = intDot x1 y1 + intDot x2 y2) ∧
    (∀ (B : Nat) (x y : Fin B → Int) (σ : Fin B → Fin B),
      IsBijective σ →
      intDot (fun i => x (σ i)) (fun i => y (σ i)) = intDot x y) := by
  refine ⟨Int.add_assoc, fun _ _ x1 y1 x2 y2 => intDot_append x1 y1 x2 y2, ?_⟩
  intro B x y σ hBij
  exact intFinSum_bijection (fun i => x i * y i) σ hBij

end MxintMxfpSwar
