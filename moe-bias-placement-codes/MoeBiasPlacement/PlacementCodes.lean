/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MoeBiasPlacement.RatHelpers

/-!
# Frontier 2 Proofs: Dispersion Duality, Affine-Plane `AG(2, q)` Codes & EPLB Pigeonhole Bound

Proves:
- Theorem 3: `fanout_intra_gpu_dispersion_duality`
- Theorem 4: `affine_plane_ag2_zero_hotspot_placement`
- Theorem 5: `eplb_redundant_expert_pigeonhole_bound`
-/

namespace MoeBiasPlacement

/-! ## Theorem 3: Exact Fanout vs Intra-GPU Dispersion Duality -/

private theorem discrete_convex_support_line (n q : Nat) :
    2 * q * n ≤ n * (n - 1) + q * (q + 1) := by
  have h : (0 : Int) ≤ ((n : Int) - (q : Int)) * ((n : Int) - (q : Int) - 1) := by
    by_cases h1 : q ≤ n
    · by_cases h2 : q = n
      · subst h2; simp
      · have hpos1 : (0 : Int) ≤ (n : Int) - (q : Int) := by omega
        have hpos2 : (0 : Int) ≤ (n : Int) - (q : Int) - 1 := by omega
        exact Int.mul_nonneg hpos1 hpos2
    · have hneg1 : (n : Int) - (q : Int) ≤ 0 := by omega
      have hneg2 : (n : Int) - (q : Int) - 1 ≤ 0 := by omega
      exact Int.mul_nonneg_of_nonpos_of_nonpos hneg1 hneg2
  have hexp :
      ((n : Int) - (q : Int)) * ((n : Int) - (q : Int) - 1) =
      (n : Int) * ((n : Int) - 1) + (q : Int) * ((q : Int) + 1) - 2 * (q : Int) * (n : Int) := by
    have : ∀ a b : Int, (a - b) * (a - b - 1) = a * (a - 1) + b * (b + 1) - 2 * b * a := by
      intro a b
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_add, Int.mul_one,
          Int.mul_sub, Int.mul_one, Int.mul_sub, Int.mul_one]
      have hab : b * a = a * b := Int.mul_comm b a
      have h2ba : 2 * b * a = b * a + b * a := by
        have h2 : (2 : Int) = 1 + 1 := by decide
        rw [h2, Int.add_mul, Int.one_mul, Int.add_mul]
      rw [h2ba, hab]
      omega
    exact this (n : Int) (q : Int)
  rw [hexp] at h
  cases n with
  | zero =>
    simp at h ⊢
  | succ k =>
    have hnat : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
    have hcast : ((k + 1) * k : Nat) = (k + 1) * ((k + 1) - 1) := by simp
    have h1 : (2 * (q : Int) * ((k + 1 : Nat) : Int)) ≤
        ((k + 1 : Nat) : Int) * (k : Int) + (q : Int) * ((q : Int) + 1) := by
      rw [← hnat]; omega
    exact_mod_cast h1

theorem fanout_intra_gpu_dispersion_duality
    (f K : Nat) (hf : 0 < f) (hfK : f ≤ K) :
    let q := K / f
    let r := K % f
    (∀ c : Fin f → Nat, sumFinNat c = K → q * (K + r - f) ≤ twiceIntraPairs c) ∧
    (∃ c : Fin f → Nat, sumFinNat c = K ∧ (∀ g : Fin f, 0 < c g) ∧
      twiceIntraPairs c = q * (K + r - f)) := by
  intro q r
  have hdiv : K = q * f + r := by
    have := Nat.div_add_mod K f
    rw [Nat.mul_comm] at this
    exact this.symm
  have hrlt : r < f := Nat.mod_lt K hf
  have hqpos : 1 ≤ q := by
    have : f * 1 ≤ K := by omega
    exact Nat.le_div_iff_mul_le hf |>.mpr (by omega)
  constructor
  · intro c hsum
    have hpoint : ∀ g : Fin f, 2 * q * c g ≤ c g * (c g - 1) + q * (q + 1) := fun g =>
      discrete_convex_support_line (c g) q
    have hsum_ineq : sumFinNat (fun g => 2 * q * c g) ≤
        sumFinNat (fun g => c g * (c g - 1) + q * (q + 1)) := sumFinNat_le hpoint
    have hlhs : sumFinNat (fun g => 2 * q * c g) = 2 * q * K := by
      have hmul : ∀ {n : Nat} (a : Nat) (h : Fin n → Nat),
          sumFinNat (fun i => a * h i) = a * sumFinNat h := by
        intro n a h
        induction n with
        | zero => simp [sumFinNat]
        | succ n ih => simp only [sumFinNat, ih, Nat.mul_add]
      rw [hmul, hsum]
    have hrhs : sumFinNat (fun g => c g * (c g - 1) + q * (q + 1)) =
        twiceIntraPairs c + f * (q * (q + 1)) := by
      rw [sumFinNat_add, sumFinNat_const]
      rfl
    rw [hlhs, hrhs] at hsum_ineq
    -- Now: 2 * q * K ≤ twiceIntraPairs c + f * (q * (q + 1))
    -- Need: q * (K + r - f) ≤ twiceIntraPairs c
    -- Note: q * (K + r - f) + f * (q * (q + 1)) = q * (K + r - f + f * q + f) = q * (2 * K) = 2 * q * K!
    have hident : q * (K + r - f) + f * (q * (q + 1)) = 2 * q * K := by
      have h1 : f * (q * (q + 1)) = q * (q * f + f) := by
        have : f * (q * (q + 1)) = (f * q) * (q + 1) := by rw [Nat.mul_assoc]
        rw [this, Nat.mul_comm f q, Nat.mul_add, Nat.mul_one, Nat.mul_assoc,
            Nat.mul_comm f q, ← Nat.mul_add]
      rw [h1, ← Nat.mul_add]
      have h2 : K + r - f + (q * f + f) = 2 * K := by omega
      rw [h2, Nat.mul_comm 2 q, Nat.mul_assoc]
    omega
  · -- Attainment witness: r GPUs with q + 1, f - r GPUs with q
    refine ⟨fun g => if g.val < r then q + 1 else q, ?_, ?_, ?_⟩
    · rw [sumFinNat_ite_lt f r (q + 1) q (Nat.le_of_lt hrlt)]
      rw [Nat.mul_add, Nat.mul_one]
      have h1 : r * q + (f - r) * q = f * q := by
        rw [← Nat.add_mul]
        have : r + (f - r) = f := by omega
        rw [this]
      rw [Nat.mul_comm f q] at h1
      omega
    · intro g
      dsimp only
      split <;> omega
    · unfold twiceIntraPairs
      have hfun : (fun g : Fin f => (if g.val < r then q + 1 else q) * ((if g.val < r then q + 1 else q) - 1)) =
          (fun g : Fin f => if g.val < r then (q + 1) * q else q * (q - 1)) := by
        funext g
        by_cases h : g.val < r <;> simp [h]
      rw [hfun, sumFinNat_ite_lt f r ((q + 1) * q) (q * (q - 1)) (Nat.le_of_lt hrlt)]
      have h1 : r * ((q + 1) * q) + (f - r) * (q * (q - 1)) =
          q * (r * (q + 1) + (f - r) * (q - 1)) := by
        rw [Nat.mul_add]
        have ha : r * ((q + 1) * q) = q * (r * (q + 1)) := by
          rw [Nat.mul_comm (q + 1) q, ← Nat.mul_assoc, Nat.mul_comm r q, Nat.mul_assoc]
        have hb : (f - r) * (q * (q - 1)) = q * ((f - r) * (q - 1)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (f - r) q, Nat.mul_assoc]
        rw [ha, hb]
      rw [h1]
      congr 1
      have h2 : r * (q + 1) = r * q + r := by rw [Nat.mul_add, Nat.mul_one]
      have h3 : (f - r) * (q - 1) + (f - r) = (f - r) * q := by
        have : (f - r) * (q - 1) + (f - r) * 1 = (f - r) * ((q - 1) + 1) := by rw [← Nat.mul_add]
        rw [Nat.mul_one] at this
        have hq : (q - 1) + 1 = q := by omega
        rw [hq] at this
        exact this
      have h4 : r * q + (f - r) * q = q * f := by
        rw [← Nat.add_mul]
        have : r + (f - r) = f := by omega
        rw [this, Nat.mul_comm]
      omega

/-! ## Theorem 4: Resolvable Affine Plane `AG(2, 4)` and `AG(2, 8)` Zero-Hotspot BIBD Placement -/

private theorem gf4_add_comm (a b : Fin 4) : gf4Add a b = gf4Add b a := by decide +revert
private theorem gf4_add_assoc (a b c : Fin 4) : gf4Add (gf4Add a b) c = gf4Add a (gf4Add b c) := by decide +revert
private theorem gf4_add_self (a : Fin 4) : gf4Add a a = 0 := by decide +revert
private theorem gf4_add_zero (a : Fin 4) : gf4Add a 0 = a := by decide +revert
private theorem gf4_mul_comm (a b : Fin 4) : gf4Mul a b = gf4Mul b a := by decide +revert
private theorem gf4_mul_assoc (a b c : Fin 4) : gf4Mul (gf4Mul a b) c = gf4Mul a (gf4Mul b c) := by decide +revert
private theorem gf4_mul_one (a : Fin 4) : gf4Mul a 1 = a := by decide +revert
private theorem gf4_mul_add (a b c : Fin 4) : gf4Mul a (gf4Add b c) = gf4Add (gf4Mul a b) (gf4Mul a c) := by decide +revert
private theorem gf4_inv_exists (a : Fin 4) (ha : a ≠ 0) : ∃ b : Fin 4, gf4Mul a b = 1 := by
  decide +revert

private theorem gf8_add_comm (a b : Fin 8) : gf8Add a b = gf8Add b a := by decide +revert
private theorem gf8_add_assoc (a b c : Fin 8) : gf8Add (gf8Add a b) c = gf8Add a (gf8Add b c) := by decide +revert
private theorem gf8_add_self (a : Fin 8) : gf8Add a a = 0 := by decide +revert
private theorem gf8_add_zero (a : Fin 8) : gf8Add a 0 = a := by decide +revert
private theorem gf8_mul_comm (a b : Fin 8) : gf8Mul a b = gf8Mul b a := by decide +revert
private theorem gf8_mul_assoc (a b c : Fin 8) : gf8Mul (gf8Mul a b) c = gf8Mul a (gf8Mul b c) := by decide +revert
private theorem gf8_mul_one (a : Fin 8) : gf8Mul a 1 = a := by decide +revert
private theorem gf8_mul_add (a b c : Fin 8) : gf8Mul a (gf8Add b c) = gf8Add (gf8Mul a b) (gf8Mul a c) := by decide +revert
private theorem gf8_inv_exists (a : Fin 8) (ha : a ≠ 0) : ∃ b : Fin 8, gf8Mul a b = 1 := by
  decide +revert

private theorem gf4_add_eq_zero_iff (a b : Fin 4) : gf4Add a b = 0 ↔ a = b := by
  decide +revert

private theorem gf8_add_eq_zero_iff (a b : Fin 8) : gf8Add a b = 0 ↔ a = b := by
  decide +revert

theorem affine_plane_ag2_zero_hotspot_placement :
    (∀ c y : Fin 4, ag24Gpu (ag24VerticalLine c y) = c) ∧
    (∀ m b : Fin 4,
      (∀ x1 x2 : Fin 4, ag24Gpu (ag24TransverseLine m b x1) = ag24Gpu (ag24TransverseLine m b x2) → x1 = x2) ∧
      (∀ g : Fin 4, ∃ x : Fin 4, ag24Gpu (ag24TransverseLine m b x) = g)) ∧
    (∀ p1 p2 : Fin 4 × Fin 4, p1 ≠ p2 →
      (p1.1 = p2.1 → ∃ c : Fin 4, p1.1 = c ∧ p2.1 = c ∧ ∀ c' : Fin 4, p1.1 = c' ∧ p2.1 = c' → c' = c) ∧
      (p1.1 ≠ p2.1 → ∃ m b : Fin 4,
        ag24TransverseLine m b p1.1 = p1 ∧ ag24TransverseLine m b p2.1 = p2 ∧
        ∀ m' b' : Fin 4,
          ag24TransverseLine m' b' p1.1 = p1 → ag24TransverseLine m' b' p2.1 = p2 →
          m' = m ∧ b' = b)) ∧
    (∀ c y : Fin 8, ag28Gpu (ag28VerticalLine c y) = c) ∧
    (∀ m b : Fin 8,
      (∀ x1 x2 : Fin 8, ag28Gpu (ag28TransverseLine m b x1) = ag28Gpu (ag28TransverseLine m b x2) → x1 = x2) ∧
      (∀ g : Fin 8, ∃ x : Fin 8, ag28Gpu (ag28TransverseLine m b x) = g)) ∧
    (∀ p1 p2 : Fin 8 × Fin 8, p1 ≠ p2 →
      (p1.1 = p2.1 → ∃ c : Fin 8, p1.1 = c ∧ p2.1 = c ∧ ∀ c' : Fin 8, p1.1 = c' ∧ p2.1 = c' → c' = c) ∧
      (p1.1 ≠ p2.1 → ∃ m b : Fin 8,
        ag28TransverseLine m b p1.1 = p1 ∧ ag28TransverseLine m b p2.1 = p2 ∧
        ∀ m' b' : Fin 8,
          ag28TransverseLine m' b' p1.1 = p1 → ag28TransverseLine m' b' p2.1 = p2 →
          m' = m ∧ b' = b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c y; rfl
  · intro m b
    exact ⟨fun _ _ h => h, fun g => ⟨g, rfl⟩⟩
  · intro ⟨x1, y1⟩ ⟨x2, y2⟩ _
    constructor
    · intro hx; exact ⟨x1, rfl, hx.symm, fun c' hc' => hc'.1.symm⟩
    · intro hne
      have hdx : gf4Add x1 x2 ≠ 0 := fun h => hne ((gf4_add_eq_zero_iff x1 x2).mp h)
      rcases gf4_inv_exists (gf4Add x1 x2) hdx with ⟨inv, hinv⟩
      let m := gf4Mul (gf4Add y1 y2) inv
      let b := gf4Add y1 (gf4Mul m x1)
      have hp1 : gf4Add (gf4Mul m x1) b = y1 := by
        show gf4Add (gf4Mul m x1) (gf4Add y1 (gf4Mul m x1)) = y1
        rw [gf4_add_comm y1, ← gf4_add_assoc, gf4_add_self, gf4_add_comm, gf4_add_zero]
      have hp2 : gf4Add (gf4Mul m x2) b = y2 := by
        show gf4Add (gf4Mul m x2) (gf4Add y1 (gf4Mul m x1)) = y2
        rw [gf4_add_comm y1, ← gf4_add_assoc, gf4_add_comm (gf4Mul m x2), ← gf4_mul_add]
        have hmx : gf4Mul m (gf4Add x1 x2) = gf4Add y1 y2 := by
          show gf4Mul (gf4Mul (gf4Add y1 y2) inv) (gf4Add x1 x2) = gf4Add y1 y2
          rw [gf4_mul_assoc, gf4_mul_comm inv, hinv, gf4_mul_one]
        rw [hmx, gf4_add_comm (gf4Add y1 y2) y1, ← gf4_add_assoc, gf4_add_self,
            gf4_add_comm 0 y2, gf4_add_zero]
      refine ⟨m, b, ?_, ?_, ?_⟩
      · simp [ag24TransverseLine, hp1]
      · simp [ag24TransverseLine, hp2]
      · intro m' b' h1 h2
        have hy1 : gf4Add (gf4Mul m' x1) b' = y1 := congrArg Prod.snd h1
        have hy2 : gf4Add (gf4Mul m' x2) b' = y2 := congrArg Prod.snd h2
        have hdiff : gf4Mul m' (gf4Add x1 x2) = gf4Add y1 y2 := by
          rw [gf4_mul_add, ← hy1, ← hy2]
          rw [gf4_add_assoc, ← gf4_add_assoc b', gf4_add_comm b' (gf4Mul m' x2),
              gf4_add_assoc (gf4Mul m' x2), gf4_add_self, gf4_add_zero]
        have hm : m' = m := by
          calc m' = gf4Mul m' 1 := (gf4_mul_one m').symm
            _ = gf4Mul m' (gf4Mul (gf4Add x1 x2) inv) := by rw [hinv]
            _ = gf4Mul (gf4Mul m' (gf4Add x1 x2)) inv := (gf4_mul_assoc _ _ _).symm
            _ = m := by rw [hdiff]
        have hb : b' = b := by
          rw [hm] at hy1
          calc b' = gf4Add 0 b' := by rw [gf4_add_comm, gf4_add_zero]
            _ = gf4Add (gf4Add (gf4Mul m x1) (gf4Mul m x1)) b' := by rw [gf4_add_self]
            _ = gf4Add (gf4Mul m x1) (gf4Add (gf4Mul m x1) b') := gf4_add_assoc _ _ _
            _ = gf4Add (gf4Mul m x1) y1 := by rw [hy1]
            _ = b := gf4_add_comm _ _
        exact ⟨hm, hb⟩
  · intro c y; rfl
  · intro m b
    exact ⟨fun _ _ h => h, fun g => ⟨g, rfl⟩⟩
  · intro ⟨x1, y1⟩ ⟨x2, y2⟩ _
    constructor
    · intro hx; exact ⟨x1, rfl, hx.symm, fun c' hc' => hc'.1.symm⟩
    · intro hne
      have hdx : gf8Add x1 x2 ≠ 0 := fun h => hne ((gf8_add_eq_zero_iff x1 x2).mp h)
      rcases gf8_inv_exists (gf8Add x1 x2) hdx with ⟨inv, hinv⟩
      let m := gf8Mul (gf8Add y1 y2) inv
      let b := gf8Add y1 (gf8Mul m x1)
      have hp1 : gf8Add (gf8Mul m x1) b = y1 := by
        show gf8Add (gf8Mul m x1) (gf8Add y1 (gf8Mul m x1)) = y1
        rw [gf8_add_comm y1, ← gf8_add_assoc, gf8_add_self, gf8_add_comm, gf8_add_zero]
      have hp2 : gf8Add (gf8Mul m x2) b = y2 := by
        show gf8Add (gf8Mul m x2) (gf8Add y1 (gf8Mul m x1)) = y2
        rw [gf8_add_comm y1, ← gf8_add_assoc, gf8_add_comm (gf8Mul m x2), ← gf8_mul_add]
        have hmx : gf8Mul m (gf8Add x1 x2) = gf8Add y1 y2 := by
          show gf8Mul (gf8Mul (gf8Add y1 y2) inv) (gf8Add x1 x2) = gf8Add y1 y2
          rw [gf8_mul_assoc, gf8_mul_comm inv, hinv, gf8_mul_one]
        rw [hmx, gf8_add_comm (gf8Add y1 y2) y1, ← gf8_add_assoc, gf8_add_self,
            gf8_add_comm 0 y2, gf8_add_zero]
      refine ⟨m, b, ?_, ?_, ?_⟩
      · simp [ag28TransverseLine, hp1]
      · simp [ag28TransverseLine, hp2]
      · intro m' b' h1 h2
        have hy1 : gf8Add (gf8Mul m' x1) b' = y1 := congrArg Prod.snd h1
        have hy2 : gf8Add (gf8Mul m' x2) b' = y2 := congrArg Prod.snd h2
        have hdiff : gf8Mul m' (gf8Add x1 x2) = gf8Add y1 y2 := by
          rw [gf8_mul_add, ← hy1, ← hy2]
          rw [gf8_add_assoc, ← gf8_add_assoc b', gf8_add_comm b' (gf8Mul m' x2),
              gf8_add_assoc (gf8Mul m' x2), gf8_add_self, gf8_add_zero]
        have hm : m' = m := by
          calc m' = gf8Mul m' 1 := (gf8_mul_one m').symm
            _ = gf8Mul m' (gf8Mul (gf8Add x1 x2) inv) := by rw [hinv]
            _ = gf8Mul (gf8Mul m' (gf8Add x1 x2)) inv := (gf8_mul_assoc _ _ _).symm
            _ = m := by rw [hdiff]
        have hb : b' = b := by
          rw [hm] at hy1
          calc b' = gf8Add 0 b' := by rw [gf8_add_comm, gf8_add_zero]
            _ = gf8Add (gf8Add (gf8Mul m x1) (gf8Mul m x1)) b' := by rw [gf8_add_self]
            _ = gf8Add (gf8Mul m x1) (gf8Add (gf8Mul m x1) b') := gf8_add_assoc _ _ _
            _ = gf8Add (gf8Mul m x1) y1 := by rw [hy1]
            _ = b := gf8_add_comm _ _
        exact ⟨hm, hb⟩

/-! ## Theorem 5: Exact EPLB Redundant-Expert Pigeonhole Capacity Bound -/

private theorem exists_true_of_countBool_pos {n : Nat} (S : Fin n → Bool) (h : 1 ≤ countBool S) :
    ∃ i : Fin n, S i = true := by
  induction n with
  | zero => simp [countBool, sumFinNat] at h
  | succ n ih =>
    unfold countBool at h
    simp only [sumFinNat] at h
    by_cases hlast : S (Fin.last n) = true
    · exact ⟨Fin.last n, hlast⟩
    · have hf : S (Fin.last n) = false := by cases h' : S (Fin.last n) <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      rcases ih (fun i => S i.castSucc) h with ⟨j, hj⟩
      exact ⟨j.castSucc, hj⟩

private theorem exists_max_on_subset {n : Nat} (S : Fin n → Bool) (f : Fin n → Rat)
    (h : 1 ≤ countBool S) :
    ∃ i : Fin n, S i = true ∧ ∀ j : Fin n, S j = true → f j ≤ f i := by
  induction n with
  | zero => simp [countBool, sumFinNat] at h
  | succ n ih =>
    unfold countBool at h
    simp only [sumFinNat] at h
    by_cases hlast : S (Fin.last n) = true
    · by_cases hprev : 1 ≤ countBool (fun i : Fin n => S i.castSucc)
      · rcases ih (fun i => S i.castSucc) (fun i => f i.castSucc) hprev with ⟨k, hkS, hkmax⟩
        rcases rat_le_total (f k.castSucc) (f (Fin.last n)) with hle | hge
        · refine ⟨Fin.last n, hlast, fun j hj => ?_⟩
          refine Fin.lastCases (motive := fun x => S x = true → f x ≤ f (Fin.last n)) ?_ ?_ j hj
          · intro _; exact rat_le_refl _
          · intro j' hj'; exact Rat.le_trans (hkmax j' hj') hle
        · refine ⟨k.castSucc, hkS, fun j hj => ?_⟩
          refine Fin.lastCases (motive := fun x => S x = true → f x ≤ f k.castSucc) ?_ ?_ j hj
          · intro _; exact hge
          · intro j' hj'; exact hkmax j' hj'
      · -- Only Fin.last n is in S
        have hzero : countBool (fun i : Fin n => S i.castSucc) = 0 := by omega
        have hall_false : ∀ j : Fin n, S j.castSucc = false := by
          intro j
          by_cases hj : S j.castSucc = true
          · exfalso
            have hge1 : 1 ≤ countBool (fun i : Fin n => S i.castSucc) := by
              have haux : ∀ {m : Nat} (P : Fin m → Bool) (x : Fin m), P x = true → 1 ≤ countBool P := by
                intro m P x hx
                induction m with
                | zero => exact Fin.elim0 x
                | succ m ihm =>
                  unfold countBool; simp only [sumFinNat]
                  refine Fin.lastCases (motive := fun y => P y = true → _) ?_ ?_ x hx
                  · intro hxl; simp [hxl]
                  · intro y hy
                    have h1 : 1 ≤ sumFinNat (fun i : Fin m => if P i.castSucc = true then 1 else 0) :=
                      ihm (fun i => P i.castSucc) y hy
                    omega
              exact haux (fun i => S i.castSucc) j hj
            omega
          · cases h' : S j.castSucc <;> simp_all
        refine ⟨Fin.last n, hlast, fun j hj => ?_⟩
        refine Fin.lastCases (motive := fun x => S x = true → f x ≤ f (Fin.last n)) ?_ ?_ j hj
        · intro _; exact rat_le_refl _
        · intro j' hj'; rw [hall_false j'] at hj'; exact absurd hj' (by decide)
    · have hf : S (Fin.last n) = false := by cases h' : S (Fin.last n) <;> simp_all
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
      rcases ih (fun i => S i.castSucc) (fun i => f i.castSucc) h with ⟨k, hkS, hkmax⟩
      refine ⟨k.castSucc, hkS, fun j hj => ?_⟩
      refine Fin.lastCases (motive := fun x => S x = true → f x ≤ f k.castSucc) ?_ ?_ j hj
      · intro hjl; rw [hf] at hjl; exact absurd hjl (by decide)
      · intro j' hj'; exact hkmax j' hj'

theorem eplb_redundant_expert_pigeonhole_bound
    (E R : Nat) (hE : 0 < E)
    (w : Fin E → Rat) (hw : ∀ i : Fin E, 0 ≤ w i)
    (rep : Fin E → Nat) (hrep_pos : ∀ i : Fin E, 1 ≤ rep i) (hrep_sum : sumFinNat rep = E + R)
    (S : Fin E → Bool) (hS : 1 ≤ countBool S) :
    let h := countBool S
    (∀ Lmax : Rat, (∀ i : Fin E, w i / (rep i : Rat) ≤ Lmax) →
      sumFinRatSubset S w ≤ Lmax * ((h + R : Nat) : Rat)) ∧
    (∃ i : Fin E, S i = true ∧
      sumFinRatSubset S w / ((h + R : Nat) : Rat) ≤ w i / (rep i : Rat)) := by
  have _ := hE
  intro h
  -- Step 1: Pigeonhole bound on replicas inside S: sumFinNatSubset S rep ≤ h + R
  have hsplit := sumFinNat_split_bool S rep
  have hnot_ge : countBool (fun i => !S i) ≤ sumFinNatSubset (fun i => !S i) rep := by
    unfold countBool sumFinNatSubset
    apply sumFinNat_le
    intro i
    by_cases hi : (!S i) = true
    · simp only [hi]; exact hrep_pos i
    · simp only [hi]; exact Nat.le_refl 0
  have hcnt := countBool_add_not S
  have hrep_S_le : sumFinNatSubset S rep ≤ h + R := by omega
  -- Step 2: Helper showing any Lmax dominating w i / rep i on S satisfies the bound
  have hbound_on_S : ∀ Lmax : Rat, 0 ≤ Lmax →
      (∀ i : Fin E, S i = true → w i / (rep i : Rat) ≤ Lmax) →
      sumFinRatSubset S w ≤ Lmax * ((h + R : Nat) : Rat) := by
    intro Lmax hLnonneg hdom
    have hpoint : ∀ i : Fin E,
        (if S i = true then w i else 0) ≤
        Lmax * ((if S i = true then rep i else 0 : Nat) : Rat) := by
      intro i
      by_cases hi : S i = true
      · simp only [hi, ↓reduceIte]
        have hrpos : (0 : Rat) < (rep i : Rat) := rat_natCast_pos (hrep_pos i)
        exact (rat_div_le_iff hrpos).mp (hdom i hi)
      · simp [hi]
    have hsum_le : sumFinRatSubset S w ≤
        sumFinRat (fun i => Lmax * ((if S i = true then rep i else 0 : Nat) : Rat)) :=
      sumFinRat_le hpoint
    rw [sumFinRat_mul_left, sumFinRat_natCast] at hsum_le
    exact Rat.le_trans hsum_le
      (rat_mul_le_mul_of_nonneg_left (rat_natCast_le hrep_S_le) hLnonneg)
  constructor
  · intro Lmax hLmax
    rcases exists_true_of_countBool_pos S hS with ⟨i0, _⟩
    have hLnonneg : 0 ≤ Lmax := by
      have h0 : 0 ≤ w i0 / (rep i0 : Rat) := by
        rw [Rat.div_def]
        exact rat_mul_nonneg (hw i0) (Rat.le_of_lt (rat_inv_pos (rat_natCast_pos (hrep_pos i0))))
      exact Rat.le_trans h0 (hLmax i0)
    exact hbound_on_S Lmax hLnonneg (fun i _ => hLmax i)
  · rcases exists_max_on_subset S (fun i => w i / (rep i : Rat)) hS with ⟨imax, himaxS, himax⟩
    refine ⟨imax, himaxS, ?_⟩
    have hLnonneg : 0 ≤ w imax / (rep imax : Rat) := by
      rw [Rat.div_def]
      exact rat_mul_nonneg (hw imax) (Rat.le_of_lt (rat_inv_pos (rat_natCast_pos (hrep_pos imax))))
    have hle := hbound_on_S (w imax / (rep imax : Rat)) hLnonneg himax
    have hhRpos : (0 : Rat) < ((h + R : Nat) : Rat) := rat_natCast_pos (by omega)
    exact (rat_div_le_iff hhRpos).mpr hle

end MoeBiasPlacement
