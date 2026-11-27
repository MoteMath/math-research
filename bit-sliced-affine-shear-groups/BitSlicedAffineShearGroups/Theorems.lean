/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSlicedAffineShearGroups.Defs

/-!
# Theorems (`BitSlicedAffineShearGroups`)

# Bit-Sliced Affine Shear-Group & Commutator Engine (`BSAS-CE`)

Pure-silicon standalone Lean 4.36.0 formalization of a reusable finite-to-infinite
group-theoretic and commutator proof engine for reversible bit-shear circuits
(XOR-shears, add-shears, masked/shifted shears, cross-lane bit-swap layers, and
block-causal intra-lane bit-swap layers) on `(BitVec w) × (BitVec w)`.

Zero external dependencies (no Mathlib), zero `sorry`, zero custom axioms, zero
`native_decide` / `Lean.ofReduceBool`.
-/


namespace BSASCE
theorem vecXor_comm (u v : Vec2) : vecXor u v = vecXor v u := by
  cases u; cases v; simp [vecXor, Bool.xor_comm]

theorem vecXor_assoc (u v w : Vec2) : vecXor (vecXor u v) w = vecXor u (vecXor v w) := by
  cases u; cases v; cases w; simp [vecXor]

theorem vecXor_zero_left (u : Vec2) : vecXor (false, false) u = u := by
  cases u; simp [vecXor]

theorem vecXor_zero_right (u : Vec2) : vecXor u (false, false) = u := by
  cases u; simp [vecXor]

theorem vecXor_cancel_right (u v w : Vec2) (h : vecXor u w = vecXor v w) : u = v := by
  cases u with | mk u1 u2 =>
  cases v with | mk v1 v2 =>
  cases w with | mk w1 w2 =>
  cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;> cases w1 <;> cases w2 <;> simp_all [vecXor]

namespace GL2
def ord : GL2 → Nat
  | I  => 1
  | L  => 2
  | U  => 2
  | J  => 2
  | R1 => 3
  | R2 => 3

theorem act_xor (M : GL2) (u v : Vec2) : M.act (vecXor u v) = vecXor (M.act u) (M.act v) := by
  cases M <;> cases u with | mk u1 u2 => cases v with | mk v1 v2 =>
  cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;> rfl

theorem act_inv_right (M : GL2) (v : Vec2) : M.act (M.inv.act v) = v := by
  cases M <;> cases v with | mk a b => cases a <;> cases b <;> rfl

theorem act_ext {M N : GL2} (h : ∀ v, M.act v = N.act v) : M = N := by
  have h1 := h (true, false)
  have h2 := h (false, true)
  cases M <;> cases N <;> simp_all [act]

theorem mul_I (M : GL2) : mul M I = M := by cases M <;> rfl
theorem I_mul (M : GL2) : mul I M = M := by cases M <;> rfl

theorem mul_inv (M : GL2) : mul M (inv M) = I := by cases M <;> rfl
theorem inv_mul (M : GL2) : mul (inv M) M = I := by cases M <;> rfl

theorem pow_add (M : GL2) (a b : Nat) : pow M (a + b) = mul (pow M a) (pow M b) := by
  induction a with
  | zero => simp [pow, I_mul]
  | succ a ih =>
    rw [Nat.succ_add, pow, ih, pow, mul_assoc]

theorem pow_six (M : GL2) : pow M 6 = I := by
  cases M <;> rfl

theorem pow_two_or_three (M : GL2) : pow M 2 = I ∨ pow M 3 = I := by
  cases M <;> decide

theorem comm_pow_three (M N : GL2) : pow (comm M N) 3 = I := by
  cases M <;> cases N <;> rfl

theorem double_comm_eq_I (A B C D : GL2) : comm (comm A B) (comm C D) = I := by
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

theorem ord_conj (H M : GL2) : (conj H M).ord = M.ord := by
  cases H <;> cases M <;> rfl

theorem comm_eq_I_of_eq (M : GL2) : comm M M = I := by
  cases M <;> rfl

theorem pow_I (n : Nat) : pow I n = I := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pow, ih, I_mul]

end GL2
theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := rfl

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f a (iter f b x) := by
  induction a with
  | zero => simp [iter]
  | succ a ih =>
    rw [Nat.succ_add, iter, ih, iter]

theorem iter_mul {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a * b) x = iter (iter f a) b x := by
  induction b with
  | zero => simp [iter]
  | succ b ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, ih, iter]

theorem iter_congr {α : Type} {f g : α → α} (h : ∀ x, f x = g x) (n : Nat) (x : α) :
    iter f n x = iter g n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih, h]

theorem iter_id_of_eq {α : Type} {f : α → α} (h : ∀ x, f x = x) (n : Nat) (x : α) :
    iter f n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih, h]

theorem iter_fixed_of_dvd {α : Type} {f : α → α} {d n : Nat}
    (hd : ∀ x, iter f d x = x) (hdvd : d ∣ n) (x : α) : iter f n x = x := by
  rcases hdvd with ⟨k, rfl⟩
  rw [iter_mul]
  exact iter_id_of_eq hd k x

namespace RevCircuit
def pow {w : Nat} (f : RevCircuit w) : Nat → RevCircuit w
  | 0     => id w
  | n + 1 => comp f (pow f n)

theorem pow_toFun {w : Nat} (f : RevCircuit w) (n : Nat) (x : State w) :
    (f.pow n).toFun x = iter f.toFun n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pow, comp, iter, ih]

theorem iter_conj {w : Nat} (h f : RevCircuit w) (n : Nat) (x : State w) :
    iter (h.conj f).toFun n x = h.toFun (iter f.toFun n (h.invFun x)) := by
  induction n with
  | zero => simp [iter, h.right_inv]
  | succ n ih =>
    rw [iter_succ, ih]
    simp [conj, comp, inv, h.left_inv, iter_succ]

theorem conj_order_eq {w : Nat} (h f : RevCircuit w) (n : Nat)
    (hf : ∀ x, iter f.toFun n x = x) (x : State w) :
    iter (h.conj f).toFun n x = x := by
  rw [iter_conj, hf, h.right_inv]

end RevCircuit
/-- Elementary gcd subtraction step in core Lean 4. -/
theorem gcd_sub_left {a b : Nat} (hle : b ≤ a) : Nat.gcd (a - b) b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have h1 := Nat.gcd_dvd_left (a - b) b
      have h2 := Nat.gcd_dvd_right (a - b) b
      have h3 := Nat.dvd_add h1 h2
      rwa [Nat.sub_add_cancel hle] at h3
    · exact Nat.gcd_dvd_right (a - b) b
  · apply Nat.dvd_gcd
    · exact Nat.dvd_sub (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)
    · exact Nat.gcd_dvd_right a b

/-- Period-gcd reduction: if `f^a = id` and `f^b = id`, then `f^(gcd a b) = id`. -/
theorem iter_gcd_id {w : Nat} (f : RevCircuit w) {a b : Nat}
    (ha : ∀ x, iter f.toFun a x = x) (hb : ∀ x, iter f.toFun b x = x) :
    ∀ x, iter f.toFun (Nat.gcd a b) x = x := by
  have haux : ∀ s a b, a + b ≤ s →
      (∀ x, iter f.toFun a x = x) → (∀ x, iter f.toFun b x = x) →
      ∀ x, iter f.toFun (Nat.gcd a b) x = x := by
    intro s
    induction s with
    | zero =>
      intro a b hab ha _ x
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0; exact ha x
    | succ s ih =>
      intro a b hab ha hb x
      by_cases ha0 : a = 0
      · subst ha0; simpa using hb x
      · by_cases hb0 : b = 0
        · subst hb0; simpa using ha x
        · by_cases hle : a ≤ b
          · have hsub : ∀ y, iter f.toFun (b - a) y = y := by
              intro y
              have h1 := hb y
              have h2 : a + (b - a) = b := by omega
              rw [← h2, iter_add, ha] at h1
              exact h1
            have hgcd : Nat.gcd a b = Nat.gcd a (b - a) := by
              rw [Nat.gcd_comm a b, ← gcd_sub_left hle, Nat.gcd_comm]
            rw [hgcd]
            exact ih a (b - a) (by omega) ha hsub x
          · have hle' : b ≤ a := by omega
            have hsub : ∀ y, iter f.toFun (a - b) y = y := by
              intro y
              have h1 := ha y
              have h2 : b + (a - b) = a := by omega
              rw [← h2, iter_add, hb] at h1
              exact h1
            have hgcd : Nat.gcd a b = Nat.gcd (a - b) b := (gcd_sub_left hle').symm
            rw [hgcd]
            exact ih (a - b) b (by omega) hsub hb x
  exact haux (a + b) a b (Nat.le_refl _) ha hb

/-- Elementary arithmetic: any proper divisor of `2 ^ k` (`k ≥ 1`) divides `2 ^ (k - 1)`. -/
theorem dvd_pow2_pred_of_lt {g k : Nat} (hk : 1 ≤ k) (hdvd : g ∣ 2 ^ k) (hlt : g < 2 ^ k) :
    g ∣ 2 ^ (k - 1) := by
  rcases hdvd with ⟨q, hq⟩
  have hq2 : 2 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0; have := Nat.pow_pos (a := 2) (n := k) (by omega); omega
    · by_cases hq1 : q = 1
      · subst hq1; omega
      · omega
  -- `q` divides `2 ^ k` and `q ≥ 2`, so `2 ∣ q`
  have h2q : 2 ∣ q := by
    have hq_mod : q % 2 = 0 ∨ q % 2 = 1 := by omega
    rcases hq_mod with hev | hodd
    · exact Nat.dvd_of_mod_eq_zero hev
    · -- An odd divisor of `2^k` must equal `1`
      have hodd_dvd : ∀ m r, r ∣ 2 ^ m → r % 2 = 1 → r = 1 := by
        intro m
        induction m with
        | zero => intro r hr _; exact Nat.eq_one_of_dvd_one hr
        | succ m ih =>
          intro r hr hrodd
          rcases hr with ⟨t, ht⟩
          have ht_ev : t % 2 = 0 := by
            have h2pow : 2 ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
            rw [ht] at h2pow
            have hmul := Nat.mul_mod r t 2
            rw [h2pow, hrodd, Nat.one_mul] at hmul
            omega
          rcases Nat.dvd_of_mod_eq_zero ht_ev with ⟨t', rfl⟩
          have hr_dvd : r ∣ 2 ^ m := by
            refine ⟨t', ?_⟩
            rw [Nat.pow_succ] at ht
            have hassoc : r * (2 * t') = (r * t') * 2 := by
              rw [Nat.mul_comm 2 t', ← Nat.mul_assoc]
            rw [hassoc] at ht
            exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2) ht
          exact ih r hr_dvd hrodd
      have hq_eq_1 := hodd_dvd k q ⟨g, by rw [Nat.mul_comm]; exact hq⟩ hodd
      omega
  rcases h2q with ⟨q', rfl⟩
  refine ⟨q', ?_⟩
  have h2k : 2 ^ k = 2 ^ (k - 1) * 2 := by
    cases k with | zero => omega | succ k' => rw [Nat.pow_succ]; rfl
  rw [h2k] at hq
  have hassoc : g * (2 * q') = (g * q') * 2 := by
    rw [Nat.mul_comm 2 q', ← Nat.mul_assoc]
  rw [hassoc] at hq
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2) hq

/-- Elementary arithmetic: if `g ∣ 3 * 2 ^ k` and `¬(3 ∣ g)`, then `g ∣ 2 ^ k`. -/
theorem dvd_pow2_of_dvd_three_mul_pow2 {g k : Nat} (hdvd : g ∣ 3 * 2 ^ k) (hn3 : ¬ (3 ∣ g)) :
    g ∣ 2 ^ k := by
  -- Use Bezout via `Nat.gcd g 3 = 1`
  have hgcd1 : Nat.gcd g 3 = 1 := by
    have hle : Nat.gcd g 3 ∣ 3 := Nat.gcd_dvd_right g 3
    have hpos : 0 < Nat.gcd g 3 := Nat.gcd_pos_of_pos_right g (by omega)
    have hlt3 : Nat.gcd g 3 ≤ 3 := Nat.le_of_dvd (by omega) hle
    have hne3 : Nat.gcd g 3 ≠ 3 := fun h3 => hn3 (h3 ▸ Nat.gcd_dvd_left g 3)
    have hne2 : Nat.gcd g 3 ≠ 2 := fun h2 => by
      rw [h2] at hle; rcases hle with ⟨c, hc⟩; omega
    omega
  -- `g ∣ 3 * 2^k` and `g ∣ g * 2^k`, so `g ∣ gcd(g, 3) * 2^k = 2^k`
  have h1 : g ∣ Nat.gcd (g * 2 ^ k) (3 * 2 ^ k) :=
    Nat.dvd_gcd (Nat.dvd_mul_right g (2 ^ k)) hdvd
  rw [Nat.gcd_mul_right, hgcd1, Nat.one_mul] at h1
  exact h1

/-- Exact order criterion for pure powers of 2: `n = 2 ^ k`. -/
theorem hasExactOrder_pow2 {w : Nat} (f : RevCircuit w) (k : Nat) (hk : 1 ≤ k)
    (hupper : ∀ x, iter f.toFun (2 ^ k) x = x)
    (hlower : ∃ x, iter f.toFun (2 ^ (k - 1)) x ≠ x) :
    HasExactOrder f (2 ^ k) := by
  refine ⟨Nat.pow_pos (by omega), hupper, ?_⟩
  intro d hd0 hdlt
  exact Classical.byContradiction fun hnone => by
    have hd_id : ∀ x, iter f.toFun d x = x := fun x =>
      Classical.byContradiction fun hne => hnone ⟨x, hne⟩
    have hgcd_id := iter_gcd_id f hd_id hupper
    let g := Nat.gcd d (2 ^ k)
    have hg_dvd : g ∣ 2 ^ k := Nat.gcd_dvd_right d (2 ^ k)
    have hg_le : g ≤ d := Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d (2 ^ k))
    have hg_lt : g < 2 ^ k := Nat.lt_of_le_of_lt hg_le hdlt
    have hg_dvd_half := dvd_pow2_pred_of_lt hk hg_dvd hg_lt
    rcases hlower with ⟨x, hx⟩
    exact hx (iter_fixed_of_dvd hgcd_id hg_dvd_half x)

/-- Exact order criterion for `n = 3 * 2 ^ k`. -/
theorem hasExactOrder_three_mul_pow2 {w : Nat} (f : RevCircuit w) (k : Nat) (hk : 1 ≤ k)
    (hupper : ∀ x, iter f.toFun (3 * 2 ^ k) x = x)
    (hlower2 : ∃ x, iter f.toFun (3 * 2 ^ (k - 1)) x ≠ x)
    (hlower3 : ∃ x, iter f.toFun (2 ^ k) x ≠ x) :
    HasExactOrder f (3 * 2 ^ k) := by
  refine ⟨by have := Nat.pow_pos (a := 2) (n := k) (by omega); omega, hupper, ?_⟩
  intro d hd0 hdlt
  exact Classical.byContradiction fun hnone => by
    have hd_id : ∀ x, iter f.toFun d x = x := fun x =>
      Classical.byContradiction fun hne => hnone ⟨x, hne⟩
    have hgcd_id := iter_gcd_id f hd_id hupper
    let g := Nat.gcd d (3 * 2 ^ k)
    have hg_dvd : g ∣ 3 * 2 ^ k := Nat.gcd_dvd_right d (3 * 2 ^ k)
    have hg_le : g ≤ d := Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d (3 * 2 ^ k))
    have hg_lt : g < 3 * 2 ^ k := Nat.lt_of_le_of_lt hg_le hdlt
    by_cases h3 : 3 ∣ g
    · rcases h3 with ⟨m, hm⟩
      have hm_dvd : m ∣ 2 ^ k := by
        rcases hg_dvd with ⟨q, hq⟩
        refine ⟨q, Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3) ?_⟩
        rw [← Nat.mul_assoc, ← hm]
        exact hq
      have hm_lt : m < 2 ^ k := by omega
      have hm_dvd_half := dvd_pow2_pred_of_lt hk hm_dvd hm_lt
      have h3m_dvd : g ∣ 3 * 2 ^ (k - 1) := by
        rw [hm]; exact Nat.mul_dvd_mul_left 3 hm_dvd_half
      rcases hlower2 with ⟨x, hx⟩
      exact hx (iter_fixed_of_dvd hgcd_id h3m_dvd x)
    · have hg_dvd_pow2 := dvd_pow2_of_dvd_three_mul_pow2 hg_dvd h3
      rcases hlower3 with ⟨x, hx⟩
      exact hx (iter_fixed_of_dvd hgcd_id hg_dvd_pow2 x)

theorem lowEq_refl {w : Nat} (k : Nat) (x : State w) : LowEq k x x :=
  fun _ _ => rfl

theorem lowEq_symm {w : Nat} {k : Nat} {x y : State w} (h : LowEq k x y) : LowEq k y x :=
  fun j hj => (h j hj).symm

theorem lowEq_trans {w : Nat} {k : Nat} {x y z : State w}
    (h1 : LowEq k x y) (h2 : LowEq k y z) : LowEq k x z :=
  fun j hj => (h1 j hj).trans (h2 j hj)

theorem lowEq_mono_le {w : Nat} {k1 k2 : Nat} {x y : State w}
    (hle : k1 ≤ k2) (h : LowEq k2 x y) : LowEq k1 x y :=
  fun j hj => h j (Nat.lt_of_lt_of_le hj hle)

theorem lowEq_w_iff {w : Nat} (x y : State w) : LowEq w x y ↔ x = y := by
  constructor
  · intro h
    cases x with | mk x1 x2 =>
    cases y with | mk y1 y2 =>
    have h1 : x1 = y1 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      exact congrArg Prod.fst (h i hi)
    have h2 : x2 = y2 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      exact congrArg Prod.snd (h i hi)
    rw [h1, h2]
  · intro h
    subst h
    exact lowEq_refl w x

theorem IsBitAffine.weaken_base {w r1 r2 : Nat} {M : Nat → GL2} {f : State w → State w}
    (hle : r1 ≤ r2) (hf : IsBitAffine r1 M f) : IsBitAffine r2 M f := by
  refine ⟨?_, ?_⟩
  · intro hr2w x y hxy
    exact hf.lowEq_lift r2 hle hr2w x y hxy
  · intro k hr2k hkw x y hxy
    exact hf.2 k (Nat.le_trans hle hr2k) hkw x y hxy

theorem IsBitAffine.iter_pow {w r : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine r M f) (n : Nat) :
    IsBitAffine r (fun k => (M k).pow n) (iter f n) := by
  induction n with
  | zero =>
    exact IsBitAffine.id w r
  | succ n ih =>
    exact hf.comp ih

/-- Uniqueness of the Jacobian profile on `[r, w)`: the profile is an intrinsic invariant of `f`. -/
theorem IsBitAffine.profile_unique {w r : Nat} {M1 M2 : Nat → GL2} {f : State w → State w}
    (h1 : IsBitAffine r M1 f) (h2 : IsBitAffine r M2 f) :
    ∀ k, r ≤ k → k < w → M1 k = M2 k := by
  intro k hrk hkw
  apply GL2.act_ext
  intro v
  let x : State w := (if v.1 then (1#w <<< k) else 0#w, if v.2 then (1#w <<< k) else 0#w)
  let y : State w := (0#w, 0#w)
  have hlow : LowEq k x y := by
    intro j hj
    have hbit : (1#w <<< k).getLsbD j = false := by
      simp only [BitVec.getLsbD_shiftLeft]
      have hnot : ¬ (k ≤ j) := by omega
      simp [hnot]
    cases v1 : v.1 <;> cases v2 : v.2 <;> simp [slice, x, y, v1, v2, hbit]
  have hsl : vecXor (slice k x) (slice k y) = v := by
    have hbit : (1#w <<< k).getLsbD k = true := by simp [hkw]
    cases v with | mk v1 v2 =>
    cases v1 <;> cases v2 <;> simp [slice, vecXor, x, y, hbit]
  have e1 := h1.2 k hrk hkw x y hlow
  have e2 := h2.2 k hrk hkw x y hlow
  rw [hsl] at e1 e2
  exact e1.symm.trans e2

/-- **BSAS-CE Conjugacy Invariant Theorem:**
    Conjugate circuits in `A_w^(r)` have identical bit-slice Jacobian order profiles at every bit `k ∈ [r, w)`. -/
theorem bsasce_conjugacy_invariant {w r : Nat} {Mf Mg Mh : Nat → GL2}
    (f g h : RevCircuit w)
    (hf : IsBitAffine r Mf f.toFun) (hg : IsBitAffine r Mg g.toFun) (hh : IsBitAffine r Mh h.toFun)
    (hconj : ∀ x, g.toFun x = (h.conj f).toFun x) :
    ∀ k, r ≤ k → k < w → (Mg k).ord = (Mf k).ord := by
  intro k hrk hkw
  have hg_conj : IsBitAffine r (fun j => GL2.conj (Mh j) (Mf j)) g.toFun := by
    have hc := hh.conj h f hf
    refine ⟨?_, ?_⟩
    · intro hrw x y hxy; rw [hconj x, hconj y]; exact hc.1 hrw x y hxy
    · intro j hrj hjw x y hxy; rw [hconj x, hconj y]; exact hc.2 j hrj hjw x y hxy
  have huniq := hg.profile_unique hg_conj k hrk hkw
  rw [huniq]
  exact GL2.ord_conj (Mh k) (Mf k)

/-! ### Kernel Squaring-Filtration & Universal Master Order-Bound Engine -/

/-- **One-Line Kernel Squaring Lift:**
    If `f ∈ K_s(w)` (identity Jacobian above `r` and fixes bits `< s` with `r ≤ s`), then `f^2 ∈ K_{s+1}(w)`. -/
theorem kernel_sq_step {w r s : Nat} {f : State w → State w}
    (hf : IsBitAffine r (fun _ => GL2.I) f) (hrs : r ≤ s)
    (hfix : ∀ x, LowEq s (f x) x) :
    ∀ x, LowEq (s + 1) (iter f 2 x) x := by
  intro x
  by_cases hsw : s < w
  · rw [lowEq_succ_iff]
    refine ⟨?_, ?_⟩
    · change LowEq s (f (f x)) x
      exact lowEq_trans (hfix (f x)) (hfix x)
    · have hdiff := hf.2 s hrs hsw (f x) x (hfix x)
      rw [GL2.act_I] at hdiff
      rw [vecXor_comm (slice s (f x)) (slice s x)] at hdiff
      exact vecXor_cancel_right _ _ _ hdiff
  · have hfx : f x = x := (lowEq_w_iff (f x) x).mp (lowEq_mono_le (by omega) (hfix x))
    have hffx : iter f 2 x = x := by simp [iter, hfx]
    rw [hffx]
    exact lowEq_refl _ _

/-- **Iterated Kernel Squaring Lift:** `f ∈ K_s(w) → f^(2^t) ∈ K_{s+t}(w)`. -/
theorem kernel_pow2_step {w r : Nat} {f : State w → State w}
    (hf : IsBitAffine r (fun _ => GL2.I) f) :
    ∀ t s, r ≤ s → (∀ x, LowEq s (f x) x) → ∀ x, LowEq (s + t) (iter f (2 ^ t) x) x := by
  intro t
  induction t with
  | zero =>
    intro s _ hfix x
    simpa [iter] using hfix x
  | succ t ih =>
    intro s hrs hfix x
    have hprev : ∀ y, LowEq (s + t) (iter f (2 ^ t) y) y := ih s hrs hfix
    have haff_pow : IsBitAffine r (fun _ => GL2.I) (iter f (2 ^ t)) := by
      have hp := hf.iter_pow (2 ^ t)
      refine ⟨hp.1, ?_⟩
      intro k hrk hkw u v huv
      simpa [GL2.pow_I] using hp.2 k hrk hkw u v huv
    have hsq := kernel_sq_step haff_pow (by omega : r ≤ s + t) hprev x
    have hexp : 2 ^ (t + 1) = 2 ^ t * 2 := by rw [Nat.pow_succ]
    rw [hexp, iter_mul]
    simpa [Nat.add_assoc] using hsq

/-- **Kernel Order Bound:** `f ∈ K_s(w) → f^(2^(w - s)) = id`. -/
theorem kernel_pow2_eq_id {w r s : Nat} {f : State w → State w}
    (hf : IsBitAffine r (fun _ => GL2.I) f) (hrs : r ≤ s) (hsw : s ≤ w)
    (hfix : ∀ x, LowEq s (f x) x) :
    ∀ x, iter f (2 ^ (w - s)) x = x := by
  intro x
  have h := kernel_pow2_step hf (w - s) s hrs hfix x
  have heq : s + (w - s) = w := by omega
  rw [heq] at h
  exact (lowEq_w_iff _ _).mp h

/-- **BSAS-CE Master Finite-to-Infinite Order Bound:**
    If `f ∈ A_w^(r)` has base-block period `D` and Jacobian exponent `D` above `r`,
    then `f^(D * 2^(w - r)) = id` for all `w ≥ r`. -/
theorem bsasce_master_order_bound {w r D : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine r M f) (hrw : r ≤ w)
    (hbase : ∀ x, LowEq r (iter f D x) x)
    (hjac : ∀ k, r ≤ k → k < w → (M k).pow D = GL2.I) :
    ∀ x, iter f (D * 2 ^ (w - r)) x = x := by
  intro x
  rw [iter_mul]
  have haffD : IsBitAffine r (fun _ => GL2.I) (iter f D) := by
    have hp := hf.iter_pow D
    refine ⟨hp.1, ?_⟩
    intro k hrk hkw u v huv
    have hstep := hp.2 k hrk hkw u v huv
    dsimp only at hstep
    rw [hjac k hrk hkw] at hstep
    exact hstep
  exact kernel_pow2_eq_id haffD (Nat.le_refl r) hrw hbase x

/-- Helper: a fixed point of `f` is a fixed point of `iter f n`. -/
theorem iter_fixed_pt {α : Type} {f : α → α} {x : α} (h : f x = x) (n : Nat) :
    iter f n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih, h]

/-- **Zero-Preserving Sharpening (`r = 0`):**
    If `f ∈ A_w^(0)` fixes `(0, 0)` and `(M k)^D = I` for all `k < w`, then `f^(D * 2^(w - 1)) = id`. -/
theorem bsasce_zero_preserving_bound {w D : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine 0 M f) (hw : 1 ≤ w)
    (hzero : f (0#w, 0#w) = (0#w, 0#w))
    (hjac : ∀ k, k < w → (M k).pow D = GL2.I) :
    ∀ x, iter f (D * 2 ^ (w - 1)) x = x := by
  have hzeroD : iter f D (0#w, 0#w) = (0#w, 0#w) := iter_fixed_pt hzero D
  have haffD : IsBitAffine 0 (fun _ => GL2.I) (iter f D) := by
    have hp := hf.iter_pow D
    refine ⟨hp.1, ?_⟩
    intro k _ hkw u v huv
    have hstep := hp.2 k (Nat.zero_le k) hkw u v huv
    dsimp only at hstep
    rw [hjac k hkw] at hstep
    exact hstep
  have hfix1 : ∀ x, LowEq 1 (iter f D x) x := by
    intro x
    rw [lowEq_succ_iff]
    refine ⟨lowEq_zero _ _, ?_⟩
    have hdiff := haffD.2 0 (Nat.le_refl 0) hw x (0#w, 0#w) (lowEq_zero _ _)
    rw [hzeroD, GL2.act_I] at hdiff
    have hzero_slice : slice 0 (0#w, 0#w) = (false, false) := by simp [slice]
    simpa [hzero_slice, vecXor_zero_right] using hdiff
  intro x
  rw [iter_mul]
  exact kernel_pow2_eq_id haffD (Nat.zero_le 1) hw hfix1 x

/-- Helper: `2 ^ w = 2 * 2 ^ (w - 1)` for `1 ≤ w`. -/
theorem pow2_eq_two_mul_pred {w : Nat} (hw : 1 ≤ w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  cases w with
  | zero => omega
  | succ w' =>
    have hsub : w' + 1 - 1 = w' := Nat.add_sub_cancel w' 1
    rw [hsub, Nat.pow_succ, Nat.mul_comm]

/-- **Universal `A_w^(0)` Order Ceiling:**
    Every zero-preserving circuit in `A_w^(0)` satisfies `f^(3 * 2^w) = id` (`∀ w ≥ 1`). -/
theorem bsasce_universal_A0_ceiling {w : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine 0 M f) (hw : 1 ≤ w) (hzero : f (0#w, 0#w) = (0#w, 0#w)) :
    ∀ x, iter f (3 * 2 ^ w) x = x := by
  have h := bsasce_zero_preserving_bound (D := 6) hf hw hzero (fun k _ => GL2.pow_six (M k))
  have hexp : 3 * 2 ^ w = 6 * 2 ^ (w - 1) := by
    rw [pow2_eq_two_mul_pred hw]; omega
  rw [hexp]
  exact h

/-- **Uniform-Jacobian `U_w` Ceiling:**
    Every zero-preserving circuit with constant Jacobian `M₀` across all bits (`U_w`) satisfies
    EITHER `f^(2^w) = id` OR `f^(3 * 2^(w - 1)) = id` — it can NEVER achieve order `3 * 2^w`. -/
theorem bsasce_uniform_ceiling {w : Nat} {M0 : GL2} {f : State w → State w}
    (hf : IsBitAffine 0 (fun _ => M0) f) (hw : 1 ≤ w) (hzero : f (0#w, 0#w) = (0#w, 0#w)) :
    (∀ x, iter f (2 ^ w) x = x) ∨ (∀ x, iter f (3 * 2 ^ (w - 1)) x = x) := by
  rcases GL2.pow_two_or_three M0 with h2 | h3
  · left
    have h := bsasce_zero_preserving_bound (D := 2) hf hw hzero (fun _ _ => h2)
    rw [pow2_eq_two_mul_pred hw]
    exact h
  · right
    exact bsasce_zero_preserving_bound (D := 3) hf hw hzero (fun _ _ => h3)

/-! ### Commutator Filtration & Derived-Series Collapse Engine -/

/-- **First-Commutator Obstruction (`∀ w ≥ 1`):**
    Any commutator `[f, g]` of zero-preserving circuits in `A_w^(0)` satisfies `[f, g]^(3 * 2^(w-1)) = id`. -/
theorem bsasce_first_commutator_bound {w : Nat} {Mf Mg : Nat → GL2}
    (f g : RevCircuit w)
    (hf : IsBitAffine 0 Mf f.toFun) (hg : IsBitAffine 0 Mg g.toFun)
    (hw : 1 ≤ w)
    (hf0 : f.toFun (0#w, 0#w) = (0#w, 0#w)) (hg0 : g.toFun (0#w, 0#w) = (0#w, 0#w)) :
    ∀ x, iter (f.comm g).toFun (3 * 2 ^ (w - 1)) x = x := by
  have hfi0 : f.invFun (0#w, 0#w) = (0#w, 0#w) := by
    have := congrArg f.invFun hf0; simpa [f.left_inv] using this.symm
  have hgi0 : g.invFun (0#w, 0#w) = (0#w, 0#w) := by
    have := congrArg g.invFun hg0; simpa [g.left_inv] using this.symm
  have hc0 : (f.comm g).toFun (0#w, 0#w) = (0#w, 0#w) := by
    simp [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, hgi0, hfi0, hg0, hf0]
  exact bsasce_zero_preserving_bound (D := 3) (hf.comm f g hg) hw hc0
    (fun k _ => GL2.comm_pow_three (Mf k) (Mg k))

/-- **Second-Commutator Pure-2-Group Collapse (`∀ w ≥ 1`):**
    Any double commutator `[[f₁, f₂], [f₃, f₄]]` in zero-preserving `A_w^(0)` has order dividing `2^(w-1)`. -/
theorem bsasce_second_commutator_bound {w : Nat} {M1 M2 M3 M4 : Nat → GL2}
    (f1 f2 f3 f4 : RevCircuit w)
    (h1 : IsBitAffine 0 M1 f1.toFun) (h2 : IsBitAffine 0 M2 f2.toFun)
    (h3 : IsBitAffine 0 M3 f3.toFun) (h4 : IsBitAffine 0 M4 f4.toFun)
    (hw : 1 ≤ w)
    (z1 : f1.toFun (0#w, 0#w) = (0#w, 0#w)) (z2 : f2.toFun (0#w, 0#w) = (0#w, 0#w))
    (z3 : f3.toFun (0#w, 0#w) = (0#w, 0#w)) (z4 : f4.toFun (0#w, 0#w) = (0#w, 0#w)) :
    ∀ x, iter ((f1.comm f2).comm (f3.comm f4)).toFun (2 ^ (w - 1)) x = x := by
  have zero_comm : ∀ a b : RevCircuit w,
      a.toFun (0#w, 0#w) = (0#w, 0#w) → b.toFun (0#w, 0#w) = (0#w, 0#w) →
      (a.comm b).toFun (0#w, 0#w) = (0#w, 0#w) := by
    intro a b za zb
    have zai : a.invFun (0#w, 0#w) = (0#w, 0#w) := by
      have := congrArg a.invFun za; simpa [a.left_inv] using this.symm
    have zbi : b.invFun (0#w, 0#w) = (0#w, 0#w) := by
      have := congrArg b.invFun zb; simpa [b.left_inv] using this.symm
    simp [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, zbi, zai, zb, za]
  have zc := zero_comm _ _ (zero_comm _ _ z1 z2) (zero_comm _ _ z3 z4)
  have haff := (h1.comm f1 f2 h2).comm (f1.comm f2) (f3.comm f4) (h3.comm f3 f4 h4)
  have h := bsasce_zero_preserving_bound (D := 1) haff hw zc
    (fun k _ => by simp [GL2.pow, GL2.double_comm_eq_I, GL2.mul_I])
  simpa using h

/-- **Kernel Commutator Filtration Lift:**
    If `f, g ∈ K_s(w)` (`r ≤ s`), then `[f, g] ∈ K_{s+1}(w)`. -/
theorem kernel_comm_step {w r s : Nat} (f g : RevCircuit w)
    (hf : IsBitAffine r (fun _ => GL2.I) f.toFun)
    (hg : IsBitAffine r (fun _ => GL2.I) g.toFun)
    (hrs : r ≤ s)
    (hfixf : ∀ x, LowEq s (f.toFun x) x)
    (hfixg : ∀ x, LowEq s (g.toFun x) x) :
    ∀ x, LowEq (s + 1) ((f.comm g).toFun x) x := by
  intro x
  by_cases hsw : s < w
  · have hfg_gf : ∀ y, LowEq (s + 1) (f.toFun (g.toFun y)) (g.toFun (f.toFun y)) := by
      intro y
      rw [lowEq_succ_iff]
      refine ⟨?_, ?_⟩
      · exact lowEq_trans (lowEq_trans (hfixf (g.toFun y)) (hfixg y))
          (lowEq_symm (lowEq_trans (hfixg (f.toFun y)) (hfixf y)))
      · have d1 := hf.2 s hrs hsw (g.toFun y) y (hfixg y)
        have d2 := hg.2 s hrs hsw (f.toFun y) y (hfixf y)
        rw [GL2.act_I] at d1 d2
        cases hA : slice s (f.toFun (g.toFun y)) with | mk a1 a2 =>
        cases hB : slice s (g.toFun (f.toFun y)) with | mk b1 b2 =>
        cases hC : slice s (f.toFun y) with | mk c1 c2 =>
        cases hD : slice s (g.toFun y) with | mk d1' d2' =>
        cases hE : slice s y with | mk e1 e2 =>
        rw [hA, hC, hD, hE] at d1
        rw [hB, hD, hC, hE] at d2
        cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;>
        cases c1 <;> cases c2 <;> cases d1' <;> cases d2' <;> cases e1 <;> cases e2 <;>
        simp_all [vecXor]
    let y := f.invFun (g.invFun x)
    have h1 := hfg_gf y
    have hgf_y : g.toFun (f.toFun y) = x := by simp [y, f.right_inv, g.right_inv]
    rw [hgf_y] at h1
    simpa [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, y] using h1
  · have hf_id : ∀ y, f.toFun y = y := fun y => (lowEq_w_iff _ _).mp (lowEq_mono_le (by omega) (hfixf y))
    have hg_id : ∀ y, g.toFun y = y := fun y => (lowEq_w_iff _ _).mp (lowEq_mono_le (by omega) (hfixg y))
    have hfi_id : ∀ y, f.invFun y = y := fun y => by
      have := congrArg f.invFun (hf_id y); simpa [f.left_inv] using this.symm
    have hgi_id : ∀ y, g.invFun y = y := fun y => by
      have := congrArg g.invFun (hg_id y); simpa [g.left_inv] using this.symm
    have hcx : (f.comm g).toFun x = x := by
      simp [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, hf_id, hg_id, hfi_id, hgi_id]
    rw [hcx]
    exact lowEq_refl _ _

/-- Unified filtration invariant for `InDerivedSeries w d f`:
  - `d = 0`: `f ∈ A_w^(0)` and `f(0,0) = (0,0)`
  - `d = 1`: `f ∈ A_w^(0)` with `M^3 = I` and `f(0,0) = (0,0)`
  - `d = t + 2`: `f ∈ K_{t + 1}(w)` (identity Jacobian and `LowEq (t + 1) (f x) x`) -/
def DerivedSpec (w : Nat) : Nat → RevCircuit w → Prop
  | 0,     f => (∃ M, IsBitAffine 0 M f.toFun) ∧ f.toFun (0#w, 0#w) = (0#w, 0#w)
  | 1,     f => (∃ M, IsBitAffine 0 M f.toFun ∧ ∀ k, (M k).pow 3 = GL2.I) ∧ f.toFun (0#w, 0#w) = (0#w, 0#w)
  | t + 2, f => IsBitAffine 0 (fun _ => GL2.I) f.toFun ∧ (∀ x, LowEq (t + 1) (f.toFun x) x)

theorem derived_series_spec {w : Nat} (hw : 1 ≤ w) {d : Nat} {f : RevCircuit w}
    (hf : InDerivedSeries w d f) : DerivedSpec w d f := by
  induction hf with
  | base haff hz => exact ⟨⟨_, haff⟩, hz⟩
  | @id d =>
    match d with
    | 0 => exact ⟨⟨fun _ => GL2.I, IsBitAffine.id w 0⟩, rfl⟩
    | 1 => exact ⟨⟨fun _ => GL2.I, IsBitAffine.id w 0, fun _ => rfl⟩, rfl⟩
    | t + 2 => exact ⟨IsBitAffine.id w 0, fun x => lowEq_refl (t + 1) x⟩
  | @comm d f g _ _ ihf ihg =>
    match d with
    | 0 =>
      rcases ihf with ⟨⟨Mf, hafff⟩, zf⟩
      rcases ihg with ⟨⟨Mg, haffg⟩, zg⟩
      have zfi : f.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg f.invFun zf; simpa [f.left_inv] using this.symm
      have zgi : g.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg g.invFun zg; simpa [g.left_inv] using this.symm
      exact ⟨⟨_, hafff.comm f g haffg, fun k => GL2.comm_pow_three (Mf k) (Mg k)⟩,
        by simp [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, zgi, zfi, zg, zf]⟩
    | 1 =>
      rcases ihf with ⟨⟨Mf, hafff, pf⟩, zf⟩
      rcases ihg with ⟨⟨Mg, haffg, pg⟩, zg⟩
      have hcommI : ∀ k, GL2.comm (Mf k) (Mg k) = GL2.I := by
        intro k; have h1 := pf k; have h2 := pg k
        cases hm1 : Mf k <;> cases hm2 : Mg k <;> rw [hm1] at h1 <;> rw [hm2] at h2 <;>
          simp_all [GL2.pow, GL2.comm, GL2.mul, GL2.inv]
      have haff_c : IsBitAffine 0 (fun _ => GL2.I) (f.comm g).toFun := by
        have hc := hafff.comm f g haffg
        refine ⟨hc.1, ?_⟩
        intro k hrk hkw x y hxy
        have hstep := hc.2 k hrk hkw x y hxy
        dsimp only at hstep
        rw [hcommI k] at hstep
        exact hstep
      have zfi : f.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg f.invFun zf; simpa [f.left_inv] using this.symm
      have zgi : g.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg g.invFun zg; simpa [g.left_inv] using this.symm
      have zc : (f.comm g).toFun (0#w, 0#w) = (0#w, 0#w) := by
        simp [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, zgi, zfi, zg, zf]
      refine ⟨haff_c, ?_⟩
      intro x
      rw [lowEq_succ_iff]
      refine ⟨lowEq_zero _ _, ?_⟩
      have hdiff := haff_c.2 0 (Nat.le_refl 0) hw x (0#w, 0#w) (lowEq_zero _ _)
      rw [zc, GL2.act_I] at hdiff
      have hz0 : slice 0 (0#w, 0#w) = (false, false) := by simp [slice]
      simpa [hz0, vecXor_zero_right] using hdiff
    | t + 2 =>
      rcases ihf with ⟨h1, l1⟩
      rcases ihg with ⟨h2, l2⟩
      have haff_c : IsBitAffine 0 (fun _ => GL2.I) (f.comm g).toFun := by
        have hc := h1.comm f g h2
        refine ⟨hc.1, ?_⟩
        intro k hrk hkw x y hxy
        exact hc.2 k hrk hkw x y hxy
      exact ⟨haff_c, kernel_comm_step f g h1 h2 (Nat.zero_le _) l1 l2⟩
  | @comp d f g _ _ ihf ihg =>
    match d with
    | 0 =>
      rcases ihf with ⟨⟨M1, h1⟩, z1⟩
      rcases ihg with ⟨⟨M2, h2⟩, z2⟩
      exact ⟨⟨_, h1.comp h2⟩, by simp [RevCircuit.comp, z2, z1]⟩
    | 1 =>
      rcases ihf with ⟨⟨M1, h1, p1⟩, z1⟩
      rcases ihg with ⟨⟨M2, h2, p2⟩, z2⟩
      have pmul : ∀ k, (GL2.mul (M1 k) (M2 k)).pow 3 = GL2.I := by
        intro k; have hk1 := p1 k; have hk2 := p2 k
        cases hm1 : M1 k <;> cases hm2 : M2 k <;> rw [hm1] at hk1 <;> rw [hm2] at hk2 <;>
          simp_all [GL2.pow, GL2.mul]
      exact ⟨⟨_, h1.comp h2, pmul⟩, by simp [RevCircuit.comp, z2, z1]⟩
    | t + 2 =>
      rcases ihf with ⟨h1, l1⟩
      rcases ihg with ⟨h2, l2⟩
      have hc : IsBitAffine 0 (fun _ => GL2.I) (f.comp g).toFun := by
        have h := h1.comp h2
        refine ⟨h.1, ?_⟩
        intro k hrk hkw x y hxy
        exact h.2 k hrk hkw x y hxy
      exact ⟨hc, fun x => lowEq_trans (l1 _) (l2 x)⟩
  | @inv d f _ ihf =>
    match d with
    | 0 =>
      rcases ihf with ⟨⟨M1, h1⟩, z1⟩
      have zi : f.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg f.invFun z1; simpa [f.left_inv] using this.symm
      exact ⟨⟨_, h1.inv f⟩, zi⟩
    | 1 =>
      rcases ihf with ⟨⟨M1, h1, p1⟩, z1⟩
      have pinv : ∀ k, (M1 k).inv.pow 3 = GL2.I := by
        intro k; have hk := p1 k
        cases hm : M1 k <;> rw [hm] at hk <;> simp_all [GL2.pow, GL2.inv, GL2.mul]
      have zi : f.invFun (0#w, 0#w) = (0#w, 0#w) := by
        have := congrArg f.invFun z1; simpa [f.left_inv] using this.symm
      exact ⟨⟨_, h1.inv f, pinv⟩, zi⟩
    | t + 2 =>
      rcases ihf with ⟨h1, l1⟩
      have hi : IsBitAffine 0 (fun _ => GL2.I) f.inv.toFun := by
        have h := h1.inv f
        refine ⟨h.1, ?_⟩
        intro k hrk hkw x y hxy
        exact h.2 k hrk hkw x y hxy
      refine ⟨hi, ?_⟩
      intro x
      have h := l1 (f.invFun x)
      rw [f.right_inv] at h
      exact lowEq_symm h

/-- **BSAS-CE Infinite-Width Solvability / Derived-Series Collapse Theorem (`∀ w ≥ 1`):**
    Every circuit in the `(w + 1)`-th derived subgroup `(A_w^(0))^(w + 1)` is identically `id`. -/
theorem bsasce_derived_series_collapse {w : Nat} (hw : 1 ≤ w) (f : RevCircuit w)
    (hf : InDerivedSeries w (w + 1) f) :
    ∀ x, f.toFun x = x := by
  have heq : w + 1 = (w - 1) + 2 := by omega
  rw [heq] at hf
  have h := (derived_series_spec hw hf).2
  intro x
  have hwx : LowEq w (f.toFun x) x := by
    have heq' : (w - 1) + 1 = w := by omega
    rw [heq'] at h
    exact h x
  exact (lowEq_w_iff _ _).mp hwx

/-! ## Section 4: Pure-Silicon Reversible Gate Library & Membership Proofs -/

/-- Carry invariance: `BitVec.carry k x y c` depends ONLY on bits `< k` of `x` and `y`. -/
theorem carry_congr {w : Nat} (k : Nat) (x1 x2 y1 y2 : BitVec w) (c : Bool)
    (hx : ∀ j < k, x1.getLsbD j = x2.getLsbD j)
    (hy : ∀ j < k, y1.getLsbD j = y2.getLsbD j) :
    BitVec.carry k x1 y1 c = BitVec.carry k x2 y2 c := by
  induction k with
  | zero => simp [BitVec.carry_zero]
  | succ k ih =>
    have hx' : ∀ j < k, x1.getLsbD j = x2.getLsbD j := fun j hj => hx j (Nat.lt_succ_of_lt hj)
    have hy' : ∀ j < k, y1.getLsbD j = y2.getLsbD j := fun j hj => hy j (Nat.lt_succ_of_lt hj)
    have hxk : x1.getLsbD k = x2.getLsbD k := hx k (Nat.lt_succ_self k)
    have hyk : y1.getLsbD k = y2.getLsbD k := hy k (Nat.lt_succ_self k)
    simp only [BitVec.carry_succ, ih hx' hy', hxk, hyk]

/-- Fundamental pure-silicon differential bit-slice law for modular addition. -/
theorem add_bit_diff {w : Nat} (k : Nat) (hkw : k < w) (x1 x2 y1 y2 : BitVec w)
    (hx : ∀ j < k, x1.getLsbD j = x2.getLsbD j)
    (hy : ∀ j < k, y1.getLsbD j = y2.getLsbD j) :
    ((x1 + y1).getLsbD k ^^ (x2 + y2).getLsbD k) =
      ((x1.getLsbD k ^^ x2.getLsbD k) ^^ (y1.getLsbD k ^^ y2.getLsbD k)) := by
  have hc := carry_congr k x1 x2 y1 y2 false hx hy
  rw [BitVec.getLsbD_add hkw, BitVec.getLsbD_add hkw, hc]
  cases x1.getLsbD k <;> cases x2.getLsbD k <;> cases y1.getLsbD k <;> cases y2.getLsbD k <;>
    cases BitVec.carry k x2 y2 false <;> rfl

/-- Left Add-Shear `A_L(s)(a, b) = (a + (b <<< s), b)`. -/
def addShearL (w s : Nat) : RevCircuit w where
  toFun := fun (a, b) => (a + (b <<< s), b)
  invFun := fun (a, b) => (a - (b <<< s), b)
  left_inv := fun (a, b) => by simp [BitVec.add_sub_cancel]
  right_inv := fun (a, b) => by simp [BitVec.sub_add_cancel]

/-- Full Lane-Swap `S(a, b) = (b, a)`. -/
def laneSwap (w : Nat) : RevCircuit w where
  toFun := fun (a, b) => (b, a)
  invFun := fun (a, b) => (b, a)
  left_inv := fun (_, _) => rfl
  right_inv := fun (_, _) => rfl

theorem bitvec1_getLsbD_0 {w : Nat} (hw : 1 ≤ w) : (1#w).getLsbD 0 = true := by
  rw [BitVec.getLsbD_ofNat]; simp [(by omega : 0 < w)]

theorem bitvec1_getLsbD_pos {w : Nat} {k : Nat} (hk : 0 < k) : (1#w).getLsbD k = false := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hkw : k < w
  · have h2 : 2 ≤ 2 ^ k := calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    have hdiv : 1 / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    simp [hkw, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  · simp [hkw]

/-! ### `IsBitAffine` Membership Theorems for the Gate Library -/

theorem addShearR_bitAffine (w s : Nat) :
    IsBitAffine 0 (fun _ => if s = 0 then GL2.L else GL2.I) (addShearR w s).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ hkw x y hxy
  have hx : ∀ j < k, x.1.getLsbD j = y.1.getLsbD j := fun j hj => congrArg Prod.fst (hxy j hj)
  have hy : ∀ j < k, x.2.getLsbD j = y.2.getLsbD j := fun j hj => congrArg Prod.snd (hxy j hj)
  have hsh : ∀ j < k, (x.1 <<< s).getLsbD j = (y.1 <<< s).getLsbD j := by
    intro j hj
    simp only [BitVec.getLsbD_shiftLeft]
    by_cases hsj : s ≤ j
    · simp [hx (j - s) (by omega)]
    · have hlt : j < s := by omega
      simp [hlt]
  have hadd := add_bit_diff k hkw x.2 y.2 (x.1 <<< s) (y.1 <<< s) hy hsh
  by_cases hs0 : s = 0
  · subst hs0
    simp only [addShearR, slice, vecXor, GL2.act, ite_true]
    apply Prod.ext
    · rfl
    · simp only [BitVec.shiftLeft_zero] at hadd ⊢
      rw [hadd, Bool.xor_comm]
  · have hshk : (x.1 <<< s).getLsbD k = (y.1 <<< s).getLsbD k := by
      simp only [BitVec.getLsbD_shiftLeft]
      by_cases hsk : s ≤ k
      · simp [hx (k - s) (by omega)]
      · have hlt : k < s := by omega
        simp [hlt]
    simp only [addShearR, slice, vecXor, hs0, ite_false, GL2.act]
    apply Prod.ext
    · rfl
    · rw [hadd, hshk, Bool.xor_self, Bool.xor_false]

theorem addShearLMask_bitAffine (w : Nat) (m : BitVec w) :
    IsBitAffine 0 (fun k => if m.getLsbD k then GL2.U else GL2.I) (addShearLMask w m).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ hkw x y hxy
  have hx : ∀ j < k, x.1.getLsbD j = y.1.getLsbD j := fun j hj => congrArg Prod.fst (hxy j hj)
  have hy : ∀ j < k, x.2.getLsbD j = y.2.getLsbD j := fun j hj => congrArg Prod.snd (hxy j hj)
  have hmask : ∀ j < k, (x.2 &&& m).getLsbD j = (y.2 &&& m).getLsbD j := by
    intro j hj; simp [hy j hj]
  have hadd := add_bit_diff k hkw x.1 y.1 (x.2 &&& m) (y.2 &&& m) hx hmask
  cases hmk : m.getLsbD k
  · simp only [addShearLMask, slice, vecXor, hmk, Bool.false_eq_true, ite_false, GL2.act]
    apply Prod.ext
    · rw [hadd]; simp [hmk]
    · rfl
  · simp only [addShearLMask, slice, vecXor, hmk, ite_true, GL2.act]
    apply Prod.ext
    · rw [hadd]; simp [hmk]
    · rfl

theorem xorShearR_bitAffine (w s : Nat) :
    IsBitAffine 0 (fun _ => if s = 0 then GL2.L else GL2.I) (xorShearR w s).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ hkw x y hxy
  have hx : ∀ j < k, x.1.getLsbD j = y.1.getLsbD j := fun j hj => congrArg Prod.fst (hxy j hj)
  by_cases hs0 : s = 0
  · subst hs0
    simp only [xorShearR, slice, vecXor, GL2.act, ite_true, BitVec.shiftLeft_zero, BitVec.getLsbD_xor]
    apply Prod.ext
    · rfl
    · cases x.1.getLsbD k <;> cases y.1.getLsbD k <;> cases x.2.getLsbD k <;> cases y.2.getLsbD k <;> rfl
  · have hshk : (x.1 <<< s).getLsbD k = (y.1 <<< s).getLsbD k := by
      simp only [BitVec.getLsbD_shiftLeft]
      by_cases hsk : s ≤ k
      · simp [hx (k - s) (by omega)]
      · have hlt : k < s := by omega
        simp [hlt]
    simp only [xorShearR, slice, vecXor, hs0, ite_false, GL2.act, BitVec.getLsbD_xor, hshk]
    apply Prod.ext
    · rfl
    · cases x.2.getLsbD k <;> cases y.2.getLsbD k <;> cases (y.1 <<< s).getLsbD k <;> rfl

theorem xorShearL_bitAffine (w s : Nat) :
    IsBitAffine 0 (fun _ => if s = 0 then GL2.U else GL2.I) (xorShearL w s).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ hkw x y hxy
  have hy : ∀ j < k, x.2.getLsbD j = y.2.getLsbD j := fun j hj => congrArg Prod.snd (hxy j hj)
  by_cases hs0 : s = 0
  · subst hs0
    simp only [xorShearL, slice, vecXor, GL2.act, ite_true, BitVec.shiftLeft_zero, BitVec.getLsbD_xor]
    apply Prod.ext
    · cases x.1.getLsbD k <;> cases y.1.getLsbD k <;> cases x.2.getLsbD k <;> cases y.2.getLsbD k <;> rfl
    · rfl
  · have hshk : (x.2 <<< s).getLsbD k = (y.2 <<< s).getLsbD k := by
      simp only [BitVec.getLsbD_shiftLeft]
      by_cases hsk : s ≤ k
      · simp [hy (k - s) (by omega)]
      · have hlt : k < s := by omega
        simp [hlt]
    simp only [xorShearL, slice, vecXor, hs0, ite_false, GL2.act, BitVec.getLsbD_xor, hshk]
    apply Prod.ext
    · cases x.1.getLsbD k <;> cases y.1.getLsbD k <;> cases (y.2 <<< s).getLsbD k <;> rfl
    · rfl

theorem crossBitSwap_bitAffine (w : Nat) (m : BitVec w) :
    IsBitAffine 0 (fun k => if m.getLsbD k then GL2.J else GL2.I) (crossBitSwap w m).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ hkw x y _
  simp only [crossBitSwap, slice, vecXor, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hkw, decide_true, Bool.true_and]
  cases hmk : m.getLsbD k <;> simp [GL2.act]

theorem laneSwap_bitAffine (w : Nat) :
    IsBitAffine 0 (fun _ => GL2.J) (laneSwap w).toFun := by
  refine ⟨fun _ _ _ _ => lowEq_zero _ _, ?_⟩
  intro k _ _ x y _
  simp [laneSwap, slice, vecXor, GL2.act]

theorem intraBitSwap01_bitAffine (w : Nat) (hw : 2 ≤ w) :
    IsBitAffine 2 (fun _ => GL2.I) (intraBitSwap01 w hw).toFun := by
  refine ⟨?_, ?_⟩
  · intro _ x y hxy j hj
    match j with
    | 0 =>
      have h1 := hxy 1 (by omega)
      have h1a : x.1.getLsbD 1 = y.1.getLsbD 1 := congrArg Prod.fst h1
      have h1b : x.2.getLsbD 1 = y.2.getLsbD 1 := congrArg Prod.snd h1
      simp [intraBitSwap01, slice, swap01_getLsbD_0 hw, h1a, h1b]
    | 1 =>
      have h0 := hxy 0 (by omega)
      have h0a : x.1.getLsbD 0 = y.1.getLsbD 0 := congrArg Prod.fst h0
      have h0b : x.2.getLsbD 0 = y.2.getLsbD 0 := congrArg Prod.snd h0
      simp [intraBitSwap01, slice, swap01_getLsbD_1 hw, h0a, h0b]
    | j + 2 => omega
  · intro k hk2 _ x y _
    simp [intraBitSwap01, slice, vecXor, GL2.act, swap01_getLsbD_ge2 _ k hk2]

theorem circuitE_bitAffine (w : Nat) :
    IsBitAffine 0 (fun k => GL2.mul GL2.L (if (1#w).getLsbD k then GL2.U else GL2.I)) (circuitE w).toFun := by
  have h1 := addShearR_bitAffine w 0
  have h2 := addShearLMask_bitAffine w 1#w
  simpa [circuitE, RevCircuit.comp] using h1.comp h2

theorem circuitE_zero (w : Nat) : (circuitE w).toFun (0#w, 0#w) = (0#w, 0#w) := by
  simp [circuitE, RevCircuit.comp, addShearR, addShearLMask]

theorem getLsbD_zero_iff_mod2 {w : Nat} (hw : 1 ≤ w) (b : BitVec w) :
    b.getLsbD 0 = decide (b.toNat % 2 = 1) := by
  rw [BitVec.getLsbD_eq_getElem (by omega : 0 < w), BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]

theorem bitvec_and_one_of_odd {w : Nat} (hw : 1 ≤ w) (b : BitVec w) (hodd : b.toNat % 2 = 1) :
    b &&& 1#w = 1#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  match k with
  | 0 =>
    have hb0 : b.getLsbD 0 = true := by rw [getLsbD_zero_iff_mod2 hw, hodd]; rfl
    simp [hb0]
  | k + 1 =>
    simp [bitvec1_getLsbD_pos (by omega : 0 < k + 1)]

theorem bitvec_and_one_of_even {w : Nat} (hw : 1 ≤ w) (b : BitVec w) (heven : b.toNat % 2 = 0) :
    b &&& 1#w = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  match k with
  | 0 =>
    have hb0 : b.getLsbD 0 = false := by rw [getLsbD_zero_iff_mod2 hw, heven]; rfl
    simp [hb0]
  | k + 1 =>
    simp [bitvec1_getLsbD_pos (by omega : 0 < k + 1)]

theorem toNat_add_mod2 {w : Nat} (hw : 1 ≤ w) (x y : BitVec w) :
    (x + y).toNat % 2 = (x.toNat + y.toNat) % 2 := by
  rw [BitVec.toNat_add]
  have hdvd : 2 ∣ 2 ^ w := by
    rw [pow2_eq_two_mul_pred hw]; exact Nat.dvd_mul_right 2 _
  exact Nat.mod_mod_of_dvd _ hdvd

/-- Exact 3-step formula for `E` on `(even, odd)` pairs (`∀ w ≥ 1`). -/
theorem circuitE_three_steps {w : Nat} (hw : 1 ≤ w) (a b : BitVec w)
    (ha : a.toNat % 2 = 0) (hb : b.toNat % 2 = 1) :
    iter (circuitE w).toFun 3 (a, b) = (a + 2#w, b + a + a + a + 4#w) := by
  have h1mod : (1#w).toNat % 2 = 1 := by
    have h2 : 2 ≤ 2 ^ w := calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
  have hb_and : b &&& 1#w = 1#w := bitvec_and_one_of_odd hw b hb
  have ha1 : (a + 1#w).toNat % 2 = 1 := by rw [toNat_add_mod2 hw]; omega
  have hb1 : (b + (a + 1#w)).toNat % 2 = 0 := by rw [toNat_add_mod2 hw]; omega
  have hb1_and : (b + (a + 1#w)) &&& 1#w = 0#w := bitvec_and_one_of_even hw _ hb1
  have hb2 : ((b + (a + 1#w)) + (a + 1#w)).toNat % 2 = 1 := by rw [toNat_add_mod2 hw]; omega
  have hb2_and : ((b + (a + 1#w)) + (a + 1#w)) &&& 1#w = 1#w := bitvec_and_one_of_odd hw _ hb2
  simp only [iter, circuitE, RevCircuit.comp, addShearR, addShearLMask, BitVec.shiftLeft_zero]
  rw [hb_and, hb1_and, BitVec.add_zero, hb2_and]
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
    congr 1; omega

/-- Closed-form orbit formula: `E^(3 * m)(0, 1) = (2*m, 3*m^2 + m + 1)` in `(BitVec w)^2` (`∀ w ≥ 1, ∀ m`). -/
theorem circuitE_orbit_closed_form {w : Nat} (hw : 1 ≤ w) (m : Nat) :
    iter (circuitE w).toFun (3 * m) (0#w, 1#w) =
      (BitVec.ofNat w (2 * m), BitVec.ofNat w (3 * m * m + m + 1)) := by
  have hdvd : 2 ∣ 2 ^ w := by
    rw [pow2_eq_two_mul_pred hw]; exact Nat.dvd_mul_right 2 _
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, ih]
    have ha : (BitVec.ofNat w (2 * m)).toNat % 2 = 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd]; omega
    have hb : (BitVec.ofNat w (3 * m * m + m + 1)).toNat % 2 = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd]
      have hm2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
      have hsq : (3 * m * m + m) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod (3 * m) m 2, Nat.mul_mod 3 m 2]
        rcases hm2 with h | h <;> rw [h] <;> rfl
      omega
    rw [circuitE_three_steps hw _ _ ha hb]
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      exact congrArg (· % 2 ^ w) (by omega)
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      congr 1
      have hpoly : (3 + 3 * m) * (m + 1) = 3 * m * m + 6 * m + 3 := by
        calc (3 + 3 * m) * (m + 1)
            = (3 + 3 * m) * m + (3 + 3 * m) * 1 := Nat.mul_add (3 + 3 * m) m 1
          _ = 3 * m + 3 * m * m + (3 + 3 * m) := by rw [Nat.add_mul, Nat.mul_one]
          _ = 3 * m * m + 6 * m + 3 := by omega
      rw [hpoly]; omega

/-- Bit-0 orbit of `E` on `(0, 1)` has exact period 3, so `E^(2^w)(0, 1) ≠ (0, 1)`. -/
theorem circuitE_bit0_ne {w : Nat} (hw : 1 ≤ w) :
    iter (circuitE w).toFun (2 ^ w) (0#w, 1#w) ≠ (0#w, 1#w) := by
  have h10 := bitvec1_getLsbD_0 hw
  have hbit0 : ∀ n : Nat,
      slice 0 (iter (circuitE w).toFun n (0#w, 1#w)) =
        match n % 3 with
        | 0 => (false, true)
        | 1 => (true, false)
        | _ => (true, true) := by
    have hstep : ∀ x : State w,
        slice 0 ((circuitE w).toFun x) = GL2.R1.act (slice 0 x) := by
      intro x
      have haff := circuitE_bitAffine w
      have h0 := haff.2 0 (Nat.le_refl 0) hw x (0#w, 0#w) (lowEq_zero _ _)
      rw [circuitE_zero] at h0
      have hz : slice 0 (0#w, 0#w) = (false, false) := by simp [slice]
      simpa [h10, hz, vecXor_zero_right, GL2.mul] using h0
    intro n
    induction n with
    | zero => simp [iter, slice, h10]
    | succ n ih =>
      rw [iter, hstep, ih]
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h | h | h
      · have h' : (n + 1) % 3 = 1 := by omega
        rw [h, h']; rfl
      · have h' : (n + 1) % 3 = 2 := by omega
        rw [h, h']; rfl
      · have h' : (n + 1) % 3 = 0 := by omega
        rw [h, h']; rfl
  have hpow2_mod3 : ∀ k, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih => rw [Nat.pow_succ]; rcases ih with h | h <;> omega
  intro heq
  have hs := congrArg (slice 0) heq
  rw [hbit0 (2 ^ w)] at hs
  have hinit : slice 0 (0#w, 1#w) = (false, true) := by simp [slice, h10]
  rw [hinit] at hs
  rcases hpow2_mod3 w with h | h <;> simp [h] at hs

/-- **THEOREM 1A (Exact Saturation of the Universal `A_w^(0)` Ceiling):**
    For ALL `w ≥ 2`, `E = A_R(0) ∘ A_{L,{0}}` has exact group order `3 * 2 ^ w`. -/
theorem theorem1_circuitE_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder (circuitE w) (3 * 2 ^ w) := by
  have hw1 : 1 ≤ w := by omega
  apply hasExactOrder_three_mul_pow2 (circuitE w) w hw1
  · exact bsasce_universal_A0_ceiling (circuitE_bitAffine w) hw1 (circuitE_zero w)
  · refine ⟨(0#w, 1#w), ?_⟩
    rw [circuitE_orbit_closed_form hw1 (2 ^ (w - 1))]
    intro heq
    have hb := congrArg (fun p => p.2.toNat) heq
    simp only [BitVec.toNat_ofNat] at hb
    have hpow_dvd : 2 ^ w ∣ 3 * 2 ^ (w - 1) * 2 ^ (w - 1) := by
      have hexp : 2 ^ (w - 1) * 2 ^ (w - 1) = 2 ^ (2 * w - 2) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [Nat.mul_assoc, hexp]
      exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega : w ≤ 2 * w - 2)) (Nat.dvd_mul_left _ 3)
    rcases hpow_dvd with ⟨q, hq⟩
    have hlt : 2 ^ (w - 1) + 1 < 2 ^ w := by
      have hhalf := pow2_eq_two_mul_pred hw1
      have hpos : 2 ≤ 2 ^ (w - 1) := calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hmod1 : (3 * 2 ^ (w - 1) * 2 ^ (w - 1) + 2 ^ (w - 1) + 1) % 2 ^ w = 2 ^ (w - 1) + 1 := by
      rw [hq, Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hmod2 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
      have : 4 ≤ 2 ^ w := calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      omega)
    rw [hmod1, hmod2] at hb
    have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by omega)
    omega
  · exact ⟨(0#w, 1#w), circuitE_bit0_ne hw1⟩

/-- **THEOREM 1B (Non-Commutator Obstruction `∀ w ≥ 2`):**
    `E = A_R(0) ∘ A_{L,{0}}` is NEVER a commutator `[f, g]` of zero-preserving circuits in `A_w^(0)`. -/
theorem theorem1_circuitE_not_commutator (w : Nat) (hw : 2 ≤ w)
    (f g : RevCircuit w) (Mf Mg : Nat → GL2)
    (hf : IsBitAffine 0 Mf f.toFun) (hg : IsBitAffine 0 Mg g.toFun)
    (hf0 : f.toFun (0#w, 0#w) = (0#w, 0#w)) (hg0 : g.toFun (0#w, 0#w) = (0#w, 0#w)) :
    ¬ (∀ x, (circuitE w).toFun x = (f.comm g).toFun x) := by
  intro heq
  have hord := theorem1_circuitE_exact_order w hw
  have hlt : 3 * 2 ^ (w - 1) < 3 * 2 ^ w := by
    have : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hpos : 0 < 3 * 2 ^ (w - 1) := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  rcases hord.2.2 (3 * 2 ^ (w - 1)) hpos hlt with ⟨x, hx⟩
  rw [iter_congr heq] at hx
  exact hx (bsasce_first_commutator_bound f g hf hg (by omega) hf0 hg0 x)

/-- **THEOREM 1C (Strict `U_w ⊊ A_w^(0)` Separation even under FULL Symmetric-Group Conjugacy `∀ w ≥ 2`):**
    `E ∈ A_w^(0)` is NOT conjugate even in `RevCircuit w` (all bijections!) to ANY zero-preserving
    uniform-Jacobian circuit `u ∈ U_w`. -/
theorem theorem1_circuitE_not_sym_conjugate_uniform (w : Nat) (hw : 2 ≤ w)
    (u h : RevCircuit w) (M0 : GL2)
    (hu : IsBitAffine 0 (fun _ => M0) u.toFun)
    (hu0 : u.toFun (0#w, 0#w) = (0#w, 0#w)) :
    ¬ (∀ x, (circuitE w).toFun x = (h.conj u).toFun x) := by
  intro hconj
  have hord := theorem1_circuitE_exact_order w hw
  rcases bsasce_uniform_ceiling hu (by omega) hu0 with h2w | h3w
  · have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have hlt : 2 ^ w < 3 * 2 ^ w := by omega
    rcases hord.2.2 (2 ^ w) hpos hlt with ⟨x, hx⟩
    rw [iter_congr hconj] at hx
    exact hx (RevCircuit.conj_order_eq h u (2 ^ w) h2w x)
  · have hpos : 0 < 3 * 2 ^ (w - 1) := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    have hlt : 3 * 2 ^ (w - 1) < 3 * 2 ^ w := by
      have : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    rcases hord.2.2 (3 * 2 ^ (w - 1)) hpos hlt with ⟨x, hx⟩
    rw [iter_congr hconj] at hx
    exact hx (RevCircuit.conj_order_eq h u (3 * 2 ^ (w - 1)) h3w x)

theorem circuitP_bitAffine (w : Nat) :
    IsBitAffine 0 (fun k => GL2.mul (if (1#w).getLsbD k then GL2.J else GL2.I) GL2.L) (circuitP w).toFun := by
  have h1 := crossBitSwap_bitAffine w 1#w
  have h2 := addShearR_bitAffine w 0
  simpa [circuitP, RevCircuit.comp] using h1.comp h2

/-- Helper: universal quantification over `State 2` via `Fin 4 × Fin 4` (kernel-decidable!). -/
theorem forall_state2 {P : State 2 → Prop}
    (h : ∀ a b : Fin 4, P (BitVec.ofNat 2 a.val, BitVec.ofNat 2 b.val)) :
    ∀ y : State 2, P y := by
  intro ⟨a, b⟩
  have ha : BitVec.ofNat 2 a.toNat = a := by apply BitVec.eq_of_toNat_eq; simp
  have hb : BitVec.ofNat 2 b.toNat = b := by apply BitVec.eq_of_toNat_eq; simp
  rw [← ha, ← hb]
  exact h ⟨a.toNat, a.isLt⟩ ⟨b.toNat, b.isLt⟩

theorem setWidth2_add {w : Nat} (hw : 2 ≤ w) (u v : BitVec w) :
    (u + v).setWidth 2 = u.setWidth 2 + v.setWidth 2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  have hdvd : 2 ^ 2 ∣ 2 ^ w := Nat.pow_dvd_pow 2 hw
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]

theorem setWidth2_xor {w : Nat} (u v : BitVec w) :
    (u ^^^ v).setWidth 2 = u.setWidth 2 ^^^ v.setWidth 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem circuitP_six_lowEq2 {w : Nat} (hw : 2 ≤ w) :
    ∀ x : State w, LowEq 2 (iter (circuitP w).toFun 6 x) x := by
  have htrunc_step : ∀ x : State w,
      (((circuitP w).toFun x).1.setWidth 2, ((circuitP w).toFun x).2.setWidth 2) =
        (circuitP 2).toFun (x.1.setWidth 2, x.2.setWidth 2) := by
    intro ⟨a, b⟩
    have hadd := setWidth2_add hw b a
    have h1w0 := bitvec1_getLsbD_0 (by omega : 1 ≤ w)
    have h1w1 := bitvec1_getLsbD_pos (w := w) (k := 1) (by omega)
    have hsw : ∀ u v : BitVec w,
        (((u &&& ~~~1#w) ||| (v &&& 1#w)).setWidth 2) =
          ((u.setWidth 2 &&& ~~~1#2) ||| (v.setWidth 2 &&& 1#2)) := by
      intro u v
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      match i with
      | 0 =>
        have h0w : 0 < w := by omega
        simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
          BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, h0w, h1w0]
        rfl
      | 1 =>
        have h1w : 1 < w := by omega
        simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
          BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, h1w, h1w1]
        rfl
    simp only [circuitP, RevCircuit.comp, crossBitSwap, addShearR, BitVec.shiftLeft_zero]
    rw [hsw, hsw, hadd]
  have htrunc_iter : ∀ n (x : State w),
      ((iter (circuitP w).toFun n x).1.setWidth 2, (iter (circuitP w).toFun n x).2.setWidth 2) =
        iter (circuitP 2).toFun n (x.1.setWidth 2, x.2.setWidth 2) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      simp only [iter]
      rw [htrunc_step, ih]
  have hfin : ∀ y : State 2, iter (circuitP 2).toFun 6 y = y :=
    forall_state2 (by decide)
  intro x j hj
  have h6 := htrunc_iter 6 x
  rw [hfin] at h6
  have h1 := congrArg (fun p => p.1.getLsbD j) h6
  have h2 := congrArg (fun p => p.2.getLsbD j) h6
  simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and] at h1 h2
  exact Prod.ext h1 h2

/-- Helper: when `b` is even, `b + 1#w` equals `b ||| 1#w` (i.e., `b &&& ~~~1#w = b`, and flipping bit 0 adds 1). -/
theorem odd_sub1_eq_and_not1 {w : Nat} (hw : 1 ≤ w) (b : BitVec w) (hb : b.toNat % 2 = 1) :
    b &&& ~~~1#w = b - 1#w := by
  have h1lt : 1 < 2 ^ w := by
    have : 2 ≤ 2 ^ w := calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
    omega
  -- Prove by `toNat`: clearing bit 0 of an odd number `b` gives `b.toNat - 1`
  have hsub_nat : (b - 1#w).toNat = b.toNat - 1 := by
    rw [BitVec.toNat_sub]
    have h1 : (1#w).toNat = 1 := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt]
    rw [h1]
    have hge1 : 1 ≤ b.toNat := by omega
    have hlt : b.toNat < 2 ^ w := b.isLt
    have h1' : (2 ^ w - 1 + b.toNat) = 2 ^ w + (b.toNat - 1) := by omega
    rw [h1', Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hbm1_even : (b - 1#w).toNat % 2 = 0 := by rw [hsub_nat]; omega
  -- Show `(b &&& ~~~1#w) + 1#w = b`? Even simpler: `(b &&& ~~~1#w) ^^^ 1#w = b` and compare with `b - 1#w` via bits!
  -- Here `toNat` of `(b &&& ~~~1#w)` is `2 * (b.toNat / 2) = b.toNat - 1`.
  -- Prove via bits using `(b - 1#w) + 1#w = b` and zero carry!
  have hbm0 : (b - 1#w).getLsbD 0 = false := by rw [getLsbD_zero_iff_mod2 hw, hbm1_even]; rfl
  have hcarry0 : ∀ j, BitVec.carry j (b - 1#w) 1#w false = false := by
    intro j
    induction j with
    | zero => exact BitVec.carry_zero
    | succ j ih =>
      rw [BitVec.carry_succ, ih]
      cases j with
      | zero => simp [hbm0]
      | succ j' => rw [bitvec1_getLsbD_pos (by omega : 0 < j' + 1)]; simp
  have h10 := bitvec1_getLsbD_0 hw
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  match k with
  | 0 =>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
      h10, Bool.not_true, Bool.and_false, hbm0]
  | k + 1 =>
    have hbit : b.getLsbD (k + 1) = (b - 1#w).getLsbD (k + 1) := by
      have hadd := congrArg (fun z => z.getLsbD (k + 1)) (BitVec.sub_add_cancel b 1#w)
      rw [BitVec.getLsbD_add hk, bitvec1_getLsbD_pos (by omega : 0 < k + 1), hcarry0 (k + 1)] at hadd
      simpa using hadd.symm
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
      bitvec1_getLsbD_pos (by omega : 0 < k + 1), Bool.not_false, Bool.and_true, hbit]

/-- Helper: when `e` is even, `e ||| 1#w = e + 1#w`. -/
theorem even_or1_eq_add1 {w : Nat} (hw : 1 ≤ w) (e : BitVec w) (he : e.toNat % 2 = 0) :
    e ||| 1#w = e + 1#w := by
  have he0 : e.getLsbD 0 = false := by rw [getLsbD_zero_iff_mod2 hw, he]; rfl
  have hcarry0 : ∀ j, BitVec.carry j e 1#w false = false := by
    intro j
    induction j with
    | zero => exact BitVec.carry_zero
    | succ j ih =>
      rw [BitVec.carry_succ, ih]
      cases j with
      | zero => simp [he0]
      | succ j' => rw [bitvec1_getLsbD_pos (by omega : 0 < j' + 1)]; simp
  have h10 := bitvec1_getLsbD_0 hw
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_add hk, hcarry0 k]
  match k with
  | 0 => simp [h10, he0]
  | k + 1 => simp [bitvec1_getLsbD_pos (by omega : 0 < k + 1)]

/-- Closed-form orbit for `P` on `(0, 1)`: `P^(3*m)(0, 1) = (0, 2*m + 1)`. -/
theorem circuitP_orbit_closed_form {w : Nat} (hw : 2 ≤ w) (m : Nat) :
    iter (circuitP w).toFun (3 * m) (0#w, 1#w) = (0#w, BitVec.ofNat w (2 * m + 1)) := by
  have hw1 : 1 ≤ w := by omega
  have h10 := bitvec1_getLsbD_0 hw1
  have hstep3 : ∀ b : BitVec w, b.toNat % 2 = 1 →
      iter (circuitP w).toFun 3 (0#w, b) = (0#w, b + 2#w) := by
    intro b hb
    have hb0 : b.getLsbD 0 = true := by rw [getLsbD_zero_iff_mod2 hw1, hb]; rfl
    have hs1 : (circuitP w).toFun (0#w, b) = (1#w, b - 1#w) := by
      simp only [circuitP, RevCircuit.comp, crossBitSwap, addShearR, BitVec.shiftLeft_zero, BitVec.add_zero]
      apply Prod.ext
      · simp [bitvec_and_one_of_odd hw1 b hb]
      · simp [odd_sub1_eq_and_not1 hw1 b hb]
    have hs2 : (circuitP w).toFun (1#w, b - 1#w) = (1#w, b) := by
      simp only [circuitP, RevCircuit.comp, crossBitSwap, addShearR, BitVec.shiftLeft_zero, BitVec.sub_add_cancel]
      apply Prod.ext
      · apply BitVec.eq_of_getLsbD_eq; intro k hk
        match k with
        | 0 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            h10, hb0, Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_or]
        | k + 1 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            bitvec1_getLsbD_pos (by omega : 0 < k + 1), Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.or_false]
      · apply BitVec.eq_of_getLsbD_eq; intro k hk
        match k with
        | 0 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            h10, hb0, Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_or]
        | k + 1 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            bitvec1_getLsbD_pos (by omega : 0 < k + 1), Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.or_false]
    have hs3 : (circuitP w).toFun (1#w, b) = (0#w, b + 2#w) := by
      have h1mod : (1#w).toNat % 2 = 1 := by
        have h2 : 2 ≤ 2 ^ w := calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw1
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
      have hbp1_ev : (b + 1#w).toNat % 2 = 0 := by rw [toNat_add_mod2 hw1]; omega
      have hbp1_0 : (b + 1#w).getLsbD 0 = false := by rw [getLsbD_zero_iff_mod2 hw1, hbp1_ev]; rfl
      have hbp1_and : (b + 1#w) &&& ~~~1#w = b + 1#w := by
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        match k with
        | 0 =>
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            h10, hbp1_0, Bool.not_true, Bool.and_false]
        | k + 1 =>
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            bitvec1_getLsbD_pos (by omega : 0 < k + 1), Bool.not_false, Bool.and_true]
      have hbp2 : (b + 1#w) + 1#w = b + 2#w := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      simp only [circuitP, RevCircuit.comp, crossBitSwap, addShearR, BitVec.shiftLeft_zero]
      apply Prod.ext
      · apply BitVec.eq_of_getLsbD_eq; intro k hk
        match k with
        | 0 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            h10, hbp1_0, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or,
            BitVec.getLsbD_zero]
        | k + 1 =>
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hk, decide_true,
            bitvec1_getLsbD_pos (by omega : 0 < k + 1), Bool.not_false,
            Bool.and_true, Bool.and_false, Bool.or_false, BitVec.getLsbD_zero]
      · rw [hbp1_and, BitVec.and_self, even_or1_eq_add1 hw1 (b + 1#w) hbp1_ev, hbp2]
    simp only [iter, hs1, hs2, hs3]
  have hdvd : 2 ∣ 2 ^ w := by rw [pow2_eq_two_mul_pred hw1]; exact Nat.dvd_mul_right 2 _
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, ih]
    have hb : (BitVec.ofNat w (2 * m + 1)).toNat % 2 = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd]; omega
    rw [hstep3 _ hb]
    apply Prod.ext
    · rfl
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      exact congrArg (· % 2 ^ w) (by omega)

/-- **THEOREM 2A (Exact Order of Bit-0 Cross-Swap Add-Shear `P = S_{0} ∘ A_R(0)`):**
    For ALL `w ≥ 2`, `P` has exact order `3 * 2 ^ (w - 1)`. -/
theorem theorem2_circuitP_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder (circuitP w) (3 * 2 ^ (w - 1)) := by
  by_cases hw2 : w = 2
  · subst hw2
    refine ⟨by decide, forall_state2 (by decide), ?_⟩
    intro d hd0 hdlt
    have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> exact ⟨(0#2, 1#2), by decide⟩
  · have hw3 : 3 ≤ w := by omega
    have hw1 : 1 ≤ w := by omega
    have h10 := bitvec1_getLsbD_0 hw1
    apply hasExactOrder_three_mul_pow2 (circuitP w) (w - 1) (by omega)
    · have haff2 := (circuitP_bitAffine w).weaken_base (r2 := 2) (Nat.zero_le 2)
      have hjac : ∀ k, 2 ≤ k → k < w →
          (GL2.mul (if (1#w).getLsbD k then GL2.J else GL2.I) GL2.L).pow 6 = GL2.I :=
        fun k _ _ => GL2.pow_six _
      have hb := bsasce_master_order_bound (r := 2) (D := 6) haff2 hw (circuitP_six_lowEq2 hw) hjac
      have hexp : 3 * 2 ^ (w - 1) = 6 * 2 ^ (w - 2) := by
        have hsub : w - 1 = (w - 2) + 1 := by omega
        rw [hsub, Nat.pow_succ]; omega
      rw [hexp]
      exact hb
    · refine ⟨(0#w, 1#w), ?_⟩
      have hsub2 : w - 1 - 1 = w - 2 := by omega
      rw [hsub2, circuitP_orbit_closed_form hw (2 ^ (w - 2))]
      intro heq
      have hb := congrArg (fun p => p.2.toNat) heq
      simp only [BitVec.toNat_ofNat] at hb
      have h2 : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
        have hsub : w - 1 = (w - 2) + 1 := by omega
        rw [hsub, Nat.pow_succ]; omega
      rw [h2] at hb
      have hlt1 : 2 ^ (w - 1) + 1 < 2 ^ w := by
        have hhalf := pow2_eq_two_mul_pred hw1
        have hpos : 4 ≤ 2 ^ (w - 1) := calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hlt2 : 1 < 2 ^ w := by omega
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hb
      have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by omega)
      omega
    · refine ⟨(0#w, 1#w), ?_⟩
      have hbit0 : ∀ n, slice 0 (iter (circuitP w).toFun n (0#w, 1#w)) =
          match n % 3 with | 0 => (false, true) | 1 => (true, false) | _ => (true, true) := by
        have hstep : ∀ x, slice 0 ((circuitP w).toFun x) = GL2.R1.act (slice 0 x) := by
          intro x
          have haff := circuitP_bitAffine w
          have h0 := haff.2 0 (Nat.le_refl 0) hw1 x (0#w, 0#w) (lowEq_zero _ _)
          have hp0 : (circuitP w).toFun (0#w, 0#w) = (0#w, 0#w) := by
            simp [circuitP, RevCircuit.comp, crossBitSwap, addShearR]
          have hz : slice 0 (0#w, 0#w) = (false, false) := by simp [slice]
          simpa [hp0, h10, hz, vecXor_zero_right, GL2.mul] using h0
        intro n
        induction n with
        | zero => simp [iter, slice, h10]
        | succ n ih =>
          rw [iter, hstep, ih]
          have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
          rcases hmod with h | h | h
          · have h' : (n + 1) % 3 = 1 := by omega
            rw [h, h']; rfl
          · have h' : (n + 1) % 3 = 2 := by omega
            rw [h, h']; rfl
          · have h' : (n + 1) % 3 = 0 := by omega
            rw [h, h']; rfl
      have hpow2_mod3 : ∀ k, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
        intro k
        induction k with
        | zero => left; rfl
        | succ k ih => rw [Nat.pow_succ]; rcases ih with h | h <;> omega
      intro heq
      have hs := congrArg (slice 0) heq
      rw [hbit0 (2 ^ (w - 1))] at hs
      have hinit : slice 0 (0#w, 1#w) = (false, true) := by simp [slice, h10]
      rw [hinit] at hs
      rcases hpow2_mod3 (w - 1) with h | h <;> simp [h] at hs

theorem circuitFm_bitAffine (w : Nat) (m : BitVec w) :
    IsBitAffine 0 (fun k => if m.getLsbD k then GL2.L else GL2.R1) (circuitFm w m).toFun := by
  have h1 := crossBitSwap_bitAffine w m
  have h2 := (addShearR_bitAffine w 0).comp (xorShearL_bitAffine w 0)
  have h3 := h1.comp h2
  refine ⟨h3.1, ?_⟩
  intro k hrk hkw x y hxy
  have hk := h3.2 k hrk hkw x y hxy
  cases hmk : m.getLsbD k <;> simpa [circuitFm, RevCircuit.comp, hmk, GL2.mul] using hk

/-- **THEOREM 2B (`2^w`-Class Pairwise Non-Conjugacy Separation in `A_w^(0)` `∀ w ≥ 1`):**
    Distinct bitmasks `m₁ ≠ m₂ : BitVec w` produce circuits `F_{m₁}, F_{m₂}` in pairwise
    distinct conjugacy classes of the entire bit-sliced affine group `A_w^(0)`. -/
theorem theorem2_circuitFm_pairwise_non_conjugate (w : Nat) (m1 m2 : BitVec w) (hne : m1 ≠ m2)
    (h : RevCircuit w) (Mh : Nat → GL2) (hh : IsBitAffine 0 Mh h.toFun) :
    ¬ (∀ x, (circuitFm w m2).toFun x = (h.conj (circuitFm w m1)).toFun x) := by
  intro hconj
  have hinv := bsasce_conjugacy_invariant (circuitFm w m1) (circuitFm w m2) h
    (circuitFm_bitAffine w m1) (circuitFm_bitAffine w m2) hh hconj
  apply hne
  apply BitVec.eq_of_getLsbD_eq
  intro k hkw
  have hord := hinv k (Nat.zero_le k) hkw
  cases hm1 : m1.getLsbD k <;> cases hm2 : m2.getLsbD k <;>
    simp [hm1, hm2, GL2.ord] at hord ⊢

/-! ### Theorem 3: Add-XOR Commutator Tower, Exact Wreath Subgroup Generation & LCS Sharpness -/

theorem xor1_of_lsb {w : Nat} (hw : 1 ≤ w) (b : BitVec w) :
    b ^^^ 1#w = if b.getLsbD 0 then b - 1#w else b + 1#w := by
  have h10 := bitvec1_getLsbD_0 hw
  cases hb0 : b.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false]
    have hc0 : ∀ j, BitVec.carry j b 1#w false = false := by
      intro j
      induction j with
      | zero => exact BitVec.carry_zero
      | succ j ih =>
        rw [BitVec.carry_succ, ih]
        cases j with
        | zero => simp [hb0]
        | succ j' => rw [bitvec1_getLsbD_pos (by omega : 0 < j' + 1)]; simp
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [BitVec.getLsbD_add hk, hc0 k]; simp
  · simp only [ite_true]
    have hx0 : (b ^^^ 1#w).getLsbD 0 = false := by simp [hb0, h10]
    have hc0 : ∀ j, BitVec.carry j (b ^^^ 1#w) 1#w false = false := by
      intro j
      induction j with
      | zero => exact BitVec.carry_zero
      | succ j ih =>
        rw [BitVec.carry_succ, ih]
        cases j with
        | zero => simp [hx0]
        | succ j' => rw [bitvec1_getLsbD_pos (by omega : 0 < j' + 1)]; simp
    have hadd : (b ^^^ 1#w) + 1#w = b := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      rw [BitVec.getLsbD_add hk, hc0 k]; simp
    exact (BitVec.add_sub_cancel (b ^^^ 1#w) 1#w).symm.trans (congrArg (· - 1#w) hadd)

/-- Exact order of `A_R(0) ∘ X_R(0)` is `2 ^ (w - 1)` for all `w ≥ 2`. -/
theorem theorem3_addXorShear_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder ((addShearR w 0).comp (xorShearR w 0)) (2 ^ (w - 1)) := by
  have hw1 : 1 ≤ w := by omega
  let F := (addShearR w 0).comp (xorShearR w 0)
  have haff : IsBitAffine 0 (fun _ => GL2.I) F.toFun := by
    have h := (addShearR_bitAffine w 0).comp (xorShearR_bitAffine w 0)
    simpa [F, RevCircuit.comp, GL2.mul] using h
  have hz : F.toFun (0#w, 0#w) = (0#w, 0#w) := by
    simp [F, RevCircuit.comp, addShearR, xorShearR]
  have hupper : ∀ x, iter F.toFun (2 ^ (w - 1)) x = x := by
    have h := bsasce_zero_preserving_bound (D := 1) haff hw1 hz (fun _ _ => rfl)
    simpa using h
  have horb : ∀ n, iter F.toFun n (1#w, 0#w) = (1#w, BitVec.ofNat w (2 * n)) := by
    have hdvd : 2 ∣ 2 ^ w := by rw [pow2_eq_two_mul_pred hw1]; exact Nat.dvd_mul_right 2 _
    have hstep : ∀ b : BitVec w, b.toNat % 2 = 0 → F.toFun (1#w, b) = (1#w, b + 2#w) := by
      intro b hb
      have hb0 : b.getLsbD 0 = false := by rw [getLsbD_zero_iff_mod2 hw1, hb]; rfl
      simp only [F, RevCircuit.comp, addShearR, xorShearR, BitVec.shiftLeft_zero]
      apply Prod.ext
      · rfl
      · rw [xor1_of_lsb hw1 b, hb0]
        simp only [Bool.false_eq_true, ite_false]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
    intro n
    induction n with
    | zero => simp [iter]
    | succ n ih =>
      rw [iter, ih, hstep]
      · apply Prod.ext
        · rfl
        · apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
          exact congrArg (· % 2 ^ w) (by omega)
      · rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hdvd]; omega
  apply hasExactOrder_pow2 F (w - 1) (by omega) hupper
  refine ⟨(1#w, 0#w), ?_⟩
  have hsub2 : w - 1 - 1 = w - 2 := by omega
  rw [hsub2, horb (2 ^ (w - 2))]
  intro heq
  have hb := congrArg (fun p => p.2.toNat) heq
  simp only [BitVec.toNat_ofNat] at hb
  have h2 : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
    have hsub : w - 1 = (w - 2) + 1 := by omega
    rw [hsub, Nat.pow_succ, Nat.mul_comm]
  rw [h2] at hb
  have hlt : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hlt] at hb
  have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by omega)
  have h0mod : 0 % 2 ^ w = 0 := Nat.zero_mod _
  rw [h0mod] at hb
  omega

/-- Parity-signed translation `signedShift d b = if b is odd then b - d else b + d`. -/
def signedShift {w : Nat} (d b : BitVec w) : BitVec w :=
  if b.getLsbD 0 then b - d else b + d

/-- Left-normed iterated commutator `C(word) = [...[[A_R(0), X_R(0)], g_1], ..., g_m]`
    where `false ↦ A_R(0)` and `true ↦ X_R(0)`. -/
def iteratedShearComm (w : Nat) : List Bool → RevCircuit w
  | [] => (addShearR w 0).comm (xorShearR w 0)
  | b :: rest => (iteratedShearComm w rest).comm (if b then xorShearR w 0 else addShearR w 0)

theorem add_even_lsb0 {w : Nat} (hw : 1 ≤ w) (b d : BitVec w) (hd : d.getLsbD 0 = false) :
    (b + d).getLsbD 0 = b.getLsbD 0 := by
  rw [BitVec.getLsbD_add hw, BitVec.carry_zero, hd]; simp

theorem sub_even_lsb0 {w : Nat} (hw : 1 ≤ w) (b d : BitVec w) (hd : d.getLsbD 0 = false) :
    (b - d).getLsbD 0 = b.getLsbD 0 := by
  have h := add_even_lsb0 hw (b - d) d hd
  rw [BitVec.sub_add_cancel] at h
  exact h.symm

theorem add1_lsb0 {w : Nat} (hw : 1 ≤ w) (b : BitVec w) :
    (b + 1#w).getLsbD 0 = !b.getLsbD 0 := by
  have h10 := bitvec1_getLsbD_0 hw
  rw [BitVec.getLsbD_add hw, BitVec.carry_zero, h10]; cases b.getLsbD 0 <;> rfl

theorem sub1_lsb0 {w : Nat} (hw : 1 ≤ w) (b : BitVec w) :
    (b - 1#w).getLsbD 0 = !b.getLsbD 0 := by
  have h := add1_lsb0 hw (b - 1#w)
  rw [BitVec.sub_add_cancel] at h
  cases h1 : (b - 1#w).getLsbD 0 <;> cases h2 : b.getLsbD 0 <;> simp_all

/-- **THEOREM 3A (Exact Iterated Commutator Tower Formula on Fiber `a = 1`, `∀ w ≥ 1`, `∀ word`):**
    Every left-normed commutator `[...[[A_R(0), X_R(0)], g_1], ..., g_m]` (`g_i ∈ {A_R(0), X_R(0)}`)
    acts on fiber `a = 1` as `b ↦ b + (-1)^b · 2^(m + 1)`. -/
theorem theorem3_iteratedComm_fiber1 {w : Nat} (hw : 1 ≤ w) (word : List Bool) :
    (∀ b : BitVec w, (iteratedShearComm w word).toFun (1#w, b) =
      (1#w, signedShift (BitVec.ofNat w (2 ^ (word.length + 1))) b)) ∧
    (∀ b : BitVec w, (iteratedShearComm w word).invFun (1#w, b) =
      (1#w, signedShift (0#w - BitVec.ofNat w (2 ^ (word.length + 1))) b)) := by
  have heven_pow : ∀ k, 1 ≤ k → (BitVec.ofNat w (2 ^ k)).getLsbD 0 = false := by
    intro k hk
    rw [BitVec.getLsbD_ofNat]
    have h0w : 0 < w := by omega
    simp only [h0w, decide_true, Bool.true_and, Nat.testBit_zero]
    cases k with
    | zero => omega
    | succ k' => rw [Nat.pow_succ]; simp
  have hneg_even : ∀ d : BitVec w, d.getLsbD 0 = false → (0#w - d).getLsbD 0 = false := by
    intro d hd
    have := sub_even_lsb0 hw 0#w d hd
    simpa using this
  have hsub_neg : ∀ (x d : BitVec w), x - (0#w - d) = x + d := by
    intro x d
    have h1 : (x + d) + (0#w - d) = x := by
      rw [BitVec.add_assoc, BitVec.add_comm d, BitVec.sub_add_cancel, BitVec.add_zero]
    have h2 := congrArg (fun z => z - (0#w - d)) h1
    rw [BitVec.add_sub_cancel] at h2
    exact h2.symm
  have hadd_neg : ∀ (x d : BitVec w), x + (0#w - d) = x - d := by
    intro x d
    have h1 : (x + (0#w - d)) + d = x := by
      rw [BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.add_zero]
    have h2 := congrArg (fun z => z - d) h1
    rw [BitVec.add_sub_cancel] at h2
    exact h2
  have hsigned_inv : ∀ (d b : BitVec w), d.getLsbD 0 = false →
      signedShift d (signedShift (0#w - d) b) = b := by
    intro d b hd
    have hnd := hneg_even d hd
    unfold signedShift
    by_cases hb0 : b.getLsbD 0 = true
    · have hlsb : (b - (0#w - d)).getLsbD 0 = true := by rw [sub_even_lsb0 hw b _ hnd, hb0]
      simp only [hb0, ite_true, hlsb]
      rw [hsub_neg, BitVec.add_sub_cancel]
    · have hb0f : b.getLsbD 0 = false := by cases h : b.getLsbD 0 <;> simp_all
      have hlsb : (b + (0#w - d)).getLsbD 0 = false := by rw [add_even_lsb0 hw b _ hnd, hb0f]
      simp only [hb0f, hlsb, Bool.false_eq_true, ite_false]
      rw [BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.add_zero]
  have hcomm_sub1 : ∀ (b d : BitVec w), b - 1#w - d + 1#w = b - d := by
    intro b d
    have h1 : (b - 1#w - d + 1#w) + d = b := by
      rw [BitVec.add_comm _ 1#w, BitVec.add_assoc, BitVec.sub_add_cancel,
        BitVec.add_comm 1#w, BitVec.sub_add_cancel]
    have := congrArg (fun z => z - d) h1
    simp [BitVec.add_sub_cancel] at this
    exact this
  have hsub_sub : ∀ (b d : BitVec w), b - d - d = b - (d + d) := by
    intro b d
    have h1 : (b - d - d) + (d + d) = b := by
      rw [← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_add_cancel]
    have := congrArg (fun z => z - (d + d)) h1
    simp [BitVec.add_sub_cancel] at this
    exact this
  induction word with
  | nil =>
    have hbase_to : ∀ b : BitVec w, ((addShearR w 0).comm (xorShearR w 0)).toFun (1#w, b) =
        (1#w, signedShift (BitVec.ofNat w 2) b) := by
      intro b
      simp only [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, addShearR, xorShearR,
        BitVec.shiftLeft_zero, signedShift]
      apply Prod.ext
      · rfl
      · rw [xor1_of_lsb hw b]
        cases hb0 : b.getLsbD 0
        · simp only [Bool.false_eq_true, ite_false]
          rw [BitVec.add_sub_cancel, xor1_of_lsb hw b, hb0]
          simp only [Bool.false_eq_true, ite_false]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
        · simp only [ite_true]
          have hlsb : (b - 1#w - 1#w).getLsbD 0 = true := by
            rw [sub1_lsb0 hw, sub1_lsb0 hw, hb0]; rfl
          rw [xor1_of_lsb hw (b - 1#w - 1#w), hlsb]
          simp only [ite_true, BitVec.sub_add_cancel]
          have h2 : (2#w : BitVec w) = 1#w + 1#w := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
          have hadd2 : (b - 1#w - 1#w) + 2#w = b := by
            rw [h2, ← BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.sub_add_cancel]
          have := congrArg (fun z => z - 2#w) hadd2
          simp [BitVec.add_sub_cancel] at this
          exact this
    have hbase_inv : ∀ b : BitVec w, ((addShearR w 0).comm (xorShearR w 0)).invFun (1#w, b) =
        (1#w, signedShift (0#w - BitVec.ofNat w 2) b) := by
      intro b
      let C := (addShearR w 0).comm (xorShearR w 0)
      have h1 : C.toFun (1#w, signedShift (0#w - BitVec.ofNat w 2) b) = (1#w, b) := by
        rw [hbase_to, hsigned_inv _ b (heven_pow 1 (Nat.le_refl 1))]
      have := congrArg C.invFun h1
      simpa [C.left_inv] using this.symm
    exact ⟨hbase_to, hbase_inv⟩
  | cons g rest ih =>
    rcases ih with ⟨ih_to, ih_inv⟩
    let d : BitVec w := BitVec.ofNat w (2 ^ (rest.length + 1))
    have hd_ev : d.getLsbD 0 = false := heven_pow (rest.length + 1) (by omega)
    have hnd_ev : (0#w - d).getLsbD 0 = false := hneg_even d hd_ev
    have h2d : BitVec.ofNat w (2 ^ ((g :: rest).length + 1)) = d + d := by
      apply BitVec.eq_of_toNat_eq
      simp only [List.length_cons, d, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      congr 1; rw [Nat.pow_succ]; omega
    have hstep_to : ∀ b : BitVec w, (iteratedShearComm w (g :: rest)).toFun (1#w, b) =
        (1#w, signedShift (d + d) b) := by
      intro b
      cases g
      · simp only [iteratedShearComm, Bool.false_eq_true, ite_false, RevCircuit.comm, RevCircuit.comp,
          RevCircuit.inv, addShearR, BitVec.shiftLeft_zero]
        rw [ih_inv, ih_to]
        apply Prod.ext
        · rfl
        · change signedShift d (signedShift (0#w - d) (b - 1#w) + 1#w) = signedShift (d + d) b
          unfold signedShift
          by_cases hb0 : b.getLsbD 0 = true
          · have hbm1 : (b - 1#w).getLsbD 0 = false := by rw [sub1_lsb0 hw, hb0]; rfl
            simp only [hb0, ite_true, hbm1, Bool.false_eq_true, ite_false]
            rw [hadd_neg, hcomm_sub1]
            have hbd : (b - d).getLsbD 0 = true := by rw [sub_even_lsb0 hw b d hd_ev, hb0]
            simp only [hbd, ite_true]
            exact hsub_sub b d
          · have hb0f : b.getLsbD 0 = false := by cases h : b.getLsbD 0 <;> simp_all
            have hbm1 : (b - 1#w).getLsbD 0 = true := by rw [sub1_lsb0 hw, hb0f]; rfl
            simp only [hb0f, Bool.false_eq_true, ite_false, hbm1, ite_true]
            rw [hsub_neg]
            have hadd_b : b - 1#w + d + 1#w = b + d := by
              rw [BitVec.add_comm (b - 1#w) d, BitVec.add_assoc, BitVec.sub_add_cancel, BitVec.add_comm]
            rw [hadd_b]
            have hbd : (b + d).getLsbD 0 = false := by rw [add_even_lsb0 hw b d hd_ev, hb0f]
            simp only [hbd, Bool.false_eq_true, ite_false]
            exact BitVec.add_assoc b d d
      · simp only [iteratedShearComm, ite_true, RevCircuit.comm, RevCircuit.comp, RevCircuit.inv,
          xorShearR, BitVec.shiftLeft_zero]
        rw [ih_inv, ih_to]
        apply Prod.ext
        · rfl
        · change signedShift d (signedShift (0#w - d) (b ^^^ 1#w) ^^^ 1#w) = signedShift (d + d) b
          have h10 := bitvec1_getLsbD_0 hw
          unfold signedShift
          by_cases hb0 : b.getLsbD 0 = true
          · have hbx : (b ^^^ 1#w).getLsbD 0 = false := by simp [hb0, h10]
            simp only [hb0, ite_true, hbx, Bool.false_eq_true, ite_false]
            rw [hadd_neg, xor1_of_lsb hw b]
            simp only [hb0, ite_true]
            have hmid : (b - 1#w - d).getLsbD 0 = false := by
              rw [sub_even_lsb0 hw _ d hd_ev, sub1_lsb0 hw, hb0]; rfl
            rw [xor1_of_lsb hw (b - 1#w - d), hmid]
            simp only [Bool.false_eq_true, ite_false]
            rw [hcomm_sub1]
            have hbd : (b - d).getLsbD 0 = true := by rw [sub_even_lsb0 hw b d hd_ev, hb0]
            simp only [hbd, ite_true]
            exact hsub_sub b d
          · have hb0f : b.getLsbD 0 = false := by cases h : b.getLsbD 0 <;> simp_all
            have hbx : (b ^^^ 1#w).getLsbD 0 = true := by simp [hb0f, h10]
            simp only [hb0f, Bool.false_eq_true, ite_false, hbx, ite_true]
            rw [hsub_neg, xor1_of_lsb hw b]
            simp only [hb0f, Bool.false_eq_true, ite_false]
            have hmid : (b + 1#w + d).getLsbD 0 = true := by
              rw [add_even_lsb0 hw _ d hd_ev, add1_lsb0 hw, hb0f]; rfl
            rw [xor1_of_lsb hw (b + 1#w + d)]
            simp only [hmid, ite_true]
            have hadd_b : b + 1#w + d - 1#w = b + d := by
              rw [BitVec.add_comm (b + 1#w) d, ← BitVec.add_assoc, BitVec.add_sub_cancel, BitVec.add_comm]
            rw [hadd_b]
            have hbd : (b + d).getLsbD 0 = false := by rw [add_even_lsb0 hw b d hd_ev, hb0f]
            simp only [hbd, Bool.false_eq_true, ite_false]
            exact BitVec.add_assoc b d d
    refine ⟨fun b => by rw [h2d]; exact hstep_to b, ?_⟩
    intro b
    let C := iteratedShearComm w (g :: rest)
    have hd2_ev : (d + d).getLsbD 0 = false := by rw [add_even_lsb0 hw _ _ hd_ev, hd_ev]
    have h1 : C.toFun (1#w, signedShift (0#w - (d + d)) b) = (1#w, b) := by
      rw [hstep_to, hsigned_inv (d + d) b hd2_ev]
    have := congrArg C.invFun h1
    rw [h2d]
    simpa [C.left_inv] using this.symm

/-- **THEOREM 3B (Exact Order of First Commutator `[A_R(0), X_R(0)]` is `2^(w-1)` `∀ w ≥ 2`):** -/
theorem theorem3_addXorComm_exact_order (w : Nat) (hw : 2 ≤ w) :
    HasExactOrder ((addShearR w 0).comm (xorShearR w 0)) (2 ^ (w - 1)) := by
  have hw1 : 1 ≤ w := by omega
  let C := (addShearR w 0).comm (xorShearR w 0)
  have haff : IsBitAffine 0 (fun _ => GL2.I) C.toFun := by
    have h := (addShearR_bitAffine w 0).comm (addShearR w 0) (xorShearR w 0) (xorShearR_bitAffine w 0)
    simpa [C, GL2.comm_eq_I_of_eq] using h
  have hz : C.toFun (0#w, 0#w) = (0#w, 0#w) := by
    simp [C, RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, addShearR, xorShearR]
  have hupper : ∀ x, iter C.toFun (2 ^ (w - 1)) x = x := by
    have h := bsasce_zero_preserving_bound (D := 1) haff hw1 hz (fun _ _ => rfl)
    simpa using h
  have hstep : ∀ b : BitVec w, C.toFun (1#w, b) = (1#w, signedShift (BitVec.ofNat w 2) b) :=
    (theorem3_iteratedComm_fiber1 hw1 []).1
  have horb : ∀ n, iter C.toFun n (1#w, 0#w) = (1#w, BitVec.ofNat w (2 * n)) := by
    intro n
    induction n with
    | zero => simp [iter]
    | succ n ih =>
      rw [iter, ih, hstep]
      apply Prod.ext
      · rfl
      · have hev : (BitVec.ofNat w (2 * n)).getLsbD 0 = false := by
          rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_zero]
        simp only [signedShift, hev, Bool.false_eq_true, ite_false]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
        exact congrArg (· % 2 ^ w) (by omega)
  apply hasExactOrder_pow2 C (w - 1) (by omega) hupper
  refine ⟨(1#w, 0#w), ?_⟩
  have hsub2 : w - 1 - 1 = w - 2 := by omega
  rw [hsub2, horb (2 ^ (w - 2))]
  intro heq
  have hb := congrArg (fun p => p.2.toNat) heq
  simp only [BitVec.toNat_ofNat] at hb
  have h2 : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
    have hsub : w - 1 = (w - 2) + 1 := by omega
    rw [hsub, Nat.pow_succ, Nat.mul_comm]
  rw [h2] at hb
  have hlt : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt hlt] at hb
  have hpos : 0 < 2 ^ (w - 1) := Nat.pow_pos (by omega)
  have h0mod : 0 % 2 ^ w = 0 := Nat.zero_mod _
  rw [h0mod] at hb
  omega

theorem theorem3_fiber1_wreath_normal_form {w : Nat} (hw : 2 ≤ w) :
    (∀ f, InFiber1Group w f → ∃ ε u v, ∀ b, f b = wreathElem ε u v b) ∧
    (∀ ε u v, InFiber1Group w (wreathElem ε u v)) ∧
    (∀ (ε1 : Bool) (u1 v1 : BitVec (w - 1)) (ε2 : Bool) (u2 v2 : BitVec (w - 1)),
      (∀ b : BitVec w, wreathElem ε1 u1 v1 b = wreathElem ε2 u2 v2 b) →
      ε1 = ε2 ∧ u1 = u2 ∧ v1 = v2) := by
  have hw1 : 1 ≤ w := by omega
  have h10 := bitvec1_getLsbD_0 hw1
  have h2pow := pow2_eq_two_mul_pred hw1
  have h2ev : ∀ k : Nat, (BitVec.ofNat w (2 * k)).getLsbD 0 = false := by
    intro k; rw [BitVec.getLsbD_ofNat]; simp [Nat.testBit_zero]
  have h2add : ∀ a b : BitVec (w - 1),
      BitVec.ofNat w (2 * a.toNat) + BitVec.ofNat w (2 * b.toNat) =
        BitVec.ofNat w (2 * (a + b).toNat) := by
    intro a b
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
    have hmul : 2 * ((a.toNat + b.toNat) % 2 ^ (w - 1)) = (2 * (a.toNat + b.toNat)) % (2 * 2 ^ (w - 1)) := by
      rw [Nat.mul_mod_mul_left]
    rw [h2pow, hmul, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
    congr 1; omega
  have hgen_add : ∀ b : BitVec w, fiber1Add1 w b = wreathElem true 0#(w - 1) 1#(w - 1) b := by
    intro b
    have h1nat : (1#(w - 1)).toNat = 1 := by
      have hpos : 2 ≤ 2 ^ (w - 1) := calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (w - 1))]
    simp only [fiber1Add1, wreathElem, ite_true, BitVec.toNat_zero, h1nat]
    cases hb0 : b.getLsbD 0
    · simp only [Bool.false_eq_true, ite_false, Nat.mul_zero]
      have hzero_eq : BitVec.ofNat w 0 = 0#w := rfl
      rw [hzero_eq, BitVec.add_zero, xor1_of_lsb hw1 b, hb0]; rfl
    · simp only [ite_true, Nat.mul_one]
      have hb2 : (b + 2#w).getLsbD 0 = true := by rw [add_even_lsb0 hw1 b 2#w (h2ev 1), hb0]
      rw [xor1_of_lsb hw1 (b + 2#w), hb2]
      simp only [ite_true]
      have h2 : (2#w : BitVec w) = 1#w + 1#w := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
      rw [h2, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  have hgen_xor : ∀ b : BitVec w, fiber1Xor1 w b = wreathElem true 0#(w - 1) 0#(w - 1) b := by
    intro b; simp [fiber1Xor1, wreathElem]
  have hcomp_wreath : ∀ (ε1 : Bool) (u1 v1 : BitVec (w - 1)) (ε2 : Bool) (u2 v2 : BitVec (w - 1)),
      ∀ b : BitVec w, wreathElem ε1 u1 v1 (wreathElem ε2 u2 v2 b) =
        wreathElem (ε1 ^^ ε2) (u2 + (if ε2 then v1 else u1)) (v2 + (if ε2 then u1 else v1)) b := by
    intro ε1 u1 v1 ε2 u2 v2 b
    have hxor1_add_even : ∀ (x : BitVec w) (k : Nat),
        (x ^^^ 1#w) + BitVec.ofNat w (2 * k) = (x + BitVec.ofNat w (2 * k)) ^^^ 1#w := by
      intro x k
      have hk := h2ev k
      rw [xor1_of_lsb hw1 x, xor1_of_lsb hw1 (x + BitVec.ofNat w (2 * k)), add_even_lsb0 hw1 x _ hk]
      cases hx0 : x.getLsbD 0
      · simp only [Bool.false_eq_true, ite_false]
        rw [BitVec.add_assoc, BitVec.add_comm 1#w, ← BitVec.add_assoc]
      · simp only [ite_true]
        have h1 : (x - 1#w + BitVec.ofNat w (2 * k)) + 1#w = x + BitVec.ofNat w (2 * k) := by
          rw [BitVec.add_assoc, BitVec.add_comm _ 1#w, ← BitVec.add_assoc, BitVec.sub_add_cancel]
        have := congrArg (fun z => z - 1#w) h1
        simpa [BitVec.add_sub_cancel] using this
    cases ε2 <;> cases ε1 <;> cases hb0 : b.getLsbD 0
    · simp only [wreathElem, Bool.false_eq_true, ite_false, hb0, add_even_lsb0 hw1 b _ (h2ev _),
        Bool.xor_false, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, add_even_lsb0 hw1 b _ (h2ev _),
        Bool.xor_false, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, add_even_lsb0 hw1 b _ (h2ev _),
        Bool.true_xor, Bool.not_false, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, add_even_lsb0 hw1 b _ (h2ev _),
        Bool.true_xor, Bool.not_false, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, BitVec.getLsbD_xor,
        add_even_lsb0 hw1 b _ (h2ev _), h10, Bool.xor_true, Bool.not_false]
      rw [hxor1_add_even, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, BitVec.getLsbD_xor,
        add_even_lsb0 hw1 b _ (h2ev _), h10, Bool.xor_true, Bool.not_true, Bool.not_false]
      rw [hxor1_add_even, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, BitVec.getLsbD_xor,
        add_even_lsb0 hw1 b _ (h2ev _), h10, Bool.false_xor, Bool.xor_self]
      rw [hxor1_add_even, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.add_assoc, h2add]
    · simp only [wreathElem, Bool.false_eq_true, ite_false, ite_true, hb0, BitVec.getLsbD_xor,
        add_even_lsb0 hw1 b _ (h2ev _), h10, Bool.xor_self]
      rw [hxor1_add_even, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.add_assoc, h2add]
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    induction hf with
    | id => exact ⟨false, 0#(w - 1), 0#(w - 1), fun b => by simp [wreathElem]⟩
    | genAdd => exact ⟨true, 0#(w - 1), 1#(w - 1), hgen_add⟩
    | genXor => exact ⟨true, 0#(w - 1), 0#(w - 1), hgen_xor⟩
    | comp _ _ ih1 ih2 =>
      rcases ih1 with ⟨ε1, u1, v1, h1⟩
      rcases ih2 with ⟨ε2, u2, v2, h2⟩
      exact ⟨ε1 ^^ ε2, u2 + (if ε2 then v1 else u1), v2 + (if ε2 then u1 else v1),
        fun b => by dsimp only; rw [h1, h2, hcomp_wreath]⟩
  · have hAX : InFiber1Group w (wreathElem false 1#(w - 1) 0#(w - 1)) := by
      have hc := InFiber1Group.comp (InFiber1Group.genAdd (w := w)) (InFiber1Group.genXor (w := w))
      have heq : (fun b => fiber1Add1 w (fiber1Xor1 w b)) = wreathElem false 1#(w - 1) 0#(w - 1) := by
        funext b; rw [hgen_add, hgen_xor, hcomp_wreath]; simp
      rwa [heq] at hc
    have hXA : InFiber1Group w (wreathElem false 0#(w - 1) 1#(w - 1)) := by
      have hc := InFiber1Group.comp (InFiber1Group.genXor (w := w)) (InFiber1Group.genAdd (w := w))
      have heq : (fun b => fiber1Xor1 w (fiber1Add1 w b)) = wreathElem false 0#(w - 1) 1#(w - 1) := by
        funext b; rw [hgen_xor, hgen_add, hcomp_wreath]; simp
      rwa [heq] at hc
    have hpow_u : ∀ n : Nat, InFiber1Group w (wreathElem false (BitVec.ofNat (w - 1) n) 0#(w - 1)) := by
      intro n
      induction n with
      | zero =>
        have heq : (fun b : BitVec w => b) = wreathElem false 0#(w - 1) 0#(w - 1) := by
          funext b; simp [wreathElem]
        simpa [← heq] using InFiber1Group.id (w := w)
      | succ n ih =>
        have hc := InFiber1Group.comp hAX ih
        have heq : (fun b => wreathElem false 1#(w - 1) 0#(w - 1)
            (wreathElem false (BitVec.ofNat (w - 1) n) 0#(w - 1) b)) =
            wreathElem false (BitVec.ofNat (w - 1) (n + 1)) 0#(w - 1) := by
          funext b; rw [hcomp_wreath]
          have hadd1 : BitVec.ofNat (w - 1) n + 1#(w - 1) = BitVec.ofNat (w - 1) (n + 1) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
          simp [hadd1]
        rwa [heq] at hc
    have hpow_v : ∀ n : Nat, InFiber1Group w (wreathElem false 0#(w - 1) (BitVec.ofNat (w - 1) n)) := by
      intro n
      induction n with
      | zero =>
        have heq : (fun b : BitVec w => b) = wreathElem false 0#(w - 1) 0#(w - 1) := by
          funext b; simp [wreathElem]
        simpa [← heq] using InFiber1Group.id (w := w)
      | succ n ih =>
        have hc := InFiber1Group.comp hXA ih
        have heq : (fun b => wreathElem false 0#(w - 1) 1#(w - 1)
            (wreathElem false 0#(w - 1) (BitVec.ofNat (w - 1) n) b)) =
            wreathElem false 0#(w - 1) (BitVec.ofNat (w - 1) (n + 1)) := by
          funext b; rw [hcomp_wreath]
          have hadd1 : BitVec.ofNat (w - 1) n + 1#(w - 1) = BitVec.ofNat (w - 1) (n + 1) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod]
          simp [hadd1]
        rwa [heq] at hc
    intro ε u v
    have hbase : InFiber1Group w (wreathElem false u v) := by
      have hc := InFiber1Group.comp (hpow_u u.toNat) (hpow_v v.toNat)
      have heq : (fun b => wreathElem false (BitVec.ofNat (w - 1) u.toNat) 0#(w - 1)
          (wreathElem false 0#(w - 1) (BitVec.ofNat (w - 1) v.toNat) b)) =
          wreathElem false u v := by
        funext b; rw [hcomp_wreath]; simp [BitVec.ofNat_toNat]
      rwa [heq] at hc
    cases ε
    · exact hbase
    · have hc := InFiber1Group.comp (InFiber1Group.genXor (w := w)) hbase
      have heq : (fun b => fiber1Xor1 w (wreathElem false u v b)) = wreathElem true u v := by
        funext b; rw [hgen_xor, hcomp_wreath]; simp
      rwa [heq] at hc
  · intro ε1 u1 v1 ε2 u2 v2 heq
    have h0 := heq 0#w
    have h1 := heq 1#w
    have hε : ε1 = ε2 := by
      have hlsb := congrArg (fun z => z.getLsbD 0) h0
      cases ε1 <;> cases ε2 <;> simp [wreathElem, h2ev, h10] at hlsb ⊢
    subst hε
    have hu : u1 = u2 := by
      have h0' : BitVec.ofNat w (2 * u1.toNat) = BitVec.ofNat w (2 * u2.toNat) := by
        cases ε1
        · simpa [wreathElem] using h0
        · have h' := congrArg (fun z => z ^^^ 1#w) h0
          simpa [wreathElem, BitVec.xor_assoc] using h'
      have hnat := congrArg BitVec.toNat h0'
      simp only [BitVec.toNat_ofNat] at hnat
      have hu1lt : 2 * u1.toNat < 2 ^ w := by have := u1.isLt; omega
      have hu2lt : 2 * u2.toNat < 2 ^ w := by have := u2.isLt; omega
      rw [Nat.mod_eq_of_lt hu1lt, Nat.mod_eq_of_lt hu2lt] at hnat
      exact BitVec.eq_of_toNat_eq (by omega)
    have hv : v1 = v2 := by
      have h1' : 1#w + BitVec.ofNat w (2 * v1.toNat) = 1#w + BitVec.ofNat w (2 * v2.toNat) := by
        cases ε1
        · simpa [wreathElem, h10] using h1
        · have h' := congrArg (fun z => z ^^^ 1#w) h1
          simpa [wreathElem, h10, BitVec.xor_assoc] using h'
      have h1'' : BitVec.ofNat w (2 * v1.toNat) = BitVec.ofNat w (2 * v2.toNat) := by
        have := congrArg (fun z => z - 1#w) h1'
        simpa [BitVec.add_comm 1#w, BitVec.add_sub_cancel] using this
      have hnat := congrArg BitVec.toNat h1''
      simp only [BitVec.toNat_ofNat] at hnat
      have hv1lt : 2 * v1.toNat < 2 ^ w := by have := v1.isLt; omega
      have hv2lt : 2 * v2.toNat < 2 ^ w := by have := v2.isLt; omega
      rw [Nat.mod_eq_of_lt hv1lt, Nat.mod_eq_of_lt hv2lt] at hnat
      exact BitVec.eq_of_toNat_eq (by omega)
    exact ⟨rfl, hu, hv⟩

/-- **SHARPNESS COUNTEREXAMPLE (LCS vs Derived Series at `w = 4`, fiber `a = 3`):**
    While the fiber-1 group `H_4` has nilpotency class `4` (and the derived series of `A_4^(0)`
    collapses at depth `5`), the 2-lane length-5 left-normed commutator `[[[[A, X], A], A], A]`
    is NON-IDENTITY on fiber `a = 3` at `w = 4`: it maps `(3, 0) ↦ (3, 8) ≠ (3, 0)`. -/
theorem sharpness_lcs_exceeds_w_at_w4 :
    (iteratedShearComm 4 [false, false, false]).toFun (3#4, 0#4) ≠ (3#4, 0#4) := by
  decide

theorem circuitH_bitAffine2 (w : Nat) (hw : 2 ≤ w) :
    IsBitAffine 2 (fun _ => GL2.R1) (circuitH w hw).toFun := by
  have h1 := intraBitSwap01_bitAffine w hw
  have h2 := ((addShearR_bitAffine w 0).comp (xorShearL_bitAffine w 0)).weaken_base (r2 := 2) (Nat.zero_le 2)
  have h3 := h1.comp h2
  refine ⟨h3.1, ?_⟩
  intro k hrk hkw x y hxy
  simpa [circuitH, RevCircuit.comp, GL2.mul] using h3.2 k hrk hkw x y hxy

/-- Truncation compatibility of `circuitH` onto the finite 2-bit base block `(BitVec 2)^2`. -/
theorem circuitH_trunc2_step {w : Nat} (hw : 2 ≤ w) (x : State w) :
    (((circuitH w hw).toFun x).1.setWidth 2, ((circuitH w hw).toFun x).2.setWidth 2) =
      (circuitH 2 (Nat.le_refl 2)).toFun (x.1.setWidth 2, x.2.setWidth 2) := by
  have hswap2 : ∀ z : BitVec w, (swap01 z).setWidth 2 = swap01 (z.setWidth 2) := by
    intro z
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    match i with
    | 0 =>
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
        swap01_getLsbD_0 hw, swap01_getLsbD_0 (Nat.le_refl 2),
        BitVec.getLsbD_setWidth, decide_eq_true (by omega : 1 < 2), Bool.true_and]
    | 1 =>
      rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and,
        swap01_getLsbD_1 hw, swap01_getLsbD_1 (Nat.le_refl 2),
        BitVec.getLsbD_setWidth, decide_eq_true (by omega : 0 < 2), Bool.true_and]
  rcases x with ⟨a, b⟩
  simp only [circuitH, RevCircuit.comp, intraBitSwap01, addShearR, xorShearL, BitVec.shiftLeft_zero]
  rw [hswap2, hswap2, setWidth2_add hw, setWidth2_xor]

theorem circuitH_trunc2_iter {w : Nat} (hw : 2 ≤ w) (n : Nat) (x : State w) :
    ((iter (circuitH w hw).toFun n x).1.setWidth 2, (iter (circuitH w hw).toFun n x).2.setWidth 2) =
      iter (circuitH 2 (Nat.le_refl 2)).toFun n (x.1.setWidth 2, x.2.setWidth 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter]
    rw [circuitH_trunc2_step, ih]

/-- Explicit 16-state transition table for `circuitH 2` on `Fin 4 × Fin 4` (for fast kernel verification). -/
def h2Tab : Fin 4 × Fin 4 → Fin 4 × Fin 4
  | (⟨0, _⟩, ⟨0, _⟩) => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | (⟨0, _⟩, ⟨1, _⟩) => (⟨2, by decide⟩, ⟨1, by decide⟩)
  | (⟨0, _⟩, ⟨2, _⟩) => (⟨1, by decide⟩, ⟨0, by decide⟩)
  | (⟨0, _⟩, ⟨3, _⟩) => (⟨3, by decide⟩, ⟨1, by decide⟩)
  | (⟨1, _⟩, ⟨0, _⟩) => (⟨2, by decide⟩, ⟨2, by decide⟩)
  | (⟨1, _⟩, ⟨1, _⟩) => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | (⟨1, _⟩, ⟨2, _⟩) => (⟨3, by decide⟩, ⟨2, by decide⟩)
  | (⟨1, _⟩, ⟨3, _⟩) => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | (⟨2, _⟩, ⟨0, _⟩) => (⟨1, by decide⟩, ⟨1, by decide⟩)
  | (⟨2, _⟩, ⟨1, _⟩) => (⟨3, by decide⟩, ⟨0, by decide⟩)
  | (⟨2, _⟩, ⟨2, _⟩) => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | (⟨2, _⟩, ⟨3, _⟩) => (⟨2, by decide⟩, ⟨0, by decide⟩)
  | (⟨3, _⟩, ⟨0, _⟩) => (⟨3, by decide⟩, ⟨3, by decide⟩)
  | (⟨3, _⟩, ⟨1, _⟩) => (⟨1, by decide⟩, ⟨3, by decide⟩)
  | (⟨3, _⟩, ⟨2, _⟩) => (⟨2, by decide⟩, ⟨3, by decide⟩)
  | (⟨3, _⟩, ⟨3, _⟩) => (⟨0, by decide⟩, ⟨3, by decide⟩)

def decState2 (y : State 2) : Fin 4 × Fin 4 := (⟨y.1.toNat, y.1.isLt⟩, ⟨y.2.toNat, y.2.isLt⟩)
def encState2 (p : Fin 4 × Fin 4) : State 2 := (BitVec.ofNat 2 p.1.val, BitVec.ofNat 2 p.2.val)

theorem enc_dec_state2 (y : State 2) : encState2 (decState2 y) = y := by
  rcases y with ⟨a, b⟩
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq <;> simp [encState2, decState2]

theorem dec_enc_state2 (p : Fin 4 × Fin 4) : decState2 (encState2 p) = p := by
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  simp [decState2, encState2, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem circuitH2_eq_h2Tab (y : State 2) :
    decState2 ((circuitH 2 (Nat.le_refl 2)).toFun y) = h2Tab (decState2 y) := by
  rw [← enc_dec_state2 y, dec_enc_state2]
  generalize decState2 y = p
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  match a, b with
  | 0, 0 => dsimp only [encState2, decState2, h2Tab]; decide
  | 0, 1 => dsimp only [encState2, decState2, h2Tab]; decide
  | 0, 2 => dsimp only [encState2, decState2, h2Tab]; decide
  | 0, 3 => dsimp only [encState2, decState2, h2Tab]; decide
  | 1, 0 => dsimp only [encState2, decState2, h2Tab]; decide
  | 1, 1 => dsimp only [encState2, decState2, h2Tab]; decide
  | 1, 2 => dsimp only [encState2, decState2, h2Tab]; decide
  | 1, 3 => dsimp only [encState2, decState2, h2Tab]; decide
  | 2, 0 => dsimp only [encState2, decState2, h2Tab]; decide
  | 2, 1 => dsimp only [encState2, decState2, h2Tab]; decide
  | 2, 2 => dsimp only [encState2, decState2, h2Tab]; decide
  | 2, 3 => dsimp only [encState2, decState2, h2Tab]; decide
  | 3, 0 => dsimp only [encState2, decState2, h2Tab]; decide
  | 3, 1 => dsimp only [encState2, decState2, h2Tab]; decide
  | 3, 2 => dsimp only [encState2, decState2, h2Tab]; decide
  | 3, 3 => dsimp only [encState2, decState2, h2Tab]; decide

theorem circuitH2_iter_eq_h2Tab (n : Nat) (y : State 2) :
    decState2 (iter (circuitH 2 (Nat.le_refl 2)).toFun n y) = iter h2Tab n (decState2 y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, circuitH2_eq_h2Tab, ih]

/-- Finite base-block certificate: `circuitH 2` has period 15 on all 16 states of `(BitVec 2)^2`. -/
theorem circuitH2_period15 : ∀ y : State 2, iter (circuitH 2 (Nat.le_refl 2)).toFun 15 y = y := by
  have htab15 : ∀ a b : Fin 4, iter h2Tab 15 (a, b) = (a, b) := by decide
  intro y
  have h1 := circuitH2_iter_eq_h2Tab 15 y
  have h2 : iter h2Tab 15 (decState2 y) = decState2 y := htab15 (decState2 y).1 (decState2 y).2
  rw [h2] at h1
  have h3 := congrArg encState2 h1
  simpa [enc_dec_state2] using h3

/-- **THEOREM 4A (Block-2 Infinite Order Bound via `BSAS-CE`):**
    For ALL `w ≥ 2`, `H^(15 * 2^(w - 2)) = id` on `(BitVec w)^2`. -/
theorem theorem4_circuitH_order_bound (w : Nat) (hw : 2 ≤ w) :
    ∀ x, iter (circuitH w hw).toFun (15 * 2 ^ (w - 2)) x = x := by
  have hlow15 : ∀ x : State w, LowEq 2 (iter (circuitH w hw).toFun 15 x) x := by
    intro x j hj
    have h15 := circuitH_trunc2_iter hw 15 x
    rw [circuitH2_period15] at h15
    have h1 := congrArg (fun p => p.1.getLsbD j) h15
    have h2 := congrArg (fun p => p.2.getLsbD j) h15
    simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and] at h1 h2
    exact Prod.ext h1 h2
  have hjac15 : ∀ k, 2 ≤ k → k < w → GL2.R1.pow 15 = GL2.I := fun _ _ _ => rfl
  exact bsasce_master_order_bound (r := 2) (D := 15) (circuitH_bitAffine2 w hw) hw hlow15 hjac15

/-- **THEOREM 4B (Prime-5 Obstruction `∀ w ≥ 2`):**
    `H^(3 * 2^w)(0, 1) ≠ (0, 1)` for EVERY `w ≥ 2`, breaking the `{2, 3}`-smoothness barrier of `A_w^(0)`. -/
theorem theorem4_circuitH_prime5_obstruction (w : Nat) (hw : 2 ≤ w) :
    iter (circuitH w hw).toFun (3 * 2 ^ w) (0#w, 1#w) ≠ (0#w, 1#w) := by
  have hiter_mod15 : ∀ n (y : State 2),
      iter (circuitH 2 (Nat.le_refl 2)).toFun n y =
        iter (circuitH 2 (Nat.le_refl 2)).toFun (n % 15) y := by
    intro n y
    have hdiv : n % 15 + 15 * (n / 15) = n := by
      have := Nat.div_add_mod n 15; omega
    calc iter (circuitH 2 (Nat.le_refl 2)).toFun n y
        = iter (circuitH 2 (Nat.le_refl 2)).toFun (n % 15 + 15 * (n / 15)) y := by rw [hdiv]
      _ = iter (circuitH 2 (Nat.le_refl 2)).toFun (n % 15)
            (iter (circuitH 2 (Nat.le_refl 2)).toFun (15 * (n / 15)) y) := iter_add _ _ _ _
      _ = iter (circuitH 2 (Nat.le_refl 2)).toFun (n % 15) y := by
            rw [iter_mul, iter_id_of_eq circuitH2_period15]
  have hmod_vals : ∀ k, 3 * 2 ^ k % 15 = 3 ∨ 3 * 2 ^ k % 15 = 6 ∨
      3 * 2 ^ k % 15 = 12 ∨ 3 * 2 ^ k % 15 = 9 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih =>
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod]
      rcases ih with h | h | h | h <;> rw [h] <;> decide
  have hne3  : iter (circuitH 2 (Nat.le_refl 2)).toFun 3  (0#2, 1#2) ≠ (0#2, 1#2) := by decide
  have hne6  : iter (circuitH 2 (Nat.le_refl 2)).toFun 6  (0#2, 1#2) ≠ (0#2, 1#2) := by decide
  have hne12 : iter (circuitH 2 (Nat.le_refl 2)).toFun 12 (0#2, 1#2) ≠ (0#2, 1#2) := by decide
  have hne9  : iter (circuitH 2 (Nat.le_refl 2)).toFun 9  (0#2, 1#2) ≠ (0#2, 1#2) := by decide
  intro heq
  have htr := circuitH_trunc2_iter hw (3 * 2 ^ w) (0#w, 1#w)
  rw [heq] at htr
  have h01 : ((0#w).setWidth 2, (1#w).setWidth 2) = (0#2, 1#2) := by
    apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
    · simp
    · have hlt : 1 < 2 ^ w := by
        have : 4 ≤ 2 ^ w := calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
        omega
      simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [h01, hiter_mod15] at htr
  rcases hmod_vals w with h | h | h | h <;> rw [h] at htr
  · exact hne3 htr.symm
  · exact hne6 htr.symm
  · exact hne12 htr.symm
  · exact hne9 htr.symm

/-- **THEOREM 4C (Strict `A_w^(0) ⊊ A_w^(2)` Separation even under FULL Symmetric-Group Conjugacy `∀ w ≥ 2`):**
    `H ∈ A_w^(2)` is NOT conjugate even in `RevCircuit w` (all bijections!) to ANY zero-preserving circuit in `A_w^(0)`. -/
theorem theorem4_circuitH_not_sym_conjugate_A0 (w : Nat) (hw : 2 ≤ w)
    (f h : RevCircuit w) (Mf : Nat → GL2)
    (hf : IsBitAffine 0 Mf f.toFun) (hf0 : f.toFun (0#w, 0#w) = (0#w, 0#w)) :
    ¬ (∀ x, (circuitH w hw).toFun x = (h.conj f).toFun x) := by
  intro hconj
  have hceil := bsasce_universal_A0_ceiling hf (by omega) hf0
  have hobs := theorem4_circuitH_prime5_obstruction w hw
  rw [iter_congr hconj] at hobs
  exact hobs (RevCircuit.conj_order_eq h f (3 * 2 ^ w) hceil (0#w, 1#w))

/-! ## Section 6: Kernel-Checked Non-Vacuity Witnesses & Axiom Audit -/

/-- Non-vacuity witness 1: `circuitE 3` inhabits zero-preserving `A_3^(0)` and achieves exact order `24`. -/
example : HasExactOrder (circuitE 3) 24 := theorem1_circuitE_exact_order 3 (by omega)

/-- Non-vacuity witness 2: `InDerivedSeries 3 4` is genuinely inhabited by a non-trivial nested commutator word. -/
theorem nonvacuity_derived_series_w3 :
    ∃ f : RevCircuit 3, InDerivedSeries 3 4 f ∧ ∀ x, f.toFun x = x := by
  let a := addShearR 3 0
  let x := xorShearR 3 0
  have ha : InDerivedSeries 3 0 a := InDerivedSeries.base (addShearR_bitAffine 3 0) (by decide)
  have hx : InDerivedSeries 3 0 x := InDerivedSeries.base (xorShearR_bitAffine 3 0) (by decide)
  have c1 : InDerivedSeries 3 1 (a.comm x) := InDerivedSeries.comm ha hx
  have c2 : InDerivedSeries 3 2 ((a.comm x).comm (a.comm x)) := InDerivedSeries.comm c1 c1
  have c3 : InDerivedSeries 3 3 (((a.comm x).comm (a.comm x)).comm ((a.comm x).comm (a.comm x))) :=
    InDerivedSeries.comm c2 c2
  have c4 : InDerivedSeries 3 4
      ((((a.comm x).comm (a.comm x)).comm ((a.comm x).comm (a.comm x))).comm
       (((a.comm x).comm (a.comm x)).comm ((a.comm x).comm (a.comm x)))) :=
    InDerivedSeries.comm c3 c3
  exact ⟨_, c4, bsasce_derived_series_collapse (w := 3) (by omega) _ c4⟩

/-- Non-vacuity witness 3: Uniform-Jacobian `U_3` is inhabited by `S ∘ A_R(0) ∘ X_R(0)` (`ord = 8`). -/
theorem nonvacuity_uniform_U3 :
    ∃ u : RevCircuit 3, IsBitAffine 0 (fun _ => GL2.J) u.toFun ∧
      u.toFun (0#3, 0#3) = (0#3, 0#3) ∧
      iter u.toFun 4 (0#3, 1#3) ≠ (0#3, 1#3) := by
  let u := (laneSwap 3).comp ((addShearR 3 0).comp (xorShearR 3 0))
  have hu : IsBitAffine 0 (fun _ => GL2.J) u.toFun := by
    have h := (laneSwap_bitAffine 3).comp ((addShearR_bitAffine 3 0).comp (xorShearR_bitAffine 3 0))
    simpa [u, RevCircuit.comp, GL2.mul] using h
  exact ⟨u, hu, by decide, by decide⟩

/-- Non-vacuity witness 4: `circuitH 3` inhabits `A_3^(2)` and achieves prime-5 separation at `w = 3`. -/
example : iter (circuitH 3 (by omega)).toFun 24 (0#3, 1#3) ≠ (0#3, 1#3) :=
  theorem4_circuitH_prime5_obstruction 3 (by omega)

end BSASCE

/-! ### Machine-Checked Axiom Audit (`#print axioms`) -/


