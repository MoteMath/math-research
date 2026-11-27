/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`BitSlicedAffineShearGroups`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace BSASCE

/-! ## Section 1: Finite Bit-Slice Jacobian Group `GL2` (GL_2(F_2) ≅ S_3) -/

abbrev Vec2 := Bool × Bool

def vecXor (u v : Vec2) : Vec2 := (u.1 ^^ v.1, u.2 ^^ v.2)

theorem vecXor_self (u : Vec2) : vecXor u u = (false, false) := by
  cases u; simp [vecXor]

theorem vecXor_eq_zero_iff (u v : Vec2) : vecXor u v = (false, false) ↔ u = v := by
  cases u with | mk u1 u2 =>
  cases v with | mk v1 v2 =>
  cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;> decide

/-- The 6 invertible 2×2 Boolean matrices forming `GL_2(F_2) ≅ S_3`:
  - `I`  = [[1,0],[0,1]]  (identity, order 1)
  - `L`  = [[1,0],[1,1]]  (right shear: (a,b) ↦ (a, b⊕a), order 2)
  - `U`  = [[1,1],[0,1]]  (left shear:  (a,b) ↦ (a⊕b, b), order 2)
  - `J`  = [[0,1],[1,0]]  (lane swap:   (a,b) ↦ (b, a), order 2)
  - `R1` = [[1,1],[1,0]]  (= L * U, order 3)
  - `R2` = [[0,1],[1,1]]  (= U * L, order 3)
-/
inductive GL2 where
  | I | L | U | J | R1 | R2
  deriving DecidableEq, Repr

namespace GL2

def act : GL2 → Vec2 → Vec2
  | I,  (a, b) => (a, b)
  | L,  (a, b) => (a, a ^^ b)
  | U,  (a, b) => (a ^^ b, b)
  | J,  (a, b) => (b, a)
  | R1, (a, b) => (a ^^ b, a)
  | R2, (a, b) => (b, a ^^ b)

def mul : GL2 → GL2 → GL2
  | I,  M  => M
  | M,  I  => M
  | L,  L  => I
  | L,  U  => R1
  | L,  J  => R2
  | L,  R1 => U
  | L,  R2 => J
  | U,  L  => R2
  | U,  U  => I
  | U,  J  => R1
  | U,  R1 => J
  | U,  R2 => L
  | J,  L  => R1
  | J,  U  => R2
  | J,  J  => I
  | J,  R1 => L
  | J,  R2 => U
  | R1, L  => J
  | R1, U  => L
  | R1, J  => U
  | R1, R1 => R2
  | R1, R2 => I
  | R2, L  => U
  | R2, U  => J
  | R2, J  => L
  | R2, R1 => I
  | R2, R2 => R1

def inv : GL2 → GL2
  | I  => I
  | L  => L
  | U  => U
  | J  => J
  | R1 => R2
  | R2 => R1

def conj (H M : GL2) : GL2 := mul (mul H M) (inv H)

def comm (M N : GL2) : GL2 := mul (mul M N) (mul (inv M) (inv N))

def pow (M : GL2) : Nat → GL2
  | 0     => I
  | n + 1 => mul M (pow M n)

theorem act_I (v : Vec2) : I.act v = v := by cases v; rfl

theorem act_mul (M N : GL2) (v : Vec2) : (mul M N).act v = M.act (N.act v) := by
  cases M <;> cases N <;> cases v with | mk a b => cases a <;> cases b <;> rfl

theorem act_inv_left (M : GL2) (v : Vec2) : M.inv.act (M.act v) = v := by
  cases M <;> cases v with | mk a b => cases a <;> cases b <;> rfl

theorem act_inj (M : GL2) {u v : Vec2} (h : M.act u = M.act v) : u = v := by
  have h' := congrArg M.inv.act h
  simpa [act_inv_left] using h'

theorem mul_assoc (A B C : GL2) : mul (mul A B) C = mul A (mul B C) := by
  cases A <;> cases B <;> cases C <;> rfl

end GL2

/-! ## Section 2: Reversible Circuits, Iteration, Conjugation, Commutators & Exact Order -/

abbrev State (w : Nat) := BitVec w × BitVec w

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0,     x => x
  | n + 1, x => f (iter f n x)

structure RevCircuit (w : Nat) where
  toFun : State w → State w
  invFun : State w → State w
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

namespace RevCircuit

def id (w : Nat) : RevCircuit w where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def comp {w : Nat} (f g : RevCircuit w) : RevCircuit w where
  toFun := fun x => f.toFun (g.toFun x)
  invFun := fun x => g.invFun (f.invFun x)
  left_inv := fun x => by simp [f.left_inv, g.left_inv]
  right_inv := fun x => by simp [f.right_inv, g.right_inv]

def inv {w : Nat} (f : RevCircuit w) : RevCircuit w where
  toFun := f.invFun
  invFun := f.toFun
  left_inv := f.right_inv
  right_inv := f.left_inv

/-- Conjugation `h ∘ f ∘ h⁻¹`. -/
def conj {w : Nat} (h f : RevCircuit w) : RevCircuit w :=
  comp h (comp f (inv h))

/-- Group commutator `[f, g] = f ∘ g ∘ f⁻¹ ∘ g⁻¹`. -/
def comm {w : Nat} (f g : RevCircuit w) : RevCircuit w :=
  comp (comp f g) (comp (inv f) (inv g))

end RevCircuit

/-- Exact minimal positive period (group order) of a reversible circuit on `State w`. -/
def HasExactOrder {w : Nat} (f : RevCircuit w) (n : Nat) : Prop :=
  0 < n ∧ (∀ x, iter f.toFun n x = x) ∧ (∀ d, 0 < d → d < n → ∃ x, iter f.toFun d x ≠ x)

/-! ## Section 3: The Reusable Infinite Proof Mechanism (`BSAS-CE`)

A reversible circuit `f : State w → State w` belongs to the Block-`r` Bit-Sliced
Affine Group `A_w^(r)` with Jacobian profile `M : Nat → GL2` iff:
  1. Base-block causality: `r ≤ w → LowEq r x y → LowEq r (f x) (f y)`
  2. Bit-slice differential linearity above `r`:
     `∀ k, r ≤ k → k < w → LowEq k x y → slice k (f x) ⊕ slice k (f y) = M k · (slice k x ⊕ slice k y)`
-/

def slice {w : Nat} (k : Nat) (x : State w) : Vec2 :=
  (x.1.getLsbD k, x.2.getLsbD k)

def LowEq {w : Nat} (k : Nat) (x y : State w) : Prop :=
  ∀ j < k, slice j x = slice j y

theorem lowEq_zero {w : Nat} (x y : State w) : LowEq 0 x y :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem lowEq_succ_iff {w : Nat} (k : Nat) (x y : State w) :
    LowEq (k + 1) x y ↔ LowEq k x y ∧ slice k x = slice k y := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩
  · rintro ⟨hk, heq⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact hk j hlt
    · exact heq

/-- Core pure-silicon predicate defining the Block-`r` Bit-Sliced Affine Group `A_w^(r)`. -/
def IsBitAffine {w : Nat} (r : Nat) (M : Nat → GL2) (f : State w → State w) : Prop :=
  (r ≤ w → ∀ x y, LowEq r x y → LowEq r (f x) (f y)) ∧
  (∀ k, r ≤ k → k < w → ∀ x y, LowEq k x y →
    vecXor (slice k (f x)) (slice k (f y)) = (M k).act (vecXor (slice k x) (slice k y)))

/-- Causality lifts inductively from the finite base block `r` to every bit level `k` (`r ≤ k ≤ w`). -/
theorem IsBitAffine.lowEq_lift {w r : Nat} {M : Nat → GL2} {f : State w → State w}
    (hf : IsBitAffine r M f) :
    ∀ k, r ≤ k → k ≤ w → ∀ x y, LowEq k x y → LowEq k (f x) (f y) := by
  intro k hrk hkw
  induction k with
  | zero =>
    intro x y _
    exact lowEq_zero _ _
  | succ k ih =>
    intro x y hxy
    by_cases hr : r = k + 1
    · subst hr
      exact hf.1 hkw x y hxy
    · have hrk' : r ≤ k := by omega
      have hkw' : k ≤ w := by omega
      rw [lowEq_succ_iff] at hxy ⊢
      refine ⟨ih hrk' hkw' x y hxy.1, ?_⟩
      have hdiff := hf.2 k hrk' (by omega) x y hxy.1
      rw [hxy.2, vecXor_self] at hdiff
      have hact0 : (M k).act (false, false) = (false, false) := by
        cases M k <;> rfl
      rw [hact0] at hdiff
      exact (vecXor_eq_zero_iff _ _).mp hdiff

theorem IsBitAffine.id (w r : Nat) : IsBitAffine r (fun _ => GL2.I) (fun x : State w => x) := by
  refine ⟨fun _ _ _ h => h, ?_⟩
  intro k _ _ x y _
  simp [GL2.act_I]

theorem IsBitAffine.comp {w r : Nat} {Mf Mg : Nat → GL2} {f g : State w → State w}
    (hf : IsBitAffine r Mf f) (hg : IsBitAffine r Mg g) :
    IsBitAffine r (fun k => GL2.mul (Mf k) (Mg k)) (fun x => f (g x)) := by
  refine ⟨?_, ?_⟩
  · intro hrw x y hxy
    exact hf.1 hrw (g x) (g y) (hg.1 hrw x y hxy)
  · intro k hrk hkw x y hxy
    have hgxy : LowEq k (g x) (g y) := hg.lowEq_lift k hrk (Nat.le_of_lt hkw) x y hxy
    rw [hf.2 k hrk hkw (g x) (g y) hgxy, hg.2 k hrk hkw x y hxy, GL2.act_mul]

/-- Base-block invertibility: if `f` is a bijection preserving `LowEq r`, then `f⁻¹` also preserves `LowEq r`. -/
theorem lowEq_inv_of_bij_base {w r : Nat} (f : RevCircuit w)
    (hrw : r ≤ w)
    (hpres : ∀ x y, LowEq r x y → LowEq r (f.toFun x) (f.toFun y)) :
    ∀ x y, LowEq r x y → LowEq r (f.invFun x) (f.invFun y) := by
  let trunc (s : State w) : Nat :=
    (s.1.toNat % 2 ^ r) + (s.2.toNat % 2 ^ r) * 2 ^ r
  have htrunc_iff : ∀ u v : State w, LowEq r u v ↔ trunc u = trunc v := by
    intro u v
    have hmod_iff : ∀ a b : BitVec w,
        (∀ j < r, a.getLsbD j = b.getLsbD j) ↔ a.toNat % 2 ^ r = b.toNat % 2 ^ r := by
      intro a b
      constructor
      · intro hbits
        have h1 : a.setWidth r = b.setWidth r := by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp [hi, hbits i hi]
        have h2 := congrArg BitVec.toNat h1
        simpa [BitVec.toNat_setWidth] using h2
      · intro hmod j hj
        have h1 : a.setWidth r = b.setWidth r := by
          apply BitVec.eq_of_toNat_eq
          simpa [BitVec.toNat_setWidth] using hmod
        have h2 := congrArg (fun z => z.getLsbD j) h1
        simpa [BitVec.getLsbD_setWidth, hj] using h2
    constructor
    · intro h
      have h1 : u.1.toNat % 2 ^ r = v.1.toNat % 2 ^ r :=
        (hmod_iff u.1 v.1).mp (fun j hj => congrArg Prod.fst (h j hj))
      have h2 : u.2.toNat % 2 ^ r = v.2.toNat % 2 ^ r :=
        (hmod_iff u.2 v.2).mp (fun j hj => congrArg Prod.snd (h j hj))
      simp [trunc, h1, h2]
    · intro ht
      have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
      have hu1 : u.1.toNat % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
      have hv1 : v.1.toNat % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
      have h1 : u.1.toNat % 2 ^ r = v.1.toNat % 2 ^ r := by
        have := congrArg (· % 2 ^ r) ht
        simp [trunc, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hv1] at this
        exact this
      have h2 : u.2.toNat % 2 ^ r = v.2.toNat % 2 ^ r := by
        have := congrArg (· / 2 ^ r) ht
        simp [trunc, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hu1, Nat.div_eq_of_lt hv1] at this
        exact this
      intro j hj
      exact Prod.ext ((hmod_iff u.1 v.1).mpr h1 j hj) ((hmod_iff u.2 v.2).mpr h2 j hj)
  let N := 2 ^ r * 2 ^ r
  let lift (idx : Fin N) : State w :=
    (BitVec.ofNat w (idx.val % 2 ^ r), BitVec.ofNat w (idx.val / 2 ^ r))
  have htrunc_lift : ∀ idx : Fin N, trunc (lift idx) = idx.val := by
    intro idx
    have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    have h2r_le : 2 ^ r ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hrw
    have ha_lt : idx.val % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
    have hb_lt : idx.val / 2 ^ r < 2 ^ r := Nat.div_lt_of_lt_mul idx.isLt
    have ha_w : idx.val % 2 ^ r < 2 ^ w := Nat.lt_of_lt_of_le ha_lt h2r_le
    have hb_w : idx.val / 2 ^ r < 2 ^ w := Nat.lt_of_lt_of_le hb_lt h2r_le
    simp only [trunc, lift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_w, Nat.mod_eq_of_lt hb_w,
      Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt]
    have := Nat.mod_add_div idx.val (2 ^ r)
    rw [Nat.mul_comm] at this
    exact this
  have htrunc_lt : ∀ s : State w, trunc s < N := by
    intro s
    have hpos : 0 < 2 ^ r := Nat.pow_pos (by omega)
    have h1 : s.1.toNat % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
    have h2 : s.2.toNat % 2 ^ r < 2 ^ r := Nat.mod_lt _ hpos
    have h3 : (s.2.toNat % 2 ^ r) * 2 ^ r + 2 ^ r ≤ 2 ^ r * 2 ^ r := by
      calc (s.2.toNat % 2 ^ r) * 2 ^ r + 2 ^ r
          = (s.2.toNat % 2 ^ r + 1) * 2 ^ r := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_right _ h2
    simp only [trunc, N]
    omega
  let bar (idx : Fin N) : Fin N := ⟨trunc (f.toFun (lift idx)), htrunc_lt _⟩
  have hbar_comm : ∀ s : State w, bar ⟨trunc s, htrunc_lt s⟩ = ⟨trunc (f.toFun s), htrunc_lt _⟩ := by
    intro s
    apply Fin.ext
    change trunc (f.toFun (lift ⟨trunc s, htrunc_lt s⟩)) = trunc (f.toFun s)
    apply (htrunc_iff _ _).mp
    apply hpres
    apply (htrunc_iff _ _).mpr
    exact htrunc_lift ⟨trunc s, htrunc_lt s⟩
  have hbar_surj : ∀ y : Fin N, ∃ x : Fin N, bar x = y := by
    intro y
    let s := f.invFun (lift y)
    refine ⟨⟨trunc s, htrunc_lt s⟩, ?_⟩
    rw [hbar_comm s]
    apply Fin.ext
    change trunc (f.toFun (f.invFun (lift y))) = y.val
    rw [f.right_inv, htrunc_lift]
  -- Surjective map `Fin n → Fin n` is injective (elementary finite pigeonhole)
  have fin_surj_inj : ∀ (n : Nat) (g : Fin n → Fin n),
      (∀ y, ∃ x, g x = y) → (∀ a b, g a = g b → a = b) := by
    intro n
    induction n with
    | zero => intro g _ a; exact Fin.elim0 a
    | succ n ih =>
      intro g hsurj a b hab
      let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
      rcases hsurj last with ⟨p, hp⟩
      let sw (x : Fin (n + 1)) : Fin (n + 1) :=
        if x = p then last else if x = last then p else x
      have hsw_inv : ∀ x, sw (sw x) = x := by
        intro x
        by_cases hxp : x = p
        · subst hxp; simp [sw]
        · by_cases hxl : x = last
          · subst hxl; simp [sw, hxp]
          · simp [sw, hxp, hxl]
      let g' (x : Fin (n + 1)) : Fin (n + 1) := g (sw x)
      have hg'_last : g' last = last := by
        by_cases hlp : last = p
        · have hswl : sw last = p := by simp [sw, hlp]
          change g (sw last) = last
          rw [hswl, hp]
        · have hswl : sw last = p := by simp [sw, hlp]
          change g (sw last) = last
          rw [hswl, hp]
      have hg'_surj : ∀ y, ∃ x, g' x = y := by
        intro y
        rcases hsurj y with ⟨x, hx⟩
        exact ⟨sw x, by simp [g', hsw_inv, hx]⟩
      have huniq_last : ∀ x : Fin (n + 1), g' x = last → x = last := by
        intro x hx
        exact Classical.byContradiction fun hne => by
          have hlt : x.val < n := by
            have h1 := x.isLt
            have h2 : x.val ≠ n := fun hv => hne (Fin.ext hv)
            omega
          have hnpos : 0 < n := by omega
          let x0 : Fin n := ⟨x.val, hlt⟩
          let zero : Fin n := ⟨0, hnpos⟩
          let h (i : Fin n) : Fin n :=
            if hi : (g' i.castSucc).val < n then ⟨(g' i.castSucc).val, hi⟩ else zero
          have hh_surj : ∀ y : Fin n, ∃ i : Fin n, h i = y := by
            intro y
            rcases hg'_surj y.castSucc with ⟨z, hz⟩
            have hz_ne : z ≠ last := by
              intro hzl
              rw [hzl, hg'_last] at hz
              have := congrArg Fin.val hz
              simp [last] at this
              omega
            have hz_lt : z.val < n := by
              have h1 := z.isLt
              have h2 : z.val ≠ n := fun hv => hz_ne (Fin.ext hv)
              omega
            refine ⟨⟨z.val, hz_lt⟩, ?_⟩
            have hcast : (⟨z.val, hz_lt⟩ : Fin n).castSucc = z := Fin.ext rfl
            simp only [h, hcast, hz]
            simp
          have hh_inj := ih h hh_surj
          rcases hg'_surj zero.castSucc with ⟨z0, hz0⟩
          have hz0_ne_last : z0 ≠ last := by
            intro hzl; rw [hzl, hg'_last] at hz0
            have := congrArg Fin.val hz0; simp [last, zero] at this; omega
          have hz0_lt : z0.val < n := by
            have h1 := z0.isLt
            have h2 : z0.val ≠ n := fun hv => hz0_ne_last (Fin.ext hv)
            omega
          let i0 : Fin n := ⟨z0.val, hz0_lt⟩
          have hi0_eq : h i0 = zero := by
            have hcast : i0.castSucc = z0 := Fin.ext rfl
            simp only [h, hcast, hz0]
            simp
          have hx0_eq : h x0 = zero := by
            have hcast : x0.castSucc = x := Fin.ext rfl
            simp only [h, hcast, hx, last]
            simp
          have hi0_x0 : i0 = x0 := hh_inj i0 x0 (hi0_eq.trans hx0_eq.symm)
          have hval_eq : i0.val = x0.val := congrArg Fin.val hi0_x0
          have hz0_x : z0 = x := Fin.ext hval_eq
          rw [hz0_x, hx] at hz0
          have := congrArg Fin.val hz0
          simp [last, zero] at this
          omega
      have hg'_lt : ∀ i : Fin n, (g' i.castSucc).val < n := by
        intro i
        have hne : g' i.castSucc ≠ last := by
          intro heq
          have := huniq_last i.castSucc heq
          have := congrArg Fin.val this
          simp [last] at this
          omega
        have h1 := (g' i.castSucc).isLt
        have hval : (g' i.castSucc).val ≠ n := fun hv => hne (Fin.ext hv)
        omega
      let h (i : Fin n) : Fin n := ⟨(g' i.castSucc).val, hg'_lt i⟩
      have hh_surj : ∀ y : Fin n, ∃ i : Fin n, h i = y := by
        intro y
        rcases hg'_surj y.castSucc with ⟨z, hz⟩
        have hz_ne : z ≠ last := by
          intro hzl; rw [hzl, hg'_last] at hz
          have := congrArg Fin.val hz; simp [last] at this; omega
        have hz_lt : z.val < n := by
          have h1 := z.isLt
          have h2 : z.val ≠ n := fun hv => hz_ne (Fin.ext hv)
          omega
        refine ⟨⟨z.val, hz_lt⟩, ?_⟩
        apply Fin.ext
        change (g' (⟨z.val, hz_lt⟩ : Fin n).castSucc).val = y.val
        have hcast : (⟨z.val, hz_lt⟩ : Fin n).castSucc = z := Fin.ext rfl
        rw [hcast, hz]; rfl
      have hh_inj := ih h hh_surj
      have hg'_inj : ∀ u v, g' u = g' v → u = v := by
        intro u v huv
        by_cases hu : u = last
        · subst hu
          rw [hg'_last] at huv
          exact (huniq_last v huv.symm).symm
        · by_cases hv : v = last
          · subst hv
            rw [hg'_last] at huv
            exact huniq_last u huv
          · have hult : u.val < n := by
              have h1 := u.isLt; have h2 : u.val ≠ n := fun h => hu (Fin.ext h); omega
            have hvlt : v.val < n := by
              have h1 := v.isLt; have h2 : v.val ≠ n := fun h => hv (Fin.ext h); omega
            have heqh : h ⟨u.val, hult⟩ = h ⟨v.val, hvlt⟩ := by
              apply Fin.ext
              have hu' : (⟨u.val, hult⟩ : Fin n).castSucc = u := Fin.ext rfl
              have hv' : (⟨v.val, hvlt⟩ : Fin n).castSucc = v := Fin.ext rfl
              change (g' (⟨u.val, hult⟩ : Fin n).castSucc).val = (g' (⟨v.val, hvlt⟩ : Fin n).castSucc).val
              rw [hu', hv', huv]
            have heqfin : (⟨u.val, hult⟩ : Fin n) = (⟨v.val, hvlt⟩ : Fin n) := hh_inj _ _ heqh
            have hval_uv : (⟨u.val, hult⟩ : Fin n).val = (⟨v.val, hvlt⟩ : Fin n).val := congrArg Fin.val heqfin
            exact Fin.ext hval_uv
      have hab' : g' (sw a) = g' (sw b) := by simp [g', hsw_inv, hab]
      have hswab := hg'_inj _ _ hab'
      have := congrArg sw hswab
      simpa [hsw_inv] using this
  have hbar_inj := fin_surj_inj N bar hbar_surj
  intro x y hxy
  apply (htrunc_iff _ _).mpr
  have hfeq : bar ⟨trunc (f.invFun x), htrunc_lt _⟩ = bar ⟨trunc (f.invFun y), htrunc_lt _⟩ := by
    rw [hbar_comm, hbar_comm, f.right_inv, f.right_inv]
    apply Fin.ext
    exact (htrunc_iff x y).mp hxy
  exact congrArg Fin.val (hbar_inj _ _ hfeq)

/-- Group closure under inverse: if `f ∈ A_w^(r)` with profile `M`, then `f⁻¹ ∈ A_w^(r)` with profile `M⁻¹`. -/
theorem IsBitAffine.inv {w r : Nat} {M : Nat → GL2} (f : RevCircuit w)
    (hf : IsBitAffine r M f.toFun) :
    IsBitAffine r (fun k => (M k).inv) f.invFun := by
  have hbase : r ≤ w → ∀ x y, LowEq r x y → LowEq r (f.invFun x) (f.invFun y) :=
    fun hrw => lowEq_inv_of_bij_base f hrw (hf.1 hrw)
  have hlift : ∀ k, r ≤ k → k ≤ w → ∀ x y, LowEq k x y → LowEq k (f.invFun x) (f.invFun y) := by
    intro k hrk hkw
    induction k with
    | zero => intro x y _; exact lowEq_zero _ _
    | succ k ih =>
      intro x y hxy
      by_cases hr : r = k + 1
      · subst hr; exact hbase hkw x y hxy
      · have hrk' : r ≤ k := by omega
        rw [lowEq_succ_iff] at hxy ⊢
        have hprev : LowEq k (f.invFun x) (f.invFun y) := ih hrk' (by omega) x y hxy.1
        refine ⟨hprev, ?_⟩
        have hdiff := hf.2 k hrk' (by omega) (f.invFun x) (f.invFun y) hprev
        rw [f.right_inv, f.right_inv, hxy.2, vecXor_self] at hdiff
        have hact0 : (M k).act (false, false) = (false, false) := by cases M k <;> rfl
        rw [← hact0] at hdiff
        have hzero := GL2.act_inj (M k) hdiff.symm
        exact (vecXor_eq_zero_iff _ _).mp hzero
  refine ⟨hbase, ?_⟩
  intro k hrk hkw x y hxy
  have hinv_low : LowEq k (f.invFun x) (f.invFun y) := hlift k hrk (Nat.le_of_lt hkw) x y hxy
  have hdiff := hf.2 k hrk hkw (f.invFun x) (f.invFun y) hinv_low
  rw [f.right_inv, f.right_inv] at hdiff
  have h' := congrArg (M k).inv.act hdiff
  simpa [GL2.act_inv_left] using h'.symm

/-- Conjugation closure inside `A_w^(r)`. -/
theorem IsBitAffine.conj {w r : Nat} {Mh Mf : Nat → GL2} (h f : RevCircuit w)
    (hh : IsBitAffine r Mh h.toFun) (hf : IsBitAffine r Mf f.toFun) :
    IsBitAffine r (fun k => GL2.conj (Mh k) (Mf k)) (h.conj f).toFun := by
  have h1 := hh.comp (hf.comp (hh.inv h))
  refine ⟨h1.1, ?_⟩
  intro k hrk hkw x y hxy
  have h2 := h1.2 k hrk hkw x y hxy
  simpa [RevCircuit.conj, RevCircuit.comp, RevCircuit.inv, GL2.conj, GL2.mul_assoc] using h2

/-- Commutator closure inside `A_w^(r)`. -/
theorem IsBitAffine.comm {w r : Nat} {Mf Mg : Nat → GL2} (f g : RevCircuit w)
    (hf : IsBitAffine r Mf f.toFun) (hg : IsBitAffine r Mg g.toFun) :
    IsBitAffine r (fun k => GL2.comm (Mf k) (Mg k)) (f.comm g).toFun := by
  have h1 := (hf.comp hg).comp ((hf.inv f).comp (hg.inv g))
  simpa [RevCircuit.comm, RevCircuit.comp, RevCircuit.inv, GL2.comm] using h1

/-- Inductive definition of the `d`-th derived subgroup `(A_w^(0))^(d)` of zero-preserving circuits. -/
inductive InDerivedSeries (w : Nat) : Nat → RevCircuit w → Prop where
  | base {f : RevCircuit w} {M : Nat → GL2} :
      IsBitAffine 0 M f.toFun → f.toFun (0#w, 0#w) = (0#w, 0#w) → InDerivedSeries w 0 f
  | comm {d : Nat} {f g : RevCircuit w} :
      InDerivedSeries w d f → InDerivedSeries w d g → InDerivedSeries w (d + 1) (f.comm g)
  | id {d : Nat} : InDerivedSeries w d (RevCircuit.id w)
  | comp {d : Nat} {f g : RevCircuit w} :
      InDerivedSeries w d f → InDerivedSeries w d g → InDerivedSeries w d (f.comp g)
  | inv {d : Nat} {f : RevCircuit w} :
      InDerivedSeries w d f → InDerivedSeries w d f.inv

/-- Right Add-Shear `A_R(s)(a, b) = (a, b + (a <<< s))`. -/
def addShearR (w s : Nat) : RevCircuit w where
  toFun := fun (a, b) => (a, b + (a <<< s))
  invFun := fun (a, b) => (a, b - (a <<< s))
  left_inv := fun (a, b) => by simp [BitVec.add_sub_cancel]
  right_inv := fun (a, b) => by simp [BitVec.sub_add_cancel]

/-- Masked Left Add-Shear `A_{L, m}(a, b) = (a + (b &&& m), b)`. -/
def addShearLMask (w : Nat) (m : BitVec w) : RevCircuit w where
  toFun := fun (a, b) => (a + (b &&& m), b)
  invFun := fun (a, b) => (a - (b &&& m), b)
  left_inv := fun (a, b) => by simp [BitVec.add_sub_cancel]
  right_inv := fun (a, b) => by simp [BitVec.sub_add_cancel]

/-- Right XOR-Shear `X_R(s)(a, b) = (a, b ^^^ (a <<< s))`. -/
def xorShearR (w s : Nat) : RevCircuit w where
  toFun := fun (a, b) => (a, b ^^^ (a <<< s))
  invFun := fun (a, b) => (a, b ^^^ (a <<< s))
  left_inv := fun (a, b) => by simp [BitVec.xor_assoc]
  right_inv := fun (a, b) => by simp [BitVec.xor_assoc]

/-- Left XOR-Shear `X_L(s)(a, b) = (a ^^^ (b <<< s), b)`. -/
def xorShearL (w s : Nat) : RevCircuit w where
  toFun := fun (a, b) => (a ^^^ (b <<< s), b)
  invFun := fun (a, b) => (a ^^^ (b <<< s), b)
  left_inv := fun (a, b) => by simp [BitVec.xor_assoc]
  right_inv := fun (a, b) => by simp [BitVec.xor_assoc]

/-- Masked Cross-Lane Bit-Swap `S_m`: swaps bit positions where `m` is `1` between lanes `a` and `b`. -/
def crossBitSwap (w : Nat) (m : BitVec w) : RevCircuit w where
  toFun := fun (a, b) => ((a &&& ~~~m) ||| (b &&& m), (b &&& ~~~m) ||| (a &&& m))
  invFun := fun (a, b) => ((a &&& ~~~m) ||| (b &&& m), (b &&& ~~~m) ||| (a &&& m))
  left_inv := fun (a, b) => by
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and] <;>
      cases m.getLsbD i <;> simp
  right_inv := fun (a, b) => by
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and] <;>
      cases m.getLsbD i <;> simp

/-- Intra-lane swap of bit `0` and bit `1` on a single `BitVec w`. -/
def swap01 {w : Nat} (x : BitVec w) : BitVec w :=
  if x.getLsbD 0 != x.getLsbD 1 then x ^^^ 3#w else x

theorem bitvec3_getLsbD_0 {w : Nat} (hw : 2 ≤ w) : (3#w).getLsbD 0 = true := by
  rw [BitVec.getLsbD_ofNat]; simp [(by omega : 0 < w)]

theorem bitvec3_getLsbD_1 {w : Nat} (hw : 2 ≤ w) : (3#w).getLsbD 1 = true := by
  rw [BitVec.getLsbD_ofNat]
  have h1 : 1 < w := by omega
  have h2 : Nat.testBit 3 1 = true := by decide
  simp [h1, h2]

theorem swap01_getLsbD_ge2 {w : Nat} (x : BitVec w) (k : Nat) (hk : 2 ≤ k) :
    (swap01 x).getLsbD k = x.getLsbD k := by
  unfold swap01
  split
  · have h3 : (3#w).getLsbD k = false := by
      rw [BitVec.getLsbD_ofNat]
      by_cases hkw : k < w
      · have h4 : 4 ≤ 2 ^ k := calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        have hdiv : 3 / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
        simp [hkw, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
      · simp [hkw]
    simp [h3]
  · rfl

theorem swap01_getLsbD_0 {w : Nat} (hw : 2 ≤ w) (x : BitVec w) :
    (swap01 x).getLsbD 0 = x.getLsbD 1 := by
  unfold swap01
  have h30 := bitvec3_getLsbD_0 hw
  cases h0 : x.getLsbD 0 <;> cases h1 : x.getLsbD 1 <;> simp [h30, h0]

theorem swap01_getLsbD_1 {w : Nat} (hw : 2 ≤ w) (x : BitVec w) :
    (swap01 x).getLsbD 1 = x.getLsbD 0 := by
  unfold swap01
  have h31 := bitvec3_getLsbD_1 hw
  cases h0 : x.getLsbD 0 <;> cases h1 : x.getLsbD 1 <;> simp [h31, h1]

theorem swap01_inv {w : Nat} (hw : 2 ≤ w) (x : BitVec w) : swap01 (swap01 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  match k with
  | 0 => rw [swap01_getLsbD_0 hw, swap01_getLsbD_1 hw]
  | 1 => rw [swap01_getLsbD_1 hw, swap01_getLsbD_0 hw]
  | k + 2 => rw [swap01_getLsbD_ge2 _ _ (by omega), swap01_getLsbD_ge2 _ _ (by omega)]

/-- Intra-lane bit-swap layer `B_{0,1}` (swaps bit `0` and bit `1` in both lanes, for `w ≥ 2`). -/
def intraBitSwap01 (w : Nat) (hw : 2 ≤ w) : RevCircuit w where
  toFun := fun (a, b) => (swap01 a, swap01 b)
  invFun := fun (a, b) => (swap01 a, swap01 b)
  left_inv := fun (a, b) => Prod.ext (swap01_inv hw a) (swap01_inv hw b)
  right_inv := fun (a, b) => Prod.ext (swap01_inv hw a) (swap01_inv hw b)

/-! ## Section 5: Concrete Infinite Theorems (`∀ w ≥ 2` / `∀ w ≥ 3`) -/

/-! ### Theorem 1: Exact Saturation of `A_w^(0)` Ceiling (`3 * 2^w`), Non-Commutator Obstruction & Uniform Separation -/

/-- `E = A_R(0) ∘ A_{L,{0}} : (a, b) ↦ (a + (b &&& 1), b + (a + (b &&& 1)))`. -/
def circuitE (w : Nat) : RevCircuit w :=
  (addShearR w 0).comp (addShearLMask w 1#w)

/-! ### Theorem 2: Exact Order of Cross-Swap Circuit `P = S_{0} ∘ A_R(0)` & `2^w`-Class Conjugacy Separation -/

/-- `P = S_{0} ∘ A_R(0)`: adds lane 1 into lane 2, then swaps bit 0 across lanes. -/
def circuitP (w : Nat) : RevCircuit w :=
  (crossBitSwap w 1#w).comp (addShearR w 0)

/-- Masked cross-lane bit-swap family `F_m = S_m ∘ A_R(0) ∘ X_L(0)` (`2^w` circuits). -/
def circuitFm (w : Nat) (m : BitVec w) : RevCircuit w :=
  (crossBitSwap w m).comp ((addShearR w 0).comp (xorShearL w 0))

/-- **THEOREM 3C (Exact Wreath Subgroup Generation `H_w = ⟨+1, ⊕1⟩ ≅ C_{2^(w-1)} ≀ C_2`, `|H_w| = 2^(2w-1)`):** -/
def fiber1Add1 (w : Nat) (b : BitVec w) : BitVec w := b + 1#w
def fiber1Xor1 (w : Nat) (b : BitVec w) : BitVec w := b ^^^ 1#w

inductive InFiber1Group (w : Nat) : (BitVec w → BitVec w) → Prop where
  | id : InFiber1Group w (fun b => b)
  | genAdd : InFiber1Group w (fiber1Add1 w)
  | genXor : InFiber1Group w (fiber1Xor1 w)
  | comp {f g} : InFiber1Group w f → InFiber1Group w g → InFiber1Group w (fun b => f (g b))

def wreathElem {w : Nat} (ε : Bool) (u v : BitVec (w - 1)) (b : BitVec w) : BitVec w :=
  let shift := if b.getLsbD 0 then BitVec.ofNat w (2 * v.toNat) else BitVec.ofNat w (2 * u.toNat)
  if ε then (b + shift) ^^^ 1#w else b + shift

/-! ### Theorem 4: Block-2 Intra-Lane Bit-Swap Symmetry-Breaking & 3-Level Strict Hierarchy -/

/-- `H = B_{0,1} ∘ A_R(0) ∘ X_L(0)` (intra-lane bit-0/bit-1 swap composed with add-shear and XOR-shear). -/
def circuitH (w : Nat) (hw : 2 ≤ w) : RevCircuit w :=
  (intraBitSwap01 w hw).comp ((addShearR w 0).comp (xorShearL w 0))

end BSASCE
