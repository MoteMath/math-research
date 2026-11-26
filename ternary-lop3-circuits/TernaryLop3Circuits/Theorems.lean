/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Circuits.Defs

/-!
# Verified Proofs for Minimal-`LOP3` Ternary Bit-Plane Circuits

All seven headline theorems proved in pure Lean 4 `Init` (zero Mathlib, zero `sorry`,
zero `native_decide`), fast in both the Lean 4 kernel and Palomar `nanoda`.
-/

namespace TernaryLop3Circuits

/-! ## Section 1: General Cardinality & Pigeonhole Helpers -/

private theorem countP_add_not {α : Type} (l : List α) (f : α → Bool) :
    l.countP f + l.countP (fun x => !f x) = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    cases f a <;> simp <;> omega

private theorem countTrue_add_not {n : Nat} (f : Fin n → Bool) :
    countTrue f + countTrue (fun x => !f x) = n := by
  unfold countTrue
  rw [countP_add_not, List.length_finRange]

private theorem countP_split {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP P = l.countP (fun x => P x && Q x) + l.countP (fun x => P x && !Q x) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons]
    cases P a <;> cases Q a <;> simp <;> omega

private theorem countTrue_split {n : Nat} (P Q : Fin n → Bool) :
    countTrue P = countTrue (fun x => P x && Q x) + countTrue (fun x => P x && !Q x) :=
  countP_split (List.finRange n) P Q

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x, x ∈ t → x ∈ l₂.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem a hx))
    have ih := length_le_of_nodup_subset t (l₂.erase a) hnd.2 hsub'
    have her : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

private theorem le_countTrue_of_inj {m n : Nat} (f : Fin n → Bool)
    (enc : Fin m → Fin n) (hinj : ∀ a b, enc a = enc b → a = b)
    (hpred : ∀ a, f (enc a) = true) :
    m ≤ countTrue f := by
  unfold countTrue
  rw [List.countP_eq_length_filter]
  have h1 : ((List.finRange m).map enc).Nodup :=
    (List.nodup_finRange m).map enc (fun _ _ hne heq => hne (hinj _ _ heq))
  have hsub : ∀ x, x ∈ (List.finRange m).map enc → x ∈ (List.finRange n).filter f := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨a, _, rfl⟩
    rw [List.mem_filter]
    exact ⟨List.mem_finRange _, hpred a⟩
  have hle := length_le_of_nodup_subset _ _ h1 hsub
  rw [List.length_map, List.length_finRange] at hle
  exact hle

private theorem le_countTrue_of_exists {α : Type} {m n : Nat} (f : Fin n → Bool)
    (g : Fin n → α) (target : Fin m → α)
    (htinj : ∀ a b, target a = target b → a = b)
    (hsurj : ∀ a : Fin m, ∃ x : Fin n, g x = target a)
    (himp : ∀ x a, g x = target a → f x = true) :
    m ≤ countTrue f := by
  let enc : Fin m → Fin n := fun a => Classical.choose (hsurj a)
  have henc : ∀ a, g (enc a) = target a := fun a => Classical.choose_spec (hsurj a)
  apply le_countTrue_of_inj f enc
  · intro a b hab
    apply htinj
    rw [← henc a, ← henc b, hab]
  · intro a
    exact himp (enc a) a (henc a)

private theorem trit_pos_of_val_eq_one (pn : Bool × Bool) (hd : tritDisjoint pn = true)
    (hv : tritVal pn = 1) : pn.1 = true := by
  rcases pn with ⟨p, n⟩
  cases p <;> cases n <;> simp [tritDisjoint, tritVal, boolToInt] at hd hv ⊢

private theorem trit_pos_false_of_val_ne_one (pn : Bool × Bool) (hd : tritDisjoint pn = true)
    (hv : tritVal pn ≠ 1) : pn.1 = false := by
  rcases pn with ⟨p, n⟩
  cases p <;> cases n <;> simp [tritDisjoint, tritVal, boolToInt] at hd hv ⊢

private theorem trit_neg_of_val_eq_neg_one (pn : Bool × Bool) (hd : tritDisjoint pn = true)
    (hv : tritVal pn = -1) : pn.2 = true := by
  rcases pn with ⟨p, n⟩
  cases p <;> cases n <;> simp [tritDisjoint, tritVal, boolToInt] at hd hv ⊢

private theorem trit_neg_false_of_val_ne_neg_one (pn : Bool × Bool) (hd : tritDisjoint pn = true)
    (hv : tritVal pn ≠ -1) : pn.2 = false := by
  rcases pn with ⟨p, n⟩
  cases p <;> cases n <;> simp [tritDisjoint, tritVal, boolToInt] at hd hv ⊢

/-! ## Section 2: Theorem 1 — 6-`LOP3` Depth-2 3-Trit / 5-Bit Circuit -/

theorem unpack_3t5b_sound_and_surjective :
    (∀ x : Fin 32,
      let (tr0, tr1, tr2) := unpack3t5b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true) ∧
    (∀ t0 t1 t2 : Fin 3,
      ∃ x : Fin 32, esc3t5b x = false ∧
        let (tr0, tr1, tr2) := unpack3t5b x
        tritVal tr0 = fin3ToTrit t0 ∧
        tritVal tr1 = fin3ToTrit t1 ∧
        tritVal tr2 = fin3ToTrit t2) := by
  decide

/-! ## Section 3: Theorem 2 — Exact 6-Gate Lower Bound for 3-Trit / 5-Bit Decoders -/

private theorem countTrue_not_lit5 :
    ∀ (j : Fin 5) (neg : Bool),
      countTrue (fun x : Fin 32 =>
        !(if neg then !(bitAt x.val j.val) else bitAt x.val j.val)) = 16 := by
  decide

private theorem fin3ToTrit_inj {a b : Fin 3} (h : fin3ToTrit a = fin3ToTrit b) : a = b := by
  unfold fin3ToTrit at h
  exact Fin.ext (by omega)

private theorem lower_bound_3t_lane
    (D : Fin 32 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 32,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2 = true)
    (hsurj : ∀ t0 t1 t2 : Fin 3, ∃ x : Fin 32,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2 = fin3ToTrit t2)
    (k : Fin 6) :
    9 ≤ countTrue (fun x => lane3t (D x) k) ∧
    18 ≤ countTrue (fun x => !(lane3t (D x) k)) := by
  let g : Fin 32 → Int × Int × Int :=
    fun x => (tritVal (D x).1, tritVal (D x).2.1, tritVal (D x).2.2)
  have hsurjG : ∀ t0 t1 t2 : Fin 3,
      ∃ x : Fin 32, g x = (fin3ToTrit t0, fin3ToTrit t1, fin3ToTrit t2) := by
    intro t0 t1 t2
    rcases hsurj t0 t1 t2 with ⟨x, h0, h1, h2⟩
    exact ⟨x, Prod.ext h0 (Prod.ext h1 h2)⟩
  let insert3 (idx : Fin 3) (v u w : Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
    match idx with
    | ⟨0, _⟩ => (v, u, w)
    | ⟨1, _⟩ => (u, v, w)
    | ⟨2, _⟩ => (u, w, v)
  let eval3 (t : Fin 3 × Fin 3 × Fin 3) : Int × Int × Int :=
    (fin3ToTrit t.1, fin3ToTrit t.2.1, fin3ToTrit t.2.2)
  let proj3 (x : Fin 32) (idx : Fin 3) : Int :=
    match idx with
    | ⟨0, _⟩ => tritVal (D x).1
    | ⟨1, _⟩ => tritVal (D x).2.1
    | ⟨2, _⟩ => tritVal (D x).2.2
  have heval3_inj : ∀ a b, eval3 a = eval3 b → a = b := by
    intro a b h
    simp only [eval3, Prod.mk.injEq] at h
    exact Prod.ext (fin3ToTrit_inj h.1) (Prod.ext (fin3ToTrit_inj h.2.1) (fin3ToTrit_inj h.2.2))
  have hinsert3_inj : ∀ idx v1 u1 w1 v2 u2 w2,
      insert3 idx v1 u1 w1 = insert3 idx v2 u2 w2 → v1 = v2 ∧ u1 = u2 ∧ w1 = w2 := by
    intro idx v1 u1 w1 v2 u2 w2 h
    rcases idx with ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp only [insert3, Prod.mk.injEq] at h; exact ⟨h.1, h.2.1, h.2.2⟩
    | 1, _ => simp only [insert3, Prod.mk.injEq] at h; exact ⟨h.2.1, h.1, h.2.2⟩
    | 2, _ => simp only [insert3, Prod.mk.injEq] at h; exact ⟨h.2.2, h.1, h.2.1⟩
  have hproj3_eq : ∀ x idx v u w,
      g x = eval3 (insert3 idx v u w) → proj3 x idx = fin3ToTrit v := by
    intro x idx v u w h
    rcases idx with ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp only [g, eval3, insert3, Prod.mk.injEq] at h; exact h.1
    | 1, _ => simp only [g, eval3, insert3, Prod.mk.injEq] at h; exact h.2.1
    | 2, _ => simp only [g, eval3, insert3, Prod.mk.injEq] at h; exact h.2.2
  have h9 : ∀ (idx : Fin 3) (v : Fin 3),
      9 ≤ countTrue (fun x => proj3 x idx == fin3ToTrit v) := by
    intro idx v
    let target : Fin 9 → Int × Int × Int := fun a =>
      eval3 (insert3 idx v ⟨a.val / 3, by omega⟩ ⟨a.val % 3, by omega⟩)
    apply le_countTrue_of_exists _ g target
    · intro a b hab
      have h1 := hinsert3_inj idx _ _ _ _ _ _ (heval3_inj _ _ hab)
      have e1 := congrArg Fin.val h1.2.1
      have e2 := congrArg Fin.val h1.2.2
      dsimp only at e1 e2
      exact Fin.ext (by omega)
    · intro a
      let t := insert3 idx v ⟨a.val / 3, by omega⟩ ⟨a.val % 3, by omega⟩
      exact hsurjG t.1 t.2.1 t.2.2
    · intro x a hgx
      simp [hproj3_eq x idx v _ _ hgx]
  have h18 : ∀ (idx : Fin 3) (v : Fin 3),
      18 ≤ countTrue (fun x => proj3 x idx != fin3ToTrit v) := by
    intro idx v
    let other : Fin 2 → Fin 3 := fun b =>
      ⟨(v.val + 1 + b.val) % 3, Nat.mod_lt _ (by omega)⟩
    have hother_ne : ∀ b : Fin 2, fin3ToTrit (other b) ≠ fin3ToTrit v := by
      intro b h
      have hv := congrArg Fin.val (fin3ToTrit_inj h)
      simp only [other] at hv
      omega
    have hother_inj : ∀ b₁ b₂ : Fin 2, other b₁ = other b₂ → b₁ = b₂ := by
      intro b₁ b₂ h
      have hv := congrArg Fin.val h
      simp only [other] at hv
      exact Fin.ext (by omega)
    let target : Fin 18 → Int × Int × Int := fun a =>
      eval3 (insert3 idx (other ⟨a.val / 9, by omega⟩) ⟨(a.val % 9) / 3, by omega⟩ ⟨a.val % 3, by omega⟩)
    apply le_countTrue_of_exists _ g target
    · intro a b hab
      have h1 := hinsert3_inj idx _ _ _ _ _ _ (heval3_inj _ _ hab)
      have e0 := congrArg Fin.val (hother_inj _ _ h1.1)
      have e1 := congrArg Fin.val h1.2.1
      have e2 := congrArg Fin.val h1.2.2
      dsimp only at e0 e1 e2
      exact Fin.ext (by omega)
    · intro a
      let t := insert3 idx (other ⟨a.val / 9, by omega⟩) ⟨(a.val % 9) / 3, by omega⟩ ⟨a.val % 3, by omega⟩
      exact hsurjG t.1 t.2.1 t.2.2
    · intro x a hgx
      simp [hproj3_eq x idx _ _ _ hgx, bne_iff_ne, hother_ne]
  have hmono : ∀ (f₁ f₂ : Fin 32 → Bool), (∀ x, f₁ x = true → f₂ x = true) →
      countTrue f₁ ≤ countTrue f₂ := by
    intro f₁ f₂ himp
    unfold countTrue
    have : ∀ l : List (Fin 32), l.countP f₁ ≤ l.countP f₂ := by
      intro l
      induction l with
      | nil => exact Nat.le_refl 0
      | cons a t ih =>
        simp only [List.countP_cons]
        cases h1 : f₁ a
        · cases f₂ a <;> simp <;> omega
        · rw [himp a h1]; simp; omega
    exact this (List.finRange 32)
  rcases k with ⟨kv, hkv⟩
  match kv, hkv with
  | 0, _ =>
    refine ⟨Nat.le_trans (h9 ⟨0, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨0, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).1 (hdisj x).1 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_pos_false_of_val_ne_one (D x).1 (hdisj x).1 hx]
  | 1, _ =>
    refine ⟨Nat.le_trans (h9 ⟨0, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨0, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).1 (hdisj x).1 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_neg_false_of_val_ne_neg_one (D x).1 (hdisj x).1 hx]
  | 2, _ =>
    refine ⟨Nat.le_trans (h9 ⟨1, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨1, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.1 (hdisj x).2.1 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_pos_false_of_val_ne_one (D x).2.1 (hdisj x).2.1 hx]
  | 3, _ =>
    refine ⟨Nat.le_trans (h9 ⟨1, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨1, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.1 (hdisj x).2.1 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_neg_false_of_val_ne_neg_one (D x).2.1 (hdisj x).2.1 hx]
  | 4, _ =>
    refine ⟨Nat.le_trans (h9 ⟨2, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨2, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.2 (hdisj x).2.2 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_pos_false_of_val_ne_one (D x).2.2 (hdisj x).2.2 hx]
  | 5, _ =>
    refine ⟨Nat.le_trans (h9 ⟨2, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h18 ⟨2, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj3, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.2 (hdisj x).2.2 hx
    · intro x hx; simp only [proj3, bne_iff_ne, fin3ToTrit] at hx
      simp [lane3t, trit_neg_false_of_val_ne_neg_one (D x).2.2 (hdisj x).2.2 hx]

theorem unpack_3t5b_six_gate_lower_bound
    (D : Fin 32 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 32,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2 = true)
    (hsurj : ∀ t0 t1 t2 : Fin 3, ∃ x : Fin 32,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2 = fin3ToTrit t2) :
    (∀ k : Fin 6,
      9 ≤ countTrue (fun x => lane3t (D x) k) ∧
      18 ≤ countTrue (fun x => !(lane3t (D x) k))) ∧
    (∀ (k : Fin 6) (j : Fin 5) (neg : Bool),
      ¬ (∀ x : Fin 32,
        lane3t (D x) k = if neg then !(bitAt x.val j.val) else bitAt x.val j.val)) := by
  have hlb := lower_bound_3t_lane D hdisj hsurj
  refine ⟨hlb, ?_⟩
  intro k j neg heq
  have h18 := (hlb k).2
  have hcongr :
      countTrue (fun x => !(lane3t (D x) k)) =
      countTrue (fun x : Fin 32 => !(if neg then !(bitAt x.val j.val) else bitAt x.val j.val)) := by
    unfold countTrue
    congr 1
    funext x
    rw [heq x]
  rw [hcongr, countTrue_not_lit5 j neg] at h18
  omega

/-! ## Section 4: Theorem 3 — 14-`LOP3` Depth-4 5-Trit / 8-Bit Circuit -/

/-- Explicit 243-entry right-inverse encoder for `unpack5t8b`, partitioned into nine
    27-entry blocks by `(t0, t1)` so kernel reduction stays shallow without `maxRecDepth`. -/
private def encode5t8bBlock (t0 t1 : Fin 3) : List Nat :=
  match t0.val, t1.val with
  | 0, 0 => [ 48,  54,  50,  58,  62,  56,  49,  60,  52,  46,  42,  40,  38,  32,  34,  44,  33,  36,
              47,  55,  53,  39,  63,  37,  59,  43,  35]
  | 0, 1 => [208, 214, 210, 218, 222, 216, 209, 220, 212, 206, 202, 200, 198, 192, 194, 204, 193, 196,
             207, 215, 213, 199, 223, 197, 219, 203, 195]
  | 0, 2 => [144, 150, 146, 154, 158, 152, 145, 156, 148, 142, 138, 136, 134, 128, 130, 140, 129, 132,
             143, 151, 149, 135, 159, 133, 155, 139, 131]
  | 1, 0 => [ 80,  86,  82,  90,  94,  88,  81,  92,  84,  78,  74,  72,  70,  64,  66,  76,  65,  68,
              79,  87,  85,  71,  95,  69,  91,  75,  67]
  | 1, 1 => [176, 182, 178, 186, 190, 184, 177, 188, 180, 174, 170, 168, 166, 160, 162, 172, 161, 164,
             175, 183, 181, 167, 191, 165, 187, 171, 163]
  | 1, 2 => [ 16,  22,  18,  26,  30,  24,  17,  28,  20,  14,  10,   8,   6,   0,   2,  12,   1,   4,
              15,  23,  21,   7,  31,   5,  27,  11,   3]
  | 2, 0 => [112, 118, 114, 122, 126, 120, 113, 124, 116, 110, 106, 104, 102,  96,  98, 108,  97, 100,
             111, 119, 117, 103, 127, 101, 123, 107,  99]
  | 2, 1 => [240, 246, 242, 250, 254, 248, 241, 252, 244, 238, 234, 232, 230, 224, 226, 236, 225, 228,
             239, 247, 245, 231, 255, 229, 251, 235, 227]
  | _, _ => [ 25,  93,  89, 217, 221, 153,  57, 157,  29, 205, 201, 137,  77,   9,  73, 141,  41,  13,
             173, 125,  61, 109, 189,  45, 249, 233, 105]

private def encode5t8b (t0 t1 t2 t3 t4 : Fin 3) : Fin 256 :=
  let idx := 9 * t2.val + 3 * t3.val + t4.val
  ⟨(encode5t8bBlock t0 t1).getD idx 0 % 256, Nat.mod_lt _ (by omega)⟩

private theorem unpack5t8b_disjoint_split :
    ∀ hi lo : Fin 16,
      let x : Fin 256 := ⟨hi.val * 16 + lo.val, by omega⟩
      let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true ∧
      tritDisjoint tr3 = true ∧ tritDisjoint tr4 = true := by
  decide

private theorem unpack5t8b_disjoint_all :
    ∀ x : Fin 256,
      let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true ∧
      tritDisjoint tr3 = true ∧ tritDisjoint tr4 = true := by
  intro x
  have hx : x = ⟨(x.val / 16) * 16 + (x.val % 16), by omega⟩ := Fin.ext (by dsimp only; omega)
  rw [hx]
  exact unpack5t8b_disjoint_split ⟨x.val / 16, by omega⟩ ⟨x.val % 16, by omega⟩

private theorem unpack5t8b_encode5t8b :
    ∀ t0 t1 t2 t3 t4 : Fin 3,
      let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b (encode5t8b t0 t1 t2 t3 t4)
      tritVal tr0 = fin3ToTrit t0 ∧
      tritVal tr1 = fin3ToTrit t1 ∧
      tritVal tr2 = fin3ToTrit t2 ∧
      tritVal tr3 = fin3ToTrit t3 ∧
      tritVal tr4 = fin3ToTrit t4 := by
  decide

theorem unpack_5t8b_sound_and_surjective :
    (∀ x : Fin 256,
      let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
      tritDisjoint tr0 = true ∧ tritDisjoint tr1 = true ∧ tritDisjoint tr2 = true ∧
      tritDisjoint tr3 = true ∧ tritDisjoint tr4 = true) ∧
    (∀ t0 t1 t2 t3 t4 : Fin 3,
      ∃ x : Fin 256,
        let (tr0, tr1, tr2, tr3, tr4) := unpack5t8b x
        tritVal tr0 = fin3ToTrit t0 ∧
        tritVal tr1 = fin3ToTrit t1 ∧
        tritVal tr2 = fin3ToTrit t2 ∧
        tritVal tr3 = fin3ToTrit t3 ∧
        tritVal tr4 = fin3ToTrit t4) := by
  refine ⟨unpack5t8b_disjoint_all, ?_⟩
  intro t0 t1 t2 t3 t4
  exact ⟨encode5t8b t0 t1 t2 t3 t4, unpack5t8b_encode5t8b t0 t1 t2 t3 t4⟩

/-! ## Section 5: Theorem 4 — Pigeonhole 4-Variable Impossibility for 5-Trit / 8-Bit Decoders -/

private theorem bitAt_eq_testBit (x i : Nat) : bitAt x i = x.testBit i := by
  unfold bitAt Nat.testBit
  rw [Nat.and_one_is_mod]
  cases h : (x >>> i) % 2 == 1
  · have hlt : (x >>> i) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hne : (x >>> i) % 2 ≠ 1 := by intro heq; rw [heq] at h; simp at h
    have h0 : (x >>> i) % 2 = 0 := by omega
    simp [h0]
  · have h1 : (x >>> i) % 2 = 1 := by simpa using h
    simp [h1]

private theorem xor_pow2_lt_256 (x : Fin 256) (j : Fin 8) :
    x.val ^^^ (1 <<< j.val) < 256 := by
  have hx : x.val < 2 ^ 8 := x.isLt
  have hj : 1 <<< j.val < 2 ^ 8 := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) j.isLt
  exact Nat.xor_lt_two_pow hx hj

private def flipBit (x : Fin 256) (j : Fin 8) : Fin 256 :=
  ⟨x.val ^^^ (1 <<< j.val), xor_pow2_lt_256 x j⟩

private theorem flipBit_involutive (x : Fin 256) (j : Fin 8) :
    flipBit (flipBit x j) j = x := by
  apply Fin.ext
  simp [flipBit, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem bitAt_flipBit (x : Fin 256) (j i : Fin 8) :
    bitAt (flipBit x j).val i.val =
      if i = j then !(bitAt x.val i.val) else bitAt x.val i.val := by
  rw [bitAt_eq_testBit, bitAt_eq_testBit]
  simp only [flipBit, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp
  · have hne : j.val ≠ i.val := fun heq => h (Fin.ext heq.symm)
    simp [h, hne]

private theorem countTrue_double_of_flip_inv (P : Fin 256 → Bool) (j : Fin 8)
    (hinv : ∀ x : Fin 256, P (flipBit x j) = P x) :
    countTrue P = 2 * countTrue (fun x => P x && !(bitAt x.val j.val)) := by
  have hsplit := countTrue_split P (fun x => bitAt x.val j.val)
  have hle1 :
      countTrue (fun x => P x && bitAt x.val j.val) ≤
      countTrue (fun x => P x && !(bitAt x.val j.val)) := by
    unfold countTrue
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    let l₁ := ((List.finRange 256).filter (fun x => P x && bitAt x.val j.val)).map (fun x => flipBit x j)
    let l₂ := (List.finRange 256).filter (fun x => P x && !(bitAt x.val j.val))
    have hinj : ∀ a b : Fin 256, flipBit a j = flipBit b j → a = b := by
      intro a b hab
      have := congrArg (fun z => flipBit z j) hab
      simpa [flipBit_involutive] using this
    have hnd : l₁.Nodup :=
      ((List.nodup_finRange 256).filter _).map (fun x => flipBit x j)
        (fun _ _ hne heq => hne (hinj _ _ heq))
    have hsub : ∀ y, y ∈ l₁ → y ∈ l₂ := by
      intro y hy
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [List.mem_filter] at hx ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      simp only [Bool.and_eq_true] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [hinv x]; exact hx.2.1
      · rw [bitAt_flipBit]; simp [hx.2.2]
    have hle := length_le_of_nodup_subset l₁ l₂ hnd hsub
    simpa [l₁, l₂] using hle
  have hle2 :
      countTrue (fun x => P x && !(bitAt x.val j.val)) ≤
      countTrue (fun x => P x && bitAt x.val j.val) := by
    unfold countTrue
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    let l₁ := ((List.finRange 256).filter (fun x => P x && !(bitAt x.val j.val))).map (fun x => flipBit x j)
    let l₂ := (List.finRange 256).filter (fun x => P x && bitAt x.val j.val)
    have hinj : ∀ a b : Fin 256, flipBit a j = flipBit b j → a = b := by
      intro a b hab
      have := congrArg (fun z => flipBit z j) hab
      simpa [flipBit_involutive] using this
    have hnd : l₁.Nodup :=
      ((List.nodup_finRange 256).filter _).map (fun x => flipBit x j)
        (fun _ _ hne heq => hne (hinj _ _ heq))
    have hsub : ∀ y, y ∈ l₁ → y ∈ l₂ := by
      intro y hy
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [List.mem_filter] at hx ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx ⊢
      refine ⟨?_, ?_⟩
      · rw [hinv x]; exact hx.2.1
      · rw [bitAt_flipBit]; simp [hx.2.2]
    have hle := length_le_of_nodup_subset l₁ l₂ hnd hsub
    simpa [l₁, l₂] using hle
  omega

private theorem countP_filter_remove_one {α : Type} [DecidableEq α] (l : List α)
    (hnd : l.Nodup) (a : α) :
    l.length ≤ (l.filter (fun x => x != a)).length + 1 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons, List.length_cons]
    by_cases hba : b = a
    · subst hba
      have hflt : t.filter (fun x => x != b) = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp [bne_iff_ne]
        intro hxb; exact hnd.1 (hxb ▸ hx)
      simp [hflt]
    · have hb : (b != a) = true := by simp [bne_iff_ne, hba]
      simp only [hb, ↓reduceIte, List.length_cons]
      have := ih hnd.2
      omega

private theorem exists_four_distinct_outside (i0 i1 i2 i3 : Fin 8) :
    ∃ j0 j1 j2 j3 : Fin 8,
      j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 ∧
      (∀ j, (j = j0 ∨ j = j1 ∨ j = j2 ∨ j = j3) →
        j ≠ i0 ∧ j ≠ i1 ∧ j ≠ i2 ∧ j ≠ i3) := by
  let l0 := List.finRange 8
  let l1 := l0.filter (fun x => x != i0)
  let l2 := l1.filter (fun x => x != i1)
  let l3 := l2.filter (fun x => x != i2)
  let l4 := l3.filter (fun x => x != i3)
  have hnd0 : l0.Nodup := List.nodup_finRange 8
  have hnd1 : l1.Nodup := hnd0.filter _
  have hnd2 : l2.Nodup := hnd1.filter _
  have hnd3 : l3.Nodup := hnd2.filter _
  have hnd4 : l4.Nodup := hnd3.filter _
  have hlen0 : l0.length = 8 := List.length_finRange
  have hlen1 : l0.length ≤ l1.length + 1 := countP_filter_remove_one l0 hnd0 i0
  have hlen2 : l1.length ≤ l2.length + 1 := countP_filter_remove_one l1 hnd1 i1
  have hlen3 : l2.length ≤ l3.length + 1 := countP_filter_remove_one l2 hnd2 i2
  have hlen4 : l3.length ≤ l4.length + 1 := countP_filter_remove_one l3 hnd3 i3
  have hge4 : 4 ≤ l4.length := by omega
  match hl4 : l4 with
  | j0 :: j1 :: j2 :: j3 :: _ =>
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd4
    have hmem : ∀ j, j ∈ l4 → j ≠ i0 ∧ j ≠ i1 ∧ j ≠ i2 ∧ j ≠ i3 := by
      intro j hj
      simp only [l4, l3, l2, l1, List.mem_filter, bne_iff_ne] at hj
      exact ⟨hj.1.1.1.2, hj.1.1.2, hj.1.2, hj.2⟩
    refine ⟨j0, j1, j2, j3,
      hnd4.1.1, hnd4.1.2.1, hnd4.1.2.2.1,
      hnd4.2.1.1, hnd4.2.1.2.1, hnd4.2.2.1.1, ?_⟩
    intro j hj
    apply hmem j
    rw [hl4]
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  | [] | [_] | [_, _] | [_, _, _] =>
    simp at hge4

private theorem dvd16_countTrue_of_dependsOnAtMost4 (f : Fin 256 → Bool)
    (hdep : DependsOnAtMost4 f) :
    ∃ q : Nat, countTrue f = 16 * q := by
  rcases hdep with ⟨i0, i1, i2, i3, g, hfg⟩
  rcases exists_four_distinct_outside i0 i1 i2 i3 with
    ⟨j0, j1, j2, j3, h01, h02, h03, h12, h13, h23, hout⟩
  have hfinv : ∀ j, (j = j0 ∨ j = j1 ∨ j = j2 ∨ j = j3) →
      ∀ x : Fin 256, f (flipBit x j) = f x := by
    intro j hj x
    rcases hout j hj with ⟨hi0, hi1, hi2, hi3⟩
    rw [hfg, hfg]
    rw [bitAt_flipBit, bitAt_flipBit, bitAt_flipBit, bitAt_flipBit]
    simp [hi0.symm, hi1.symm, hi2.symm, hi3.symm]
  let P1 : Fin 256 → Bool := fun x => f x && !(bitAt x.val j0.val)
  let P2 : Fin 256 → Bool := fun x => P1 x && !(bitAt x.val j1.val)
  let P3 : Fin 256 → Bool := fun x => P2 x && !(bitAt x.val j2.val)
  let P4 : Fin 256 → Bool := fun x => P3 x && !(bitAt x.val j3.val)
  have h1 : countTrue f = 2 * countTrue P1 :=
    countTrue_double_of_flip_inv f j0 (hfinv j0 (Or.inl rfl))
  have h2 : countTrue P1 = 2 * countTrue P2 := by
    apply countTrue_double_of_flip_inv P1 j1
    intro x; simp only [P1, hfinv j1 (Or.inr (Or.inl rfl)) x, bitAt_flipBit, h01, ↓reduceIte]
  have h3 : countTrue P2 = 2 * countTrue P3 := by
    apply countTrue_double_of_flip_inv P2 j2
    intro x; simp only [P2, P1, hfinv j2 (Or.inr (Or.inr (Or.inl rfl))) x, bitAt_flipBit,
      h02, h12, ↓reduceIte]
  have h4 : countTrue P3 = 2 * countTrue P4 := by
    apply countTrue_double_of_flip_inv P3 j3
    intro x; simp only [P3, P2, P1, hfinv j3 (Or.inr (Or.inr (Or.inr rfl))) x, bitAt_flipBit,
      h03, h13, h23, ↓reduceIte]
  refine ⟨countTrue P4, ?_⟩
  omega

private theorem lower_bound_5t_lane
    (D : Fin 256 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 256,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.2 = true)
    (hsurj : ∀ t0 t1 t2 t3 t4 : Fin 3, ∃ x : Fin 256,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2.1 = fin3ToTrit t2 ∧
      tritVal (D x).2.2.2.1 = fin3ToTrit t3 ∧
      tritVal (D x).2.2.2.2 = fin3ToTrit t4)
    (k : Fin 10) :
    81 ≤ countTrue (fun x => lane5t (D x) k) ∧
    162 ≤ countTrue (fun x => !(lane5t (D x) k)) := by
  let g : Fin 256 → Int × Int × Int × Int × Int :=
    fun x => (tritVal (D x).1, tritVal (D x).2.1, tritVal (D x).2.2.1,
              tritVal (D x).2.2.2.1, tritVal (D x).2.2.2.2)
  have hsurjG : ∀ t0 t1 t2 t3 t4 : Fin 3,
      ∃ x : Fin 256,
        g x = (fin3ToTrit t0, fin3ToTrit t1, fin3ToTrit t2, fin3ToTrit t3, fin3ToTrit t4) := by
    intro t0 t1 t2 t3 t4
    rcases hsurj t0 t1 t2 t3 t4 with ⟨x, h0, h1, h2, h3, h4⟩
    exact ⟨x, Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))⟩
  let insert5 (idx : Fin 5) (v u0 u1 u2 u3 : Fin 3) : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
    match idx with
    | ⟨0, _⟩ => (v, u0, u1, u2, u3)
    | ⟨1, _⟩ => (u0, v, u1, u2, u3)
    | ⟨2, _⟩ => (u0, u1, v, u2, u3)
    | ⟨3, _⟩ => (u0, u1, u2, v, u3)
    | ⟨4, _⟩ => (u0, u1, u2, u3, v)
  let eval5 (t : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3) : Int × Int × Int × Int × Int :=
    (fin3ToTrit t.1, fin3ToTrit t.2.1, fin3ToTrit t.2.2.1, fin3ToTrit t.2.2.2.1, fin3ToTrit t.2.2.2.2)
  let proj5 (x : Fin 256) (idx : Fin 5) : Int :=
    match idx with
    | ⟨0, _⟩ => tritVal (D x).1
    | ⟨1, _⟩ => tritVal (D x).2.1
    | ⟨2, _⟩ => tritVal (D x).2.2.1
    | ⟨3, _⟩ => tritVal (D x).2.2.2.1
    | ⟨4, _⟩ => tritVal (D x).2.2.2.2
  have heval5_inj : ∀ a b, eval5 a = eval5 b → a = b := by
    intro a b h
    simp only [eval5, Prod.mk.injEq] at h
    exact Prod.ext (fin3ToTrit_inj h.1)
      (Prod.ext (fin3ToTrit_inj h.2.1)
        (Prod.ext (fin3ToTrit_inj h.2.2.1)
          (Prod.ext (fin3ToTrit_inj h.2.2.2.1) (fin3ToTrit_inj h.2.2.2.2))))
  have hinsert5_inj : ∀ idx v1 u0 u1 u2 u3 v2 w0 w1 w2 w3,
      insert5 idx v1 u0 u1 u2 u3 = insert5 idx v2 w0 w1 w2 w3 →
      v1 = v2 ∧ u0 = w0 ∧ u1 = w1 ∧ u2 = w2 ∧ u3 = w3 := by
    intro idx v1 u0 u1 u2 u3 v2 w0 w1 w2 w3 h
    rcases idx with ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    | 1, _ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    | 2, _ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
    | 3, _ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.2.1, h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
    | 4, _ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.2.2, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hproj_eq : ∀ x idx v u0 u1 u2 u3,
      g x = eval5 (insert5 idx v u0 u1 u2 u3) → proj5 x idx = fin3ToTrit v := by
    intro x idx v u0 u1 u2 u3 h
    rcases idx with ⟨i, hi⟩
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
      simp only [g, eval5, insert5, Prod.mk.injEq] at h
      simp [proj5, h]
  have h81 : ∀ (idx : Fin 5) (v : Fin 3),
      81 ≤ countTrue (fun x => proj5 x idx == fin3ToTrit v) := by
    intro idx v
    let target : Fin 81 → Int × Int × Int × Int × Int := fun a =>
      let u0 : Fin 3 := ⟨a.val / 27, by omega⟩
      let u1 : Fin 3 := ⟨(a.val % 27) / 9, by omega⟩
      let u2 : Fin 3 := ⟨(a.val % 9) / 3, by omega⟩
      let u3 : Fin 3 := ⟨a.val % 3, by omega⟩
      eval5 (insert5 idx v u0 u1 u2 u3)
    apply le_countTrue_of_exists _ g target
    · intro a b hab
      have h1 := hinsert5_inj idx _ _ _ _ _ _ _ _ _ _ (heval5_inj _ _ hab)
      have e0 := congrArg Fin.val h1.2.1
      have e1 := congrArg Fin.val h1.2.2.1
      have e2 := congrArg Fin.val h1.2.2.2.1
      have e3 := congrArg Fin.val h1.2.2.2.2
      dsimp only at e0 e1 e2 e3
      exact Fin.ext (by omega)
    · intro a
      let t := insert5 idx v ⟨a.val / 27, by omega⟩ ⟨(a.val % 27) / 9, by omega⟩
        ⟨(a.val % 9) / 3, by omega⟩ ⟨a.val % 3, by omega⟩
      exact hsurjG t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
    · intro x a hgx
      simp [hproj_eq x idx v _ _ _ _ hgx]
  have h162 : ∀ (idx : Fin 5) (v : Fin 3),
      162 ≤ countTrue (fun x => proj5 x idx != fin3ToTrit v) := by
    intro idx v
    let other : Fin 2 → Fin 3 := fun b =>
      ⟨(v.val + 1 + b.val) % 3, Nat.mod_lt _ (by omega)⟩
    have hother_ne : ∀ b : Fin 2, fin3ToTrit (other b) ≠ fin3ToTrit v := by
      intro b h
      have hv := congrArg Fin.val (fin3ToTrit_inj h)
      simp only [other] at hv
      omega
    have hother_inj : ∀ b₁ b₂ : Fin 2, other b₁ = other b₂ → b₁ = b₂ := by
      intro b₁ b₂ h
      have hv := congrArg Fin.val h
      simp only [other] at hv
      exact Fin.ext (by omega)
    let target : Fin 162 → Int × Int × Int × Int × Int := fun a =>
      let b  : Fin 2 := ⟨a.val / 81, by omega⟩
      let r  : Nat := a.val % 81
      let u0 : Fin 3 := ⟨r / 27, by omega⟩
      let u1 : Fin 3 := ⟨(r % 27) / 9, by omega⟩
      let u2 : Fin 3 := ⟨(r % 9) / 3, by omega⟩
      let u3 : Fin 3 := ⟨r % 3, by omega⟩
      eval5 (insert5 idx (other b) u0 u1 u2 u3)
    apply le_countTrue_of_exists _ g target
    · intro a b hab
      have h1 := hinsert5_inj idx _ _ _ _ _ _ _ _ _ _ (heval5_inj _ _ hab)
      have eb := congrArg Fin.val (hother_inj _ _ h1.1)
      have e0 := congrArg Fin.val h1.2.1
      have e1 := congrArg Fin.val h1.2.2.1
      have e2 := congrArg Fin.val h1.2.2.2.1
      have e3 := congrArg Fin.val h1.2.2.2.2
      dsimp only at eb e0 e1 e2 e3
      exact Fin.ext (by omega)
    · intro a
      let r : Nat := a.val % 81
      let t := insert5 idx (other ⟨a.val / 81, by omega⟩) ⟨r / 27, by omega⟩ ⟨(r % 27) / 9, by omega⟩
        ⟨(r % 9) / 3, by omega⟩ ⟨r % 3, by omega⟩
      exact hsurjG t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
    · intro x a hgx
      simp [hproj_eq x idx _ _ _ _ _ hgx, bne_iff_ne, hother_ne]
  have hmono : ∀ (f₁ f₂ : Fin 256 → Bool), (∀ x, f₁ x = true → f₂ x = true) →
      countTrue f₁ ≤ countTrue f₂ := by
    intro f₁ f₂ himp
    unfold countTrue
    have : ∀ l : List (Fin 256), l.countP f₁ ≤ l.countP f₂ := by
      intro l
      induction l with
      | nil => exact Nat.le_refl 0
      | cons a t ih =>
        simp only [List.countP_cons]
        cases h1 : f₁ a
        · cases f₂ a <;> simp <;> omega
        · rw [himp a h1]; simp; omega
    exact this (List.finRange 256)
  rcases k with ⟨kv, hkv⟩
  match kv, hkv with
  | 0, _ =>
    refine ⟨Nat.le_trans (h81 ⟨0, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨0, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).1 (hdisj x).1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_pos_false_of_val_ne_one (D x).1 (hdisj x).1 hx]
  | 1, _ =>
    refine ⟨Nat.le_trans (h81 ⟨0, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨0, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).1 (hdisj x).1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_neg_false_of_val_ne_neg_one (D x).1 (hdisj x).1 hx]
  | 2, _ =>
    refine ⟨Nat.le_trans (h81 ⟨1, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨1, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.1 (hdisj x).2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_pos_false_of_val_ne_one (D x).2.1 (hdisj x).2.1 hx]
  | 3, _ =>
    refine ⟨Nat.le_trans (h81 ⟨1, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨1, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.1 (hdisj x).2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_neg_false_of_val_ne_neg_one (D x).2.1 (hdisj x).2.1 hx]
  | 4, _ =>
    refine ⟨Nat.le_trans (h81 ⟨2, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨2, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.2.1 (hdisj x).2.2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_pos_false_of_val_ne_one (D x).2.2.1 (hdisj x).2.2.1 hx]
  | 5, _ =>
    refine ⟨Nat.le_trans (h81 ⟨2, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨2, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.2.1 (hdisj x).2.2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_neg_false_of_val_ne_neg_one (D x).2.2.1 (hdisj x).2.2.1 hx]
  | 6, _ =>
    refine ⟨Nat.le_trans (h81 ⟨3, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨3, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.2.2.1 (hdisj x).2.2.2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_pos_false_of_val_ne_one (D x).2.2.2.1 (hdisj x).2.2.2.1 hx]
  | 7, _ =>
    refine ⟨Nat.le_trans (h81 ⟨3, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨3, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.2.2.1 (hdisj x).2.2.2.1 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_neg_false_of_val_ne_neg_one (D x).2.2.2.1 (hdisj x).2.2.2.1 hx]
  | 8, _ =>
    refine ⟨Nat.le_trans (h81 ⟨4, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨4, by omega⟩ ⟨2, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_pos_of_val_eq_one (D x).2.2.2.2 (hdisj x).2.2.2.2 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_pos_false_of_val_ne_one (D x).2.2.2.2 (hdisj x).2.2.2.2 hx]
  | 9, _ =>
    refine ⟨Nat.le_trans (h81 ⟨4, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_),
            Nat.le_trans (h162 ⟨4, by omega⟩ ⟨0, by omega⟩) (hmono _ _ ?_)⟩
    · intro x hx; simp only [proj5, beq_iff_eq, fin3ToTrit] at hx
      exact trit_neg_of_val_eq_neg_one (D x).2.2.2.2 (hdisj x).2.2.2.2 hx
    · intro x hx; simp only [proj5, bne_iff_ne, fin3ToTrit] at hx
      simp [lane5t, trit_neg_false_of_val_ne_neg_one (D x).2.2.2.2 (hdisj x).2.2.2.2 hx]

theorem unpack_5t8b_four_var_impossibility
    (D : Fin 256 → (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool))
    (hdisj : ∀ x : Fin 256,
      tritDisjoint (D x).1 = true ∧
      tritDisjoint (D x).2.1 = true ∧
      tritDisjoint (D x).2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.1 = true ∧
      tritDisjoint (D x).2.2.2.2 = true)
    (hsurj : ∀ t0 t1 t2 t3 t4 : Fin 3, ∃ x : Fin 256,
      tritVal (D x).1 = fin3ToTrit t0 ∧
      tritVal (D x).2.1 = fin3ToTrit t1 ∧
      tritVal (D x).2.2.1 = fin3ToTrit t2 ∧
      tritVal (D x).2.2.2.1 = fin3ToTrit t3 ∧
      tritVal (D x).2.2.2.2 = fin3ToTrit t4) :
    (∀ k : Fin 10,
      81 ≤ countTrue (fun x => lane5t (D x) k) ∧
      162 ≤ countTrue (fun x => !(lane5t (D x) k))) ∧
    (∀ k : Fin 10, ¬ DependsOnAtMost4 (fun x => lane5t (D x) k)) := by
  have hlb := lower_bound_5t_lane D hdisj hsurj
  refine ⟨hlb, ?_⟩
  intro k hdep
  rcases dvd16_countTrue_of_dependsOnAtMost4 (fun x => lane5t (D x) k) hdep with ⟨q, hq⟩
  have hsum := countTrue_add_not (fun x => lane5t (D x) k)
  have ⟨h81, h162⟩ := hlb k
  omega

/-! ## Section 6: Theorems 5 & 6 — Exact Ternary × INT4 & FP4 (E2M1) Circuits -/

theorem ternary_int4_exact5_sound (p n a0 a1 a2 a3 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, y4) := ternaryInt4Exact5 p n a0 a1 a2 a3
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 + 16 * boolToInt y4 =
      tritVal (p, n) * int4Signed a0 a1 a2 a3 + 8 ∧
    (int4Signed a0 a1 a2 a3 ≠ -8 → y4 = false) := by
  cases p <;> cases n <;> cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
    simp_all [tritDisjoint, ternaryInt4Exact5, lop3, tritVal, int4Signed, boolToInt]

theorem ternary_fp4_exact5_sound (p n s e1 e0 m0 : Bool)
    (hdisj : tritDisjoint (p, n) = true) :
    let (y0, y1, y2, y3, t4) := ternaryFp4Exact5 p n s e1 e0 m0
    boolToInt y0 + 2 * boolToInt y1 + 4 * boolToInt y2 + 8 * boolToInt y3 - 16 * boolToInt t4 =
      tritVal (p, n) * fp4Scaled2 s e1 e0 m0 := by
  cases p <;> cases n <;> cases s <;> cases e1 <;> cases e0 <;> cases m0 <;>
    simp_all [tritDisjoint, ternaryFp4Exact5, fp4ToMag4, lop3, tritVal, fp4Scaled2, boolToInt]

/-! ## Section 7: Theorem 7 — Universal 3:2 CSA `popcnt` Conservation over `Nat` -/

private theorem popcnt_unfold (n : Nat) : popcnt n = n % 2 + popcnt (n / 2) := by
  rw [popcnt]
  split
  · rename_i h; subst h; simp [popcnt]
  · rfl

private theorem csa32_bit_identity (x y z : Nat) (hx : x < 2) (hy : y < 2) (hz : z < 2) :
    x + y + z = (x ^^^ y ^^^ z) + 2 * ((x &&& y) ||| (y &&& z) ||| (x &&& z)) := by
  match x, y, z, hx, hy, hz with
  | 0, 0, 0, _, _, _ | 0, 0, 1, _, _, _ | 0, 1, 0, _, _, _ | 0, 1, 1, _, _, _
  | 1, 0, 0, _, _, _ | 1, 0, 1, _, _, _ | 1, 1, 0, _, _, _ | 1, 1, 1, _, _, _ => decide

private theorem mod_two_eq_testBit_zero (n : Nat) :
    n % 2 = if n.testBit 0 then 1 else 0 := by
  rw [Nat.testBit_zero]
  cases h : decide (n % 2 = 1)
  · have : n % 2 ≠ 1 := by simpa using h
    have : n % 2 < 2 := Nat.mod_lt n (by omega)
    simp; omega
  · have : n % 2 = 1 := by simpa using h
    simp [this]

private theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  rw [mod_two_eq_testBit_zero, Nat.testBit_xor, mod_two_eq_testBit_zero a, mod_two_eq_testBit_zero b]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

private theorem and_mod_two (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  rw [mod_two_eq_testBit_zero, Nat.testBit_and, mod_two_eq_testBit_zero a, mod_two_eq_testBit_zero b]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

private theorem or_mod_two (a b : Nat) : (a ||| b) % 2 = (a % 2) ||| (b % 2) := by
  rw [mod_two_eq_testBit_zero, Nat.testBit_or, mod_two_eq_testBit_zero a, mod_two_eq_testBit_zero b]
  cases a.testBit 0 <;> cases b.testBit 0 <;> rfl

theorem csa32_popcnt_conservation (a b c : Nat) :
    popcnt a + popcnt b + popcnt c =
      popcnt (a ^^^ b ^^^ c) + 2 * popcnt ((a &&& b) ||| (b &&& c) ||| (a &&& c)) := by
  if h0 : a = 0 ∧ b = 0 ∧ c = 0 then
    rcases h0 with ⟨rfl, rfl, rfl⟩
    simp [popcnt]
  else
    have hlt : a / 2 + b / 2 + c / 2 < a + b + c := by omega
    have ih := csa32_popcnt_conservation (a / 2) (b / 2) (c / 2)
    rw [popcnt_unfold a, popcnt_unfold b, popcnt_unfold c,
        popcnt_unfold (a ^^^ b ^^^ c),
        popcnt_unfold ((a &&& b) ||| (b &&& c) ||| (a &&& c))]
    simp only [xor_mod_two, Nat.xor_div_two,
               and_mod_two, Nat.and_div_two,
               or_mod_two, Nat.or_div_two]
    have hbit := csa32_bit_identity (a % 2) (b % 2) (c % 2)
      (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega)) (Nat.mod_lt c (by omega))
    omega
termination_by a + b + c

end TernaryLop3Circuits
