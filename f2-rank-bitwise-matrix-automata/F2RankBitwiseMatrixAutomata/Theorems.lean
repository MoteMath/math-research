/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import F2RankBitwiseMatrixAutomata.Defs

/-!
# Theorems (`f2-rank-bitwise-matrix-automata`)

Full proofs of the headline infinite theorems of Exact F2-Rank and Corank Block-Elimination Automaton Engine.
-/

namespace F2RankAutomaton

theorem vxor_zero_left {n : Nat} (v : Vec n) : vxor (vzero n) v = v := by
  funext i; simp [vxor, vzero]

theorem vxor_comm {n : Nat} (u v : Vec n) : vxor u v = vxor v u := by
  funext i; exact xor_comm (u i) (v i)

theorem foldXor_cast {m n : Nat} (h : m = n) (f : Fin m → Bool) (g : Fin n → Bool)
    (hfg : ∀ (i : Fin m), f i = g ⟨i.val, h ▸ i.isLt⟩) :
    foldXor m f = foldXor n g := by
  subst h
  exact foldXor_congr hfg

theorem foldXor_add (a b : Nat) (f : Fin (a + b) → Bool) :
    foldXor (a + b) f =
    xor (foldXor a (fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩))
        (foldXor b (fun j => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩)) := by
  induction b with
  | zero =>
    simp [foldXor]
  | succ b ih =>
    change foldXor ((a + b) + 1) f = _
    simp only [foldXor]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    rw [xor_assoc]

theorem foldXor_even_odd (n : Nat) (f : Fin n → Bool) :
    foldXor n f =
    xor (foldXor ((n + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩))
        (foldXor (n / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [foldXor]
    rw [ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    by_cases hpar : n % 2 = 0
    · have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have h2 : (n + 1) / 2 = n / 2 := by omega
      have hE : foldXor ((n + 1 + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩) =
                xor (foldXor ((n + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩))
                    (f ⟨n, Nat.lt_succ_self n⟩) := by
        rw [foldXor_cast h1 _ (fun a : Fin ((n + 1) / 2 + 1) => f ⟨2 * a.val, by omega⟩) (fun _ => rfl)]
        simp only [foldXor]
        congr 1
        congr 1
        apply Fin.ext; dsimp; omega
      have hO : foldXor ((n + 1) / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩) =
                foldXor (n / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩) :=
        foldXor_cast h2 _ _ (fun _ => rfl)
      rw [hE, hO]
      cases foldXor ((n + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩) <;>
      cases foldXor (n / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩) <;>
      cases f ⟨n, Nat.lt_succ_self n⟩ <;> rfl
    · have h1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      have h2 : (n + 1) / 2 = n / 2 + 1 := by omega
      have hE : foldXor ((n + 1 + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩) =
                foldXor ((n + 1) / 2) (fun a => f ⟨2 * a.val, by omega⟩) :=
        foldXor_cast h1 _ _ (fun _ => rfl)
      have hO : foldXor ((n + 1) / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩) =
                xor (foldXor (n / 2) (fun b => f ⟨2 * b.val + 1, by omega⟩))
                    (f ⟨n, Nat.lt_succ_self n⟩) := by
        rw [foldXor_cast h2 _ (fun b : Fin (n / 2 + 1) => f ⟨2 * b.val + 1, by omega⟩) (fun _ => rfl)]
        simp only [foldXor]
        congr 1
        congr 1
        apply Fin.ext; dsimp; omega
      rw [hE, hO, xor_assoc]

theorem matVec_zero {m n : Nat} (M : Mat m n) : matVec M (vzero n) = vzero m := by
  funext i
  simp only [matVec, vzero, Bool.and_false]
  exact foldXor_zero n

theorem matVec_zero_mat {m n : Nat} (v : Vec n) : matVec (matZero m n) v = vzero m := by
  funext i
  simp only [matVec, matZero, Bool.false_and, vzero]
  exact foldXor_zero n

namespace LinEquiv


theorem map_zero {m n : Nat} (e : LinEquiv m n) : e.toFun (vzero m) = vzero n := by
  have h := e.map_xor (vzero m) (vzero m)
  rw [vxor_self, vxor_self] at h
  exact h

end LinEquiv

theorem vecToNat_lt : {n : Nat} → (v : Vec n) → vecToNat v < 2 ^ n
  | 0, _ => by simp [vecToNat]
  | n + 1, v => by
    simp only [vecToNat]
    have ih := vecToNat_lt (fun i : Fin n => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
    cases v ⟨n, Nat.lt_succ_self n⟩ <;> simp <;> omega

theorem natToVec_vecToNat : {n : Nat} → (v : Vec n) → natToVec n (vecToNat v) = v
  | 0, v => by funext i; exact Fin.elim0 i
  | n + 1, v => by
    funext i
    simp only [natToVec, vecToNat]
    have ih := natToVec_vecToNat (fun j : Fin n => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have hlt := vecToNat_lt (fun j : Fin n => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    by_cases hi : i.val < n
    · simp only [hi, ↓reduceDIte]
      have hmod : (vecToNat (fun j : Fin n => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
                   if v ⟨n, Nat.lt_succ_self n⟩ then 2 ^ n else 0) % 2 ^ n =
                  vecToNat (fun j : Fin n => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) := by
        cases v ⟨n, Nat.lt_succ_self n⟩ <;> simp [Nat.mod_eq_of_lt hlt]
      rw [hmod]
      exact congrFun ih ⟨i.val, hi⟩
    · simp only [hi, ↓reduceDIte]
      have hval_i : i.val = n := by have := i.isLt; omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval_i
      rw [hi_eq]
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      cases hb : v ⟨n, Nat.lt_succ_self n⟩
      · simp [Nat.div_eq_of_lt hlt]
      · simp only [↓reduceIte]
        have hdiv : (vecToNat (fun j : Fin n => v ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + 2 ^ n) / 2 ^ n = 1 := by
          rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt hlt]
        rw [hdiv]
        rfl

theorem vecToNat_natToVec : {n : Nat} → (x : Nat) → x < 2 ^ n → vecToNat (natToVec n x) = x
  | 0, x, hx => by
    simp only [Nat.pow_zero] at hx
    simp only [vecToNat]
    omega
  | n + 1, x, hx => by
    simp only [vecToNat]
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hmod_lt : x % 2 ^ n < 2 ^ n := Nat.mod_lt x hpos
    have hsub : (fun i : Fin n => natToVec (n + 1) x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
                natToVec n (x % 2 ^ n) := by
      funext i
      simp [natToVec, i.isLt]
    rw [hsub, vecToNat_natToVec (x % 2 ^ n) hmod_lt]
    have hlast : natToVec (n + 1) x ⟨n, Nat.lt_succ_self n⟩ = ((x / 2 ^ n) % 2 == 1) := by
      simp [natToVec]
    rw [hlast]
    have hdiv_lt : x / 2 ^ n < 2 := by
      have : x < 2 * 2 ^ n := by omega
      exact (Nat.div_lt_iff_lt_mul hpos).mpr this
    have hdecomp : x = x % 2 ^ n + (x / 2 ^ n) * 2 ^ n := by
      have h1 := Nat.div_add_mod x (2 ^ n)
      rw [Nat.mul_comm] at h1
      omega
    cases hq : x / 2 ^ n with
    | zero =>
      rw [hq] at hdecomp; simp at hdecomp ⊢; omega
    | succ q =>
      have hq0 : q = 0 := by omega
      subst hq0
      rw [hq] at hdecomp; simp at hdecomp ⊢; omega

theorem vecEqZero_eq_true_iff : {n : Nat} → (v : Vec n) → (vecEqZero v = true ↔ v = vzero n)
  | 0, v => by
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · intro _; rfl
  | n + 1, v => by
    simp only [vecEqZero, Bool.and_eq_true, Bool.not_eq_true']
    rw [vecEqZero_eq_true_iff (fun i : Fin n => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
    constructor
    · rintro ⟨h1, h2⟩
      funext i
      by_cases hi : i.val < n
      · have := congrFun h1 ⟨i.val, hi⟩
        simpa [vzero] using this
      · have hval_i : i.val = n := by have := i.isLt; omega
        have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval_i
        rw [hi_eq, h2]; rfl
    · intro h
      refine ⟨?_, ?_⟩
      · funext i; exact congrFun h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      · exact congrFun h ⟨n, Nat.lt_succ_self n⟩

theorem countPred_true (N : Nat) : countPred N (fun _ => true) = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [countPred, ih]

theorem countPred_congr {N : Nat} {p q : Fin N → Bool} (h : ∀ i, p i = q i) :
    countPred N p = countPred N q := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [countPred]
    rw [ih (fun i => h _), h]

theorem countPred_clear_one {N : Nat} (p : Fin N → Bool) (k : Fin N) (hk : p k = true) :
    countPred N p = countPred N (fun i => if i == k then false else p i) + 1 := by
  induction N with
  | zero => exact Fin.elim0 k
  | succ N ih =>
    simp only [countPred]
    by_cases hkn : k.val = N
    · have hk_eq : k = ⟨N, Nat.lt_succ_self N⟩ := Fin.ext hkn
      subst hk_eq
      simp only [hk, ↓reduceIte, beq_self_eq_true, Bool.false_eq_true]
      have hcongr : countPred N (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
                    countPred N (fun i => if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) == ⟨N, Nat.lt_succ_self N⟩
                                          then false else p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
        apply countPred_congr
        intro i
        have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) ≠ ⟨N, Nat.lt_succ_self N⟩ := by
          intro heq
          have hv : i.val = N := congrArg Fin.val heq
          have := i.isLt
          omega
        simp [hne]
      rw [hcongr]
    · have hklt : k.val < N := by have := k.isLt; omega
      have hne_last : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) ≠ k := by
        intro heq
        exact hkn (congrArg Fin.val heq).symm
      have hbeq_last : ((⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) == k) = false := by
        simp [hne_last]
      simp only [hbeq_last, Bool.false_eq_true, ↓reduceIte]
      have hsub := ih (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨k.val, hklt⟩ hk
      rw [hsub]
      have hcongr : countPred N (fun i => if i == ⟨k.val, hklt⟩ then false else p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
                    countPred N (fun i => if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) == k then false
                                          else p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
        apply countPred_congr
        intro i
        by_cases hik : i.val = k.val
        · have h1 : i = ⟨k.val, hklt⟩ := Fin.ext hik
          have h2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) = k := Fin.ext hik
          simp [h1]
        · have h1 : i ≠ ⟨k.val, hklt⟩ := fun h => hik (congrArg Fin.val h)
          have h2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)) ≠ k := fun h => hik (congrArg Fin.val h)
          simp [beq_false_of_ne h1, beq_false_of_ne h2]
      rw [hcongr]
      omega

/-- Exact finite bijection invariance for predicate counts (proves cardinality of ker(M)). -/
theorem countPred_bij {A B : Nat} (p : Fin A → Bool) (q : Fin B → Bool)
    (f : (x : Fin A) → p x = true → Fin B)
    (g : (y : Fin B) → q y = true → Fin A)
    (hf_q : ∀ x hx, q (f x hx) = true)
    (hg_p : ∀ y hy, p (g y hy) = true)
    (hfg : ∀ x hx, g (f x hx) (hf_q x hx) = x)
    (hgf : ∀ y hy, f (g y hy) (hg_p y hy) = y) :
    countPred A p = countPred B q := by
  induction A generalizing q with
  | zero =>
    simp only [countPred]
    symm
    have hq0 : ∀ y, q y = false := by
      intro y
      cases hy : q y with
      | false => rfl
      | true => exact Fin.elim0 (g y hy)
    rw [countPred_congr hq0]
    clear hq0 hf_q hg_p hfg hgf f g q
    induction B with
    | zero => rfl
    | succ B ihB => simp [countPred, ihB]
  | succ A ih =>
    simp only [countPred]
    by_cases hlast : p ⟨A, Nat.lt_succ_self A⟩ = true
    · simp only [hlast, ↓reduceIte]
      let y0 := f ⟨A, Nat.lt_succ_self A⟩ hlast
      have hqy0 : q y0 = true := hf_q ⟨A, Nat.lt_succ_self A⟩ hlast
      let q' : Fin B → Bool := fun y => if y == y0 then false else q y
      rw [countPred_clear_one q y0 hqy0]
      congr 1
      have hq'_imp : ∀ y, q' y = true → y ≠ y0 ∧ q y = true := by
        intro y hy
        simp only [q'] at hy
        by_cases heq : y == y0
        · simp [heq] at hy
        · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hy
          exact ⟨by intro h; subst h; simp at heq, hy⟩
      have hgy_lt : ∀ y (hy : q' y = true), (g y (hq'_imp y hy).2).val < A := by
        intro y hy
        have ⟨hne, hqy⟩ := hq'_imp y hy
        have hlt := (g y hqy).isLt
        by_cases heq : (g y hqy).val = A
        · exfalso
          have hgeq : g y hqy = ⟨A, Nat.lt_succ_self A⟩ := Fin.ext heq
          have hfy := hgf y hqy
          have : f (g y hqy) (hg_p y hqy) = y0 := by
            simp only [y0]
            congr 1
          rw [this] at hfy
          exact hne hfy.symm
        · omega
      refine ih (fun x => p ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩) q'
        (fun x hx => f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx)
        (fun y hy => ⟨(g y (hq'_imp y hy).2).val, hgy_lt y hy⟩)
        ?hf_q' ?hg_p' ?hfg' ?hgf'
      case hf_q' =>
        intro x hx
        simp only [q']
        have hne : f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx ≠ y0 := by
          intro heq
          have h1 := hfg ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx
          have h2 := hfg ⟨A, Nat.lt_succ_self A⟩ hlast
          have h3 : g (f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx) (hf_q _ hx) =
                    g y0 hqy0 := by
            congr 1
          rw [h1, h2] at h3
          have hv : x.val = A := congrArg Fin.val h3
          have := x.isLt
          omega
        have hbeq : (f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx == y0) = false :=
          beq_false_of_ne hne
        simp [hbeq, hf_q]
      case hg_p' =>
        intro y hy
        exact hg_p y (hq'_imp y hy).2
      case hfg' =>
        intro x hx
        apply Fin.ext
        have h := hfg ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx
        exact congrArg Fin.val h |>.trans rfl
      case hgf' =>
        intro y hy
        exact hgf y (hq'_imp y hy).2
    · have hfalse : p ⟨A, Nat.lt_succ_self A⟩ = false := by
        cases hp : p ⟨A, Nat.lt_succ_self A⟩ <;> simp_all
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hgy_lt : ∀ y (hy : q y = true), (g y hy).val < A := by
        intro y hy
        have hlt := (g y hy).isLt
        by_cases heq : (g y hy).val = A
        · exfalso
          have hgeq : g y hy = ⟨A, Nat.lt_succ_self A⟩ := Fin.ext heq
          have hp := hg_p y hy
          rw [hgeq] at hp
          exact hlast hp
        · omega
      refine ih (fun x => p ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩) q
        (fun x hx => f ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx)
        (fun y hy => ⟨(g y hy).val, hgy_lt y hy⟩)
        ?hf_q' ?hg_p' ?hfg' ?hgf'
      case hf_q' => intro x hx; exact hf_q _ hx
      case hg_p' => intro y hy; exact hg_p y hy
      case hfg' =>
        intro x hx
        apply Fin.ext
        have h := hfg ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩ hx
        exact congrArg Fin.val h |>.trans rfl
      case hgf' =>
        intro y hy
        exact hgf y hy

theorem pow2_inj {a b : Nat} (h : 2 ^ a = 2 ^ b) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ b =>
      simp only [Nat.pow_zero, Nat.pow_succ] at h
      have := Nat.two_pow_pos b
      omega
  | succ a ih =>
    cases b with
    | zero =>
      simp only [Nat.pow_zero, Nat.pow_succ] at h
      have := Nat.two_pow_pos a
      omega
    | succ b =>
      simp only [Nat.pow_succ] at h
      have : 2 ^ a = 2 ^ b := by omega
      exact congrArg Nat.succ (ih this)

/-- Soundness of HasRank: exact cardinality of ker(M) over F_2^n is 2^(n - r). -/
theorem hasRank_kerCount {m n r : Nat} {M : Mat m n} (h : HasRank M r) :
    kerCount M = 2 ^ (n - r) := by
  rcases h with ⟨hrm, hrn, P, Q, hPQ⟩
  unfold kerCount
  rw [← countPred_true (2 ^ (n - r))]
  -- Construct an explicit bijection between ker(M) and Vec (n - r) via Q⁻¹!
  -- Given x < 2^n with M (natToVec n x) = 0, w := Q.invFun (natToVec n x) has w_i = false for i < r.
  -- Map x ↦ vecToNat (fun j : Fin (n - r) => w ⟨r + j.val, _⟩).
  -- Inverse: given y < 2^(n - r), u := natToVec (n - r) y, lift to w : Vec n with 0 on < r, u on ≥ r,
  -- and return vecToNat (Q.toFun w).
  let p : Fin (2 ^ n) → Bool := fun x => vecEqZero (matVec M (natToVec n x.val))
  let q : Fin (2 ^ (n - r)) → Bool := fun _ => true
  have hker_iff : ∀ v : Vec n, matVec M v = vzero m ↔
      ∀ i : Fin n, i.val < r → Q.invFun v i = false := by
    intro v
    constructor
    · intro hv i hi
      have h1 := hPQ (Q.invFun v)
      rw [Q.right_inv, hv, P.map_zero, matVec_diagRank hrn] at h1
      have h2 := congrFun h1 ⟨i.val, Nat.lt_of_lt_of_le hi hrm⟩
      simp only [vzero, hi, ↓reduceDIte] at h2
      exact h2.symm
    · intro hzero
      have h1 := hPQ (Q.invFun v)
      rw [Q.right_inv, matVec_diagRank hrn] at h1
      have h2 : P.toFun (matVec M v) = vzero m := by
        rw [h1]
        funext i
        by_cases hi : i.val < r
        · simp only [hi, ↓reduceDIte, vzero]
          exact hzero ⟨i.val, Nat.lt_of_lt_of_le hi hrn⟩ hi
        · simp [hi, vzero]
      have h3 := congrArg P.invFun h2
      rw [P.left_inv] at h3
      have h4 : P.invFun (vzero m) = vzero m := P.symm.map_zero
      rw [h3, h4]
  let f : (x : Fin (2 ^ n)) → p x = true → Fin (2 ^ (n - r)) := fun x _ =>
    let w := Q.invFun (natToVec n x.val)
    let u : Vec (n - r) := fun j => w ⟨r + j.val, by omega⟩
    ⟨vecToNat u, vecToNat_lt u⟩
  let g : (y : Fin (2 ^ (n - r))) → q y = true → Fin (2 ^ n) := fun y _ =>
    let u := natToVec (n - r) y.val
    let w : Vec n := fun i => if h : i.val < r then false else u ⟨i.val - r, by omega⟩
    let v := Q.toFun w
    ⟨vecToNat v, vecToNat_lt v⟩
  refine countPred_bij p q f g ?hf_q ?hg_p ?hfg ?hgf
  case hf_q => intro _ _; rfl
  case hg_p =>
    intro y _
    simp only [p, g]
    rw [vecEqZero_eq_true_iff, hker_iff]
    rw [natToVec_vecToNat, Q.left_inv]
    intro i hi
    simp [hi]
  case hfg =>
    intro x hx
    apply Fin.ext
    simp only [f, g]
    have hx0 : matVec M (natToVec n x.val) = vzero m := (vecEqZero_eq_true_iff _).mp hx
    have hzero := (hker_iff (natToVec n x.val)).mp hx0
    have hw_eq : (fun i : Fin n =>
        if h : i.val < r then false
        else natToVec (n - r) (vecToNat (fun j : Fin (n - r) => Q.invFun (natToVec n x.val) ⟨r + j.val, by omega⟩))
          ⟨i.val - r, by omega⟩) = Q.invFun (natToVec n x.val) := by
      funext i
      by_cases hi : i.val < r
      · simp only [hi, ↓reduceDIte]
        exact (hzero i hi).symm
      · simp only [hi, ↓reduceDIte]
        rw [natToVec_vecToNat]
        congr 1
        apply Fin.ext
        dsimp
        omega
    rw [hw_eq, Q.right_inv, vecToNat_natToVec x.val x.isLt]
  case hgf =>
    intro y _
    apply Fin.ext
    simp only [f, g]
    rw [natToVec_vecToNat, Q.left_inv]
    have hu_eq : (fun j : Fin (n - r) =>
        if h : (⟨r + j.val, by omega⟩ : Fin n).val < r then false
        else natToVec (n - r) y.val ⟨(⟨r + j.val, by omega⟩ : Fin n).val - r, by omega⟩) =
        natToVec (n - r) y.val := by
      funext j
      have hnot : ¬ (r + j.val < r) := by omega
      simp only [hnot, ↓reduceDIte]
      congr 1
      apply Fin.ext
      dsimp
      omega
    rw [hu_eq, vecToNat_natToVec y.val y.isLt]

/-- Uniqueness of F_2-rank (proved directly from exact 2^(n-r) kernel cardinality!). -/
theorem hasRank_unique {m n r1 r2 : Nat} {M : Mat m n}
    (h1 : HasRank M r1) (h2 : HasRank M r2) : r1 = r2 := by
  have hk1 := hasRank_kerCount h1
  have hk2 := hasRank_kerCount h2
  have hpow : 2 ^ (n - r1) = 2 ^ (n - r2) := hk1.symm.trans hk2
  have hsub : n - r1 = n - r2 := pow2_inj hpow
  have hr1 := h1.le_cols
  have hr2 := h2.le_cols
  omega

theorem hasNullity_unique {m n ν1 ν2 : Nat} {M : Mat m n}
    (h1 : HasNullity M ν1) (h2 : HasNullity M ν2) : ν1 = ν2 := by
  have hr := hasRank_unique h1.2 h2.2
  have hle1 := h1.1
  have hle2 := h2.1
  omega

theorem hasNullity_kerCount {m n ν : Nat} {M : Mat m n} (h : HasNullity M ν) :
    kerCount M = 2 ^ ν := by
  have hk := hasRank_kerCount h.2
  have hle := h.1
  have : n - (n - ν) = ν := by omega
  rw [this] at hk
  exact hk

theorem hasRank_zero {m n : Nat} : HasRank (matZero m n) 0 := by
  refine ⟨Nat.zero_le m, Nat.zero_le n, LinEquiv.refl m, LinEquiv.refl n, ?_⟩
  intro v
  simp only [LinEquiv.refl, id_eq, matVec_zero_mat]
  rw [matVec_diagRank (Nat.zero_le n)]
  funext i
  simp [vzero]

theorem hasRank_id (n : Nat) : HasRank (matId n) n := by
  refine ⟨Nat.le_refl n, Nat.le_refl n, LinEquiv.refl n, LinEquiv.refl n, ?_⟩
  intro v
  simp only [LinEquiv.refl, id_eq, matVec_id]
  rw [matVec_diagRank (Nat.le_refl n)]
  funext i
  simp [i.isLt]

theorem hasRank_of_inv {n : Nat} (A B : Mat n n)
    (hAB : matMul A B = matId n) (hBA : matMul B A = matId n) :
    HasRank A n := by
  refine ⟨Nat.le_refl n, Nat.le_refl n, LinEquiv.ofMatInv B A hBA hAB, LinEquiv.refl n, ?_⟩
  intro v
  simp only [LinEquiv.ofMatInv, LinEquiv.refl, id_eq]
  rw [← matVec_mul, hBA, matVec_id, matVec_diagRank (Nat.le_refl n)]
  funext i
  simp [i.isLt]

theorem matVec_blockMat {a b c d : Nat} (A : Mat a c) (B : Mat a d) (C : Mat b c) (D : Mat b d)
    (u : Vec c) (v : Vec d) :
    matVec (blockMat A B C D) (joinVec u v) =
    joinVec (vxor (matVec A u) (matVec B v)) (vxor (matVec C u) (matVec D v)) := by
  funext i
  simp only [matVec, joinVec, vxor]
  rw [foldXor_add c d]
  by_cases hi : i.val < a
  · simp only [hi, ↓reduceDIte]
    congr 1
    · apply foldXor_congr; intro j
      simp [blockMat, hi, j.isLt]
    · apply foldXor_congr; intro j
      have hnot : ¬ (c + j.val < c) := by omega
      simp only [blockMat, hi, hnot, ↓reduceDIte]
      have hfin : (⟨c + j.val - c, by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
      rw [hfin]
  · simp only [hi, ↓reduceDIte]
    congr 1
    · apply foldXor_congr; intro j
      simp [blockMat, hi, j.isLt]
    · apply foldXor_congr; intro j
      have hnot : ¬ (c + j.val < c) := by omega
      simp only [blockMat, hi, hnot, ↓reduceDIte]
      have hfin : (⟨c + j.val - c, by omega⟩ : Fin d) = j := Fin.ext (by dsimp; omega)
      rw [hfin]

theorem matVec_matXor {m n : Nat} (A B : Mat m n) (v : Vec n) :
    matVec (matXor A B) v = vxor (matVec A v) (matVec B v) := by
  funext i
  simp only [matVec, matXor, vxor]
  rw [← foldXor_xor]
  apply foldXor_congr; intro j
  exact and_xor_right (A i j) (B i j) (v j)

theorem matVec_outer {a b : Nat} (u : Vec a) (v : Vec b) (w : Vec b) :
    matVec (outerMat u v) w = fun i => u i && vdot v w := by
  funext i
  simp only [matVec, outerMat, vdot]
  rw [← foldXor_and_left]
  apply foldXor_congr; intro j
  cases u i <;> cases v j <;> cases w j <;> rfl

/-- Invariance of HasRank under arbitrary invertible F_2-linear equivalences. -/
theorem hasRank_of_equiv {m n m' n' r : Nat} {M : Mat m n} {M' : Mat m' n'}
    (hm : m = m') (hn : n = n')
    (P : LinEquiv m m') (Q : LinEquiv n' n)
    (hPMQ : ∀ v, P.toFun (matVec M (Q.toFun v)) = matVec M' v)
    (hr : HasRank M' r) : HasRank M r := by
  rcases hr with ⟨hrm', hrn', P', Q', hP'Q'⟩
  refine ⟨hm ▸ hrm', hn ▸ hrn',
    P.trans (P'.trans (LinEquiv.cast hm.symm)),
    (LinEquiv.cast hn).trans (Q'.trans Q), ?_⟩
  intro v
  subst hm; subst hn
  simp only [LinEquiv.trans, LinEquiv.cast, LinEquiv.refl, id_eq]
  rw [hPMQ, hP'Q']

theorem hasRank_congr {m n r : Nat} {M1 M2 : Mat m n}
    (h : ∀ i j, M1 i j = M2 i j) (hr : HasRank M2 r) : HasRank M1 r := by
  have heq : M1 = M2 := by funext i j; exact h i j
  rw [heq]; exact hr

/-- Exact F_2 Direct-Sum Rank Additivity (for arbitrary rectangular/square blocks). -/
theorem hasRank_directSum {a b c d rA rB : Nat}
    {A : Mat a c} {B : Mat b d}
    (hA : HasRank A rA) (hB : HasRank B rB) :
    HasRank (blockMat A (matZero a d) (matZero b c) B) (rA + rB) := by
  rcases hA with ⟨hAr, hAc, PA, QA, hPAQA⟩
  rcases hB with ⟨hBr, hBc, PB, QB, hPBQB⟩
  let P0 := LinEquiv.blockDiag PA PB
  let Q0 := LinEquiv.blockDiag QA QB
  let PackR := LinEquiv.packDirectSum a b rA rB hAr hBr
  let PackC := LinEquiv.packDirectSum c d rA rB hAc hBc
  refine ⟨by omega, by omega, P0.trans PackR, PackC.symm.trans Q0, ?_⟩
  intro v
  have h0 : P0.toFun (matVec (blockMat A (matZero a d) (matZero b c) B) (Q0.toFun (PackC.invFun v))) =
            joinVec (matVec (matDiagRank a c rA) (splitLeft (PackC.invFun v)))
                    (matVec (matDiagRank b d rB) (splitRight (PackC.invFun v))) := by
    simp only [P0, Q0, LinEquiv.blockDiag]
    rw [matVec_blockMat, matVec_zero_mat, matVec_zero_mat, vxor_zero_right, vxor_zero_left]
    simp only [splitLeft_joinVec, splitRight_joinVec, hPAQA, hPBQB]
  simp only [LinEquiv.trans, LinEquiv.symm]
  rw [h0, matVec_diagRank (by omega : rA + rB ≤ c + d)]
  funext i
  simp only [PackR, PackC, LinEquiv.packDirectSum, LinEquiv.ofFinBij, joinVec, splitLeft, splitRight,
    matVec_diagRank hAc, matVec_diagRank hBc]
  by_cases c1 : i.val < rA
  · have c12 : i.val < rA + rB := by omega
    have hlt_a : i.val < a := by omega
    simp [c1, c12, hlt_a]
  · by_cases c2 : i.val < rA + rB
    · have n_a : ¬ (a + (i.val - rA) < a) := by omega
      have hlt_rB : a + (i.val - rA) - a < rB := by omega
      simp only [c1, c2, n_a, hlt_rB, ↓reduceDIte]
      have n_rA' : ¬ (c + (a + (i.val - rA) - a) < rA) := by omega
      have n_c' : ¬ (c + (a + (i.val - rA) - a) < c) := by omega
      have hlt_crB' : c + (a + (i.val - rA) - a) < c + rB := by omega
      simp only [n_rA', n_c', hlt_crB', ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
    · by_cases c3 : i.val < a + rB
      · have hlt_a : i.val - rB < a := by omega
        have n_rA : ¬ (i.val - rB < rA) := by omega
        simp [c1, c2, c3, hlt_a, n_rA]
      · have n_a : ¬ (i.val < a) := by omega
        have n_rB : ¬ (i.val - a < rB) := by omega
        simp [c1, c2, c3, n_a, n_rB]

/-- Exact F_2 Schur-Complement Elimination with Explicit Invertible Pivot A. -/
theorem hasRank_schur_inv {a b c : Nat}
    {A : Mat a a} {Ainv : Mat a a} {B : Mat a c} {C : Mat b a} {D : Mat b c} {rS : Nat}
    (hAA : matMul A Ainv = matId a) (hAA' : matMul Ainv A = matId a)
    (hS : HasRank (matXor D (matMul C (matMul Ainv B))) rS) :
    HasRank (blockMat A B C D) (a + rS) := by
  let P := LinEquiv.rowShearDown (matVec (matMul C Ainv)) (matVec_xor _)
  let Q := LinEquiv.rowShearUp (matVec (matMul Ainv B)) (matVec_xor _)
  apply hasRank_of_equiv rfl rfl P Q
    (M' := blockMat A (matZero a c) (matZero b a) (matXor D (matMul C (matMul Ainv B))))
  · intro w
    rw [← joinVec_split w]
    let u := splitLeft w
    let v := splitRight w
    simp only [P, Q, LinEquiv.rowShearDown, LinEquiv.rowShearUp, splitLeft_joinVec, splitRight_joinVec]
    rw [matVec_blockMat, matVec_blockMat, matVec_zero_mat, matVec_zero_mat,
        vxor_zero_right, vxor_zero_left]
    simp only [splitLeft_joinVec, splitRight_joinVec]
    have hAB : matVec A (matVec (matMul Ainv B) v) = matVec B v := by
      rw [matVec_mul, ← matVec_mul A Ainv, hAA, matVec_id]
    have htop : vxor (matVec A (vxor u (matVec (matMul Ainv B) v))) (matVec B v) = matVec A u := by
      rw [matVec_xor, hAB, vxor_assoc, vxor_self, vxor_zero_right]
    have hCAu : matVec (matMul C Ainv) (matVec A u) = matVec C u := by
      rw [matVec_mul, ← matVec_mul Ainv A, hAA', matVec_id]
    have hbot : vxor (vxor (matVec C (vxor u (matVec (matMul Ainv B) v))) (matVec D v))
                     (matVec (matMul C Ainv) (matVec A u)) =
                matVec (matXor D (matMul C (matMul Ainv B))) v := by
      rw [matVec_xor, hCAu, matVec_matXor, matVec_mul C (matMul Ainv B)]
      funext i; simp only [vxor]
      cases matVec C u i <;> cases matVec C (matVec (matMul Ainv B) v) i <;> cases matVec D v i <;> rfl
    rw [htop, hbot]
  · exact hasRank_directSum (hasRank_of_inv A Ainv hAA hAA') hS

/-- Exact F_2 Isotropic Rank-1 Border Decoupling:
    If A is symmetric and A * x = u with u · x = 0, then
    [[A, u v^T], [v u^T, B]] ~ A ⊕ B (independent of B!). -/
theorem hasRank_isotropic_rank1_decouple {a b rA rB : Nat}
    {A : Mat a a} {B : Mat b b} {u : Vec a} {v : Vec b}
    (hAsym : ∀ i j, A i j = A j i)
    (x : Vec a) (hAx : matVec A x = u) (hiso : vdot u x = false)
    (hA : HasRank A rA) (hB : HasRank B rB) :
    HasRank (blockMat A (outerMat u v) (outerMat v u) B) (rA + rB) := by
  let P := LinEquiv.rowShearDown (matVec (outerMat v x)) (matVec_xor _)
  let Q := LinEquiv.rowShearUp (matVec (outerMat x v)) (matVec_xor _)
  apply hasRank_of_equiv rfl rfl P Q (M' := blockMat A (matZero a b) (matZero b a) B)
  · intro w
    rw [← joinVec_split w]
    let u0 := splitLeft w
    let v0 := splitRight w
    simp only [P, Q, LinEquiv.rowShearDown, LinEquiv.rowShearUp, splitLeft_joinVec, splitRight_joinVec]
    rw [matVec_blockMat, matVec_blockMat, matVec_zero_mat, matVec_zero_mat,
        vxor_zero_right, vxor_zero_left]
    simp only [splitLeft_joinVec, splitRight_joinVec]
    have hA_outer : matVec A (matVec (outerMat x v) v0) = matVec (outerMat u v) v0 := by
      funext i
      rw [matVec_outer]
      simp only [matVec, outerMat, vdot]
      rw [foldXor_congr (g := fun j => (A i j && x j) && foldXor b (fun k => v k && v0 k))]
      · rw [foldXor_and_right]
        have hi := congrFun hAx i
        simp only [matVec] at hi
        rw [hi, ← foldXor_and_left]
        apply foldXor_congr; intro j
        cases u i <;> cases v j <;> cases v0 j <;> rfl
      · intro j
        cases A i j <;> cases x j <;> cases foldXor b (fun k => v k && v0 k) <;> rfl
    have htop : vxor (matVec A (vxor u0 (matVec (outerMat x v) v0))) (matVec (outerMat u v) v0) =
                matVec A u0 := by
      rw [matVec_xor, hA_outer, vxor_assoc, vxor_self, vxor_zero_right]
    have hdot_Ax : vdot x (matVec A u0) = vdot u u0 := by
      simp only [vdot, matVec]
      rw [foldXor_congr (g := fun i => foldXor a (fun j => x i && (A i j && u0 j)))]
      · rw [foldXor_swap]
        apply foldXor_congr; intro j
        have hj := congrFun hAx j
        simp only [matVec] at hj
        rw [← hj]
        rw [← foldXor_and_right]
        apply foldXor_congr; intro i
        rw [hAsym j i]
        cases A i j <;> cases x i <;> cases u0 j <;> rfl
      · intro i
        rw [foldXor_and_left]
    have hdot_uv : vdot u (matVec (outerMat x v) v0) = false := by
      rw [matVec_outer]
      simp only [vdot]
      rw [foldXor_congr (g := fun i => (u i && x i) && foldXor b (fun k => v k && v0 k))]
      · rw [foldXor_and_right]
        have : foldXor a (fun i => u i && x i) = false := hiso
        rw [this]; rfl
      · intro i
        cases u i <;> cases x i <;> cases foldXor b (fun k => v k && v0 k) <;> rfl
    have hbot : vxor (vxor (matVec (outerMat v u) (vxor u0 (matVec (outerMat x v) v0))) (matVec B v0))
                     (matVec (outerMat v x) (matVec A u0)) = matVec B v0 := by
      rw [matVec_xor]
      have h1 : matVec (outerMat v u) (matVec (outerMat x v) v0) = vzero b := by
        funext i; rw [matVec_outer, hdot_uv]; simp [vzero]
      have h2 : matVec (outerMat v x) (matVec A u0) = matVec (outerMat v u) u0 := by
        funext i; rw [matVec_outer, matVec_outer, hdot_Ax]
      rw [h1, vxor_zero_right, h2]
      funext i; simp only [vxor]
      cases matVec (outerMat v u) u0 i <;> cases matVec B v0 i <;> rfl
    rw [htop, hbot]
  · exact hasRank_directSum hA hB

/-- Exact F_2 Antidiagonal / Bipartite Block Rank:
    [[0, B], [C, 0]] with B : Mat a b, C : Mat b a has rank rank(B) + rank(C). -/
theorem hasRank_antidiag {a b rB rC : Nat}
    {B : Mat a b} {C : Mat b a}
    (hB : HasRank B rB) (hC : HasRank C rC) :
    HasRank (blockMat (matZero a a) B C (matZero b b)) (rB + rC) := by
  let Q := LinEquiv.swapBlocks b a
  apply hasRank_of_equiv rfl (Nat.add_comm a b) (LinEquiv.refl (a + b)) Q
    (M' := blockMat B (matZero a a) (matZero b b) C)
  · intro w
    rw [← joinVec_split w]
    simp only [Q, LinEquiv.refl, LinEquiv.swapBlocks, id_eq, splitLeft_joinVec, splitRight_joinVec]
    rw [matVec_blockMat, matVec_blockMat, matVec_zero_mat, matVec_zero_mat,
        vxor_zero_left, vxor_zero_right, vxor_zero_right, vxor_zero_left]
  · exact hasRank_directSum hB hC

/-- Full-column-rank rectangular matrix: if the top b x b submatrix of B : Mat (b + d) b
    has full rank b, then B has rank b. -/
theorem hasRank_rect_tall_of_top_full {b d : Nat} {B : Mat (b + d) b}
    (hTop : HasRank (fun i j : Fin b => B ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right b d)⟩ j) b) :
    HasRank B b := by
  let B0 : Mat b b := fun i j => B ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right b d)⟩ j
  let B1 : Mat d b := fun i j => B ⟨b + i.val, Nat.add_lt_add_left i.isLt b⟩ j
  let eB0 := LinEquiv.ofHasRankFull hTop
  let P := LinEquiv.rowShearDown (fun u : Vec b => matVec B1 (eB0.invFun u))
    (fun u1 u2 => by rw [eB0.inv_map_xor, matVec_xor])
  have hB_eq : B = blockMat B0 (matZero b 0) B1 (matZero d 0) := by
    funext i j
    simp only [blockMat, B0, B1]
    by_cases hi : i.val < b
    · simp only [hi, j.isLt, ↓reduceDIte]
    · simp only [hi, j.isLt, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
  -- Apply P to B directly: P (B v) = joinVec (B0 v) 0
  have hM' : ∀ v : Vec b, P.toFun (matVec B v) =
      matVec (blockMat B0 (matZero b 0) (matZero d b) (matZero d 0)) (joinVec v (vzero 0)) := by
    intro v
    have hsplit : matVec B v = joinVec (matVec B0 v) (matVec B1 v) := by
      funext i
      simp only [matVec, joinVec, B0, B1]
      by_cases hi : i.val < b
      · simp [hi]
      · simp only [hi, ↓reduceDIte]
        apply foldXor_congr; intro j
        congr 2; apply Fin.ext; dsimp; omega
    rw [hsplit]
    simp only [P, LinEquiv.rowShearDown, splitLeft_joinVec, splitRight_joinVec]
    have hinv : eB0.invFun (matVec B0 v) = v := eB0.left_inv v
    rw [hinv, vxor_self]
    rw [matVec_blockMat, matVec_zero_mat, matVec_zero_mat, matVec_zero_mat,
        vxor_zero_right, vxor_zero_right]
  let hQ0 : LinEquiv (b + 0) b := LinEquiv.cast (Nat.add_zero b)
  apply hasRank_of_equiv rfl (Nat.add_zero b).symm P hQ0
    (M' := blockMat B0 (matZero b 0) (matZero d b) (matZero d 0))
  · intro w
    have hw : w = joinVec (splitLeft w) (vzero 0) := by
      funext i
      simp only [joinVec, splitLeft, vzero]
      have hi : i.val < b := by have := i.isLt; omega
      simp [hi]
    rw [hw]
    have hcast : hQ0.toFun (joinVec (splitLeft w) (vzero 0)) = splitLeft w := by
      funext i
      simp only [hQ0, LinEquiv.cast, LinEquiv.refl, id_eq, joinVec, splitLeft, i.isLt, ↓reduceDIte]
    rw [hcast]
    exact hM' (splitLeft w)
  · have := hasRank_directSum (A := B0) (B := matZero d 0) hTop hasRank_zero
    simpa using this

/-- Full-row-rank rectangular matrix: if the left b x b submatrix of C : Mat b (b + d)
    has full rank b, then C has rank b. -/
theorem hasRank_rect_wide_of_left_full {b d : Nat} {C : Mat b (b + d)}
    (hLeft : HasRank (fun i j : Fin b => C i ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right b d)⟩) b) :
    HasRank C b := by
  let C0 : Mat b b := fun i j => C i ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right b d)⟩
  let C1 : Mat b d := fun i j => C i ⟨b + j.val, Nat.add_lt_add_left j.isLt b⟩
  let eC0 := LinEquiv.ofHasRankFull hLeft
  let Q := LinEquiv.rowShearUp (fun v : Vec d => eC0.invFun (matVec C1 v))
    (fun v1 v2 => by rw [matVec_xor, eC0.inv_map_xor])
  let hP0 : LinEquiv b (b + 0) := LinEquiv.cast (Nat.add_zero b).symm
  apply hasRank_of_equiv (Nat.add_zero b).symm rfl hP0 Q
    (M' := blockMat C0 (matZero b d) (matZero 0 b) (matZero 0 d))
  · intro w
    rw [← joinVec_split w]
    let u := splitLeft w
    let v := splitRight w
    have hsplit : matVec C (Q.toFun (joinVec u v)) =
        vxor (matVec C0 (vxor u (eC0.invFun (matVec C1 v)))) (matVec C1 v) := by
      funext i
      simp only [matVec, vxor, Q, LinEquiv.rowShearUp, splitLeft_joinVec, splitRight_joinVec]
      rw [foldXor_add b d]
      congr 1
      · apply foldXor_congr; intro j
        simp [joinVec, j.isLt, C0, vxor]
      · apply foldXor_congr; intro j
        have hnot : ¬ (b + j.val < b) := by omega
        simp only [joinVec, hnot, ↓reduceDIte, C1]
        congr 2; apply Fin.ext; dsimp; omega
    rw [hsplit, matVec_xor]
    have hright : matVec C0 (eC0.invFun (matVec C1 v)) = matVec C1 v := eC0.right_inv (matVec C1 v)
    rw [hright, vxor_assoc, vxor_self, vxor_zero_right]
    rw [matVec_blockMat, matVec_zero_mat, matVec_zero_mat, matVec_zero_mat,
        vxor_zero_right, vxor_zero_right]
    funext i
    simp only [hP0, LinEquiv.cast, LinEquiv.refl, id_eq, joinVec]
    have hi : i.val < b := by have := i.isLt; omega
    simp only [hi, ↓reduceDIte]
    rfl
  · have := hasRank_directSum (A := C0) (B := matZero 0 d) hLeft hasRank_zero
    simpa using this

theorem hasRank_cast_rows {m m' n r : Nat} (hm : m = m') (M : Mat m n) (M' : Mat m' n)
    (heq : ∀ (i : Fin m) (j : Fin n), M i j = M' ⟨i.val, hm ▸ i.isLt⟩ j)
    (h : HasRank M' r) : HasRank M r := by
  subst hm
  exact hasRank_congr heq h

theorem hasRank_cast_cols {m n n' r : Nat} (hn : n = n') (M : Mat m n) (M' : Mat m n')
    (heq : ∀ (i : Fin m) (j : Fin n), M i j = M' i ⟨j.val, hn ▸ j.isLt⟩)
    (h : HasRank M' r) : HasRank M r := by
  subst hn
  exact hasRank_congr heq h

/-! ## Section 4: Pure-Silicon Bit Arithmetic & Theorem 2 (Dbar Involution & D Parity Nullity) -/

theorem popcountAux_ge (fuel n : Nat) (h : n ≤ fuel) :
    popcountAux fuel n = if n == 0 then 0 else (n % 2) + popcountAux (fuel - 1) (n / 2) := by
  cases fuel with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ f =>
    simp [popcountAux]

theorem popcountAux_indep (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    popcountAux f1 n = popcountAux f2 n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    rw [popcountAux_ge f1 n h1, popcountAux_ge f2 n h2]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · have hbeq : (n == 0) = false := beq_false_of_ne hn0
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact ih (n / 2) (by omega) (f1 - 1) (f2 - 1) (by omega) (by omega)

theorem popcount_step (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  by_cases hn0 : n = 0
  · subst hn0; rfl
  · simp only [popcount]
    rw [popcountAux_ge n n (Nat.le_refl n)]
    have hbeq : (n == 0) = false := beq_false_of_ne hn0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact popcountAux_indep (n - 1) (n / 2) (n / 2) (by omega) (Nat.le_refl _)

theorem popParityAux_ge (fuel n : Nat) (h : n ≤ fuel) :
    popParityAux fuel n = if n == 0 then false else xor (n % 2 == 1) (popParityAux (fuel - 1) (n / 2)) := by
  cases fuel with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ f =>
    simp [popParityAux]

theorem popParityAux_indep (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    popParityAux f1 n = popParityAux f2 n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    rw [popParityAux_ge f1 n h1, popParityAux_ge f2 n h2]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · have hbeq : (n == 0) = false := beq_false_of_ne hn0
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact ih (n / 2) (by omega) (f1 - 1) (f2 - 1) (by omega) (by omega)

theorem popParity_step (n : Nat) : popParity n = xor (n % 2 == 1) (popParity (n / 2)) := by
  by_cases hn0 : n = 0
  · subst hn0; rfl
  · simp only [popParity]
    rw [popParityAux_ge n n (Nat.le_refl n)]
    have hbeq : (n == 0) = false := beq_false_of_ne hn0
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact popParityAux_indep (n - 1) (n / 2) (n / 2) (by omega) (Nat.le_refl _)

theorem popParity_eq_popcount (n : Nat) : popParity n = (popcount n % 2 == 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ k =>
      rw [popParity_step, popcount_step]
      have hlt : (k + 1) / 2 < k + 1 := by omega
      rw [ih _ hlt]
      have h1 : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by omega
      have h2 : popcount ((k + 1) / 2) % 2 = 0 ∨ popcount ((k + 1) / 2) % 2 = 1 := by omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2] <;> omega

theorem ctzParityAux_ge (fuel n : Nat) (h : n ≤ fuel) :
    ctzParityAux fuel n =
      if n == 0 then false else if n % 2 == 1 then false else !(ctzParityAux (fuel - 1) (n / 2)) := by
  cases fuel with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ f =>
    simp [ctzParityAux]

theorem ctzParityAux_indep (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    ctzParityAux f1 n = ctzParityAux f2 n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    rw [ctzParityAux_ge f1 n h1, ctzParityAux_ge f2 n h2]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · have hbeq : (n == 0) = false := beq_false_of_ne hn0
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      by_cases hm : n % 2 == 1
      · simp [hm]
      · simp only [hm, Bool.false_eq_true, ↓reduceIte]
        congr 1
        exact ih (n / 2) (by omega) (f1 - 1) (f2 - 1) (by omega) (by omega)

theorem ctzParity_succ (n : Nat) :
    ctzParity (n + 1) = if (n + 1) % 2 == 1 then false else !(ctzParity ((n + 1) / 2)) := by
  simp only [ctzParity]
  rw [ctzParityAux_ge (n + 1) (n + 1) (Nat.le_refl _)]
  have hne : (n + 1 == 0) = false := beq_false_of_ne (by omega)
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  by_cases hm : (n + 1) % 2 == 1
  · simp [hm]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact ctzParityAux_indep n ((n + 1) / 2) ((n + 1) / 2) (by omega) (Nat.le_refl _)

theorem land_div_two (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_div_two, Nat.testBit_div_two]

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_div_two, Nat.testBit_div_two]

theorem testBit_zero_eq_mod_two (x : Nat) : x.testBit 0 = (x % 2 == 1) := by
  rw [Nat.testBit_zero]
  have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem land_mod_two_eq_one (a b : Nat) : ((a &&& b) % 2 == 1) = ((a % 2 == 1) && (b % 2 == 1)) := by
  rw [← testBit_zero_eq_mod_two, ← testBit_zero_eq_mod_two, ← testBit_zero_eq_mod_two]
  exact Nat.testBit_and a b 0

theorem xor_mod_two_eq_one (a b : Nat) : ((a ^^^ b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  rw [← testBit_zero_eq_mod_two, ← testBit_zero_eq_mod_two, ← testBit_zero_eq_mod_two]
  exact Nat.testBit_xor a b 0

theorem M0Entry_sym (i j : Nat) : M0Entry i j = M0Entry j i := by
  simp only [M0Entry, Nat.add_comm, Nat.xor_comm]

theorem M1Entry_sym (i j : Nat) : M1Entry i j = M1Entry j i := by
  simp only [M1Entry, Nat.add_comm i j, Nat.xor_comm]

theorem DEntry_sym (i j : Nat) : DEntry i j = DEntry j i := by
  simp only [DEntry, M0Entry_sym, M1Entry_sym]

theorem DbarEntry_sym (i j : Nat) : DbarEntry i j = DbarEntry j i := by
  simp only [DbarEntry, DEntry_sym]

/-! ### Exact LSB Parity-Split Recurrences for M0, M1, D, Dbar -/

theorem M0Entry_even_even (a b : Nat) : M0Entry (2 * a) (2 * b) = M0Entry a b := by
  simp only [M0Entry]
  rw [popParity_step, land_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : (2 * a + 2 * b) % 2 = 0 := by omega
  have h2 : (2 * a + 2 * b) / 2 = a + b := by omega
  have h3 : (2 * a) / 2 = a := by omega
  have h4 : (2 * b) / 2 = b := by omega
  rw [h1, h2, h3, h4]; simp

theorem M0Entry_even_odd (a b : Nat) : M0Entry (2 * a) (2 * b + 1) = !(M0Entry a b) := by
  simp only [M0Entry]
  rw [popParity_step, land_mod_two_eq_one, xor_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : (2 * a + (2 * b + 1)) % 2 = 1 := by omega
  have h2 : (2 * a) % 2 = 0 := by omega
  have h3 : (2 * b + 1) % 2 = 1 := by omega
  have h4 : (2 * a + (2 * b + 1)) / 2 = a + b := by omega
  have h5 : (2 * a) / 2 = a := by omega
  have h6 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, h3, h4, h5, h6]; cases popParity ((a + b) &&& (a ^^^ b)) <;> rfl

theorem M0Entry_odd_even (a b : Nat) : M0Entry (2 * a + 1) (2 * b) = !(M0Entry a b) := by
  rw [M0Entry_sym, M0Entry_even_odd, M0Entry_sym]

theorem M0Entry_odd_odd (a b : Nat) : M0Entry (2 * a + 1) (2 * b + 1) = M1Entry a b := by
  simp only [M0Entry, M1Entry]
  rw [popParity_step, land_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : ((2 * a + 1) + (2 * b + 1)) % 2 = 0 := by omega
  have h2 : ((2 * a + 1) + (2 * b + 1)) / 2 = a + b + 1 := by omega
  have h3 : (2 * a + 1) / 2 = a := by omega
  have h4 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, h3, h4]; simp

theorem M1Entry_even_even (a b : Nat) : M1Entry (2 * a) (2 * b) = M0Entry a b := by
  simp only [M1Entry, M0Entry]
  rw [popParity_step, land_mod_two_eq_one, xor_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : (2 * a) % 2 = 0 := by omega
  have h2 : (2 * b) % 2 = 0 := by omega
  have h3 : (2 * a + 2 * b + 1) / 2 = a + b := by omega
  have h4 : (2 * a) / 2 = a := by omega
  have h5 : (2 * b) / 2 = b := by omega
  rw [h1, h2, h3, h4, h5]; simp

theorem M1Entry_even_odd (a b : Nat) : M1Entry (2 * a) (2 * b + 1) = M1Entry a b := by
  simp only [M1Entry]
  rw [popParity_step, land_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : (2 * a + (2 * b + 1) + 1) % 2 = 0 := by omega
  have h2 : (2 * a + (2 * b + 1) + 1) / 2 = a + b + 1 := by omega
  have h3 : (2 * a) / 2 = a := by omega
  have h4 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, h3, h4]; simp

theorem M1Entry_odd_even (a b : Nat) : M1Entry (2 * a + 1) (2 * b) = M1Entry a b := by
  rw [M1Entry_sym, M1Entry_even_odd, M1Entry_sym]

theorem M1Entry_odd_odd (a b : Nat) : M1Entry (2 * a + 1) (2 * b + 1) = M1Entry a b := by
  simp only [M1Entry]
  rw [popParity_step, land_mod_two_eq_one, xor_mod_two_eq_one, land_div_two, xor_div_two]
  have h1 : (2 * a + 1) % 2 = 1 := by omega
  have h2 : (2 * b + 1) % 2 = 1 := by omega
  have h3 : ((2 * a + 1) + (2 * b + 1) + 1) / 2 = a + b + 1 := by omega
  have h4 : (2 * a + 1) / 2 = a := by omega
  have h5 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, h3, h4, h5]; simp

theorem DEntry_even_even (a b : Nat) : DEntry (2 * a) (2 * b) = false := by
  simp [DEntry, M0Entry_even_even, M1Entry_even_even]

theorem DEntry_odd_odd (a b : Nat) : DEntry (2 * a + 1) (2 * b + 1) = false := by
  simp [DEntry, M0Entry_odd_odd, M1Entry_odd_odd]

theorem DEntry_even_odd (a b : Nat) : DEntry (2 * a) (2 * b + 1) = DbarEntry a b := by
  simp only [DEntry, DbarEntry, M0Entry_even_odd, M1Entry_even_odd]
  cases M0Entry a b <;> cases M1Entry a b <;> rfl

theorem DEntry_odd_even (a b : Nat) : DEntry (2 * a + 1) (2 * b) = DbarEntry a b := by
  rw [DEntry_sym, DEntry_even_odd, DbarEntry_sym]

/-- Exact closed form for the carry-defect entry: D(i, j) = ctz((i ^ j) + 1) mod 2. -/
theorem DEntry_eq_ctzParity (i j : Nat) : DEntry i j = ctzParity ((i ^^^ j) + 1) := by
  induction hsum : i + j using Nat.strongRecOn generalizing i j with
  | ind s ih =>
    let a := i / 2
    let b := j / 2
    have him : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hjm : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases him with hi0 | hi1 <;> rcases hjm with hj0 | hj1
    · have hi' : i = 2 * a := by omega
      have hj' : j = 2 * b := by omega
      rw [hi', hj', DEntry_even_even, ctzParity_succ]
      have hx0 : (2 * a ^^^ 2 * b) % 2 = 0 := by
        have hx := xor_mod_two_eq_one (2 * a) (2 * b)
        have h2a : (2 * a) % 2 = 0 := by omega
        have h2b : (2 * b) % 2 = 0 := by omega
        rw [h2a, h2b] at hx; simp only [show (0 == 1) = false by rfl, xor_false_left] at hx
        have hcases : (2 * a ^^^ 2 * b) % 2 = 0 ∨ (2 * a ^^^ 2 * b) % 2 = 1 := by omega
        rcases hcases with h | h
        · exact h
        · rw [h] at hx; cases hx
      have hmod : ((2 * a ^^^ 2 * b) + 1) % 2 = 1 := by omega
      simp [hmod]
    · have hi' : i = 2 * a := by omega
      have hj' : j = 2 * b + 1 := by omega
      rw [hi', hj', DEntry_even_odd, ctzParity_succ]
      have hx1 : (2 * a ^^^ (2 * b + 1)) % 2 = 1 := by
        have hx := xor_mod_two_eq_one (2 * a) (2 * b + 1)
        have h2a : (2 * a) % 2 = 0 := by omega
        have h2b : (2 * b + 1) % 2 = 1 := by omega
        rw [h2a, h2b] at hx; simp only [show (0 == 1) = false by rfl, show (1 == 1) = true by rfl, xor_false_left] at hx
        have hcases : (2 * a ^^^ (2 * b + 1)) % 2 = 0 ∨ (2 * a ^^^ (2 * b + 1)) % 2 = 1 := by omega
        rcases hcases with h | h
        · rw [h] at hx; cases hx
        · exact h
      have hmod0 : ((2 * a ^^^ (2 * b + 1)) + 1) % 2 = 0 := by omega
      have hxd : (2 * a ^^^ (2 * b + 1)) / 2 = a ^^^ b := by
        rw [xor_div_two]
        have h1 : (2 * a) / 2 = a := by omega
        have h2 : (2 * b + 1) / 2 = b := by omega
        rw [h1, h2]
      have hdiv : ((2 * a ^^^ (2 * b + 1)) + 1) / 2 = (a ^^^ b) + 1 := by omega
      rw [hmod0, hdiv]
      simp only [show (0 == 1) = false by rfl, Bool.false_eq_true, ↓reduceIte, DbarEntry]
      rw [ih (a + b) (by omega) a b rfl]
    · have hi' : i = 2 * a + 1 := by omega
      have hj' : j = 2 * b := by omega
      rw [hi', hj', DEntry_odd_even, ctzParity_succ]
      have hx1 : ((2 * a + 1) ^^^ 2 * b) % 2 = 1 := by
        have hx := xor_mod_two_eq_one (2 * a + 1) (2 * b)
        have h2a : (2 * a + 1) % 2 = 1 := by omega
        have h2b : (2 * b) % 2 = 0 := by omega
        rw [h2a, h2b] at hx; simp only [show (0 == 1) = false by rfl, show (1 == 1) = true by rfl, xor_false_right] at hx
        have hcases : ((2 * a + 1) ^^^ 2 * b) % 2 = 0 ∨ ((2 * a + 1) ^^^ 2 * b) % 2 = 1 := by omega
        rcases hcases with h | h
        · rw [h] at hx; cases hx
        · exact h
      have hmod0 : (((2 * a + 1) ^^^ 2 * b) + 1) % 2 = 0 := by omega
      have hxd : ((2 * a + 1) ^^^ 2 * b) / 2 = a ^^^ b := by
        rw [xor_div_two]
        have h1 : (2 * a + 1) / 2 = a := by omega
        have h2 : (2 * b) / 2 = b := by omega
        rw [h1, h2]
      have hdiv : (((2 * a + 1) ^^^ 2 * b) + 1) / 2 = (a ^^^ b) + 1 := by omega
      rw [hmod0, hdiv]
      simp only [show (0 == 1) = false by rfl, Bool.false_eq_true, ↓reduceIte, DbarEntry]
      rw [ih (a + b) (by omega) a b rfl]
    · have hi' : i = 2 * a + 1 := by omega
      have hj' : j = 2 * b + 1 := by omega
      rw [hi', hj', DEntry_odd_odd, ctzParity_succ]
      have hx0 : ((2 * a + 1) ^^^ (2 * b + 1)) % 2 = 0 := by
        have hx := xor_mod_two_eq_one (2 * a + 1) (2 * b + 1)
        have h2a : (2 * a + 1) % 2 = 1 := by omega
        have h2b : (2 * b + 1) % 2 = 1 := by omega
        rw [h2a, h2b] at hx; simp only [show (1 == 1) = true by rfl, xor_self] at hx
        have hcases : ((2 * a + 1) ^^^ (2 * b + 1)) % 2 = 0 ∨ ((2 * a + 1) ^^^ (2 * b + 1)) % 2 = 1 := by omega
        rcases hcases with h | h
        · exact h
        · rw [h] at hx; cases hx
      have hmod : (((2 * a + 1) ^^^ (2 * b + 1)) + 1) % 2 = 1 := by omega
      simp [hmod]

/-! ### MSB Anti-Diagonal Shift Laws for Dbar & Exact F_2-Involution Dbar(2^d)^2 = I -/

theorem DEntry_msb_diag (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DEntry (i + 2 ^ d) (j + 2 ^ d) = DEntry i j := by
  induction d generalizing i j with
  | zero =>
    simp only [Nat.pow_zero] at hi hj ⊢
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; decide
  | succ d ih =>
    let a := i / 2
    let b := j / 2
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
    have him : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hjm : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases him with hi0 | hi1 <;> rcases hjm with hj0 | hj1
    · have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) := by omega
      have h2 : j + 2 ^ (d + 1) = 2 * (b + 2 ^ d) := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h2, DEntry_even_even, h3, h4, DEntry_even_even]
    · have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) := by omega
      have h2 : j + 2 ^ (d + 1) = 2 * (b + 2 ^ d) + 1 := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h2, DEntry_even_odd, h3, h4, DEntry_even_odd]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
    · have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) + 1 := by omega
      have h2 : j + 2 ^ (d + 1) = 2 * (b + 2 ^ d) := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h2, DEntry_odd_even, h3, h4, DEntry_odd_even]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
    · have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) + 1 := by omega
      have h2 : j + 2 ^ (d + 1) = 2 * (b + 2 ^ d) + 1 := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h2, DEntry_odd_odd, h3, h4, DEntry_odd_odd]

theorem DEntry_msb_off (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DEntry (i + 2 ^ d) j = xor (DEntry i j) (i + j == 2 ^ d - 1) := by
  induction d generalizing i j with
  | zero =>
    simp only [Nat.pow_zero] at hi hj ⊢
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; decide
  | succ d ih =>
    let a := i / 2
    let b := j / 2
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
    have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    have him : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hjm : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases him with hi0 | hi1 <;> rcases hjm with hj0 | hj1
    · have hne : (i + j == 2 ^ (d + 1) - 1) = false := by
        simp only [beq_eq_false_iff_ne]; omega
      rw [hne]
      have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h4, DEntry_even_even, h3, DEntry_even_even]; rfl
    · have heq : (i + j == 2 ^ (d + 1) - 1) = (a + b == 2 ^ d - 1) := by
        by_cases hc : a + b = 2 ^ d - 1
        · have hc2 : i + j = 2 ^ (d + 1) - 1 := by omega
          simp [hc, hc2]
        · have hc2 : i + j ≠ 2 ^ (d + 1) - 1 := by omega
          simp [beq_false_of_ne hc, beq_false_of_ne hc2]
      rw [heq]
      have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h4, DEntry_even_odd, h3, DEntry_even_odd]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
      cases DEntry a b <;> cases (a + b == 2 ^ d - 1) <;> rfl
    · have heq : (i + j == 2 ^ (d + 1) - 1) = (a + b == 2 ^ d - 1) := by
        by_cases hc : a + b = 2 ^ d - 1
        · have hc2 : i + j = 2 ^ (d + 1) - 1 := by omega
          simp [hc, hc2]
        · have hc2 : i + j ≠ 2 ^ (d + 1) - 1 := by omega
          simp [beq_false_of_ne hc, beq_false_of_ne hc2]
      rw [heq]
      have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) + 1 := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h4, DEntry_odd_even, h3, DEntry_odd_even]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
      cases DEntry a b <;> cases (a + b == 2 ^ d - 1) <;> rfl
    · have hne : (i + j == 2 ^ (d + 1) - 1) = false := by
        simp only [beq_eq_false_iff_ne]; omega
      rw [hne]
      have h1 : i + 2 ^ (d + 1) = 2 * (a + 2 ^ d) + 1 := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h4, DEntry_odd_odd, h3, DEntry_odd_odd]; rfl

theorem DEntry_antidiag_sym (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DEntry (2 ^ d - 1 - i) (2 ^ d - 1 - j) = DEntry i j := by
  induction d generalizing i j with
  | zero =>
    simp only [Nat.pow_zero] at hi hj ⊢
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; rfl
  | succ d ih =>
    let a := i / 2
    let b := j / 2
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
    have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
    have him : i % 2 = 0 ∨ i % 2 = 1 := by omega
    have hjm : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases him with hi0 | hi1 <;> rcases hjm with hj0 | hj1
    · have h1 : 2 ^ (d + 1) - 1 - i = 2 * (2 ^ d - 1 - a) + 1 := by omega
      have h2 : 2 ^ (d + 1) - 1 - j = 2 * (2 ^ d - 1 - b) + 1 := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h2, DEntry_odd_odd, h3, h4, DEntry_even_even]
    · have h1 : 2 ^ (d + 1) - 1 - i = 2 * (2 ^ d - 1 - a) + 1 := by omega
      have h2 : 2 ^ (d + 1) - 1 - j = 2 * (2 ^ d - 1 - b) := by omega
      have h3 : i = 2 * a := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h2, DEntry_odd_even, h3, h4, DEntry_even_odd]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
    · have h1 : 2 ^ (d + 1) - 1 - i = 2 * (2 ^ d - 1 - a) := by omega
      have h2 : 2 ^ (d + 1) - 1 - j = 2 * (2 ^ d - 1 - b) + 1 := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b := by omega
      rw [h1, h2, DEntry_even_odd, h3, h4, DEntry_odd_even]
      simp only [DbarEntry, ih a b (by omega) (by omega)]
    · have h1 : 2 ^ (d + 1) - 1 - i = 2 * (2 ^ d - 1 - a) := by omega
      have h2 : 2 ^ (d + 1) - 1 - j = 2 * (2 ^ d - 1 - b) := by omega
      have h3 : i = 2 * a + 1 := by omega
      have h4 : j = 2 * b + 1 := by omega
      rw [h1, h2, DEntry_even_even, h3, h4, DEntry_odd_odd]

theorem DbarEntry_msb_diag (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DbarEntry (i + 2 ^ d) (j + 2 ^ d) = DbarEntry i j := by
  simp only [DbarEntry, DEntry_msb_diag d i j hi hj]

theorem DbarEntry_msb_off (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DbarEntry (i + 2 ^ d) j = xor (DbarEntry i j) (i + j == 2 ^ d - 1) := by
  simp only [DbarEntry, DEntry_msb_off d i j hi hj]
  cases DEntry i j <;> cases (i + j == 2 ^ d - 1) <;> rfl

theorem DbarEntry_antidiag_sym (d i j : Nat) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    DbarEntry (2 ^ d - 1 - i) (2 ^ d - 1 - j) = DbarEntry i j := by
  simp only [DbarEntry, DEntry_antidiag_sym d i j hi hj]

/-- Theorem 2A: For every d : Nat, Dbar(2^d) is an exact F_2-involution: Dbar(2^d)^2 = I. -/
theorem Dbar_pow2_invol (d : Nat) :
    matMul (DbarMat (2 ^ d)) (DbarMat (2 ^ d)) = matId (2 ^ d) := by
  induction d with
  | zero =>
    funext i j
    have hi : i.val = 0 := by have := i.isLt; simp at this; omega
    have hj : j.val = 0 := by have := j.isLt; simp at this; omega
    have hi0 : i = ⟨0, by decide⟩ := Fin.ext hi
    have hj0 : j = ⟨0, by decide⟩ := Fin.ext hj
    subst hi0; subst hj0; decide
  | succ d ih =>
    funext i j
    simp only [matMul, matId]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by omega
    rw [foldXor_cast hpow _
      (fun t : Fin (2 ^ d + 2 ^ d) => DbarMat (2 ^ (d + 1)) i ⟨t.val, by omega⟩ &&
                                      DbarMat (2 ^ (d + 1)) ⟨t.val, by omega⟩ j) (fun _ => rfl)]
    rw [foldXor_add (2 ^ d) (2 ^ d)]
    -- Split into 4 quadrants for (i, j) relative to 2^d!
    have hJ : ∀ (a b : Fin (2 ^ d)),
        foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          (a.val + t.val == 2 ^ d - 1) && DbarEntry t.val b.val) =
        DbarEntry (2 ^ d - 1 - a.val) b.val := by
      intro a b
      rw [foldXor_single ⟨2 ^ d - 1 - a.val, by omega⟩]
      · have h1 : a.val + (2 ^ d - 1 - a.val) = 2 ^ d - 1 := by omega
        simp [h1]
      · intro t ht
        have hne : (a.val + t.val == 2 ^ d - 1) = false := by
          simp only [beq_eq_false_iff_ne]
          intro heq; apply ht; apply Fin.ext; dsimp; omega
        simp [hne]
    have hJ2 : ∀ (a b : Fin (2 ^ d)),
        foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarEntry a.val t.val && (t.val + b.val == 2 ^ d - 1)) =
        DbarEntry a.val (2 ^ d - 1 - b.val) := by
      intro a b
      rw [foldXor_single ⟨2 ^ d - 1 - b.val, by omega⟩]
      · have h1 : (2 ^ d - 1 - b.val) + b.val = 2 ^ d - 1 := by omega
        simp [h1]
      · intro t ht
        have hne : (t.val + b.val == 2 ^ d - 1) = false := by
          simp only [beq_eq_false_iff_ne]
          intro heq; apply ht; apply Fin.ext; dsimp; omega
        simp [hne]
    have hJJ : ∀ (a b : Fin (2 ^ d)),
        foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          (a.val + t.val == 2 ^ d - 1) && (t.val + b.val == 2 ^ d - 1)) =
        (a.val == b.val) := by
      intro a b
      rw [foldXor_single ⟨2 ^ d - 1 - a.val, by omega⟩]
      · have h1 : a.val + (2 ^ d - 1 - a.val) = 2 ^ d - 1 := by omega
        simp only [h1, beq_self_eq_true, Bool.true_and]
        by_cases hab : a.val = b.val
        · have h2 : 2 ^ d - 1 - b.val + b.val = 2 ^ d - 1 := by omega
          simp [hab, h2]
        · have h2 : 2 ^ d - 1 - a.val + b.val ≠ 2 ^ d - 1 := by omega
          simp [beq_false_of_ne hab, beq_false_of_ne h2]
      · intro t ht
        have hne : (a.val + t.val == 2 ^ d - 1) = false := by
          simp only [beq_eq_false_iff_ne]
          intro heq; apply ht; apply Fin.ext; dsimp; omega
        simp [hne]
    by_cases hi : i.val < 2 ^ d <;> by_cases hj : j.val < 2 ^ d
    · -- Top-left: Dbar * Dbar ⊕ (Dbar ⊕ J) * (Dbar ⊕ J) = J * J = I!
      have hterm2 :
          foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
            DbarMat (2 ^ (d + 1)) i ⟨2 ^ d + t.val, by omega⟩ &&
            DbarMat (2 ^ (d + 1)) ⟨2 ^ d + t.val, by omega⟩ j) =
          xor (xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i.val t.val && DbarEntry t.val j.val))
                   (DbarEntry i.val (2 ^ d - 1 - j.val)))
              (xor (DbarEntry (2 ^ d - 1 - i.val) j.val)
                   (i.val == j.val)) := by
        rw [foldXor_congr (g := fun t : Fin (2 ^ d) =>
          xor (xor (DbarEntry i.val t.val && DbarEntry t.val j.val)
                   (DbarEntry i.val t.val && (t.val + j.val == 2 ^ d - 1)))
              (xor ((i.val + t.val == 2 ^ d - 1) && DbarEntry t.val j.val)
                   ((i.val + t.val == 2 ^ d - 1) && (t.val + j.val == 2 ^ d - 1))))]
        · rw [foldXor_xor, foldXor_xor, foldXor_xor,
              hJ2 ⟨i.val, hi⟩ ⟨j.val, hj⟩, hJ ⟨i.val, hi⟩ ⟨j.val, hj⟩, hJJ ⟨i.val, hi⟩ ⟨j.val, hj⟩]
        · intro t
          simp only [DbarMat]
          have h1 : DbarEntry i.val (2 ^ d + t.val) = xor (DbarEntry i.val t.val) (i.val + t.val == 2 ^ d - 1) := by
            rw [DbarEntry_sym, Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_off d t.val i.val t.isLt hi,
                DbarEntry_sym, Nat.add_comm t.val i.val]
          have h2 : DbarEntry (2 ^ d + t.val) j.val = xor (DbarEntry t.val j.val) (t.val + j.val == 2 ^ d - 1) := by
            rw [Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_off d t.val j.val t.isLt hj]
          rw [h1, h2]
          cases DbarEntry i.val t.val <;> cases DbarEntry t.val j.val <;>
          cases (i.val + t.val == 2 ^ d - 1) <;> cases (t.val + j.val == 2 ^ d - 1) <;> rfl
      have hcomm : DbarEntry i.val (2 ^ d - 1 - j.val) = DbarEntry (2 ^ d - 1 - i.val) j.val := by
        have h := DbarEntry_antidiag_sym d i.val (2 ^ d - 1 - j.val) hi (by omega)
        have hsub : 2 ^ d - 1 - (2 ^ d - 1 - j.val) = j.val := by omega
        rw [hsub] at h; exact h.symm
      rw [hterm2, hcomm]
      have hterm1 : foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarMat (2 ^ (d + 1)) i ⟨t.val, by omega⟩ && DbarMat (2 ^ (d + 1)) ⟨t.val, by omega⟩ j) =
          foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i.val t.val && DbarEntry t.val j.val) := rfl
      rw [hterm1]
      cases foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i.val t.val && DbarEntry t.val j.val) <;>
      cases DbarEntry (2 ^ d - 1 - i.val) j.val <;> cases (i.val == j.val) <;> rfl
    · -- Top-right: Dbar * (Dbar ⊕ J) ⊕ (Dbar ⊕ J) * Dbar = 0!
      have hne : (i.val == j.val) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hne]
      let j' : Fin (2 ^ d) := ⟨j.val - 2 ^ d, by omega⟩
      have hj_eq : j.val = j'.val + 2 ^ d := by dsimp [j']; omega
      have h1 : foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarMat (2 ^ (d + 1)) i ⟨t.val, by omega⟩ && DbarMat (2 ^ (d + 1)) ⟨t.val, by omega⟩ j) =
          xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i.val t.val && DbarEntry t.val j'.val))
              (DbarEntry i.val (2 ^ d - 1 - j'.val)) := by
        rw [← hJ2 ⟨i.val, hi⟩ j', ← foldXor_xor]
        apply foldXor_congr; intro t
        simp only [DbarMat]
        have he : DbarEntry t.val j.val = xor (DbarEntry t.val j'.val) (t.val + j'.val == 2 ^ d - 1) := by
          rw [hj_eq, DbarEntry_sym, DbarEntry_msb_off d j'.val t.val j'.isLt t.isLt,
              DbarEntry_sym, Nat.add_comm j'.val t.val]
        rw [he, and_xor_left]
      have h2 : foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarMat (2 ^ (d + 1)) i ⟨2 ^ d + t.val, by omega⟩ && DbarMat (2 ^ (d + 1)) ⟨2 ^ d + t.val, by omega⟩ j) =
          xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i.val t.val && DbarEntry t.val j'.val))
              (DbarEntry (2 ^ d - 1 - i.val) j'.val) := by
        rw [← hJ ⟨i.val, hi⟩ j', ← foldXor_xor]
        apply foldXor_congr; intro t
        simp only [DbarMat]
        have he1 : DbarEntry i.val (2 ^ d + t.val) = xor (DbarEntry i.val t.val) (i.val + t.val == 2 ^ d - 1) := by
          rw [DbarEntry_sym, Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_off d t.val i.val t.isLt hi,
              DbarEntry_sym, Nat.add_comm t.val i.val]
        have he2 : DbarEntry (2 ^ d + t.val) j.val = DbarEntry t.val j'.val := by
          rw [hj_eq, Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_diag d t.val j'.val t.isLt j'.isLt]
        rw [he1, he2, and_xor_right]
      have hcomm : DbarEntry i.val (2 ^ d - 1 - j'.val) = DbarEntry (2 ^ d - 1 - i.val) j'.val := by
        have h := DbarEntry_antidiag_sym d i.val (2 ^ d - 1 - j'.val) hi (by omega)
        have hsub : 2 ^ d - 1 - (2 ^ d - 1 - j'.val) = j'.val := by omega
        rw [hsub] at h; exact h.symm
      rw [h1, h2, hcomm, xor_self]
    · -- Bottom-left: symmetric to Top-right!
      have hne : (i.val == j.val) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hne]
      let i' : Fin (2 ^ d) := ⟨i.val - 2 ^ d, by omega⟩
      have hi_eq : i.val = i'.val + 2 ^ d := by dsimp [i']; omega
      have h1 : foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarMat (2 ^ (d + 1)) i ⟨t.val, by omega⟩ && DbarMat (2 ^ (d + 1)) ⟨t.val, by omega⟩ j) =
          xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i'.val t.val && DbarEntry t.val j.val))
              (DbarEntry (2 ^ d - 1 - i'.val) j.val) := by
        rw [← hJ i' ⟨j.val, hj⟩, ← foldXor_xor]
        apply foldXor_congr; intro t
        simp only [DbarMat]
        have he : DbarEntry i.val t.val = xor (DbarEntry i'.val t.val) (i'.val + t.val == 2 ^ d - 1) := by
          rw [hi_eq, DbarEntry_msb_off d i'.val t.val i'.isLt t.isLt]
        rw [he, and_xor_right]
      have h2 : foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
          DbarMat (2 ^ (d + 1)) i ⟨2 ^ d + t.val, by omega⟩ && DbarMat (2 ^ (d + 1)) ⟨2 ^ d + t.val, by omega⟩ j) =
          xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i'.val t.val && DbarEntry t.val j.val))
              (DbarEntry i'.val (2 ^ d - 1 - j.val)) := by
        rw [← hJ2 i' ⟨j.val, hj⟩, ← foldXor_xor]
        apply foldXor_congr; intro t
        simp only [DbarMat]
        have he1 : DbarEntry i.val (2 ^ d + t.val) = DbarEntry i'.val t.val := by
          rw [hi_eq, Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_diag d i'.val t.val i'.isLt t.isLt]
        have he2 : DbarEntry (2 ^ d + t.val) j.val = xor (DbarEntry t.val j.val) (t.val + j.val == 2 ^ d - 1) := by
          rw [Nat.add_comm (2 ^ d) t.val, DbarEntry_msb_off d t.val j.val t.isLt hj]
        rw [he1, he2, and_xor_left]
      have hcomm : DbarEntry i'.val (2 ^ d - 1 - j.val) = DbarEntry (2 ^ d - 1 - i'.val) j.val := by
        have h := DbarEntry_antidiag_sym d i'.val (2 ^ d - 1 - j.val) i'.isLt (by omega)
        have hsub : 2 ^ d - 1 - (2 ^ d - 1 - j.val) = j.val := by omega
        rw [hsub] at h; exact h.symm
      rw [h1, h2, hcomm, xor_self]
    · -- Bottom-right: (Dbar ⊕ J)*(Dbar ⊕ J) ⊕ Dbar*Dbar = J*J = I!
      let i' : Fin (2 ^ d) := ⟨i.val - 2 ^ d, by omega⟩
      let j' : Fin (2 ^ d) := ⟨j.val - 2 ^ d, by omega⟩
      have hi_eq : i.val = i'.val + 2 ^ d := by dsimp [i']; omega
      have hj_eq : j.val = j'.val + 2 ^ d := by dsimp [j']; omega
      have hij : (i.val == j.val) = (i'.val == j'.val) := by
        by_cases hc : i.val = j.val
        · have hc' : i'.val = j'.val := by omega
          simp [hc, hc']
        · have hc' : i'.val ≠ j'.val := by omega
          simp [beq_false_of_ne hc, beq_false_of_ne hc']
      rw [hij]
      have hterm1 :
          foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
            DbarMat (2 ^ (d + 1)) i ⟨t.val, by omega⟩ &&
            DbarMat (2 ^ (d + 1)) ⟨t.val, by omega⟩ j) =
          xor (xor (foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i'.val t.val && DbarEntry t.val j'.val))
                   (DbarEntry i'.val (2 ^ d - 1 - j'.val)))
              (xor (DbarEntry (2 ^ d - 1 - i'.val) j'.val)
                   (i'.val == j'.val)) := by
        rw [foldXor_congr (g := fun t : Fin (2 ^ d) =>
          xor (xor (DbarEntry i'.val t.val && DbarEntry t.val j'.val)
                   (DbarEntry i'.val t.val && (t.val + j'.val == 2 ^ d - 1)))
              (xor ((i'.val + t.val == 2 ^ d - 1) && DbarEntry t.val j'.val)
                   ((i'.val + t.val == 2 ^ d - 1) && (t.val + j'.val == 2 ^ d - 1))))]
        · rw [foldXor_xor, foldXor_xor, foldXor_xor,
              hJ2 i' j', hJ i' j', hJJ i' j']
        · intro t
          simp only [DbarMat]
          have h1 : DbarEntry i.val t.val = xor (DbarEntry i'.val t.val) (i'.val + t.val == 2 ^ d - 1) := by
            rw [hi_eq, DbarEntry_msb_off d i'.val t.val i'.isLt t.isLt]
          have h2 : DbarEntry t.val j.val = xor (DbarEntry t.val j'.val) (t.val + j'.val == 2 ^ d - 1) := by
            rw [hj_eq, DbarEntry_sym, DbarEntry_msb_off d j'.val t.val j'.isLt t.isLt,
                DbarEntry_sym, Nat.add_comm j'.val t.val]
          rw [h1, h2]
          cases DbarEntry i'.val t.val <;> cases DbarEntry t.val j'.val <;>
          cases (i'.val + t.val == 2 ^ d - 1) <;> cases (t.val + j'.val == 2 ^ d - 1) <;> rfl
      have hterm2 :
          foldXor (2 ^ d) (fun t : Fin (2 ^ d) =>
            DbarMat (2 ^ (d + 1)) i ⟨2 ^ d + t.val, by omega⟩ &&
            DbarMat (2 ^ (d + 1)) ⟨2 ^ d + t.val, by omega⟩ j) =
          foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i'.val t.val && DbarEntry t.val j'.val) := by
        apply foldXor_congr; intro t
        simp only [DbarMat]
        rw [hi_eq, hj_eq, Nat.add_comm (2 ^ d) t.val,
            DbarEntry_msb_diag d i'.val t.val i'.isLt t.isLt,
            DbarEntry_msb_diag d t.val j'.val t.isLt j'.isLt]
      have hcomm : DbarEntry i'.val (2 ^ d - 1 - j'.val) = DbarEntry (2 ^ d - 1 - i'.val) j'.val := by
        have h := DbarEntry_antidiag_sym d i'.val (2 ^ d - 1 - j'.val) i'.isLt (by omega)
        have hsub : 2 ^ d - 1 - (2 ^ d - 1 - j'.val) = j'.val := by omega
        rw [hsub] at h; exact h.symm
      rw [hterm1, hterm2, hcomm]
      cases foldXor (2 ^ d) (fun t : Fin (2 ^ d) => DbarEntry i'.val t.val && DbarEntry t.val j'.val) <;>
      cases DbarEntry (2 ^ d - 1 - i'.val) j'.val <;> cases (i'.val == j'.val) <;> rfl

/-- Helper: every positive n decomposes as 2^d + r with 0 ≤ r < 2^d. -/
theorem exists_msb_split (n : Nat) (hn : n ≥ 1) :
    ∃ d r : Nat, n = 2 ^ d + r ∧ r < 2 ^ d := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, 0, by omega, by decide⟩
    · have hhalf : n / 2 ≥ 1 := by omega
      have hlt : n / 2 < n := by omega
      rcases ih (n / 2) hlt hhalf with ⟨d, r, heq, hr⟩
      refine ⟨d + 1, 2 * r + n % 2, ?_, ?_⟩
      · have : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
        omega
      · have : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
        omega

/-- Theorem 2B: Dbar(n) has full F_2-rank n for EVERY (arbitrary non-power-of-two!) n : Nat. -/
theorem Dbar_hasRank_full (n : Nat) : HasRank (DbarMat n) n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; exact hasRank_congr (fun i => Fin.elim0 i) hasRank_zero
    · rcases exists_msb_split n (by omega) with ⟨d, r, hnr, hr⟩
      subst hnr
      -- Unipotent congruence: Row_{2^d+i} ← Row_{2^d+i} ⊕ Row_i, Col_{2^d+j} ← Col_{2^d+j} ⊕ Col_j
      -- transforms Dbar(2^d + r) into [[Dbar(2^d), K], [K^T, 0]], where K[i, j] = (i + j == 2^d - 1).
      let K : Mat (2 ^ d) r := fun i j => i.val + j.val == 2 ^ d - 1
      let KT : Mat r (2 ^ d) := fun i j => i.val + j.val == 2 ^ d - 1
      let trunc : Vec (2 ^ d) → Vec r := fun u j => u ⟨j.val, Nat.lt_trans j.isLt hr⟩
      let pad : Vec r → Vec (2 ^ d) := fun v i => if h : i.val < r then v ⟨i.val, h⟩ else false
      let P := LinEquiv.rowShearDown trunc (fun _ _ => rfl)
      let Q := LinEquiv.rowShearUp pad (fun v1 v2 => by
        funext i; simp only [pad, vxor]; by_cases h : i.val < r <;> simp [h])
      apply hasRank_of_equiv rfl rfl P Q
        (M' := blockMat (DbarMat (2 ^ d)) K KT (matZero r r))
      · intro w
        rw [← joinVec_split w]
        let u := splitLeft w
        let v := splitRight w
        simp only [P, Q, LinEquiv.rowShearDown, LinEquiv.rowShearUp, splitLeft_joinVec, splitRight_joinVec]
        rw [matVec_blockMat, matVec_zero_mat, vxor_zero_right]
        have hpad_sum : ∀ (f : Fin (2 ^ d) → Bool),
            foldXor (2 ^ d) (fun j => f j && pad v j) =
            foldXor r (fun j => f ⟨j.val, Nat.lt_trans j.isLt hr⟩ && v j) := by
          intro f
          have hadd : 2 ^ d = r + (2 ^ d - r) := by omega
          rw [foldXor_cast hadd _ (fun j : Fin (r + (2 ^ d - r)) => f ⟨j.val, by omega⟩ && pad v ⟨j.val, by omega⟩) (fun _ => rfl)]
          rw [foldXor_add r (2 ^ d - r)]
          have h0_right : foldXor (2 ^ d - r) (fun j => f ⟨r + j.val, by omega⟩ && pad v ⟨r + j.val, by omega⟩) = false := by
            rw [foldXor_congr (g := fun _ => false)]
            · exact foldXor_zero _
            · intro j; simp only [pad]; have hnot : ¬ (r + j.val < r) := by omega
              simp [hnot]
          rw [h0_right, xor_false_right]
          apply foldXor_congr; intro j; simp [pad, j.isLt]
        -- Evaluate M * (u ⊕ pad v, v) on top (2^d) and bottom (r)
        have htop : splitLeft (matVec (DbarMat (2 ^ d + r)) (joinVec (vxor u (pad v)) v)) =
                    vxor (matVec (DbarMat (2 ^ d)) u) (matVec K v) := by
          funext i
          simp only [splitLeft, matVec, vxor]
          rw [foldXor_add (2 ^ d) r]
          have hleft : foldXor (2 ^ d) (fun j => DbarMat (2 ^ d + r) ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ &&
                         joinVec (vxor u (pad v)) v ⟨j.val, by omega⟩) =
                       xor (foldXor (2 ^ d) (fun j => DbarEntry i.val j.val && u j))
                           (foldXor r (fun j => DbarEntry i.val j.val && v j)) := by
            rw [foldXor_congr (g := fun j => xor (DbarEntry i.val j.val && u j) (DbarEntry i.val j.val && pad v j))]
            · rw [foldXor_xor, hpad_sum (fun j => DbarEntry i.val j.val)]
            · intro j; simp only [DbarMat, joinVec, j.isLt, ↓reduceDIte, vxor, and_xor_left]
          have hright : foldXor r (fun j => DbarMat (2 ^ d + r) ⟨i.val, by omega⟩ ⟨2 ^ d + j.val, by omega⟩ &&
                          joinVec (vxor u (pad v)) v ⟨2 ^ d + j.val, by omega⟩) =
                        xor (foldXor r (fun j => DbarEntry i.val j.val && v j))
                            (foldXor r (fun j => (i.val + j.val == 2 ^ d - 1) && v j)) := by
            rw [← foldXor_xor]
            apply foldXor_congr; intro j
            have hnot : ¬ (2 ^ d + j.val < 2 ^ d) := by omega
            simp only [DbarMat, joinVec, hnot, ↓reduceDIte]
            have hfin : (⟨2 ^ d + j.val - 2 ^ d, by omega⟩ : Fin r) = j := Fin.ext (by dsimp; omega)
            rw [hfin, DbarEntry_sym, Nat.add_comm (2 ^ d) j.val,
                DbarEntry_msb_off d j.val i.val (Nat.lt_trans j.isLt hr) i.isLt,
                DbarEntry_sym, Nat.add_comm j.val i.val, and_xor_right]
          rw [hleft, hright]
          simp only [K, DbarMat]
          cases foldXor (2 ^ d) (fun j => DbarEntry i.val j.val && u j) <;>
          cases foldXor r (fun j => DbarEntry i.val j.val && v j) <;>
          cases foldXor r (fun j => (i.val + j.val == 2 ^ d - 1) && v j) <;> rfl
        have hbot : vxor (splitRight (matVec (DbarMat (2 ^ d + r)) (joinVec (vxor u (pad v)) v)))
                         (trunc (vxor (matVec (DbarMat (2 ^ d)) u) (matVec K v))) =
                    matVec KT u := by
          funext i
          simp only [splitRight, trunc, matVec, vxor]
          rw [foldXor_add (2 ^ d) r]
          have hleft : foldXor (2 ^ d) (fun j => DbarMat (2 ^ d + r) ⟨2 ^ d + i.val, by omega⟩ ⟨j.val, by omega⟩ &&
                         joinVec (vxor u (pad v)) v ⟨j.val, by omega⟩) =
                       xor (xor (foldXor (2 ^ d) (fun j => DbarEntry i.val j.val && u j))
                                (foldXor (2 ^ d) (fun j => (i.val + j.val == 2 ^ d - 1) && u j)))
                           (xor (foldXor r (fun j => DbarEntry i.val j.val && v j))
                                (foldXor r (fun j => (i.val + j.val == 2 ^ d - 1) && v j))) := by
            rw [← hpad_sum (fun j => DbarEntry i.val j.val),
                ← hpad_sum (fun j => i.val + j.val == 2 ^ d - 1),
                ← foldXor_xor, ← foldXor_xor, ← foldXor_xor]
            apply foldXor_congr; intro j
            simp only [DbarMat, joinVec, j.isLt, ↓reduceDIte, vxor]
            rw [Nat.add_comm (2 ^ d) i.val, DbarEntry_msb_off d i.val j.val (Nat.lt_trans i.isLt hr) j.isLt]
            cases DbarEntry i.val j.val <;> cases (i.val + j.val == 2 ^ d - 1) <;>
            cases u j <;> cases pad v j <;> rfl
          have hright : foldXor r (fun j => DbarMat (2 ^ d + r) ⟨2 ^ d + i.val, by omega⟩ ⟨2 ^ d + j.val, by omega⟩ &&
                          joinVec (vxor u (pad v)) v ⟨2 ^ d + j.val, by omega⟩) =
                        foldXor r (fun j => DbarEntry i.val j.val && v j) := by
            apply foldXor_congr; intro j
            have hnot : ¬ (2 ^ d + j.val < 2 ^ d) := by omega
            simp only [DbarMat, joinVec, hnot, ↓reduceDIte]
            have hfin : (⟨2 ^ d + j.val - 2 ^ d, by omega⟩ : Fin r) = j := Fin.ext (by dsimp; omega)
            rw [hfin, Nat.add_comm (2 ^ d) i.val, Nat.add_comm (2 ^ d) j.val,
                DbarEntry_msb_diag d i.val j.val (Nat.lt_trans i.isLt hr) (Nat.lt_trans j.isLt hr)]
          rw [hleft, hright]
          simp only [KT, K, DbarMat]
          cases foldXor (2 ^ d) (fun j => DbarEntry i.val j.val && u j) <;>
          cases foldXor (2 ^ d) (fun j => (i.val + j.val == 2 ^ d - 1) && u j) <;>
          cases foldXor r (fun j => DbarEntry i.val j.val && v j) <;>
          cases foldXor r (fun j => (i.val + j.val == 2 ^ d - 1) && v j) <;> rfl
        rw [htop, hbot]
      · -- Apply Exact Involutive Schur-Complement Elimination with pivot Dbar(2^d)!
        have hinvol := Dbar_pow2_invol d
        apply hasRank_schur_inv hinvol hinvol
        -- Schur complement = 0 ⊕ KT * Dbar(2^d) * K = Dbar(r)!!
        have hschur : ∀ i j : Fin r,
            matXor (matZero r r) (matMul KT (matMul (DbarMat (2 ^ d)) K)) i j = DbarMat r i j := by
          intro i j
          simp only [matXor, matZero, xor_false_left, matMul, KT, K, DbarMat]
          rw [foldXor_single ⟨2 ^ d - 1 - i.val, by omega⟩]
          · have h1 : i.val + (2 ^ d - 1 - i.val) = 2 ^ d - 1 := by omega
            simp only [h1, beq_self_eq_true, Bool.true_and]
            rw [foldXor_single ⟨2 ^ d - 1 - j.val, by omega⟩]
            · have h2 : (2 ^ d - 1 - j.val) + j.val = 2 ^ d - 1 := by omega
              simp only [h2, beq_self_eq_true, Bool.and_true]
              exact DbarEntry_antidiag_sym d i.val j.val (Nat.lt_trans i.isLt hr) (Nat.lt_trans j.isLt hr)
            · intro t ht
              have hne : (t.val + j.val == 2 ^ d - 1) = false := by
                simp only [beq_eq_false_iff_ne]; intro heq; apply ht; apply Fin.ext; dsimp; omega
              simp [hne]
          · intro t ht
            have hne : (i.val + t.val == 2 ^ d - 1) = false := by
              simp only [beq_eq_false_iff_ne]; intro heq; apply ht; apply Fin.ext; dsimp; omega
            simp [hne]
        exact hasRank_congr hschur (ih r (by omega))

/-- Theorem 2C: Carry-defect matrix D(n) has exact F_2-rank 2 * (n / 2) and nullity n % 2 for ALL n : Nat! -/
theorem D_hasRank (n : Nat) : HasRank (DMat n) (2 * (n / 2)) := by
  let n0 := (n + 1) / 2
  let n1 := n / 2
  let P := LinEquiv.paritySplit n
  let B : Mat n0 n1 := fun a b => DbarEntry a.val b.val
  let C : Mat n1 n0 := fun a b => DbarEntry a.val b.val
  have hn_eq : n = n0 + n1 := by omega
  apply hasRank_of_equiv hn_eq hn_eq P P.symm (M' := blockMat (matZero n0 n0) B C (matZero n1 n1))
  · intro w
    rw [← joinVec_split w]
    let u := splitLeft w
    let v := splitRight w
    rw [matVec_blockMat, matVec_zero_mat, matVec_zero_mat, vxor_zero_left, vxor_zero_right]
    simp only [P, LinEquiv.paritySplit, LinEquiv.symm]
    congr 1
    · funext a
      simp only [matVec, B]
      rw [foldXor_even_odd n]
      have hE : foldXor n0 (fun t => DMat n ⟨2 * a.val, by omega⟩ ⟨2 * t.val, by omega⟩ &&
                  (if h : (2 * t.val) % 2 = 0 then splitLeft (joinVec u v) ⟨(2 * t.val) / 2, by omega⟩
                   else splitRight (joinVec u v) ⟨(2 * t.val) / 2, by omega⟩)) = false := by
        rw [foldXor_congr (g := fun _ => false)]
        · exact foldXor_zero _
        · intro t; simp [DMat, DEntry_even_even]
      have hO : foldXor n1 (fun t => DMat n ⟨2 * a.val, by omega⟩ ⟨2 * t.val + 1, by omega⟩ &&
                  (if h : (2 * t.val + 1) % 2 = 0 then splitLeft (joinVec u v) ⟨(2 * t.val + 1) / 2, by omega⟩
                   else splitRight (joinVec u v) ⟨(2 * t.val + 1) / 2, by omega⟩)) =
                foldXor n1 (fun t => DbarEntry a.val t.val && v t) := by
        apply foldXor_congr; intro t
        have hodd : ¬ ((2 * t.val + 1) % 2 = 0) := by omega
        simp only [DMat, DEntry_even_odd, hodd, ↓reduceDIte, splitRight_joinVec]
        congr 2; apply Fin.ext; dsimp; omega
      rw [hE, hO, xor_false_left]
    · funext b
      simp only [matVec, C]
      rw [foldXor_even_odd n]
      have hE : foldXor n0 (fun t => DMat n ⟨2 * b.val + 1, by omega⟩ ⟨2 * t.val, by omega⟩ &&
                  (if h : (2 * t.val) % 2 = 0 then splitLeft (joinVec u v) ⟨(2 * t.val) / 2, by omega⟩
                   else splitRight (joinVec u v) ⟨(2 * t.val) / 2, by omega⟩)) =
                foldXor n0 (fun t => DbarEntry b.val t.val && u t) := by
        apply foldXor_congr; intro t
        have hev : (2 * t.val) % 2 = 0 := by omega
        simp only [DMat, DEntry_odd_even, hev, ↓reduceDIte, splitLeft_joinVec]
        congr 2; apply Fin.ext; dsimp; omega
      have hO : foldXor n1 (fun t => DMat n ⟨2 * b.val + 1, by omega⟩ ⟨2 * t.val + 1, by omega⟩ &&
                  (if h : (2 * t.val + 1) % 2 = 0 then splitLeft (joinVec u v) ⟨(2 * t.val + 1) / 2, by omega⟩
                   else splitRight (joinVec u v) ⟨(2 * t.val + 1) / 2, by omega⟩)) = false := by
        rw [foldXor_congr (g := fun _ => false)]
        · exact foldXor_zero _
        · intro t; simp [DMat, DEntry_odd_odd]
      rw [hE, hO, xor_false_right]
  · have h2 : 2 * n1 = n1 + n1 := by omega
    rw [h2]
    have hd : n0 = n1 + (n0 - n1) := by omega
    have hB : HasRank B n1 := by
      let B' : Mat (n1 + (n0 - n1)) n1 := fun a b => DbarEntry a.val b.val
      have hB' : HasRank B' n1 := hasRank_rect_tall_of_top_full (Dbar_hasRank_full n1)
      exact hasRank_cast_rows hd B B' (fun _ _ => rfl) hB'
    have hC : HasRank C n1 := by
      let C' : Mat n1 (n1 + (n0 - n1)) := fun a b => DbarEntry a.val b.val
      have hC' : HasRank C' n1 := hasRank_rect_wide_of_left_full (Dbar_hasRank_full n1)
      exact hasRank_cast_cols hd C C' (fun _ _ => rfl) hC'
    exact hasRank_antidiag hB hC

theorem D_hasNullity (n : Nat) : HasNullity (DMat n) (n % 2) := by
  refine ⟨by omega, ?_⟩
  have heq : n - n % 2 = 2 * (n / 2) := by omega
  rw [heq]
  exact D_hasRank n

/-! ## Section 5: Theorem 1 — Carry-Free XOR-Sum Parity Matrix M0 & Gray-Code Bit-Transition Law -/

/-- Explicit 2-bit isotropic identity: ∀ k ≥ 0, ∀ i < 2^(k+1), M0(i, 0) ⊕ M0(i, 2^k) = 1. -/
theorem M0Entry_xor_pow2 (k i : Nat) (hi : i < 2 ^ (k + 1)) :
    xor (M0Entry i 0) (M0Entry i (2 ^ k)) = true := by
  induction k generalizing i with
  | zero =>
    simp only [Nat.pow_zero] at hi ⊢
    have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl <;> decide
  | succ k ih =>
    let a := i / 2
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
    have hpow2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have him : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases him with hi0 | hi1
    · have hi' : i = 2 * a := by omega
      have h0 : (0 : Nat) = 2 * 0 := rfl
      rw [hi', hpow, h0, M0Entry_even_even, M0Entry_even_even]
      exact ih a (by omega)
    · have hi' : i = 2 * a + 1 := by omega
      have h0 : (0 : Nat) = 2 * 0 := rfl
      rw [hi', hpow, h0, M0Entry_odd_even, M0Entry_odd_even]
      have hrec := ih a (by omega)
      cases h1 : M0Entry a 0 <;> cases h2 : M0Entry a (2 ^ k) <;>
        rw [h1, h2] at hrec <;> exact hrec

/-- Constructive 2-bit isotropic witness vector x = e_0 ⊕ e_{2^k} for M0(m) * x = 1_m (m ≥ 2). -/
theorem M0_isotropic_witness (m : Nat) (hm : m ≥ 2) :
    ∃ x : Vec m, matVec (M0Mat m) x = (fun _ => true) ∧ vdot (fun _ => true) x = false := by
  rcases exists_msb_split (m - 1) (by omega) with ⟨k, r, hmr, hr⟩
  have hpk_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h0ne : (0 : Nat) ≠ 2 ^ k := by omega
  have hpk_lt : 2 ^ k < m := by omega
  have hm_le : m ≤ 2 ^ (k + 1) := by
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
    omega
  let x : Vec m := fun j => (j.val == 0) || (j.val == 2 ^ k)
  refine ⟨x, ?_, ?_⟩
  · funext i
    simp only [matVec, M0Mat]
    have hsum : foldXor m (fun j => M0Entry i.val j.val && x j) =
                xor (M0Entry i.val 0) (M0Entry i.val (2 ^ k)) := by
      have hsplit : foldXor m (fun j => M0Entry i.val j.val && x j) =
          xor (foldXor m (fun j => if j.val == 0 then M0Entry i.val j.val else false))
              (foldXor m (fun j => if j.val == 2 ^ k then M0Entry i.val j.val else false)) := by
        rw [← foldXor_xor]
        apply foldXor_congr; intro j
        simp only [x]
        by_cases h0 : j.val = 0
        · simp [h0, beq_false_of_ne h0ne]
        · by_cases hp : j.val = 2 ^ k
          · simp [hp, beq_false_of_ne h0ne.symm]
          · simp [beq_false_of_ne h0, beq_false_of_ne hp]
      rw [hsplit]
      congr 1
      · rw [foldXor_single ⟨0, by omega⟩]
        · simp
        · intro j hj
          have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
          simp [beq_false_of_ne hne]
      · rw [foldXor_single ⟨2 ^ k, hpk_lt⟩]
        · simp
        · intro j hj
          have hne : j.val ≠ 2 ^ k := fun h => hj (Fin.ext h)
          simp [beq_false_of_ne hne]
    rw [hsum]
    exact M0Entry_xor_pow2 k i.val (Nat.lt_of_lt_of_le i.isLt hm_le)
  · simp only [vdot, Bool.true_and]
    have hsplit : foldXor m x =
        xor (foldXor m (fun j : Fin m => j.val == 0))
            (foldXor m (fun j : Fin m => j.val == 2 ^ k)) := by
      rw [← foldXor_xor]
      apply foldXor_congr; intro j
      simp only [x]
      by_cases h0 : j.val = 0
      · simp [h0, beq_false_of_ne h0ne]
      · by_cases hp : j.val = 2 ^ k
        · simp [hp, beq_false_of_ne h0ne.symm]
        · simp [beq_false_of_ne h0, beq_false_of_ne hp]
    rw [hsplit]
    have h1 : foldXor m (fun j : Fin m => j.val == 0) = true := by
      rw [foldXor_single ⟨0, by omega⟩]
      · simp
      · intro j hj; exact beq_false_of_ne (fun h => hj (Fin.ext h))
    have h2 : foldXor m (fun j : Fin m => j.val == 2 ^ k) = true := by
      rw [foldXor_single ⟨2 ^ k, hpk_lt⟩]
      · simp
      · intro j hj; exact beq_false_of_ne (fun h => hj (Fin.ext h))
    rw [h1, h2]; rfl

/-- Core LSB Decoupling Step for M0(n):
    For every n ≥ 3, M0(n) ~ M0(⌈n/2⌉) ⊕ D(⌊n/2⌋) over F_2! -/
theorem M0_lsb_step (n r0 r1 : Nat) (hn : n ≥ 3)
    (h0 : HasRank (M0Mat ((n + 1) / 2)) r0)
    (h1 : HasRank (DMat (n / 2)) r1) :
    HasRank (M0Mat n) (r0 + r1) := by
  let n0 := (n + 1) / 2
  let n1 := n / 2
  have hn_eq : n = n0 + n1 := by omega
  have hn0_ge2 : n0 ≥ 2 := by omega
  have hle : n1 ≤ n0 := by omega
  let P1 := LinEquiv.paritySplit n
  let trunc : Vec n0 → Vec n1 := fun u j => u ⟨j.val, Nat.lt_of_lt_of_le j.isLt hle⟩
  let pad : Vec n1 → Vec n0 := fun v i => if h : i.val < n1 then v ⟨i.val, h⟩ else false
  let P2 := LinEquiv.rowShearDown trunc (fun _ _ => rfl)
  let Q2 := LinEquiv.rowShearUp pad (fun v1 v2 => by
    funext i; simp only [pad, vxor]; by_cases h : i.val < n1 <;> simp [h])
  let ones0 : Vec n0 := fun _ => true
  let ones1 : Vec n1 := fun _ => true
  apply hasRank_of_equiv hn_eq hn_eq (P1.trans P2) (Q2.trans P1.symm)
    (M' := blockMat (M0Mat n0) (outerMat ones0 ones1) (outerMat ones1 ones0) (DMat n1))
  · intro w
    rw [← joinVec_split w]
    let u := splitLeft w
    let v := splitRight w
    rw [matVec_blockMat]
    simp only [LinEquiv.trans, P1, P2, Q2, LinEquiv.rowShearDown, LinEquiv.rowShearUp,
      LinEquiv.paritySplit, LinEquiv.symm, splitLeft_joinVec, splitRight_joinVec]
    have hpad_sum : ∀ (f : Fin n0 → Bool),
        foldXor n0 (fun j => f j && pad v j) =
        foldXor n1 (fun j => f ⟨j.val, Nat.lt_of_lt_of_le j.isLt hle⟩ && v j) := by
      intro f
      have hadd : n0 = n1 + (n0 - n1) := by omega
      rw [foldXor_cast hadd _ (fun j : Fin (n1 + (n0 - n1)) => f ⟨j.val, by omega⟩ && pad v ⟨j.val, by omega⟩) (fun _ => rfl)]
      rw [foldXor_add n1 (n0 - n1)]
      have hz : foldXor (n0 - n1) (fun j => f ⟨n1 + j.val, by omega⟩ && pad v ⟨n1 + j.val, by omega⟩) = false := by
        rw [foldXor_congr (g := fun _ => false)]
        · exact foldXor_zero _
        · intro j
          have hnot : ¬ (n1 + j.val < n1) := by omega
          simp [pad, hnot]
      rw [hz, xor_false_right]
      apply foldXor_congr; intro j; simp [pad, j.isLt]
    have hpad_sum1 : foldXor n0 (fun j => pad v j) = foldXor n1 (fun j => v j) := by
      have h := hpad_sum (fun _ => true)
      simpa using h
    -- Compute even entries of M0(n) * Q_total(u, v)
    have hE : (fun a : Fin n0 =>
        matVec (M0Mat n) (fun i : Fin n =>
          if h : i.val % 2 = 0 then vxor u (pad v) ⟨i.val / 2, by omega⟩
          else v ⟨i.val / 2, by omega⟩) ⟨2 * a.val, by omega⟩) =
        vxor (matVec (M0Mat n0) u) (matVec (outerMat ones0 ones1) v) := by
      funext a
      simp only [matVec, vxor, outerMat, ones0, ones1, Bool.true_and]
      rw [foldXor_even_odd n]
      have hev : foldXor n0 (fun t : Fin n0 => M0Mat n ⟨2 * a.val, by omega⟩ ⟨2 * t.val, by omega⟩ &&
                  (if h : (2 * t.val) % 2 = 0 then (xor (u ⟨(2 * t.val) / 2, by omega⟩) (pad v ⟨(2 * t.val) / 2, by omega⟩))
                   else v ⟨(2 * t.val) / 2, by omega⟩)) =
                xor (foldXor n0 (fun t => M0Entry a.val t.val && u t))
                    (foldXor n1 (fun t => M0Entry a.val t.val && v t)) := by
        rw [← hpad_sum (fun t => M0Entry a.val t.val), ← foldXor_xor]
        apply foldXor_congr; intro t
        have h2 : (2 * t.val) % 2 = 0 := by omega
        simp only [M0Mat, M0Entry_even_even, h2, ↓reduceDIte]
        have hfin : (⟨(2 * t.val) / 2, by omega⟩ : Fin n0) = t := Fin.ext (by dsimp; omega)
        rw [hfin, and_xor_left]
      have hodd : foldXor n1 (fun t : Fin n1 => M0Mat n ⟨2 * a.val, by omega⟩ ⟨2 * t.val + 1, by omega⟩ &&
                  (if h : (2 * t.val + 1) % 2 = 0 then (xor (u ⟨(2 * t.val + 1) / 2, by omega⟩) (pad v ⟨(2 * t.val + 1) / 2, by omega⟩))
                   else v ⟨(2 * t.val + 1) / 2, by omega⟩)) =
                xor (foldXor n1 (fun t => M0Entry a.val t.val && v t))
                    (foldXor n1 (fun t => v t)) := by
        rw [← foldXor_xor]
        apply foldXor_congr; intro t
        have h2 : ¬ ((2 * t.val + 1) % 2 = 0) := by omega
        simp only [M0Mat, M0Entry_even_odd, h2, ↓reduceDIte]
        have hfin : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin n1) = t := Fin.ext (by dsimp; omega)
        rw [hfin]
        cases M0Entry a.val t.val <;> cases v t <;> rfl
      dsimp only
      rw [hev, hodd]
      simp only [M0Mat]
      cases foldXor n0 (fun t => M0Entry a.val t.val && u t) <;>
      cases foldXor n1 (fun t => M0Entry a.val t.val && v t) <;>
      cases foldXor n1 (fun t => v t) <;> rfl
    -- Compute odd entries XOR trunc(even entries)
    have hO : vxor (fun b : Fin n1 =>
        matVec (M0Mat n) (fun i : Fin n =>
          if h : i.val % 2 = 0 then vxor u (pad v) ⟨i.val / 2, by omega⟩
          else v ⟨i.val / 2, by omega⟩) ⟨2 * b.val + 1, by omega⟩)
        (trunc (vxor (matVec (M0Mat n0) u) (matVec (outerMat ones0 ones1) v))) =
        vxor (matVec (outerMat ones1 ones0) u) (matVec (DMat n1) v) := by
      funext b
      simp only [vxor, trunc, matVec, outerMat, ones0, ones1, Bool.true_and, M0Mat, DMat]
      rw [foldXor_even_odd n]
      have hev : foldXor n0 (fun t : Fin n0 => M0Entry (2 * b.val + 1) (2 * t.val) &&
                  (if h : (2 * t.val) % 2 = 0 then (xor (u ⟨(2 * t.val) / 2, by omega⟩) (pad v ⟨(2 * t.val) / 2, by omega⟩))
                   else v ⟨(2 * t.val) / 2, by omega⟩)) =
                xor (xor (foldXor n0 (fun t => M0Entry b.val t.val && u t))
                         (foldXor n0 (fun t => u t)))
                    (xor (foldXor n1 (fun t => M0Entry b.val t.val && v t))
                         (foldXor n1 (fun t => v t))) := by
        rw [← hpad_sum (fun t => M0Entry b.val t.val), ← hpad_sum1,
            ← foldXor_xor, ← foldXor_xor, ← foldXor_xor]
        apply foldXor_congr; intro t
        have h2 : (2 * t.val) % 2 = 0 := by omega
        simp only [M0Entry_odd_even, h2, ↓reduceDIte]
        have hfin : (⟨(2 * t.val) / 2, by omega⟩ : Fin n0) = t := Fin.ext (by dsimp; omega)
        rw [hfin]
        cases M0Entry b.val t.val <;> cases u t <;> cases pad v t <;> rfl
      have hodd : foldXor n1 (fun t : Fin n1 => M0Entry (2 * b.val + 1) (2 * t.val + 1) &&
                  (if h : (2 * t.val + 1) % 2 = 0 then (xor (u ⟨(2 * t.val + 1) / 2, by omega⟩) (pad v ⟨(2 * t.val + 1) / 2, by omega⟩))
                   else v ⟨(2 * t.val + 1) / 2, by omega⟩)) =
                foldXor n1 (fun t => M1Entry b.val t.val && v t) := by
        apply foldXor_congr; intro t
        have h2 : ¬ ((2 * t.val + 1) % 2 = 0) := by omega
        simp only [M0Entry_odd_odd, h2, ↓reduceDIte]
        have hfin : (⟨(2 * t.val + 1) / 2, by omega⟩ : Fin n1) = t := Fin.ext (by dsimp; omega)
        rw [hfin]
      have hD : foldXor n1 (fun t => DEntry b.val t.val && v t) =
                xor (foldXor n1 (fun t => M0Entry b.val t.val && v t))
                    (foldXor n1 (fun t => M1Entry b.val t.val && v t)) := by
        rw [← foldXor_xor]
        apply foldXor_congr; intro t
        simp only [DEntry, and_xor_right]
      dsimp only
      rw [hev, hodd, hD]
      cases foldXor n0 (fun t => M0Entry b.val t.val && u t) <;>
      cases foldXor n0 (fun t => u t) <;>
      cases foldXor n1 (fun t => M0Entry b.val t.val && v t) <;>
      cases foldXor n1 (fun t => v t) <;>
      cases foldXor n1 (fun t => M1Entry b.val t.val && v t) <;> rfl
    rw [hE, hO]
  · rcases M0_isotropic_witness n0 hn0_ge2 with ⟨x, hAx, hiso⟩
    exact hasRank_isotropic_rank1_decouple (fun i j => M0Entry_sym i.val j.val) x hAx hiso h0 h1

/-! ### Exact Closed-Form Gray-Code Bit-Transition Formula for M0(n) -/

theorem gray_div_two (m : Nat) : gray m / 2 = gray (m / 2) := by
  simp only [gray, xor_div_two]

theorem gray_mod_two (m : Nat) :
    (gray m % 2 == 1) = xor (m % 2 == 1) ((m / 2) % 2 == 1) := by
  simp only [gray, xor_mod_two_eq_one]

theorem popcount_gray_pos (m : Nat) (hm : m ≥ 1) : popcount (gray m) ≥ 1 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h1 : m = 1
    · subst h1; decide
    · rw [popcount_step, gray_div_two]
      have := ih (m / 2) (by omega) (by omega)
      omega

theorem m0Nullity_step (n : Nat) (hn : n ≥ 3) :
    m0Nullity n = m0Nullity ((n + 1) / 2) + (n / 2) % 2 := by
  have h1 : n ≠ 0 := by omega
  have h2 : n ≠ 1 := by omega
  have h3 : (n + 1) / 2 ≠ 0 := by omega
  have h4 : (n + 1) / 2 ≠ 1 := by omega
  simp only [m0Nullity, h1, h2, h3, h4, ↓reduceIte]
  have hsub : (n + 1) / 2 - 1 = (n - 1) / 2 := by omega
  rw [hsub, popcount_step (gray (n - 1)), gray_div_two]
  have hpos := popcount_gray_pos ((n - 1) / 2) (by omega)
  have hmod : gray (n - 1) % 2 = (n / 2) % 2 := by
    have hg := gray_mod_two (n - 1)
    have hnm4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hnm4 with h | h | h | h
    · have a : (n - 1) % 2 = 1 := by omega
      have b : ((n - 1) / 2) % 2 = 1 := by omega
      have c : (n / 2) % 2 = 0 := by omega
      rw [a, b] at hg; simp at hg; omega
    · have a : (n - 1) % 2 = 0 := by omega
      have b : ((n - 1) / 2) % 2 = 0 := by omega
      have c : (n / 2) % 2 = 0 := by omega
      rw [a, b] at hg; simp at hg; omega
    · have a : (n - 1) % 2 = 1 := by omega
      have b : ((n - 1) / 2) % 2 = 0 := by omega
      have c : (n / 2) % 2 = 1 := by omega
      rw [a, b] at hg; simp at hg; omega
    · have a : (n - 1) % 2 = 0 := by omega
      have b : ((n - 1) / 2) % 2 = 1 := by omega
      have c : (n / 2) % 2 = 1 := by omega
      rw [a, b] at hg; simp at hg; omega
  omega

theorem m0Nullity_le (n : Nat) : m0Nullity n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; decide
    · by_cases h1 : n = 1
      · subst h1; decide
      · by_cases h2 : n = 2
        · subst h2; decide
        · rw [m0Nullity_step n (by omega)]
          have := ih ((n + 1) / 2) (by omega)
          omega

/-- MAIN THEOREM 1A: Exact F_2-rank of the carry-free XOR-sum parity matrix M0(n) ∀ n : Nat. -/
theorem M0_hasRank (n : Nat) : HasRank (M0Mat n) (n - m0Nullity n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; exact hasRank_congr (fun i => Fin.elim0 i) hasRank_zero
    · by_cases h1 : n = 1
      · subst h1
        have hz : ∀ i j : Fin 1, M0Mat 1 i j = matZero 1 1 i j := by decide
        exact hasRank_congr hz hasRank_zero
      · by_cases h2 : n = 2
        · subst h2
          -- M0Mat 2 = [[0, 1], [1, 0]], which is its own inverse!
          have hinv_pt : ∀ i j : Fin 2, matMul (M0Mat 2) (M0Mat 2) i j = matId 2 i j := by decide
          have hinv : matMul (M0Mat 2) (M0Mat 2) = matId 2 := by
            funext i j; exact hinv_pt i j
          have hr : HasRank (M0Mat 2) 2 := hasRank_of_inv (M0Mat 2) (M0Mat 2) hinv hinv
          have hnu2 : 2 - m0Nullity 2 = 2 := by decide
          rw [hnu2]; exact hr
        · have hn3 : n ≥ 3 := by omega
          have h0_rk := ih ((n + 1) / 2) (by omega)
          have h1_rk := D_hasRank (n / 2)
          have hstep := M0_lsb_step n _ _ hn3 h0_rk h1_rk
          have hle0 := m0Nullity_le ((n + 1) / 2)
          have hnu := m0Nullity_step n hn3
          have heq : ((n + 1) / 2 - m0Nullity ((n + 1) / 2)) + 2 * ((n / 2) / 2) = n - m0Nullity n := by
            omega
          rw [heq] at hstep
          exact hstep

/-- MAIN THEOREM 1B: Exact F_2-nullity of M0(n) ∀ n : Nat. -/
theorem M0_hasNullity (n : Nat) : HasNullity (M0Mat n) (m0Nullity n) :=
  ⟨m0Nullity_le n, M0_hasRank n⟩

/-- MAIN THEOREM 1C: Closed-form Gray-code bit-transition nullity ∀ n ≥ 2. -/
theorem M0_gray_nullity (n : Nat) (hn : n ≥ 2) :
    HasNullity (M0Mat n) (popcount (gray (n - 1)) - 1) := by
  have h := M0_hasNullity n
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simpa [m0Nullity, h0, h1] using h

/-- MAIN THEOREM 1D: Exact 2^n-vector kernel cardinality of M0(n) ∀ n ≥ 2. -/
theorem M0_kerCount (n : Nat) (hn : n ≥ 2) :
    kerCount (M0Mat n) = 2 ^ (popcount (gray (n - 1)) - 1) :=
  hasNullity_kerCount (M0_gray_nullity n hn)

/-- Helper: popcount(gray(m)) = 1 ↔ ∃ k ≥ 1, m + 1 = 2^k (for m ≥ 1). -/
theorem popcount_gray_eq_one_iff (m : Nat) (hm : m ≥ 1) :
    popcount (gray m) = 1 ↔ ∃ k : Nat, k ≥ 1 ∧ m + 1 = 2 ^ k := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases h1 : m = 1
    · subst h1
      constructor
      · intro _; exact ⟨1, by omega, by decide⟩
      · intro _; decide
    · rw [popcount_step, gray_div_two]
      have hpos := popcount_gray_pos (m / 2) (by omega)
      have hih := ih (m / 2) (by omega) (by omega)
      constructor
      · intro hsum
        have hmod0 : gray m % 2 = 0 := by omega
        have hrec1 : popcount (gray (m / 2)) = 1 := by omega
        rcases hih.mp hrec1 with ⟨k, hk1, hpow⟩
        have hhalf_odd : (m / 2) % 2 = 1 := by
          have : 2 ^ k = 2 * 2 ^ (k - 1) := by
            cases k with
            | zero => omega
            | succ k' => simp [Nat.pow_succ]; omega
          omega
        have hm_odd : m % 2 = 1 := by
          have hg := gray_mod_two m
          rw [hmod0, hhalf_odd] at hg
          have hcases : m % 2 = 0 ∨ m % 2 = 1 := by omega
          rcases hcases with h | h <;> simp [h] at hg ⊢
        refine ⟨k + 1, by omega, ?_⟩
        have : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
        omega
      · rintro ⟨k, hk1, hpow⟩
        have hk2 : k ≥ 2 := by
          cases k with
          | zero => omega
          | succ k' =>
            cases k' with
            | zero => simp at hpow; omega
            | succ _ => omega
        have hpow_step : 2 ^ k = 2 * 2 ^ (k - 1) := by
          cases k with
          | zero => omega
          | succ k' => simp [Nat.pow_succ]; omega
        have hm_odd : m % 2 = 1 := by omega
        have hdiv : m / 2 + 1 = 2 ^ (k - 1) := by omega
        have hrec1 : popcount (gray (m / 2)) = 1 := hih.mpr ⟨k - 1, by omega, hdiv⟩
        have hhalf_odd : (m / 2) % 2 = 1 := by
          have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
            have hksub : k - 1 = (k - 2) + 1 := by omega
            rw [hksub, Nat.pow_succ]; omega
          omega
        have hmod0 : gray m % 2 = 0 := by
          have hg := gray_mod_two m
          rw [hm_odd, hhalf_odd] at hg; simp at hg; omega
        omega

/-- MAIN THEOREM 1E (Exact Invertibility Characterization):
    For n ≥ 1, M0(n) is invertible over F_2 iff n = 2^k for some k ≥ 1! -/
theorem M0_invertible_iff_pow2 (n : Nat) (hn : n ≥ 1) :
    HasRank (M0Mat n) n ↔ ∃ k : Nat, k ≥ 1 ∧ n = 2 ^ k := by
  by_cases h1 : n = 1
  · subst h1
    constructor
    · intro hr
      have h0 := M0_hasRank 1
      have := hasRank_unique hr h0
      simp [m0Nullity] at this
    · rintro ⟨k, hk1, heq⟩
      have hge : 2 ^ k ≥ 2 := by
        cases k with
        | zero => omega
        | succ k' => have := Nat.two_pow_pos k'; simp [Nat.pow_succ]; omega
      omega
  · have hn2 : n ≥ 2 := by omega
    have hnu := M0_gray_nullity n hn2
    constructor
    · intro hr
      have heq := hasRank_unique hr hnu.2
      have hpos := popcount_gray_pos (n - 1) (by omega)
      have h1_gray : popcount (gray (n - 1)) = 1 := by omega
      rcases (popcount_gray_eq_one_iff (n - 1) (by omega)).mp h1_gray with ⟨k, hk1, hpow⟩
      exact ⟨k, hk1, by omega⟩
    · rintro ⟨k, hk1, hpow⟩
      have h1_gray : popcount (gray (n - 1)) = 1 :=
        (popcount_gray_eq_one_iff (n - 1) (by omega)).mpr ⟨k, hk1, by omega⟩
      have hr := hnu.2
      rw [h1_gray] at hr
      simpa using hr

/-! ## Section 6: Theorem 3 — Induced Hypercube Family H(d, n) & MSB Involutive Schur-Automaton -/

theorem popcount_eq_zero_iff (n : Nat) : popcount n = 0 ↔ n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [popcount, popcountAux]
    · rw [popcount_step]
      have hrec := ih (n / 2) (by omega)
      constructor
      · intro hp; have : n % 2 = 0 := by omega
        have : popcount (n / 2) = 0 := by omega
        have : n / 2 = 0 := hrec.mp this
        omega
      · intro h; omega

theorem xor_eq_zero_iff (i j : Nat) : i ^^^ j = 0 ↔ i = j := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq; intro k
    have hk := congrArg (fun x => x.testBit k) h
    rw [Nat.testBit_xor, Nat.zero_testBit] at hk
    cases hi : i.testBit k <;> cases hj : j.testBit k <;> rw [hi, hj] at hk <;> first | rfl | cases hk
  · intro h; subst h; exact Nat.xor_self i

theorem xor_add_pow2_both (k i j : Nat) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    (i + 2 ^ k) ^^^ (j + 2 ^ k) = i ^^^ j := by
  induction k generalizing i j with
  | zero =>
    simp only [Nat.pow_zero] at hi hj ⊢
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; rfl
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
    apply Nat.eq_of_testBit_eq; intro t
    cases t with
    | zero =>
      rw [testBit_zero_eq_mod_two, testBit_zero_eq_mod_two, xor_mod_two_eq_one, xor_mod_two_eq_one]
      have h1 : (i + 2 ^ (k + 1)) % 2 = i % 2 := by omega
      have h2 : (j + 2 ^ (k + 1)) % 2 = j % 2 := by omega
      rw [h1, h2]
    | succ t =>
      rw [← Nat.testBit_div_two, ← Nat.testBit_div_two, xor_div_two, xor_div_two]
      have h1 : (i + 2 ^ (k + 1)) / 2 = i / 2 + 2 ^ k := by omega
      have h2 : (j + 2 ^ (k + 1)) / 2 = j / 2 + 2 ^ k := by omega
      rw [h1, h2, ih (i / 2) (j / 2) (by omega) (by omega)]

theorem nat_beq_comm (a b : Nat) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := Ne.symm h
    rw [beq_false_of_ne h, beq_false_of_ne h']

theorem div_lt_three {x h : Nat} (hpos : 0 < h) (hx : x < 3 * h) :
    x / h = 0 ∨ x / h = 1 ∨ x / h = 2 := by
  have hlt : x / h < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  cases hq : x / h with
  | zero => exact Or.inl rfl
  | succ q =>
    cases q with
    | zero => exact Or.inr (Or.inl rfl)
    | succ q' =>
      cases q' with
      | zero => exact Or.inr (Or.inr rfl)
      | succ _ => omega

theorem popcount_xor_add_pow2_left (k i j : Nat) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    popcount ((i + 2 ^ k) ^^^ j) = 1 + popcount (i ^^^ j) := by
  induction k generalizing i j with
  | zero =>
    simp only [Nat.pow_zero] at hi hj ⊢
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0; decide
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
    rw [popcount_step ((i + 2 ^ (k + 1)) ^^^ j), popcount_step (i ^^^ j),
        xor_div_two, xor_div_two]
    have hmod : ((i + 2 ^ (k + 1)) ^^^ j) % 2 = (i ^^^ j) % 2 := by
      have h1 := xor_mod_two_eq_one (i + 2 ^ (k + 1)) j
      have h2 := xor_mod_two_eq_one i j
      have hm : (i + 2 ^ (k + 1)) % 2 = i % 2 := by omega
      rw [hm, ← h2] at h1
      have c1 : ((i + 2 ^ (k + 1)) ^^^ j) % 2 = 0 ∨ ((i + 2 ^ (k + 1)) ^^^ j) % 2 = 1 := by omega
      have c2 : (i ^^^ j) % 2 = 0 ∨ (i ^^^ j) % 2 = 1 := by omega
      rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
      · rw [c1, c2]
      · rw [c1, c2] at h1; cases h1
      · rw [c1, c2] at h1; cases h1
      · rw [c1, c2]
    have hdiv : (i + 2 ^ (k + 1)) / 2 = i / 2 + 2 ^ k := by omega
    rw [hmod, hdiv, ih (i / 2) (j / 2) (by omega) (by omega)]
    omega

theorem HEntry_sym (d : Bool) (i j : Nat) : HEntry d i j = HEntry d j i := by
  simp only [HEntry, Nat.xor_comm, nat_beq_comm]

theorem HEntry_msb_diag (d : Bool) (k i j : Nat) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    HEntry d (i + 2 ^ k) (j + 2 ^ k) = HEntry d i j := by
  simp only [HEntry, xor_add_pow2_both k i j hi hj]
  by_cases h : i = j
  · subst h; simp
  · have h2 : i + 2 ^ k ≠ j + 2 ^ k := by omega
    simp [beq_false_of_ne h, beq_false_of_ne h2]

theorem HEntry_msb_off (d : Bool) (k i j : Nat) (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    HEntry d (i + 2 ^ k) j = (i == j) := by
  simp only [HEntry, popcount_xor_add_pow2_left k i j hi hj]
  have hne : (i + 2 ^ k == j) = false := beq_false_of_ne (by omega)
  rw [hne, Bool.and_false, xor_false_right]
  by_cases h : i = j
  · subst h
    have hp : popcount (i ^^^ i) = 0 := by rw [Nat.xor_self]; rfl
    rw [hp]; simp
  · have hp : popcount (i ^^^ j) ≠ 0 := by
      intro hz
      exact h ((xor_eq_zero_iff i j).mp ((popcount_eq_zero_iff _).mp hz))
    have hne1 : (1 + popcount (i ^^^ j) == 1) = false := beq_false_of_ne (by omega)
    rw [hne1, beq_false_of_ne h]

/-- Theorem 3A: Exact F_2-squaring law on powers of 2: H(d, 2^k)^2 = ((k mod 2 = 1) ≠ d) * I. -/
theorem H_pow2_sq (d : Bool) (k : Nat) :
    matMul (HMat d (2 ^ k)) (HMat d (2 ^ k)) =
    if (k % 2 == 1) != d then matId (2 ^ k) else matZero (2 ^ k) (2 ^ k) := by
  induction k with
  | zero =>
    funext i j
    have hi : i.val = 0 := by have := i.isLt; simp at this; omega
    have hj : j.val = 0 := by have := j.isLt; simp at this; omega
    have hi0 : i = ⟨0, by decide⟩ := Fin.ext hi
    have hj0 : j = ⟨0, by decide⟩ := Fin.ext hj
    subst hi0; subst hj0; cases d <;> decide
  | succ k ih =>
    funext i j
    simp only [matMul]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    rw [foldXor_cast hpow _
      (fun t : Fin (2 ^ k + 2 ^ k) => HMat d (2 ^ (k + 1)) i ⟨t.val, by omega⟩ &&
                                      HMat d (2 ^ (k + 1)) ⟨t.val, by omega⟩ j) (fun _ => rfl)]
    rw [foldXor_add (2 ^ k) (2 ^ k)]
    have hpar : ((k + 1) % 2 == 1) = !((k % 2 == 1)) := by
      have : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases this with h | h <;> simp [h, Nat.add_mod]
    have hne_flip : (((k + 1) % 2 == 1) != d) = !((k % 2 == 1) != d) := by
      rw [hpar]; cases (k % 2 == 1) <;> cases d <;> rfl
    rw [hne_flip]
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
    · -- Top-left: A^2 ⊕ I
      have h1 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨t.val, by omega⟩ j) =
          matMul (HMat d (2 ^ k)) (HMat d (2 ^ k)) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := rfl
      have h2 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨2 ^ k + t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨2 ^ k + t.val, by omega⟩ j) =
          (i.val == j.val) := by
        rw [foldXor_single ⟨i.val, hi⟩]
        · simp only [HMat]
          rw [HEntry_sym, Nat.add_comm (2 ^ k) i.val, HEntry_msb_off d k i.val i.val hi hi,
              HEntry_msb_off d k i.val j.val hi hj]
          simp
        · intro t ht
          simp only [HMat]
          rw [HEntry_sym, Nat.add_comm (2 ^ k) t.val, HEntry_msb_off d k t.val i.val t.isLt hi]
          have hne : (t.val == i.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h))
          simp [hne]
      rw [h1, ih, h2]
      cases ((k % 2 == 1) != d) <;> simp [matId, matZero]
    · -- Top-right: A*I ⊕ I*A = 0
      let j' : Fin (2 ^ k) := ⟨j.val - 2 ^ k, by omega⟩
      have hj_eq : j.val = j'.val + 2 ^ k := by dsimp [j']; omega
      have h1 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨t.val, by omega⟩ j) =
          HEntry d i.val j'.val := by
        rw [foldXor_single j']
        · simp only [HMat]
          rw [hj_eq, HEntry_sym d j'.val (j'.val + 2 ^ k), HEntry_msb_off d k j'.val j'.val j'.isLt j'.isLt]
          simp
        · intro t ht
          simp only [HMat]
          rw [hj_eq, HEntry_sym d t.val (j'.val + 2 ^ k), HEntry_msb_off d k j'.val t.val j'.isLt t.isLt]
          have hne : (j'.val == t.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h.symm))
          simp [hne]
      have h2 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨2 ^ k + t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨2 ^ k + t.val, by omega⟩ j) =
          HEntry d i.val j'.val := by
        rw [foldXor_single ⟨i.val, hi⟩]
        · simp only [HMat]
          rw [HEntry_sym d i.val (2 ^ k + i.val), Nat.add_comm (2 ^ k) i.val,
              HEntry_msb_off d k i.val i.val hi hi, hj_eq, HEntry_msb_diag d k i.val j'.val hi j'.isLt]
          simp
        · intro t ht
          simp only [HMat]
          rw [HEntry_sym d i.val (2 ^ k + t.val), Nat.add_comm (2 ^ k) t.val,
              HEntry_msb_off d k t.val i.val t.isLt hi]
          have hne : (t.val == i.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h))
          simp [hne]
      rw [h1, h2, xor_self]
      have hne : (i.val == j.val) = false := beq_false_of_ne (by omega)
      cases ((k % 2 == 1) != d) <;> simp [matId, matZero, hne]
    · -- Bottom-left: I*A ⊕ A*I = 0
      let i' : Fin (2 ^ k) := ⟨i.val - 2 ^ k, by omega⟩
      have hi_eq : i.val = i'.val + 2 ^ k := by dsimp [i']; omega
      have h1 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨t.val, by omega⟩ j) =
          HEntry d i'.val j.val := by
        rw [foldXor_single i']
        · simp only [HMat]
          rw [hi_eq, HEntry_msb_off d k i'.val i'.val i'.isLt i'.isLt]
          simp
        · intro t ht
          simp only [HMat]
          rw [hi_eq, HEntry_msb_off d k i'.val t.val i'.isLt t.isLt]
          have hne : (i'.val == t.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h.symm))
          simp [hne]
      have h2 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨2 ^ k + t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨2 ^ k + t.val, by omega⟩ j) =
          HEntry d i'.val j.val := by
        rw [foldXor_single ⟨j.val, hj⟩]
        · simp only [HMat]
          rw [hi_eq, Nat.add_comm (2 ^ k) j.val, HEntry_msb_diag d k i'.val j.val i'.isLt hj,
              HEntry_msb_off d k j.val j.val hj hj]
          simp
        · intro t ht
          simp only [HMat]
          rw [Nat.add_comm (2 ^ k) t.val, HEntry_msb_off d k t.val j.val t.isLt hj]
          have hne : (t.val == j.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h))
          simp [hne]
      rw [h1, h2, xor_self]
      have hne : (i.val == j.val) = false := beq_false_of_ne (by omega)
      cases ((k % 2 == 1) != d) <;> simp [matId, matZero, hne]
    · -- Bottom-right: I ⊕ A^2
      let i' : Fin (2 ^ k) := ⟨i.val - 2 ^ k, by omega⟩
      let j' : Fin (2 ^ k) := ⟨j.val - 2 ^ k, by omega⟩
      have hi_eq : i.val = i'.val + 2 ^ k := by dsimp [i']; omega
      have hj_eq : j.val = j'.val + 2 ^ k := by dsimp [j']; omega
      have hij : (i.val == j.val) = (i'.val == j'.val) := by
        by_cases h : i.val = j.val
        · have h' : i'.val = j'.val := by omega
          simp [h, h']
        · have h' : i'.val ≠ j'.val := by omega
          simp [beq_false_of_ne h, beq_false_of_ne h']
      have h1 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨t.val, by omega⟩ j) =
          (i'.val == j'.val) := by
        rw [foldXor_single i']
        · simp only [HMat]
          rw [hi_eq, hj_eq, HEntry_msb_off d k i'.val i'.val i'.isLt i'.isLt,
              HEntry_sym d i'.val (j'.val + 2 ^ k), HEntry_msb_off d k j'.val i'.val j'.isLt i'.isLt]
          simp [nat_beq_comm]
        · intro t ht
          simp only [HMat]
          rw [hi_eq, HEntry_msb_off d k i'.val t.val i'.isLt t.isLt]
          have hne : (i'.val == t.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h.symm))
          simp [hne]
      have h2 : foldXor (2 ^ k) (fun t : Fin (2 ^ k) =>
          HMat d (2 ^ (k + 1)) i ⟨2 ^ k + t.val, by omega⟩ && HMat d (2 ^ (k + 1)) ⟨2 ^ k + t.val, by omega⟩ j) =
          matMul (HMat d (2 ^ k)) (HMat d (2 ^ k)) i' j' := by
        simp only [matMul, HMat]
        apply foldXor_congr; intro t
        rw [hi_eq, hj_eq, Nat.add_comm (2 ^ k) t.val,
            HEntry_msb_diag d k i'.val t.val i'.isLt t.isLt,
            HEntry_msb_diag d k t.val j'.val t.isLt j'.isLt]
      rw [h1, h2, ih]
      cases ((k % 2 == 1) != d) <;> simp [matId, matZero, hij]

/-- Rule 1 (Octave Freeze): When (k mod 2 = 1) ≠ d and r ≤ 2^k, rank(H(d, 2^k + r)) = 2^k! -/
theorem H_msb_freeze (d : Bool) (k r : Nat)
    (hpar : ((k % 2 == 1) != d) = true) (hr : r ≤ 2 ^ k) :
    HasRank (HMat d (2 ^ k + r)) (2 ^ k) := by
  let A := HMat d (2 ^ k)
  let E : Mat (2 ^ k) r := fun i j => i.val == j.val
  let ET : Mat r (2 ^ k) := fun i j => i.val == j.val
  let D := HMat d r
  have hblock : ∀ i j : Fin (2 ^ k + r), HMat d (2 ^ k + r) i j = blockMat A E ET D i j := by
    intro i j
    simp only [blockMat, HMat, A, E, ET, D]
    by_cases hi : i.val < 2 ^ k <;> by_cases hj : j.val < 2 ^ k
    · simp [hi, hj]
    · simp only [hi, hj, ↓reduceDIte]
      let j' := j.val - 2 ^ k
      have hj_eq : j.val = j' + 2 ^ k := by omega
      change HEntry d i.val j.val = (i.val == j')
      rw [hj_eq, HEntry_sym, HEntry_msb_off d k j' i.val (by omega) hi, nat_beq_comm]
    · simp only [hi, hj, ↓reduceDIte]
      let i' := i.val - 2 ^ k
      have hi_eq : i.val = i' + 2 ^ k := by omega
      change HEntry d i.val j.val = (i' == j.val)
      rw [hi_eq, HEntry_msb_off d k i' j.val (by omega) hj]
    · simp only [hi, hj, ↓reduceDIte]
      let i' := i.val - 2 ^ k
      let j' := j.val - 2 ^ k
      have hi_eq : i.val = i' + 2 ^ k := by omega
      have hj_eq : j.val = j' + 2 ^ k := by omega
      change HEntry d i.val j.val = HEntry d i' j'
      rw [hi_eq, hj_eq, HEntry_msb_diag d k i' j' (by omega) (by omega)]
  apply hasRank_congr hblock
  have hsq : matMul A A = matId (2 ^ k) := by
    have h := H_pow2_sq d k; simp only [hpar, ↓reduceIte] at h; exact h
  have h0 : HasRank (matXor D (matMul ET (matMul A E))) 0 := by
    apply hasRank_congr (M2 := matZero r r)
    · intro i j
      simp only [matXor, matMul, matZero, ET, E, A, D, HMat]
      rw [foldXor_single ⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩]
      · simp only [beq_self_eq_true, Bool.true_and]
        rw [foldXor_single ⟨j.val, Nat.lt_of_lt_of_le j.isLt hr⟩]
        · simp
        · intro t ht
          have hne : (t.val == j.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h))
          simp [hne]
      · intro t ht
        have hne : (i.val == t.val) = false := beq_false_of_ne (fun h => ht (Fin.ext h.symm))
        simp [hne]
    · exact hasRank_zero
  simpa using hasRank_schur_inv hsq hsq h0

/-- Rule 2 (Slope-+2 Surge): When k ≥ 1, (k mod 2 = 1) = d, and r ≤ 2^(k-1),
    rank(H(d, 2^k + r)) = 2^(k-1) + 2 * r! -/
theorem H_msb_ramp (d : Bool) (k r : Nat) (hk : k ≥ 1)
    (hpar : ((k % 2 == 1) != d) = false) (hr : r ≤ 2 ^ (k - 1)) :
    HasRank (HMat d (2 ^ k + r)) (2 ^ (k - 1) + 2 * r) := by
  let h := 2 ^ (k - 1)
  have h2k : 2 ^ k = h + h := by
    have : k = (k - 1) + 1 := by omega
    rw [this, Nat.pow_succ]; dsimp [h]; omega
  have hdim : 2 ^ k + r = h + (h + r) := by omega
  let U := HMat d h
  have hpar_prev : (((k - 1) % 2 == 1) != d) = true := by
    have : (k - 1) % 2 = 0 ∨ (k - 1) % 2 = 1 := by omega
    rcases this with h0 | h1
    · have hk1 : k % 2 = 1 := by omega
      rw [hk1] at hpar; rw [h0]; cases d <;> simp at hpar ⊢
    · have hk0 : k % 2 = 0 := by omega
      rw [hk0] at hpar; rw [h1]; cases d <;> simp at hpar ⊢
  have hUsq : matMul U U = matId h := by
    have := H_pow2_sq d (k - 1); simp only [hpar_prev, ↓reduceIte] at this; exact this
  -- Split H(d, h + (h + r)) into [[U, B], [C, D]]!
  let B : Mat h (h + r) := fun i j =>
    if j.val < h then (i.val == j.val) else (i.val == j.val - h)
  let C : Mat (h + r) h := fun i j =>
    if i.val < h then (i.val == j.val) else (i.val - h == j.val)
  let D : Mat (h + r) (h + r) := blockMat U (matZero h r) (matZero r h) (HMat d r)
  have hM_eq : ∀ i j : Fin (h + (h + r)),
      HMat d (h + (h + r)) i j = blockMat U B C D i j := by
    intro i j
    simp only [blockMat, HMat, U, B, C, D]
    by_cases hi : i.val < h <;> by_cases hj : j.val < h
    · simp [hi, hj]
    · simp only [hi, hj, ↓reduceDIte]
      by_cases hj2 : j.val - h < h
      · simp only [hj2, ↓reduceIte]
        let j' := j.val - h
        have hj_eq : j.val = j' + h := by omega
        change HEntry d i.val j.val = (i.val == j')
        rw [hj_eq, HEntry_sym, HEntry_msb_off d (k - 1) j' i.val hj2 hi, nat_beq_comm]
      · simp only [hj2, ↓reduceIte]
        let j' := j.val - 2 ^ k
        have hj_eq : j.val = j' + 2 ^ k := by omega
        have hsub : j.val - h - h = j' := by omega
        change HEntry d i.val j.val = (i.val == j.val - h - h)
        rw [hsub, hj_eq, HEntry_sym, HEntry_msb_off d k j' i.val (by omega) (by omega), nat_beq_comm]
    · simp only [hi, hj, ↓reduceDIte]
      by_cases hi2 : i.val - h < h
      · simp only [hi2, ↓reduceIte]
        let i' := i.val - h
        have hi_eq : i.val = i' + h := by omega
        change HEntry d i.val j.val = (i' == j.val)
        rw [hi_eq, HEntry_msb_off d (k - 1) i' j.val hi2 hj]
      · simp only [hi2, ↓reduceIte]
        let i' := i.val - 2 ^ k
        have hi_eq : i.val = i' + 2 ^ k := by omega
        have hsub : i.val - h - h = i' := by omega
        change HEntry d i.val j.val = (i.val - h - h == j.val)
        rw [hsub, hi_eq, HEntry_msb_off d k i' j.val (by omega) (by omega)]
    · simp only [hi, hj, ↓reduceDIte]
      by_cases hi2 : i.val - h < h <;> by_cases hj2 : j.val - h < h
      · simp only [hi2, hj2, ↓reduceDIte]
        let i' := i.val - h
        let j' := j.val - h
        have hi_eq : i.val = i' + h := by omega
        have hj_eq : j.val = j' + h := by omega
        change HEntry d i.val j.val = HEntry d i' j'
        rw [hi_eq, hj_eq, HEntry_msb_diag d (k - 1) i' j' hi2 hj2]
      · simp only [hi2, hj2, ↓reduceDIte, matZero]
        let j' := j.val - 2 ^ k
        have hj_eq : j.val = j' + 2 ^ k := by omega
        rw [hj_eq, HEntry_sym, HEntry_msb_off d k j' i.val (by omega) (by omega)]
        exact beq_false_of_ne (by omega)
      · simp only [hi2, hj2, ↓reduceDIte, matZero]
        let i' := i.val - 2 ^ k
        have hi_eq : i.val = i' + 2 ^ k := by omega
        rw [hi_eq, HEntry_msb_off d k i' j.val (by omega) (by omega)]
        exact beq_false_of_ne (by omega)
      · simp only [hi2, hj2, ↓reduceDIte]
        let i' := i.val - 2 ^ k
        let j' := j.val - 2 ^ k
        have hi_eq : i.val = i' + 2 ^ k := by omega
        have hj_eq : j.val = j' + 2 ^ k := by omega
        have hs1 : i.val - h - h = i' := by omega
        have hs2 : j.val - h - h = j' := by omega
        change HEntry d i.val j.val = HEntry d (i.val - h - h) (j.val - h - h)
        rw [hs1, hs2, hi_eq, hj_eq, HEntry_msb_diag d k i' j' (by omega) (by omega)]
  -- Cast dimension 2^k + r = h + (h + r)
  have hcast : HasRank (HMat d (h + (h + r))) (h + 2 * r) → HasRank (HMat d (2 ^ k + r)) (h + 2 * r) := fun hR =>
    hasRank_cast_rows hdim (HMat d (2 ^ k + r)) (fun i j => HEntry d i.val j.val) (fun _ _ => rfl)
      (hasRank_cast_cols hdim (fun i j => HEntry d i.val j.val) (HMat d (h + (h + r))) (fun _ _ => rfl) hR)
  apply hcast
  apply hasRank_congr hM_eq
  -- Apply Involutive Schur Elimination on pivot U!
  apply hasRank_schur_inv hUsq hUsq
  -- Schur complement S = D ⊕ C * U * B = [[0, U * E], [E^T * U, 0]]!
  let E : Mat h r := fun i j => i.val == j.val
  let ET : Mat r h := fun i j => i.val == j.val
  have hS_eq : ∀ i j : Fin (h + r),
      matXor D (matMul C (matMul U B)) i j =
      blockMat (matZero h h) (matMul U E) (matMul ET U) (matZero r r) i j := by
    intro i j
    -- Compute C * U * B entry (i, j) = U[i', j'] where i' = i (if < h) else i - h!
    have hCUB : matMul C (matMul U B) i j =
        HEntry d (if i.val < h then i.val else i.val - h) (if j.val < h then j.val else j.val - h) := by
      simp only [matMul, C, U, B, HMat]
      let i' : Fin h := if hc : i.val < h then ⟨i.val, hc⟩ else ⟨i.val - h, by omega⟩
      let j' : Fin h := if hc : j.val < h then ⟨j.val, hc⟩ else ⟨j.val - h, by omega⟩
      have hi'_val : i'.val = if i.val < h then i.val else i.val - h := by
        dsimp [i']; split <;> rfl
      have hj'_val : j'.val = if j.val < h then j.val else j.val - h := by
        dsimp [j']; split <;> rfl
      rw [← hi'_val, ← hj'_val]
      rw [foldXor_single i']
      · have hci : (if i.val < h then (i.val == i'.val) else (i.val - h == i'.val)) = true := by
          rw [hi'_val]; split <;> simp
        rw [hci, Bool.true_and]
        rw [foldXor_single j']
        · have hcj : (if j.val < h then (j'.val == j.val) else (j'.val == j.val - h)) = true := by
            rw [hj'_val]; split <;> simp
          rw [hcj, Bool.and_true]
        · intro t ht
          have hne : (if j.val < h then (t.val == j.val) else (t.val == j.val - h)) = false := by
            have htj : t.val ≠ j'.val := fun heq => ht (Fin.ext heq)
            rw [hj'_val] at htj
            by_cases hjl : j.val < h <;> simp [hjl] at htj ⊢ <;> exact htj
          rw [hne, Bool.and_false]
      · intro t ht
        have hne : (if i.val < h then (i.val == t.val) else (i.val - h == t.val)) = false := by
          have hit : i'.val ≠ t.val := fun heq => ht (Fin.ext heq.symm)
          rw [hi'_val] at hit
          by_cases hil : i.val < h <;> simp [hil] at hit ⊢ <;> exact hit
        rw [hne, Bool.false_and]
    simp only [matXor, hCUB, blockMat, D, matZero]
    by_cases hi : i.val < h <;> by_cases hj : j.val < h
    · simp [hi, hj, U, HMat]
    · simp only [hi, hj, ↓reduceDIte, ↓reduceIte, xor_false_left, matMul, U, E, HMat]
      rw [foldXor_single ⟨j.val - h, by omega⟩]
      · simp
      · intro t ht
        have hne : (t.val == j.val - h) = false := beq_false_of_ne (fun heq => ht (Fin.ext heq))
        simp [hne]
    · simp only [hi, hj, ↓reduceDIte, ↓reduceIte, xor_false_left, matMul, U, ET, HMat]
      rw [foldXor_single ⟨i.val - h, by omega⟩]
      · simp
      · intro t ht
        have hne : (i.val - h == t.val) = false := beq_false_of_ne (fun heq => ht (Fin.ext heq.symm))
        simp [hne]
    · simp [hi, hj, HMat]
  apply hasRank_congr hS_eq
  -- Eliminate U via blockDiag (ofMatInv U U) (refl r) on both sides -> [[0, E], [ET, 0]]!
  let eU := LinEquiv.ofMatInv U U hUsq hUsq
  let P := LinEquiv.blockDiag eU (LinEquiv.refl r)
  let Q := LinEquiv.blockDiag eU (LinEquiv.refl r)
  apply hasRank_of_equiv rfl rfl P Q (M' := blockMat (matZero h h) E ET (matZero r r))
  · intro w
    rw [← joinVec_split w]
    simp only [P, Q, eU, LinEquiv.blockDiag, LinEquiv.ofMatInv, LinEquiv.refl, id_eq,
      splitLeft_joinVec, splitRight_joinVec]
    rw [matVec_blockMat, matVec_blockMat]
    simp only [matVec_zero_mat, vxor_zero_left, vxor_zero_right, splitLeft_joinVec, splitRight_joinVec]
    congr 1
    · rw [matVec_mul, ← matVec_mul U U, hUsq, matVec_id]
    · rw [matVec_mul, ← matVec_mul U U, hUsq, matVec_id]
  · have h2r : 2 * r = r + r := by omega
    rw [h2r]
    have hd : h = r + (h - r) := by omega
    have hE : HasRank E r := by
      let E' : Mat (r + (h - r)) r := fun i j => i.val == j.val
      have hE' : HasRank E' r := hasRank_rect_tall_of_top_full (hasRank_congr (fun _ _ => rfl) (hasRank_id r))
      exact hasRank_cast_rows hd E E' (fun _ _ => rfl) hE'
    have hET : HasRank ET r := by
      let ET' : Mat r (r + (h - r)) := fun i j => i.val == j.val
      have hET' : HasRank ET' r := hasRank_rect_wide_of_left_full (hasRank_congr (fun _ _ => rfl) (hasRank_id r))
      exact hasRank_cast_cols hd ET ET' (fun _ _ => rfl) hET'
    exact hasRank_antidiag hE hET

/-- Rule 3 (Self-Similar Restart): When k ≥ 1, (k mod 2 = 1) = d, and s ≤ 2^(k-1),
    H(d, 3 * 2^(k-1) + s) ~ I_{3 * 2^(k-1)} ⊕ H(d, s), proved via the explicit 3x3 block inverse! -/
theorem H_msb_restart (d : Bool) (k s rs : Nat) (hk : k ≥ 1)
    (hpar : ((k % 2 == 1) != d) = false) (hs : s ≤ 2 ^ (k - 1))
    (hRs : HasRank (HMat d s) rs) :
    HasRank (HMat d (3 * 2 ^ (k - 1) + s)) (3 * 2 ^ (k - 1) + rs) := by
  let h := 2 ^ (k - 1)
  have h2k : 2 ^ k = 2 * h := by
    have : k = (k - 1) + 1 := by omega
    rw [this, Nat.pow_succ]; dsimp [h]; omega
  let U := HMat d h
  have hpar_prev : (((k - 1) % 2 == 1) != d) = true := by
    have : (k - 1) % 2 = 0 ∨ (k - 1) % 2 = 1 := by omega
    rcases this with h0 | h1
    · have hk1 : k % 2 = 1 := by omega
      rw [hk1] at hpar; rw [h0]; cases d <;> simp at hpar ⊢
    · have hk0 : k % 2 = 0 := by omega
      rw [hk0] at hpar; rw [h1]; cases d <;> simp at hpar ⊢
  have hUsq : matMul U U = matId h := by
    have := H_pow2_sq d (k - 1); simp only [hpar_prev, ↓reduceIte] at this; exact this
  -- Explicit 3x3 block inverse of A = HMat d (3 * h):
  -- Ainv = [[U, I, I], [I, 0, U], [I, U, 0]]!
  let A := HMat d (3 * h)
  let Ainv : Mat (3 * h) (3 * h) := fun i j =>
    let bi := i.val / h; let ri := i.val % h
    let bj := j.val / h; let rj := j.val % h
    if bi = 0 then
      if bj = 0 then HEntry d ri rj else (ri == rj)
    else if bi = 1 then
      if bj = 0 then (ri == rj) else if bj = 1 then false else HEntry d ri rj
    else
      if bj = 0 then (ri == rj) else if bj = 1 then HEntry d ri rj else false
  -- Verify A's 3x3 block formula: [[U, I, I], [I, U, 0], [I, 0, U]]
  have hA_entry : ∀ i j : Fin (3 * h),
      A i j =
        let bi := i.val / h; let ri := i.val % h
        let bj := j.val / h; let rj := j.val % h
        if bi = 0 then
          if bj = 0 then HEntry d ri rj else (ri == rj)
        else if bi = 1 then
          if bj = 0 then (ri == rj) else if bj = 1 then HEntry d ri rj else false
        else
          if bj = 0 then (ri == rj) else if bj = 1 then false else HEntry d ri rj := by
    intro i j
    have hpos : 0 < h := Nat.two_pow_pos (k - 1)
    have hri : i.val % h < h := Nat.mod_lt i.val hpos
    have hrj : j.val % h < h := Nat.mod_lt j.val hpos
    have hbi := div_lt_three hpos i.isLt
    have hbj := div_lt_three hpos j.isLt
    have hidec : i.val = (i.val / h) * h + i.val % h := by
      have := Nat.div_add_mod i.val h; rw [Nat.mul_comm] at this; omega
    have hjdec : j.val = (j.val / h) * h + j.val % h := by
      have := Nat.div_add_mod j.val h; rw [Nat.mul_comm] at this; omega
    let ri := i.val % h
    let rj := j.val % h
    simp only [A, HMat]
    rcases hbi with hi | hi | hi <;> rcases hbj with hj | hj | hj <;>
      simp only [hi, hj, ↓reduceIte,
        show ¬ (1 = 0) by decide, show ¬ (2 = 0) by decide, show ¬ (2 = 1) by decide]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri := by dsimp [ri]; omega
      have h2 : j.val = rj := by dsimp [rj]; omega
      change HEntry d i.val j.val = HEntry d ri rj
      rw [h1, h2]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri := by dsimp [ri]; omega
      have h2 : j.val = rj + h := by dsimp [rj]; omega
      change HEntry d i.val j.val = (ri == rj)
      rw [h1, h2, HEntry_sym, HEntry_msb_off d (k - 1) rj ri hrj hri, nat_beq_comm]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri := by dsimp [ri]; omega
      have h2 : j.val = rj + 2 ^ k := by dsimp [rj]; omega
      change HEntry d i.val j.val = (ri == rj)
      rw [h1, h2, HEntry_sym, HEntry_msb_off d k rj ri (by omega) (by omega), nat_beq_comm]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + h := by dsimp [ri]; omega
      have h2 : j.val = rj := by dsimp [rj]; omega
      change HEntry d i.val j.val = (ri == rj)
      rw [h1, h2, HEntry_msb_off d (k - 1) ri rj hri hrj]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + h := by dsimp [ri]; omega
      have h2 : j.val = rj + h := by dsimp [rj]; omega
      change HEntry d i.val j.val = HEntry d ri rj
      rw [h1, h2, HEntry_msb_diag d (k - 1) ri rj hri hrj]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + h := by dsimp [ri]; omega
      have h2 : j.val = rj + 2 ^ k := by dsimp [rj]; omega
      change HEntry d i.val j.val = false
      rw [h2, HEntry_sym, HEntry_msb_off d k rj i.val (by omega) (by omega)]
      exact beq_false_of_ne (by omega)
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + 2 ^ k := by dsimp [ri]; omega
      have h2 : j.val = rj := by dsimp [rj]; omega
      change HEntry d i.val j.val = (ri == rj)
      rw [h1, h2, HEntry_msb_off d k ri rj (by omega) (by omega)]
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + 2 ^ k := by dsimp [ri]; omega
      have h2 : j.val = rj + h := by dsimp [rj]; omega
      change HEntry d i.val j.val = false
      rw [h1, HEntry_msb_off d k ri j.val (by omega) (by omega)]
      exact beq_false_of_ne (by omega)
    · rw [hi] at hidec; rw [hj] at hjdec
      have h1 : i.val = ri + 2 ^ k := by dsimp [ri]; omega
      have h2 : j.val = rj + 2 ^ k := by dsimp [rj]; omega
      change HEntry d i.val j.val = HEntry d ri rj
      rw [h1, h2, HEntry_msb_diag d k ri rj (by omega) (by omega)]
  -- Helper: split foldXor (3 * h) into 3 blocks of size h
  have hfold3 : ∀ (f : Fin (3 * h) → Bool),
      foldXor (3 * h) f =
      xor (xor (foldXor h (fun t => f ⟨t.val, by omega⟩))
               (foldXor h (fun t => f ⟨h + t.val, by omega⟩)))
          (foldXor h (fun t => f ⟨2 * h + t.val, by omega⟩)) := by
    intro f
    have h3 : 3 * h = (h + h) + h := by omega
    rw [foldXor_cast h3 f (fun t : Fin ((h + h) + h) => f ⟨t.val, by omega⟩) (fun _ => rfl)]
    rw [foldXor_add (h + h) h, foldXor_add h h]
    congr 1
    apply foldXor_congr; intro t; congr 1; apply Fin.ext; dsimp; omega
  -- Helper lemmas for single-block products of U and I
  have hUU : ∀ a b : Fin h, foldXor h (fun t : Fin h => HEntry d a.val t.val && HEntry d t.val b.val) = (a.val == b.val) := by
    intro a b
    have h := congrFun (congrFun hUsq a) b
    simpa [matMul, matId, U, HMat] using h
  have hUI : ∀ a b : Fin h, foldXor h (fun t : Fin h => HEntry d a.val t.val && (t.val == b.val)) = HEntry d a.val b.val := by
    intro a b
    rw [foldXor_single b]
    · simp
    · intro t ht; simp [beq_false_of_ne (fun heq => ht (Fin.ext heq))]
  have hIU : ∀ a b : Fin h, foldXor h (fun t : Fin h => (a.val == t.val) && HEntry d t.val b.val) = HEntry d a.val b.val := by
    intro a b
    rw [foldXor_single a]
    · simp
    · intro t ht; simp [beq_false_of_ne (fun heq => ht (Fin.ext heq.symm))]
  have hII : ∀ a b : Fin h, foldXor h (fun t : Fin h => (a.val == t.val) && (t.val == b.val)) = (a.val == b.val) := by
    intro a b
    rw [foldXor_single a]
    · simp
    · intro t ht; simp [beq_false_of_ne (fun heq => ht (Fin.ext heq.symm))]
  -- Prove A * Ainv = I (and by symmetry Ainv * A = I!)
  have hAAinv : matMul A Ainv = matId (3 * h) := by
    funext i j
    simp only [matMul, matId]
    rw [hfold3]
    have hpos : 0 < h := Nat.two_pow_pos (k - 1)
    have hri : i.val % h < h := Nat.mod_lt i.val hpos
    have hrj : j.val % h < h := Nat.mod_lt j.val hpos
    let ri : Fin h := ⟨i.val % h, hri⟩
    let rj : Fin h := ⟨j.val % h, hrj⟩
    have hbi := div_lt_three hpos i.isLt
    have hbj := div_lt_three hpos j.isLt
    have ht0 : ∀ t : Fin h, t.val / h = 0 ∧ t.val % h = t.val := fun t =>
      ⟨Nat.div_eq_of_lt t.isLt, Nat.mod_eq_of_lt t.isLt⟩
    have ht1 : ∀ t : Fin h, (h + t.val) / h = 1 ∧ (h + t.val) % h = t.val := fun t => by
      constructor
      · rw [Nat.add_comm, Nat.add_div_right _ hpos, Nat.div_eq_of_lt t.isLt]
      · rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
    have ht2 : ∀ t : Fin h, (2 * h + t.val) / h = 2 ∧ (2 * h + t.val) % h = t.val := fun t => by
      have h1 : 2 * h + t.val = t.val + h * 2 := by omega
      constructor
      · rw [h1, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt t.isLt]
      · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]
    have hij_same : ∀ (b : Nat), i.val / h = b → j.val / h = b → (i.val == j.val) = (ri.val == rj.val) := by
      intro b h1 h2
      have d1 := Nat.div_add_mod i.val h
      have d2 := Nat.div_add_mod j.val h
      rw [h1] at d1; rw [h2] at d2
      by_cases he : i.val = j.val
      · have : ri.val = rj.val := by dsimp [ri, rj]; omega
        simp [he, this]
      · have : ri.val ≠ rj.val := by dsimp [ri, rj]; omega
        simp [beq_false_of_ne he, beq_false_of_ne this]
    have hij_diff : i.val / h ≠ j.val / h → (i.val == j.val) = false := fun hne =>
      beq_false_of_ne (fun he => hne (congrArg (· / h) he))
    -- Simplify all 3 sums using hA_entry and Ainv
    have simp_sum0 : ∀ (f1 f2 : Fin h → Bool),
        (∀ t : Fin h, A i ⟨t.val, by omega⟩ = f1 t) →
        (∀ t : Fin h, Ainv ⟨t.val, by omega⟩ j = f2 t) →
        foldXor h (fun t => A i ⟨t.val, by omega⟩ && Ainv ⟨t.val, by omega⟩ j) =
        foldXor h (fun t => f1 t && f2 t) := fun f1 f2 h1 h2 =>
      foldXor_congr (fun t => by rw [h1 t, h2 t])
    have simp_sum1 : ∀ (f1 f2 : Fin h → Bool),
        (∀ t : Fin h, A i ⟨h + t.val, by omega⟩ = f1 t) →
        (∀ t : Fin h, Ainv ⟨h + t.val, by omega⟩ j = f2 t) →
        foldXor h (fun t => A i ⟨h + t.val, by omega⟩ && Ainv ⟨h + t.val, by omega⟩ j) =
        foldXor h (fun t => f1 t && f2 t) := fun f1 f2 h1 h2 =>
      foldXor_congr (fun t => by rw [h1 t, h2 t])
    have simp_sum2 : ∀ (f1 f2 : Fin h → Bool),
        (∀ t : Fin h, A i ⟨2 * h + t.val, by omega⟩ = f1 t) →
        (∀ t : Fin h, Ainv ⟨2 * h + t.val, by omega⟩ j = f2 t) →
        foldXor h (fun t => A i ⟨2 * h + t.val, by omega⟩ && Ainv ⟨2 * h + t.val, by omega⟩ j) =
        foldXor h (fun t => f1 t && f2 t) := fun f1 f2 h1 h2 =>
      foldXor_congr (fun t => by rw [h1 t, h2 t])
    have hne10 : ¬ (1 = 0) := by decide
    have hne20 : ¬ (2 = 0) := by decide
    have hne21 : ¬ (2 = 1) := by decide
    have hff : foldXor h (fun _ : Fin h => false && false) = false := foldXor_zero h
    rcases hbi with hi0 | hi1 | hi2 <;> rcases hbj with hj0 | hj1 | hj2
    · rw [simp_sum0 (fun t => HEntry d ri.val t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht0 t).1, (ht0 t).2, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht0 t).1, (ht0 t).2, ↓reduceIte, rj]),
          simp_sum1 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, rj]),
          simp_sum2 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht2 t).1, (ht2 t).2, hne20, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, rj]),
          hUU, hII, hij_same 0 hi0 hj0]
      cases (ri.val == rj.val) <;> rfl
    · rw [simp_sum0 (fun t => HEntry d ri.val t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht0 t).1, (ht0 t).2, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, rj]),
          simp_sum1 (fun t => ri.val == t.val) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht1 t).1, hne10, ↓reduceIte]),
          simp_sum2 (fun t => ri.val == t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht2 t).1, (ht2 t).2, hne20, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht2 t).1, (ht2 t).2, hne20, hne21, hne10, ↓reduceIte, rj]),
          hUI, hIU, foldXor_congr (g := fun _ => false) (fun _ => Bool.and_false _), foldXor_zero,
          hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => HEntry d ri.val t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht0 t).1, (ht0 t).2, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht0 t).1, (ht0 t).2, hne20, ↓reduceIte, rj]),
          simp_sum1 (fun t => ri.val == t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht1 t).1, (ht1 t).2, hne10, hne20, hne21, ↓reduceIte, rj]),
          simp_sum2 (fun t => ri.val == t.val) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi0, (ht2 t).1, (ht2 t).2, hne20, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht2 t).1, hne20, hne21, ↓reduceIte]),
          hUI, hIU, foldXor_congr (g := fun _ => false) (fun _ => Bool.and_false _), foldXor_zero,
          hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht0 t).1, (ht0 t).2, ↓reduceIte, rj]),
          simp_sum1 (fun t => HEntry d ri.val t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, rj]),
          simp_sum2 (fun _ => false) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht2 t).1, hne10, hne20, hne21, ↓reduceIte])
            (fun t => by simp only [Ainv, hj0, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, rj]),
          hIU, hUI, foldXor_congr (g := fun _ => false) (fun _ => Bool.false_and _), foldXor_zero,
          hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, rj]),
          simp_sum1 (fun t => HEntry d ri.val t.val) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht1 t).1, hne10, ↓reduceIte]),
          simp_sum2 (fun _ => false) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht2 t).1, hne10, hne20, hne21, ↓reduceIte])
            (fun t => by simp only [Ainv, hj1, (ht2 t).1, (ht2 t).2, hne20, hne21, hne10, ↓reduceIte, rj]),
          hII, foldXor_congr (g := fun _ => false) (fun _ => Bool.and_false _),
          foldXor_congr (g := fun _ => false) (fun _ => Bool.false_and _), foldXor_zero,
          hij_same 1 hi1 hj1]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht0 t).1, (ht0 t).2, hne20, ↓reduceIte, rj]),
          simp_sum1 (fun t => HEntry d ri.val t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht1 t).1, (ht1 t).2, hne10, hne20, hne21, ↓reduceIte, rj]),
          simp_sum2 (fun _ => false) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi1, (ht2 t).1, hne10, hne20, hne21, ↓reduceIte])
            (fun t => by simp only [Ainv, hj2, (ht2 t).1, hne20, hne21, ↓reduceIte]),
          hII, hUU, hff, hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht0 t).1, (ht0 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht0 t).1, (ht0 t).2, ↓reduceIte, rj]),
          simp_sum1 (fun _ => false) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht1 t).1, hne20, hne21, hne10, ↓reduceIte])
            (fun t => by simp only [Ainv, hj0, (ht1 t).1, (ht1 t).2, hne10, ↓reduceIte, rj]),
          simp_sum2 (fun t => HEntry d ri.val t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj0, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, rj]),
          hIU, hUI, foldXor_congr (g := fun _ => false) (fun _ => Bool.false_and _), foldXor_zero,
          hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht0 t).1, (ht0 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht0 t).1, (ht0 t).2, hne10, ↓reduceIte, rj]),
          simp_sum1 (fun _ => false) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht1 t).1, hne20, hne21, hne10, ↓reduceIte])
            (fun t => by simp only [Ainv, hj1, (ht1 t).1, hne10, ↓reduceIte]),
          simp_sum2 (fun t => HEntry d ri.val t.val) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj1, (ht2 t).1, (ht2 t).2, hne20, hne21, hne10, ↓reduceIte, rj]),
          hII, hUU, hff, hij_diff (by omega)]
      simp
    · rw [simp_sum0 (fun t => ri.val == t.val) (fun t => t.val == rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht0 t).1, (ht0 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht0 t).1, (ht0 t).2, hne20, ↓reduceIte, rj]),
          simp_sum1 (fun _ => false) (fun t => HEntry d t.val rj.val)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht1 t).1, hne20, hne21, hne10, ↓reduceIte])
            (fun t => by simp only [Ainv, hj2, (ht1 t).1, (ht1 t).2, hne10, hne20, hne21, ↓reduceIte, rj]),
          simp_sum2 (fun t => HEntry d ri.val t.val) (fun _ => false)
            (fun t => by rw [hA_entry]; simp only [hi2, (ht2 t).1, (ht2 t).2, hne20, hne21, ↓reduceIte, ri])
            (fun t => by simp only [Ainv, hj2, (ht2 t).1, hne20, hne21, ↓reduceIte]),
          hII, foldXor_congr (g := fun _ => false) (fun _ => Bool.false_and _),
          foldXor_congr (g := fun _ => false) (fun _ => Bool.and_false _), foldXor_zero,
          hij_same 2 hi2 hj2]
      simp
  -- Symmetry gives Ainv * A = I automatically!
  have hAsym : ∀ i j, A i j = A j i := fun i j => HEntry_sym d i.val j.val
  have hAinvsym : ∀ i j, Ainv i j = Ainv j i := by
    intro i j
    have hpos : 0 < h := Nat.two_pow_pos (k - 1)
    have hbi := div_lt_three hpos i.isLt
    have hbj := div_lt_three hpos j.isLt
    have hne10 : ¬ (1 = 0) := by decide
    have hne20 : ¬ (2 = 0) := by decide
    have hne21 : ¬ (2 = 1) := by decide
    simp only [Ainv]
    rcases hbi with hi | hi | hi <;> rcases hbj with hj | hj | hj <;>
      simp only [hi, hj, ↓reduceIte, hne10, hne20, hne21, HEntry_sym, nat_beq_comm]
  have hAinvA : matMul Ainv A = matId (3 * h) := by
    funext i j
    have h := congrFun (congrFun hAAinv j) i
    simp only [matMul, matId] at h ⊢
    rw [nat_beq_comm, ← h]
    apply foldXor_congr; intro t
    rw [hAinvsym i t, hAsym t j, Bool.and_comm]
  -- Now split HMat d (3 * h + s) = blockMat A B C (HMat d s) where
  -- B[i, j] = (i == h + j) ∨ (i == 2*h + j), C = B^T!
  let B : Mat (3 * h) s := fun i j => (i.val == h + j.val) || (i.val == 2 * h + j.val)
  let C : Mat s (3 * h) := fun i j => (j.val == h + i.val) || (j.val == 2 * h + i.val)
  have hblock : ∀ i j : Fin (3 * h + s),
      HMat d (3 * h + s) i j = blockMat A B C (HMat d s) i j := by
    intro i j
    simp only [blockMat, HMat, A, B, C]
    have hpos : 0 < h := Nat.two_pow_pos (k - 1)
    by_cases hi : i.val < 3 * h <;> by_cases hj : j.val < 3 * h
    · simp [hi, hj]
    · simp only [hi, hj, ↓reduceDIte]
      let j' := j.val - 3 * h
      have hj'_lt : j' < h := by omega
      have hj_eq : j.val = (j' + h) + 2 ^ k := by omega
      change HEntry d i.val j.val = ((i.val == h + j') || (i.val == 2 * h + j'))
      by_cases hi2 : i.val < 2 ^ k
      · rw [hj_eq, HEntry_sym, HEntry_msb_off d k (j' + h) i.val (by omega) hi2]
        by_cases h1 : i.val = h + j'
        · have h3 : j' + h = i.val := by omega
          simp [h1, h3]
        · have h2 : i.val ≠ 2 * h + j' := by omega
          have h3 : j' + h ≠ i.val := by omega
          rw [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]; rfl
      · let i'' := i.val - 2 ^ k
        have hi_eq : i.val = i'' + 2 ^ k := by omega
        rw [hi_eq, hj_eq, HEntry_msb_diag d k i'' (j' + h) (by omega) (by omega),
            HEntry_sym, HEntry_msb_off d (k - 1) j' i'' hj'_lt (by omega)]
        by_cases h2 : i'' = j'
        · have h1 : (i'' + 2 ^ k == 2 * h + j') = true := by
            have : i'' + 2 ^ k = 2 * h + j' := by omega
            simp [this]
          rw [h1, h2]; simp
        · have h1a : i'' + 2 ^ k ≠ h + j' := by omega
          have h1b : i'' + 2 ^ k ≠ 2 * h + j' := by omega
          have h3 : j' ≠ i'' := Ne.symm h2
          rw [beq_false_of_ne h1a, beq_false_of_ne h1b, beq_false_of_ne h3]; rfl
    · simp only [hi, hj, ↓reduceDIte]
      let i' := i.val - 3 * h
      have hi'_lt : i' < h := by omega
      have hi_eq : i.val = (i' + h) + 2 ^ k := by omega
      change HEntry d i.val j.val = ((j.val == h + i') || (j.val == 2 * h + i'))
      by_cases hj2 : j.val < 2 ^ k
      · rw [hi_eq, HEntry_msb_off d k (i' + h) j.val (by omega) hj2]
        by_cases h1 : j.val = h + i'
        · have h3 : i' + h = j.val := by omega
          simp [h1, h3]
        · have h2 : j.val ≠ 2 * h + i' := by omega
          have h3 : i' + h ≠ j.val := by omega
          rw [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3]; rfl
      · let j'' := j.val - 2 ^ k
        have hj_eq : j.val = j'' + 2 ^ k := by omega
        rw [hi_eq, hj_eq, HEntry_msb_diag d k (i' + h) j'' (by omega) (by omega),
            HEntry_msb_off d (k - 1) i' j'' hi'_lt (by omega)]
        by_cases h2 : i' = j''
        · have h1 : (j'' + 2 ^ k == 2 * h + i') = true := by
            have : j'' + 2 ^ k = 2 * h + i' := by omega
            simp [this]
          rw [h1, h2]; simp
        · have h1a : j'' + 2 ^ k ≠ h + i' := by omega
          have h1b : j'' + 2 ^ k ≠ 2 * h + i' := by omega
          rw [beq_false_of_ne h1a, beq_false_of_ne h1b, beq_false_of_ne h2]; rfl
    · simp only [hi, hj, ↓reduceDIte]
      let i' := i.val - 3 * h
      let j' := j.val - 3 * h
      have hi_eq : i.val = (i' + h) + 2 ^ k := by omega
      have hj_eq : j.val = (j' + h) + 2 ^ k := by omega
      change HEntry d i.val j.val = HEntry d i' j'
      rw [hi_eq, hj_eq, HEntry_msb_diag d k (i' + h) (j' + h) (by omega) (by omega),
          HEntry_msb_diag d (k - 1) i' j' (by omega) (by omega)]
  apply hasRank_congr hblock
  apply hasRank_schur_inv hAAinv hAinvA
  -- Verify C * Ainv * B = 0, so Schur complement is literally HMat d s!
  have hschur : ∀ i j : Fin s,
      matXor (HMat d s) (matMul C (matMul Ainv B)) i j = HMat d s i j := by
    intro i j
    simp only [matXor]
    have hzero : matMul C (matMul Ainv B) i j = false := by
      change foldXor (3 * h) (fun t => C i t && matMul Ainv B t j) = false
      rw [hfold3]
      have hpos : 0 < h := Nat.two_pow_pos (k - 1)
      have hi_lt : i.val < h := Nat.lt_of_lt_of_le i.isLt hs
      have hj_lt : j.val < h := Nat.lt_of_lt_of_le j.isLt hs
      have ht0 : foldXor h (fun t : Fin h => C i ⟨t.val, by omega⟩ && matMul Ainv B ⟨t.val, by omega⟩ j) = false := by
        rw [foldXor_congr (g := fun _ => false)]
        · exact foldXor_zero h
        · intro t
          have h1 : (t.val == h + i.val) = false := beq_false_of_ne (by omega)
          have h2 : (t.val == 2 * h + i.val) = false := beq_false_of_ne (by omega)
          simp [C, h1, h2]
      have hAB : ∀ (blk : Nat) (hblk : blk = 1 ∨ blk = 2) (t : Fin h) (hlt : blk * h + t.val < 3 * h),
          matMul Ainv B ⟨blk * h + t.val, hlt⟩ j = HEntry d t.val j.val := by
        intro blk hblk t hlt
        change foldXor (3 * h) (fun u => Ainv ⟨blk * h + t.val, hlt⟩ u && B u j) = HEntry d t.val j.val
        rw [hfold3]
        have hs0 : foldXor h (fun u : Fin h => Ainv ⟨blk * h + t.val, hlt⟩ ⟨u.val, by omega⟩ && B ⟨u.val, by omega⟩ j) = false := by
          rw [foldXor_congr (g := fun _ => false)]
          · exact foldXor_zero h
          · intro u
            have h1 : (u.val == h + j.val) = false := beq_false_of_ne (by omega)
            have h2 : (u.val == 2 * h + j.val) = false := beq_false_of_ne (by omega)
            simp [B, h1, h2]
        have hbt_div : (blk * h + t.val) / h = blk := by
          have : blk * h + t.val = t.val + h * blk := by rw [Nat.mul_comm, Nat.add_comm]
          rw [this, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt t.isLt]; omega
        have hbt_mod : (blk * h + t.val) % h = t.val := by
          have : blk * h + t.val = t.val + h * blk := by rw [Nat.mul_comm, Nat.add_comm]
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]
        have hs1 : foldXor h (fun u : Fin h => Ainv ⟨blk * h + t.val, hlt⟩ ⟨h + u.val, by omega⟩ && B ⟨h + u.val, by omega⟩ j) =
            if blk = 1 then false else HEntry d t.val j.val := by
          rw [foldXor_single ⟨j.val, hj_lt⟩]
          · have hb : B ⟨h + j.val, by omega⟩ j = true := by simp [B]
            rw [hb, Bool.and_true]
            have hd1 : (h + j.val) / h = 1 := by
              rw [Nat.add_comm, Nat.add_div_right _ hpos, Nat.div_eq_of_lt hj_lt]
            have hm1 : (h + j.val) % h = j.val := by
              rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hj_lt]
            simp only [Ainv, hbt_div, hbt_mod, hd1, hm1]
            rcases hblk with rfl | rfl <;> simp
          · intro u hu
            have h1 : (h + u.val == h + j.val) = false := beq_false_of_ne (fun he => hu (Fin.ext (by dsimp; omega)))
            have h2 : (h + u.val == 2 * h + j.val) = false := beq_false_of_ne (by omega)
            simp [B, h1, h2]
        have hs2 : foldXor h (fun u : Fin h => Ainv ⟨blk * h + t.val, hlt⟩ ⟨2 * h + u.val, by omega⟩ && B ⟨2 * h + u.val, by omega⟩ j) =
            if blk = 1 then HEntry d t.val j.val else false := by
          rw [foldXor_single ⟨j.val, hj_lt⟩]
          · have hb : B ⟨2 * h + j.val, by omega⟩ j = true := by simp [B]
            rw [hb, Bool.and_true]
            have hd2 : (2 * h + j.val) / h = 2 := by
              have : 2 * h + j.val = j.val + h * 2 := by omega
              rw [this, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj_lt]
            have hm2 : (2 * h + j.val) % h = j.val := by
              have : 2 * h + j.val = j.val + h * 2 := by omega
              rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
            simp only [Ainv, hbt_div, hbt_mod, hd2, hm2]
            rcases hblk with rfl | rfl <;> simp
          · intro u hu
            have h1 : (2 * h + u.val == h + j.val) = false := beq_false_of_ne (by omega)
            have h2 : (2 * h + u.val == 2 * h + j.val) = false := beq_false_of_ne (fun he => hu (Fin.ext (by dsimp; omega)))
            simp [B, h1, h2]
        rw [hs0, hs1, hs2]
        rcases hblk with rfl | rfl <;> simp
      have ht1 : foldXor h (fun t : Fin h => C i ⟨h + t.val, by omega⟩ && matMul Ainv B ⟨h + t.val, by omega⟩ j) =
          HEntry d i.val j.val := by
        rw [foldXor_single ⟨i.val, hi_lt⟩]
        · have hc : C i ⟨h + i.val, by omega⟩ = true := by simp [C]
          rw [hc, Bool.true_and]
          have h1 := hAB 1 (Or.inl rfl) ⟨i.val, hi_lt⟩ (by omega)
          have hfin : (⟨1 * h + i.val, by omega⟩ : Fin (3 * h)) = ⟨h + i.val, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [← hfin]; exact h1
        · intro t ht
          have h1 : (h + t.val == h + i.val) = false := beq_false_of_ne (fun he => ht (Fin.ext (by dsimp; omega)))
          have h2 : (h + t.val == 2 * h + i.val) = false := beq_false_of_ne (by omega)
          simp [C, h1, h2]
      have ht2 : foldXor h (fun t : Fin h => C i ⟨2 * h + t.val, by omega⟩ && matMul Ainv B ⟨2 * h + t.val, by omega⟩ j) =
          HEntry d i.val j.val := by
        rw [foldXor_single ⟨i.val, hi_lt⟩]
        · have hc : C i ⟨2 * h + i.val, by omega⟩ = true := by simp [C]
          rw [hc, Bool.true_and]
          exact hAB 2 (Or.inr rfl) ⟨i.val, hi_lt⟩ (by omega)
        · intro t ht
          have h1 : (2 * h + t.val == h + i.val) = false := beq_false_of_ne (by omega)
          have h2 : (2 * h + t.val == 2 * h + i.val) = false := beq_false_of_ne (fun he => ht (Fin.ext (by dsimp; omega)))
          simp [C, h1, h2]
      rw [ht0, ht1, ht2, xor_false_left, xor_self]
    rw [hzero, xor_false_right]
  exact hasRank_congr hschur hRs

/-! ### Exact 2-State MSB Corank Automaton for H(d, n) ∀ n : Nat -/

theorem bitLenAux_ge (fuel n : Nat) (h : n ≤ fuel) :
    bitLenAux fuel n = if n == 0 then 0 else 1 + bitLenAux (fuel - 1) (n / 2) := by
  cases fuel with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ f => simp [bitLenAux]

theorem bitLenAux_indep (f1 f2 n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    bitLenAux f1 n = bitLenAux f2 n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    rw [bitLenAux_ge f1 n h1, bitLenAux_ge f2 n h2]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · simp only [beq_false_of_ne hn0, Bool.false_eq_true, ↓reduceIte]
      congr 1; exact ih (n / 2) (by omega) (f1 - 1) (f2 - 1) (by omega) (by omega)

theorem bitLen_step (n : Nat) (hn : n ≥ 1) : bitLen n = 1 + bitLen (n / 2) := by
  simp only [bitLen]
  rw [bitLenAux_ge n n (Nat.le_refl n)]
  simp only [beq_false_of_ne (by omega : n ≠ 0), Bool.false_eq_true, ↓reduceIte]
  congr 1; exact bitLenAux_indep (n - 1) (n / 2) (n / 2) (by omega) (Nat.le_refl _)

theorem pow2_pred_mul_two (m : Nat) (hm : m ≥ 1) : 2 ^ m = 2 * 2 ^ (m - 1) := by
  cases m with
  | zero => omega
  | succ m' => simp [Nat.pow_succ]; omega

theorem bitLen_bounds (n : Nat) (hn : n ≥ 1) :
    2 ^ (bitLen n - 1) ≤ n ∧ n < 2 ^ (bitLen n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1; decide
    · rw [bitLen_step n hn]
      have hrec := ih (n / 2) (by omega) (by omega)
      have hbl_pos : bitLen (n / 2) ≥ 1 := by
        rw [bitLen_step (n / 2) (by omega)]; omega
      have hp1 : 2 ^ (1 + bitLen (n / 2) - 1) = 2 * 2 ^ (bitLen (n / 2) - 1) := by
        have hsub : 1 + bitLen (n / 2) - 1 = bitLen (n / 2) := by omega
        rw [hsub]
        exact pow2_pred_mul_two (bitLen (n / 2)) hbl_pos
      have hp2 : 2 ^ (1 + bitLen (n / 2)) = 2 * 2 ^ (bitLen (n / 2)) := by
        have : 1 + bitLen (n / 2) = bitLen (n / 2) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      omega

theorem bitLen_ge_two (n : Nat) (hn : n ≥ 2) : bitLen n ≥ 2 := by
  have hb := bitLen_bounds n (by omega)
  cases hbl : bitLen n with
  | zero => rw [hbl] at hb; simp at hb; omega
  | succ k =>
    cases k with
    | zero => rw [hbl] at hb; simp at hb; omega
    | succ _ => omega

theorem hcNullityAux_indep (f1 f2 : Nat) (d : Bool) (n : Nat) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    hcNullityAux f1 d n = hcNullityAux f2 d n := by
  induction n using Nat.strongRecOn generalizing f1 f2 with
  | ind n ih =>
    by_cases hn0 : n = 0
    · subst hn0; cases f1 <;> cases f2 <;> rfl
    · cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [hcNullityAux, beq_false_of_ne hn0, Bool.false_eq_true, ↓reduceIte]
          by_cases hn1 : n = 1
          · simp [hn1]
          · simp only [beq_false_of_ne hn1, Bool.false_eq_true, ↓reduceIte]
            split
            · rfl
            · split
              · rfl
              · have hb := bitLen_bounds n (by omega)
                have hpos1 : 0 < 2 ^ (bitLen n - 1) := Nat.two_pow_pos _
                have hpos2 : 0 < 2 ^ (bitLen n - 1 - 1) := Nat.two_pow_pos _
                exact ih (n - 2 ^ (bitLen n - 1) - 2 ^ (bitLen n - 1 - 1)) (by omega) f1' f2' (by omega) (by omega)

theorem hcNullity_step (d : Bool) (n : Nat) (hn : n ≥ 2) :
    hcNullity d n =
      let k := bitLen n - 1
      let r := n - 2 ^ k
      if (k % 2 == 1) != d then r
      else
        let half := 2 ^ (k - 1)
        if r ≤ half then half - r
        else hcNullity d (r - half) := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have h1 : hcNullity d n = hcNullityAux ((n - 1) + 1) d n := by
    have : (n - 1) + 1 = n := by omega
    rw [this]; rfl
  rw [h1]
  simp only [hcNullityAux, beq_false_of_ne hn0, beq_false_of_ne hn1, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · split
    · rfl
    · have hb := bitLen_bounds n (by omega)
      have hpos1 : 0 < 2 ^ (bitLen n - 1) := Nat.two_pow_pos _
      have hpos2 : 0 < 2 ^ (bitLen n - 1 - 1) := Nat.two_pow_pos _
      exact hcNullityAux_indep (n - 1) _ d _ (by omega) (Nat.le_refl _)

theorem hcNullity_le (d : Bool) (n : Nat) : hcNullity d n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; cases d <;> decide
    · by_cases h1 : n = 1
      · subst h1; cases d <;> decide
      · rw [hcNullity_step d n (by omega)]
        dsimp only
        have hb := bitLen_bounds n (by omega)
        have hbl2 := bitLen_ge_two n (by omega)
        have hpos1 : 0 < 2 ^ (bitLen n - 1) := Nat.two_pow_pos _
        have hpos2 : 0 < 2 ^ (bitLen n - 1 - 1) := Nat.two_pow_pos _
        have hhalf : 2 ^ (bitLen n - 1) = 2 * 2 ^ (bitLen n - 1 - 1) :=
          pow2_pred_mul_two (bitLen n - 1) (by omega)
        split
        · omega
        · split
          · omega
          · have := ih (n - 2 ^ (bitLen n - 1) - 2 ^ (bitLen n - 1 - 1)) (by omega)
            omega

/-- MAIN THEOREM 3B: Exact F_2-rank of the induced hypercube family H(d, n) ∀ d : Bool, ∀ n : Nat. -/
theorem H_hasRank (d : Bool) (n : Nat) : HasRank (HMat d n) (n - hcNullity d n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; cases d <;> exact hasRank_congr (fun i => Fin.elim0 i) hasRank_zero
    · by_cases h1 : n = 1
      · subst h1
        cases d
        · have hz : ∀ i j : Fin 1, HMat false 1 i j = matZero 1 1 i j := by decide
          exact hasRank_congr hz hasRank_zero
        · have hi : ∀ i j : Fin 1, HMat true 1 i j = matId 1 i j := by decide
          exact hasRank_congr hi (hasRank_id 1)
      · have hn2 : n ≥ 2 := by omega
        have hb := bitLen_bounds n (by omega)
        have hbl2 := bitLen_ge_two n hn2
        let k := bitLen n - 1
        let r := n - 2 ^ k
        have hk1 : k ≥ 1 := by dsimp [k]; omega
        have hbleq : bitLen n = k + 1 := by dsimp [k]; omega
        have hp2 : 2 ^ (bitLen n) = 2 * 2 ^ k := by
          rw [hbleq, Nat.pow_succ]; omega
        have hpow_le : 2 ^ k ≤ n := hb.1
        have hpow_gt : n < 2 * 2 ^ k := by rw [← hp2]; exact hb.2
        have hnr : n = 2 ^ k + r := by dsimp [r]; omega
        have hr_le : r ≤ 2 ^ k := by dsimp [r]; omega
        rw [hcNullity_step d n hn2]
        dsimp only
        change HasRank (HMat d n) (n - if (k % 2 == 1) != d then r
          else if r ≤ 2 ^ (k - 1) then 2 ^ (k - 1) - r else hcNullity d (r - 2 ^ (k - 1)))
        by_cases hpar : ((k % 2 == 1) != d) = true
        · simp only [hpar, ↓reduceIte]
          have hsub : n - r = 2 ^ k := by omega
          rw [hsub]
          have hR := H_msb_freeze d k r hpar hr_le
          exact hasRank_cast_rows hnr _ _ (fun _ _ => rfl)
            (hasRank_cast_cols hnr _ _ (fun _ _ => rfl) hR)
        · have hparf : ((k % 2 == 1) != d) = false := by
            cases hc : ((k % 2 == 1) != d) <;> simp_all
          simp only [hparf, Bool.false_eq_true, ↓reduceIte]
          have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := pow2_pred_mul_two k hk1
          by_cases hrh : r ≤ 2 ^ (k - 1)
          · simp only [hrh, ↓reduceIte]
            have hsub : n - (2 ^ (k - 1) - r) = 2 ^ (k - 1) + 2 * r := by omega
            rw [hsub]
            have hR := H_msb_ramp d k r hk1 hparf hrh
            exact hasRank_cast_rows hnr _ _ (fun _ _ => rfl)
              (hasRank_cast_cols hnr _ _ (fun _ _ => rfl) hR)
          · simp only [hrh, ↓reduceIte]
            let s := r - 2 ^ (k - 1)
            have hs_le : s ≤ 2 ^ (k - 1) := by dsimp [s]; omega
            have hs_lt : s < n := by dsimp [s]; omega
            have hns : n = 3 * 2 ^ (k - 1) + s := by dsimp [s]; omega
            have hRs := ih s hs_lt
            have hle_s := hcNullity_le d s
            have hsub : n - hcNullity d s = 3 * 2 ^ (k - 1) + (s - hcNullity d s) := by omega
            rw [hsub]
            have hR := H_msb_restart d k s (s - hcNullity d s) hk1 hparf hs_le hRs
            exact hasRank_cast_rows hns _ _ (fun _ _ => rfl)
              (hasRank_cast_cols hns _ _ (fun _ _ => rfl) hR)

theorem H_hasNullity (d : Bool) (n : Nat) : HasNullity (HMat d n) (hcNullity d n) :=
  ⟨hcNullity_le d n, H_hasRank d n⟩

theorem H_kerCount (d : Bool) (n : Nat) : kerCount (HMat d n) = 2 ^ (hcNullity d n) :=
  hasNullity_kerCount (H_hasNullity d n)

theorem base4RestAux_indep (f1 f2 m : Nat) (h1 : m ≤ f1) (h2 : m ≤ f2) :
    base4RestAux f1 m = base4RestAux f2 m := by
  induction m using Nat.strongRecOn generalizing f1 f2 with
  | ind m ih =>
    by_cases hm0 : m = 0
    · subst hm0; cases f1 <;> cases f2 <;> rfl
    · cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [base4RestAux, beq_false_of_ne hm0, Bool.false_eq_true, ↓reduceIte]
          congr 1
          exact ih (m / 4) (by omega) f1' f2' (by omega) (by omega)

theorem base4StartAux_indep (f1 f2 m : Nat) (h1 : m ≤ f1) (h2 : m ≤ f2) :
    base4StartAux f1 m = base4StartAux f2 m := by
  induction m using Nat.strongRecOn generalizing f1 f2 with
  | ind m ih =>
    by_cases hm0 : m = 0
    · subst hm0; cases f1 <;> cases f2 <;> rfl
    · cases f1 with
      | zero => omega
      | succ f1' =>
        cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [base4StartAux, beq_false_of_ne hm0, Bool.false_eq_true, ↓reduceIte]
          by_cases h0 : m % 4 == 0
          · simp only [h0, ↓reduceIte]
            exact ih (m / 4) (by omega) f1' f2' (by omega) (by omega)
          · simp only [h0, Bool.false_eq_true, ↓reduceIte]
            by_cases h13 : (m % 4 == 1) || (m % 4 == 3)
            · simp only [h13, ↓reduceIte]
              exact base4RestAux_indep f1' f2' (m / 4) (by omega) (by omega)
            · simp [h13]

theorem base4RestAux_pow4_three (m u f1 f2 : Nat) (hu : u < 4 ^ m)
    (hf1 : 3 * 4 ^ m + u ≤ f1) (hf2 : u ≤ f2) :
    base4RestAux f1 (3 * 4 ^ m + u) = base4RestAux f2 u := by
  induction m generalizing u f1 f2 with
  | zero =>
    simp only [Nat.pow_zero] at hu hf1 ⊢
    have hu0 : u = 0 := by omega
    subst hu0
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f1' with
      | zero => omega
      | succ f1'' =>
        cases f2 <;> simp [base4RestAux]
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f1 with
    | zero => omega
    | succ f1' =>
      have hne : 3 * 4 ^ (m + 1) + u ≠ 0 := by omega
      simp only [base4RestAux, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
      have hmod : (3 * 4 ^ (m + 1) + u) % 4 = u % 4 := by omega
      have hdiv : (3 * 4 ^ (m + 1) + u) / 4 = 3 * 4 ^ m + u / 4 := by omega
      rw [hmod, hdiv]
      by_cases hu0 : u = 0
      · subst hu0
        simp only [Nat.zero_mod, Nat.zero_div, Nat.add_zero, beq_self_eq_true, Bool.true_or, Bool.true_and]
        have h0 := ih 0 f1' f2 hpos (by omega) (Nat.zero_le _)
        simpa using h0
      · cases f2 with
        | zero => omega
        | succ f2' =>
          simp only [base4RestAux, beq_false_of_ne hu0, Bool.false_eq_true, ↓reduceIte]
          congr 1
          exact ih (u / 4) f1' f2' (by omega) (by omega) (by omega)

theorem base4StartAux_pow4_one (m f : Nat) (hf : 4 ^ m ≤ f) :
    base4StartAux f (4 ^ m) = true := by
  induction m generalizing f with
  | zero =>
    simp only [Nat.pow_zero] at hf ⊢
    cases f with
    | zero => omega
    | succ f' => cases f' <;> simp [base4StartAux, base4RestAux]
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f with
    | zero => omega
    | succ f' =>
      have hne : 4 ^ (m + 1) ≠ 0 := by omega
      have hm0 : 4 ^ (m + 1) % 4 = 0 := by omega
      have hd : 4 ^ (m + 1) / 4 = 4 ^ m := by omega
      simp only [base4StartAux, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte, hm0, beq_self_eq_true, hd]
      exact ih f' (by omega)

theorem base4StartAux_pow4_three_zero (m f : Nat) (hf : 3 * 4 ^ m ≤ f) :
    base4StartAux f (3 * 4 ^ m) = true := by
  induction m generalizing f with
  | zero =>
    simp only [Nat.pow_zero] at hf ⊢
    cases f with
    | zero => omega
    | succ f' => cases f' <;> simp [base4StartAux, base4RestAux]
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f with
    | zero => omega
    | succ f' =>
      have hne : 3 * 4 ^ (m + 1) ≠ 0 := by omega
      have hm0 : (3 * 4 ^ (m + 1)) % 4 = 0 := by omega
      have hd : (3 * 4 ^ (m + 1)) / 4 = 3 * 4 ^ m := by omega
      simp only [base4StartAux, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte, hm0, beq_self_eq_true, hd]
      exact ih f' (by omega)

theorem base4StartAux_pow4_three_add (m t f1 f2 : Nat) (ht1 : 1 ≤ t) (ht2 : t < 4 ^ m)
    (hf1 : 3 * 4 ^ m + t ≤ f1) (hf2 : t ≤ f2) :
    base4StartAux f1 (3 * 4 ^ m + t) = base4StartAux f2 t := by
  induction m generalizing t f1 f2 with
  | zero => simp at ht2; omega
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f1 with
    | zero => omega
    | succ f1' =>
      cases f2 with
      | zero => omega
      | succ f2' =>
        have hne1 : 3 * 4 ^ (m + 1) + t ≠ 0 := by omega
        have hne2 : t ≠ 0 := by omega
        have hmod : (3 * 4 ^ (m + 1) + t) % 4 = t % 4 := by omega
        have hdiv : (3 * 4 ^ (m + 1) + t) / 4 = 3 * 4 ^ m + t / 4 := by omega
        simp only [base4StartAux, beq_false_of_ne hne1, beq_false_of_ne hne2,
          Bool.false_eq_true, ↓reduceIte, hmod, hdiv]
        by_cases h0 : t % 4 == 0
        · simp only [h0, ↓reduceIte]
          have ht4 : t % 4 = 0 := by simpa using h0
          exact ih (t / 4) f1' f2' (by omega) (by omega) (by omega) (by omega)
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          by_cases h13 : (t % 4 == 1) || (t % 4 == 3)
          · simp only [h13, ↓reduceIte]
            exact base4RestAux_pow4_three m (t / 4) f1' f2' (by omega) (by omega) (by omega)
          · simp [h13]

theorem base4StartAux_lt_false_of_two_mul_pow4 (m t f : Nat) (ht : t < 4 ^ m)
    (hf : 4 ^ m + t ≤ f) (ht1 : 1 ≤ t) :
    base4StartAux f (4 ^ m + t) = false := by
  induction m generalizing t f with
  | zero => simp at ht; omega
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f with
    | zero => omega
    | succ f' =>
      have hne : 4 ^ (m + 1) + t ≠ 0 := by omega
      have hmod : (4 ^ (m + 1) + t) % 4 = t % 4 := by omega
      have hdiv : (4 ^ (m + 1) + t) / 4 = 4 ^ m + t / 4 := by omega
      simp only [base4StartAux, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte, hmod, hdiv]
      by_cases h0 : t % 4 == 0
      · simp only [h0, ↓reduceIte]
        have ht4 : t % 4 = 0 := by simpa using h0
        exact ih (t / 4) f' (by omega) (by omega) (by omega)
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        by_cases h13 : (t % 4 == 1) || (t % 4 == 3)
        · simp only [h13, ↓reduceIte]
          -- base4RestAux f' (4^m + t/4) = false because the top digit is 1!
          clear h0 h13 hmod hdiv hne ht1 ih
          generalize hu : t / 4 = u
          have hu_lt : u < 4 ^ m := by omega
          have hf' : 4 ^ m + u ≤ f' := by omega
          clear hu ht hf h4 hpos t
          induction m generalizing u f' with
          | zero =>
            simp only [Nat.pow_zero] at hu_lt hf' ⊢
            have hu0 : u = 0 := by omega
            subst hu0
            cases f' with
            | zero => omega
            | succ f'' => simp [base4RestAux]
          | succ m ihm =>
            have h4m : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
            have hpm : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
            cases f' with
            | zero => omega
            | succ f'' =>
              have hne' : 4 ^ (m + 1) + u ≠ 0 := by omega
              have hdiv' : (4 ^ (m + 1) + u) / 4 = 4 ^ m + u / 4 := by omega
              simp only [base4RestAux, beq_false_of_ne hne', Bool.false_eq_true, ↓reduceIte, hdiv']
              rw [ihm f'' (u / 4) (by omega) (by omega), Bool.and_false]
        · simp [h13]

theorem base4StartAux_two_mul_pow4_false (m t f : Nat) (ht : t < 4 ^ m)
    (hf : 2 * 4 ^ m + t ≤ f) :
    base4StartAux f (2 * 4 ^ m + t) = false := by
  induction m generalizing t f with
  | zero =>
    simp only [Nat.pow_zero] at ht hf ⊢
    have ht0 : t = 0 := by omega
    subst ht0
    cases f with
    | zero => omega
    | succ f' => simp [base4StartAux]
  | succ m ih =>
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
    cases f with
    | zero => omega
    | succ f' =>
      have hne : 2 * 4 ^ (m + 1) + t ≠ 0 := by omega
      have hmod : (2 * 4 ^ (m + 1) + t) % 4 = t % 4 := by omega
      have hdiv : (2 * 4 ^ (m + 1) + t) / 4 = 2 * 4 ^ m + t / 4 := by omega
      simp only [base4StartAux, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte, hmod, hdiv]
      by_cases h0 : t % 4 == 0
      · simp only [h0, ↓reduceIte]
        exact ih (t / 4) f' (by omega) (by omega)
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        by_cases h13 : (t % 4 == 1) || (t % 4 == 3)
        · simp only [h13, ↓reduceIte]
          clear h0 h13 hmod hdiv hne ih
          generalize hu : t / 4 = u
          have hu_lt : u < 4 ^ m := by omega
          have hf' : 2 * 4 ^ m + u ≤ f' := by omega
          clear hu ht hf h4 hpos t
          induction m generalizing u f' with
          | zero =>
            simp only [Nat.pow_zero] at hu_lt hf' ⊢
            have hu0 : u = 0 := by omega
            subst hu0
            cases f' with
            | zero => omega
            | succ f'' => simp [base4RestAux]
          | succ m ihm =>
            have h4m : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
            have hpm : 0 < 4 ^ m := Nat.pow_pos (by decide : 0 < 4)
            cases f' with
            | zero => omega
            | succ f'' =>
              have hne' : 2 * 4 ^ (m + 1) + u ≠ 0 := by omega
              have hdiv' : (2 * 4 ^ (m + 1) + u) / 4 = 2 * 4 ^ m + u / 4 := by omega
              simp only [base4RestAux, beq_false_of_ne hne', Bool.false_eq_true, ↓reduceIte, hdiv']
              rw [ihm f'' (u / 4) (by omega) (by omega), Bool.and_false]
        · simp [h13]

theorem pow2_two_mul (m : Nat) : 2 ^ (2 * m) = 4 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m) + 2 := by omega
    rw [h1, Nat.pow_succ, Nat.pow_succ, ih, Nat.pow_succ]; omega

theorem hcNullity_false_eq_zero_iff_base4 (n : Nat) :
    hcNullity false n = 0 ↔ hc0Base4Accept n = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; decide
    · by_cases h1 : n = 1
      · subst h1; decide
      · have hn2 : n ≥ 2 := by omega
        have hb := bitLen_bounds n (by omega)
        have hbl2 := bitLen_ge_two n hn2
        let k := bitLen n - 1
        let r := n - 2 ^ k
        have hk1 : k ≥ 1 := by dsimp [k]; omega
        have hbleq : bitLen n = k + 1 := by dsimp [k]; omega
        have hp2 : 2 ^ (bitLen n) = 2 * 2 ^ k := by rw [hbleq, Nat.pow_succ]; omega
        have hpow_le : 2 ^ k ≤ n := hb.1
        have hpow_gt : n < 2 * 2 ^ k := by rw [← hp2]; exact hb.2
        have hnr : n = 2 ^ k + r := by dsimp [r]; omega
        have hr_lt : r < 2 ^ k := by dsimp [r]; omega
        rw [hcNullity_step false n hn2]
        dsimp only
        change (if (k % 2 == 1) != false then r
          else if r ≤ 2 ^ (k - 1) then 2 ^ (k - 1) - r else hcNullity false (r - 2 ^ (k - 1))) = 0 ↔ _
        by_cases hkodd : k % 2 = 1
        · have hpar : ((k % 2 == 1) != false) = true := by simp [hkodd]
          simp only [hpar, ↓reduceIte]
          let m := k / 2
          have hk_eq : k = 2 * m + 1 := by omega
          have h2k : 2 ^ k = 2 * 4 ^ m := by
            rw [hk_eq, Nat.pow_succ, pow2_two_mul]; omega
          by_cases hr0 : r = 0
          · have hn_eq : n = 2 * 4 ^ m := by omega
            have hne0 : n ≠ 0 := h0
            have hev : n % 2 = 0 := by omega
            have hdiv : n / 2 = 4 ^ m := by omega
            simp only [hr0, true_iff, hc0Base4Accept, beq_false_of_ne hne0, Bool.false_eq_true, ↓reduceIte,
              hev, show (0 == 1) = false by rfl, hdiv]
            exact base4StartAux_pow4_one m n (by omega)
          · constructor
            · intro h; exact absurd h hr0
            · intro hacc
              exfalso
              simp only [hc0Base4Accept, beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte] at hacc
              by_cases hodd : n % 2 = 1
              · simp [hodd] at hacc
              · have hev : n % 2 = 0 := by omega
                simp only [hev, show (0 == 1) = false by rfl, Bool.false_eq_true, ↓reduceIte] at hacc
                have hdiv : n / 2 = 4 ^ m + r / 2 := by omega
                rw [hdiv] at hacc
                have hfalse := base4StartAux_lt_false_of_two_mul_pow4 m (r / 2) n (by omega) (by omega) (by omega)
                rw [hfalse] at hacc; cases hacc
        · have hkeven : k % 2 = 0 := by omega
          have hpar : ((k % 2 == 1) != false) = false := by simp [hkeven]
          simp only [hpar, Bool.false_eq_true, ↓reduceIte]
          let m := k / 2 - 1
          have hk_eq : k - 1 = 2 * m + 1 := by omega
          have hhalf : 2 ^ (k - 1) = 2 * 4 ^ m := by
            rw [hk_eq, Nat.pow_succ, pow2_two_mul]; omega
          have h2k : 2 ^ k = 4 * 4 ^ m := by
            have := pow2_pred_mul_two k hk1; omega
          by_cases hrh : r ≤ 2 ^ (k - 1)
          · simp only [hrh, ↓reduceIte]
            by_cases hreq : r = 2 ^ (k - 1)
            · have hn_eq : n = 6 * 4 ^ m := by omega
              have hev : n % 2 = 0 := by omega
              have hdiv : n / 2 = 3 * 4 ^ m := by omega
              simp only [hreq, Nat.sub_self, true_iff, hc0Base4Accept, beq_false_of_ne h0,
                Bool.false_eq_true, ↓reduceIte, hev, show (0 == 1) = false by rfl, hdiv]
              exact base4StartAux_pow4_three_zero m n (by omega)
            · have hpos_sub : 2 ^ (k - 1) - r ≠ 0 := by omega
              constructor
              · intro h; exact absurd h hpos_sub
              · intro hacc
                exfalso
                simp only [hc0Base4Accept, beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte] at hacc
                by_cases hodd : n % 2 = 1
                · simp [hodd] at hacc
                · have hev : n % 2 = 0 := by omega
                  simp only [hev, show (0 == 1) = false by rfl, Bool.false_eq_true, ↓reduceIte] at hacc
                  have hdiv : n / 2 = 2 * 4 ^ m + r / 2 := by omega
                  rw [hdiv] at hacc
                  have hfalse := base4StartAux_two_mul_pow4_false m (r / 2) n (by omega) (by omega)
                  rw [hfalse] at hacc; cases hacc
          · simp only [hrh, ↓reduceIte]
            let s := r - 2 ^ (k - 1)
            have hs_pos : 1 ≤ s := by dsimp [s]; omega
            have hs_lt : s < 2 * 4 ^ m := by dsimp [s]; omega
            have hns : n = 6 * 4 ^ m + s := by dsimp [s]; omega
            rw [ih s (by omega)]
            simp only [hc0Base4Accept, beq_false_of_ne h0, beq_false_of_ne (by omega : s ≠ 0),
              Bool.false_eq_true, ↓reduceIte]
            by_cases hsodd : s % 2 = 1
            · have hnodd : n % 2 = 1 := by omega
              simp [hsodd, hnodd]
            · have hsev : s % 2 = 0 := by omega
              have hnev : n % 2 = 0 := by omega
              have hsdiv_pos : 1 ≤ s / 2 := by omega
              have hndiv : n / 2 = 3 * 4 ^ m + s / 2 := by omega
              simp only [hsev, hnev, show (0 == 1) = false by rfl, Bool.false_eq_true, ↓reduceIte, hndiv]
              rw [base4StartAux_pow4_three_add m (s / 2) n s hsdiv_pos (by omega) (by omega) (by omega)]

/-- MAIN THEOREM 3C (Exact Base-4 Regular Language of Invertible Induced Hypercubes):
    For EVERY n : Nat, H(0, n) is invertible over F_2 iff n is accepted by the 2-state Base-4 DFA! -/
theorem H0_invertible_iff_base4 (n : Nat) :
    HasRank (HMat false n) n ↔ hc0Base4Accept n = true := by
  have hnu := H_hasNullity false n
  rw [← hcNullity_false_eq_zero_iff_base4 n]
  constructor
  · intro hr
    have heq := hasRank_unique hr hnu.2
    have hle := hnu.1
    omega
  · intro hz
    have hr := hnu.2
    rw [hz, Nat.sub_zero] at hr
    exact hr

/-! ## Section 7: Non-Vacuity Witnesses, Sharpness Counterexamples, and Axiom Audits -/

-- Non-vacuity witnesses for Theorem 1 (M0 Gray-code bit-transition nullity)

example : HasNullity (M0Mat 6) 2 := M0_gray_nullity 6 (by decide)

example : HasRank (M0Mat 8) 8 := (M0_invertible_iff_pow2 8 (by decide)).mpr ⟨3, by decide, by decide⟩

example : HasNullity (M0Mat 11) 3 := M0_gray_nullity 11 (by decide)

example : HasNullity (M0Mat 22) 4 := M0_gray_nullity 22 (by decide)

example : kerCount (M0Mat 6) = 4 := M0_kerCount 6 (by decide)

example : kerCount (M0Mat 8) = 1 := by
  have h := M0_kerCount 8 (by decide); simpa [gray, popcount, popcountAux] using h

-- Non-vacuity witnesses for Theorem 2 (Dbar full rank & D parity nullity)

example : HasRank (DbarMat 13) 13 := Dbar_hasRank_full 13

example : HasNullity (DMat 13) 1 := D_hasNullity 13

example : HasNullity (DMat 14) 0 := D_hasNullity 14

-- Non-vacuity witnesses for Theorem 3 (Induced Hypercube MSB Automaton)

example : HasNullity (HMat false 12) 4 := by
  have h := H_hasNullity false 12; simpa [hcNullity, hcNullityAux, bitLen, bitLenAux] using h

example : HasNullity (HMat false 19) 5 := by
  have h := H_hasNullity false 19; simpa [hcNullity, hcNullityAux, bitLen, bitLenAux] using h

example : HasRank (HMat false 26) 26 := by
  have h := H_hasRank false 26; simpa [hcNullity, hcNullityAux, bitLen, bitLenAux] using h

example : HasNullity (HMat true 12) 0 := by
  have h := H_hasNullity true 12; simpa [hcNullity, hcNullityAux, bitLen, bitLenAux] using h

example : hc0Base4Accept 26 = true ∧ hc0Base4Accept 24 = true ∧ hc0Base4Accept 12 = false := by decide

-- Sharpness Counterexample 1: Carry-in c = 1 (M1Mat) breaks Theorem 1 at n = 2 and n = 4!

theorem sharp_carry_in_one_breaks_thm1 :
    kerCount (M1Mat 2) = 4 ∧ kerCount (M0Mat 2) = 1 ∧
    kerCount (M1Mat 4) = 4 ∧ kerCount (M0Mat 4) = 1 := by decide

-- Sharpness Counterexample 2: Bitwise OR instead of AND breaks Theorem 1 at n = 4!

theorem sharp_bitwise_or_breaks_thm1 :
    kerCount (MOrMat 4) = 4 ∧ kerCount (M0Mat 4) = 1 := by decide

-- Sharpness Counterexample 3: n >= 2 bound in Theorem 1 is sharp (at n = 1, nullity = 1 while popcount(gray(0)) = 0)

theorem sharp_boundary_n1 :
    kerCount (M0Mat 1) = 2 ∧ popcount (gray 0) = 0 := by decide

-- Sharpness Counterexample 4: Hamming distance 2 breaks the hypercube MSB involutive automaton at n = 4!

theorem sharp_hamming_dist2_breaks_thm3 :
    kerCount (H2Mat 4) = 1 ∧ kerCount (HMat false 4) = 4 := by decide

end F2RankAutomaton
