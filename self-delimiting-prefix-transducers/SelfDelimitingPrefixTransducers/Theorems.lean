/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SelfDelimitingPrefixTransducers.Defs

/-!
# Theorems (`self-delimiting-prefix-transducers`)

Full proofs of the headline infinite theorems of Self-Delimiting Binary Prefix-Code Kirchhoff-Bellman Transducer Engine.
-/

namespace PrefixCodeEngine

theorem negOnePow_zero : negOnePow 0 = 1 := rfl

theorem negOnePow_succ (n : Nat) : negOnePow (n + 1) = -negOnePow n := rfl

theorem negOnePow_add (m n : Nat) : negOnePow (m + n) = negOnePow m * negOnePow n := by
  induction n with
  | zero => simp [negOnePow]
  | succ n ih =>
    rw [Nat.add_succ, negOnePow_succ, negOnePow_succ, ih]
    grind

theorem negOnePow_mul_self (n : Nat) : negOnePow n * negOnePow n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [negOnePow_succ]
    grind

theorem negOnePow_natAbs (n : Nat) : (negOnePow n).natAbs = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [negOnePow, ih]

theorem jacobsthal_step (n : Nat) : jacobsthal (n + 1) = 2 * jacobsthal n + negOnePow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change jacobsthal (n + 1) + 2 * jacobsthal n = 2 * jacobsthal (n + 1) + negOnePow (n + 1)
    rw [negOnePow_succ]
    omega

theorem jacobsthal_three_mul (n : Nat) : 3 * jacobsthal n = (2 : Int) ^ n - negOnePow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [jacobsthal_step, Int.pow_succ, negOnePow_succ]
    omega

theorem int_two_pow_pos (n : Nat) : (1 : Int) ≤ (2 : Int) ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ]; omega

theorem jacobsthal_pos (n : Nat) (hn : 1 ≤ n) : 0 < jacobsthal n := by
  cases n with
  | zero => omega
  | succ m =>
    have h3 := jacobsthal_three_mul (m + 1)
    have hpow : (2 : Int) ^ (m + 1) ≥ 2 := by
      rw [Int.pow_succ]
      have := int_two_pow_pos m
      omega
    have hneg : negOnePow (m + 1) ≤ 1 := by
      have habs := negOnePow_natAbs (m + 1)
      omega
    omega

theorem popcount_append (u v : List Bool) : popcount (u ++ v) = popcount u + popcount v := by
  induction u with
  | nil => simp [popcount]
  | cons b u ih =>
    cases b <;> simp [popcount, ih, Nat.add_assoc]

theorem lexDiverge_imp_lexLt {u v : List Bool} (h : lexDiverge u v) : lexLt u v := by
  induction h with
  | head u v => exact lexLt.false_true u v
  | cons b _ ih => exact lexLt.cons_same b ih

theorem lexDiverge_append_right {u v : List Bool} (s t : List Bool) (h : lexDiverge u v) :
    lexDiverge (u ++ s) (v ++ t) := by
  induction h with
  | head u v => exact lexDiverge.head (u ++ s) (v ++ t)
  | cons b _ ih => exact lexDiverge.cons b ih

theorem lexDiverge_append_left (p : List Bool) {u v : List Bool} (h : lexDiverge u v) :
    lexDiverge (p ++ u) (p ++ v) := by
  induction p with
  | nil => exact h
  | cons b p ih => exact lexDiverge.cons b ih

theorem lexLt_append_left (p : List Bool) {u v : List Bool} (h : lexLt u v) :
    lexLt (p ++ u) (p ++ v) := by
  induction p with
  | nil => exact h
  | cons b p ih => exact lexLt.cons_same b ih

theorem lexLt_irrefl (u : List Bool) : ¬ lexLt u u := by
  induction u with
  | nil => intro h; cases h
  | cons b u ih =>
    intro h
    cases h with
    | cons_same _ h' => exact ih h'

theorem lexLt_asymm {u v : List Bool} (h1 : lexLt u v) (h2 : lexLt v u) : False := by
  induction h1 with
  | nil_cons b bs => cases h2
  | false_true u v => cases h2
  | cons_same b _ ih =>
    cases h2 with
    | cons_same _ h2' => exact ih h2'

theorem allBits_length (N : Nat) : (allBits N).length = 2 ^ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp [allBits, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem mem_allBits_iff (N : Nat) (u : List Bool) : u ∈ allBits N ↔ u.length = N := by
  induction N generalizing u with
  | zero => simp [allBits]
  | succ N ih =>
    cases u with
    | nil => simp [allBits]
    | cons b u => cases b <;> simp [allBits, ih]

theorem listSumInt_append {α : Type} (f : α → Int) (xs ys : List α) :
    listSumInt f (xs ++ ys) = listSumInt f xs + listSumInt f ys := by
  induction xs with
  | nil => simp [listSumInt]
  | cons x xs ih => simp [listSumInt, ih]; omega

theorem listSumInt_map {α β : Type} (f : β → Int) (g : α → β) (xs : List α) :
    listSumInt f (xs.map g) = listSumInt (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listSumInt, ih]

theorem listSumInt_const {α : Type} (c : Int) (xs : List α) :
    listSumInt (fun _ => c) xs = (xs.length : Int) * c := by
  induction xs with
  | nil => simp [listSumInt]
  | cons x xs ih => simp [listSumInt, ih, Int.add_mul]; omega

theorem listSumInt_mul_left {α : Type} (c : Int) (f : α → Int) (xs : List α) :
    listSumInt (fun x => c * f x) xs = c * listSumInt f xs := by
  induction xs with
  | nil => simp [listSumInt]
  | cons x xs ih => simp [listSumInt, ih, Int.mul_add]

theorem listSumInt_add {α : Type} (f g : α → Int) (xs : List α) :
    listSumInt (fun x => f x + g x) xs = listSumInt f xs + listSumInt g xs := by
  induction xs with
  | nil => simp [listSumInt]
  | cons x xs ih => simp [listSumInt, ih]; omega


/-! ==========================================================================
    SECTION 2: MECHANISM I — Weighted Finite-State Prefix-Code Transducer Engine
    ========================================================================== -/

/-- Theorem M1.1 (Self-Delimiting Prefix Framing). -/
theorem decodeOne_append {S : Nat} (A : PrefixAut S) {q : Fin S} {w : List Bool}
    (hw : Accepts A q w) (rest : List Bool) :
    decodeOne A q (w ++ rest) = some (w, rest) := by
  induction hw with
  | emit h => simp [decodeOne, h]
  | cont h _ ih => simp [decodeOne, h, ih]

/-- Theorem M1.2 (Prefix-Freeness). -/
theorem accepts_prefix_free {S : Nat} (A : PrefixAut S) {q : Fin S} {u v : List Bool}
    (hu : Accepts A q u) (huv : Accepts A q (u ++ v)) : v = [] := by
  have h1 := decodeOne_append A hu v
  have h2 := decodeOne_append A huv []
  simp at h2
  rw [h1] at h2
  injection h2 with hpair
  exact congrArg Prod.snd hpair

theorem accepts_nonempty {S : Nat} (A : PrefixAut S) {q : Fin S} {w : List Bool}
    (hw : Accepts A q w) : w ≠ [] := by
  cases hw <;> simp

/-- Theorem M1.3 (Infinite-Length Stream Unique Decodability). -/
theorem decodeStream_flatten {S : Nat} (A : PrefixAut S) (ws : List (List Bool))
    (hws : ∀ w ∈ ws, Accepts A A.init w) :
    decodeStream A ws.flatten = some ws := by
  induction ws with
  | nil => simp [decodeStream]
  | cons w ws ih =>
    have hw : Accepts A A.init w := hws w (by simp)
    have hrest : ∀ u ∈ ws, Accepts A A.init u := fun u hu => hws u (by simp [hu])
    have hne : w ≠ [] := accepts_nonempty A hw
    cases w with
    | nil => exact absurd rfl hne
    | cons b bs =>
      have hdec : decodeOne A A.init (b :: (bs ++ ws.flatten)) = some (b :: bs, ws.flatten) :=
        decodeOne_append A hw ws.flatten
      simp only [List.flatten_cons, List.cons_append]
      unfold decodeStream
      split
      · rename_i hnone
        rw [hdec] at hnone; cases hnone
      · rename_i w' rem hsome
        rw [hdec] at hsome
        injection hsome with hpair
        have hw' : w' = b :: bs := (congrArg Prod.fst hpair).symm
        have hrem : rem = ws.flatten := (congrArg Prod.snd hpair).symm
        subst hw'; subst hrem
        rw [ih hrest]

/-- Theorem M1.4 (Injectivity of Arbitrary-Length Stream Encoding). -/
theorem flatten_injective {S : Nat} (A : PrefixAut S) {ws1 ws2 : List (List Bool)}
    (h1 : ∀ w ∈ ws1, Accepts A A.init w) (h2 : ∀ w ∈ ws2, Accepts A A.init w)
    (heq : ws1.flatten = ws2.flatten) : ws1 = ws2 := by
  have d1 := decodeStream_flatten A ws1 h1
  have d2 := decodeStream_flatten A ws2 h2
  rw [heq] at d1
  rw [d1] at d2
  injection d2

/-! ### Exact Finite-Horizon Character & Cost Potential Operators -/

theorem evalRunChar_scale {S : Nat} (A : PrefixAut S) (mu : Fin S → Bool → Int) (q : Fin S)
    (c pm : Int) (u : List Bool) :
    evalRunChar A mu q (c * pm) u = c * evalRunChar A mu q pm u := by
  induction u generalizing q pm with
  | nil => simp [evalRunChar]
  | cons b bs ih =>
    simp only [evalRunChar]
    cases A.step q b with
    | emit => grind
    | dead => simp
    | cont q' =>
      rw [Int.mul_assoc]
      exact ih q' (pm * mu q b)

theorem evalRunCost_decomp {S : Nat} (A : PrefixAut S) (mu cost : Fin S → Bool → Int) (q : Fin S)
    (pm sc : Int) (u : List Bool) :
    evalRunCost A mu cost q pm sc u =
      pm * (sc * evalRunChar A mu q 1 u + evalRunCost A mu cost q 1 0 u) := by
  induction u generalizing q pm sc with
  | nil => simp [evalRunCost, evalRunChar]
  | cons b bs ih =>
    simp only [evalRunCost, evalRunChar]
    cases A.step q b with
    | emit => dsimp only; grind
    | dead => dsimp only; simp
    | cont q' =>
      dsimp only
      rw [ih q' (pm * mu q b) (sc + cost q b)]
      rw [ih q' (1 * mu q b) (0 + cost q b)]
      have hsc : evalRunChar A mu q' (1 * mu q b) bs = mu q b * evalRunChar A mu q' 1 bs := by
        have h1 : (1 : Int) * mu q b = mu q b * 1 := Int.mul_comm 1 (mu q b)
        rw [h1]
        exact evalRunChar_scale A mu q' (mu q b) 1 bs
      rw [hsc]
      grind

/-- Semantic Bridge Theorem (Layer 0): For `B = 2`, `charSum A 2 mu N q` is IDENTICALLY equal
    to summing `evalRunChar` over all `2^N` bitstrings `u ∈ allBits N`. -/
theorem charSum_eq_evalAllBits {S : Nat} (A : PrefixAut S) (mu : Fin S → Bool → Int)
    (N : Nat) (q : Fin S) :
    charSum A 2 mu N q = listSumInt (evalRunChar A mu q 1) (allBits N) := by
  induction N generalizing q with
  | zero => simp [charSum, allBits, listSumInt, evalRunChar]
  | succ N ih =>
    simp only [charSum, allBits, listSumInt_append, listSumInt_map]
    congr 1
    · cases h0 : A.step q false with
      | dead => simp [evalRunChar, h0, listSumInt_const]
      | emit =>
        simp only [evalRunChar, h0, Int.one_mul, listSumInt_const, allBits_length]
        have hcast : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by simp
        rw [hcast, Int.mul_comm]
      | cont q' =>
        simp only [evalRunChar, h0, Int.one_mul]
        have hsc : (fun x => evalRunChar A mu q' (mu q false) x) =
            (fun x => mu q false * evalRunChar A mu q' 1 x) := by
          funext x
          have := evalRunChar_scale A mu q' (mu q false) 1 x
          simpa using this
        rw [hsc, listSumInt_mul_left, ← ih q']
    · cases h1 : A.step q true with
      | dead => simp [evalRunChar, h1, listSumInt_const]
      | emit =>
        simp only [evalRunChar, h1, Int.one_mul, listSumInt_const, allBits_length]
        have hcast : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by simp
        rw [hcast, Int.mul_comm]
      | cont q' =>
        simp only [evalRunChar, h1, Int.one_mul]
        have hsc : (fun x => evalRunChar A mu q' (mu q true) x) =
            (fun x => mu q true * evalRunChar A mu q' 1 x) := by
          funext x
          have := evalRunChar_scale A mu q' (mu q true) 1 x
          simpa using this
        rw [hsc, listSumInt_mul_left, ← ih q']

/-- Semantic Bridge Theorem (Layer 1): For `B = 2`, `costSum A 2 mu cost N q` is IDENTICALLY equal
    to summing `evalRunCost` over all `2^N` bitstrings `u ∈ allBits N`. -/
theorem costSum_eq_evalAllBits {S : Nat} (A : PrefixAut S) (mu cost : Fin S → Bool → Int)
    (N : Nat) (q : Fin S) :
    costSum A 2 mu cost N q = listSumInt (evalRunCost A mu cost q 1 0) (allBits N) := by
  induction N generalizing q with
  | zero => simp [costSum, allBits, listSumInt, evalRunCost]
  | succ N ih =>
    simp only [costSum, allBits, listSumInt_append, listSumInt_map]
    congr 1
    · cases h0 : A.step q false with
      | dead => simp [evalRunCost, h0, listSumInt_const]
      | emit =>
        simp only [evalRunCost, h0, Int.one_mul, Int.zero_add, listSumInt_const, allBits_length]
        have hcast : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by simp
        rw [hcast]; grind
      | cont q' =>
        simp only [evalRunCost, h0, Int.one_mul, Int.zero_add]
        have hd : (fun x => evalRunCost A mu cost q' (mu q false) (cost q false) x) =
            (fun x => mu q false * (cost q false * evalRunChar A mu q' 1 x +
              evalRunCost A mu cost q' 1 0 x)) := by
          funext x
          exact evalRunCost_decomp A mu cost q' (mu q false) (cost q false) x
        rw [hd, listSumInt_mul_left, listSumInt_add, listSumInt_mul_left,
            ← charSum_eq_evalAllBits, ← ih q']
    · cases h1 : A.step q true with
      | dead => simp [evalRunCost, h1, listSumInt_const]
      | emit =>
        simp only [evalRunCost, h1, Int.one_mul, Int.zero_add, listSumInt_const, allBits_length]
        have hcast : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by simp
        rw [hcast]; grind
      | cont q' =>
        simp only [evalRunCost, h1, Int.one_mul, Int.zero_add]
        have hd : (fun x => evalRunCost A mu cost q' (mu q true) (cost q true) x) =
            (fun x => mu q true * (cost q true * evalRunChar A mu q' 1 x +
              evalRunCost A mu cost q' 1 0 x)) := by
          funext x
          exact evalRunCost_decomp A mu cost q' (mu q true) (cost q true) x
        rw [hd, listSumInt_mul_left, listSumInt_add, listSumInt_mul_left,
            ← charSum_eq_evalAllBits, ← ih q']

/-! ### Core Finite-to-Infinite Potential Conservation Theorems (Layers 0 & 1) -/

/-- Theorem M1.5 (Layer-0 Finite-to-Infinite Character / Kraft Conservation). -/
theorem layer0_conservation {S : Nat} (A : PrefixAut S) (B : Int) (mu : Fin S → Bool → Int)
    (D : Int) (kappa : Fin S → Int) (hK : IsKirchhoff0 A B mu D kappa) :
    ∀ (N : Nat) (q : Fin S),
      D * charSum A B mu N q + activePot A mu kappa N q = B ^ N * kappa q := by
  intro N
  induction N with
  | zero => intro q; simp [charSum, activePot]
  | succ N ih =>
    intro q
    simp only [charSum, activePot]
    have branch_eq : ∀ b : Bool,
        D * (match A.step q b with
             | Step.dead => 0
             | Step.emit => mu q b * B ^ N
             | Step.cont q' => mu q b * charSum A B mu N q') +
        (match A.step q b with
         | Step.dead => 0
         | Step.emit => 0
         | Step.cont q' => mu q b * activePot A mu kappa N q') =
        B ^ N * (mu q b * stepVal kappa D (A.step q b)) := by
      intro b
      cases A.step q b with
      | dead => simp [stepVal]
      | emit => simp only [stepVal]; grind
      | cont q' =>
        simp only [stepVal]
        have := ih q'
        grind
    have h0 := branch_eq false
    have h1 := branch_eq true
    have hKq := hK q
    have hcomb : ∀ a b c d : Int, (a + b) + (c + d) = (a + c) + (b + d) := fun _ _ _ _ => by omega
    have hadd : ∀ a b c d : Int, a = b → c = d → a + c = b + d := by intro _ _ _ _ ha hb; rw [ha, hb]
    rw [Int.mul_add, hcomb]
    exact (hadd _ _ _ _ h0 h1).trans (by rw [← Int.mul_add, ← hKq, Int.pow_succ, Int.mul_assoc])

/-- Theorem M1.6 (Layer-1 Coupled Additive-Multiplicative Cost Conservation). -/
theorem layer1_conservation {S : Nat} (A : PrefixAut S) (B : Int)
    (mu cost : Fin S → Bool → Int) (D : Int) (kappa phi : Fin S → Int)
    (hK0 : IsKirchhoff0 A B mu D kappa)
    (hK1 : IsKirchhoff1 A B mu cost D kappa phi) :
    ∀ (N : Nat) (q : Fin S),
      D * costSum A B mu cost N q + activeCostPot A mu cost kappa phi N q = B ^ N * phi q := by
  have hL0 := layer0_conservation A B mu D kappa hK0
  intro N
  induction N with
  | zero => intro q; simp [costSum, activeCostPot]
  | succ N ih =>
    intro q
    simp only [costSum, activeCostPot]
    have branch_eq : ∀ b : Bool,
        D * (match A.step q b with
             | Step.dead => 0
             | Step.emit => mu q b * (cost q b * B ^ N)
             | Step.cont q' => mu q b * (cost q b * charSum A B mu N q' + costSum A B mu cost N q')) +
        (match A.step q b with
         | Step.dead => 0
         | Step.emit => 0
         | Step.cont q' =>
           mu q b * (cost q b * activePot A mu kappa N q' + activeCostPot A mu cost kappa phi N q')) =
        B ^ N * (mu q b * (cost q b * stepVal kappa D (A.step q b) + stepVal phi 0 (A.step q b))) := by
      intro b
      cases A.step q b with
      | dead => simp [stepVal]
      | emit => simp only [stepVal]; grind
      | cont q' =>
        simp only [stepVal]
        have h0' := hL0 N q'
        have h1' := ih q'
        grind
    have h0 := branch_eq false
    have h1 := branch_eq true
    have hK1q := hK1 q
    have hcomb : ∀ a b c d : Int, (a + b) + (c + d) = (a + c) + (b + d) := fun _ _ _ _ => by omega
    have hadd : ∀ a b c d : Int, a = b → c = d → a + c = b + d := by intro _ _ _ _ ha hb; rw [ha, hb]
    rw [Int.mul_add, hcomb]
    exact (hadd _ _ _ _ h0 h1).trans (by rw [← Int.mul_add, ← hK1q, Int.pow_succ, Int.mul_assoc])

/-! ### Pure-Integer Geometric Residual Contraction (Finite → Infinite Limit Engine) -/

theorem activeMass_le_pow {S : Nat} (A : PrefixAut S) (N : Nat) (q : Fin S) :
    activeMass A N q ≤ 2 ^ N := by
  induction N generalizing q with
  | zero => simp [activeMass]
  | succ N ih =>
    simp only [activeMass, Nat.pow_succ]
    have h0 : (match A.step q false with | Step.cont q' => activeMass A N q' | _ => 0) ≤ 2 ^ N := by
      cases A.step q false <;> simp [ih]
    have h1 : (match A.step q true with | Step.cont q' => activeMass A N q' | _ => 0) ≤ 2 ^ N := by
      cases A.step q true <;> simp [ih]
    exact Nat.le_trans (Nat.add_le_add h0 h1) (by omega)

/-- Single-Exit Contraction Lemma. -/
theorem activeMass_lt_pow_of_exit {S : Nat} (A : PrefixAut S) {q : Fin S} {u : List Bool}
    (hexit : runActive A q u = none) :
    activeMass A u.length q < 2 ^ u.length := by
  induction u generalizing q with
  | nil => simp [runActive] at hexit
  | cons b bs ih =>
    simp only [List.length_cons, activeMass, Nat.pow_succ]
    have h0_le : (match A.step q false with | Step.cont q' => activeMass A bs.length q' | _ => 0) ≤ 2 ^ bs.length := by
      cases A.step q false <;> simp [activeMass_le_pow]
    have h1_le : (match A.step q true with | Step.cont q' => activeMass A bs.length q' | _ => 0) ≤ 2 ^ bs.length := by
      cases A.step q true <;> simp [activeMass_le_pow]
    have hpos : 0 < 2 ^ bs.length := Nat.pow_pos (by omega)
    cases b with
    | false =>
      simp only [runActive] at hexit
      cases hs : A.step q false with
      | cont q' =>
        simp only [hs] at hexit
        have hlt := ih hexit
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hlt h1_le) (by omega)
      | emit => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hpos h1_le) (by omega)
      | dead => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hpos h1_le) (by omega)
    | true =>
      simp only [runActive] at hexit
      cases hs : A.step q true with
      | cont q' =>
        simp only [hs] at hexit
        have hlt := ih hexit
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt h0_le hlt) (by omega)
      | emit => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt h0_le hpos) (by omega)
      | dead => exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt h0_le hpos) (by omega)

theorem activeMass_add_le {S : Nat} (A : PrefixAut S) {n R : Nat}
    (hR : ∀ q' : Fin S, activeMass A n q' ≤ R) :
    ∀ (m : Nat) (q : Fin S), activeMass A (m + n) q ≤ activeMass A m q * R := by
  intro m
  induction m with
  | zero => intro q; simp [activeMass, hR q]
  | succ m ih =>
    intro q
    rw [Nat.succ_add]
    simp only [activeMass, Nat.add_mul]
    have h0 : (match A.step q false with | Step.cont q' => activeMass A (m + n) q' | _ => 0) ≤
        (match A.step q false with | Step.cont q' => activeMass A m q' | _ => 0) * R := by
      cases A.step q false <;> simp [ih]
    have h1 : (match A.step q true with | Step.cont q' => activeMass A (m + n) q' | _ => 0) ≤
        (match A.step q true with | Step.cont q' => activeMass A m q' | _ => 0) * R := by
      cases A.step q true <;> simp [ih]
    exact Nat.add_le_add h0 h1

theorem activeMass_mul_le {S : Nat} (A : PrefixAut S) {M R : Nat}
    (hR : ∀ q : Fin S, activeMass A M q ≤ R) :
    ∀ (k : Nat) (q : Fin S), activeMass A (k * M) q ≤ R ^ k := by
  intro k
  induction k with
  | zero => intro q; simp [activeMass]
  | succ k ih =>
    intro q
    rw [Nat.succ_mul, Nat.pow_succ]
    exact Nat.le_trans (activeMass_add_le A hR (k * M) q) (Nat.mul_le_mul_right R (ih q))

theorem activePot_natAbs_le {S : Nat} (A : PrefixAut S) (mu : Fin S → Bool → Int)
    (kappa : Fin S → Int) (Kmax : Nat)
    (hmu : ∀ q b, (mu q b).natAbs ≤ 1) (hK : ∀ q, (kappa q).natAbs ≤ Kmax) :
    ∀ (N : Nat) (q : Fin S), (activePot A mu kappa N q).natAbs ≤ activeMass A N q * Kmax := by
  intro N
  induction N with
  | zero => intro q; simp [activePot, activeMass, hK q]
  | succ N ih =>
    intro q
    simp only [activePot, activeMass, Nat.add_mul]
    have hbr : ∀ b : Bool,
        (match A.step q b with
         | Step.dead => (0 : Int)
         | Step.emit => 0
         | Step.cont q' => mu q b * activePot A mu kappa N q').natAbs ≤
        (match A.step q b with
         | Step.cont q' => activeMass A N q'
         | _ => 0) * Kmax := by
      intro b
      cases A.step q b with
      | dead => simp
      | emit => simp
      | cont q' =>
        rw [Int.natAbs_mul]
        simpa using Nat.mul_le_mul (hmu q b) (ih q')
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add (hbr false) (hbr true))

theorem activeCostPot_natAbs_le {S : Nat} (A : PrefixAut S) (mu cost : Fin S → Bool → Int)
    (kappa phi : Fin S → Int) (Cmax Kmax Pmax : Nat)
    (hmu : ∀ q b, (mu q b).natAbs ≤ 1)
    (hC : ∀ q b, (cost q b).natAbs ≤ Cmax)
    (hK : ∀ q, (kappa q).natAbs ≤ Kmax)
    (hP : ∀ q, (phi q).natAbs ≤ Pmax) :
    ∀ (N : Nat) (q : Fin S),
      (activeCostPot A mu cost kappa phi N q).natAbs ≤
        activeMass A N q * (N * Cmax * Kmax + Pmax) := by
  intro N
  induction N with
  | zero => intro q; simp [activeCostPot, activeMass, hP q]
  | succ N ih =>
    intro q
    simp only [activeCostPot, activeMass]
    rw [Nat.add_mul]
    have hbr : ∀ b : Bool,
        (match A.step q b with
         | Step.dead => (0 : Int)
         | Step.emit => 0
         | Step.cont q' =>
           mu q b * (cost q b * activePot A mu kappa N q' + activeCostPot A mu cost kappa phi N q')).natAbs ≤
        (match A.step q b with
         | Step.cont q' => activeMass A N q'
         | _ => 0) * ((N + 1) * Cmax * Kmax + Pmax) := by
      intro b
      cases A.step q b with
      | dead => simp
      | emit => simp
      | cont q' =>
        rw [Int.natAbs_mul]
        have h1 : (cost q b * activePot A mu kappa N q').natAbs ≤
            Cmax * (activeMass A N q' * Kmax) := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul (hC q b) (activePot_natAbs_le A mu kappa Kmax hmu hK N q')
        have h2 := ih q'
        have hstep : Cmax * (activeMass A N q' * Kmax) + activeMass A N q' * (N * Cmax * Kmax + Pmax) =
            activeMass A N q' * ((N + 1) * Cmax * Kmax + Pmax) := by grind
        have hsum : (cost q b * activePot A mu kappa N q' + activeCostPot A mu cost kappa phi N q').natAbs ≤
            activeMass A N q' * ((N + 1) * Cmax * Kmax + Pmax) := by
          rw [← hstep]
          exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add h1 h2)
        simpa using Nat.mul_le_mul (hmu q b) hsum
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add (hbr false) (hbr true))

/-- Theorem M1.7a (Pure-Integer Layer-0 Exponential Limit Certificate, ∀ k : Nat). -/
theorem layer0_contraction {S : Nat} (A : PrefixAut S) (B : Int) (mu : Fin S → Bool → Int)
    (D : Int) (kappa : Fin S → Int) (M R Kmax : Nat)
    (hK0 : IsKirchhoff0 A B mu D kappa)
    (hmu : ∀ q b, (mu q b).natAbs ≤ 1)
    (hK : ∀ q, (kappa q).natAbs ≤ Kmax)
    (hR : ∀ q, activeMass A M q ≤ R) :
    ∀ (k : Nat) (q : Fin S),
      (B ^ (k * M) * kappa q - D * charSum A B mu (k * M) q).natAbs ≤ R ^ k * Kmax := by
  intro k q
  have hcons := layer0_conservation A B mu D kappa hK0 (k * M) q
  have hdiff : B ^ (k * M) * kappa q - D * charSum A B mu (k * M) q = activePot A mu kappa (k * M) q := by
    omega
  rw [hdiff]
  exact Nat.le_trans (activePot_natAbs_le A mu kappa Kmax hmu hK (k * M) q)
    (Nat.mul_le_mul_right Kmax (activeMass_mul_le A hR k q))

/-- Theorem M1.7b (Pure-Integer Layer-1 Exponential Limit Certificate, ∀ k : Nat). -/
theorem layer1_contraction {S : Nat} (A : PrefixAut S) (B : Int) (mu cost : Fin S → Bool → Int)
    (D : Int) (kappa phi : Fin S → Int) (M R Cmax Kmax Pmax : Nat)
    (hK0 : IsKirchhoff0 A B mu D kappa)
    (hK1 : IsKirchhoff1 A B mu cost D kappa phi)
    (hmu : ∀ q b, (mu q b).natAbs ≤ 1)
    (hC : ∀ q b, (cost q b).natAbs ≤ Cmax)
    (hK : ∀ q, (kappa q).natAbs ≤ Kmax)
    (hP : ∀ q, (phi q).natAbs ≤ Pmax)
    (hR : ∀ q, activeMass A M q ≤ R) :
    ∀ (k : Nat) (q : Fin S),
      (B ^ (k * M) * phi q - D * costSum A B mu cost (k * M) q).natAbs ≤
        R ^ k * (k * M * Cmax * Kmax + Pmax) := by
  intro k q
  have hcons := layer1_conservation A B mu cost D kappa phi hK0 hK1 (k * M) q
  have hdiff : B ^ (k * M) * phi q - D * costSum A B mu cost (k * M) q =
      activeCostPot A mu cost kappa phi (k * M) q := by
    omega
  rw [hdiff]
  exact Nat.le_trans (activeCostPot_natAbs_le A mu cost kappa phi Cmax Kmax Pmax hmu hC hK hP (k * M) q)
    (Nat.mul_le_mul_right _ (activeMass_mul_le A hR k q))

/-! ### Theorem M1.8: Finite-State Order-Type ω Obstruction Engine -/

theorem runActive_append {S : Nat} (A : PrefixAut S) (q q' : Fin S) (u v : List Bool)
    (hu : runActive A q u = some q') :
    runActive A q (u ++ v) = runActive A q' v := by
  induction u generalizing q with
  | nil => simp [runActive] at hu; subst hu; rfl
  | cons b bs ih =>
    simp only [runActive] at hu
    cases hs : A.step q b with
    | cont q1 =>
      simp only [hs] at hu
      simp only [List.cons_append, runActive, hs]
      exact ih q1 hu
    | emit => simp only [hs] at hu; cases hu
    | dead => simp only [hs] at hu; cases hu

theorem accepts_of_runActive_append {S : Nat} (A : PrefixAut S) {q q' : Fin S} {u v : List Bool}
    (hu : runActive A q u = some q') (hv : Accepts A q' v) :
    Accepts A q (u ++ v) := by
  induction u generalizing q with
  | nil => simp [runActive] at hu; subst hu; exact hv
  | cons b bs ih =>
    simp only [runActive] at hu
    cases hs : A.step q b with
    | cont q1 =>
      simp only [hs] at hu
      exact Accepts.cont hs (ih hu)
    | emit => simp only [hs] at hu; cases hu
    | dead => simp only [hs] at hu; cases hu

theorem no_infinite_descending_nat (f : Nat → Nat) (h : ∀ n, f (n + 1) < f n) : False := by
  suffices ∀ m n, f n ≤ m → False from this (f 0) 0 (Nat.le_refl _)
  intro m
  induction m with
  | zero => intro n hn; have := h n; omega
  | succ m ih => intro n hn; have := h n; exact ih (n + 1) (by omega)

/-- Theorem M1.8 (Finite-State Order-Type ω Obstruction). -/
theorem order_type_omega_obstruction {S : Nat} (A : PrefixAut S)
    (q : Fin S) (p c' s' : List Bool)
    (hp : runActive A A.init p = some q)
    (hc : runActive A q (false :: c') = some q)
    (hs : Accepts A q (true :: s')) :
    (∀ n, Accepts A A.init (p ++ repeatList (false :: c') n ++ (true :: s'))) ∧
    (∀ n, lexLt (p ++ repeatList (false :: c') (n + 1) ++ (true :: s'))
                (p ++ repeatList (false :: c') n ++ (true :: s'))) ∧
    (∀ e : Nat → List Bool,
      (∀ i j, i < j → lexLt (e i) (e j)) →
      (∀ w, Accepts A A.init w → ∃ i, e i = w) → False) := by
  have hrep : ∀ n, runActive A q (repeatList (false :: c') n) = some q := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [repeatList]
      rw [runActive_append A q q (false :: c') (repeatList (false :: c') n) hc, ih]
  have hacc : ∀ n, Accepts A A.init (p ++ repeatList (false :: c') n ++ (true :: s')) := by
    intro n
    rw [List.append_assoc]
    exact accepts_of_runActive_append A hp (accepts_of_runActive_append A (hrep n) hs)
  have hdesc : ∀ n, lexLt (p ++ repeatList (false :: c') (n + 1) ++ (true :: s'))
                          (p ++ repeatList (false :: c') n ++ (true :: s')) := by
    intro n
    have hsplit : ∀ m, repeatList (false :: c') (m + 1) =
        repeatList (false :: c') m ++ (false :: c') := by
      intro m
      induction m with
      | zero => simp [repeatList]
      | succ m ihm =>
        change (false :: c') ++ repeatList (false :: c') (m + 1) =
          ((false :: c') ++ repeatList (false :: c') m) ++ (false :: c')
        rw [ihm, List.append_assoc]
    rw [hsplit n]
    have hlhs : p ++ (repeatList (false :: c') n ++ (false :: c')) ++ (true :: s') =
        (p ++ repeatList (false :: c') n) ++ (false :: (c' ++ (true :: s'))) := by
      simp [List.append_assoc]
    rw [hlhs]
    apply lexLt_append_left
    exact lexLt.false_true (c' ++ (true :: s')) s'
  refine ⟨hacc, hdesc, ?_⟩
  intro e hmono hsurj
  have hex : ∀ n, ∃ i, e i = p ++ repeatList (false :: c') n ++ (true :: s') :=
    fun n => hsurj _ (hacc n)
  let idx : Nat → Nat := fun n => Classical.choose (hex n)
  have hidx : ∀ n, e (idx n) = p ++ repeatList (false :: c') n ++ (true :: s') :=
    fun n => Classical.choose_spec (hex n)
  have hlt : ∀ n, idx (n + 1) < idx n := by
    intro n
    have hchain := hdesc n
    rw [← hidx (n + 1), ← hidx n] at hchain
    cases Nat.lt_or_ge (idx (n + 1)) (idx n) with
    | inl h => exact h
    | inr hge =>
      cases Nat.eq_or_lt_of_le hge with
      | inl heq => rw [heq] at hchain; exact False.elim (lexLt_irrefl _ hchain)
      | inr hgt => exact False.elim (lexLt_asymm hchain (hmono _ _ hgt))
  exact no_infinite_descending_nat idx hlt


/-! ==========================================================================
    SECTION 3: PARAMETERIZED INFINITE THEOREMS T1, T2, T3, T4 (VIA MECHANISM I)
    ========================================================================== -/

/-! ### The `k`-bonacci Self-Delimiting Prefix-Code Automaton (`k ≥ 1`) -/

/-- Theorem T1a (`k`-bonacci Infinite-Length Unique Stream Decodability, ∀ k ≥ 1). -/
theorem fibAut_unique_decodable (k : Nat) (hk : 0 < k) (ws : List (List Bool))
    (hws : ∀ w ∈ ws, Accepts (fibAut k hk) ⟨0, hk⟩ w) :
    decodeStream (fibAut k hk) ws.flatten = some ws :=
  decodeStream_flatten (fibAut k hk) ws hws

theorem fibAut_exit_ones (k : Nat) (hk : 0 < k) (q : Fin k) :
    runActive (fibAut k hk) q (List.replicate k true) = none := by
  have hgen : ∀ (m : Nat) (q : Fin k), k - q.val ≤ m →
      runActive (fibAut k hk) q (List.replicate m true) = none := by
    intro m
    induction m with
    | zero => intro q hle; have := q.isLt; omega
    | succ m ih =>
      intro q hle
      have := q.isLt
      simp only [List.replicate_succ, runActive, fibAut]
      by_cases hlt : q.val + 1 < k
      · simp only [hlt, ↓reduceDIte]
        exact ih ⟨q.val + 1, hlt⟩ (by dsimp only; omega)
      · simp only [hlt, ↓reduceDIte]
  exact hgen k q (by omega)

theorem fibAut_activeMass_le (k : Nat) (hk : 0 < k) (q : Fin k) :
    activeMass (fibAut k hk) k q ≤ 2 ^ k - 1 := by
  have hlt := activeMass_lt_pow_of_exit (fibAut k hk) (fibAut_exit_ones k hk q)
  simp only [List.length_replicate] at hlt
  omega

theorem fibAut_kraft_kirchhoff (k : Nat) (hk : 0 < k) :
    IsKirchhoff0 (fibAut k hk) 2 (fun _ _ => 1) 1 (fun _ => 1) := by
  intro q
  simp only [fibAut, stepVal]
  by_cases hlt : q.val + 1 < k <;> simp [hlt]

/-- Theorem T1b (`k`-bonacci Exact Finite-Horizon Kraft Conservation & Contraction, ∀ k ≥ 1, ∀ N). -/
theorem fibAut_kraft_conservation (k : Nat) (hk : 0 < k) (N : Nat) (q : Fin k) :
    charSum (fibAut k hk) 2 (fun _ _ => 1) N q +
      activePot (fibAut k hk) (fun _ _ => 1) (fun _ => 1) N q = (2 : Int) ^ N := by
  have h := layer0_conservation (fibAut k hk) 2 (fun _ _ => 1) 1 (fun _ => 1)
    (fibAut_kraft_kirchhoff k hk) N q
  simpa using h

theorem fibAut_kraft_contraction (k : Nat) (hk : 0 < k) (m : Nat) :
    ((2 : Int) ^ (m * k) - charSum (fibAut k hk) 2 (fun _ _ => 1) (m * k) ⟨0, hk⟩).natAbs ≤
      (2 ^ k - 1) ^ m := by
  have h := layer0_contraction (fibAut k hk) 2 (fun _ _ => 1) 1 (fun _ => 1) k (2 ^ k - 1) 1
    (fibAut_kraft_kirchhoff k hk) (fun _ _ => by decide) (fun _ => by decide)
    (fibAut_activeMass_le k hk) m ⟨0, hk⟩
  simpa using h

theorem fibAut_len_kirchhoff (k : Nat) (hk : 0 < k) :
    IsKirchhoff1 (fibAut k hk) 2 (fun _ _ => 1) (fun _ _ => 1) 1 (fun _ => 1) (fibLenPhi k) := by
  intro q
  simp only [fibAut, stepVal, fibLenPhi, Int.one_mul]
  have hp0 : (2 : Int) ^ (0 + 1) = 2 := by decide
  by_cases hlt : q.val + 1 < k
  · simp only [hlt, ↓reduceDIte, hp0]
    have hp1 : (2 : Int) ^ (q.val + 1 + 1) = 2 * (2 : Int) ^ (q.val + 1) := by
      rw [Int.pow_succ]; grind
    rw [hp1]; omega
  · simp only [hlt, ↓reduceDIte, hp0]
    have hq : q.val + 1 = k := by omega
    have hpk : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ k := by rw [Int.pow_succ]; grind
    rw [hq, hpk]; omega

theorem fibAut_length_conservation (k : Nat) (hk : 0 < k) (N : Nat) :
    costSum (fibAut k hk) 2 (fun _ _ => 1) (fun _ _ => 1) N ⟨0, hk⟩ +
      activeCostPot (fibAut k hk) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1) (fibLenPhi k) N ⟨0, hk⟩ =
      (2 : Int) ^ N * ((2 : Int) ^ (k + 1) - 2) := by
  have h := layer1_conservation (fibAut k hk) 2 (fun _ _ => 1) (fun _ _ => 1) 1
    (fun _ => 1) (fibLenPhi k) (fibAut_kraft_kirchhoff k hk) (fibAut_len_kirchhoff k hk) N ⟨0, hk⟩
  simpa [fibLenPhi] using h

theorem fibAut_zero_bias (k : Nat) (hk : 0 < k) (N : Nat) (q : Fin k) :
    costSum (fibAut k hk) 2 (fun _ _ => 1) biasCost N q +
      activeCostPot (fibAut k hk) (fun _ _ => 1) biasCost (fun _ => 1) (fun _ => 0) N q = 0 := by
  have hK1 : IsKirchhoff1 (fibAut k hk) 2 (fun _ _ => 1) biasCost 1 (fun _ => 1) (fun _ => 0) := by
    intro q'
    simp only [fibAut, stepVal, biasCost]
    by_cases hlt : q'.val + 1 < k <;> simp [hlt]
  have h := layer1_conservation (fibAut k hk) 2 (fun _ _ => 1) biasCost 1
    (fun _ => 1) (fun _ => 0) (fibAut_kraft_kirchhoff k hk) hK1 N q
  simpa using h

/-! ### Theorem T2: `k`-bonacci Popcount-Parity vs. Length-Parity Jacobsthal Reciprocal Laws -/

theorem fibAut_popParity_kirchhoff (k : Nat) (hk : 0 < k) :
    IsKirchhoff0 (fibAut k hk) 2 popParityMu (jacobsthal (k + 1)) (fibPopKappa k) := by
  intro q
  have hq_lt := q.isLt
  dsimp only [IsKirchhoff0, fibAut, popParityMu]
  have h0 : fibPopKappa k ⟨0, hk⟩ = negOnePow k := by simp [fibPopKappa, jacobsthal]
  by_cases hlt : q.val + 1 < k
  · simp only [hlt, ↓reduceDIte, stepVal, h0, Bool.false_eq_true, ↓reduceIte]
    simp only [fibPopKappa]
    have hstep := jacobsthal_step (q.val + 1)
    have hsign1 : negOnePow (k + (q.val + 1)) = -negOnePow (k + q.val) := by
      rw [← Nat.add_assoc, negOnePow_succ]
    have hmul : negOnePow (k + q.val) * negOnePow (q.val + 1) = -negOnePow k := by
      rw [negOnePow_add k q.val, negOnePow_succ]
      have hsq := negOnePow_mul_self q.val
      grind
    rw [hsign1, hstep]; grind
  · simp only [hlt, ↓reduceDIte, stepVal, h0, Bool.false_eq_true, ↓reduceIte]
    simp only [fibPopKappa]
    have hq : q.val + 1 = k := by omega
    have hstep := jacobsthal_step k
    have hodd : negOnePow (k + q.val) = -1 := by
      have heq : k + q.val = q.val + q.val + 1 := by omega
      rw [heq, negOnePow_succ, negOnePow_add, negOnePow_mul_self]
    rw [hstep, hodd, hq]; grind

theorem fibAut_lenParity_kirchhoff (k : Nat) (hk : 0 < k) :
    IsKirchhoff0 (fibAut k hk) 2 lenParityMu (jacobsthal (k + 2)) (fibLenPKappa k) := by
  intro q
  have hq_lt := q.isLt
  dsimp only [IsKirchhoff0, fibAut, lenParityMu]
  have h0 : fibLenPKappa k ⟨0, hk⟩ = negOnePow k := by simp [fibLenPKappa, jacobsthal]
  by_cases hlt : q.val + 1 < k
  · simp only [hlt, ↓reduceDIte, stepVal, h0]
    simp only [fibLenPKappa]
    have hstep : jacobsthal (q.val + 1 + 2) = 2 * jacobsthal (q.val + 2) + negOnePow (q.val + 2) := by
      have heq : q.val + 1 + 2 = (q.val + 2) + 1 := by omega
      rw [heq]; exact jacobsthal_step (q.val + 2)
    have hsign1 : negOnePow (k + (q.val + 1)) = -negOnePow (k + q.val) := by
      rw [← Nat.add_assoc, negOnePow_succ]
    have hmul : negOnePow (k + q.val) * negOnePow (q.val + 2) = negOnePow k := by
      rw [negOnePow_add k q.val, negOnePow_succ, negOnePow_succ]
      have hsq := negOnePow_mul_self q.val
      grind
    rw [hsign1, hstep]; grind
  · simp only [hlt, ↓reduceDIte, stepVal, h0]
    simp only [fibLenPKappa]
    have hq : q.val + 2 = k + 1 := by omega
    have hstep : jacobsthal (k + 2) = 2 * jacobsthal (k + 1) + negOnePow (k + 1) := jacobsthal_step (k + 1)
    have hodd : negOnePow (k + q.val) = -1 := by
      have heq : k + q.val = q.val + q.val + 1 := by omega
      rw [heq, negOnePow_succ, negOnePow_add, negOnePow_mul_self]
    rw [hq, hstep, hodd, negOnePow_succ]; grind

/-- Theorem T2a (`k`-bonacci Popcount-Parity Jacobsthal Conservation, ∀ k ≥ 1, ∀ N). -/
theorem fibAut_popParity_conservation (k : Nat) (hk : 0 < k) (N : Nat) :
    jacobsthal (k + 1) * charSum (fibAut k hk) 2 popParityMu N ⟨0, hk⟩ +
      activePot (fibAut k hk) popParityMu (fibPopKappa k) N ⟨0, hk⟩ =
      (2 : Int) ^ N * negOnePow k := by
  have h := layer0_conservation (fibAut k hk) 2 popParityMu (jacobsthal (k + 1)) (fibPopKappa k)
    (fibAut_popParity_kirchhoff k hk) N ⟨0, hk⟩
  simpa [fibPopKappa, jacobsthal] using h

/-- Theorem T2b (`k`-bonacci Length-Parity Jacobsthal Conservation, ∀ k ≥ 1, ∀ N). -/
theorem fibAut_lenParity_conservation (k : Nat) (hk : 0 < k) (N : Nat) :
    jacobsthal (k + 2) * charSum (fibAut k hk) 2 lenParityMu N ⟨0, hk⟩ +
      activePot (fibAut k hk) lenParityMu (fibLenPKappa k) N ⟨0, hk⟩ =
      (2 : Int) ^ N * negOnePow k := by
  have h := layer0_conservation (fibAut k hk) 2 lenParityMu (jacobsthal (k + 2)) (fibLenPKappa k)
    (fibAut_lenParity_kirchhoff k hk) N ⟨0, hk⟩
  simpa [fibLenPKappa, jacobsthal] using h

/-- Theorem T2c (Exact Finite-Potential State-Shift Duality Embedding, ∀ k ≥ 1). -/
theorem fibAut_parity_duality_embedding (k : Nat) (hk : 0 < k) :
    fibPopKappa (k + 1) ⟨0, Nat.succ_pos k⟩ = -fibLenPKappa k ⟨0, hk⟩ ∧
    ∀ (q : Fin k), fibPopKappa (k + 1) ⟨q.val + 1, Nat.succ_lt_succ q.isLt⟩ = fibLenPKappa k q := by
  constructor
  · simp [fibPopKappa, fibLenPKappa, jacobsthal, negOnePow_succ]
  · intro q
    simp only [fibPopKappa, fibLenPKappa]
    have hidx : k + 1 + (q.val + 1) = (k + q.val) + 2 := by omega
    rw [hidx, negOnePow_succ, negOnePow_succ, Int.neg_neg]

/-! ### Theorem T3: Two-Parameter `(a, b)`-Run-Delimited Prefix-Code Family (`∀ a ≥ 1, b ≥ 1`) -/

/-- Theorem T3a (`(a, b)`-Run-Delimited Infinite-Length Unique Stream Decodability). -/
theorem runAut_unique_decodable (a b : Nat) (ha : 0 < a) (hb : 0 < b) (ws : List (List Bool))
    (hws : ∀ w ∈ ws, Accepts (runAut a b ha hb) ⟨0, by omega⟩ w) :
    decodeStream (runAut a b ha hb) ws.flatten = some ws :=
  decodeStream_flatten (runAut a b ha hb) ws hws

theorem runAut_step_false_SO (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1))
    (h : q.val = 0 ∨ a ≤ q.val) :
    (runAut a b ha hb).step q false =
      if ha1 : 1 < a then Step.cont ⟨1, by omega⟩ else Step.dead := by
  simp [runAut, h]

theorem runAut_step_false_Z (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1))
    (h1 : q.val ≠ 0) (h2 : q.val < a) :
    (runAut a b ha hb).step q false =
      if hnext : q.val + 1 < a then Step.cont ⟨q.val + 1, by omega⟩ else Step.dead := by
  have hnot : ¬ (q.val = 0 ∨ a ≤ q.val) := by omega
  simp [runAut, hnot]

theorem runAut_step_true_lt (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1))
    (h : q.val < a) :
    (runAut a b ha hb).step q true =
      if hb1 : 1 < b then Step.cont ⟨a, by omega⟩ else Step.emit := by
  simp [runAut, h]

theorem runAut_step_true_ge (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1))
    (h : a ≤ q.val) :
    (runAut a b ha hb).step q true =
      if hnext : q.val + 1 < a + b - 1 then Step.cont ⟨q.val + 1, hnext⟩ else Step.emit := by
  have hnot : ¬ (q.val < a) := by omega
  simp [runAut, hnot]

theorem runAut_exit_ones (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1)) :
    runActive (runAut a b ha hb) q (List.replicate b true) = none := by
  have hO : ∀ (m : Nat) (q : Fin (a + b - 1)), a ≤ q.val → a + b - 1 - q.val ≤ m →
      runActive (runAut a b ha hb) q (List.replicate m true) = none := by
    intro m
    induction m with
    | zero => intro q _ hle; have := q.isLt; omega
    | succ m ih =>
      intro q hge hle
      have := q.isLt
      simp only [List.replicate_succ, runActive]
      rw [runAut_step_true_ge a b ha hb q hge]
      by_cases hnext : q.val + 1 < a + b - 1
      · simp only [hnext, ↓reduceDIte]
        exact ih ⟨q.val + 1, hnext⟩ (by dsimp only; omega) (by dsimp only; omega)
      · simp only [hnext, ↓reduceDIte]
  cases b with
  | zero => omega
  | succ b' =>
    have := q.isLt
    simp only [List.replicate_succ, runActive]
    by_cases hlt : q.val < a
    · rw [runAut_step_true_lt a (b' + 1) ha hb q hlt]
      by_cases hb1 : 1 < b' + 1
      · simp only [hb1, ↓reduceDIte]
        exact hO b' ⟨a, by omega⟩ (Nat.le_refl a) (by dsimp only; omega)
      · simp only [hb1, ↓reduceDIte]
    · rw [runAut_step_true_ge a (b' + 1) ha hb q (by omega)]
      by_cases hnext : q.val + 1 < a + (b' + 1) - 1
      · simp only [hnext, ↓reduceDIte]
        exact hO b' ⟨q.val + 1, hnext⟩ (by dsimp only; omega) (by dsimp only; omega)
      · simp only [hnext, ↓reduceDIte]

theorem runAut_activeMass_le (a b : Nat) (ha : 0 < a) (hb : 0 < b) (q : Fin (a + b - 1)) :
    activeMass (runAut a b ha hb) b q ≤ 2 ^ b - 1 := by
  have hlt := activeMass_lt_pow_of_exit (runAut a b ha hb) (runAut_exit_ones a b ha hb q)
  simp only [List.length_replicate] at hlt
  omega

theorem int_pow_pred_mul_two (n : Nat) (hn : 1 ≤ n) :
    (2 : Int) ^ n = 2 * (2 : Int) ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ m => simp [Int.pow_succ]; grind

theorem runAut_kraft_kirchhoff (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    IsKirchhoff0 (runAut a b ha hb) 2 (fun _ _ => 1) (2 * runD a b) (runKraftKappa a b) := by
  intro q
  have hq_lt := q.isLt
  dsimp only [IsKirchhoff0]
  simp only [Int.one_mul]
  -- Evaluate the common boundary states `Z_1` and `O_1`
  have hZ1 : ∀ (h : 1 < a), runKraftKappa a b ⟨1, by omega⟩ = 2 * ((2 : Int) ^ (a - 1) - 1) := by
    intro h; simp [runKraftKappa, h]
  have hO1 : ∀ (h : 1 < b), runKraftKappa a b ⟨a, by omega⟩ = 2 * (2 : Int) ^ (a - 1) := by
    intro h
    have ha0 : a ≠ 0 := by omega
    have han : ¬ (a < a) := by omega
    simp [runKraftKappa, ha0, han]
  by_cases hq0 : q.val = 0
  · rw [runAut_step_false_SO a b ha hb q (Or.inl hq0),
        runAut_step_true_lt a b ha hb q (by omega)]
    have hqS : runKraftKappa a b q = 2 * (2 : Int) ^ (a - 1) - 1 := by simp [runKraftKappa, hq0]
    rw [hqS]
    by_cases ha1 : 1 < a <;> by_cases hb1 : 1 < b
    · simp only [ha1, hb1, ↓reduceDIte, stepVal, hZ1 ha1, hO1 hb1]; omega
    · have hb_eq : b = 1 := by omega
      have hB1 : (2 : Int) ^ (b - 1) = 1 := by simp [hb_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hZ1 ha1, runD, hB1]; omega
    · have ha_eq : a = 1 := by omega
      have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hO1 hb1, hA1]; omega
    · have ha_eq : a = 1 := by omega
      have hb_eq : b = 1 := by omega
      have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
      have hB1 : (2 : Int) ^ (b - 1) = 1 := by simp [hb_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, runD, hA1, hB1]; omega
  · by_cases hqa : q.val < a
    · rw [runAut_step_false_Z a b ha hb q hq0 hqa,
          runAut_step_true_lt a b ha hb q hqa]
      have hqZ : runKraftKappa a b q = 2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ (q.val - 1)) := by
        simp [runKraftKappa, hq0, hqa]
      rw [hqZ]
      have hp : (2 : Int) ^ q.val = 2 * (2 : Int) ^ (q.val - 1) := int_pow_pred_mul_two q.val (by omega)
      by_cases hnext : q.val + 1 < a <;> by_cases hb1 : 1 < b
      · simp only [hnext, hb1, ↓reduceDIte, stepVal, hO1 hb1]
        have hqn : runKraftKappa a b ⟨q.val + 1, by omega⟩ = 2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ q.val) := by
          simp [runKraftKappa, hnext]
        rw [hqn, hp]; omega
      · have hb_eq : b = 1 := by omega
        have hB1 : (2 : Int) ^ (b - 1) = 1 := by simp [hb_eq]
        simp only [hnext, hb1, ↓reduceDIte, stepVal, runD, hB1]
        have hqn : runKraftKappa a b ⟨q.val + 1, by omega⟩ = 2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ q.val) := by
          simp [runKraftKappa, hnext]
        rw [hqn, hp]; omega
      · have hqeq : a - 1 = q.val := by omega
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hO1 hb1]
        rw [hqeq, hp]; omega
      · have hqeq : a - 1 = q.val := by omega
        have hb_eq : b = 1 := by omega
        have hB1 : (2 : Int) ^ (b - 1) = 1 := by simp [hb_eq]
        simp only [hnext, hb1, ↓reduceDIte, stepVal, runD, hB1]
        rw [hqeq, hp]; omega
    · rw [runAut_step_false_SO a b ha hb q (Or.inr (by omega)),
          runAut_step_true_ge a b ha hb q (by omega)]
      have hqO : runKraftKappa a b q = 2 * ((2 : Int) ^ (a - 1) + (2 : Int) ^ (q.val - a) - 1) := by
        simp [runKraftKappa, hq0, hqa]
      rw [hqO]
      have hp : (2 : Int) ^ (q.val + 1 - a) = 2 * (2 : Int) ^ (q.val - a) := by
        have hs : q.val + 1 - a = (q.val - a) + 1 := by omega
        rw [hs, Int.pow_succ]; grind
      by_cases ha1 : 1 < a <;> by_cases hnext : q.val + 1 < a + b - 1
      · simp only [ha1, hnext, ↓reduceDIte, stepVal, hZ1 ha1]
        have hqn : runKraftKappa a b ⟨q.val + 1, hnext⟩ =
            2 * ((2 : Int) ^ (a - 1) + (2 : Int) ^ (q.val + 1 - a) - 1) := by
          have hna : ¬ (q.val + 1 < a) := by omega
          simp [runKraftKappa, hna]
        rw [hqn, hp]; omega
      · have hqeq : b - 1 = (q.val - a) + 1 := by omega
        have hpB : (2 : Int) ^ (b - 1) = 2 * (2 : Int) ^ (q.val - a) := by
          rw [hqeq, Int.pow_succ]; grind
        simp only [ha1, hnext, ↓reduceDIte, stepVal, hZ1 ha1, runD]
        rw [hpB]; omega
      · have ha_eq : a = 1 := by omega
        have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
        simp only [ha1, hnext, ↓reduceDIte, stepVal]
        have hqn : runKraftKappa a b ⟨q.val + 1, hnext⟩ =
            2 * ((2 : Int) ^ (a - 1) + (2 : Int) ^ (q.val + 1 - a) - 1) := by
          have hna : ¬ (q.val + 1 < a) := by omega
          simp [runKraftKappa, hna]
        rw [hqn, hp, hA1]; omega
      · have ha_eq : a = 1 := by omega
        have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
        have hqeq : b - 1 = (q.val - a) + 1 := by omega
        have hpB : (2 : Int) ^ (b - 1) = 2 * (2 : Int) ^ (q.val - a) := by
          rw [hqeq, Int.pow_succ]; grind
        simp only [ha1, hnext, ↓reduceDIte, stepVal, runD]
        rw [hpB, hA1]; omega

/-- Theorem T3b (`(a, b)`-Run-Delimited Exact Incomplete Kraft Conservation, ∀ a, b ≥ 1, ∀ N). -/
theorem runAut_kraft_conservation (a b : Nat) (ha : 0 < a) (hb : 0 < b) (N : Nat) :
    (2 * runD a b) * charSum (runAut a b ha hb) 2 (fun _ _ => 1) N ⟨0, by omega⟩ +
      activePot (runAut a b ha hb) (fun _ _ => 1) (runKraftKappa a b) N ⟨0, by omega⟩ =
      (2 : Int) ^ N * (2 * (2 : Int) ^ (a - 1) - 1) := by
  have h := layer0_conservation (runAut a b ha hb) 2 (fun _ _ => 1) (2 * runD a b)
    (runKraftKappa a b) (runAut_kraft_kirchhoff a b ha hb) N ⟨0, by omega⟩
  simpa [runKraftKappa] using h

theorem jacobsthal_run_step (A : Int) (j : Nat) (hj : 1 ≤ j) :
    2 * (2 * A * jacobsthal (j + 1) - 2 * jacobsthal (j - 1)) =
      (2 * A * jacobsthal (j + 2) - 2 * jacobsthal j) + negOnePow j * (2 * A - 2) := by
  have hs1 : jacobsthal (j + 2) = 2 * jacobsthal (j + 1) + negOnePow (j + 1) := jacobsthal_step (j + 1)
  have hs2 := jacobsthal_step (j - 1)
  have hjm : (j - 1) + 1 = j := by omega
  rw [hjm] at hs2
  have hsign1 : negOnePow (j + 1) = -negOnePow j := negOnePow_succ j
  have hsign2 : negOnePow (j - 1) = -negOnePow j := by
    have := negOnePow_succ (j - 1); rw [hjm] at this; omega
  rw [hs1, hs2, hsign1, hsign2]; grind

theorem runAut_popParity_kirchhoff (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    IsKirchhoff0 (runAut a b ha hb) 2 popParityMu (runPopD a b) (runPopKappa a b) := by
  intro q
  have hq_lt := q.isLt
  dsimp only [IsKirchhoff0, popParityMu]
  have hZ1 : ∀ (h : 1 < a), runPopKappa a b ⟨1, by omega⟩ = negOnePow b * (2 * ((2 : Int) ^ (a - 1) - 1)) := by
    intro h; simp [runPopKappa, h]
  have hO1 : ∀ (h : 1 < b), runPopKappa a b ⟨a, by omega⟩ = -negOnePow b * (2 * (2 : Int) ^ (a - 1)) := by
    intro h
    have ha0 : a ≠ 0 := by omega
    have han : ¬ (a < a) := by omega
    simp only [runPopKappa, ha0, han, ↓reduceIte, Nat.sub_self, Nat.zero_add, jacobsthal, negOnePow_succ]
    grind
  by_cases hq0 : q.val = 0
  · rw [runAut_step_false_SO a b ha hb q (Or.inl hq0),
        runAut_step_true_lt a b ha hb q (by omega)]
    have hqS : runPopKappa a b q = negOnePow b * (2 * (2 : Int) ^ (a - 1) - 1) := by simp [runPopKappa, hq0]
    rw [hqS]
    by_cases ha1 : 1 < a <;> by_cases hb1 : 1 < b
    · simp only [ha1, hb1, ↓reduceDIte, stepVal, hZ1 ha1, hO1 hb1]; grind
    · have hb_eq : b = 1 := by omega
      have hnb : negOnePow b = -1 := by simp [hb_eq, negOnePow]
      have hDb : runPopD a b = 2 * (2 : Int) ^ (a - 1) := by simp [runPopD, hb_eq, jacobsthal]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hZ1 ha1, hDb, hnb]; grind
    · have ha_eq : a = 1 := by omega
      have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hO1 hb1, hA1]; grind
    · have ha_eq : a = 1 := by omega
      have hb_eq : b = 1 := by omega
      have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
      have hnb : negOnePow b = -1 := by simp [hb_eq, negOnePow]
      have hDb : runPopD a b = 2 * (2 : Int) ^ (a - 1) := by simp [runPopD, hb_eq, jacobsthal]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hDb, hnb, hA1]; grind
  · by_cases hqa : q.val < a
    · rw [runAut_step_false_Z a b ha hb q hq0 hqa,
          runAut_step_true_lt a b ha hb q hqa]
      have hqZ : runPopKappa a b q = negOnePow b * (2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ (q.val - 1))) := by
        simp [runPopKappa, hq0, hqa]
      rw [hqZ]
      have hp : (2 : Int) ^ q.val = 2 * (2 : Int) ^ (q.val - 1) := int_pow_pred_mul_two q.val (by omega)
      by_cases hnext : q.val + 1 < a <;> by_cases hb1 : 1 < b
      · simp only [hnext, hb1, ↓reduceDIte, stepVal, hO1 hb1]
        have hqn : runPopKappa a b ⟨q.val + 1, by omega⟩ =
            negOnePow b * (2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ q.val)) := by
          simp [runPopKappa, hnext]
        rw [hqn, hp]; grind
      · have hb_eq : b = 1 := by omega
        have hnb : negOnePow b = -1 := by simp [hb_eq, negOnePow]
        have hDb : runPopD a b = 2 * (2 : Int) ^ (a - 1) := by simp [runPopD, hb_eq, jacobsthal]
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hDb]
        have hqn : runPopKappa a b ⟨q.val + 1, by omega⟩ =
            negOnePow b * (2 * ((2 : Int) ^ (a - 1) - (2 : Int) ^ q.val)) := by
          simp [runPopKappa, hnext]
        rw [hqn, hp, hnb]; grind
      · have hqeq : a - 1 = q.val := by omega
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hO1 hb1]
        rw [hqeq, hp]; grind
      · have hqeq : a - 1 = q.val := by omega
        have hb_eq : b = 1 := by omega
        have hnb : negOnePow b = -1 := by simp [hb_eq, negOnePow]
        have hDb : runPopD a b = 2 * (2 : Int) ^ (a - 1) := by simp [runPopD, hb_eq, jacobsthal]
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hDb, hnb]
        rw [hqeq, hp]; grind
    · rw [runAut_step_false_SO a b ha hb q (Or.inr (by omega)),
          runAut_step_true_ge a b ha hb q (by omega)]
      let j : Nat := q.val - a + 1
      have hj : 1 ≤ j := by omega
      have hqO : runPopKappa a b q =
          negOnePow (b + j) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 1) - 2 * jacobsthal (j - 1)) := by
        simp [runPopKappa, hq0, hqa, j]
      rw [hqO]
      have hstep := jacobsthal_run_step ((2 : Int) ^ (a - 1)) j hj
      have hsign_mul : negOnePow (b + j) * negOnePow j = negOnePow b := by
        rw [negOnePow_add, Int.mul_assoc, negOnePow_mul_self, Int.mul_one]
      have hsj : negOnePow (b + (j + 1)) = -negOnePow (b + j) := by
        rw [← Nat.add_assoc, negOnePow_succ]
      have hkey :
          2 * (negOnePow (b + j) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 1) - 2 * jacobsthal (j - 1))) =
          1 * (negOnePow b * (2 * ((2 : Int) ^ (a - 1) - 1))) +
            (-1) * (negOnePow (b + (j + 1)) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 2) - 2 * jacobsthal j)) := by
        have h1 : 2 * (negOnePow (b + j) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 1) - 2 * jacobsthal (j - 1))) =
            negOnePow (b + j) * (2 * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 1) - 2 * jacobsthal (j - 1))) := by
          grind
        rw [h1, hstep, hsj, Int.mul_add, ← Int.mul_assoc, hsign_mul]
        grind
      by_cases ha1 : 1 < a <;> by_cases hnext : q.val + 1 < a + b - 1
      · simp only [ha1, hnext, ↓reduceDIte, stepVal, hZ1 ha1]
        have hqn : runPopKappa a b ⟨q.val + 1, hnext⟩ =
            negOnePow (b + (j + 1)) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 2) - 2 * jacobsthal j) := by
          have hna : ¬ (q.val + 1 < a) := by omega
          have hj1 : q.val + 1 - a + 1 = j + 1 := by omega
          simp [runPopKappa, hna, hj1]
        rw [hqn]; exact hkey
      · have hjb : j + 1 = b := by omega
        have hsign2b : negOnePow (b + (j + 1)) = 1 := by
          rw [hjb, negOnePow_add, negOnePow_mul_self]
        have hjb1 : j + 2 = b + 1 := by omega
        have hjb2 : j = b - 1 := by omega
        simp only [ha1, hnext, ↓reduceDIte, stepVal, hZ1 ha1, runPopD]
        rw [hkey, hsign2b, hjb1, hjb2]; grind
      · have ha_eq : a = 1 := by omega
        have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
        simp only [ha1, hnext, ↓reduceDIte, stepVal]
        have hqn : runPopKappa a b ⟨q.val + 1, hnext⟩ =
            negOnePow (b + (j + 1)) * (2 * (2 : Int) ^ (a - 1) * jacobsthal (j + 2) - 2 * jacobsthal j) := by
          have hna : ¬ (q.val + 1 < a) := by omega
          have hj1 : q.val + 1 - a + 1 = j + 1 := by omega
          simp [runPopKappa, hna, hj1]
        rw [hqn, hkey, hA1]; grind
      · have ha_eq : a = 1 := by omega
        have hA1 : (2 : Int) ^ (a - 1) = 1 := by simp [ha_eq]
        have hjb : j + 1 = b := by omega
        have hsign2b : negOnePow (b + (j + 1)) = 1 := by
          rw [hjb, negOnePow_add, negOnePow_mul_self]
        have hjb1 : j + 2 = b + 1 := by omega
        have hjb2 : j = b - 1 := by omega
        simp only [ha1, hnext, ↓reduceDIte, stepVal, runPopD]
        rw [hkey, hsign2b, hjb1, hjb2, hA1]; grind

/-- Theorem T3c (`(a, b)`-Run-Delimited Exact Popcount-Parity Jacobsthal Conservation, ∀ a, b ≥ 1, ∀ N). -/
theorem runAut_popParity_conservation (a b : Nat) (ha : 0 < a) (hb : 0 < b) (N : Nat) :
    runPopD a b * charSum (runAut a b ha hb) 2 popParityMu N ⟨0, by omega⟩ +
      activePot (runAut a b ha hb) popParityMu (runPopKappa a b) N ⟨0, by omega⟩ =
      (2 : Int) ^ N * (negOnePow b * (2 * (2 : Int) ^ (a - 1) - 1)) := by
  have h := layer0_conservation (runAut a b ha hb) 2 popParityMu (runPopD a b)
    (runPopKappa a b) (runAut_popParity_kirchhoff a b ha hb) N ⟨0, by omega⟩
  simpa [runPopKappa] using h

theorem runAut_kraftScaled_kirchhoff (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    IsKirchhoff0 (runAut a b ha hb) 2 (fun _ _ => 1) (2 * runD a b * runD a b) (runKraftScaled a b) := by
  intro q
  have h := runAut_kraft_kirchhoff a b ha hb q
  dsimp only [IsKirchhoff0] at h ⊢
  simp only [Int.one_mul] at h ⊢
  have hsv : ∀ st, stepVal (runKraftScaled a b) (2 * runD a b * runD a b) st =
      runD a b * stepVal (runKraftKappa a b) (2 * runD a b) st := by
    intro st; cases st with
    | cont q' => rfl
    | emit => simp only [stepVal]; grind
    | dead => simp [stepVal]
  rw [hsv, hsv, runKraftScaled]; grind

theorem bias_start_alg (A B a b : Int) :
    let D := A + B - 1
    2 * (2 * A * B * (a + b - 2) - (a - 2) * A - (b - 2) * B - 1) =
    -(D * (2 * (A - 1))) + (2 * (A - 1) * (B * (b - 1) + (B - 1) * (a - 1)) + 2 * D * (a - 1)) +
    (D * (2 * A) + (2 * (B - 1) * (A * (a - 1) + (A - 1) * (b - 1)) + 2 * D * (b - 1))) := by
  grind

theorem bias_chain_alg (A D P r X : Int) :
    2 * (2 * (A - X) * P + 2 * D * r * X) =
    -(D * (2 * (A - 2 * X))) + (2 * (A - 2 * X) * P + 2 * D * (r - 1) * (2 * X)) +
    (D * (2 * A) + 2 * A * P) := by
  grind

theorem bias_ochain_alg (A B D Q r X : Int) (_hD : D = A + B - 1) :
    2 * (2 * (B - X) * Q + 2 * D * r * X) =
    -(D * (2 * (A - 1))) + 2 * B * Q +
    (D * (2 * (A + 2 * X - 1)) + (2 * (B - 2 * X) * Q + 2 * D * (r - 1) * (2 * X))) := by
  grind

theorem bias_O1_eq (A B a b : Int) :
    let D := A + B - 1
    2 * (B - 1) * (A * (a - 1) + (A - 1) * (b - 1)) + 2 * D * (b - 1) =
    2 * A * (B * (b - 1) + (B - 1) * (a - 1)) := by
  grind

theorem bias_Z1_eq (A B a b : Int) :
    let D := A + B - 1
    2 * (A - 1) * (B * (b - 1) + (B - 1) * (a - 1)) + 2 * D * (a - 1) =
    2 * B * (A * (a - 1) + (A - 1) * (b - 1)) := by
  grind

theorem runAut_bias_kirchhoff (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    IsKirchhoff1 (runAut a b ha hb) 2 (fun _ _ => 1) biasCost
      (2 * runD a b * runD a b) (runKraftScaled a b) (runBiasPhi a b) := by
  intro q
  have hq_lt := q.isLt
  dsimp only [IsKirchhoff1, biasCost]
  simp only [Int.one_mul]
  let A : Int := (2 : Int) ^ (a - 1)
  let B : Int := (2 : Int) ^ (b - 1)
  let D : Int := A + B - 1
  let P : Int := B * ((b : Int) - 1) + (B - 1) * ((a : Int) - 1)
  let Q : Int := A * ((a : Int) - 1) + (A - 1) * ((b : Int) - 1)
  have hD : runD a b = D := rfl
  have hKZ1 : ∀ (h : 1 < a), runKraftScaled a b ⟨1, by omega⟩ = D * (2 * (A - 1)) := by
    intro h; simp [runKraftScaled, runKraftKappa, h, hD, A]
  have hKO1 : ∀ (h : 1 < b), runKraftScaled a b ⟨a, by omega⟩ = D * (2 * A) := by
    intro h
    have ha0 : a ≠ 0 := by omega
    have han : ¬ (a < a) := by omega
    simp [runKraftScaled, runKraftKappa, ha0, han, hD, A]
  have hPZ1 : ∀ (h : 1 < a), runBiasPhi a b ⟨1, by omega⟩ = 2 * B * Q := by
    intro h
    have hraw : runBiasPhi a b ⟨1, by omega⟩ = 2 * (A - 1) * P + 2 * D * ((a : Int) - 1) := by
      simp [runBiasPhi, h, A, B, D, P]
    rw [hraw]
    exact bias_Z1_eq A B a b
  have hPO1 : ∀ (h : 1 < b), runBiasPhi a b ⟨a, by omega⟩ = 2 * A * P := by
    intro h
    have ha0 : a ≠ 0 := by omega
    have han : ¬ (a < a) := by omega
    have hraw : runBiasPhi a b ⟨a, by omega⟩ = 2 * (B - 1) * Q + 2 * D * ((b : Int) - 1) := by
      simp [runBiasPhi, ha0, han, A, B, D, Q]
    rw [hraw]
    exact bias_O1_eq A B a b
  by_cases hq0 : q.val = 0
  · rw [runAut_step_false_SO a b ha hb q (Or.inl hq0),
        runAut_step_true_lt a b ha hb q (by omega)]
    have hqS : runBiasPhi a b q = runBiasNum a b := by simp [runBiasPhi, hq0]
    rw [hqS]
    by_cases ha1 : 1 < a <;> by_cases hb1 : 1 < b
    · simp only [ha1, hb1, ↓reduceDIte, stepVal, hKZ1 ha1, hKO1 hb1, hPZ1 ha1, hPO1 hb1, runBiasNum]
      have := bias_start_alg A B a b
      have := bias_O1_eq A B a b
      have := bias_Z1_eq A B a b
      grind
    · have hb_eq : b = 1 := by omega
      have hB1 : B = 1 := by simp [B, hb_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hKZ1 ha1, hPZ1 ha1, hD, runBiasNum]
      have := bias_start_alg A B a b
      have := bias_Z1_eq A B a b
      have hDA : D = A := by omega
      have hP0 : P = 0 := by simp [P, hB1, hb_eq]
      grind
    · have ha_eq : a = 1 := by omega
      have hA1 : A = 1 := by simp [A, ha_eq]
      simp only [ha1, hb1, ↓reduceDIte, stepVal, hKO1 hb1, hPO1 hb1, runBiasNum]
      have := bias_start_alg A B a b
      have := bias_O1_eq A B a b
      have hDB : D = B := by omega
      have hQ0 : Q = 0 := by simp [Q, hA1, ha_eq]
      grind
    · have ha_eq : a = 1 := by omega
      have hb_eq : b = 1 := by omega
      simp [stepVal, runBiasNum, runD, ha_eq, hb_eq]
  · by_cases hqa : q.val < a
    · rw [runAut_step_false_Z a b ha hb q hq0 hqa,
          runAut_step_true_lt a b ha hb q hqa]
      let X : Int := (2 : Int) ^ (q.val - 1)
      have hqZ : runBiasPhi a b q = 2 * (A - X) * P + 2 * D * ((a : Int) - (q.val : Int)) * X := by
        simp [runBiasPhi, hq0, hqa, A, B, D, P, X]
      rw [hqZ]
      have hp : (2 : Int) ^ q.val = 2 * X := int_pow_pred_mul_two q.val (by omega)
      have halg := bias_chain_alg A D P ((a : Int) - (q.val : Int)) X
      by_cases hnext : q.val + 1 < a <;> by_cases hb1 : 1 < b
      · simp only [hnext, hb1, ↓reduceDIte, stepVal, hKO1 hb1, hPO1 hb1]
        have hnz : q.val + 1 ≠ 0 := by omega
        have hKn : runKraftScaled a b ⟨q.val + 1, by omega⟩ = D * (2 * (A - 2 * X)) := by
          simp only [runKraftScaled, runKraftKappa, hnz, hnext, ↓reduceIte, Nat.add_sub_cancel, hD, A, hp]
        have hPn : runBiasPhi a b ⟨q.val + 1, by omega⟩ =
            2 * (A - 2 * X) * P + 2 * D * (((a : Int) - (q.val : Int)) - 1) * (2 * X) := by
          have hr : (a : Int) - ((q.val + 1 : Nat) : Int) = ((a : Int) - (q.val : Int)) - 1 := by omega
          simp only [runBiasPhi, hnz, hnext, ↓reduceIte, Nat.add_sub_cancel, A, B, D, P, hp, hr]
        rw [hKn, hPn]; grind
      · have hb_eq : b = 1 := by omega
        have hB1 : B = 1 := by simp [B, hb_eq]
        have hP0 : P = 0 := by simp [P, hB1, hb_eq]
        have hDA : D = A := by omega
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hD]
        have hnz : q.val + 1 ≠ 0 := by omega
        have hKn : runKraftScaled a b ⟨q.val + 1, by omega⟩ = D * (2 * (A - 2 * X)) := by
          simp only [runKraftScaled, runKraftKappa, hnz, hnext, ↓reduceIte, Nat.add_sub_cancel, hD, A, hp]
        have hPn : runBiasPhi a b ⟨q.val + 1, by omega⟩ =
            2 * (A - 2 * X) * P + 2 * D * (((a : Int) - (q.val : Int)) - 1) * (2 * X) := by
          have hr : (a : Int) - ((q.val + 1 : Nat) : Int) = ((a : Int) - (q.val : Int)) - 1 := by omega
          simp only [runBiasPhi, hnz, hnext, ↓reduceIte, Nat.add_sub_cancel, A, B, D, P, hp, hr]
        rw [hKn, hPn]; grind
      · have hqeq : a - 1 = q.val := by omega
        have h2X : 2 * X = A := by simp only [A, hqeq, hp]
        have haq : (a : Int) - (q.val : Int) = 1 := by omega
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hKO1 hb1, hPO1 hb1]
        grind
      · have hqeq : a - 1 = q.val := by omega
        have hb_eq : b = 1 := by omega
        have hB1 : B = 1 := by simp [B, hb_eq]
        have hP0 : P = 0 := by simp [P, hB1, hb_eq]
        have hDA : D = A := by omega
        have h2X : 2 * X = A := by simp only [A, hqeq, hp]
        have haq : (a : Int) - (q.val : Int) = 1 := by omega
        simp only [hnext, hb1, ↓reduceDIte, stepVal, hD]
        grind
    · rw [runAut_step_false_SO a b ha hb q (Or.inr (by omega)),
          runAut_step_true_ge a b ha hb q (by omega)]
      let j : Nat := q.val - a + 1
      let X : Int := (2 : Int) ^ (q.val - a)
      have hjm : j - 1 = q.val - a := by omega
      have hqO : runBiasPhi a b q = 2 * (B - X) * Q + 2 * D * ((b : Int) - (j : Int)) * X := by
        simp [runBiasPhi, hq0, hqa, A, B, D, Q, j, X, hjm]
      rw [hqO]
      have hp : (2 : Int) ^ (q.val + 1 - a) = 2 * X := by
        have hs : q.val + 1 - a = (q.val - a) + 1 := by omega
        rw [hs, Int.pow_succ]; grind
      have halg := bias_ochain_alg A B D Q ((b : Int) - (j : Int)) X rfl
      by_cases ha1 : 1 < a <;> by_cases hnext : q.val + 1 < a + b - 1
      · simp only [ha1, hnext, ↓reduceDIte, stepVal, hKZ1 ha1, hPZ1 ha1]
        have hnz : q.val + 1 ≠ 0 := by omega
        have hna : ¬ (q.val + 1 < a) := by omega
        have hKn : runKraftScaled a b ⟨q.val + 1, hnext⟩ = D * (2 * (A + 2 * X - 1)) := by
          simp only [runKraftScaled, runKraftKappa, hnz, hna, ↓reduceIte, hD, A, hp]
        have hPn : runBiasPhi a b ⟨q.val + 1, hnext⟩ =
            2 * (B - 2 * X) * Q + 2 * D * (((b : Int) - (j : Int)) - 1) * (2 * X) := by
          have hj1 : q.val + 1 - a + 1 = j + 1 := by omega
          have hj1m : (j + 1) - 1 = q.val + 1 - a := by omega
          have hr : (b : Int) - ((j + 1 : Nat) : Int) = ((b : Int) - (j : Int)) - 1 := by omega
          simp only [runBiasPhi, hnz, hna, ↓reduceIte, A, B, D, Q, hj1, hj1m, hp, hr]
        rw [hKn, hPn]; grind
      · have hjeq : b - 1 = (q.val - a) + 1 := by omega
        have h2X : 2 * X = B := by simp only [B, hjeq, Int.pow_succ]; grind
        have hbj : (b : Int) - (j : Int) = 1 := by omega
        simp only [ha1, hnext, ↓reduceDIte, stepVal, hKZ1 ha1, hPZ1 ha1, hD]
        grind
      · have ha_eq : a = 1 := by omega
        have hA1 : A = 1 := by simp [A, ha_eq]
        have hQ0 : Q = 0 := by simp [Q, hA1, ha_eq]
        simp only [ha1, hnext, ↓reduceDIte, stepVal]
        have hnz : q.val + 1 ≠ 0 := by omega
        have hna : ¬ (q.val + 1 < a) := by omega
        have hKn : runKraftScaled a b ⟨q.val + 1, hnext⟩ = D * (2 * (A + 2 * X - 1)) := by
          simp only [runKraftScaled, runKraftKappa, hnz, hna, ↓reduceIte, hD, A, hp]
        have hPn : runBiasPhi a b ⟨q.val + 1, hnext⟩ =
            2 * (B - 2 * X) * Q + 2 * D * (((b : Int) - (j : Int)) - 1) * (2 * X) := by
          have hj1 : q.val + 1 - a + 1 = j + 1 := by omega
          have hj1m : (j + 1) - 1 = q.val + 1 - a := by omega
          have hr : (b : Int) - ((j + 1 : Nat) : Int) = ((b : Int) - (j : Int)) - 1 := by omega
          simp only [runBiasPhi, hnz, hna, ↓reduceIte, A, B, D, Q, hj1, hj1m, hp, hr]
        rw [hKn, hPn]; grind
      · have ha_eq : a = 1 := by omega
        have hA1 : A = 1 := by simp [A, ha_eq]
        have hQ0 : Q = 0 := by simp [Q, hA1, ha_eq]
        have hDB : D = B := by omega
        have hjeq : b - 1 = (q.val - a) + 1 := by omega
        have h2X : 2 * X = B := by simp only [B, hjeq, Int.pow_succ]; grind
        have hbj : (b : Int) - (j : Int) = 1 := by omega
        simp only [ha1, hnext, ↓reduceDIte, stepVal, hD]
        grind

/-- Theorem T3d (`(a, b)`-Run-Delimited Exact Symmetric Hamming-Bias Conservation, ∀ a, b ≥ 1, ∀ N). -/
theorem runAut_bias_conservation (a b : Nat) (ha : 0 < a) (hb : 0 < b) (N : Nat) :
    (2 * runD a b * runD a b) * costSum (runAut a b ha hb) 2 (fun _ _ => 1) biasCost N ⟨0, by omega⟩ +
      activeCostPot (runAut a b ha hb) (fun _ _ => 1) biasCost (runKraftScaled a b) (runBiasPhi a b) N ⟨0, by omega⟩ =
      (2 : Int) ^ N * runBiasNum a b := by
  have h := layer1_conservation (runAut a b ha hb) 2 (fun _ _ => 1) biasCost
    (2 * runD a b * runD a b) (runKraftScaled a b) (runBiasPhi a b)
    (runAut_kraftScaled_kirchhoff a b ha hb) (runAut_bias_kirchhoff a b ha hb) N ⟨0, by omega⟩
  simpa [runBiasPhi] using h

/-- Theorem T3e (Exact `(a, b) ↔ (b, a)` Symmetry of the Hamming-Bias Law). -/
theorem runAut_bias_symmetric (a b : Nat) :
    runBiasNum a b = runBiasNum b a ∧ runD a b = runD b a := by
  simp only [runBiasNum, runD]; grind

/-- Theorem T3f (Exact Diagonal Formula at `a = b = k`). -/
theorem runAut_bias_diag (k : Nat) (hk : 0 < k) :
    runBiasNum k k = ((2 : Int) ^ k - 1) * (((k : Int) - 1) * (2 : Int) ^ k + 1) := by
  simp only [runBiasNum]
  have h2A : (2 : Int) ^ k = 2 * (2 : Int) ^ (k - 1) := int_pow_pred_mul_two k hk
  rw [h2A]; grind

/-- Theorem T3g (Strict Positivity of Leaky Hamming Bias, ∀ a, b ≥ 1). -/
theorem runAut_bias_pos (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < runBiasNum a b := by
  simp only [runBiasNum]
  let A : Int := (2 : Int) ^ (a - 1)
  let B : Int := (2 : Int) ^ (b - 1)
  have hA : 1 ≤ A := int_two_pow_pos (a - 1)
  have hB : 1 ≤ B := int_two_pow_pos (b - 1)
  have hrew : 2 * A * B * ((a : Int) + (b : Int) - 2) - ((a : Int) - 2) * A - ((b : Int) - 2) * B - 1 =
      A * (2 * B - 1) * ((a : Int) - 1) + B * (2 * A - 1) * ((b : Int) - 1) + (A - 1) + (B - 1) + 1 := by
    grind
  change 0 < 2 * A * B * ((a : Int) + (b : Int) - 2) - ((a : Int) - 2) * A - ((b : Int) - 2) * B - 1
  rw [hrew]
  have h1 : 0 ≤ A * (2 * B - 1) * ((a : Int) - 1) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have h2 : 0 ≤ B * (2 * A - 1) * ((b : Int) - 1) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  omega

/-! ### Theorem T4: Order-Type ω Obstruction for ALL `k`-bonacci Codes (`∀ k ≥ 1`) -/

theorem fibAut_accepts_ones (k : Nat) (hk : 0 < k) :
    Accepts (fibAut k hk) ⟨0, hk⟩ (List.replicate k true) := by
  have hgen : ∀ (m : Nat) (q : Fin k), q.val + m = k → 0 < m →
      Accepts (fibAut k hk) q (List.replicate m true) := by
    intro m
    induction m with
    | zero => intro _ _ hpos; omega
    | succ m ih =>
      intro q hsum _
      have := q.isLt
      cases m with
      | zero =>
        simp only [List.replicate_succ, List.replicate_zero]
        apply Accepts.emit
        simp only [fibAut]
        have hnot : ¬ (q.val + 1 < k) := by omega
        simp [hnot]
      | succ m' =>
        simp only [List.replicate_succ]
        have hlt : q.val + 1 < k := by omega
        have hstep : (fibAut k hk).step q true = Step.cont ⟨q.val + 1, hlt⟩ := by
          simp [fibAut, hlt]
        exact Accepts.cont hstep (ih ⟨q.val + 1, hlt⟩ (by dsimp only; omega) (Nat.succ_pos m'))
  exact hgen k ⟨0, hk⟩ (by dsimp only; omega) hk

/-- Theorem T4 (`fibAut_no_order_preserving_bijection`, ∀ k ≥ 1). -/
theorem fibAut_no_order_preserving_bijection (k : Nat) (hk : 0 < k) :
    ∀ e : Nat → List Bool,
      (∀ i j, i < j → lexLt (e i) (e j)) →
      (∀ w, Accepts (fibAut k hk) ⟨0, hk⟩ w → ∃ i, e i = w) → False := by
  cases k with
  | zero => omega
  | succ k' =>
    have hacc : Accepts (fibAut (k' + 1) hk) ⟨0, hk⟩ (true :: List.replicate k' true) :=
      fibAut_accepts_ones (k' + 1) hk
    have hobs := order_type_omega_obstruction (fibAut (k' + 1) hk) ⟨0, hk⟩ [] []
      (List.replicate k' true) rfl (by simp [runActive, fibAut]) hacc
    exact hobs.2.2


/-! ==========================================================================
    SECTION 4: MECHANISM II — Compositional Order-Preserving Elias-Lift Engine
    ========================================================================== -/

theorem toBitsMSB_lexDiverge (w : Nat) :
    ∀ x y : Nat, x < y → y < 2 ^ w → lexDiverge (toBitsMSB w x) (toBitsMSB w y) := by
  induction w with
  | zero => intro x y hxy hy; omega
  | succ w ih =>
    intro x y hxy hy
    simp only [toBitsMSB]
    have hdy : y / 2 < 2 ^ w := by rw [Nat.pow_succ] at hy; omega
    cases Nat.lt_or_ge (x / 2) (y / 2) with
    | inl hlt => exact lexDiverge_append_right _ _ (ih (x / 2) (y / 2) hlt hdy)
    | inr hge =>
      have heq : x / 2 = y / 2 := by omega
      have hx0 : x % 2 = 0 := by omega
      have hy1 : y % 2 = 1 := by omega
      rw [heq]
      apply lexDiverge_append_left
      simp only [hx0, hy1]
      exact lexDiverge.head [] []

theorem floorLog2_unique {m L : Nat} (hlo : 2 ^ L ≤ m) (hhi : m < 2 ^ (L + 1)) :
    floorLog2 m = L := by
  have hm : 1 ≤ m := Nat.le_trans (Nat.pow_pos (by omega)) hlo
  have ⟨h1, h2⟩ := floorLog2_spec m hm
  cases Nat.lt_trichotomy (floorLog2 m) L with
  | inl hlt =>
    have : 2 ^ (floorLog2 m + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  | inr h =>
    cases h with
    | inl heq => exact heq
    | inr hgt =>
      have : 2 ^ (L + 1) ≤ 2 ^ floorLog2 m := Nat.pow_le_pow_right (by omega) (by omega)
      omega

theorem floorLog2_mono {m n : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) :
    floorLog2 m ≤ floorLog2 n := by
  have ⟨h1, _⟩ := floorLog2_spec m hm
  have ⟨_, h2⟩ := floorLog2_spec n (Nat.le_trans hm hmn)
  by_cases hle : floorLog2 m ≤ floorLog2 n
  · exact hle
  · have hp : 2 ^ (floorLog2 n + 1) ≤ 2 ^ floorLog2 m := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- Theorem M2.1 (Universal Stream Unique Decodability for ANY `PrefixCode`). -/
theorem PrefixCode.decStream_encStream (C : PrefixCode) (ns : List Nat) :
    C.decStream (C.encStream ns) = some ns := by
  induction ns with
  | nil => simp [PrefixCode.encStream, PrefixCode.decStream]
  | cons n ns ih =>
    have hne := C.nonempty n
    cases he : C.enc n with
    | nil => exact absurd he hne
    | cons b bs =>
      have hrt : C.decOne (b :: (bs ++ C.encStream ns)) = some (n, C.encStream ns) := by
        have h := C.roundtrip n (C.encStream ns)
        simpa [he] using h
      have hlen : (C.encStream ns).length < (b :: (bs ++ C.encStream ns)).length := by
        simp; omega
      have henc : C.encStream (n :: ns) = b :: (bs ++ C.encStream ns) := by
        simp [PrefixCode.encStream, he]
      rw [henc]
      unfold PrefixCode.decStream
      rw [hrt]
      simp only [hlen, ↓reduceDIte]
      rw [ih]

theorem unary1Code_orderPreserving : unary1Code.OrderPreserving := by
  intro m n hmn
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => omega
    | succ n' =>
      simp only [unary1Code, List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append]
      exact lexDiverge.head [] _
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n' =>
      simp only [unary1Code, List.replicate_succ, List.cons_append]
      exact lexDiverge.cons true (ih n' (by omega))

/-- Theorem M2.3 (Order-Preservation Lifting under `eliasLift`). -/
theorem eliasLift_orderPreserving (C : PrefixCode) (hC : C.OrderPreserving) :
    (eliasLift C).OrderPreserving := by
  intro m n hmn
  simp only [eliasLift]
  have hle : floorLog2 (m + 1) ≤ floorLog2 (n + 1) := floorLog2_mono (by omega) (by omega)
  cases Nat.eq_or_lt_of_le hle with
  | inl heq =>
    rw [heq]
    apply lexDiverge_append_left
    have ⟨hlo_m, _⟩ := floorLog2_spec (m + 1) (by omega)
    have ⟨hlo_n, hhi_n⟩ := floorLog2_spec (n + 1) (by omega)
    rw [heq] at hlo_m
    have h1 : (m + 1) - 2 ^ floorLog2 (n + 1) < (n + 1) - 2 ^ floorLog2 (n + 1) := by omega
    have h2 : (n + 1) - 2 ^ floorLog2 (n + 1) < 2 ^ floorLog2 (n + 1) := by
      have hp : 2 ^ (floorLog2 (n + 1) + 1) = 2 ^ floorLog2 (n + 1) * 2 := Nat.pow_succ 2 _
      omega
    exact toBitsMSB_lexDiverge (floorLog2 (n + 1)) _ _ h1 h2
  | inr hlt =>
    exact lexDiverge_append_right _ _ (hC (floorLog2 (m + 1)) (floorLog2 (n + 1)) hlt)

/-! ### Exact Finite-Block Sums for `PrefixCode` (Kraft, Popcount-Parity, Length-Sum) -/

theorem sumRangeNat_add (f : Nat → Nat) (a b : Nat) :
    sumRangeNat f (a + b) = sumRangeNat f a + sumRangeNat (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [sumRangeNat]
  | succ b ih => rw [Nat.add_succ, sumRangeNat, sumRangeNat, ih, Nat.add_assoc]

theorem sumRangeInt_add (f : Nat → Int) (a b : Nat) :
    sumRangeInt f (a + b) = sumRangeInt f a + sumRangeInt (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [sumRangeInt]
  | succ b ih => rw [Nat.add_succ, sumRangeInt, sumRangeInt, ih, Int.add_assoc]

theorem sumRangeNat_const (c N : Nat) : sumRangeNat (fun _ => c) N = N * c := by
  induction N with
  | zero => simp [sumRangeNat]
  | succ N ih => simp [sumRangeNat, ih, Nat.succ_mul]

theorem sumRangeNat_congr {f g : Nat → Nat} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    sumRangeNat f N = sumRangeNat g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [sumRangeNat]
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

theorem sumRangeInt_congr {f g : Nat → Int} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    sumRangeInt f N = sumRangeInt g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [sumRangeInt]
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

theorem sumRangeNat_le {f g : Nat → Nat} {N : Nat} (h : ∀ i, i < N → f i ≤ g i) :
    sumRangeNat f N ≤ sumRangeNat g N := by
  induction N with
  | zero => exact Nat.le_refl 0
  | succ N ih =>
    simp only [sumRangeNat]
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))

theorem eliasLift_enc_in_block (C : PrefixCode) (L r : Nat) (hr : r < 2 ^ L) :
    (eliasLift C).enc ((2 ^ L - 1) + r) = C.enc L ++ toBitsMSB L r := by
  have hpos : 1 ≤ 2 ^ L := Nat.pow_pos (by omega)
  have heq : ((2 ^ L - 1) + r) + 1 = 2 ^ L + r := by omega
  have hlog : floorLog2 (((2 ^ L - 1) + r) + 1) = L := by
    rw [heq]
    apply floorLog2_unique (by omega)
    rw [Nat.pow_succ]; omega
  simp only [eliasLift]
  rw [hlog, heq, Nat.add_sub_cancel_left]

/-- Theorem M2.4 (Exact Finite-Block Kraft Conservation Lifting under `eliasLift`, ∀ M : Nat). -/
theorem eliasLift_kraft_block (C : PrefixCode) (H M : Nat)
    (hH : ∀ L, L < M → (C.enc L).length + L ≤ H) :
    kraftBlock (eliasLift C) H (2 ^ M - 1) = kraftBlock C H M := by
  induction M with
  | zero => simp [kraftBlock, sumRangeNat]
  | succ M ih =>
    have hsplit : 2 ^ (M + 1) - 1 = (2 ^ M - 1) + 2 ^ M := by
      have hpos : 1 ≤ 2 ^ M := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]; omega
    simp only [kraftBlock]
    rw [hsplit, sumRangeNat_add, sumRangeNat]
    have ih' := ih (fun L hL => hH L (by omega))
    simp only [kraftBlock] at ih'
    rw [ih']
    congr 1
    have hconst : sumRangeNat (fun i => 2 ^ (H - ((eliasLift C).enc ((2 ^ M - 1) + i)).length)) (2 ^ M) =
        sumRangeNat (fun _ => 2 ^ (H - ((C.enc M).length + M))) (2 ^ M) := by
      apply sumRangeNat_congr
      intro i hi
      rw [eliasLift_enc_in_block C M i hi, List.length_append, toBitsMSB_length]
    rw [hconst, sumRangeNat_const]
    have hle := hH M (by omega)
    rw [← Nat.pow_add]
    congr 1; omega

theorem sum_popParity_toBitsMSB_zero (L : Nat) (hL : 1 ≤ L) :
    sumRangeInt (fun r => negOnePow (popcount (toBitsMSB L r))) (2 ^ L) = 0 := by
  cases L with
  | zero => omega
  | succ L' =>
    have hsplit : 2 ^ (L' + 1) = 2 ^ L' * 2 := Nat.pow_succ _ _
    have hpair : ∀ K : Nat,
        sumRangeInt (fun r => negOnePow (popcount (toBitsMSB (L' + 1) r))) (2 * K) = 0 := by
      intro K
      induction K with
      | zero => rfl
      | succ K ih =>
        have hstep : 2 * (K + 1) = 2 * K + 1 + 1 := by omega
        rw [hstep, sumRangeInt, sumRangeInt, ih, Int.zero_add]
        simp only [toBitsMSB]
        have hdiv0 : (2 * K) / 2 = K := by omega
        have hmod0 : (2 * K) % 2 = 0 := by omega
        have hdiv1 : (2 * K + 1) / 2 = K := by omega
        have hmod1 : (2 * K + 1) % 2 = 1 := by omega
        have hb0 : ((0 : Nat) == 1) = false := rfl
        have hb1 : ((1 : Nat) == 1) = true := rfl
        rw [hdiv0, hmod0, hdiv1, hmod1, hb0, hb1]
        simp only [popcount_append, popcount, Nat.add_zero, negOnePow_add, negOnePow]
        grind
    rw [hsplit, Nat.mul_comm]
    exact hpair (2 ^ L')

/-- Theorem M2.5 (Exact Popcount-Parity Collapse Law under `eliasLift`, ∀ M ≥ 1). -/
theorem eliasLift_popParity_collapse (C : PrefixCode) (H M : Nat) (hM : 1 ≤ M) :
    popParityBlock (eliasLift C) H (2 ^ M - 1) =
      negOnePow (popcount (C.enc 0)) * ((2 ^ (H - (C.enc 0).length) : Nat) : Int) := by
  induction M with
  | zero => omega
  | succ M ih =>
    cases M with
    | zero =>
      simp only [popParityBlock]
      have h1 : 2 ^ 1 - 1 = 1 := rfl
      rw [h1, sumRangeInt, sumRangeInt, Int.zero_add]
      have h0 := eliasLift_enc_in_block C 0 0 (by decide)
      simp only [Nat.pow_zero, Nat.sub_self, Nat.zero_add, toBitsMSB, List.append_nil] at h0
      rw [h0]
    | succ M' =>
      have hsplit : 2 ^ (M' + 2) - 1 = (2 ^ (M' + 1) - 1) + 2 ^ (M' + 1) := by
        have hpos : 1 ≤ 2 ^ (M' + 1) := Nat.pow_pos (by omega)
        rw [Nat.pow_succ]; omega
      simp only [popParityBlock]
      rw [hsplit, sumRangeInt_add]
      have ih' := ih (by omega)
      simp only [popParityBlock] at ih'
      rw [ih']
      let fac : Int := negOnePow (popcount (C.enc (M' + 1))) *
          ((2 ^ (H - ((C.enc (M' + 1)).length + (M' + 1))) : Nat) : Int)
      have hblock_zero :
          sumRangeInt (fun i =>
            negOnePow (popcount ((eliasLift C).enc ((2 ^ (M' + 1) - 1) + i))) *
            ((2 ^ (H - ((eliasLift C).enc ((2 ^ (M' + 1) - 1) + i)).length) : Nat) : Int))
            (2 ^ (M' + 1)) = 0 := by
        have hcongr :
            sumRangeInt (fun i =>
              negOnePow (popcount ((eliasLift C).enc ((2 ^ (M' + 1) - 1) + i))) *
              ((2 ^ (H - ((eliasLift C).enc ((2 ^ (M' + 1) - 1) + i)).length) : Nat) : Int))
              (2 ^ (M' + 1)) =
            sumRangeInt (fun i => fac * negOnePow (popcount (toBitsMSB (M' + 1) i))) (2 ^ (M' + 1)) := by
          apply sumRangeInt_congr
          intro i hi
          rw [eliasLift_enc_in_block C (M' + 1) i hi, popcount_append, List.length_append,
              toBitsMSB_length, negOnePow_add]
          dsimp only [fac]; grind
        rw [hcongr]
        have hpull : ∀ N (f : Nat → Int), sumRangeInt (fun i => fac * f i) N = fac * sumRangeInt f N := by
          intro N f
          induction N with
          | zero => simp [sumRangeInt]
          | succ N ihN => simp [sumRangeInt, ihN, Int.mul_add]
        rw [hpull, sum_popParity_toBitsMSB_zero (M' + 1) (by omega), Int.mul_zero]
      rw [hblock_zero, Int.add_zero]

/-- Theorem M2.6 (Exact Unweighted Bitwise Length-Sum Lifting Law under `eliasLift`, ∀ M : Nat). -/
theorem eliasLift_length_sum (C : PrefixCode) (M : Nat) :
    lenBlock (eliasLift C) (2 ^ M - 1) + 2 ^ (M + 1) =
      sumRangeNat (fun L => 2 ^ L * (C.enc L).length) M + M * 2 ^ M + 2 := by
  induction M with
  | zero => simp [lenBlock, sumRangeNat]
  | succ M ih =>
    have hsplit : 2 ^ (M + 1) - 1 = (2 ^ M - 1) + 2 ^ M := by
      have hpos : 1 ≤ 2 ^ M := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]; omega
    simp only [lenBlock]
    rw [hsplit, sumRangeNat_add, sumRangeNat]
    have hconst : sumRangeNat (fun i => ((eliasLift C).enc ((2 ^ M - 1) + i)).length) (2 ^ M) =
        2 ^ M * ((C.enc M).length + M) := by
      have hc := sumRangeNat_congr (N := 2 ^ M)
        (f := fun i => ((eliasLift C).enc ((2 ^ M - 1) + i)).length)
        (g := fun _ => (C.enc M).length + M)
        (fun i hi => by rw [eliasLift_enc_in_block C M i hi, List.length_append, toBitsMSB_length])
      rw [hc, sumRangeNat_const]
    rw [hconst]
    simp only [lenBlock] at ih
    have hp1 : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [Nat.pow_succ, Nat.mul_comm]
    have hp2 : 2 ^ (M + 2) = 4 * 2 ^ M := by rw [Nat.pow_succ, hp1]; omega
    rw [hp1] at ih
    rw [hp2]
    grind


/-! ==========================================================================
    SECTION 5: THEOREM T5 — Iterated Order-Preserving Elias-Lift Tower `E^r(Unary1)`
    ========================================================================== -/

theorem eliasTower_enc_len_le (r : Nat) :
    ∀ M n, n < towerBound r M → ((eliasTower r).enc n).length ≤ towerMaxLen r M := by
  induction r with
  | zero =>
    intro M n hn
    simp only [eliasTower, unary1Code, towerBound, towerMaxLen, List.length_append,
               List.length_replicate, List.length_singleton] at hn ⊢
    omega
  | succ r ih =>
    intro M n hn
    simp only [eliasTower, eliasLift, towerBound, towerMaxLen, List.length_append,
               toBitsMSB_length] at hn ⊢
    have hL : floorLog2 (n + 1) < towerBound r M := by
      have ⟨hlo, _⟩ := floorLog2_spec (n + 1) (by omega)
      cases Nat.lt_or_ge (floorLog2 (n + 1)) (towerBound r M) with
      | inl h => exact h
      | inr hge =>
        have hp : 2 ^ towerBound r M ≤ 2 ^ floorLog2 (n + 1) := Nat.pow_le_pow_right (by omega) hge
        omega
    have h1 := ih M (floorLog2 (n + 1)) hL
    omega

/-- Theorem T5a (`eliasTower` Infinite-Length Unique Stream Decodability, ∀ r : Nat). -/
theorem eliasTower_unique_decodable (r : Nat) (ns : List Nat) :
    (eliasTower r).decStream ((eliasTower r).encStream ns) = some ns :=
  (eliasTower r).decStream_encStream ns

/-- Theorem T5b (`eliasTower` Strict Lexicographic Order Preservation, ∀ r : Nat). -/
theorem eliasTower_orderPreserving (r : Nat) : (eliasTower r).OrderPreserving := by
  induction r with
  | zero => exact unary1Code_orderPreserving
  | succ r ih => exact eliasLift_orderPreserving (eliasTower r) ih

theorem eliasTower_lexLt (r m n : Nat) (hmn : m < n) :
    lexLt ((eliasTower r).enc m) ((eliasTower r).enc n) :=
  lexDiverge_imp_lexLt (eliasTower_orderPreserving r m n hmn)

theorem unary1_kraft_block (H M : Nat) (hM : M ≤ H) :
    kraftBlock unary1Code H M = 2 ^ H - 2 ^ (H - M) := by
  induction M with
  | zero => simp [kraftBlock, sumRangeNat]
  | succ M ih =>
    have hstep : 2 ^ (H - M) = 2 ^ (H - (M + 1)) + 2 ^ (H - (M + 1)) := by
      have hs : H - M = (H - (M + 1)) + 1 := by omega
      rw [hs, Nat.pow_succ]; omega
    have hle : 2 ^ (H - M) ≤ 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
    have hlen : (unary1Code.enc M).length = M + 1 := by simp [unary1Code]
    have hrec : kraftBlock unary1Code H (M + 1) =
        kraftBlock unary1Code H M + 2 ^ (H - (unary1Code.enc M).length) := rfl
    rw [hrec, ih (by omega), hlen]
    rw [hstep] at hle ⊢
    have haux : ∀ x y : Nat, y + y ≤ x → x - (y + y) + y = x - y := by intro x y h; omega
    exact haux (2 ^ H) (2 ^ (H - (M + 1))) hle

/-- Theorem T5c (`eliasTower` Exact Finite-Block Kraft Conservation = `1 - 2^(-M)`, ∀ r M : Nat). -/
theorem eliasTower_kraft_block (r M H : Nat) (hM : M ≤ H) (hH : towerMaxLen r M ≤ H) :
    kraftBlock (eliasTower r) H (towerBound r M) = 2 ^ H - 2 ^ (H - M) := by
  induction r with
  | zero => exact unary1_kraft_block H M hM
  | succ r ih =>
    simp only [eliasTower, towerBound]
    have hstep : ∀ L, L < towerBound r M → ((eliasTower r).enc L).length + L ≤ H := by
      intro L hL
      have hlen := eliasTower_enc_len_le r M L hL
      simp only [towerMaxLen] at hH
      omega
    rw [eliasLift_kraft_block (eliasTower r) H (towerBound r M) hstep]
    simp only [towerMaxLen] at hH
    exact ih (by omega)

theorem eliasTower_enc_zero (r : Nat) : (eliasTower r).enc 0 = [false] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h0 := eliasLift_enc_in_block (eliasTower r) 0 0 (by decide)
    simp only [Nat.pow_zero, Nat.sub_self, Nat.zero_add, toBitsMSB, List.append_nil] at h0
    change (eliasLift (eliasTower r)).enc 0 = [false]
    rw [h0, ih]

/-- Theorem T5d (`eliasTower` Exact Popcount-Parity Collapse = `+1/2`, ∀ r ≥ 1, M ≥ 1). -/
theorem eliasTower_popParity_collapse (r M H : Nat) (hr : 1 ≤ r) (hM : 1 ≤ M) :
    popParityBlock (eliasTower r) H (towerBound r M) = ((2 ^ (H - 1) : Nat) : Int) := by
  cases r with
  | zero => omega
  | succ r' =>
    have htb_pos : ∀ k X, 1 ≤ X → 1 ≤ towerBound k X := by
      intro k
      induction k with
      | zero => intro X hX; exact hX
      | succ k ihk =>
        intro X hX
        simp only [towerBound]
        have h1 := ihk X hX
        have h2 : 2 ^ 1 ≤ 2 ^ towerBound k X := Nat.pow_le_pow_right (by omega) h1
        omega
    simp only [eliasTower, towerBound]
    rw [eliasLift_popParity_collapse (eliasTower r') H (towerBound r' M) (htb_pos r' M hM)]
    rw [eliasTower_enc_zero r']
    simp [popcount, negOnePow]

/-- Theorem T5e (Order-Preserving Elias-Gamma Exact Bitwise Length-Sum Law, ∀ M : Nat). -/
theorem eliasGamma_exact_length_sum (M : Nat) :
    lenBlock (eliasTower 1) (2 ^ M - 1) + 3 * 2 ^ M = 2 * M * 2 ^ M + 3 := by
  have haux : sumRangeNat (fun L => 2 ^ L * (unary1Code.enc L).length) M + 2 ^ M = M * 2 ^ M + 1 := by
    have hlen : (fun L => 2 ^ L * (unary1Code.enc L).length) = (fun L => 2 ^ L * (L + 1)) := by
      funext L
      simp [unary1Code]
    rw [hlen]
    induction M with
    | zero => simp [sumRangeNat]
    | succ M ih =>
      rw [sumRangeNat]
      have hp : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp]; grind
  have hlift := eliasLift_length_sum unary1Code M
  have hp : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [Nat.pow_succ, Nat.mul_comm]
  change lenBlock (eliasLift unary1Code) (2 ^ M - 1) + 3 * 2 ^ M = 2 * M * 2 ^ M + 3
  rw [hp] at hlift
  grind

/-- Theorem T5f (Sharpness Phase Transition Part 1: Elias-Gamma `r = 1` Expected Length `≤ 3`, ∀ M). -/
theorem eliasGamma_expLen_exact (M H : Nat) (hH : 2 * M ≤ H) :
    expLenBlock (eliasTower 1) H (2 ^ M - 1) + (2 * M + 3) * 2 ^ (H - M) = 3 * 2 ^ H := by
  induction M with
  | zero => simp [expLenBlock, sumRangeNat]
  | succ M ih =>
    have hsplit : 2 ^ (M + 1) - 1 = (2 ^ M - 1) + 2 ^ M := by
      have hpos : 1 ≤ 2 ^ M := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]; omega
    simp only [expLenBlock]
    rw [hsplit, sumRangeNat_add]
    have hblk : sumRangeNat (fun i =>
        ((eliasTower 1).enc ((2 ^ M - 1) + i)).length *
        2 ^ (H - ((eliasTower 1).enc ((2 ^ M - 1) + i)).length)) (2 ^ M) =
        (2 * M + 1) * 2 ^ (H - (M + 1)) := by
      have hc : sumRangeNat (fun i =>
          ((eliasTower 1).enc ((2 ^ M - 1) + i)).length *
          2 ^ (H - ((eliasTower 1).enc ((2 ^ M - 1) + i)).length)) (2 ^ M) =
          sumRangeNat (fun _ => (2 * M + 1) * 2 ^ (H - (2 * M + 1))) (2 ^ M) := by
        apply sumRangeNat_congr
        intro i hi
        change ((eliasLift unary1Code).enc ((2 ^ M - 1) + i)).length *
            2 ^ (H - ((eliasLift unary1Code).enc ((2 ^ M - 1) + i)).length) = _
        rw [eliasLift_enc_in_block unary1Code M i hi, List.length_append, toBitsMSB_length]
        simp only [unary1Code, List.length_append, List.length_replicate, List.length_singleton]
        have h2M : M + 1 + M = 2 * M + 1 := by omega
        rw [h2M]
      rw [hc, sumRangeNat_const, ← Nat.mul_assoc, Nat.mul_comm (2 ^ M) (2 * M + 1),
          Nat.mul_assoc, ← Nat.pow_add]
      congr 2; omega
    rw [hblk]
    have ih' := ih (by omega)
    simp only [expLenBlock] at ih'
    have hstep : 2 ^ (H - M) = 2 * 2 ^ (H - (M + 1)) := by
      have hs : H - M = (H - (M + 1)) + 1 := by omega
      rw [hs, Nat.pow_succ, Nat.mul_comm]
    rw [hstep] at ih'
    grind

theorem eliasGamma_expLen_le_three (M H : Nat) (hH : 2 * M ≤ H) :
    expLenBlock (eliasTower 1) H (2 ^ M - 1) ≤ 3 * 2 ^ H := by
  have h := eliasGamma_expLen_exact M H hH
  omega

/-- Theorem T5g (Sharpness Phase Transition Part 2: Elias-Delta `r = 2` Expected Length DIVERGES `≥ M / 2`). -/
theorem eliasDelta_expLen_diverges (M H : Nat) (hH : towerMaxLen 2 M ≤ H) :
    M * 2 ^ (H - 1) ≤ expLenBlock (eliasTower 2) H (towerBound 2 M) := by
  have hlift_exp : ∀ (C : PrefixCode) (K : Nat),
      (∀ L, L < K → (C.enc L).length + L ≤ H) →
      expLenBlock (eliasLift C) H (2 ^ K - 1) =
        sumRangeNat (fun L => ((C.enc L).length + L) * 2 ^ (H - (C.enc L).length)) K := by
    intro C K hHK
    induction K with
    | zero => simp [expLenBlock, sumRangeNat]
    | succ K ihK =>
      have hsplit : 2 ^ (K + 1) - 1 = (2 ^ K - 1) + 2 ^ K := by
        have hpos : 1 ≤ 2 ^ K := Nat.pow_pos (by omega)
        rw [Nat.pow_succ]; omega
      simp only [expLenBlock]
      rw [hsplit, sumRangeNat_add, sumRangeNat]
      have ih' := ihK (fun L hL => hHK L (by omega))
      simp only [expLenBlock] at ih'
      rw [ih']
      congr 1
      have hc : sumRangeNat (fun i =>
          ((eliasLift C).enc ((2 ^ K - 1) + i)).length *
          2 ^ (H - ((eliasLift C).enc ((2 ^ K - 1) + i)).length)) (2 ^ K) =
          sumRangeNat (fun _ => ((C.enc K).length + K) * 2 ^ (H - ((C.enc K).length + K))) (2 ^ K) := by
        apply sumRangeNat_congr
        intro i hi
        rw [eliasLift_enc_in_block C K i hi, List.length_append, toBitsMSB_length]
      rw [hc, sumRangeNat_const, ← Nat.mul_assoc, Nat.mul_comm (2 ^ K), Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      have := hHK K (by omega)
      omega
  have hH_step : ∀ L, L < 2 ^ M - 1 → ((eliasTower 1).enc L).length + L ≤ H := by
    intro L hL
    have hlen := eliasTower_enc_len_le 1 M L hL
    simp only [towerMaxLen, towerBound] at hH hlen
    omega
  change M * 2 ^ (H - 1) ≤ expLenBlock (eliasLift (eliasTower 1)) H (2 ^ (2 ^ M - 1) - 1)
  rw [hlift_exp (eliasTower 1) (2 ^ M - 1) hH_step]
  have hH_ge : 2 * M + 1 ≤ H := by
    simp only [towerMaxLen, towerBound] at hH
    omega
  clear hH hH_step
  induction M with
  | zero => simp [sumRangeNat]
  | succ M ih =>
    have hsplit : 2 ^ (M + 1) - 1 = (2 ^ M - 1) + 2 ^ M := by
      have hpos : 1 ≤ 2 ^ M := Nat.pow_pos (by omega)
      rw [Nat.pow_succ]; omega
    rw [hsplit, sumRangeNat_add]
    have h1 := ih (by omega)
    have hblk : 2 ^ (H - 1) ≤
        sumRangeNat (fun i =>
          (((eliasTower 1).enc ((2 ^ M - 1) + i)).length + ((2 ^ M - 1) + i)) *
          2 ^ (H - ((eliasTower 1).enc ((2 ^ M - 1) + i)).length)) (2 ^ M) := by
      have hlow : sumRangeNat (fun _ => 2 ^ M * 2 ^ (H - (2 * M + 1))) (2 ^ M) ≤
          sumRangeNat (fun i =>
            (((eliasTower 1).enc ((2 ^ M - 1) + i)).length + ((2 ^ M - 1) + i)) *
            2 ^ (H - ((eliasTower 1).enc ((2 ^ M - 1) + i)).length)) (2 ^ M) := by
        apply sumRangeNat_le
        intro i hi
        change 2 ^ M * 2 ^ (H - (2 * M + 1)) ≤
          (((eliasLift unary1Code).enc ((2 ^ M - 1) + i)).length + ((2 ^ M - 1) + i)) *
          2 ^ (H - ((eliasLift unary1Code).enc ((2 ^ M - 1) + i)).length)
        rw [eliasLift_enc_in_block unary1Code M i hi, List.length_append, toBitsMSB_length]
        simp only [unary1Code, List.length_append, List.length_replicate, List.length_singleton]
        have h2M : M + 1 + M = 2 * M + 1 := by omega
        rw [h2M]
        have hge : 2 ^ M ≤ (2 * M + 1) + ((2 ^ M - 1) + i) := by
          have : 1 ≤ 2 ^ M := Nat.pow_pos (by omega)
          omega
        exact Nat.mul_le_mul_right _ hge
      rw [sumRangeNat_const, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add] at hlow
      have hexp : M + M + (H - (2 * M + 1)) = H - 1 := by omega
      rw [hexp] at hlow
      exact hlow
    have hstep : (M + 1) * 2 ^ (H - 1) = M * 2 ^ (H - 1) + 2 ^ (H - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hstep]
    exact Nat.add_le_add h1 hblk


/-! ==========================================================================
    SECTION 6: KERNEL-CHECKED NON-VACUITY WITNESSES & SHARPNESS COUNTEREXAMPLES
    ========================================================================== -/

/-- Non-Vacuity Witness 1: Fibonacci code (`fibAut 2`) accepts non-trivial stream `["11", "011", "1011"]`
    and decodes it uniquely. -/
example : Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [true, true] ∧
          Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [false, true, true] ∧
          Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [true, false, true, true] ∧
          decodeStream (fibAut 2 (by decide))
            ([[true, true], [false, true, true], [true, false, true, true]].flatten) =
            some [[true, true], [false, true, true], [true, false, true, true]] := by
  have h1 : Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [true, true] :=
    Accepts.cont (q' := ⟨1, by decide⟩) (by decide) (Accepts.emit (by decide))
  have h2 : Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [false, true, true] :=
    Accepts.cont (q' := ⟨0, by decide⟩) (by decide) h1
  have h3 : Accepts (fibAut 2 (by decide)) ⟨0, by decide⟩ [true, false, true, true] :=
    Accepts.cont (q' := ⟨1, by decide⟩) (by decide)
      (Accepts.cont (q' := ⟨0, by decide⟩) (by decide) h1)
  refine ⟨h1, h2, h3, ?_⟩
  apply fibAut_unique_decodable 2 (by decide)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- Non-Vacuity Witness 2: `(2, 3)`-Run-Delimited code (`runAut 2 3`) exact Kraft `3/10`,
    Popcount-Parity `-1/6`, and Symmetric Bias `43/50`. -/
example :
    runD 2 3 = 5 ∧
    2 * runD 2 3 = 10 ∧
    (2 * (2 : Int) ^ (2 - 1) - 1) = 3 ∧
    runPopD 2 3 = 18 ∧
    negOnePow 3 * (2 * (2 : Int) ^ (2 - 1) - 1) = -3 ∧
    runBiasNum 2 3 = 43 ∧
    runBiasNum 3 2 = 43 := by
  decide

/-- Non-Vacuity Witness 3: Concrete instantiations of `eliasTower 1..2` (`γ~`, `δ~`). -/
example :
    (eliasTower 1).enc 0 = [false] ∧
    (eliasTower 1).enc 1 = [true, false, false] ∧
    (eliasTower 1).enc 2 = [true, false, true] ∧
    (eliasTower 1).enc 3 = [true, true, false, false, false] ∧
    (eliasTower 2).enc 3 = [true, false, true, false, false] := by
  decide

/-- Sharpness Counterexample 1 (Kirchhoff Perturbation Failure). -/
theorem sharpness_kirchhoff_perturbation :
    let A := fibAut 2 (by decide)
    let badKappa : Fin 2 → Int := fun q => if q.val = 0 then 2 else 1
    ¬ IsKirchhoff0 A 2 (fun _ _ => 1) 1 badKappa ∧
    charSum A 2 (fun _ _ => 1) 1 ⟨0, by decide⟩ +
      activePot A (fun _ _ => 1) badKappa 1 ⟨0, by decide⟩ ≠
      (2 : Int) ^ 1 * badKappa ⟨0, by decide⟩ := by
  constructor
  · intro h
    have h0 := h ⟨0, by decide⟩
    simp [fibAut, stepVal] at h0
  · decide

/-- Sharpness Counterexample 2 (Non-Prefix Code Ambiguity). -/
theorem sharpness_nonprefix_ambiguity :
    let ws1 : List (List Bool) := [[true], [false, true]]
    let ws2 : List (List Bool) := [[true, false], [true]]
    ws1 ≠ ws2 ∧ ws1.flatten = ws2.flatten := by
  decide

/-- Sharpness Counterexample 3 (Concrete Order-Type ω Failure Witness for `fibAut 2`). -/
theorem sharpness_fib_descending_witness :
    lexLt [false, true, true] [true, true] ∧
    lexLt [false, false, true, true] [false, true, true] := by
  exact ⟨lexLt.false_true _ _, lexLt.cons_same false (lexLt.false_true _ _)⟩

end PrefixCodeEngine
