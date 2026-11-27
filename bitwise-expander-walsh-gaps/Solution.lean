import BitwiseExpanderWalshGaps

namespace BitwiseExpanderWalshGapsChallenge

open WalshAutomatonEngine

theorem wht_plancherel {k : Nat} (f g : BitVec k → Int) :
    bvSum (fun ξ => wht f ξ * wht g ξ) =
    ((2 ^ k : Nat) : Int) * bvSum (fun x => f x * g x) :=
  _root_.WalshAutomatonEngine.wht_plancherel f g

theorem dirichletForm_eq_wht {k : Nat} (P : BitVec k → Bool) (f : BitVec k → Int) :
    ((2 ^ k : Nat) : Int) * dirichletForm P f =
    bvSum (fun ξ => if ξ = 0 then 0 else (graphDeg P - graphEig P ξ) * (wht f ξ * wht f ξ)) :=
  _root_.WalshAutomatonEngine.dirichletForm_eq_wht P f

theorem expander_mixing_lemma_int {k : Nat} (P : BitVec k → Bool) (μ : Int)
    (hbound : ∀ ξ : BitVec k, ξ ≠ 0 → -μ ≤ graphEig P ξ ∧ graphEig P ξ ≤ μ)
    (S T : BitVec k → Bool) :
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let disc := ((2 ^ k : Nat) : Int) * edgesBetween P S T - graphDeg P * s * t
    disc * disc ≤ (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) * (t * (((2 ^ k : Nat) : Int) - t)) :=
  _root_.WalshAutomatonEngine.expander_mixing_lemma_int P μ hbound S T

theorem mod3_exact_spectral_gap (k : Nat) (hk : 1 ≤ k) :
    (∀ f : BitVec k → Int, mod3Gap k * intVariance f ≤ ((2 ^ k : Nat) : Int) * dirichletForm mod3Pred f) ∧
    (∀ f : BitVec k → Int, bvSum f = 0 → mod3Gap k * bvSum (fun x => f x * f x) ≤ dirichletForm mod3Pred f) ∧
    (bvSum (chi (BitVec.allOnes k)) = 0 ∧
     bvSum (fun x => chi (BitVec.allOnes k) x * chi (BitVec.allOnes k) x) = ((2 ^ k : Nat) : Int) ∧
     dirichletForm mod3Pred (chi (BitVec.allOnes k)) =
       mod3Gap k * bvSum (fun x => chi (BitVec.allOnes k) x * chi (BitVec.allOnes k) x)) :=
  _root_.WalshAutomatonEngine.mod3_exact_spectral_gap k hk

theorem fib_expander_mixing_lemma {k : Nat} (hk : 3 ≤ k) (S T : BitVec k → Bool) :
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let μ := (lucas (k - 1) : Int) - 1
    let disc := ((2 ^ k : Nat) : Int) * edgesBetween fibPred S T - graphDeg (fibPred (k := k)) * s * t
    disc * disc ≤ (μ * μ) * (s * (((2 ^ k : Nat) : Int) - s)) * (t * (((2 ^ k : Nat) : Int) - t)) :=
  _root_.WalshAutomatonEngine.fib_expander_mixing_lemma hk S T

theorem witness_fib_k4 :
    graphDeg (fibPred (k := 4)) = 7 ∧
    graphEig (fibPred (k := 4)) (fibWitnessMax 4) = 3 ∧
    graphEig (fibPred (k := 4)) (fibWitnessMin 4) = -3 ∧
    dirichletForm (fibPred (k := 4)) (chi (fibWitnessMax 4)) = 64 :=
  _root_.WalshAutomatonEngine.witness_fib_k4

theorem sharpness_mod2_always_disconnected (k : Nat) (hk : 1 ≤ k) :
    let ξ : BitVec k := BitVec.ofNat k 1
    bvSum (chi ξ) = 0 ∧
    bvSum (fun x => chi ξ x * chi ξ x) = ((2 ^ k : Nat) : Int) ∧
    dirichletForm mod2Pred (chi ξ) = 0 :=
  _root_.WalshAutomatonEngine.sharpness_mod2_always_disconnected k hk

theorem witness_mod3_eml_k5 :
    let S : BitVec 5 → Bool := fun x => x.toNat < 11
    let T : BitVec 5 → Bool := fun x => x.toNat % 2 == 1
    let s := bvSum (indBool S)
    let t := bvSum (indBool T)
    let disc := ((2 ^ 5 : Nat) : Int) * edgesBetween mod3Pred S T - graphDeg (mod3Pred (k := 5)) * s * t
    s = 11 ∧ t = 16 ∧
    disc * disc ≤ (8 * 8) * (s * (32 - s)) * (t * (32 - t)) :=
  _root_.WalshAutomatonEngine.witness_mod3_eml_k5

end BitwiseExpanderWalshGapsChallenge
