import SiliconTfunctionBentDuality

namespace SiliconTfunctionBentDualityChallenge

open SiliconBent

theorem walsh_walsh (n : Nat) (f : Nat → Int) (x : Nat) (hx : x < 2 ^ n) :
    walsh n (walsh n f) x = (2 ^ n : Int) * f x :=
  _root_.SiliconBent.walsh_walsh n f x hx

theorem mm_isBent {π : Nat → Nat} (hπ : TBijection π) (g : Nat → Bool) (k : Nat) :
    IsBentWithDual k (mmSign k π g) (mmDualSign k π g) :=
  _root_.SiliconBent.mm_isBent hπ g k

theorem zeroSum_tQuad_isBent {φ1 φ2 : Nat → Nat} (hφ1 : Causal φ1) (hφ2 : Causal φ2) (k : Nat) :
    let ψ0 := fun a => a
    let ψ1 := fun a => a ^^^ (2 * φ1 a)
    let ψ2 := fun a => a ^^^ (2 * φ2 a)
    let ψ3 := fun a => a ^^^ (2 * (φ1 a ^^^ φ2 a))
    let f0 := mmDualSign k ψ0 (fun _ => false)
    let f1 := mmDualSign k ψ1 (fun _ => false)
    let f2 := mmDualSign k ψ2 (fun _ => false)
    let f3 := mmDualSign k ψ3 (fun _ => true)
    let d0 := mmSign k ψ0 (fun _ => false)
    let d1 := mmSign k ψ1 (fun _ => false)
    let d2 := mmSign k ψ2 (fun _ => false)
    let d3 := mmSign k ψ3 (fun _ => true)
    IsBentWithDual (k + 1) (quadCombine f0 f1 f2 f3) (quadDual d0 d1 d2 d3) :=
  _root_.SiliconBent.zeroSum_tQuad_isBent hφ1 hφ2 k

theorem mul3_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piMul3) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piMul3) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piMul3) :=
  _root_.SiliconBent.mul3_infinite_bent_and_nonMM k hk

theorem mul7_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piMul7) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piMul7) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piMul7) :=
  _root_.SiliconBent.mul7_infinite_bent_and_nonMM k hk

theorem counterexample_non_bijective_mul2 :
    ¬ FlatWalsh 1 (mmSign 1 (fun y => 2 * y) (fun _ => false)) ∧
    ¬ VanishingAutocorr 2 (mmSign 1 (fun y => 2 * y) (fun _ => false)) :=
  _root_.SiliconBent.counterexample_non_bijective_mul2

theorem counterexample_non_causal_shift :
    let π := fun y => y ^^^ (2 * (y / 2))
    π 0 % 4 = π 2 % 4 ∧ (0 : Nat) ≠ 2 :=
  _root_.SiliconBent.counterexample_non_causal_shift

theorem nonvacuity_carletT_nonzero_pi0 (k : Nat) (hk : 2 ≤ k) :
    FlatWalsh k (carletTSign k 2 (fun y => 3 * y + 1)) ∧
    VanishingAutocorr (2 * k) (carletTSign k 2 (fun y => 3 * y + 1)) :=
  _root_.SiliconBent.nonvacuity_carletT_nonzero_pi0 k hk

end SiliconTfunctionBentDualityChallenge
