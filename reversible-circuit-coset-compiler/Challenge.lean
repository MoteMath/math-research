import ReversibleCircuitCosetCompiler.Defs

namespace ReversibleCircuitCosetCompilerChallenge

open RevCert

/-- Layer 1A Soundness Meta-Theorem: lifts finite width-w0 equivalence to ALL w ≥ w0! -/
theorem sound_checkWindowEq (r w0 : Nat) (C1 C2 : Circuit r)
    (h : checkWindowEq r w0 C1 C2 = true) :
    ∀ (w : Nat), w0 ≤ w → ∀ (s : State r w), evalCircuit C1 s = evalCircuit C2 s := by
  sorry

/-- Layer 2B soundness (universal order bound, for every bit-width w ≥ w0): if the coset certificate checks and `repeatWord d word` returns to coset 0, then W^d = id on every `State r w` with w ≥ w0, where W is the circuit `evalWord gens word`. (The statement is only W^d = id; the consequence W^n = W^(n % d) is not stated here.) -/
theorem sound_coset_order {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) (d : Nat)
    (hCycle : walkCoset cc.table 0 (repeatWord d word) = 0) :
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (repeatCircuit d (evalWord gens word)) s = s := by
  sorry

/-- Theorem I.5 (Universal D6 Power-Mod-6 Reduction ∀ n : Nat, ∀ w ≥ 1): C^n = C^(n % 6). -/
theorem thm_d6_C_power_mod :
    ∀ (n w : Nat), 1 ≤ w → ∀ (s : State 2 w),
      evalCircuit (repeatCircuit n circC) s = evalCircuit (repeatCircuit (n % 6) circC) s := by
  sorry

/-- Theorem II.3 (Universal Modulo-6 Power Reduction ∀ n : Nat, ∀ w ≥ 3): (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^n = (bCnot(0,1) · bSwap(0,1) · bToff(0,1,2))^(n % 6). -/
theorem thm_b3_AST_power_mod :
    ∀ (n w : Nat), 3 ≤ w → ∀ (s : State 1 w),
      evalCircuit (repeatCircuit n [gA, gS, gT]) s =
      evalCircuit (repeatCircuit (n % 6) [gA, gS, gT]) s := by
  sorry

/-- Theorem III.2 (Infinite Family of Hybrid Toffoli-Add Involutions ∀ n : Nat, ∀ w : Nat): (P_toff(0,1,3;2)^n · rNot(3))^2 = Id for ALL exponents n and ALL bit-widths w! -/
theorem thm_ptoff_dihedral_family :
    ∀ (n w : Nat) (s : State 4 w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n circPtoff ++ [.rNot 3])) s = s := by
  sorry

/-- Sharpness III.c (width threshold of T3), collapse half only: at width w = 2, `circT3 0 1 3 2` is the identity on every `State 4 2`. (The other half, T3 ≠ Id for w ≥ 3, is `thm_t3_nontrivial_ge3` in `Theorems.lean` and is not part of this file.) -/
theorem thm_t3_sharp_collapse_w2 :
    ∀ (s : State 4 2), evalCircuit (circT3 0 1 3 2) s = s := by
  sorry

theorem mut_window_out_of_bounds :
    checkWindowEq 1 2 [gT] [gT] = false := by
  sorry

theorem mut_order_lower_inflated :
    checkOrderLowerAt 2 2 12 circC = false := by
  sorry

end ReversibleCircuitCosetCompilerChallenge
