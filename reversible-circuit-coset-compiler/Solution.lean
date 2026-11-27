import ReversibleCircuitCosetCompiler

namespace ReversibleCircuitCosetCompilerChallenge

open RevCert

theorem sound_checkWindowEq (r w0 : Nat) (C1 C2 : Circuit r)
    (h : checkWindowEq r w0 C1 C2 = true) :
    ∀ (w : Nat), w0 ≤ w → ∀ (s : State r w), evalCircuit C1 s = evalCircuit C2 s :=
  _root_.RevCert.sound_checkWindowEq r w0 C1 C2 h

theorem sound_coset_order {r w0 : Nat} (lib : RelLib r) (hLib : LibSound lib w0)
    (gens : Array (Circuit r)) (cc : CosetCert r)
    (hCert : checkCosetCert lib gens cc = true)
    (word : List Nat) (hWord : ∀ k ∈ word, k < gens.size) (d : Nat)
    (hCycle : walkCoset cc.table 0 (repeatWord d word) = 0) :
    ∀ w, w0 ≤ w → ∀ s : State r w,
      evalCircuit (repeatCircuit d (evalWord gens word)) s = s :=
  _root_.RevCert.sound_coset_order lib hLib gens cc hCert word hWord d hCycle

theorem thm_d6_C_power_mod :
    ∀ (n w : Nat), 1 ≤ w → ∀ (s : State 2 w),
      evalCircuit (repeatCircuit n circC) s = evalCircuit (repeatCircuit (n % 6) circC) s :=
  _root_.RevCert.thm_d6_C_power_mod

theorem thm_b3_AST_power_mod :
    ∀ (n w : Nat), 3 ≤ w → ∀ (s : State 1 w),
      evalCircuit (repeatCircuit n [gA, gS, gT]) s =
      evalCircuit (repeatCircuit (n % 6) [gA, gS, gT]) s :=
  _root_.RevCert.thm_b3_AST_power_mod

theorem thm_ptoff_dihedral_family :
    ∀ (n w : Nat) (s : State 4 w),
      evalCircuit (repeatCircuit 2 (repeatCircuit n circPtoff ++ [.rNot 3])) s = s :=
  _root_.RevCert.thm_ptoff_dihedral_family

theorem thm_t3_sharp_collapse_w2 :
    ∀ (s : State 4 2), evalCircuit (circT3 0 1 3 2) s = s :=
  _root_.RevCert.thm_t3_sharp_collapse_w2

theorem mut_window_out_of_bounds :
    checkWindowEq 1 2 [gT] [gT] = false :=
  _root_.RevCert.mut_window_out_of_bounds

theorem mut_order_lower_inflated :
    checkOrderLowerAt 2 2 12 circC = false :=
  _root_.RevCert.mut_order_lower_inflated

end ReversibleCircuitCosetCompilerChallenge
