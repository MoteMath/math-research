import BruhatTitsCarryGaugeAutomata

namespace BruhatTitsCarryGaugeAutomataChallenge

open BruhatTitsCarryEngine BruhatTitsCarryEngine.ModQuotientCert

theorem carryCount_eq_evalMat (w : Nat → Int) (hw0 : w 0 = 1) (C : Nat) :
    ∀ width n, n < 2 ^ width → ∀ c : Fin (C + 1),
      carryCount w C width n c.val =
        evalMat (carryMat w C false) (carryMat w C true) (e0Vec C) n c :=
  _root_.BruhatTitsCarryEngine.carryCount_eq_evalMat w hw0 C

theorem sound {d K : Nat} {hd : 0 < d} {M0 M1 : Mat d} {v0 : Vec d} {d K : Nat} {m : Int} {M0 M1 : Mat d} {v0 : Vec d} (C : ModQuotientCert d K m M0 M1 v0) :
    ∀ n i, evalMat M0 M1 v0 n i % m = C.phi (C.runQ n) i % m :=
  _root_.BruhatTitsCarryEngine.ModQuotientCert.sound C

theorem thm_2x2_5point_rigidity (w1 w2 w3 : Int) :
    ((∀ n : Nat, ExactVal2 (f2 w1 w2 w3 n) (phi3 n)) ↔
     (ExactVal2 (f2 w1 w2 w3 1) (phi3 1) ∧
      ExactVal2 (f2 w1 w2 w3 2) (phi3 2) ∧
      ExactVal2 (f2 w1 w2 w3 3) (phi3 3) ∧
      ExactVal2 (f2 w1 w2 w3 7) (phi3 7) ∧
      ExactVal2 (f2 w1 w2 w3 8) (phi3 8)))
    ∧
    ((ExactVal2 (f2 w1 w2 w3 1) (phi3 1) ∧
      ExactVal2 (f2 w1 w2 w3 2) (phi3 2) ∧
      ExactVal2 (f2 w1 w2 w3 3) (phi3 3) ∧
      ExactVal2 (f2 w1 w2 w3 7) (phi3 7) ∧
      ExactVal2 (f2 w1 w2 w3 8) (phi3 8)) ↔
     (w1 % 4 = 3 ∧ w2 % 4 = 3 ∧ w3 % 4 = 1 ∧ (w1 + w2 + w3) % 8 = 7)) :=
  _root_.BruhatTitsCarryEngine.thm_2x2_5point_rigidity w1 w2 w3

theorem thm_2x2_k_equiv_3_mod_8 (t : Nat) :
    let k := 8 * t + 3
    ∀ n : Nat, ExactVal2 (f2 (choose k 1 : Int) (choose k 2 : Int) (choose k 3 : Int) n) (phi3 n) :=
  _root_.BruhatTitsCarryEngine.thm_2x2_k_equiv_3_mod_8 t

theorem thm_3x3_exact_v2 (w1 w2 w3 w4 w5 : Int)
    (h1 : w1 % 8 = 4) (h2 : w2 % 4 = 2) (h3 : w3 % 8 = 4)
    (h4 : w4 % 2 = 1) (h5 : w5 % 16 = 0) :
    ∀ n : Nat, ExactVal2 (f3 w1 w2 w3 w4 w5 n) (phi4 n) :=
  _root_.BruhatTitsCarryEngine.thm_3x3_exact_v2 w1 w2 w3 w4 w5 h1 h2 h3 h4 h5

theorem thm_phi4_unbounded {d K : Nat} {m : Int} {M0 M1 : Mat d} {v0 : Vec d} : ∀ m : Nat, phi4 (2 ^ (m + 2) - 1) = m + 2 :=
  _root_.BruhatTitsCarryEngine.thm_phi4_unbounded

theorem nonvacuous_3x3_k4 :
    Nonempty (LatticeGaugeCert 3 6 (by decide) (M3_0 4 6 4 1) (M3_1 4 6 4 1 0) v3_0) :=
  _root_.BruhatTitsCarryEngine.nonvacuous_3x3_k4

theorem sharpness_3x3_all_five_weights :
    ¬ ExactVal2 (f3 8 6 4 1 0 1) (phi4 1) ∧
    ¬ ExactVal2 (f3 4 0 4 1 0 2) (phi4 2) ∧
    ¬ ExactVal2 (f3 4 6 8 1 0 3) (phi4 3) ∧
    ¬ ExactVal2 (f3 4 6 4 2 0 4) (phi4 4) ∧
    ¬ ExactVal2 (f3 4 6 4 1 8 5) (phi4 5) :=
  _root_.BruhatTitsCarryEngine.sharpness_3x3_all_five_weights

end BruhatTitsCarryGaugeAutomataChallenge
