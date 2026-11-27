import BinaryPartitionWindowAutomata

namespace BinaryPartitionWindowAutomataChallenge

open BinaryPartitionAutomaton.WindowAutomatonCert BinaryPartitionAutomaton

theorem soundness (c : WindowAutomatonCert) (hD : ValidDigitSet c.D c.L)
    (hv : c.isValid = true) :
    ∀ n : Nat, c.runState n < c.S ∧ ∀ j < c.L, winVec c.D c.M n j = c.embed (c.runState n) j :=
  _root_.BinaryPartitionAutomaton.WindowAutomatonCert.soundness c hD hv

theorem b5_forbids_three_mod4_via_dfa : ∀ n : Nat, br 5 n % 4 ≠ 3 :=
  _root_.BinaryPartitionAutomaton.b5_forbids_three_mod4_via_dfa

theorem b4_coupled_8n_5_mod4 : ∀ n : Nat, br 4 (8 * n + 5) % 4 = (3 * br 4 (8 * n)) % 4 :=
  _root_.BinaryPartitionAutomaton.b4_coupled_8n_5_mod4

theorem mutation_rejects_bad_q0 : ({ cert_b5 with q0 := 1 }).isValid = false :=
  _root_.BinaryPartitionAutomaton.mutation_rejects_bad_q0

theorem br_universal_mod4_carry_law (t u : Nat) (ht : t ≥ 1) (hu : u % 2 = 1) (j : Nat) :
    br (2 ^ t * u - 1) (2 * u * j) % 4 = phi t (j % 2 ^ t) :=
  _root_.BinaryPartitionAutomaton.br_universal_mod4_carry_law t u ht hu j

theorem sharpness_r3_even_v2 : br 3 4 % 4 = 3 :=
  _root_.BinaryPartitionAutomaton.sharpness_r3_even_v2

theorem sharpness_b5_fails_mod8 : br 5 6 % 8 ≠ 1 :=
  _root_.BinaryPartitionAutomaton.sharpness_b5_fails_mod8

theorem sharpness_gap023_offset17_fails :
    binPart [0, 2, 3] (32 * 0 + 17) % 4 ≠ (3 * binPart [0, 2, 3] 0) % 4 :=
  _root_.BinaryPartitionAutomaton.sharpness_gap023_offset17_fails

end BinaryPartitionWindowAutomataChallenge
