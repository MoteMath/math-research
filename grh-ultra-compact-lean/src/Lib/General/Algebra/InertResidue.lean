import Lib.Adelic.Adeles.AdeleIdempotent
import Lib.Weil.Construction.GaussSumSign
open Nat NumberField StablyUnram FiniteField Ideal Quotient Fint selfAdjoint
lemma card_selfAdjoint {k} [Field k] [StarRing k] [Finite k] {i : k} (a : i * i = -1) (h : star i ≠ i) : .card (selfAdjoint k) ^ 2 = Nat.card k ∧ .card (selfAdjoint k) % 4 = 3 := by
 rw [sq, ← card_prod]
 use card_congr ⟨fun (x, y) ↦ (x - i * y) / 2, fun z ↦ ⟨⟨_, .add_star_self z⟩, _, .add_star_self (i * z)⟩, ?_, ?_⟩, Fintype.card_eq_nat_card ▸ isSquare_neg_one_iff.not_left.1 ?_ <;> simp_intro x [mem_iff, IsSquare, Subtype.ext_iff] <;> grind [star_mul, star_inj, star_neg, star_one]
variable {E} [Field E] [NumberField E] [IsCMField E] [StablyUnram E] {w : FinPlace E}
lemma StablyUnram.exists_sq_eq_q_of_inert (h : star w = w) : ∃ r, r ^ 2 = w.q ∧ r % 4 = 3 := by
 obtain ⟨i, ω, a, b, ⟨⟩⟩ := ‹StablyUnram E›.exists_i_c₀
 let := Quotient.field w.1
 apply_fun Ideal.Quotient.mk w at *
 exact ⟨_, @card_selfAdjoint _ _ (starRingOfInvolution (quotientMap _ _ congr($h.1).ge) (Quot.ind (congrArg _ <| star_star ·))) _ i a (b.trans_ne (by grind [one_add_one_eq_two, mem_star_place, eq_zero_iff_mem]))⟩
lemma isSplit_of_q_prime (h : w.q.Prime) : w.IsSplit := by grind [exists_sq_eq_q_of_inert, h.pow_eq_iff]
