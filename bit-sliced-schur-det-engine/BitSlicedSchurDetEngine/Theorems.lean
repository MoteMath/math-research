import BitSlicedSchurDetEngine.Defs

namespace BitSlicedSchur
namespace CRing
variable {R : Type u} [CRing R]

end CRing
section FinOps
variable {R : Type u} [CRing R]

end FinOps
section SumVecProps
variable {R : Type u} [CRing R]

end SumVecProps
/-- Codomain transposition also flips `eps`! (Used for `det_col_swap`.) -/
theorem eps_swap_codomain {n : Nat} (c1 c2 : Fin n) (hc : c1 ≠ c2) (f : Fin n → Fin n) :
    eps (fun i => swapFin c1 c2 (f i)) = -(eps f) := by
  by_cases hinj : ∀ x y : Fin n, f x = f y → x = y
  · -- When f is injective on Fin n, it is surjective! Pick p, q with f p = c1, f q = c2.
    rcases fin_inj_surj f hinj c1 with ⟨p, hp⟩
    rcases fin_inj_surj f hinj c2 with ⟨q, hq⟩
    have hpq : p ≠ q := fun h => hc (by rw [← hp, ← hq, h])
    have heq : (fun i => (swapFin c1 c2 (f i)).val) = (fun i => (f (swapFin p q i)).val) := by
      funext i; congr 1
      by_cases h1 : i = p
      · subst h1; rw [hp, swapFin_left, swapFin_left, hq]
      · by_cases h2 : i = q
        · subst h2; rw [hq, swapFin_right, swapFin_right, hp]
        · have hne1 : f i ≠ c1 := fun h => h1 (hinj i p (h.trans hp.symm))
          have hne2 : f i ≠ c2 := fun h => h2 (hinj i q (h.trans hq.symm))
          unfold swapFin; simp [h1, h2, hne1, hne2]
    unfold eps
    rw [heq]
    exact epsNat_swap p q hpq (fun i => (f i).val)
  · -- Not injective -> ∃ x ≠ y with f x = f y -> both sides are 0!
    -- Prove constructively by scanning Fin n × Fin n? Let's write a tiny decidable finder!
    have hex : ∃ x y : Fin n, x ≠ y ∧ f x = f y := by
      have hdec : ¬ (∀ x y : Fin n, f x = f y → x = y) := hinj
      -- Classical.byContradiction is NOT even needed because Fin n is finite & decidable!
      -- Using decide/Fin search:
      suffices ∀ (P : Fin n → Fin n → Bool),
          (¬ ∀ x y, P x y = true) → ∃ x y, P x y = false by
        rcases this (fun x y => decide (f x = f y → x = y)) (by
          intro hall; apply hdec; intro x y hxy
          have := hall x y; simp only [decide_eq_true_eq] at this; exact this hxy) with ⟨x, y, hxy⟩
        simp only [decide_eq_false_iff_not] at hxy
        by_cases h1 : f x = f y
        · exact ⟨x, y, fun heq => hxy (fun _ => heq), h1⟩
        · exfalso; exact hxy (fun h => absurd h h1)
      intro P hnot
      -- Decidable existential over finite Fin n
      have h1 : ∀ (m : Nat) (Q : Fin m → Bool), (¬ ∀ i, Q i = true) → ∃ i, Q i = false := by
        intro m
        induction m with
        | zero => intro Q h; exfalso; apply h; intro i; exact Fin.elim0 i
        | succ m ih =>
          intro Q h
          cases hlast : Q (Fin.last m)
          · exact ⟨Fin.last m, hlast⟩
          · rcases ih (fun i => Q i.castSucc) (by
              intro hall; apply h; intro i
              by_cases hi : i.val < m
              · have : i = (⟨i.val, hi⟩ : Fin m).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨i.val, hi⟩
              · have : i = Fin.last m := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨i, hi⟩
            exact ⟨i.castSucc, hi⟩
      rcases h1 n (fun x => decide (∀ y : Fin n, P x y = true)) (by
        intro hall; apply hnot; intro x y
        have := hall x; simp only [decide_eq_true_eq] at this; exact this y) with ⟨x, hx⟩
      simp only [decide_eq_false_iff_not] at hx
      rcases h1 n (fun y => P x y) hx with ⟨y, hy⟩
      exact ⟨x, y, hy⟩
    rcases hex with ⟨x, y, hxy, hfxy⟩
    have h1 : eps f = 0 := epsNat_eq_zero_of_eq (fun i => (f i).val) x y hxy (congrArg Fin.val hfxy)
    have h2 : eps (fun i => swapFin c1 c2 (f i)) = 0 :=
      epsNat_eq_zero_of_eq (fun i => (swapFin c1 c2 (f i)).val) x y hxy
        (congrArg (fun z => (swapFin c1 c2 z).val) hfxy)
    rw [h1, h2]; rfl

/-! ### Inversion Count for Sorting Injective `Fin n -> Fin n` (for `det_mul`) -/

section MatDefs
variable {R : Type u} [CRing R]

/-- Alternating row-permutation sum lemma used for `det_mul`. -/
theorem altSum_rows {n : Nat} (B : Mat R n) (h : Fin n → Fin n) :
    sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (h i) (g i)))) =
    CRing.mul (CRing.ofInt (eps h)) (det B) := by
  -- Helper: adjacent swap on h negates the LHS
  have hswap_adj : ∀ (j : Nat) (hj : j + 1 < n) (u : Fin n → Fin n),
      sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (u (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) (g i)))) =
      CRing.neg (sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (u i) (g i))))) := by
    intro j hj u
    rw [← sumVec_swap_adj j hj (fun g => CRing.mul (CRing.ofInt (eps g))
          (prodFin n (fun i => B (u (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) (g i))))]
    rw [← sumVec_neg]
    apply sumVec_congr; intro g
    have heps : eps (fun i => g (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)) = -(eps g) :=
      epsNat_swap_adj j hj (fun i => (g i).val)
    rw [heps, CRing.ofInt_neg, CRing.neg_mul]
    congr 1; congr 1
    exact prodFin_swap_adj j hj (fun i => B (u i) (g i))
  -- Check whether h is injective on Fin n!
  by_cases hinj : ∀ p q : Fin n, h p = h q → p = q
  · -- Sort h to id by strong induction on invCount!
    suffices hsort : ∀ (c : Nat) (u : Fin n → Fin n),
        (∀ p q, u p = u q → p = q) → invCount n (fun i => (u i).val) = c →
        sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (u i) (g i)))) =
        CRing.mul (CRing.ofInt (eps u)) (det B) by
      exact hsort (invCount n (fun i => (h i).val)) h hinj rfl
    intro c
    induction c with
    | zero =>
      intro u hu_inj hinv0
      -- invCount = 0 and injective => u = id!
      have hmono : ∀ j : Nat, (hj : j + 1 < n) → (u ⟨j, by omega⟩).val < (u ⟨j + 1, hj⟩).val := by
        intro j hj
        by_cases hlt : (u ⟨j + 1, hj⟩).val < (u ⟨j, by omega⟩).val
        · have hdec := invCount_swap_adj_dec j hj (fun i => (u i).val) hlt
          omega
        · have hne : (u ⟨j, by omega⟩).val ≠ (u ⟨j + 1, hj⟩).val := by
            intro heq
            have := hu_inj ⟨j, by omega⟩ ⟨j + 1, hj⟩ (Fin.ext heq)
            have hv := congrArg Fin.val this; simp at hv
          omega
      have hge : ∀ i : Fin n, i.val ≤ (u i).val := by
        suffices ∀ k (hk : k < n), k ≤ (u ⟨k, hk⟩).val by intro i; exact this i.val i.isLt
        intro k
        induction k with
        | zero => intro _; exact Nat.zero_le _
        | succ k ihk =>
          intro hk
          have h1 := ihk (Nat.lt_of_succ_lt hk)
          have h2 := hmono k hk
          omega
      have hle : ∀ i : Fin n, (u i).val ≤ i.val := by
        suffices ∀ d (k : Nat) (hk : k < n), k + d = n - 1 → (u ⟨k, hk⟩).val ≤ k by
          intro i; exact this (n - 1 - i.val) i.val i.isLt (by omega)
        intro d
        induction d with
        | zero => intro k hk hkd; have := (u ⟨k, hk⟩).isLt; omega
        | succ d ihd =>
          intro k hk hkd
          have h1 := ihd (k + 1) (by omega) (by omega)
          have h2 := hmono k (by omega)
          omega
      have huid : u = id := by
        funext i; apply Fin.ext
        have h1 := hge i; have h2 := hle i; simp; omega
      subst huid
      have heps1 : eps (id : Fin n → Fin n) = 1 := epsNat_id n
      rw [heps1, CRing.ofInt_one, CRing.one_mul]; rfl
    | succ c ihc =>
      intro u hu_inj hinv
      rcases exists_adj_inv_of_invCount_pos (fun i => (u i).val) (by omega) with ⟨j, hj, hlt⟩
      let u' : Fin n → Fin n := fun i => u (swapFin ⟨j, by omega⟩ ⟨j + 1, hj⟩ i)
      have hu'_inj : ∀ p q, u' p = u' q → p = q := fun p q heq =>
        swapFin_inj ⟨j, by omega⟩ ⟨j + 1, hj⟩ (hu_inj _ _ heq)
      have hu'_inv : invCount n (fun i => (u' i).val) = c := by
        have hdec := invCount_swap_adj_dec j hj (fun i => (u i).val) hlt
        dsimp only [u']; omega
      have hrec := ihc u' hu'_inj hu'_inv
      have hstep := hswap_adj j hj u
      -- hstep says LHS(u') = -LHS(u), so LHS(u) = -LHS(u')!
      have hneg1 : sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (u i) (g i)))) =
                   CRing.neg (sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g)) (prodFin n (fun i => B (u' i) (g i))))) := by
        rw [hstep, CRing.neg_neg]
      rw [hneg1, hrec]
      have heps_u' : eps u' = -(eps u) := epsNat_swap_adj j hj (fun i => (u i).val)
      rw [heps_u', CRing.ofInt_neg, CRing.neg_mul, CRing.neg_neg]
  · -- Non-injective h: find p ≠ q with h p = h q constructively!
    have hex : ∃ p q : Fin n, p ≠ q ∧ h p = h q := by
      have h1 : ∀ (m : Nat) (Q : Fin m → Bool), (¬ ∀ i, Q i = true) → ∃ i, Q i = false := by
        intro m
        induction m with
        | zero => intro Q hnot; exfalso; apply hnot; intro i; exact Fin.elim0 i
        | succ m ih =>
          intro Q hnot
          cases hlast : Q (Fin.last m)
          · exact ⟨Fin.last m, hlast⟩
          · rcases ih (fun i => Q i.castSucc) (by
              intro hall; apply hnot; intro i
              by_cases hi : i.val < m
              · have : i = (⟨i.val, hi⟩ : Fin m).castSucc := Fin.ext rfl
                rw [this]; exact hall ⟨i.val, hi⟩
              · have : i = Fin.last m := by apply Fin.ext; simp; omega
                rw [this]; exact hlast) with ⟨i, hi⟩
            exact ⟨i.castSucc, hi⟩
      rcases h1 n (fun p => decide (∀ q : Fin n, h p = h q → p = q)) (by
        intro hall; apply hinj; intro p q hpq
        have := hall p; simp only [decide_eq_true_eq] at this; exact this q hpq) with ⟨p, hp⟩
      simp only [decide_eq_false_iff_not] at hp
      rcases h1 n (fun q => decide (h p = h q → p = q)) (by
        intro hall; apply hp; intro q hq
        have := hall q; simp only [decide_eq_true_eq] at this; exact this hq) with ⟨q, hq⟩
      simp only [decide_eq_false_iff_not] at hq
      by_cases hpq_eq : h p = h q
      · exact ⟨p, q, fun heq => hq (fun _ => heq), hpq_eq⟩
      · exfalso; exact hq (fun heq => absurd heq hpq_eq)
    rcases hex with ⟨p, q, hpq, hhpq⟩
    have heps0 : eps h = 0 := epsNat_eq_zero_of_eq (fun i => (h i).val) p q hpq (congrArg Fin.val hhpq)
    rw [heps0, CRing.ofInt_zero, CRing.zero_mul]
    -- Apply sumVec_skew_zero with transposition (p, q)!
    apply sumVec_skew_zero p q hpq
    · intro g hg
      have hg0 : eps g = 0 := epsNat_eq_zero_of_eq (fun i => (g i).val) p q hpq (congrArg Fin.val hg)
      rw [hg0, CRing.ofInt_zero, CRing.zero_mul]
    · intro g
      have heps_sw : eps (fun i => g (swapFin p q i)) = -(eps g) :=
        epsNat_swap p q hpq (fun i => (g i).val)
      rw [heps_sw, CRing.ofInt_neg, CRing.neg_mul]
      congr 1; congr 1
      -- Show prodFin n (fun i => B (h i) (g (swapFin p q i))) = prodFin n (fun i => B (h i) (g i))
      -- Because h p = h q, swapping p and q in (fun i => B (h i) (g i)) matches!
      have hswap_prod : ∀ (r : Fin n → R),
          prodFin n (fun i => r (swapFin p q i)) = prodFin n r := by
        -- Prove general prodFin_swap from prodFin_swap_adj (same decomposition as sumVec_swap)!
        intro r
        suffices hs : ∀ (d : Nat) (a b : Fin n), a.val + d = b.val →
            ∀ r : Fin n → R, prodFin n (fun i => r (swapFin a b i)) = prodFin n r by
          by_cases hab : p.val ≤ q.val
          · exact hs (q.val - p.val) p q (by omega) r
          · rw [prodFin_congr (fun i => by rw [swapFin_comm])]
            exact hs (p.val - q.val) q p (by omega) r
        intro d
        induction d with
        | zero =>
          intro a b hab r
          have : a = b := Fin.ext (by omega); subst this
          exact prodFin_congr (fun i => by rw [swapFin_self])
        | succ d ihd =>
          intro a b hab r
          cases d with
          | zero =>
            have hj : a.val + 1 < n := by omega
            have hb : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simp; omega); subst hb
            exact prodFin_swap_adj a.val hj r
          | succ d' =>
            have hc_lt : a.val + d' + 1 < n := by omega
            let c : Fin n := ⟨a.val + d' + 1, hc_lt⟩
            have hac : a.val + (d' + 1) = c.val := by simp [c]; omega
            have hb_eq : b = ⟨c.val + 1, by simp [c]; omega⟩ := Fin.ext (by simp [c]; omega)
            have hc_eq : (⟨c.val, by omega⟩ : Fin n) = c := Fin.ext rfl
            have hdec : ∀ i : Fin n, swapFin a b i = swapFin c b (swapFin a c (swapFin c b i)) := by
              intro i
              have h1 : a ≠ c := by intro h; have := congrArg Fin.val h; simp [c] at this; omega
              have h2 : a ≠ b := by intro h; have := congrArg Fin.val h; omega
              have h3 : c ≠ b := by intro h; have := congrArg Fin.val h; simp [c] at this; omega
              by_cases c1 : i = a
              · subst c1
                have : swapFin c b i = i := by unfold swapFin; simp [h1, h2]
                rw [swapFin_left, this, swapFin_left, swapFin_left]
              · by_cases c2 : i = b
                · subst c2
                  rw [swapFin_right, swapFin_right, swapFin_right]
                  unfold swapFin; simp [h1, h2]
                · by_cases c3 : i = c
                  · subst c3
                    rw [swapFin_left]
                    have : swapFin a c b = b := by unfold swapFin; simp [Ne.symm h2, Ne.symm h3]
                    rw [this, swapFin_right]
                    unfold swapFin; simp [c1, c2]
                  · have s1 : swapFin c b i = i := by unfold swapFin; simp [c3, c2]
                    have s2 : swapFin a c i = i := by unfold swapFin; simp [c1, c3]
                    have s3 : swapFin a b i = i := by unfold swapFin; simp [c1, c2]
                    rw [s1, s2, s1, s3]
            have hs1 : prodFin n (fun i => r (swapFin c b (swapFin a c (swapFin c b i)))) =
                       prodFin n (fun i => r (swapFin c b (swapFin a c i))) := by
              have h := prodFin_swap_adj c.val (by simp [c]; omega) (fun i => r (swapFin c b (swapFin a c i)))
              rw [hc_eq, ← hb_eq] at h; exact h
            have hs2 : prodFin n (fun i => r (swapFin c b (swapFin a c i))) =
                       prodFin n (fun i => r (swapFin c b i)) :=
              ihd a c hac (fun i => r (swapFin c b i))
            have hs3 : prodFin n (fun i => r (swapFin c b i)) = prodFin n r := by
              have h := prodFin_swap_adj c.val (by simp [c]; omega) r
              rw [hc_eq, ← hb_eq] at h; exact h
            calc prodFin n (fun i => r (swapFin a b i))
                = prodFin n (fun i => r (swapFin c b (swapFin a c (swapFin c b i)))) :=
                    prodFin_congr (fun i => by rw [hdec])
              _ = prodFin n (fun i => r (swapFin c b (swapFin a c i))) := hs1
              _ = prodFin n (fun i => r (swapFin c b i)) := hs2
              _ = prodFin n r := hs3
      rw [← hswap_prod (fun i => B (h i) (g i))]
      apply prodFin_congr; intro i
      have hhsw : h (swapFin p q i) = h i := by
        unfold swapFin
        by_cases h1 : i = p
        · subst h1; simp [hhpq]
        · by_cases h2 : i = q
          · subst h2; simp [h1, hhpq]
          · simp [h1, h2]
      rw [hhsw]

/-- Multiplicativity of the classical Leibniz determinant over ANY commutative ring `R`. -/
theorem det_mul {n : Nat} (A B : Mat R n) : det (matMul A B) = CRing.mul (det A) (det B) := by
  unfold det matMul
  have h1 : sumVec n n (fun g => CRing.mul (CRing.ofInt (eps g))
              (prodFin n (fun i => sumFin n (fun k => CRing.mul (A i k) (B k (g i)))))) =
            sumVec n n (fun g => sumVec n n (fun h =>
              CRing.mul (CRing.ofInt (eps g))
                (CRing.mul (prodFin n (fun i => A i (h i)))
                           (prodFin n (fun i => B (h i) (g i)))))) := by
    apply sumVec_congr; intro g
    rw [prodFin_sumFin, sumVec_mul_left]
    apply sumVec_congr; intro h
    rw [prodFin_mul]
  rw [h1]
  -- Swap outer sumVec g and inner sumVec h!
  have hsf : ∀ (r1 k1 k2 : Nat) (G : Fin k1 → (Fin r1 → Fin k2) → R),
      sumFin k1 (fun a => sumVec r1 k2 (fun h => G a h)) =
      sumVec r1 k2 (fun h => sumFin k1 (fun a => G a h)) := by
    intro r1 k1 k2
    induction r1 with
    | zero => intro _; rfl
    | succ r1 ihr =>
      intro G
      simp only [sumVec]
      rw [sumFin_comm]
      exact sumFin_congr (fun b => ihr (fun a u => G a (finSnoc u b)))
  have hcomm : ∀ (m1 m2 k1 k2 : Nat) (F : (Fin m1 → Fin k1) → (Fin m2 → Fin k2) → R),
      sumVec m1 k1 (fun g => sumVec m2 k2 (fun h => F g h)) =
      sumVec m2 k2 (fun h => sumVec m1 k1 (fun g => F g h)) := by
    intro m1 m2 k1 k2
    induction m1 with
    | zero => intro _; rfl
    | succ m1 ih1 =>
      intro F
      simp only [sumVec]
      rw [sumFin_congr (fun a => ih1 (fun g h => F (finSnoc g a) h)), hsf]
  rw [hcomm]
  have h2 : sumVec n n (fun h => sumVec n n (fun g =>
              CRing.mul (CRing.ofInt (eps g))
                (CRing.mul (prodFin n (fun i => A i (h i)))
                           (prodFin n (fun i => B (h i) (g i)))))) =
            sumVec n n (fun h => CRing.mul (prodFin n (fun i => A i (h i)))
              (CRing.mul (CRing.ofInt (eps h)) (det B))) := by
    apply sumVec_congr; intro h
    rw [← altSum_rows B h, sumVec_mul_left]
    apply sumVec_congr; intro g
    rw [← CRing.mul_assoc, CRing.mul_comm (CRing.ofInt (eps g)) (prodFin n (fun i => A i (h i))),
        CRing.mul_assoc]
  rw [h2]
  rw [sumVec_mul_right]
  apply sumVec_congr; intro h
  rw [← CRing.mul_assoc, CRing.mul_comm (prodFin n (fun i => A i (h i))) (CRing.ofInt (eps h))]
  rfl

/-! ### Row/Column Multilinearity, Column Swap, Unit-Row Congruence, and Block-Triangular `det` -/

theorem det_col_swap {n : Nat} (c1 c2 : Fin n) (hc : c1 ≠ c2) (M : Mat R n) :
    det (fun i j => M i (swapFin c1 c2 j)) = CRing.neg (det M) := by
  unfold det
  rw [← sumVec_swap_codomain c1 c2 (fun f => CRing.mul (CRing.ofInt (eps f))
        (prodFin n (fun i => M i (swapFin c1 c2 (f i)))))]
  rw [← sumVec_neg]
  apply sumVec_congr; intro f
  rw [eps_swap_codomain c1 c2 hc f, CRing.ofInt_neg, CRing.neg_mul]
  congr 1; congr 1
  exact prodFin_congr (fun i => by rw [swapFin_invol])

/-- Exact unimodular left Block-Schur complement over ANY commutative ring `R`. -/
theorem det_block_schur_left_unimodular {n : Nat} (A B C D L : Mat R n)
    (hLA : matMul L A = C) :
    det (blockMat A B C D) = CRing.mul (det A) (det (matSub D (matMul L B))) := by
  have hmul : matMul (blockMat (matOne n) (matZero n) (matNeg L) (matOne n)) (blockMat A B C D) =
              blockMat A B (matZero n) (matSub D (matMul L B)) := by
    rw [blockMat_mul, matMul_one_left, matMul_zero_left, matAdd_zero_right,
        matMul_one_left, matMul_zero_left, matAdd_zero_right,
        matMul_neg_left, matMul_one_left, matMul_neg_left, matMul_one_left]
    congr 1
    · funext i j; unfold matAdd matNeg matZero; rw [hLA]; exact CRing.add_left_neg (C i j)
    · funext i j; unfold matAdd matNeg matSub CRing.sub; exact CRing.add_comm _ _
  have hdet := congrArg det hmul
  rw [det_mul, det_blockLower_zero, det_one, CRing.mul_one, CRing.one_mul, det_blockUpper_zero] at hdet
  exact hdet

/-- Exact unimodular right Block-Schur complement over ANY commutative ring `R`. -/
theorem det_block_schur_right_unimodular {n : Nat} (A B C D U : Mat R n)
    (hAU : matMul A U = B) :
    det (blockMat A B C D) = CRing.mul (det A) (det (matSub D (matMul C U))) := by
  have hmul : matMul (blockMat A B C D) (blockMat (matOne n) (matNeg U) (matZero n) (matOne n)) =
              blockMat A (matZero n) C (matSub D (matMul C U)) := by
    rw [blockMat_mul, matMul_one_right, matMul_zero_right, matAdd_zero_right,
        matMul_neg_right, matMul_one_right,
        matMul_one_right, matMul_zero_right, matAdd_zero_right,
        matMul_neg_right, matMul_one_right]
    congr 1
    · funext i j; unfold matAdd matNeg matZero; rw [hAU]; exact CRing.add_left_neg (B i j)
    · funext i j; unfold matAdd matNeg matSub CRing.sub; exact CRing.add_comm _ _
  have hdet := congrArg det hmul
  rw [det_mul, det_blockUpper_zero, det_one, CRing.mul_one, CRing.mul_one, det_blockLower_zero] at hdet
  exact hdet

/-- Exact division-free scaled left Block-Schur complement over ANY commutative ring `R`. -/
theorem det_block_schur_left_scaled {n : Nat} (A B C D L : Mat R n) (s : R)
    (hLA : matMul L A = matSmul s C) :
    CRing.mul (CRing.pow s n) (det (blockMat A B C D)) =
    CRing.mul (det A) (det (matSub (matSmul s D) (matMul L B))) := by
  have hmul : matMul (blockMat (matOne n) (matZero n) (matNeg L) (matSmul s (matOne n))) (blockMat A B C D) =
              blockMat A B (matZero n) (matSub (matSmul s D) (matMul L B)) := by
    rw [blockMat_mul, matMul_one_left, matMul_zero_left, matAdd_zero_right,
        matMul_one_left, matMul_zero_left, matAdd_zero_right,
        matMul_neg_left, matMul_smul_left, matMul_one_left,
        matMul_neg_left, matMul_smul_left, matMul_one_left]
    congr 1
    · funext i j; unfold matAdd matNeg matZero; rw [hLA]; exact CRing.add_left_neg _
    · funext i j; unfold matAdd matNeg matSub CRing.sub; exact CRing.add_comm _ _
  have hdet := congrArg det hmul
  rw [det_mul, det_blockLower_zero, det_one, det_smul, det_one, CRing.mul_one, CRing.one_mul,
      det_blockUpper_zero] at hdet
  exact hdet

/-- Exact division-free scaled right Block-Schur complement over ANY commutative ring `R`. -/
theorem det_block_schur_right_scaled {n : Nat} (A B C D U : Mat R n) (s : R)
    (hAU : matMul A U = matSmul s B) :
    CRing.mul (CRing.pow s n) (det (blockMat A B C D)) =
    CRing.mul (det A) (det (matSub (matSmul s D) (matMul C U))) := by
  have hmul : matMul (blockMat A B C D) (blockMat (matOne n) (matNeg U) (matZero n) (matSmul s (matOne n))) =
              blockMat A (matZero n) C (matSub (matSmul s D) (matMul C U)) := by
    rw [blockMat_mul, matMul_one_right, matMul_zero_right, matAdd_zero_right,
        matMul_neg_right, matMul_smul_right, matMul_one_right,
        matMul_one_right, matMul_zero_right, matAdd_zero_right,
        matMul_neg_right, matMul_smul_right, matMul_one_right]
    congr 1
    · funext i j; unfold matAdd matNeg matZero; rw [hAU]; exact CRing.add_left_neg _
    · funext i j; unfold matAdd matNeg matSub CRing.sub; exact CRing.add_comm _ _
  have hdet := congrArg det hmul
  rw [det_mul, det_blockUpper_zero, det_one, det_smul, det_one, CRing.mul_one, CRing.one_mul,
      CRing.mul_comm (det (blockMat A B C D)), det_blockLower_zero] at hdet
  exact hdet

/-- Constructive universal scalar-top block determinant over EVERY `CRing R`
    (no division, works even when `γ = 0` or `γ` is a zero divisor!). -/
theorem det_block_scalar_top {n : Nat} (γ α : R) (C D : Mat R n) :
    det (blockMat (matSmul γ (matOne n)) (matSmul α (matOne n)) C D) =
    det (matSub (matSmul γ D) (matSmul α C)) := by
  -- Define intermediate matrix P r (0 ≤ r ≤ n) where columns < r are already Schur-eliminated!
  let P : Nat → Mat R (n + n) := fun r i j =>
    if hi : i.val < n then
      if i.val < r then
        if i = j then CRing.one else CRing.zero
      else
        if j.val = i.val then γ
        else if j.val = n + i.val then α
        else CRing.zero
    else
      if hj : j.val < n then
        if j.val < r then CRing.zero
        else C ⟨i.val - n, by omega⟩ ⟨j.val, hj⟩
      else
        if j.val - n < r then
          CRing.sub (CRing.mul γ (D ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩))
                    (CRing.mul α (C ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩))
        else
          D ⟨i.val - n, by omega⟩ ⟨j.val - n, by omega⟩
  have hP0 : P 0 = blockMat (matSmul γ (matOne n)) (matSmul α (matOne n)) C D := by
    funext i j; dsimp only [P]; unfold blockMat matSmul matOne
    by_cases hi : i.val < n
    · simp only [hi, dite_true, Nat.not_lt_zero, ite_false]
      by_cases hj : j.val < n
      · simp only [hj, dite_true]
        by_cases heq : j.val = i.val
        · have h1 : (⟨i.val, hi⟩ : Fin n) = ⟨j.val, hj⟩ := Fin.ext heq.symm
          simp [heq, h1, CRing.mul_one]
        · have h1 : (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val, hj⟩ := fun h => heq (congrArg Fin.val h).symm
          have h2 : j.val ≠ n + i.val := by omega
          simp [heq, h1, h2, CRing.mul_zero]
      · simp only [hj, dite_false]
        have h1 : j.val ≠ i.val := by omega
        by_cases heq : j.val = n + i.val
        · have h2 : (⟨i.val, hi⟩ : Fin n) = ⟨j.val - n, by omega⟩ := Fin.ext (by simp; omega)
          have hn0 : n ≠ 0 := by omega
          simp [heq, h2, hn0, CRing.mul_one]
        · have h2 : (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val - n, by omega⟩ := fun h => heq (by have := congrArg Fin.val h; simp at this; omega)
          simp [h1, heq, h2, CRing.mul_zero]
    · simp only [hi, dite_false]
      by_cases hj : j.val < n <;> simp [hj]
  have hPn : P n = blockMat (matOne n) (matZero n) (matZero n) (matSub (matSmul γ D) (matSmul α C)) := by
    funext i j; dsimp only [P]; unfold blockMat matOne matZero matSub matSmul
    by_cases hi : i.val < n
    · simp only [hi, dite_true, ite_true]
      by_cases hj : j.val < n
      · simp only [hj, dite_true]
        have hiff : i = j ↔ (⟨i.val, hi⟩ : Fin n) = ⟨j.val, hj⟩ := by
          constructor
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
          · intro h; apply Fin.ext; have hv := congrArg Fin.val h; exact hv
        by_cases h : i = j
        · simp [h]
        · have h' : (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val, hj⟩ := fun hc => h (hiff.mpr hc)
          simp [h, h']
      · simp only [hj, dite_false]
        have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
        simp [hne]
    · simp only [hi, dite_false]
      by_cases hj : j.val < n
      · simp [hj]
      · have hlt : j.val - n < n := by omega
        simp [hj, hlt]
  -- Inductive step: det (P r) = det (P (r + 1)) for r < n!
  have hstep : ∀ (r : Nat), r < n → det (P r) = det (P (r + 1)) := by
    intro r hr
    let rowIdx : Fin (n + n) := ⟨r, by omega⟩
    let colIdx : Fin (n + n) := ⟨n + r, by omega⟩
    have hrc_ne : rowIdx ≠ colIdx := by intro h; have := congrArg Fin.val h; simp [rowIdx, colIdx] at this; omega
    -- Split row r of P r as γ * e_r + α * e_{n+r}!
    let Q1 : Mat R (n + n) := fun i j =>
      if i = rowIdx then (if j = rowIdx then CRing.one else CRing.zero) else P r i j
    let Q2 : Mat R (n + n) := fun i j =>
      if i = rowIdx then (if j = colIdx then CRing.one else CRing.zero) else P r i j
    let M1 : Mat R (n + n) := fun i j =>
      if i = rowIdx then CRing.mul γ (Q1 i j) else P r i j
    let M2 : Mat R (n + n) := fun i j =>
      if i = rowIdx then CRing.mul α (Q2 i j) else P r i j
    have hsplit : det (P r) = CRing.add (det M1) (det M2) := by
      apply det_row_add rowIdx (P r) M1 M2
      · intro i j hi; dsimp only [M1, M2]; simp [hi]
      · intro j; dsimp only [M1, M2, Q1, Q2, P]
        have h1 : rowIdx.val < n := hr
        have h2 : ¬ (rowIdx.val < r) := by simp [rowIdx]
        simp only [ite_true, h1, dite_true, h2, ite_false]
        by_cases hj1 : j = rowIdx
        · subst hj1
          simp [rowIdx, hrc_ne, CRing.mul_one, CRing.mul_zero, CRing.add_zero]
        · by_cases hj2 : j = colIdx
          · subst hj2
            have hn0 : n ≠ 0 := by omega
            simp [rowIdx, colIdx, Ne.symm hrc_ne, hn0, CRing.mul_one, CRing.mul_zero, CRing.zero_add]
          · have hv1 : j.val ≠ rowIdx.val := fun h => hj1 (Fin.ext h)
            have hv2 : j.val ≠ n + rowIdx.val := fun h => hj2 (Fin.ext (by simp [colIdx]; exact h))
            simp [hj1, hj2, hv1, hv2, CRing.mul_zero, CRing.add_zero]
    -- M1 has row r = γ * (row r of Q1), so det M1 = γ * det Q1
    have hM1 : det M1 = CRing.mul γ (det Q1) := by
      apply det_row_smul rowIdx γ M1 Q1
      · intro i j hi; dsimp only [M1, Q1]; simp [hi]
      · intro j; dsimp only [M1]; simp
    -- M2 has row r = α * (row r of Q2), so det M2 = α * det Q2
    have hM2 : det M2 = CRing.mul α (det Q2) := by
      apply det_row_smul rowIdx α M2 Q2
      · intro i j hi; dsimp only [M2, Q2]; simp [hi]
      · intro j; dsimp only [M2]; simp
    -- In Q1, absorb γ into colIdx (= n + r) and zero out column rowIdx below row r!
    let R1 : Mat R (n + n) := fun i j =>
      if j = colIdx then CRing.mul γ (Q1 i colIdx)
      else if j = rowIdx then (if i = rowIdx then CRing.one else CRing.zero)
      else Q1 i j
    have hR1 : CRing.mul γ (det Q1) = det R1 := by
      let Q1z : Mat R (n + n) := fun i j =>
        if j = rowIdx then (if i = rowIdx then CRing.one else CRing.zero) else Q1 i j
      have hcz : det Q1 = det Q1z := by
        apply det_congr_of_unit_row rowIdx Q1 Q1z
        · intro j; dsimp only [Q1]; simp
        · intro j; dsimp only [Q1z, Q1]
          by_cases hj : j = rowIdx <;> simp [hj]
        · intro i j hj; dsimp only [Q1z]; simp [hj]
      rw [hcz]
      symm
      apply det_col_smul colIdx γ R1 Q1z
      · intro i j hj; dsimp only [R1, Q1z]; simp [hj]
      · intro i; dsimp only [R1, Q1z]; simp [Ne.symm hrc_ne]
    -- In Q2, swap columns rowIdx and colIdx (negates det!), absorb (-α) into colIdx, zero column rowIdx!
    let Q2sw : Mat R (n + n) := fun i j => Q2 i (swapFin rowIdx colIdx j)
    have hQ2sw : det Q2 = CRing.neg (det Q2sw) := by
      have h := det_col_swap rowIdx colIdx hrc_ne Q2
      rw [h, CRing.neg_neg]
    let R2 : Mat R (n + n) := fun i j =>
      if j = colIdx then CRing.mul (CRing.neg α) (Q2sw i colIdx)
      else if j = rowIdx then (if i = rowIdx then CRing.one else CRing.zero)
      else Q2sw i j
    have hR2 : CRing.mul α (det Q2) = det R2 := by
      rw [hQ2sw, CRing.mul_neg, ← CRing.neg_mul]
      let Q2z : Mat R (n + n) := fun i j =>
        if j = rowIdx then (if i = rowIdx then CRing.one else CRing.zero) else Q2sw i j
      have hcz : det Q2sw = det Q2z := by
        apply det_congr_of_unit_row rowIdx Q2sw Q2z
        · intro j; dsimp only [Q2sw, Q2]
          simp only [ite_true]
          by_cases hj : j = rowIdx
          · subst hj; rw [swapFin_left]; simp
          · have hne : swapFin rowIdx colIdx j ≠ colIdx := by
              intro h; exact hj (swapFin_inj rowIdx colIdx (h.trans (swapFin_left rowIdx colIdx).symm))
            simp [hj, hne]
        · intro j; dsimp only [Q2z, Q2sw, Q2]
          by_cases hj : j = rowIdx
          · simp [hj]
          · simp only [hj, ite_false, ite_true]
            have hne : swapFin rowIdx colIdx j ≠ colIdx := by
              intro h; exact hj (swapFin_inj rowIdx colIdx (h.trans (swapFin_left rowIdx colIdx).symm))
            simp [hne]
        · intro i j hj; dsimp only [Q2z]; simp [hj]
      rw [hcz]
      symm
      apply det_col_smul colIdx (CRing.neg α) R2 Q2z
      · intro i j hj; dsimp only [R2, Q2z]; simp [hj]
      · intro i; dsimp only [R2, Q2z]; simp [Ne.symm hrc_ne]
    -- Now combine det R1 + det R2 = det (P (r + 1)) along column colIdx!
    rw [hsplit, hM1, hM2, hR1, hR2]
    symm
    apply det_col_add colIdx (P (r + 1)) R1 R2
    · intro i j hj
      have hne_c : j ≠ colIdx := hj
      by_cases hjr : j = rowIdx
      · subst hjr
        dsimp only [P, R1, R2]
        simp only [hrc_ne, ite_false, ite_true]
        by_cases hi : i.val < n
        · simp only [hi, dite_true]
          by_cases hir : i.val < r + 1
          · simp only [hir, ite_true]
            by_cases hieq : i = rowIdx
            · subst hieq; simp
            · simp
          · simp only [hir, ite_false]
            have h1 : rowIdx.val ≠ i.val := by simp [rowIdx]; omega
            have h2 : rowIdx.val ≠ n + i.val := by simp [rowIdx]; omega
            have h3 : i ≠ rowIdx := by intro h; have := congrArg Fin.val h; simp [rowIdx] at this; omega
            simp [h1, h2, h3]
        · simp only [hi, dite_false]
          have h1 : rowIdx.val < n := hr
          have h2 : rowIdx.val < r + 1 := by simp [rowIdx]
          have h3 : i ≠ rowIdx := by intro h; have := congrArg Fin.val h; simp [rowIdx] at this; omega
          simp [h1, h2, h3]
      · dsimp only [R1, R2, Q2sw, Q1, Q2]
        have hsw : swapFin rowIdx colIdx j = j := by unfold swapFin; simp [hjr, hne_c]
        simp only [hne_c, hjr, hsw, ite_false]
        by_cases hir : i = rowIdx
        · subst hir
          dsimp only [P]
          have h1 : rowIdx.val < n := hr
          have h2 : rowIdx.val < r + 1 := by simp [rowIdx]
          have h3 : rowIdx ≠ j := Ne.symm hjr
          simp [h1, h2, h3]
        · simp only [hir, ite_false]
          have hsame : P (r + 1) i j = P r i j := by
            dsimp only [P]
            by_cases hi : i.val < n
            · simp only [hi, dite_true]
              have hne_i : i.val ≠ r := fun h => hir (Fin.ext h)
              have hiff : i.val < r + 1 ↔ i.val < r := by omega
              by_cases hc : i.val < r <;> simp [hc, hiff]
            · simp only [hi, dite_false]
              by_cases hjlt : j.val < n
              · simp only [hjlt, dite_true]
                have hne_j : j.val ≠ r := fun h => hjr (Fin.ext h)
                have hiff : j.val < r + 1 ↔ j.val < r := by omega
                by_cases hc : j.val < r <;> simp [hc, hiff]
              · simp only [hjlt, dite_false]
                have hne_j : j.val - n ≠ r := by
                  intro h; apply hne_c; apply Fin.ext; simp [colIdx]; omega
                have hiff : j.val - n < r + 1 ↔ j.val - n < r := by omega
                by_cases hc : j.val - n < r <;> simp [hc, hiff]
          exact ⟨hsame, hsame⟩
    · intro i
      dsimp only [R1, R2, Q2sw, Q1, Q2]
      rw [swapFin_right]
      simp only [ite_true]
      by_cases hir : i = rowIdx
      · subst hir
        dsimp only [P]
        have h1 : rowIdx.val < n := hr
        have h2 : rowIdx.val < r + 1 := by simp [rowIdx]
        simp [h1, h2, hrc_ne, Ne.symm hrc_ne, CRing.mul_zero, CRing.add_zero]
      · simp only [hir, ite_false]
        dsimp only [P]
        by_cases hi : i.val < n
        · simp only [hi, dite_true]
          have hne_i : i.val ≠ r := fun h => hir (Fin.ext h)
          by_cases hilt : i.val < r
          · have hilt1 : i.val < r + 1 := by omega
            have hne1 : i ≠ colIdx := by intro h; have := congrArg Fin.val h; simp [colIdx] at this; omega
            have hne2 : i ≠ rowIdx := hir
            simp [hilt, hilt1, hne1, hne2, CRing.mul_zero, CRing.add_zero]
          · have hnot1 : ¬ (i.val < r + 1) := by omega
            have h1 : colIdx.val ≠ i.val := by simp [colIdx]; omega
            have h2 : colIdx.val ≠ n + i.val := by simp [colIdx]; omega
            have h3 : rowIdx.val ≠ i.val := by simp [rowIdx]; omega
            have h4 : rowIdx.val ≠ n + i.val := by simp [rowIdx]; omega
            simp [hilt, hnot1, h1, h2, h3, h4, CRing.mul_zero, CRing.add_zero]
        · simp only [hi, dite_false]
          have hcn : ¬ (colIdx.val < n) := by simp [colIdx]
          have hrn : rowIdx.val < n := hr
          have hsub : colIdx.val - n = r := by simp [colIdx]
          have hlt1 : colIdx.val - n < r + 1 := by omega
          have hnot : ¬ (colIdx.val - n < r) := by omega
          have hnotr : ¬ (rowIdx.val < r) := by simp [rowIdx]
          simp only [hcn, hrn, dite_false, dite_true, hlt1, hnot, hnotr, ite_true, ite_false]
          have hfin : (⟨colIdx.val - n, by omega⟩ : Fin n) = ⟨rowIdx.val, hrn⟩ := Fin.ext (by simp [colIdx, rowIdx])
          rw [hfin, CRing.neg_mul]; rfl
  -- Chain hstep from 0 to n!
  have hchain : ∀ (r : Nat), r ≤ n → det (P 0) = det (P r) := by
    intro r
    induction r with
    | zero => intro _; rfl
    | succ r ih => intro hr; rw [ih (Nat.le_of_lt hr), hstep r hr]
  rw [← hP0, hchain n (Nat.le_refl n), hPn, det_blockUpper_zero, det_one, CRing.one_mul]

/-- Universal Proportional-Block Schur Renormalization Law over EVERY commutative ring `R`
    (works even when `γ = 0` or `γ` is a zero divisor, with ZERO division and ZERO cancellation!). -/
theorem det_block_schur_proportional {n : Nat} (γ α β : R) (A D : Mat R n) :
    det (blockMat (matSmul γ A) (matSmul α A) (matSmul β A) D) =
    CRing.mul (det A) (det (matSub (matSmul γ D) (matSmul (CRing.mul α β) A))) := by
  have hfac : blockMat (matSmul γ A) (matSmul α A) (matSmul β A) D =
              matMul (blockMat A (matZero n) (matZero n) (matOne n))
                     (blockMat (matSmul γ (matOne n)) (matSmul α (matOne n)) (matSmul β A) D) := by
    rw [blockMat_mul, matMul_smul_right, matMul_one_right, matMul_zero_left, matAdd_zero_right,
        matMul_smul_right, matMul_one_right, matMul_zero_left, matAdd_zero_right,
        matMul_zero_left, matMul_one_left, matAdd_zero_left,
        matMul_zero_left, matMul_one_left, matAdd_zero_left]
  rw [hfac, det_mul, det_blockUpper_zero, det_one, CRing.mul_one, det_block_scalar_top]
  congr 1; congr 1
  funext i j; unfold matSub matSmul
  congr 1; exact (CRing.mul_assoc α β (A i j)).symm

end MatDefs
/-- **AUTOMATIC INVERTIBILITY DICHOTOMY LIFTER** over any `IntDomain R`. -/
theorem det_bitSliced_schur_zero_iff {R : Type u} [IntDomain R]
    {P : Nat → Type v}
    (M : ∀ k, P k → Mat R (pow2 k))
    (base : P 0 → R)
    (step : ∀ k, P (k + 1) → P k × P k)
    (hbase : ∀ p : P 0, det (M 0 p) = base p)
    (hstep : ∀ k (p : P (k + 1)),
      det (M (k + 1) p) = CRing.mul (det (M k (step k p).1)) (det (M k (step k p).2)))
    (k : Nat) (p : P k) :
    det (M k p) = CRing.zero ↔ ∃ s : Fin (pow2 k), evalBitTree base step k p s = CRing.zero := by
  rw [det_bitSliced_schur_lift M base step hbase hstep k p, prodFin_eq_zero_iff]

/-! ## Section 4: Pure-Silicon Bitwise Primitives & Family I (Non-Uniform HCB Weighted Kernel) -/

section FamilyI
variable {R : Type u} [CRing R]

/-- 1-step Block-Schur determinant recurrence for Family I (over ANY `CRing R`). -/
theorem det_hcbMat_succ (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) :
    det (hcbMat γ α β δ (k + 1) f) =
    CRing.mul (det (hcbMat γ α β δ k f))
              (det (hcbMat γ α β δ k (hcbRenorm γ α β δ (k + 1) f))) := by
  have h1 : (hcbMat γ α β δ (k + 1) f : Mat R (pow2 k + pow2 k)) =
            blockMat (matSmul (γ (k + 1)) (hcbMat γ α β δ k f))
                     (matSmul (α (k + 1)) (hcbMat γ α β δ k f))
                     (matSmul (β (k + 1)) (hcbMat γ α β δ k f))
                     (matSmul (f (k + 1)) (kronBitMat γ α β δ k)) :=
    hcbMat_succ_eq_block γ α β δ k f
  have h2 := det_block_schur_proportional (γ (k + 1)) (α (k + 1)) (β (k + 1))
               (hcbMat γ α β δ k f) (matSmul (f (k + 1)) (kronBitMat γ α β δ k))
  have h3 := hcbMat_schur_closure γ α β δ k f
  exact (congrArg det h1).trans (h2.trans (by rw [h3]))

/-! ### Explicit Closed-Form Bitmask Factor `hcbMaskFactor` & Telescoping Proof -/

/-- **MAIN THEOREM I (`det_hcbMat_closed_form`)**:
    For ALL `k : Nat`, ALL profiles `f : Nat -> R`, and ALL bit-position weight sequences
    `γ, α, β, δ : Nat -> R` over ANY commutative ring `R` (including rings with zero divisors
    and `γ m = 0`), the exact Leibniz determinant of the `2^k × 2^k` Highest-Common-Bit
    Weighted Matrix equals the `2^k`-bitmask product of `hcbMaskFactor`. -/
theorem det_hcbMat_closed_form (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) :
    det (hcbMat γ α β δ k f) =
    prodFin (pow2 k) (fun s => hcbMaskFactor γ α β δ k f s.val) := by
  let base : (Nat → R) → R := fun f0 => f0 0
  let step : ∀ k, (Nat → R) → (Nat → R) × (Nat → R) :=
    fun k fk => (fk, hcbRenorm γ α β δ (k + 1) fk)
  have hlift := det_bitSliced_schur_lift (P := fun _ => Nat → R)
    (M := fun k fk => hcbMat γ α β δ k fk)
    base step
    (fun f0 => det_hcbMat_zero γ α β δ f0)
    (fun k fk => det_hcbMat_succ γ α β δ k fk)
    k f
  rw [hlift]
  suffices heval : ∀ (m : Nat) (fm : Nat → R) (sm : Fin (pow2 m)),
      evalBitTree (P := fun _ => Nat → R) base step m fm sm = hcbMaskFactor γ α β δ m fm sm.val by
    exact prodFin_congr (fun s => heval k f s)
  intro m
  induction m with
  | zero =>
    intro fm sm
    unfold evalBitTree hcbMaskFactor negPProd sumFin
    dsimp only [base]
    rw [CRing.one_mul, CRing.add_zero]
  | succ m ihm =>
    intro fm sm
    unfold evalBitTree
    by_cases hlt : sm.val < pow2 m
    · simp only [hlt, dite_true]
      rw [ihm (step m fm).1 ⟨sm.val, hlt⟩]
      exact (hcbMaskFactor_low γ α β δ m fm sm.val hlt).symm
    · simp only [hlt, dite_false]
      have hsub : sm.val - pow2 m < pow2 m := by have := sm.isLt; unfold pow2 at this; omega
      rw [ihm (step m fm).2 ⟨sm.val - pow2 m, hsub⟩]
      dsimp only [step]
      rw [hcbMaskFactor_renorm γ α β δ m fm (sm.val - pow2 m) hsub]
      congr 1; omega

theorem det_msbAnd_closed_form (k : Nat) (f : Nat → R) :
    det (msbAndMat k f) =
    if k = 0 then f 0
    else if k = 1 then CRing.mul (f 0) (CRing.sub (f 1) (f 0))
    else CRing.neg (CRing.mul (f 0) (prodFin k (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (k - 1 - j.val))))) := by
  have hrec : ∀ m (fm : Nat → R),
      det (msbAndMat (m + 1) fm) =
      CRing.mul (det (msbAndMat m fm)) (det (msbAndMat m (fun j => CRing.sub (fm (m + 1)) (fm j)))) := by
    intro m fm
    rw [msbAndMat_eq_hcb (m + 1), det_hcbMat_succ, ← msbAndMat_eq_hcb, ← msbAndMat_eq_hcb]
    apply congrArg (CRing.mul _)
    apply congrArg det
    apply congrArg (msbAndMat m)
    funext j; unfold hcbRenorm
    by_cases hj : j = 0
    · simp only [hj, ite_true, CRing.one_mul]
    · simp only [hj, ite_false, CRing.one_mul]
  induction k generalizing f with
  | zero =>
    simp only [ite_true]
    rw [msbAndMat_eq_hcb, det_hcbMat_zero]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
      rw [hrec 0 f, ih f, ih (fun j => CRing.sub (f 1) (f j))]
      simp only [ite_true]
    | succ k' =>
      cases k' with
      | zero =>
        simp only [show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false]
        rw [hrec 1 f, ih f, ih (fun j => CRing.sub (f 2) (f j))]
        simp only [show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
        rw [sub_sub_sub_eq_neg]
        let A := f 0
        let B := CRing.sub (f 1) (f 0)
        let C := CRing.sub (f 2) (f 0)
        have hrhs : prodFin 2 (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (2 - 1 - j.val))) =
                    CRing.mul (CRing.mul B B) C := by
          change CRing.mul (CRing.mul CRing.one (CRing.pow B 2)) (CRing.pow C 1) = CRing.mul (CRing.mul B B) C
          rw [CRing.one_mul, CRing.pow_one, CRing.pow_succ, CRing.pow_one]
        rw [hrhs]
        change CRing.mul (CRing.mul A B) (CRing.mul C (CRing.neg B)) =
               CRing.neg (CRing.mul A (CRing.mul (CRing.mul B B) C))
        rw [CRing.mul_neg, CRing.mul_neg]
        congr 1
        rw [CRing.mul_assoc A B (CRing.mul C B), CRing.mul_comm C B, ← CRing.mul_assoc B B C]
      | succ k'' =>
        let m := k'' + 2
        have hm0 : m ≠ 0 := by omega
        have hm1 : m ≠ 1 := by omega
        have hm'0 : m + 1 ≠ 0 := by omega
        have hm'1 : m + 1 ≠ 1 := by omega
        change det (msbAndMat (m + 1) f) =
               if m + 1 = 0 then f 0
               else if m + 1 = 1 then CRing.mul (f 0) (CRing.sub (f 1) (f 0))
               else CRing.neg (CRing.mul (f 0) (prodFin (m + 1) (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m + 1 - 1 - j.val)))))
        simp only [hm'0, hm'1, ite_false]
        rw [hrec m f, ih f, ih (fun j => CRing.sub (f (m + 1)) (f j))]
        have hite_m : (if m = 0 then f 0
                       else if m = 1 then CRing.mul (f 0) (CRing.sub (f 1) (f 0))
                       else CRing.neg (CRing.mul (f 0) (prodFin m (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - 1 - j.val)))))) =
                      CRing.neg (CRing.mul (f 0) (prodFin m (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - 1 - j.val))))) := by
          simp only [hm0, hm1, ite_false]
        have hite_g : (if m = 0 then CRing.sub (f (m + 1)) (f 0)
                       else if m = 1 then CRing.mul (CRing.sub (f (m + 1)) (f 0)) (CRing.sub (CRing.sub (f (m + 1)) (f 1)) (CRing.sub (f (m + 1)) (f 0)))
                       else CRing.neg (CRing.mul (CRing.sub (f (m + 1)) (f 0))
                         (prodFin m (fun j => CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (j.val + 1))) (CRing.sub (f (m + 1)) (f 0))) (pow2 (m - 1 - j.val)))))) =
                      CRing.neg (CRing.mul (CRing.sub (f (m + 1)) (f 0))
                        (prodFin m (fun j => CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (j.val + 1))) (CRing.sub (f (m + 1)) (f 0))) (pow2 (m - 1 - j.val))))) := by
          simp only [hm0, hm1, ite_false]
        rw [hite_m, hite_g, CRing.neg_mul_neg]
        have hneg_pow_even : ∀ (e : Nat) (x : R), CRing.pow (CRing.neg x) (e + e) = CRing.pow x (e + e) := by
          intro e x
          rw [CRing.pow_add, CRing.pow_add, ← CRing.mul_pow, CRing.neg_mul_neg, CRing.mul_pow]
        have hprod_g :
            prodFin m (fun j => CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (j.val + 1)))
                                                     (CRing.sub (f (m + 1)) (f 0)))
                                          (pow2 (m - 1 - j.val))) =
            CRing.neg (prodFin m (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - 1 - j.val)))) := by
          change CRing.mul
            (prodFin (k'' + 1) (fun j => CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (j.val + 1)))
                                                              (CRing.sub (f (m + 1)) (f 0)))
                                                   (pow2 (m - 1 - j.val))))
            (CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (k'' + 1 + 1)))
                                  (CRing.sub (f (m + 1)) (f 0)))
                       (pow2 (m - 1 - (k'' + 1)))) =
            CRing.neg (CRing.mul
              (prodFin (k'' + 1) (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - 1 - j.val))))
              (CRing.pow (CRing.sub (f (k'' + 1 + 1)) (f 0)) (pow2 (m - 1 - (k'' + 1)))))
          have hlo : prodFin (k'' + 1) (fun j => CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (j.val + 1)))
                                                                      (CRing.sub (f (m + 1)) (f 0)))
                                                           (pow2 (m - 1 - j.val))) =
                     prodFin (k'' + 1) (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0))
                                                           (pow2 (m - 1 - j.val))) := by
            apply prodFin_congr; intro j
            rw [sub_sub_sub_eq_neg]
            have hexp : m - 1 - j.val = (m - 2 - j.val) + 1 := by omega
            rw [hexp]; unfold pow2
            exact hneg_pow_even (pow2 (m - 2 - j.val)) _
          have hlast : CRing.pow (CRing.sub (CRing.sub (f (m + 1)) (f (k'' + 1 + 1)))
                                            (CRing.sub (f (m + 1)) (f 0)))
                                 (pow2 (m - 1 - (k'' + 1))) =
                       CRing.neg (CRing.pow (CRing.sub (f (k'' + 1 + 1)) (f 0)) (pow2 (m - 1 - (k'' + 1)))) := by
            have h0 : m - 1 - (k'' + 1) = 0 := by omega
            rw [h0, pow2, CRing.pow_one, CRing.pow_one]
            exact sub_sub_sub_eq_neg
          rw [hlo, hlast, CRing.mul_neg]
        rw [hprod_g, CRing.mul_neg, CRing.mul_neg]
        congr 1
        let P := prodFin m (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - 1 - j.val)))
        have hPP : CRing.mul P P =
                   prodFin m (fun j => CRing.pow (CRing.sub (f (j.val + 1)) (f 0)) (pow2 (m - j.val))) := by
          dsimp only [P]
          rw [← prodFin_mul]
          apply prodFin_congr; intro j
          rw [← CRing.pow_add]
          have hexp : m - j.val = (m - 1 - j.val) + 1 := by omega
          rw [hexp]; rfl
        simp only [prodFin, Fin.val_castSucc, Fin.val_last]
        have hsub0 : m + 1 - 1 - m = 0 := by omega
        have hsub_cast : ∀ j : Fin m, m + 1 - 1 - j.val = m - j.val := fun _ => by omega
        have hrhs : prodFin m (fun i => CRing.pow (CRing.sub (f (i.val + 1)) (f 0)) (pow2 (m + 1 - 1 - i.val))) =
                    CRing.mul P P := by
          rw [hPP]
          apply prodFin_congr; intro j
          rw [hsub_cast j]
        rw [hsub0, pow2, CRing.pow_one, hrhs]
        change CRing.mul (CRing.mul (f 0) P) (CRing.mul (CRing.sub (f (m + 1)) (f 0)) P) =
               CRing.mul (f 0) (CRing.mul (CRing.mul P P) (CRing.sub (f (m + 1)) (f 0)))
        rw [CRing.mul_assoc (f 0) P (CRing.mul (CRing.sub (f (m + 1)) (f 0)) P),
            CRing.mul_comm (CRing.sub (f (m + 1)) (f 0)) P,
            ← CRing.mul_assoc P P (CRing.sub (f (m + 1)) (f 0))]

end FamilyI
/-- **COROLLARY I-B (Exact Bitmask Invertibility Dichotomy for Family I over Integral Domains)**:
    Over ANY integral domain `R` (e.g., `Int`), `det (hcbMat γ α β δ k f) = 0` IF AND ONLY IF
    there exists a `k`-bit mask `s < 2^k` with `hcbMaskFactor γ α β δ k f s = 0`! -/
theorem det_hcbMat_eq_zero_iff {R : Type u} [IntDomain R]
    (γ α β δ : Nat → R) (k : Nat) (f : Nat → R) :
    det (hcbMat γ α β δ k f) = CRing.zero ↔
    ∃ s : Fin (pow2 k), hcbMaskFactor γ α β δ k f s.val = CRing.zero := by
  rw [det_hcbMat_closed_form, prodFin_eq_zero_iff]

theorem det_popMsbAnd_closed_form (k : Nat) (f : Nat → Int) :
    det (popMsbAndMat k f) =
    prodFin (R := Int) (pow2 k)
      (fun s => hcbMaskFactor (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) k f s.val) := by
  rw [popMsbAndMat_eq_hcb, det_hcbMat_closed_form]

/-! ## Section 5: Family II — Weighted Boolean-Poset Subset-Disjointness Hybrid Kernel -/

section FamilyII
variable {R : Type u} [CRing R]

/-- 1-step Right Unimodular Block-Schur determinant recurrence for Family II! -/
theorem det_boolHybridMat_succ (u w d : Nat → R) (k : Nat) (a c : R) :
    det (boolHybridMat u w d (k + 1) a c) =
    CRing.mul (det (boolHybridMat u w d k a c))
              (det (boolHybridMat u w d k (CRing.mul (d (k + 1)) a)
                                          (CRing.mul (CRing.neg (CRing.mul (u (k + 1)) (w (k + 1)))) c))) := by
  have h1 : (boolHybridMat u w d (k + 1) a c : Mat R (pow2 k + pow2 k)) =
      blockMat (boolHybridMat u w d k a c)
               (matSmul (u (k + 1)) (boolHybridMat u w d k a c))
               (fun x y => CRing.mul (CRing.mul (w (k + 1)) c) (disjWeight u w k x.val y.val))
               (fun x y => CRing.mul (CRing.mul (d (k + 1)) a) (subsetWeight u d k x.val y.val)) :=
    boolHybridMat_succ_eq_block u w d k a c
  have h2 := det_block_schur_right_unimodular
    (A := boolHybridMat u w d k a c)
    (B := matSmul (u (k + 1)) (boolHybridMat u w d k a c))
    (C := fun x y => CRing.mul (CRing.mul (w (k + 1)) c) (disjWeight u w k x.val y.val))
    (D := fun x y => CRing.mul (CRing.mul (d (k + 1)) a) (subsetWeight u d k x.val y.val))
    (U := matSmul (u (k + 1)) (matOne (pow2 k)))
    (by rw [matMul_smul_right, matMul_one_right])
  refine (congrArg det h1).trans (h2.trans ?_)
  congr 1; congr 1
  rw [matMul_smul_right, matMul_one_right]
  funext x y
  unfold matSub matSmul boolHybridMat CRing.sub
  congr 1
  dsimp only
  rw [← CRing.mul_assoc (u (k + 1)), ← CRing.mul_assoc (u (k + 1)), CRing.neg_mul, CRing.neg_mul]

/-- **MAIN THEOREM II (`det_boolHybridMat_closed_form`)**:
    Proved through the SAME reusable `det_bitSliced_schur_lift` engine over ANY `CRing R`! -/
theorem det_boolHybridMat_closed_form (u w d : Nat → R) (k : Nat) (a c : R) :
    det (boolHybridMat u w d k a c) =
    prodFin (pow2 k) (fun s => boolHybridMaskFactor u w d k a c s.val) := by
  let base : R × R → R := fun p => CRing.add p.1 p.2
  let step : ∀ k, R × R → (R × R) × (R × R) :=
    fun k p => (p, (CRing.mul (d (k + 1)) p.1, CRing.mul (CRing.neg (CRing.mul (u (k + 1)) (w (k + 1)))) p.2))
  have hlift := det_bitSliced_schur_lift (P := fun _ => R × R)
    (M := fun k p => boolHybridMat u w d k p.1 p.2)
    base step
    (fun p => det_boolHybridMat_zero u w d p.1 p.2)
    (fun k p => det_boolHybridMat_succ u w d k p.1 p.2)
    k (a, c)
  rw [hlift]
  suffices heval : ∀ (m : Nat) (p : R × R) (sm : Fin (pow2 m)),
      evalBitTree (P := fun _ => R × R) base step m p sm = boolHybridMaskFactor u w d m p.1 p.2 sm.val by
    exact prodFin_congr (fun s => heval k (a, c) s)
  intro m
  induction m with
  | zero =>
    intro p sm
    unfold evalBitTree boolHybridMaskFactor prodFin
    dsimp only [base]
    rw [CRing.mul_one, CRing.mul_one]
  | succ m ihm =>
    intro p sm
    unfold evalBitTree
    by_cases hlt : sm.val < pow2 m
    · simp only [hlt, dite_true]
      rw [ihm (step m p).1 ⟨sm.val, hlt⟩]
      dsimp only [step]
      unfold boolHybridMaskFactor
      simp only [prodFin, Fin.val_castSucc, Fin.val_last,
                 testBit_lt_pow2 m sm.val m hlt (Nat.le_refl m), Bool.false_eq_true, ite_false, CRing.mul_one]
    · simp only [hlt, dite_false]
      have hsub : sm.val - pow2 m < pow2 m := by have := sm.isLt; unfold pow2 at this; omega
      have hsm_eq : sm.val = pow2 m + (sm.val - pow2 m) := by omega
      have htbm : sm.val.testBit m = true := by rw [hsm_eq]; exact testBit_add_pow2_eq m _ hsub
      rw [ihm (step m p).2 ⟨sm.val - pow2 m, hsub⟩]
      dsimp only [step]
      unfold boolHybridMaskFactor
      simp only [prodFin, Fin.val_castSucc, Fin.val_last, htbm, ite_true]
      congr 1
      · have hlo : prodFin m (fun b => if sm.val.testBit b.val then d (b.val + 1) else CRing.one) =
                   prodFin m (fun b => if (sm.val - pow2 m).testBit b.val then d (b.val + 1) else CRing.one) :=
          prodFin_congr (fun b => by
            have htb := testBit_add_pow2_lt m (sm.val - pow2 m) b.val b.isLt
            rw [← hsm_eq] at htb; rw [htb])
        rw [hlo, CRing.mul_comm (d (m + 1)) p.1, CRing.mul_assoc,
            CRing.mul_comm (d (m + 1)) (prodFin m _)]
      · have hlo : prodFin m (fun b => if sm.val.testBit b.val
                                       then CRing.neg (CRing.mul (u (b.val + 1)) (w (b.val + 1))) else CRing.one) =
                   prodFin m (fun b => if (sm.val - pow2 m).testBit b.val
                                       then CRing.neg (CRing.mul (u (b.val + 1)) (w (b.val + 1))) else CRing.one) :=
          prodFin_congr (fun b => by
            have htb := testBit_add_pow2_lt m (sm.val - pow2 m) b.val b.isLt
            rw [← hsm_eq] at htb; rw [htb])
        rw [hlo, CRing.mul_comm (CRing.neg (CRing.mul (u (m + 1)) (w (m + 1)))) p.2,
            CRing.mul_assoc, CRing.mul_comm (CRing.neg (CRing.mul (u (m + 1)) (w (m + 1)))) (prodFin m _)]

theorem det_subsetDisjMat_closed_form (k : Nat) (a c : R) :
    det (subsetDisjMat (k + 1) a c) =
    CRing.pow (CRing.sub (CRing.mul a a) (CRing.mul c c)) (pow2 k) := by
  induction k generalizing a c with
  | zero =>
    rw [subsetDisjMat_eq_boolHybrid, det_boolHybridMat_succ, det_boolHybridMat_zero,
        det_boolHybridMat_zero, CRing.one_mul, CRing.one_mul, CRing.neg_one_mul,
        pow2, CRing.pow_one]
    rw [CRing.left_distrib, CRing.right_distrib, CRing.right_distrib,
        CRing.mul_neg, CRing.mul_neg, CRing.mul_comm c a]
    unfold CRing.sub
    rw [CRing.add_assoc, ← CRing.add_assoc (CRing.mul a c), CRing.add_right_neg, CRing.zero_add]
  | succ k ih =>
    rw [subsetDisjMat_eq_boolHybrid, det_boolHybridMat_succ,
        ← subsetDisjMat_eq_boolHybrid, ← subsetDisjMat_eq_boolHybrid,
        CRing.one_mul, CRing.one_mul, CRing.neg_one_mul]
    rw [ih a c, ih a (CRing.neg c), CRing.neg_mul_neg]
    change CRing.mul (CRing.pow (CRing.sub (CRing.mul a a) (CRing.mul c c)) (pow2 k))
                     (CRing.pow (CRing.sub (CRing.mul a a) (CRing.mul c c)) (pow2 k)) =
           CRing.pow (CRing.sub (CRing.mul a a) (CRing.mul c c)) (pow2 k + pow2 k)
    rw [CRing.pow_add]

end FamilyII
/-- **COROLLARY II-B (Sharp Invertibility Dichotomy for `subsetDisjMat`)**:
    Over ANY integral domain `R` and ALL `k ≥ 1`,
    `det (subsetDisjMat (k + 1) a c) = 0 ↔ a = c ∨ a = -c`! -/
theorem det_subsetDisjMat_zero_iff {R : Type u} [IntDomain R] (k : Nat) (a c : R) :
    det (subsetDisjMat (k + 1) a c) = CRing.zero ↔ a = c ∨ a = CRing.neg c := by
  rw [det_subsetDisjMat_closed_form]
  have hpow_zero : ∀ (m : Nat) (x : R), m ≠ 0 → (CRing.pow x m = CRing.zero ↔ x = CRing.zero) := by
    intro m x hm
    induction m with
    | zero => exact absurd rfl hm
    | succ m ihm =>
      cases m with
      | zero => rw [CRing.pow_one]
      | succ m' =>
        rw [CRing.pow_succ]
        constructor
        · intro h
          rcases IntDomain.mul_eq_zero _ _ h with h1 | h2
          · exact (ihm (Nat.succ_ne_zero m')).mp h1
          · exact h2
        · intro h; subst h; exact CRing.mul_zero _
  rw [hpow_zero (pow2 k) _ (Nat.ne_of_gt (pow2_pos k))]
  have hfac : CRing.sub (CRing.mul a a) (CRing.mul c c) =
              CRing.mul (CRing.sub a c) (CRing.add a c) := by
    unfold CRing.sub
    rw [CRing.right_distrib, CRing.left_distrib, CRing.left_distrib, CRing.neg_mul,
        CRing.neg_mul, CRing.mul_comm c a, CRing.add_assoc, ← CRing.add_assoc (CRing.mul a c),
        CRing.add_right_neg, CRing.zero_add]
  rw [hfac]
  constructor
  · intro h
    rcases IntDomain.mul_eq_zero _ _ h with h1 | h2
    · left; exact (CRing.sub_eq_zero_iff a c).mp h1
    · right
      have h3 := CRing.neg_eq_of_add_eq_zero (R := R) (by rw [CRing.add_comm]; exact h2)
      exact h3.symm
  · rintro (rfl | rfl)
    · rw [CRing.sub_self, CRing.zero_mul]
    · rw [CRing.add_left_neg, CRing.mul_zero]

/-! ## Section 6: Kernel-Checked Non-Vacuity Witnesses, Delayed Singularity & Sharpness Counterexamples -/

theorem witness_fSing_k0 : det (popMsbAndMat 0 fSing) = 1 := by
  rw [det_popMsbAnd_closed_form]; decide

theorem witness_fSing_k1 : det (popMsbAndMat 1 fSing) = 2 := by
  rw [det_popMsbAnd_closed_form]; decide

theorem witness_fSing_k2 : det (popMsbAndMat 2 fSing) = 24 := by
  rw [det_popMsbAnd_closed_form]; decide

theorem witness_fSing_singular_all_ge3 (k : Nat) (hk : 3 ≤ k) :
    det (popMsbAndMat k fSing) = 0 := by
  change det (popMsbAndMat k fSing) = CRing.zero
  rw [popMsbAndMat_eq_hcb, det_hcbMat_eq_zero_iff]
  have h7lt : 7 < pow2 k := by
    rw [pow2_eq]
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  refine ⟨⟨7, h7lt⟩, ?_⟩
  suffices hred : ∀ (m : Nat), 3 ≤ m →
      hcbMaskFactor (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) m fSing 7 =
      hcbMaskFactor (R := Int) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) 3 fSing 7 by
    rw [hred k hk]; decide
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm3 : m = 2
    · subst hm3; rfl
    · have hge3 : 3 ≤ m := by omega
      have h7m : 7 < pow2 m := by
        rw [pow2_eq]; have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hge3; omega
      rw [hcbMaskFactor_low (R := Int) _ _ _ _ m fSing 7 h7m, ih hge3]

/-- Witness 2 (Zero-Divisor Ring `ZMod 5` = Z/6Z Non-Vacuity — Invertible Unit Determinant!):
    In `Z/6Z`, `γ(1) = 2` and `γ(2) = 3` are BOTH zero divisors (`2 * 3 = 0`), yet our
    universal `CRing` closed-form theorem certifies `det H_2 = 1 (mod 6)` (a unit!)! -/
theorem witness_zmod6_zero_divisors :
    CRing.mul (⟨2, by omega⟩ : ZMod 5) ⟨3, by omega⟩ = CRing.zero ∧
    det (hcbMat (R := ZMod 5)
          (fun m => if m = 1 then ⟨2, by omega⟩ else ⟨3, by omega⟩)
          (fun m => if m = 1 then ⟨5, by omega⟩ else ⟨2, by omega⟩)
          (fun _ => ⟨1, by omega⟩)
          (fun _ => ⟨2, by omega⟩)
          2 (fun j => if j = 1 then ⟨2, by omega⟩ else ⟨1, by omega⟩)) =
    ⟨1, by omega⟩ := by
  constructor
  · decide
  · rw [det_hcbMat_closed_form]; decide

/-- Witness 3 (Family II Non-Vacuity & Sharp Dichotomy):
    `det (subsetDisjMat 3 2 3) = (-5)^4 = 625 ≠ 0`, whereas `det (subsetDisjMat (k+1) 5 (-5)) = 0` ∀ k! -/
theorem witness_subsetDisj_invertible : det (subsetDisjMat (R := Int) 3 2 3) = 625 := by
  rw [det_subsetDisjMat_closed_form]; decide

theorem witness_subsetDisj_singular_all (k : Nat) :
    det (subsetDisjMat (R := Int) (k + 1) 5 (-5)) = 0 := by
  change det (subsetDisjMat (R := Int) (k + 1) 5 (-5)) = CRing.zero
  rw [det_subsetDisjMat_zero_iff]; right; rfl

/-- Sharpness Counterexample A (Kernel-Checked!):
    Replacing `(x &&& y)` by `(x ||| y)` in `msbAndMat` breaks the formula at `k = 2, f(j) = 2^j`:
    `det (fun x y => 2^(msbPos (x ||| y))) = 0 ≠ -3 = det (msbAndMat 2 (2^·))`! -/
theorem counterexample_msb_or_breaks :
    det (R := Int) (fun x y : Fin (pow2 2) => (2 : Int) ^ msbPos (x.val ||| y.val)) = 0 ∧
    det (msbAndMat (R := Int) 2 (fun j => (2 : Int) ^ j)) = -3 := by
  constructor
  · decide
  · rw [det_msbAnd_closed_form]; decide

/-- Sharpness Counterexample B (Kernel-Checked!):
    Replacing `(x &&& y)` by `(x ^^^ y)` in `msbAndMat` breaks the formula at `k = 2, f(j) = 2^j`:
    `det (fun x y => 2^(msbPos (x ^^^ y))) = -55 ≠ -3`! -/
theorem counterexample_msb_xor_breaks :
    det (R := Int) (fun x y : Fin (pow2 2) => (2 : Int) ^ msbPos (x.val ^^^ y.val)) = -55 ∧
    det (msbAndMat (R := Int) 2 (fun j => (2 : Int) ^ j)) = -3 := by
  constructor
  · decide
  · rw [det_msbAnd_closed_form]; decide

/-- Sharpness Counterexample C (Kernel-Checked!):
    Adding the superset term `[y ⊆ x]` to `subsetDisjMat` (`a = c = 1`) breaks the
    `(a^2 - c^2)^(2^(k-1))` law: at `k = 1`, `det = 2 ≠ 0`, while at `k = 2`, `det = 0`! -/
theorem counterexample_bool_plus_superset_breaks :
    det (R := Int) (fun x y : Fin (pow2 1) =>
      (if (x.val &&& y.val) = x.val then (1 : Int) else 0) +
      (if (x.val &&& y.val) = y.val then 1 else 0) +
      (if (x.val &&& y.val) = 0 then 1 else 0)) = 2 ∧
    det (R := Int) (fun x y : Fin (pow2 2) =>
      (if (x.val &&& y.val) = x.val then (1 : Int) else 0) +
      (if (x.val &&& y.val) = y.val then 1 else 0) +
      (if (x.val &&& y.val) = 0 then 1 else 0)) = 0 := by
  constructor <;> decide

/-! ### Axiom Verification Receipts -/


end BitSlicedSchur
