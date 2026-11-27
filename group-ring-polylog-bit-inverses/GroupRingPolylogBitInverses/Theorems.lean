import GroupRingPolylogBitInverses.Defs

namespace SpecMat13
/-- **Core Engine Theorem 3 (Exact Parseval / Plancherel Duality):**
    `∑_ω wht(f)(ω) * wht(g)(ω) = 2^k * ∑_x f(x) * g(x)`. -/
theorem parseval_plancherel : {k : Nat} → (f g : GR k) →
    sumBVec (fun ω => wht f ω * wht g ω) = (2 : Int) ^ k * sumBVec (fun x => f x * g x)
  | 0, f, g => by
      simp [sumBVec, wht, bdot, signBit]
  | k + 1, f, g => by
      simp only [sumBVec]
      let f0 : GR k := fun x => f (.cons false x)
      let f1 : GR k := fun x => f (.cons true x)
      let g0 : GR k := fun x => g (.cons false x)
      let g1 : GR k := fun x => g (.cons true x)
      have hL : sumBVec (fun ω => wht f (.cons false ω) * wht g (.cons false ω)) +
                sumBVec (fun ω => wht f (.cons true ω) * wht g (.cons true ω)) =
          2 * sumBVec (fun ω => wht f0 ω * wht g0 ω) +
          2 * sumBVec (fun ω => wht f1 ω * wht g1 ω) := by
        rw [← sumBVec_add, ← sumBVec_mul_left, ← sumBVec_mul_left, ← sumBVec_add]
        apply sumBVec_congr; intro ω
        rw [wht_cons f false ω, wht_cons g false ω, wht_cons f true ω, wht_cons g true ω]
        let hf0 := wht f0 ω
        let hf1 := wht f1 ω
        let hg0 := wht g0 ω
        let hg1 := wht g1 ω
        change (hf0 + 1 * hf1) * (hg0 + 1 * hg1) + (hf0 + (-1) * hf1) * (hg0 + (-1) * hg1) =
            2 * (hf0 * hg0) + 2 * (hf1 * hg1)
        have e1 : hf0 + 1 * hf1 = hf0 + hf1 := by omega
        have e2 : hg0 + 1 * hg1 = hg0 + hg1 := by omega
        have e3 : hf0 + (-1) * hf1 = hf0 - hf1 := by omega
        have e4 : hg0 + (-1) * hg1 = hg0 - hg1 := by omega
        rw [e1, e2, e3, e4, Int.add_mul, Int.mul_add, Int.mul_add,
            Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      rw [hL, parseval_plancherel f0 g0, parseval_plancherel f1 g1, Int.pow_succ]
      let s0 := sumBVec (fun x => f0 x * g0 x)
      let s1 := sumBVec (fun x => f1 x * g1 x)
      let p := (2 : Int) ^ k
      change 2 * (p * s0) + 2 * (p * s1) = p * 2 * (s0 + s1)
      rw [Int.mul_add]
      have a1 : 2 * (p * s0) = p * 2 * s0 := by ac_rfl
      have a2 : 2 * (p * s1) = p * 2 * s1 := by ac_rfl
      rw [a1, a2]

theorem parseval {k : Nat} (f : GR k) :
    sumSq (wht f) = (2 : Int) ^ k * sumSq f :=
  parseval_plancherel f f

/-- **Obstruction Theorem 1 (Pure-Silicon Higman Rigidity):**
    In `Z[F_2^k]` for ALL `k ≥ 0`, every exact `Z`-unit (`f * g = δ_0`) satisfies
    `∑_x f(x)^2 = 1`, i.e., `f = ± δ_a` (no non-trivial `Z`-units exist). -/
theorem higman_rigidity {k : Nat} {f g : GR k}
    (hinv : ∀ x, conv f g x = scaleDelta 1 x) : sumSq f = 1 := by
  have hw := (group_ring_inv_iff f g 1).mp hinv
  have hsq : ∀ ω, wht f ω * wht f ω = 1 := by
    intro ω
    have h1 := hw ω
    have hcases : wht f ω = 1 ∨ wht f ω = -1 := by
      have habs : (wht f ω).natAbs * (wht g ω).natAbs = 1 := by
        have := congrArg Int.natAbs h1
        rw [Int.natAbs_mul] at this
        exact this
      have hna : (wht f ω).natAbs = 1 := Nat.eq_one_of_mul_eq_one_right habs
      omega
    rcases hcases with h | h <;> simp [h]
  have hp := parseval f
  have hsum : sumSq (wht f) = (2 : Int) ^ k * 1 := by
    simp only [sumSq]
    rw [sumBVec_congr hsq, sumBVec_const]
  rw [hsum] at hp
  have hpos : (2 : Int) ^ k ≠ 0 := by have := pow2_pos k; omega
  exact (Int.eq_of_mul_eq_mul_left hpos hp).symm

/-- **Obstruction Theorem 4 (Mod-12 Parseval Dyadic Obstruction):**
    If `f : GR k` is ternary (`f x ∈ {-1, 0, 1}`), `|supp(f)| ≥ 2`, and `f` is
    dyadically invertible (`f * g = 2^m • δ_0`), then:
    `|supp(f)| ≥ 4` and `|supp(f)| % 6 = 4` (so `|supp| ∈ {4, 10, 16, 22, ...}`). -/
theorem mod12_parseval_dyadic_obstruction {k m : Nat} {f g : GR k}
    (ht : IsTernary f) (hinv : ∀ x, conv f g x = scaleDelta ((2 : Int) ^ m) x)
    (hge2 : 2 ≤ suppCount f) :
    4 ≤ suppCount f ∧ suppCount f % 6 = 4 := by
  have hw := (group_ring_inv_iff f g ((2 : Int) ^ m)).mp hinv
  have hpow : ∀ ω, ∃ e : Nat, wht f ω * wht f ω = (4 : Int) ^ e := by
    intro ω
    have hd : wht f ω ∣ (2 : Int) ^ m := ⟨wht g ω, (hw ω).symm⟩
    have hna : (wht f ω).natAbs ∣ 2 ^ m := by
      have := Int.natAbs_dvd_natAbs.mpr hd
      simpa [Int.natAbs_pow] using this
    rcases nat_dvd_pow2 m (wht f ω).natAbs hna with ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hsq : wht f ω * wht f ω = ((wht f ω).natAbs : Int) * ((wht f ω).natAbs : Int) := by
      have := Int.natAbs_mul_self (a := wht f ω)
      omega
    rw [hsq, he]
    exact nat_pow2_sq_eq_pow4 e
  have hall_ge1 : ∀ ω, ∃ e : Nat, 1 ≤ e ∧ wht f ω * wht f ω = (4 : Int) ^ e := by
    intro ω
    rcases hpow ω with ⟨e, he⟩
    by_cases he0 : e = 0
    · exfalso
      subst he0
      have hodd0 : wht f ω % 2 = 1 := by
        have hpm : wht f ω = 1 ∨ wht f ω = -1 := by
          have : (wht f ω).natAbs * (wht f ω).natAbs = 1 := by
            have := congrArg Int.natAbs he; rw [Int.natAbs_mul] at this; exact this
          have : (wht f ω).natAbs = 1 := Nat.eq_one_of_mul_eq_one_right this
          omega
        rcases hpm with h | h <;> omega
      have hall_one : ∀ ω', wht f ω' * wht f ω' = 1 := by
        intro ω'
        have hpar : wht f ω' % 2 = 1 := by
          rw [wht_const_parity f ω', ← wht_const_parity f ω, hodd0]
        rcases hpow ω' with ⟨e', he'⟩
        cases e' with
        | zero => exact he'
        | succ e'' =>
            rw [Int.pow_succ] at he'
            have h4 : (wht f ω' * wht f ω') % 2 = 0 := by omega
            have h1 : (wht f ω' * wht f ω') % 2 = 1 := by
              rw [Int.mul_emod, hpar]; decide
            omega
      have hp := parseval f
      have hsum : sumSq (wht f) = (2 : Int) ^ k * 1 := by
        simp only [sumSq]; rw [sumBVec_congr hall_one, sumBVec_const]
      rw [hsum] at hp
      have hpos : (2 : Int) ^ k ≠ 0 := by have := pow2_pos k; omega
      have hsq1 : sumSq f = 1 := (Int.eq_of_mul_eq_mul_left hpos hp).symm
      rw [sumSq_eq_sumInd_of_ternary ht, ← suppCount_eq_sumInd] at hsq1
      omega
    · exact ⟨e, by omega, he⟩
  have hpow4_ge : ∀ e : Nat, 1 ≤ e → (4 : Int) ≤ (4 : Int) ^ e := by
    intro e he
    cases e with
    | zero => omega
    | succ e' =>
        clear he
        induction e' with
        | zero => decide
        | succ n ih => rw [Int.pow_succ]; omega
  have hpow4_mod12 : ∀ e : Nat, 1 ≤ e → (4 : Int) ^ e % 12 = 4 := by
    intro e he
    cases e with
    | zero => omega
    | succ e' =>
        clear he
        induction e' with
        | zero => decide
        | succ n ih =>
            rw [Int.pow_succ, Int.mul_emod, ih]
            decide
  have hge4_all : ∀ ω, (4 : Int) ≤ wht f ω * wht f ω := by
    intro ω; rcases hall_ge1 ω with ⟨e, he, hsq⟩; rw [hsq]; exact hpow4_ge e he
  have hmod12_all : ∀ ω, (wht f ω * wht f ω) % 12 = (4 : Int) % 12 := by
    intro ω; rcases hall_ge1 ω with ⟨e, he, hsq⟩; rw [hsq, hpow4_mod12 e he]; rfl
  have hge4_sum : (2 : Int) ^ k * 4 ≤ sumSq (wht f) := by
    rw [← sumBVec_const (k := k) 4]
    exact sumBVec_le hge4_all
  rw [parseval f, sumSq_eq_sumInd_of_ternary ht, ← suppCount_eq_sumInd] at hge4_sum
  have hpos := pow2_pos k
  have hge4 : 4 ≤ suppCount f := by
    by_cases hlt : 4 ≤ suppCount f
    · exact hlt
    · exfalso
      have h1 : (suppCount f : Int) ≤ 3 := by omega
      have h2 : (2 : Int) ^ k * (suppCount f : Int) ≤ (2 : Int) ^ k * 3 :=
        Int.mul_le_mul_of_nonneg_left h1 (by omega)
      omega
  have hmod12 : ((2 : Int) ^ k * (suppCount f : Int)) % 12 = ((2 : Int) ^ k * 4) % 12 := by
    rw [suppCount_eq_sumInd, ← sumSq_eq_sumInd_of_ternary ht, ← parseval f]
    rw [← sumBVec_const (k := k) 4]
    exact sumBVec_mod 12 _ _ hmod12_all
  have heven : suppCount f % 2 = 0 := by
    have h0even : wht f (bzero k) % 2 = 0 := by
      rcases hall_ge1 (bzero k) with ⟨e, he, hsq⟩
      cases e with
      | zero => omega
      | succ e' =>
          rw [Int.pow_succ] at hsq
          have : (wht f (bzero k) * wht f (bzero k)) % 2 = 0 := by omega
          by_cases hodd : wht f (bzero k) % 2 = 0
          · exact hodd
          · exfalso
            have h1 : wht f (bzero k) % 2 = 1 := by omega
            have h2 : (wht f (bzero k) * wht f (bzero k)) % 2 = 1 := by
              rw [Int.mul_emod, h1]; decide
            omega
    have hpar_eq : wht f (bzero k) % 2 = (suppCount f : Int) % 2 := by
      rw [suppCount_eq_sumInd, ← sumSq_eq_sumInd_of_ternary ht]
      simp only [wht, sumSq]
      apply sumBVec_mod 2
      intro x
      rw [bdot_bzero_left]
      rcases ht x with h | h | h <;> simp [signBit, h]
    omega
  have hmod3 : ((2 : Int) ^ k * ((suppCount f : Int) - 4)) % 3 = 0 := by
    have hfac : (2 : Int) ^ k * ((suppCount f : Int) - 4) =
        (2 : Int) ^ k * (suppCount f : Int) - (2 : Int) ^ k * 4 := Int.mul_sub _ _ _
    rw [hfac]; omega
  have h3 : ((suppCount f : Int) - 4) % 3 = 0 := by
    rw [Int.mul_emod] at hmod3
    rcases pow2_int_mod3 k with h | h <;> rw [h] at hmod3 <;> omega
  exact ⟨hge4, by omega⟩

/-- **Obstruction Theorem 5 (Pure `{0, 1}` Self-Inversion Impossibility):**
    No non-negative binary element `f : BVec k → {0, 1}` with `|supp(f)| ≥ 2` can
    satisfy `f * f = c • δ_0` for ANY integer `c`. -/
theorem binary01_no_self_inverse {k : Nat} {f : GR k} {c : Int}
    (hb : IsBinary01 f) (hself : ∀ x, conv f f x = scaleDelta c x) :
    suppCount f ≤ 1 := by
  have hw0 := (group_ring_inv_iff f f c).mp hself (bzero k)
  have hf0 : wht f (bzero k) = (suppCount f : Int) := by
    rw [suppCount_eq_sumInd]
    simp only [wht, sumInd]
    apply sumBVec_congr; intro x
    rw [bdot_bzero_left]
    rcases hb x with h | h <;> simp [signBit, h]
  have hc : c = (suppCount f : Int) := by
    have h0 := hself (bzero k)
    simp only [scaleDelta, beq_self_eq_true, ↓reduceIte] at h0
    rw [← h0, suppCount_eq_sumInd]
    simp only [conv, sumInd]
    apply sumBVec_congr; intro x
    rw [bxor_bzero_right]
    rcases hb x with h | h <;> simp [h]
  rw [hf0, hc] at hw0
  have hnat : suppCount f * suppCount f = suppCount f := by omega
  by_cases hle : suppCount f ≤ 1
  · exact hle
  · exfalso
    have h2 : 2 ≤ suppCount f := by omega
    have : 2 * suppCount f ≤ suppCount f * suppCount f := Nat.mul_le_mul_right _ h2
    omega

theorem parseval_uncertainty {k : Nat} {f g : GR k} {D : Int}
    (hinv : ∀ x, conv f g x = scaleDelta D x) :
    D ^ 2 ≤ sumSq f * sumSq g := by
  have hw := (group_ring_inv_iff f g D).mp hinv
  have hcs := cauchy_schwarz_bvec (wht f) (wht g)
  have hsum : sumBVec (fun ω => wht f ω * wht g ω) = (2 : Int) ^ k * D := by
    rw [sumBVec_congr hw, sumBVec_const]
  rw [hsum, parseval f, parseval g] at hcs
  have h1 : ((2 : Int) ^ k * D) ^ 2 = ((2 : Int) ^ k * (2 : Int) ^ k) * (D ^ 2) := by
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]; ac_rfl
  have h2 : (2 : Int) ^ k * sumSq f * ((2 : Int) ^ k * sumSq g) =
      ((2 : Int) ^ k * (2 : Int) ^ k) * (sumSq f * sumSq g) := by ac_rfl
  rw [h1, h2] at hcs
  have hpos : 0 < (2 : Int) ^ k * (2 : Int) ^ k :=
    Int.mul_pos (pow2_pos k) (pow2_pos k)
  by_cases hle : D ^ 2 ≤ sumSq f * sumSq g
  · exact hle
  · exfalso
    have hneg : sumSq f * sumSq g - D ^ 2 < 0 := by omega
    have : ((2 : Int) ^ k * (2 : Int) ^ k) * (sumSq f * sumSq g - D ^ 2) < 0 :=
      Int.mul_neg_of_pos_of_neg hpos hneg
    rw [Int.mul_sub] at this
    omega

/-! ## Part III: Reusable Shared-Bit / Disjoint-Subspace Idempotent Lifting Engine -/

/-- **Theorem A.1 (Dual Multiplexer Tree WHT Law):**
    Every single Walsh coefficient of `treeElem d` is `2^d * spectralSign d ω ∈ {-2^d, +2^d}`. -/
theorem treeElem_wht : (d : Nat) → (ω : BVec (treeWidth d)) →
    wht (treeElem d) ω = (2 : Int) ^ d * spectralSign d ω
  | 0, .nil => by decide
  | d + 1, .cons ωt (.cons ωu ωx) => by
      simp only [treeElem, spectralSign]
      rw [sharedLift_wht]
      cases ωt
      · simp only [beq_self_eq_true, ↓reduceIte]
        rw [treeElem_wht d (bsplitR (treeWidth d + 0) (treeWidth d) ωx).1, Int.pow_succ]
        ac_rfl
      · simp only [beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
        have hnil : (bsplitR (treeWidth d) 0 (bsplitR (treeWidth d + 0) (treeWidth d) ωx).1).2 = .nil := rfl
        rw [hnil]
        change 2 * signBit ωu * wht (treeElem d) (bsplitR (treeWidth d + 0) (treeWidth d) ωx).2 =
               (2 : Int) ^ (d + 1) * (signBit ωu * spectralSign d (bsplitR (treeWidth d + 0) (treeWidth d) ωx).2)
        rw [treeElem_wht d, Int.pow_succ]
        ac_rfl

theorem treeElem_polylog_identity (d : Nat) :
    4 * suppCount (treeElem d) = (treeWidth d + 2) ^ 2 := by
  rw [treeElem_suppCount, treeWidth_closed]
  induction d with
  | zero => decide
  | succ d ih =>
      rw [Nat.pow_succ 2 (d + 1), Nat.pow_succ 4 d]
      have hsq : (2 ^ (d + 1) * 2) ^ 2 = (2 ^ (d + 1)) ^ 2 * 4 := by
        have h22 : 2 * 2 = 4 := rfl
        calc
          (2 ^ (d + 1) * 2) ^ 2 = (2 ^ (d + 1) * 2) * (2 ^ (d + 1) * 2) := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
          _ = (2 ^ (d + 1) * 2 ^ (d + 1)) * (2 * 2) := by ac_rfl
          _ = (2 ^ (d + 1)) ^ 2 * 4 := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, h22]
      rw [hsq, ← ih]; ac_rfl

theorem asymTree_non_self_inverse (d : Nat) :
    asymTreeP d ≠ asymTreeQ d ∧ (∃ x, asymTreeP d x ≠ - asymTreeQ d x) := by
  constructor
  · intro heq
    have h := asymTree_val_diff d
    rw [heq] at h
    omega
  · refine ⟨bzero (asymWidth d), ?_⟩
    have h := asymTree_val_zero d
    omega

/-! ### Theorem C: Universal All-Dimension Polylogarithmic Theorem (`∀ k ≥ 2, k ≠ 3`) -/

/-- **Sharpness 2 (`k = 3` Dyadic Inversion Impossibility — Exact Gap at `k = 3`):**
    NO full-affine-spanning ternary element on `F_2^3` is dyadically invertible (`f * g = 2^m • δ_0`).
    Combined with Theorem C (`∀ k ≥ 2, k ≠ 3`) and `baseA3` (`k = 3, D = 3`), this proves
    the `k ≠ 3` exclusion in Theorem C is 100% sharp. -/
theorem k3_no_spanning_ternary_dyadic {m : Nat} {f g : GR 3}
    (ht : IsTernary f) (hspan : AffineSpan f)
    (hinv : ∀ x, conv f g x = scaleDelta ((2 : Int) ^ m) x) : False := by
  have hge2 : 2 ≤ suppCount f := by
    by_cases hge : 2 ≤ suppCount f
    · exact hge
    · exfalso
      have huniq : ∀ x y : BVec 3, f x ≠ 0 → f y ≠ 0 → x = y := by
        intro x y hx hy
        by_cases hxy : x = y
        · exact hxy
        · exfalso
          have h2 : ∀ z : BVec 3, (if z == x then (1 : Int) else 0) + (if z == y then 1 else 0) ≤
              (if f z == 0 then 0 else 1) := by
            intro z
            by_cases hzx : z = x
            · rw [hzx]
              simp [hxy, hx]
            · by_cases hzy : z = y
              · rw [hzy]
                simp [Ne.symm hxy, hy]
              · simp [hzx, hzy]; split <;> omega
          have hle := sumBVec_le h2
          rw [sumBVec_add, sumBVec_delta x (fun _ => 1), sumBVec_delta y (fun _ => 1)] at hle
          change 2 ≤ sumInd f at hle
          rw [← suppCount_eq_sumInd] at hle
          omega
      by_cases hex : ∃ x0, f x0 ≠ 0
      · rcases hex with ⟨x0, hx0⟩
        have hbad : BVec.cons true (.cons false (.cons false .nil)) = bzero 3 := by
          apply hspan (.cons true (.cons false (.cons false .nil)))
            (bdot (.cons true (.cons false (.cons false .nil))) x0)
          intro x hx
          rw [huniq x x0 hx hx0]
        simp [bzero] at hbad
      · have hbad : BVec.cons true (.cons false (.cons false .nil)) = bzero 3 := by
          apply hspan (.cons true (.cons false (.cons false .nil))) false
          intro x hx; exact False.elim (hex ⟨x, hx⟩)
        simp [bzero] at hbad
  have ⟨hge4, hmod6⟩ := mod12_parseval_dyadic_obstruction ht hinv hge2
  have hle8 : suppCount f ≤ 8 := by
    have h1 : sumInd f ≤ sumBVec (fun (_ : BVec 3) => (1 : Int)) := by
      apply sumBVec_le; intro x; split <;> omega
    rw [sumBVec_const, ← suppCount_eq_sumInd] at h1
    omega
  have h4 : suppCount f = 4 := by omega
  have hw := (group_ring_inv_iff f g ((2 : Int) ^ m)).mp hinv
  have hall_sq4 : ∀ ω : BVec 3, wht f ω * wht f ω = 4 := by
    have hge4_w : ∀ ω : BVec 3, 4 ≤ wht f ω * wht f ω := by
      intro ω
      have hne0 : wht f ω ≠ 0 := by
        intro h0; have := hw ω; rw [h0, Int.zero_mul] at this
        have := pow2_pos m; omega
      have heven : wht f ω % 2 = 0 := by
        rw [wht_const_parity f ω]
        have hpar : wht f (bzero 3) % 2 = (suppCount f : Int) % 2 := by
          rw [suppCount_eq_sumInd, ← sumSq_eq_sumInd_of_ternary ht]
          simp only [wht, sumSq]
          apply sumBVec_mod 2; intro x
          rw [bdot_bzero_left]
          rcases ht x with h | h | h <;> simp [signBit, h]
        rw [hpar, h4]; decide
      exact sq_ge_four_of_abs_ge_two (by omega)
    intro ω
    by_cases heq4 : wht f ω * wht f ω = 4
    · exact heq4
    · exfalso
      have hgt4 : 5 ≤ wht f ω * wht f ω := by have := hge4_w ω; omega
      have hsum_gt : 32 < sumSq (wht f) := by
        have hle : sumBVec (fun ω' : BVec 3 => (4 : Int) + (if ω' == ω then 1 else 0)) ≤ sumSq (wht f) := by
          apply sumBVec_le; intro ω'
          by_cases h : ω' = ω
          · subst h; simp [hgt4]
          · simp [h, hge4_w ω']
        rw [sumBVec_add, sumBVec_const, sumBVec_delta ω (fun _ => 1)] at hle
        omega
      have hp := parseval f
      rw [sumSq_eq_sumInd_of_ternary ht, ← suppCount_eq_sumInd, h4] at hp
      omega
  have hff : ∀ z, conv f f z = scaleDelta 4 z :=
    (group_ring_inv_iff f f 4).mpr hall_sq4
  have hall_pairs : ∀ a b : BVec 3, a ≠ b → f a ≠ 0 → f b ≠ 0 →
      ∃ c : BVec 3, c ≠ a ∧ c ≠ b ∧ f c ≠ 0 ∧ f (bxor c (bxor a b)) ≠ 0 := by
    intro a b hab ha hb
    have hz : conv f f (bxor a b) = 0 := by
      have h0 := hff (bxor a b)
      have hne : bxor a b ≠ bzero 3 := fun hc => hab ((bxor_eq_bzero_iff).mp hc)
      simpa [scaleDelta, hne] using h0
    by_cases hex : ∃ c : BVec 3, c ≠ a ∧ c ≠ b ∧ f c ≠ 0 ∧ f (bxor c (bxor a b)) ≠ 0
    · exact hex
    · exfalso
      have honly : ∀ c : BVec 3, f c * f (bxor c (bxor a b)) =
          (if c == a then f a * f b else 0) + (if c == b then f b * f a else 0) := by
        intro c
        by_cases hca : c = a
        · rw [hca]
          have hxa : bxor a (bxor a b) = b := by
            rw [← bxor_assoc, bxor_self, bxor_bzero_left]
          simp [hab, hxa]
        · by_cases hcb : c = b
          · rw [hcb]
            have hxb : bxor b (bxor a b) = a := by
              rw [bxor_comm a b, ← bxor_assoc, bxor_self, bxor_bzero_left]
            simp [Ne.symm hab, hxb]
          · simp only [hca, hcb, beq_iff_eq, ↓reduceIte, Int.add_zero]
            by_cases hfc : f c = 0
            · simp [hfc]
            · by_cases hfc2 : f (bxor c (bxor a b)) = 0
              · simp [hfc2]
              · exact False.elim (hex ⟨c, hca, hcb, hfc, hfc2⟩)
      simp only [conv] at hz
      rw [sumBVec_congr honly, sumBVec_add, sumBVec_delta a (fun _ => f a * f b),
          sumBVec_delta b (fun _ => f b * f a)] at hz
      have hfab : f a * f b ≠ 0 := Int.mul_ne_zero ha hb
      have : f a * f b + f b * f a = 2 * (f a * f b) := by
        rw [Int.mul_comm (f b) (f a)]; omega
      rw [this] at hz
      omega
  have hex1 : ∃ a : BVec 3, f a ≠ 0 := by
    by_cases h : ∃ a : BVec 3, f a ≠ 0
    · exact h
    · exfalso
      have hz : sumInd f = 0 := by
        simp only [sumInd]
        rw [sumBVec_congr (g := fun _ => 0) (fun x => by
          by_cases hx : f x = 0
          · simp [hx]
          · exact False.elim (h ⟨x, hx⟩)), sumBVec_zero]
      rw [← suppCount_eq_sumInd, h4] at hz; omega
  rcases hex1 with ⟨a, ha⟩
  have hex2 : ∃ b : BVec 3, b ≠ a ∧ f b ≠ 0 := by
    by_cases h : ∃ b : BVec 3, b ≠ a ∧ f b ≠ 0
    · exact h
    · exfalso
      have hle1 : sumInd f ≤ 1 := by
        have : ∀ x : BVec 3, (if f x == 0 then (0 : Int) else 1) ≤ (if x == a then 1 else 0) := by
          intro x; by_cases hxa : x = a
          · subst hxa; simp [ha]
          · by_cases hx : f x = 0
            · simp [hxa, hx]
            · exact False.elim (h ⟨x, hxa, hx⟩)
        have h' := sumBVec_le this
        rw [sumBVec_delta a (fun _ => 1)] at h'
        exact h'
      rw [← suppCount_eq_sumInd, h4] at hle1; omega
  rcases hex2 with ⟨b, hba, hb⟩
  rcases hall_pairs a b (Ne.symm hba) ha hb with ⟨c, hca, hcb, hc, hd⟩
  let d := bxor c (bxor a b)
  have hda : d ≠ a := by
    intro h
    have : bxor c b = bzero 3 := by
      have h1 := congrArg (fun z => bxor z a) h
      simp only [d] at h1
      rw [bxor_self, bxor_assoc c (bxor a b) a, bxor_comm (bxor a b) a,
          ← bxor_assoc a a b, bxor_self, bxor_bzero_left] at h1
      exact h1
    exact hcb ((bxor_eq_bzero_iff).mp this)
  have hdb : d ≠ b := by
    intro h
    have : bxor c a = bzero 3 := by
      have h1 := congrArg (fun z => bxor z b) h
      simp only [d] at h1
      rw [bxor_self, bxor_assoc, bxor_assoc, bxor_self, bxor_bzero_right] at h1
      exact h1
    exact hca ((bxor_eq_bzero_iff).mp this)
  have hdc : d ≠ c := by
    intro h
    have : bxor a b = bzero 3 := by
      have h1 := congrArg (fun z => bxor c z) h
      simp only [d] at h1
      rw [← bxor_assoc, bxor_self, bxor_bzero_left] at h1
      exact h1
    exact hba ((bxor_eq_bzero_iff).mp this).symm
  have hmem : ∀ x : BVec 3, f x ≠ 0 → x = a ∨ x = b ∨ x = c ∨ x = d := by
    intro x hx
    by_cases h1 : x = a
    · exact Or.inl h1
    · by_cases h2 : x = b
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : x = c
        · exact Or.inr (Or.inr (Or.inl h3))
        · by_cases h4' : x = d
          · exact Or.inr (Or.inr (Or.inr h4'))
          · exfalso
            have hfd : f d ≠ 0 := hd
            have hle : ∀ z : BVec 3,
                (if z == a then (1 : Int) else 0) + (if z == b then 1 else 0) +
                (if z == c then 1 else 0) + (if z == d then 1 else 0) + (if z == x then 1 else 0) ≤
                (if f z == 0 then 0 else 1) := by
              intro z
              by_cases za : z = a
              · subst za; simp [Ne.symm hba, Ne.symm hca, Ne.symm hda, Ne.symm h1, ha]
              · by_cases zb : z = b
                · subst zb; simp [hba, Ne.symm hcb, Ne.symm hdb, Ne.symm h2, hb]
                · by_cases zc : z = c
                  · subst zc; simp [hca, hcb, Ne.symm hdc, Ne.symm h3, hc]
                  · by_cases zd : z = d
                    · subst zd; simp [hda, hdb, hdc, Ne.symm h4', hfd]
                    · by_cases zx : z = x
                      · subst zx; simp [h1, h2, h3, h4', hx]
                      · simp [za, zb, zc, zd, zx]; split <;> omega
            have hge5 := sumBVec_le hle
            rw [sumBVec_add, sumBVec_add, sumBVec_add, sumBVec_add,
                sumBVec_delta a (fun _ => 1), sumBVec_delta b (fun _ => 1),
                sumBVec_delta c (fun _ => 1), sumBVec_delta d (fun _ => 1),
                sumBVec_delta x (fun _ => 1)] at hge5
            change 5 ≤ sumInd f at hge5
            rw [← suppCount_eq_sumInd, h4] at hge5; omega
  have hex_orth : ∀ u v : BVec 3, ∃ ω : BVec 3, ω ≠ bzero 3 ∧ bdot ω u = false ∧ bdot ω v = false := by
    intro u v
    match u, v with
    | .cons u0 (.cons u1 (.cons u2 .nil)), .cons v0 (.cons v1 (.cons v2 .nil)) =>
        cases u0 <;> cases u1 <;> cases u2 <;> cases v0 <;> cases v1 <;> cases v2 <;>
        first
        | exact ⟨.cons true  (.cons false (.cons false .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons false (.cons true  (.cons false .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons false (.cons false (.cons true  .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons true  (.cons true  (.cons false .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons true  (.cons false (.cons true  .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons false (.cons true  (.cons true  .nil)), by decide, rfl, rfl⟩
        | exact ⟨.cons true  (.cons true  (.cons true  .nil)), by decide, rfl, rfl⟩
  rcases hex_orth (bxor a b) (bxor a c) with ⟨ω, hωne, hωab, hωac⟩
  have hω0 : ω = bzero 3 := by
    apply hspan ω (bdot ω a)
    intro x hx
    have hdot_b : bdot ω b = bdot ω a := by
      have h := bdot_bxor_right ω a b
      rw [hωab] at h
      cases h1 : bdot ω a <;> cases h2 : bdot ω b <;> simp [h1, h2] at h ⊢
    have hdot_c : bdot ω c = bdot ω a := by
      have h := bdot_bxor_right ω a c
      rw [hωac] at h
      cases h1 : bdot ω a <;> cases h2 : bdot ω c <;> simp [h1, h2] at h ⊢
    have hdot_d : bdot ω d = bdot ω a := by
      simp only [d, bdot_bxor_right, hωab, hdot_c, Bool.xor_false]
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · rfl
    · exact hdot_b
    · exact hdot_c
    · exact hdot_d
  exact hωne hω0

theorem unshiftedLift_breaks_ternary :
    ¬ IsTernary (unshiftedLift (treeElem 1) (treeElem 1)) := by
  intro ht
  have h0 := ht (.cons false (.cons false (.cons false .nil)))
  have hv : unshiftedLift (treeElem 1) (treeElem 1) (.cons false (.cons false (.cons false .nil))) = 2 := by
    decide
  rw [hv] at h0
  omega

/-- **Non-Vacuity Witnesses (Kernel-Checked Concrete Instances):** -/
example : Nonempty (DyadicSparseWitness 2 1) := ⟨treeWitness 1⟩
example : Nonempty (DyadicSparseWitness 4 2) := depth_covers_interval 2 (by omega) 4 (by omega) (by omega)
example : Nonempty (DyadicSparseWitness 5 2) := depth_covers_interval 2 (by omega) 5 (by omega) (by omega)
example : Nonempty (DyadicSparseWitness 6 2) := ⟨treeWitness 2⟩
example : Nonempty (DyadicSparseWitness 7 3) := depth_covers_interval 3 (by omega) 7 (by omega) (by omega)
example : Nonempty (DyadicSparseWitness 14 3) := ⟨treeWitness 3⟩

example : treeWidth 2 = 6 ∧ suppCount (treeElem 2) = 16 := ⟨rfl, treeElem_suppCount 2⟩
example : treeWidth 3 = 14 ∧ suppCount (treeElem 3) = 64 := ⟨rfl, treeElem_suppCount 3⟩
example : asymWidth 1 = 8 ∧ suppCount (asymTreeP 1) = 20 := ⟨rfl, asymTreeP_suppCount 1⟩
example : asymWidth 2 = 18 ∧ suppCount (asymTreeP 2) = 80 := ⟨rfl, asymTreeP_suppCount 2⟩

/-! ### Axiom Cleanliness Audit (`#print axioms`) -/


end SpecMat13
