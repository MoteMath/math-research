import MahlerVanderput2adicCerts.Defs

namespace Z2CertEngine
namespace Z2
theorem ofInt_ofNat (n : Nat) : ofInt (n : Int) = ofNat n := by
  apply Z2.ext; intro w
  apply BitVec.eq_of_toNat_eq
  simp [ofInt, ofNat]

theorem ofInt_add (a b : Int) : ofInt (a + b) = ofInt a + ofInt b := by
  apply Z2.ext; intro w
  change BitVec.ofInt w (a + b) = BitVec.ofInt w a + BitVec.ofInt w b
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_add]
  have ha := Int.emod_nonneg a (two_pow_ne_zero_int w)
  have hb := Int.emod_nonneg b (two_pow_ne_zero_int w)
  have hab := Int.emod_nonneg (a + b) (two_pow_ne_zero_int w)
  have hmod : (a + b) % ((2 ^ w : Nat) : Int) =
              (a % ((2 ^ w : Nat) : Int) + b % ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int) :=
    Int.add_emod a b _
  have hcast : ((((a % ((2 ^ w : Nat) : Int)).toNat + (b % ((2 ^ w : Nat) : Int)).toNat) % 2 ^ w : Nat) : Int) =
               (a % ((2 ^ w : Nat) : Int) + b % ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_add, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
  omega

theorem ofInt_sub (a b : Int) : ofInt (a - b) = ofInt a - ofInt b := by
  apply Z2.ext; intro w
  change BitVec.ofInt w (a - b) = BitVec.ofInt w a - BitVec.ofInt w b
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_sub]
  have ha := Int.emod_nonneg a (two_pow_ne_zero_int w)
  have hb := Int.emod_nonneg b (two_pow_ne_zero_int w)
  have hblt : b % ((2 ^ w : Nat) : Int) < ((2 ^ w : Nat) : Int) := Int.emod_lt_of_pos b (two_pow_pos_int w)
  have hab := Int.emod_nonneg (a - b) (two_pow_ne_zero_int w)
  have hmod : (a - b) % ((2 ^ w : Nat) : Int) =
              ((((2 ^ w : Nat) : Int) - b % ((2 ^ w : Nat) : Int) + a % ((2 ^ w : Nat) : Int))) % ((2 ^ w : Nat) : Int) := by
    rw [int_emod_eq_iff_dvd]
    have hrearr : (a - b) - (((2 ^ w : Nat) : Int) - b % ((2 ^ w : Nat) : Int) + a % ((2 ^ w : Nat) : Int)) =
           ((a - a % ((2 ^ w : Nat) : Int)) - (b - b % ((2 ^ w : Nat) : Int))) - ((2 ^ w : Nat) : Int) := by omega
    rw [hrearr]
    have hda : ((2 ^ w : Nat) : Int) ∣ (a - a % ((2 ^ w : Nat) : Int)) := by
      rw [← int_emod_eq_iff_dvd, Int.emod_emod]
    have hdb : ((2 ^ w : Nat) : Int) ∣ (b - b % ((2 ^ w : Nat) : Int)) := by
      rw [← int_emod_eq_iff_dvd, Int.emod_emod]
    exact Int.dvd_sub (Int.dvd_sub hda hdb) (Int.dvd_refl _)
  have hcast : (((2 ^ w - (b % ((2 ^ w : Nat) : Int)).toNat + (a % ((2 ^ w : Nat) : Int)).toNat) % 2 ^ w : Nat) : Int) =
               (((2 ^ w : Nat) : Int) - b % ((2 ^ w : Nat) : Int) + a % ((2 ^ w : Nat) : Int)) % ((2 ^ w : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_add]
    have hsub_cast : ((2 ^ w - (b % ((2 ^ w : Nat) : Int)).toNat : Nat) : Int) =
                     ((2 ^ w : Nat) : Int) - b % ((2 ^ w : Nat) : Int) := by omega
    rw [hsub_cast, Int.toNat_of_nonneg ha]
  omega

theorem ofInt_neg (a : Int) : ofInt (-a) = -(ofInt a) := by
  have h := ofInt_sub 0 a
  simp only [Int.zero_sub] at h
  rw [h]
  apply Z2.ext; intro w
  change BitVec.ofInt w 0 - BitVec.ofInt w a = -(BitVec.ofInt w a)
  simp

theorem ofInt_mul (a b : Int) : ofInt (a * b) = ofInt a * ofInt b := by
  apply Z2.ext; intro w
  change BitVec.ofInt w (a * b) = BitVec.ofInt w a * BitVec.ofInt w b
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_mul]
  have ha := Int.emod_nonneg a (two_pow_ne_zero_int w)
  have hb := Int.emod_nonneg b (two_pow_ne_zero_int w)
  have hab := Int.emod_nonneg (a * b) (two_pow_ne_zero_int w)
  have hmod : (a * b) % ((2 ^ w : Nat) : Int) =
              ((a % ((2 ^ w : Nat) : Int)) * (b % ((2 ^ w : Nat) : Int))) % ((2 ^ w : Nat) : Int) :=
    Int.mul_emod a b _
  have hcast : ((((a % ((2 ^ w : Nat) : Int)).toNat * (b % ((2 ^ w : Nat) : Int)).toNat) % 2 ^ w : Nat) : Int) =
               ((a % ((2 ^ w : Nat) : Int)) * (b % ((2 ^ w : Nat) : Int))) % ((2 ^ w : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_mul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
  omega

theorem ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b := by
  rw [← ofInt_ofNat, ← ofInt_ofNat, ← ofInt_ofNat, Int.natCast_add, ofInt_add]

theorem ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b := by
  rw [← ofInt_ofNat, ← ofInt_ofNat, ← ofInt_ofNat, Int.natCast_mul, ofInt_mul]

theorem ofNat_xor (a b : Nat) : ofNat (a ^^^ b) = ofNat a ^^^ ofNat b := by
  apply Z2.ext; intro w
  change BitVec.ofNat w (a ^^^ b) = BitVec.ofNat w a ^^^ BitVec.ofNat w b
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem ofNat_and (a b : Nat) : ofNat (a &&& b) = ofNat a &&& ofNat b := by
  apply Z2.ext; intro w
  change BitVec.ofNat w (a &&& b) = BitVec.ofNat w a &&& BitVec.ofNat w b
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem ofNat_pow (a k : Nat) : ofNat (a ^ k) = (ofNat a) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, ofNat_mul, ih]
    rfl

theorem ofNat_proj_eq (x : Z2) (w : Nat) : (ofNat (x.proj w).toNat).proj w = x.proj w := by
  apply BitVec.eq_of_toNat_eq
  simp [ofNat]

theorem proj_eq_of_le {x y : Z2} {k w : Nat} (hk : k ≤ w) (h : x.proj w = y.proj w) :
    x.proj k = y.proj k := by
  rw [← x.proj_truncate hk, ← y.proj_truncate hk, h]

end Z2
private theorem bitvec_neg_add_self {w : Nat} (a : BitVec w) : -a + a = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.zero_mod]
  by_cases h : a.toNat = 0
  · simp [h]
  · have hlt : a.toNat < 2 ^ w := a.isLt
    have hsub : 2 ^ w - a.toNat < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt hsub]
    have hsum : 2 ^ w - a.toNat + a.toNat = 2 ^ w := by omega
    rw [hsum, Nat.mod_self]

-- ============================================================================
-- SECTION 2: Quantitative 2-Adic Continuity & Universal Density Identity Engine
-- ============================================================================

theorem isContinuous_of_1Lipschitz {F : Z2 → Z2} (h : Is1Lipschitz F) : IsContinuous F :=
  ⟨id, fun m => ⟨m, Nat.le_refl m⟩, h⟩

theorem hasModulus_id : HasModulus id (fun x => x) := fun _ _ _ h => h
theorem hasModulus_const (c : Z2) : HasModulus id (fun _ => c) := fun _ _ _ _ => rfl

theorem hasModulus_add {μ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ F) (hG : HasModulus μ G) :
    HasModulus μ (fun x => F x + G x) := by
  intro w x y hxy
  change (F x).proj (μ w) + (G x).proj (μ w) = (F y).proj (μ w) + (G y).proj (μ w)
  rw [hF w x y hxy, hG w x y hxy]

theorem hasModulus_sub {μ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ F) (hG : HasModulus μ G) :
    HasModulus μ (fun x => F x - G x) := by
  intro w x y hxy
  change (F x).proj (μ w) - (G x).proj (μ w) = (F y).proj (μ w) - (G y).proj (μ w)
  rw [hF w x y hxy, hG w x y hxy]

theorem hasModulus_mul {μ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ F) (hG : HasModulus μ G) :
    HasModulus μ (fun x => F x * G x) := by
  intro w x y hxy
  change (F x).proj (μ w) * (G x).proj (μ w) = (F y).proj (μ w) * (G y).proj (μ w)
  rw [hF w x y hxy, hG w x y hxy]

theorem hasModulus_neg {μ : Nat → Nat} {F : Z2 → Z2} (hF : HasModulus μ F) :
    HasModulus μ (fun x => -(F x)) := by
  intro w x y hxy
  change -((F x).proj (μ w)) = -((F y).proj (μ w))
  rw [hF w x y hxy]

theorem hasModulus_xor {μ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ F) (hG : HasModulus μ G) :
    HasModulus μ (fun x => F x ^^^ G x) := by
  intro w x y hxy
  change (F x).proj (μ w) ^^^ (G x).proj (μ w) = (F y).proj (μ w) ^^^ (G y).proj (μ w)
  rw [hF w x y hxy, hG w x y hxy]

theorem hasModulus_and {μ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ F) (hG : HasModulus μ G) :
    HasModulus μ (fun x => F x &&& G x) := by
  intro w x y hxy
  change (F x).proj (μ w) &&& (G x).proj (μ w) = (F y).proj (μ w) &&& (G y).proj (μ w)
  rw [hF w x y hxy, hG w x y hxy]

theorem hasModulus_pow {μ : Nat → Nat} {F : Z2 → Z2} (hF : HasModulus μ F) (r : Nat) :
    HasModulus μ (fun x => (F x) ^ r) := by
  induction r with
  | zero => intro w _ _ _; rfl
  | succ r ih => exact hasModulus_mul ih hF

theorem hasModulus_comp {μ₁ μ₂ : Nat → Nat} {F G : Z2 → Z2}
    (hF : HasModulus μ₁ F) (hG : HasModulus μ₂ G) :
    HasModulus (fun w => μ₁ (μ₂ w)) (fun x => F (G x)) := by
  intro w x y hxy
  exact hF (μ₂ w) (G x) (G y) (hG w x y hxy)

/-- Universal Density Identity Principle on `Z2`:
    Any two continuous functions on `Z2` that agree on `Nat` agree on ALL of `Z2`. -/
theorem z2_density_identity {F G : Z2 → Z2}
    (hF : IsContinuous F) (hG : IsContinuous G)
    (hNat : ∀ n : Nat, F (Z2.ofNat n) = G (Z2.ofNat n)) :
    ∀ x : Z2, F x = G x := by
  rcases hF with ⟨μF, hDivF, hModF⟩
  rcases hG with ⟨μG, hDivG, hModG⟩
  intro x
  apply Z2.ext; intro m
  rcases hDivF m with ⟨wF, hwF⟩
  rcases hDivG m with ⟨wG, hwG⟩
  let w := max wF wG
  let n := (x.proj w).toNat
  have hxn : (Z2.ofNat n).proj w = x.proj w := Z2.ofNat_proj_eq x w
  have hxF : (Z2.ofNat n).proj wF = x.proj wF := Z2.proj_eq_of_le (Nat.le_max_left wF wG) hxn
  have hxG : (Z2.ofNat n).proj wG = x.proj wG := Z2.proj_eq_of_le (Nat.le_max_right wF wG) hxn
  have h1 : (F (Z2.ofNat n)).proj m = (F x).proj m :=
    Z2.proj_eq_of_le hwF (hModF wF (Z2.ofNat n) x hxF)
  have h2 : (G (Z2.ofNat n)).proj m = (G x).proj m :=
    Z2.proj_eq_of_le hwG (hModG wG (Z2.ofNat n) x hxG)
  rw [← h1, ← h2, hNat n]

-- ============================================================================
-- SECTION 3: Rooted Van der Put Basis Engine on BitVec w and Z2
-- ============================================================================

private theorem sumRange_unique_hit (g : Nat → Int) (N idx : Nat) (hidx : idx < N)
    (hzero : ∀ i, i < N → i ≠ idx → g i = 0) :
    sumRange g N = g idx := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [sumRange]
    by_cases h : idx = N
    · subst h
      have h0 : sumRange g idx = 0 :=
        sumRange_zero (fun i hi => hzero i (Nat.lt_succ_of_lt hi) (by omega))
      rw [h0, Int.zero_add]
    · have hlt : idx < N := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hidx) h
      rw [hzero N (Nat.lt_succ_self N) (Ne.symm h), Int.add_zero]
      exact ih hlt (fun i hi hne => hzero i (Nat.lt_succ_of_lt hi) hne)

/-- Theorem 2A.1: Exact Finite Van der Put Reconstruction on `BitVec w`. -/
theorem vdp_reconstruct (f : Nat → Int) (w : Nat) (x : BitVec w) :
    vdpEval f w x = f x.toNat := by
  unfold vdpEval
  have hmain : ∀ m (y : Nat), y < 2 ^ m →
      sumRange (fun n => vdpCoeff f n * vdpBasis n y) (2 ^ m) = f y := by
    intro m
    induction m with
    | zero =>
      intro y hy
      have hy0 : y = 0 := by omega
      subst hy0
      simp [sumRange, vdpCoeff, vdpBasis]
    | succ m ih =>
      intro y hy
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      rw [hpow, sumRange_split]
      have h1 : sumRange (fun n => vdpCoeff f n * vdpBasis n y) (2 ^ m) = f (y % 2 ^ m) := by
        have heq : ∀ n, n < 2 ^ m → vdpBasis n y = vdpBasis n (y % 2 ^ m) := by
          intro n hn
          unfold vdpBasis
          by_cases hn0 : n = 0
          · simp [hn0]
          · simp only [hn0, ↓reduceIte]
            have hlog : Nat.log2 n + 1 ≤ m := by
              have hle : 2 ^ Nat.log2 n ≤ n := pow2_log2_le (by omega)
              have hlt_m : Nat.log2 n < m := Nat.lt_of_not_ge (fun hge => by
                have : 2 ^ m ≤ 2 ^ Nat.log2 n := Nat.pow_le_pow_right (by omega) hge
                omega)
              omega
            rw [Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 2 hlog)]
        have hsum_eq : ∀ N, (∀ n, n < N → vdpBasis n y = vdpBasis n (y % 2 ^ m)) →
            sumRange (fun n => vdpCoeff f n * vdpBasis n y) N =
            sumRange (fun n => vdpCoeff f n * vdpBasis n (y % 2 ^ m)) N := by
          intro N hN
          induction N with
          | zero => rfl
          | succ N ihN =>
            simp only [sumRange, hN N (Nat.lt_succ_self N),
                       ihN (fun n hn => hN n (Nat.lt_succ_of_lt hn))]
        rw [hsum_eq (2 ^ m) heq]
        exact ih (y % 2 ^ m) (Nat.mod_lt y (Nat.two_pow_pos m))
      rw [h1]
      by_cases hlt : y < 2 ^ m
      · have hmod : y % 2 ^ m = y := Nat.mod_eq_of_lt hlt
        rw [hmod]
        have hzero : sumRange (fun i => vdpCoeff f (2 ^ m + i) * vdpBasis (2 ^ m + i) y) (2 ^ m) = 0 := by
          apply sumRange_zero
          intro i hi
          have hne : 2 ^ m + i ≠ 0 := by have := Nat.two_pow_pos m; omega
          have hlog : Nat.log2 (2 ^ m + i) = m := log2_eq_of_bounds (by omega) (by omega)
          have hne_y : y ≠ 2 ^ m + i := by omega
          simp [vdpBasis, hlog, Nat.mod_eq_of_lt hy, hne_y]
        rw [hzero, Int.add_zero]
      · have hge : 2 ^ m ≤ y := Nat.le_of_not_lt hlt
        let idx := y - 2 ^ m
        have hidx : idx < 2 ^ m := by omega
        have hy_eq : 2 ^ m + idx = y := by omega
        have hmod : y % 2 ^ m = idx := by
          have : y = idx + 2 ^ m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
        rw [hmod]
        have hhit : sumRange (fun i => vdpCoeff f (2 ^ m + i) * vdpBasis (2 ^ m + i) y) (2 ^ m) =
                    vdpCoeff f y * 1 := by
          rw [sumRange_unique_hit _ (2 ^ m) idx hidx]
          · have hne : y ≠ 0 := by have := Nat.two_pow_pos m; omega
            have hlog : Nat.log2 y = m := log2_eq_of_bounds hge hy
            rw [hy_eq]
            simp [vdpBasis, hne, hlog, Nat.mod_eq_of_lt hy]
          · intro i hi hne_i
            have hne : 2 ^ m + i ≠ 0 := by have := Nat.two_pow_pos m; omega
            have hlog : Nat.log2 (2 ^ m + i) = m := log2_eq_of_bounds (by omega) (by omega)
            have hne_y : y ≠ 2 ^ m + i := by omega
            simp [vdpBasis, hlog, Nat.mod_eq_of_lt hy, hne_y]
        rw [hhit, Int.mul_one]
        have hne : y ≠ 0 := by have := Nat.two_pow_pos m; omega
        have hlog : Nat.log2 y = m := log2_eq_of_bounds hge hy
        simp [vdpCoeff, hne, hlog, idx]; omega
  exact hmain w x.toNat x.isLt

/-- Theorem 2A.2a: `vdpLift` satisfies the exact uniform modulus `μ` on all of `Z2`. -/
theorem vdpLift_hasModulus (f : Nat → Int) (μ invμ : Nat → Nat)
    (hMono : IsMonotone μ) (hInv : ∀ m, m ≤ μ (invμ m))
    (hVdP : ∀ n, 1 ≤ n → ((2 ^ μ (Nat.log2 n) : Nat) : Int) ∣ vdpCoeff f n) :
    HasModulus μ (vdpLift f μ invμ hMono hInv hVdP) := by
  intro w x y hxy
  change BitVec.ofInt (μ w) (f (x.proj (invμ (μ w))).toNat) =
         BitVec.ofInt (μ w) (f (y.proj (invμ (μ w))).toNat)
  rw [bitvec_ofInt_eq_iff_dvd]
  let w' := max w (invμ (μ w))
  let nx := (x.proj w').toNat
  let ny := (y.proj w').toNat
  have hnx_w : nx % 2 ^ w = (x.proj w).toNat := by
    have h := congrArg BitVec.toNat (x.proj_truncate (Nat.le_max_left w (invμ (μ w))))
    simpa [BitVec.truncate, nx, w'] using h
  have hny_w : ny % 2 ^ w = (y.proj w).toNat := by
    have h := congrArg BitVec.toNat (y.proj_truncate (Nat.le_max_left w (invμ (μ w))))
    simpa [BitVec.truncate, ny, w'] using h
  have hnx_i : nx % 2 ^ (invμ (μ w)) = (x.proj (invμ (μ w))).toNat := by
    have h := congrArg BitVec.toNat (x.proj_truncate (Nat.le_max_right w (invμ (μ w))))
    simpa [BitVec.truncate, nx, w'] using h
  have hny_i : ny % 2 ^ (invμ (μ w)) = (y.proj (invμ (μ w))).toNat := by
    have h := congrArg BitVec.toNat (y.proj_truncate (Nat.le_max_right w (invμ (μ w))))
    simpa [BitVec.truncate, ny, w'] using h
  have h1 : ((2 ^ μ w : Nat) : Int) ∣ (f nx - f (x.proj (invμ (μ w))).toNat) := by
    rw [← hnx_i]
    exact Int.dvd_trans (pow2_dvd_pow2_int (hInv (μ w))) (vdp_mod_congr hMono hVdP (invμ (μ w)) nx)
  have h2 : ((2 ^ μ w : Nat) : Int) ∣ (f ny - f (y.proj (invμ (μ w))).toNat) := by
    rw [← hny_i]
    exact Int.dvd_trans (pow2_dvd_pow2_int (hInv (μ w))) (vdp_mod_congr hMono hVdP (invμ (μ w)) ny)
  have h3 : ((2 ^ μ w : Nat) : Int) ∣ (f nx - f (x.proj w).toNat) := by
    rw [← hnx_w]; exact vdp_mod_congr hMono hVdP w nx
  have h4 : ((2 ^ μ w : Nat) : Int) ∣ (f ny - f (y.proj w).toNat) := by
    rw [← hny_w]; exact vdp_mod_congr hMono hVdP w ny
  have hxy_nat : (x.proj w).toNat = (y.proj w).toNat := congrArg BitVec.toNat hxy
  have hdiff : f (x.proj (invμ (μ w))).toNat - f (y.proj (invμ (μ w))).toNat =
      ((f nx - f (x.proj w).toNat) - (f nx - f (x.proj (invμ (μ w))).toNat)) -
      ((f ny - f (y.proj w).toNat) - (f ny - f (y.proj (invμ (μ w))).toNat)) := by
    rw [hxy_nat]; omega
  rw [hdiff]
  exact Int.dvd_sub (Int.dvd_sub h3 h1) (Int.dvd_sub h4 h2)

theorem vdpLift_isContinuous (f : Nat → Int) (μ invμ : Nat → Nat)
    (hMono : IsMonotone μ) (hInv : ∀ m, m ≤ μ (invμ m))
    (hVdP : ∀ n, 1 ≤ n → ((2 ^ μ (Nat.log2 n) : Nat) : Int) ∣ vdpCoeff f n) :
    IsContinuous (vdpLift f μ invμ hMono hInv hVdP) :=
  ⟨μ, fun m => ⟨invμ m, hInv m⟩, vdpLift_hasModulus f μ invμ hMono hInv hVdP⟩

/-- Theorem 2A.2b: `vdpLift` agrees with `f` on every natural number `n`. -/
theorem vdpLift_ofNat (f : Nat → Int) (μ invμ : Nat → Nat)
    (hMono : IsMonotone μ) (hInv : ∀ m, m ≤ μ (invμ m))
    (hVdP : ∀ n, 1 ≤ n → ((2 ^ μ (Nat.log2 n) : Nat) : Int) ∣ vdpCoeff f n)
    (n : Nat) :
    vdpLift f μ invμ hMono hInv hVdP (Z2.ofNat n) = Z2.ofInt (f n) := by
  apply Z2.ext; intro m
  change BitVec.ofInt m (f (BitVec.ofNat (invμ m) n).toNat) = BitVec.ofInt m (f n)
  rw [bitvec_ofInt_eq_iff_dvd]
  simp only [BitVec.toNat_ofNat]
  have hd := Int.dvd_trans (pow2_dvd_pow2_int (hInv m)) (vdp_mod_congr hMono hVdP (invμ m) n)
  have hneg : f (n % 2 ^ invμ m) - f n = -(f n - f (n % 2 ^ invμ m)) := by omega
  rw [hneg]
  exact Int.dvd_neg.mpr hd

/-- Theorem 2A.2c (Sharpness Converse):
    If ANY `F : Z2 → Z2` has modulus `μ` and extends `f`, then EVERY Van der Put coefficient
    `vdpCoeff f n` (`n ≥ 1`) MUST be divisible by `2 ^ μ (Nat.log2 n)`. -/
theorem vdp_necessity {f : Nat → Int} {μ : Nat → Nat} {F : Z2 → Z2}
    (hMod : HasModulus μ F) (hExt : ∀ n : Nat, F (Z2.ofNat n) = Z2.ofInt (f n)) :
    ∀ n, 1 ≤ n → ((2 ^ μ (Nat.log2 n) : Nat) : Int) ∣ vdpCoeff f n := by
  intro n hn
  let k := Nat.log2 n
  have h2k : 2 ^ k ≤ n := pow2_log2_le hn
  have hproj : (Z2.ofNat n).proj k = (Z2.ofNat (n - 2 ^ k)).proj k := by
    apply BitVec.eq_of_toNat_eq
    simp only [Z2.ofNat, BitVec.toNat_ofNat]
    have hsplit : n = n - 2 ^ k + 2 ^ k := by omega
    have hmod : n % 2 ^ k = (n - 2 ^ k + 2 ^ k) % 2 ^ k := congrArg (· % 2 ^ k) hsplit
    rw [hmod, Nat.add_mod_right]
  have hF := hMod k (Z2.ofNat n) (Z2.ofNat (n - 2 ^ k)) hproj
  rw [hExt n, hExt (n - 2 ^ k)] at hF
  change BitVec.ofInt (μ k) (f n) = BitVec.ofInt (μ k) (f (n - 2 ^ k)) at hF
  rw [bitvec_ofInt_eq_iff_dvd] at hF
  have hne : n ≠ 0 := by omega
  simpa [vdpCoeff, hne, k] using hF

-- ============================================================================
-- SECTION 4: Discrete Mahler Forward-Difference Engine & Mahler -> VdP Bridge
-- ============================================================================

theorem mahler1LipschitzLift_is1Lipschitz (f : Nat → Int)
    (hMahler : ∀ n, 1 ≤ n → ((2 ^ Nat.log2 n : Nat) : Int) ∣ mahlerCoeff f n) :
    Is1Lipschitz (mahler1LipschitzLift f hMahler) :=
  vdpLift_hasModulus f id id (fun _ _ h => h) (fun m => Nat.le_refl m) (mahler_to_vdp_1lipschitz hMahler)

theorem mahler1LipschitzLift_ofNat (f : Nat → Int)
    (hMahler : ∀ n, 1 ≤ n → ((2 ^ Nat.log2 n : Nat) : Int) ∣ mahlerCoeff f n) (n : Nat) :
    mahler1LipschitzLift f hMahler (Z2.ofNat n) = Z2.ofInt (f n) :=
  vdpLift_ofNat f id id (fun _ _ h => h) (fun m => Nat.le_refl m) (mahler_to_vdp_1lipschitz hMahler) n

/-- Theorem 2B.3 (Constructive Quantitative Mahler Continuity Theorem via Van der Put Bridge!):
    Any monotone diverging Mahler valuation lower bound `ν(n) → ∞` yields quantitative
    Van der Put divisibility, hence lifts `f` to a continuous function on `Z2`. -/
theorem mahler_to_vdp_continuous {f : Nat → Int} {ν invν : Nat → Nat}
    (hMonoν : IsMonotone ν)
    (hInvν : ∀ m, m ≤ ν (invν m))
    (hMahler : ∀ n, 1 ≤ n → ((2 ^ ν n : Nat) : Int) ∣ mahlerCoeff f n) :
    ∀ m n : Nat, 1 ≤ n → m + Nat.log2 (max 1 (invν m)) ≤ Nat.log2 n →
      ((2 ^ m : Nat) : Int) ∣ vdpCoeff f n := by
  intro m n hn hlog
  let k := Nat.log2 n
  have hne : n ≠ 0 := by omega
  have h2k : 2 ^ k ≤ n := pow2_log2_le hn
  let x := n - 2 ^ k
  have hnx : n = x + 2 ^ k := by omega
  have hvdp : vdpCoeff f n = f (x + 2 ^ k) - f x := by
    simp only [vdpCoeff, hne, ↓reduceIte]
    have h1 : n - 2 ^ Nat.log2 n = x := rfl
    rw [h1, ← hnx]
  rw [hvdp, mahler_shift_sum]
  apply sumRange_dvd
  intro j _hj
  by_cases hj0 : j = 0
  · subst hj0; simp
  · have hj1 : 1 ≤ j := by omega
    by_cases hjN : invν m ≤ j
    · have hmv : m ≤ ν j := Nat.le_trans (hInvν m) (hMonoν (invν m) j hjN)
      exact Int.dvd_mul_of_dvd_left (Int.dvd_trans (pow2_dvd_pow2_int hmv) (hMahler j hj1))
    · have hj_le : j ≤ max 1 (invν m) := by omega
      have hlogj : Nat.log2 j ≤ Nat.log2 (max 1 (invν m)) := log2_mono hj1 hj_le
      have hlogj_k : Nat.log2 j ≤ k := by omega
      have hm_le : m ≤ k - Nat.log2 j := by omega
      have hd := Int.dvd_trans (pow2_dvd_pow2_int hm_le) (two_pow_dvd_choose_shift (w := k) (x := x) hj1 hlogj_k)
      exact Int.dvd_mul_of_dvd_right hd

-- ============================================================================
-- SECTION 5: Reusable Finite-to-Infinite Silicon Certificate Compilers
--   (Affine 2-Regular Matrix Engine + Lattice Contraction + Sharpness + Kernel ID)
-- ============================================================================

theorem finSum_dvd {n : Nat} {d : Int} {f : Fin n → Int} (h : ∀ i, d ∣ f i) :
    d ∣ finSum f := by
  induction n with
  | zero => exact Int.dvd_zero d
  | succ n ih =>
    simp only [finSum]
    exact Int.dvd_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

private theorem finSum2 (f : Fin 2 → Int) :
    finSum f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  simp [finSum, Fin.castSucc, Fin.castAdd, Fin.last]

private theorem finSum3 (f : Fin 3 → Int) :
    finSum f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ := by
  simp [finSum, Fin.castSucc, Fin.castAdd, Fin.last]

theorem latticeCertLift_hasModulus {r d L s : Nat} (hL : 1 ≤ L) (hs : 1 ≤ s)
    (cert : LatticeContractCert r d L s) {c0 c1 : Vec r} {g : Nat → Vec r}
    (hReg : IsAffineTwoRegular cert.A0 cert.A1 c0 c1 g)
    (hValid : cert.Valid (vdpCoeffVec g 1)) (u : Vec r) :
    HasModulus (fun w => s * (w / L)) (latticeCertLift hL hs cert hReg hValid u) :=
  vdpLift_hasModulus _ _ _ _ _ _

theorem latticeCertLift_ofNat {r d L s : Nat} (hL : 1 ≤ L) (hs : 1 ≤ s)
    (cert : LatticeContractCert r d L s) {c0 c1 : Vec r} {g : Nat → Vec r}
    (hReg : IsAffineTwoRegular cert.A0 cert.A1 c0 c1 g)
    (hValid : cert.Valid (vdpCoeffVec g 1)) (u : Vec r) (n : Nat) :
    latticeCertLift hL hs cert hReg hValid u (Z2.ofNat n) = Z2.ofInt (dotVec u (g n)) :=
  vdpLift_ofNat _ _ _ _ _ _ n

-- ----------------------------------------------------------------------------
-- COMPILER B: Finite 2-Adic Sharpness Witness -> Exact Lower Bound on Holder Exponent
-- ----------------------------------------------------------------------------

theorem iterWord_pos (L w m : Nat) : 1 ≤ iterWord L w m := by
  induction m with
  | zero => exact Nat.le_refl 1
  | succ m ih =>
    simp only [iterWord]
    have := Nat.two_pow_pos L
    have h1 : 1 * 1 ≤ iterWord L w m * 2 ^ L := Nat.mul_le_mul ih this
    omega

theorem iterWord_log2 (L w : Nat) (hw : w < 2 ^ L) (m : Nat) :
    Nat.log2 (iterWord L w m) = m * L := by
  induction m with
  | zero => simp [iterWord]
  | succ m ih =>
    simp only [iterWord]
    have hm1 : 2 ^ (m * L) ≤ iterWord L w m := by
      rw [← ih]; exact pow2_log2_le (iterWord_pos L w m)
    have hm2 : iterWord L w m < 2 ^ (m * L + 1) := by
      rw [← ih]; exact lt_pow2_log2_succ (iterWord_pos L w m)
    have hlow : 2 ^ ((m + 1) * L) ≤ iterWord L w m * 2 ^ L + w := by
      have hmul : 2 ^ (m * L) * 2 ^ L ≤ iterWord L w m * 2 ^ L := Nat.mul_le_mul_right _ hm1
      rw [← Nat.pow_add] at hmul
      have hexp : m * L + L = (m + 1) * L := by rw [Nat.succ_mul]
      rw [hexp] at hmul
      omega
    have hhigh : iterWord L w m * 2 ^ L + w < 2 ^ ((m + 1) * L + 1) := by
      have hle : iterWord L w m + 1 ≤ 2 ^ (m * L + 1) := hm2
      have hmul : (iterWord L w m + 1) * 2 ^ L ≤ 2 ^ (m * L + 1) * 2 ^ L := Nat.mul_le_mul_right _ hle
      rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add] at hmul
      have hexp : m * L + 1 + L = (m + 1) * L + 1 := by rw [Nat.succ_mul]; omega
      rw [hexp] at hmul
      omega
    exact log2_eq_of_bounds hlow hhigh

/-- Exact Van der Put value along `iterWord L wStar m`. -/
theorem lattice_cert_iterWord {r d L s : Nat}
    (cert : LatticeContractCert r d L s) {c0 c1 : Vec r} {g : Nat → Vec r}
    (hReg : IsAffineTwoRegular cert.A0 cert.A1 c0 c1 g)
    (hValid : cert.Valid (vdpCoeffVec g 1))
    (wStar : Fin (2 ^ L)) (m : Nat) :
    vdpCoeffVec g (iterWord L wStar.val m) =
    scaleVec ((2 ^ (s * m) : Nat) : Int) (matVec cert.P (matVec (matPow (cert.Q wStar) m) cert.z0)) := by
  induction m with
  | zero =>
    simp only [iterWord, Nat.mul_zero, Nat.pow_zero, matPow, matVec_id]
    funext i; simp [scaleVec, hValid.1 i]
  | succ m ih =>
    let n := iterWord L wStar.val (m + 1)
    have h2L : 2 ^ L ≤ n := by
      have hpos := iterWord_pos L wStar.val m
      have hmul : 1 * 2 ^ L ≤ iterWord L wStar.val m * 2 ^ L := Nat.mul_le_mul_right _ hpos
      simp only [n, iterWord]; omega
    have hmod : n % 2 ^ L = wStar.val := by
      simp only [n, iterWord]
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt wStar.isLt]
    have hdiv : n / 2 ^ L = iterWord L wStar.val m := by
      simp only [n, iterWord]
      rw [Nat.mul_comm (iterWord L wStar.val m), Nat.mul_add_div (Nat.two_pow_pos L),
          Nat.div_eq_of_lt wStar.isLt, Nat.add_zero]
    change vdpCoeffVec g n = _
    rw [vdp_peel_word hReg L n h2L, hmod, hdiv, ih, matVec_scale, ← matVec_mul]
    have hmat : matMul (wordMat cert.A0 cert.A1 L wStar.val) cert.P =
                scaleMat ((2 ^ s : Nat) : Int) (matMul cert.P (cert.Q wStar)) := by
      funext i j; exact hValid.2 wStar i j
    rw [hmat, matPow, matVec_mul]
    funext i
    simp only [scaleVec, matVec, scaleMat, matMul]
    have hpull :
        finSum (fun j => ((2 ^ s : Nat) : Int) * finSum (fun k => cert.P i k * cert.Q wStar k j) *
                         finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l)) =
        ((2 ^ s : Nat) : Int) *
          finSum (fun k => cert.P i k *
            finSum (fun j => cert.Q wStar k j *
              finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l))) := by
      have h1 :
          finSum (fun j => ((2 ^ s : Nat) : Int) * finSum (fun k => cert.P i k * cert.Q wStar k j) *
                           finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l)) =
          ((2 ^ s : Nat) : Int) *
            finSum (fun j => finSum (fun k => cert.P i k * cert.Q wStar k j) *
                             finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l)) := by
        rw [← finSum_mul_left]
        apply finSum_congr; intro j; exact Int.mul_assoc _ _ _
      rw [h1]; congr 1
      have h2 :
          finSum (fun j => finSum (fun k => cert.P i k * cert.Q wStar k j) *
                           finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l)) =
          finSum (fun j => finSum (fun k => cert.P i k * (cert.Q wStar k j *
                           finSum (fun l => matPow (cert.Q wStar) m j l * cert.z0 l)))) := by
        apply finSum_congr; intro j
        rw [← finSum_mul_right]
        apply finSum_congr; intro k; exact Int.mul_assoc _ _ _
      rw [h2, finSum_comm]
      apply finSum_congr; intro k
      rw [finSum_mul_left]
    rw [hpull, ← Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add]
    have hexp : s * m + s = s * (m + 1) := by rw [Nat.mul_succ]
    rw [hexp]

private theorem matPow_add {r : Nat} (A : Mat r r) (a b : Nat) (v : Vec r) :
    matVec (matPow A (a + b)) v = matVec (matPow A a) (matVec (matPow A b) v) := by
  induction a with
  | zero => simp [matPow, matVec_id]
  | succ a ih =>
    rw [Nat.succ_add, matPow, matPow, matVec_mul, matVec_mul, ih]

private theorem matVec_mod2_congr {r c : Nat} (A : Mat r c) {u v : Vec c}
    (h : ∀ j, (2 : Int) ∣ (u j - v j)) :
    ∀ i, (2 : Int) ∣ (matVec A u i - matVec A v i) := by
  intro i
  have hsub : matVec A u i - matVec A v i = finSum (fun j => A i j * (u j - v j)) := by
    simp only [matVec, ← finSum_sub]
    apply finSum_congr; intro j; exact (Int.mul_sub _ _ _).symm
  rw [hsub]
  exact finSum_dvd (fun j => Int.dvd_mul_of_dvd_right (h j))

/-- Theorem 3B (Compiler B Sharpness Soundness):
    A finite `decide`-checked `SharpHolderCert` proves that for ALL `k : Nat`,
    along `n_k = iterWord L w* (k * p)` (of bit-length `k * p * L`),
    `2^(s * k * p + 1)` DOES NOT DIVIDE `B~_{n_k}(u · g)` — hence NO continuous extension
    can achieve modulus `μ(k * p * L) ≥ s * k * p + 1`! -/
theorem sharp_holder_sound {r d L s : Nat}
    (cert : LatticeContractCert r d L s) {c0 c1 : Vec r} {g : Nat → Vec r}
    (hReg : IsAffineTwoRegular cert.A0 cert.A1 c0 c1 g)
    (hValid : cert.Valid (vdpCoeffVec g 1))
    (u : Vec r) (sc : SharpHolderCert cert u) (hSharp : sc.Valid) :
    ∀ k : Nat,
      ¬ (((2 ^ (s * (k * sc.period) + 1) : Nat) : Int) ∣
          vdpCoeff (fun x => dotVec u (g x)) (iterWord L sc.wStar.val (k * sc.period))) := by
  -- Step 1: By induction on k, Q^{k*p} * z0 ≡ z0 (mod 2)
  have horbit : ∀ k j, (2 : Int) ∣ (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0 j - cert.z0 j) := by
    intro k
    induction k with
    | zero =>
      intro j; simp [matPow, matVec_id]
    | succ k ih =>
      intro j
      have hmul : (k + 1) * sc.period = sc.period + k * sc.period := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hmul, matPow_add]
      have h1 := matVec_mod2_congr (matPow (cert.Q sc.wStar) sc.period) ih j
      have h2 : (2 : Int) ∣ (matVec (matPow (cert.Q sc.wStar) sc.period) cert.z0 j - cert.z0 j) :=
        Int.dvd_of_emod_eq_zero (hSharp.1 j)
      have hadd : matVec (matPow (cert.Q sc.wStar) sc.period)
                    (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0) j - cert.z0 j =
                  (matVec (matPow (cert.Q sc.wStar) sc.period)
                    (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0) j -
                   matVec (matPow (cert.Q sc.wStar) sc.period) cert.z0 j) +
                  (matVec (matPow (cert.Q sc.wStar) sc.period) cert.z0 j - cert.z0 j) := by omega
      rw [hadd]
      exact Int.dvd_add h1 h2
  -- Step 2: Therefore u · (P · Q^{k*p} z0) is ODD for all k!
  intro k hdvd
  rw [vdpCoeff_dotVec, lattice_cert_iterWord cert hReg hValid sc.wStar (k * sc.period), dotVec_scale] at hdvd
  have hodd_diff : (2 : Int) ∣
      (dotVec u (matVec cert.P (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0)) -
       dotVec u (matVec cert.P cert.z0)) := by
    have hP := matVec_mod2_congr cert.P (horbit k)
    have hdot : dotVec u (matVec cert.P (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0)) -
                dotVec u (matVec cert.P cert.z0) =
                finSum (fun i => u i * (matVec cert.P (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0) i -
                                        matVec cert.P cert.z0 i)) := by
      simp only [dotVec, ← finSum_sub]
      apply finSum_congr; intro i; exact (Int.mul_sub _ _ _).symm
    rw [hdot]
    exact finSum_dvd (fun i => Int.dvd_mul_of_dvd_right (hP i))
  have hpow_split : ((2 ^ (s * (k * sc.period) + 1) : Nat) : Int) =
                    ((2 ^ (s * (k * sc.period)) : Nat) : Int) * 2 := by
    rw [Nat.pow_succ, Int.natCast_mul]; rfl
  rw [hpow_split] at hdvd
  rcases hdvd with ⟨q, hq⟩
  have hne : ((2 ^ (s * (k * sc.period)) : Nat) : Int) ≠ 0 := two_pow_ne_zero_int _
  have heven : dotVec u (matVec cert.P (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0)) = 2 * q := by
    have hmul' : ((2 ^ (s * (k * sc.period)) : Nat) : Int) *
                 dotVec u (matVec cert.P (matVec (matPow (cert.Q sc.wStar) (k * sc.period)) cert.z0)) =
                 ((2 ^ (s * (k * sc.period)) : Nat) : Int) * (2 * q) := by
      rw [hq, Int.mul_assoc]
    exact Int.eq_of_mul_eq_mul_left hne hmul'
  rcases hodd_diff with ⟨t, ht⟩
  have h1 := hSharp.2
  omega

/-- Corollary: NO continuous extension `F` of `u · g` can satisfy `HasModulus μ F`
    with `μ(k * p * L) ≥ s * k * p + 1`! -/
theorem sharp_holder_no_better_modulus {r d L s : Nat}
    (cert : LatticeContractCert r d L s) {c0 c1 : Vec r} {g : Nat → Vec r}
    (hReg : IsAffineTwoRegular cert.A0 cert.A1 c0 c1 g)
    (hValid : cert.Valid (vdpCoeffVec g 1))
    (u : Vec r) (sc : SharpHolderCert cert u) (hSharp : sc.Valid)
    {F : Z2 → Z2} {μ : Nat → Nat}
    (hMod : HasModulus μ F) (hExt : ∀ n, F (Z2.ofNat n) = Z2.ofInt (dotVec u (g n)))
    (k : Nat) :
    μ (k * sc.period * L) ≤ s * (k * sc.period) := by
  exact Nat.le_of_not_lt (fun hgt => by
    have hne := sharp_holder_sound cert hReg hValid u sc hSharp k
    let n := iterWord L sc.wStar.val (k * sc.period)
    have hlog : Nat.log2 n = k * sc.period * L := iterWord_log2 L sc.wStar.val sc.wStar.isLt (k * sc.period)
    have hdvd := vdp_necessity hMod hExt n (iterWord_pos L sc.wStar.val (k * sc.period))
    rw [hlog] at hdvd
    exact hne (Int.dvd_trans (pow2_dvd_pow2_int hgt) hdvd))

-- ----------------------------------------------------------------------------
-- COMPILER C: Finite Kernel-Invariant Certificate -> Infinite Z2 Functional Identity
-- ----------------------------------------------------------------------------

/-- Theorem 3C (Compiler C Soundness):
    A finite `decide`-checked `KernelIdCert` proves `U · F(n) = 0` for ALL `n : Nat`. -/
theorem kernel_id_cert_sound {r d : Nat} (cert : KernelIdCert r d) {F : Nat → Vec r}
    (hReg : ∀ n, F (2 * n) = matVec cert.M0 (F n) ∧ F (2 * n + 1) = matVec cert.M1 (F n))
    (hValid : cert.Valid (F 0)) :
    ∀ (n : Nat) (i : Fin d), matVec cert.U (F n) i = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i
    by_cases hn : n = 0
    · subst hn; exact hValid.2.2 i
    · have hhalf : n / 2 < n := by omega
      have hih : matVec cert.U (F (n / 2)) = fun _ => 0 := funext (ih (n / 2) hhalf)
      by_cases hpar : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        rw [heq, (hReg (n / 2)).1, ← matVec_mul]
        have hM0 : matMul cert.U cert.M0 = matMul cert.C0 cert.U := by
          funext a b; exact hValid.1 a b
        rw [hM0, matVec_mul, hih]
        simp only [matVec]
        exact finSum_zero _ (fun j => by simp)
      · have heq : n = 2 * (n / 2) + 1 := by omega
        rw [heq, (hReg (n / 2)).2, ← matVec_mul]
        have hM1 : matMul cert.U cert.M1 = matMul cert.C1 cert.U := by
          funext a b; exact hValid.2.1 a b
        rw [hM1, matVec_mul, hih]
        simp only [matVec]
        exact finSum_zero _ (fun j => by simp)

-- ============================================================================
-- SECTION 6: Concrete Novel Infinite 2-Adic Theorems, Non-Vacuity & Sharpness
-- ============================================================================

-- ----------------------------------------------------------------------------
-- THEOREM I: Infinite q-Deformed Gray-Alternating 2-Adic Duality
-- ----------------------------------------------------------------------------

theorem phiZ2_is1Lipschitz (q : Int) (hq : (2 : Int) ∣ q) : Is1Lipschitz (phiZ2 q hq) :=
  vdpLift_hasModulus _ _ _ _ _ _

theorem thetaZ2_is1Lipschitz (q : Int) (hq : (2 : Int) ∣ q) : Is1Lipschitz (thetaZ2 q hq) :=
  vdpLift_hasModulus _ _ _ _ _ _

theorem phiZ2_ofNat (q : Int) (hq : (2 : Int) ∣ q) (n : Nat) :
    phiZ2 q hq (Z2.ofNat n) = Z2.ofInt (phiNat q n) :=
  vdpLift_ofNat _ _ _ _ _ _ n

theorem thetaZ2_ofNat (q : Int) (hq : (2 : Int) ∣ q) (n : Nat) :
    thetaZ2 q hq (Z2.ofNat n) = Z2.ofInt (thetaNat q n) :=
  vdpLift_ofNat _ _ _ _ _ _ n

/-- Enhanced `r`-Holder modulus for `Φ_q` whenever `2^r ∣ q` (e.g., `Φ_{2^r}` is `r`-Holder!). -/
theorem phiZ2_hasHolderModulus (q : Int) (r : Nat) (hr : 1 ≤ r)
    (hq : ((2 ^ r : Nat) : Int) ∣ q) :
    HasModulus (fun w => r * w) (phiZ2 q (Int.dvd_trans (pow2_dvd_pow2_int hr) hq)) := by
  let hq2 : (2 : Int) ∣ q := Int.dvd_trans (pow2_dvd_pow2_int hr) hq
  let hMono : IsMonotone (fun w => r * w) := fun a b hab => Nat.mul_le_mul_left r hab
  let hInv : ∀ m, m ≤ r * id m := fun m => Nat.le_mul_of_pos_left m (by omega)
  let hVdP : ∀ n, 1 ≤ n → ((2 ^ (r * Nat.log2 n) : Nat) : Int) ∣ vdpCoeff (phiNat q) n :=
    fun n hn => by
      rw [vdpCoeff_phiNat q n hn]
      have hpow : ((2 ^ (r * Nat.log2 n) : Nat) : Int) = (((2 ^ r : Nat) : Int) ^ Nat.log2 n) := by
        rw [Nat.pow_mul, Int.natCast_pow]
      rw [hpow]
      exact dvd_pow_of_dvd hq (Nat.log2 n)
  let F := vdpLift (phiNat q) (fun w => r * w) id hMono hInv hVdP
  have hEq : phiZ2 q hq2 = F := by
    funext x
    exact z2_density_identity
      (isContinuous_of_1Lipschitz (phiZ2_is1Lipschitz q hq2))
      (vdpLift_isContinuous (phiNat q) (fun w => r * w) id hMono hInv hVdP)
      (fun n => by rw [phiZ2_ofNat, vdpLift_ofNat]) x
  rw [hEq]
  exact vdpLift_hasModulus (phiNat q) (fun w => r * w) id hMono hInv hVdP

-- Bitwise helper lemmas in core Lean 4
private theorem my_testBit_two_mul_zero (m : Nat) : (2 * m).testBit 0 = false := by
  simp [Nat.testBit_zero]

private theorem my_testBit_two_mul_succ (m i : Nat) : (2 * m).testBit (i + 1) = m.testBit i := by
  rw [Nat.testBit_succ]; congr 1; omega

private theorem my_testBit_two_mul_add_one_zero (m : Nat) : (2 * m + 1).testBit 0 = true := by
  simp [Nat.testBit_zero]

private theorem my_testBit_two_mul_add_one_succ (m i : Nat) : (2 * m + 1).testBit (i + 1) = m.testBit i := by
  rw [Nat.testBit_succ]; congr 1; omega

private theorem xor_two_mul_even (k : Nat) :
    (2 * (2 * k)) ^^^ (2 * k) = 2 * ((2 * k) ^^^ k) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp
  | succ i => simp [my_testBit_two_mul_succ]

private theorem xor_two_mul_odd (k : Nat) :
    (2 * (2 * k + 1)) ^^^ (2 * k + 1) = 2 * ((2 * k + 1) ^^^ k) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp
  | succ i => simp [my_testBit_two_mul_succ, my_testBit_two_mul_add_one_succ]

private theorem xor_two_mul_add_one_even (k : Nat) :
    (2 * (2 * k) + 1) ^^^ (2 * k) = 2 * ((2 * k) ^^^ k) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp
  | succ i => simp [my_testBit_two_mul_succ, my_testBit_two_mul_add_one_succ]

private theorem xor_two_mul_add_one_odd (k : Nat) :
    (2 * (2 * k + 1) + 1) ^^^ (2 * k + 1) = 2 * ((2 * k + 1) ^^^ k) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp
  | succ i => simp [my_testBit_two_mul_succ, my_testBit_two_mul_add_one_succ]

/-- Finite-Nat version of the q-deformed Gray-Alternating Duality (proved simultaneously for both branches). -/
theorem q_gray_alternating_duality_nat (q : Int) :
    ∀ x : Nat,
      thetaNat q ((2 * x) ^^^ x) = -(q - 1) * phiNat q x ∧
      thetaNat q ((2 * x + 1) ^^^ x) = (q - 1) * phiNat q x + 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx0 : x = 0
    · subst hx0
      simp [phiNat_zero, thetaNat_zero, thetaNat_two_mul_add_one q 0]
    · let m := x / 2
      have hm_lt : m < x := by omega
      rcases ih m hm_lt with ⟨ihE, ihO⟩
      by_cases hpar : x % 2 = 0
      · have hx : x = 2 * m := by omega
        rw [hx, xor_two_mul_even, xor_two_mul_add_one_even,
            thetaNat_two_mul, thetaNat_two_mul_add_one, phiNat_two_mul, ihE]
        constructor
        · rw [Int.mul_left_comm]
        · rw [Int.neg_mul, Int.mul_neg, Int.sub_eq_add_neg, Int.neg_neg, Int.mul_left_comm, Int.add_comm]
      · have hx : x = 2 * m + 1 := by omega
        rw [hx, xor_two_mul_odd, xor_two_mul_add_one_odd,
            thetaNat_two_mul_add_one, thetaNat_two_mul, phiNat_two_mul_add_one, ihO]
        constructor
        · rw [Int.mul_add, Int.mul_one, Int.neg_mul, Int.mul_add, Int.mul_one, Int.mul_left_comm]
          omega
        · rw [Int.mul_add, Int.mul_one, Int.mul_add, Int.mul_one, Int.mul_left_comm]
          omega

/-- THEOREM Ia (Infinite q-Deformed Gray-Alternating 2-Adic Duality — Even Branch):
    For EVERY even `q : Int` and EVERY `x : Z2`:
    `Θ_q((2x) ^^^ x) = -(q - 1) * Φ_q(x)`. -/
theorem q_gray_alternating_duality_even (q : Int) (hq : (2 : Int) ∣ q) :
    ∀ x : Z2, thetaZ2 q hq ((2 * x) ^^^ x) = -(Z2.ofInt (q - 1)) * phiZ2 q hq x := by
  have hLHS : IsContinuous (fun x => thetaZ2 q hq ((2 * x) ^^^ x)) :=
    isContinuous_of_1Lipschitz (hasModulus_comp (thetaZ2_is1Lipschitz q hq)
      (hasModulus_xor (hasModulus_mul (hasModulus_const 2) hasModulus_id) hasModulus_id))
  have hRHS : IsContinuous (fun x => -(Z2.ofInt (q - 1)) * phiZ2 q hq x) :=
    isContinuous_of_1Lipschitz (hasModulus_mul (hasModulus_const _) (phiZ2_is1Lipschitz q hq))
  apply z2_density_identity hLHS hRHS
  intro n
  have h2n : (2 : Z2) * Z2.ofNat n = Z2.ofNat (2 * n) := (Z2.ofNat_mul 2 n).symm
  rw [h2n, ← Z2.ofNat_xor, thetaZ2_ofNat, phiZ2_ofNat, ← Z2.ofInt_neg, ← Z2.ofInt_mul]
  rw [(q_gray_alternating_duality_nat q n).1]

/-- THEOREM Ib (Infinite q-Deformed Gray-Alternating 2-Adic Duality — Odd Branch):
    For EVERY even `q : Int` and EVERY `x : Z2`:
    `Θ_q((2x + 1) ^^^ x) = (q - 1) * Φ_q(x) + 1`. -/
theorem q_gray_alternating_duality_odd (q : Int) (hq : (2 : Int) ∣ q) :
    ∀ x : Z2, thetaZ2 q hq ((2 * x + 1) ^^^ x) = Z2.ofInt (q - 1) * phiZ2 q hq x + 1 := by
  have hLHS : IsContinuous (fun x => thetaZ2 q hq ((2 * x + 1) ^^^ x)) :=
    isContinuous_of_1Lipschitz (hasModulus_comp (thetaZ2_is1Lipschitz q hq)
      (hasModulus_xor (hasModulus_add (hasModulus_mul (hasModulus_const 2) hasModulus_id) (hasModulus_const 1))
        hasModulus_id))
  have hRHS : IsContinuous (fun x => Z2.ofInt (q - 1) * phiZ2 q hq x + 1) :=
    isContinuous_of_1Lipschitz (hasModulus_add (hasModulus_mul (hasModulus_const _) (phiZ2_is1Lipschitz q hq))
      (hasModulus_const 1))
  apply z2_density_identity hLHS hRHS
  intro n
  have h2n : (2 : Z2) * Z2.ofNat n = Z2.ofNat (2 * n) := (Z2.ofNat_mul 2 n).symm
  have h2n1 : (2 : Z2) * Z2.ofNat n + 1 = Z2.ofNat (2 * n + 1) := by
    rw [h2n]; exact (Z2.ofNat_add (2 * n) 1).symm
  rw [h2n1, ← Z2.ofNat_xor, thetaZ2_ofNat, phiZ2_ofNat, ← Z2.ofInt_mul,
      show (1 : Z2) = Z2.ofInt 1 from (Z2.ofInt_ofNat 1).symm, ← Z2.ofInt_add]
  rw [(q_gray_alternating_duality_nat q n).2]

/-- THEOREM Ic (Universal q-Independent Conservation Law on Z2):
    For EVERY even `q : Int` and EVERY `x : Z2`:
    `Θ_q((2x) ^^^ x) + Θ_q((2x + 1) ^^^ x) = 1`. -/
theorem q_gray_conservation_Z2 (q : Int) (hq : (2 : Int) ∣ q) (x : Z2) :
    thetaZ2 q hq ((2 * x) ^^^ x) + thetaZ2 q hq ((2 * x + 1) ^^^ x) = 1 := by
  rw [q_gray_alternating_duality_even q hq x, q_gray_alternating_duality_odd q hq x]
  apply Z2.ext; intro w
  change (-(BitVec.ofInt w (q - 1)) * (phiZ2 q hq x).proj w) +
         (BitVec.ofInt w (q - 1) * (phiZ2 q hq x).proj w + BitVec.ofNat w 1) = BitVec.ofNat w 1
  rw [BitVec.neg_mul, ← BitVec.add_assoc, bitvec_neg_add_self, BitVec.zero_add]

/-- COROLLARY (Exact Closed-Form Bitwise Inverse of Alternating Binary `Θ_2` on all of `Z2`):
    `∀ x : Z2, Θ_2((-2x) ^^^ (-x)) = x`. -/
theorem theta2_bitwise_inverse_Z2 :
    ∀ x : Z2, thetaZ2 2 (by decide) ((2 * (-x)) ^^^ (-x)) = x := by
  have hphi2 : ∀ y : Z2, phiZ2 2 (by decide) y = y := by
    apply z2_density_identity (isContinuous_of_1Lipschitz (phiZ2_is1Lipschitz 2 (by decide)))
      (isContinuous_of_1Lipschitz hasModulus_id)
    intro n
    rw [phiZ2_ofNat, ← Z2.ofInt_ofNat]
    congr 1
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn0 : n = 0
      · subst hn0; simp [phiNat_zero]
      · let m := n / 2
        have hlt : m < n := by omega
        by_cases hpar : n % 2 = 0
        · have heq : n = 2 * m := by omega
          rw [heq, phiNat_two_mul, ih m hlt]; omega
        · have heq : n = 2 * m + 1 := by omega
          rw [heq, phiNat_two_mul_add_one, ih m hlt]; omega
  intro x
  rw [q_gray_alternating_duality_even 2 (by decide) (-x), hphi2 (-x)]
  apply Z2.ext; intro w
  change -(BitVec.ofInt w (2 - 1)) * (-(x.proj w)) = x.proj w
  have h1 : BitVec.ofInt w (2 - 1) = 1#w := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h1, BitVec.neg_mul, BitVec.one_mul, BitVec.neg_neg]

/-- Non-vacuity witness at non-natural 2-adic integer `x = -1 ∈ Z2`:
    `(1 - q) * Φ_q(-1) = 1` in `Z2` (i.e. `Φ_q(-1) = 1 / (1 - q)`). -/
theorem phiZ2_neg_one (q : Int) (hq : (2 : Int) ∣ q) :
    (1 - Z2.ofInt q) * phiZ2 q hq (-1) = 1 := by
  have hgeom : ∀ w : Nat, (1 - q) * phiNat q (2 ^ w - 1) = 1 - q ^ w := by
    intro w
    induction w with
    | zero => simp [phiNat_zero]
    | succ w ih =>
      have hpow : 2 ^ (w + 1) - 1 = 2 * (2 ^ w - 1) + 1 := by
        have := Nat.two_pow_pos w; rw [Nat.pow_succ]; omega
      rw [hpow, phiNat_two_mul_add_one, Int.mul_add, Int.mul_one, Int.mul_left_comm, ih,
          Int.pow_succ, Int.mul_sub, Int.mul_one, Int.mul_comm q (q ^ w)]
      omega
  apply Z2.ext; intro w
  have hneg1 : ((-1 : Z2).proj w).toNat = 2 ^ w - 1 := by
    change (-(BitVec.ofNat w 1)).toNat = 2 ^ w - 1
    simp [BitVec.toNat_neg]
    have := Nat.two_pow_pos w
    by_cases hw : w = 0
    · subst hw; simp
    · have hgt : 1 < 2 ^ w := by
        cases w with
        | zero => omega
        | succ m => have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega
      rw [Nat.mod_eq_of_lt hgt, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
  have hproj : (phiZ2 q hq (-1)).proj w = BitVec.ofInt w (phiNat q (2 ^ w - 1)) := by
    change BitVec.ofInt w (phiNat q ((-1 : Z2).proj w).toNat) = _
    rw [hneg1]
  change (BitVec.ofNat w 1 - BitVec.ofInt w q) * (phiZ2 q hq (-1)).proj w = BitVec.ofNat w 1
  rw [hproj]
  have h3 : BitVec.ofNat w 1 = BitVec.ofInt w 1 :=
    (congrArg (fun z => z.proj w) (Z2.ofInt_ofNat 1)).symm
  have h1 : BitVec.ofInt w 1 - BitVec.ofInt w q = BitVec.ofInt w (1 - q) :=
    (congrArg (fun z => z.proj w) (Z2.ofInt_sub 1 q)).symm
  have h2 : BitVec.ofInt w (1 - q) * BitVec.ofInt w (phiNat q (2 ^ w - 1)) =
            BitVec.ofInt w ((1 - q) * phiNat q (2 ^ w - 1)) :=
    (congrArg (fun z => z.proj w) (Z2.ofInt_mul (1 - q) (phiNat q (2 ^ w - 1)))).symm
  rw [h3, h1, h2, hgeom w, bitvec_ofInt_eq_iff_dvd]
  have hsub : (1 - q ^ w) - 1 = -(q ^ w) := by omega
  rw [hsub]
  have hcast : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
  rw [hcast]
  exact Int.dvd_neg.mpr (dvd_pow_of_dvd hq w)

/-- Sharpness counterexample for Theorem I: at odd `q = 3`, `Φ_3` has NO continuous extension to `Z2`! -/
theorem phi3_not_continuous :
    ¬ ∃ F : Z2 → Z2, IsContinuous F ∧ ∀ n : Nat, F (Z2.ofNat n) = Z2.ofInt (phiNat 3 n) := by
  rintro ⟨F, ⟨μ, hDiv, hMod⟩, hExt⟩
  rcases hDiv 1 with ⟨w, hw⟩
  have hdvd := vdp_necessity hMod hExt (2 ^ w) (Nat.two_pow_pos w)
  have hlog : Nat.log2 (2 ^ w) = w := log2_eq_of_bounds (Nat.le_refl _) (by rw [Nat.pow_succ]; have := Nat.two_pow_pos w; omega)
  rw [hlog, vdpCoeff_phiNat 3 (2 ^ w) (Nat.two_pow_pos w), hlog] at hdvd
  have h2dvd : (2 : Int) ∣ (3 : Int) ^ w :=
    Int.dvd_trans (pow2_dvd_pow2_int hw) hdvd
  have hodd : ∀ k : Nat, (3 : Int) ^ k % 2 = 1 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => rw [Int.pow_succ, Int.mul_emod, ih]; decide
  rcases h2dvd with ⟨t, ht⟩
  have := hodd w
  omega

-- ----------------------------------------------------------------------------
-- THEOREM IIa: Triadic Non-Commuting Carry-Shear (Exact 2/3-Holder Exponent!)
-- ----------------------------------------------------------------------------

/-- Non-commutativity witness: `A0_tri * A1_tri ≠ A1_tri * A0_tri`. -/
theorem triadic_noncommuting : matMul A0_tri A1_tri ≠ matMul A1_tri A0_tri := by
  intro h
  have h01 := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
  revert h01; decide

/-- THEOREM IIa (Upper Bound — Exact 2/3-Holder Continuity on Z2):
    `∀ w x y, x.proj w = y.proj w → (triadicZ2 x).proj (2 * (w / 3)) = (triadicZ2 y).proj (2 * (w / 3))`. -/
theorem triadic_holder_2_3 : HasModulus (fun w => 2 * (w / 3)) triadicZ2 :=
  latticeCertLift_hasModulus (by omega) (by omega) cert_tri g_tri_isReg cert_tri_valid u_tri

theorem sharp_tri_valid : sharp_tri.Valid := by decide

/-- THEOREM IIa (Sharpness Lower Bound via Compiler B):
    NO extension of `u_tri · g_tri` to `Z2` can achieve modulus `μ(3k) > 2k` for ANY `k`! -/
theorem triadic_holder_2_3_sharp {F : Z2 → Z2} {μ : Nat → Nat}
    (hMod : HasModulus μ F) (hExt : ∀ n, F (Z2.ofNat n) = Z2.ofInt (dotVec u_tri (g_tri n))) (k : Nat) :
    μ (3 * k) ≤ 2 * k := by
  have h := sharp_holder_no_better_modulus cert_tri g_tri_isReg cert_tri_valid u_tri sharp_tri sharp_tri_valid hMod hExt k
  simpa [sharp_tri, Nat.mul_comm, Nat.mul_one] using h

theorem g_tri_bad_isReg : IsAffineTwoRegular A0_tri A1_tri_bad c0_tri c1_tri g_tri_bad :=
  evalAffineTwoReg_isAffineTwoRegular A0_tri A1_tri_bad c0_tri c1_tri v0_tri
    (by funext i; exact (by decide : ∀ i : Fin 3, vecAdd (matVec A0_tri v0_tri) c0_tri i = v0_tri i) i)

theorem g_tri_bad_vdp1 : vdpCoeffVec g_tri_bad 1 = c1_tri :=
  vdpCoeffVec_one_of_zero g_tri_bad_isReg (evalAffineTwoReg_zero _ _ _ _ _)

theorem triadic_perturbed_not_continuous :
    ¬ ∃ F : Z2 → Z2, IsContinuous F ∧ ∀ n : Nat, F (Z2.ofNat n) = Z2.ofInt (dotVec u_tri (g_tri_bad n)) := by
  have hodd : ∀ k : Nat,
      vdpCoeffVec g_tri_bad (2 ^ (k + 1) - 1) ⟨0, by omega⟩ % 2 = 0 ∧
      vdpCoeffVec g_tri_bad (2 ^ (k + 1) - 1) ⟨1, by omega⟩ % 2 = 0 ∧
      vdpCoeffVec g_tri_bad (2 ^ (k + 1) - 1) ⟨2, by omega⟩ % 2 = 1 := by
    intro k
    induction k with
    | zero =>
      have h1 : 2 ^ (0 + 1) - 1 = 1 := rfl
      rw [h1, g_tri_bad_vdp1]; decide
    | succ k ih =>
      have hpos : 1 ≤ 2 ^ (k + 1) - 1 := by have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
      have heq : 2 ^ (k + 2) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by
        have := Nat.two_pow_pos (k + 1); rw [Nat.pow_succ]; omega
      rw [heq, vdp_affine_two_regular_odd g_tri_bad_isReg hpos]
      rcases ih with ⟨h0, h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [matVec, finSum3, A1_tri_bad, A1_tri]; omega
      · simp [matVec, finSum3, A1_tri_bad, A1_tri]
      · simp [matVec, finSum3, A1_tri_bad, A1_tri]
        have h0' : vdpCoeffVec g_tri_bad (2 ^ (k + 1) - 1) 0 % 2 = 0 := h0
        have h2' : vdpCoeffVec g_tri_bad (2 ^ (k + 1) - 1) 2 % 2 = 1 := h2
        omega
  rintro ⟨F, ⟨μ, hDiv, hMod⟩, hExt⟩
  rcases hDiv 1 with ⟨w, hw⟩
  have h2w : 0 < 2 ^ w := Nat.two_pow_pos w
  have h2ws : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w
  let n := 2 ^ (w + 1) - 1
  have hn : 1 ≤ n := by omega
  have hlog : Nat.log2 n = w := by
    apply log2_eq_of_bounds <;> omega
  have hdvd := vdp_necessity hMod hExt n hn
  rw [hlog, vdpCoeff_dotVec] at hdvd
  have h2dvd : (2 : Int) ∣ dotVec u_tri (vdpCoeffVec g_tri_bad n) :=
    Int.dvd_trans (pow2_dvd_pow2_int hw) hdvd
  have hdot : dotVec u_tri (vdpCoeffVec g_tri_bad n) = vdpCoeffVec g_tri_bad n ⟨2, by omega⟩ := by
    simp [dotVec, finSum3, u_tri]
  rw [hdot] at h2dvd
  have h2odd : vdpCoeffVec g_tri_bad n ⟨2, by omega⟩ % 2 = 1 := (hodd w).2.2
  rcases h2dvd with ⟨t, ht⟩
  rw [ht] at h2odd
  omega

-- ----------------------------------------------------------------------------
-- THEOREM IIb: Shear-Carry System (Non-Trivial Lattice Basis P = diag(1, 2))
-- ----------------------------------------------------------------------------

/-- THEOREM IIb (Upper Bound via Non-Trivial Lattice Basis P = diag(1, 2)):
    Exact 1-Lipschitz continuity certified in a single step `L = 1, s = 1`! -/
theorem shear_carry_1lipschitz : Is1Lipschitz shearCarryZ2 := by
  have h := latticeCertLift_hasModulus (Nat.le_refl 1) (Nat.le_refl 1) cert_sc g_sc_isReg cert_sc_valid u_sc
  intro w x y hxy
  have hw : (shearCarryZ2 x).proj (1 * (w / 1)) = (shearCarryZ2 y).proj (1 * (w / 1)) := h w x y hxy
  have heq : 1 * (w / 1) = w := by omega
  rw [heq] at hw
  exact hw

theorem sharp_sc_valid : sharp_sc.Valid := by decide

/-- THEOREM IIb (Exact Period-2 Sharpness Lower Bound via Compiler B):
    NO extension can achieve modulus `μ(2k) > 2k`! -/
theorem shear_carry_1lipschitz_sharp {F : Z2 → Z2} {μ : Nat → Nat}
    (hMod : HasModulus μ F) (hExt : ∀ n, F (Z2.ofNat n) = Z2.ofInt (dotVec u_sc (g_sc n))) (k : Nat) :
    μ (2 * k) ≤ 2 * k := by
  have h := sharp_holder_no_better_modulus cert_sc g_sc_isReg cert_sc_valid u_sc sharp_sc sharp_sc_valid hMod hExt k
  simpa [sharp_sc, Nat.mul_comm, Nat.one_mul] using h

/-- Necessity of non-trivial lattice basis `P`:
    For EVERY odd block length `L = 2m + 1`, `2^L` DOES NOT DIVIDE `(A0_sc^L)[0][1] = L * 2^(L-1)`,
    so the trivial lattice `P = I_2` fails at infinitely many depths! -/
theorem shear_carry_trivial_lattice_fails (m : Nat) :
    ¬ (((2 ^ (2 * m + 1) : Nat) : Int) ∣ matPow A0_sc (2 * m + 1) ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  have hpow : ∀ k : Nat,
      matPow A0_sc k ⟨0, by omega⟩ ⟨0, by omega⟩ = ((2 ^ k : Nat) : Int) ∧
      matPow A0_sc k ⟨0, by omega⟩ ⟨1, by omega⟩ = (k : Int) * ((2 ^ (k - 1) : Nat) : Int) ∧
      matPow A0_sc k ⟨1, by omega⟩ ⟨0, by omega⟩ = 0 ∧
      matPow A0_sc k ⟨1, by omega⟩ ⟨1, by omega⟩ = ((2 ^ k : Nat) : Int) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rcases ih with ⟨h00, h01, h10, h11⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [matPow, matMul, finSum2, A0_sc]
        rw [h00, h10, Nat.pow_succ, Int.natCast_mul]; omega
      · simp only [matPow, matMul, finSum2, A0_sc]
        rw [h01, h11]
        cases k with
        | zero => simp
        | succ k' =>
          have hsub : k' + 1 - 1 = k' := by omega
          have hsub2 : k' + 1 + 1 - 1 = k' + 1 := by omega
          rw [hsub, hsub2, Nat.pow_succ, Int.natCast_mul]
          have heq : (2 : Int) * (((k' + 1 : Nat) : Int) * ((2 ^ k' : Nat) : Int)) +
                     1 * (((2 ^ k' : Nat) : Int) * (2 : Int)) =
                     (((k' + 1 : Nat) : Int) + 1) * (((2 ^ k' : Nat) : Int) * 2) := by
            rw [Int.add_mul, Int.one_mul, Int.mul_comm (2 : Int) (((k' + 1 : Nat) : Int) * ((2 ^ k' : Nat) : Int)),
                Int.mul_assoc]
          simpa [Int.natCast_add] using heq
      · simp only [matPow, matMul, finSum2, A0_sc]
        rw [h10]; simp
      · simp only [matPow, matMul, finSum2, A0_sc]
        rw [h11, Nat.pow_succ, Int.natCast_mul]; omega
  rw [(hpow (2 * m + 1)).2.1]
  intro ⟨q, hq⟩
  have hsub : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hsub, Nat.pow_succ, Int.natCast_mul] at hq
  have hne : ((2 ^ (2 * m) : Nat) : Int) ≠ 0 := two_pow_ne_zero_int (2 * m)
  have hrearr : ((2 ^ (2 * m) : Nat) : Int) * ((2 * m + 1 : Nat) : Int) =
                ((2 ^ (2 * m) : Nat) : Int) * ((2 : Int) * q) := by
    rw [Int.mul_comm ((2 ^ (2 * m) : Nat) : Int), hq, Int.mul_assoc]; rfl
  have hcancel := Int.eq_of_mul_eq_mul_left hne hrearr
  omega

-- ----------------------------------------------------------------------------
-- THEOREM III: Exact 2-Adic Morton-Carry First-Difference Law on all of Z2
-- ----------------------------------------------------------------------------

theorem lsbNat_odd {k : Nat} (h : k % 2 = 1) : lsbNat k = 1 := by
  rw [lsbNat]
  have hne : k ≠ 0 := by omega
  simp [hne, h]

theorem lsbNat_two_mul {k : Nat} (hk : 1 ≤ k) : lsbNat (2 * k) = 2 * lsbNat k := by
  rw [lsbNat]
  have hne : 2 * k ≠ 0 := by omega
  have hdiv : (2 * k) / 2 = k := by omega
  simp [hne, hdiv]

/-- `Z2.lsbMask (ofNat k) = ofNat (lsbNat k)` for all `k : Nat`! -/
theorem z2_lsbMask_ofNat (k : Nat) : Z2.lsbMask (Z2.ofNat k) = Z2.ofNat (lsbNat k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      apply Z2.ext; intro w
      change BitVec.ofNat w 0 &&& -(BitVec.ofNat w 0) = BitVec.ofNat w (lsbNat 0)
      have h0 : lsbNat 0 = 0 := by rw [lsbNat]; simp
      rw [h0]; simp
    · by_cases hodd : k % 2 = 1
      · rw [lsbNat_odd hodd]
        apply Z2.ext; intro w
        change BitVec.ofNat w k &&& -(BitVec.ofNat w k) = BitVec.ofNat w 1
        have hneg : -(BitVec.ofNat w k) = ~~~(BitVec.ofNat w (k - 1)) := by
          have hk1 : (k - 1) + 1 = k := by omega
          have hadd : BitVec.ofNat w k = BitVec.ofNat w (k - 1) + 1#w := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hk1]
          have hnot : ~~~(BitVec.ofNat w (k - 1)) = -(BitVec.ofNat w (k - 1) + 1#w) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_not, BitVec.toNat_neg, BitVec.toNat_add, BitVec.toNat_ofNat]
            have hlt : (k - 1) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
            by_cases hw0 : w = 0
            · subst hw0; simp [Nat.mod_one]
            · have h2pos : 1 < 2 ^ w := by
                cases w with
                | zero => omega
                | succ m => have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega
              rw [Nat.mod_eq_of_lt h2pos]
              by_cases htop : (k - 1) % 2 ^ w + 1 = 2 ^ w
              · rw [htop, Nat.mod_self, Nat.sub_zero, Nat.mod_self]; omega
              · have hlt2 : (k - 1) % 2 ^ w + 1 < 2 ^ w := by omega
                rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (by omega : 2 ^ w - ((k - 1) % 2 ^ w + 1) < 2 ^ w)]
                omega
          rw [hadd, hnot]
        rw [hneg]
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
        cases i with
        | zero =>
          have hb0 : k.testBit 0 = true := by simp [Nat.testBit_zero, hodd]
          have hb0' : (k - 1).testBit 0 = false := by simp [Nat.testBit_zero]; omega
          rw [hb0, hb0']; rfl
        | succ i =>
          let m := k / 2
          have hk_eq : k = 2 * m + 1 := by omega
          have hk1_eq : k - 1 = 2 * m := by omega
          rw [hk1_eq, hk_eq, my_testBit_two_mul_succ, my_testBit_two_mul_add_one_succ]
          have h1 : (1 : Nat).testBit (i + 1) = false := by
            rw [Nat.testBit_succ]; simp
          rw [h1]
          cases m.testBit i <;> rfl
      · let m := k / 2
        have hpos : 1 ≤ m := by omega
        have hlt : m < k := by omega
        have hk_eq : k = 2 * m := by omega
        rw [hk_eq, lsbNat_two_mul hpos]
        have hih := ih m hlt
        apply Z2.ext; intro w
        cases w with
        | zero =>
          apply BitVec.eq_of_toNat_eq
          have h1 := ((Z2.ofNat (2 * m)).lsbMask.proj 0).isLt
          have h2 := ((Z2.ofNat (2 * lsbNat m)).proj 0).isLt
          omega
        | succ w =>
          have hprev := congrArg (fun z => z.proj w) hih
          change BitVec.ofNat (w + 1) (2 * m) &&& -(BitVec.ofNat (w + 1) (2 * m)) =
                 BitVec.ofNat (w + 1) (2 * lsbNat m)
          change BitVec.ofNat w m &&& -(BitVec.ofNat w m) = BitVec.ofNat w (lsbNat m) at hprev
          have hneg2 : -(BitVec.ofNat (w + 1) (2 * m)) =
                       (BitVec.ofNat (w + 1) (2 * (-(BitVec.ofNat w m)).toNat)) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
            have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
            rw [hpow, Nat.mul_mod_mul_left]
            by_cases hm : m % 2 ^ w = 0
            · simp [hm]
            · have hlt_w : m % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
              have h1 : 2 ^ w - m % 2 ^ w < 2 ^ w := by omega
              have h2 : 2 * 2 ^ w - 2 * (m % 2 ^ w) = 2 * (2 ^ w - m % 2 ^ w) := by omega
              rw [h2, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : 2 * (2 ^ w - m % 2 ^ w) < 2 * 2 ^ w)]
          rw [hneg2]
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
          cases i with
          | zero => simp
          | succ i =>
            have hi' : i < w := by omega
            have hbit := congrArg (fun v => v.getLsbD i) hprev
            simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hi', decide_true, Bool.true_and] at hbit
            rw [my_testBit_two_mul_succ, my_testBit_two_mul_succ, my_testBit_two_mul_succ]
            have hget : (-(BitVec.ofNat w m)).toNat.testBit i = (-(BitVec.ofNat w m)).getLsbD i := rfl
            rw [hget, hbit]

/-- Finite-Nat Morton-Carry First-Difference Law for ALL `r ≥ 1` and ALL `n : Nat`. -/
theorem morton_carry_first_diff_nat (r : Nat) (_hr : 1 ≤ r) :
    ∀ n : Nat,
      (((2 ^ r : Nat) : Int) - 1) * (phiNat ((2 ^ r : Nat) : Int) (n + 1) - phiNat ((2 ^ r : Nat) : Int) n) =
      (((2 ^ r : Nat) : Int) - 2) * ((lsbNat (n + 1) : Int) ^ r) + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let m := n / 2
    by_cases hpar : n % 2 = 0
    · have hn : n = 2 * m := by omega
      have hn1 : n + 1 = 2 * m + 1 := by omega
      rw [hn1, lsbNat_odd (by omega : (2 * m + 1) % 2 = 1), phiNat_two_mul_add_one,
          hn, phiNat_two_mul]
      have h1pow : ((1 : Nat) : Int) ^ r = 1 := Int.one_pow
      rw [h1pow]; omega
    · have hn : n = 2 * m + 1 := by omega
      have hn1 : n + 1 = 2 * (m + 1) := by omega
      have hlt : m < n := by omega
      have hih := ih m hlt
      rw [hn1, lsbNat_two_mul (by omega : 1 ≤ m + 1), phiNat_two_mul, hn, phiNat_two_mul_add_one]
      have hpow_mul : ((2 * lsbNat (m + 1) : Nat) : Int) ^ r =
                      ((2 ^ r : Nat) : Int) * ((lsbNat (m + 1) : Int) ^ r) := by
        rw [Int.natCast_mul, Int.mul_pow]; simp
      rw [hpow_mul]
      let q : Int := ((2 ^ r : Nat) : Int)
      have hlhs : (q - 1) * (q * phiNat q (m + 1) - (q * phiNat q m + 1)) =
                  q * ((q - 1) * (phiNat q (m + 1) - phiNat q m)) - (q - 1) := by
        rw [Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_add, Int.mul_one,
            Int.mul_left_comm (q - 1) q (phiNat q (m + 1)),
            Int.mul_left_comm (q - 1) q (phiNat q m)]
        omega
      change (q - 1) * (q * phiNat q (m + 1) - (q * phiNat q m + 1)) =
             (q - 2) * (q * ((lsbNat (m + 1) : Int) ^ r)) + 1
      rw [hlhs, hih]
      rw [Int.mul_add, Int.mul_one, Int.mul_left_comm]
      dsimp only [q]
      omega

/-- THEOREM III (Exact 2-Adic Morton-Carry First-Difference Law on ALL of Z2):
    For EVERY `r ≥ 1` and EVERY `x : Z2` (including `x = -1`, where carries propagate to `∞`!):
    `(2^r - 1) * (Φ_{2^r}(x + 1) - Φ_{2^r}(x)) = (2^r - 2) * ((x + 1) &&& -(x + 1))^r + 1`. -/
theorem morton_carry_first_diff_Z2 (r : Nat) (hr : 1 ≤ r) :
    ∀ x : Z2,
      let hq : (2 : Int) ∣ ((2 ^ r : Nat) : Int) := pow2_dvd_pow2_int hr
      Z2.ofInt (((2 ^ r : Nat) : Int) - 1) * (phiZ2 ((2 ^ r : Nat) : Int) hq (x + 1) - phiZ2 ((2 ^ r : Nat) : Int) hq x) =
      Z2.ofInt (((2 ^ r : Nat) : Int) - 2) * (Z2.lsbMask (x + 1)) ^ r + 1 := by
  let hq : (2 : Int) ∣ ((2 ^ r : Nat) : Int) := pow2_dvd_pow2_int hr
  have hLHS : IsContinuous (fun x =>
      Z2.ofInt (((2 ^ r : Nat) : Int) - 1) * (phiZ2 ((2 ^ r : Nat) : Int) hq (x + 1) - phiZ2 ((2 ^ r : Nat) : Int) hq x)) :=
    isContinuous_of_1Lipschitz (hasModulus_mul (hasModulus_const _)
      (hasModulus_sub (hasModulus_comp (phiZ2_is1Lipschitz _ hq) (hasModulus_add hasModulus_id (hasModulus_const 1)))
        (phiZ2_is1Lipschitz _ hq)))
  have hRHS : IsContinuous (fun x =>
      Z2.ofInt (((2 ^ r : Nat) : Int) - 2) * (Z2.lsbMask (x + 1)) ^ r + 1) :=
    isContinuous_of_1Lipschitz (hasModulus_add
      (hasModulus_mul (hasModulus_const _)
        (hasModulus_pow (hasModulus_and (hasModulus_add hasModulus_id (hasModulus_const 1))
          (hasModulus_neg (hasModulus_add hasModulus_id (hasModulus_const 1)))) r))
      (hasModulus_const 1))
  apply z2_density_identity hLHS hRHS
  intro n
  have hn1 : Z2.ofNat n + 1 = Z2.ofNat (n + 1) := (Z2.ofNat_add n 1).symm
  rw [hn1, phiZ2_ofNat, phiZ2_ofNat, z2_lsbMask_ofNat, ← Z2.ofNat_pow,
      ← Z2.ofInt_ofNat (lsbNat (n + 1) ^ r),
      ← Z2.ofInt_sub, ← Z2.ofInt_mul, ← Z2.ofInt_mul,
      show (1 : Z2) = Z2.ofInt 1 from (Z2.ofInt_ofNat 1).symm, ← Z2.ofInt_add]
  congr 1
  rw [Int.natCast_pow]
  exact morton_carry_first_diff_nat r hr n

-- ----------------------------------------------------------------------------
-- THEOREM IV: Mahler Engine Showcase — 2-Adic Exponential `(1 + 2c)^x` & Sharpness
-- ----------------------------------------------------------------------------

theorem exp2c_is1Lipschitz (c : Int) : Is1Lipschitz (exp2cZ2 c) :=
  mahler1LipschitzLift_is1Lipschitz _ _

theorem exp2c_ofNat (c : Int) (n : Nat) :
    exp2cZ2 c (Z2.ofNat n) = Z2.ofInt ((1 + 2 * c) ^ n) :=
  mahler1LipschitzLift_ofNat _ _ n

/-- THEOREM IVa (2-Adic Exponential Group Homomorphism on ALL of Z2):
    `∀ c : Int, ∀ x y : Z2, (1 + 2c)^(x + y) = (1 + 2c)^x * (1 + 2c)^y`. -/
theorem exp2c_hom_Z2 (c : Int) (x y : Z2) :
    exp2cZ2 c (x + y) = exp2cZ2 c x * exp2cZ2 c y := by
  have hNatY : ∀ (m : Nat) (x : Z2), exp2cZ2 c (x + Z2.ofNat m) = exp2cZ2 c x * exp2cZ2 c (Z2.ofNat m) := by
    intro m
    apply z2_density_identity
      (isContinuous_of_1Lipschitz (hasModulus_comp (exp2c_is1Lipschitz c)
        (hasModulus_add hasModulus_id (hasModulus_const _))))
      (isContinuous_of_1Lipschitz (hasModulus_mul (exp2c_is1Lipschitz c) (hasModulus_const _)))
    intro n
    rw [← Z2.ofNat_add, exp2c_ofNat, exp2c_ofNat, exp2c_ofNat, ← Z2.ofInt_mul, Int.pow_add]
  revert y
  apply z2_density_identity
    (isContinuous_of_1Lipschitz (hasModulus_comp (exp2c_is1Lipschitz c)
      (hasModulus_add (hasModulus_const x) hasModulus_id)))
    (isContinuous_of_1Lipschitz (hasModulus_mul (hasModulus_const _) (exp2c_is1Lipschitz c)))
  intro m
  exact hNatY m x

/-- Non-vacuity witness at `x = -1 ∈ Z2`: `(1 + 2c)^(-1) * (1 + 2c) = 1` in `Z2`! -/
theorem exp2c_neg_one_inv (c : Int) :
    exp2cZ2 c (-1) * Z2.ofInt (1 + 2 * c) = 1 := by
  have h1 : Z2.ofInt (1 + 2 * c) = exp2cZ2 c 1 := by
    change Z2.ofInt (1 + 2 * c) = exp2cZ2 c (Z2.ofNat 1)
    rw [exp2c_ofNat, Int.pow_one]
  rw [h1, ← exp2c_hom_Z2]
  have hzero : (-1 : Z2) + 1 = Z2.ofNat 0 := by
    apply Z2.ext; intro w
    change -(BitVec.ofNat w 1) + BitVec.ofNat w 1 = 0#w
    exact bitvec_neg_add_self _
  rw [hzero, exp2c_ofNat, Int.pow_zero]
  exact Z2.ofInt_ofNat 1

/-- Sharpness counterexample for the Mahler 1-Lipschitz criterion (`mahler_to_vdp_1lipschitz`):
    `f(x) = binom x 2` has `mahlerCoeff f 2 = 1` (fails `2^(log2 2) = 2 ∣ a_2`),
    and provably admits NO 1-Lipschitz lift to `Z2`! -/
theorem mahler_binom2_not_1lipschitz :
    mahlerCoeff (fun x => (binom x 2 : Int)) 2 = 1 ∧
    ¬ ∃ F : Z2 → Z2, Is1Lipschitz F ∧ ∀ n : Nat, F (Z2.ofNat n) = Z2.ofInt (binom n 2 : Int) := by
  constructor
  · decide
  · rintro ⟨F, hLip, hExt⟩
    have hdvd := vdp_necessity hLip hExt 2 (by omega)
    dsimp only [id] at hdvd
    have hv : vdpCoeff (fun x => (binom x 2 : Int)) 2 = 1 := by decide
    have hl : Nat.log2 2 = 1 := by decide
    rw [hv, hl] at hdvd
    rcases hdvd with ⟨q, hq⟩
    omega

-- ----------------------------------------------------------------------------
-- COMPILER C NON-VACUITY & CONCRETE KERNEL-INVARIANT IDENTITY WITNESS
-- (Proves `Θ_4((2x)^^^x) + 3 Φ_4(x) = 0` & `Θ_4((2x)^^^x) + Θ_4((2x+1)^^^x) = 1`
--  purely via a `decide`-checked 2x4 `KernelIdCert`!)
-- ----------------------------------------------------------------------------

/-- Machine-checked finite Compiler C certificate (`decide` discharges both matrix invariants + base vector!). -/
theorem cert_kernel_gray4_valid : cert_kernel_gray4.Valid v0_gray4 := by decide

/-- Explicit kernel-checked non-vacuity witnesses for all three finite certificate engines. -/
theorem nonvacuity_all_compilers :
    (∃ c : LatticeContractCert 3 3 3 2, c.Valid (vdpCoeffVec g_tri 1)) ∧
    (∃ c : LatticeContractCert 2 2 1 1, c.Valid (vdpCoeffVec g_sc 1)) ∧
    (∃ sc : SharpHolderCert cert_tri u_tri, sc.Valid) ∧
    (∃ sc : SharpHolderCert cert_sc u_sc, sc.Valid) ∧
    (∃ kc : KernelIdCert 4 2, kc.Valid v0_gray4) :=
  ⟨⟨cert_tri, cert_tri_valid⟩, ⟨cert_sc, cert_sc_valid⟩,
   ⟨sharp_tri, sharp_tri_valid⟩, ⟨sharp_sc, sharp_sc_valid⟩,
   ⟨cert_kernel_gray4, cert_kernel_gray4_valid⟩⟩

end Z2CertEngine
