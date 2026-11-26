/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8

/-!
# Verified Solutions (`kahan-neumaier-fp8-bounds`)
-/

namespace KahanNeumaierFp8Challenge

open KahanNeumaierFp8

theorem microbatch_rne_freeze_threshold_exact :
    (rhoFreezeMin 2 = 8 ∧ rhoFreezeMin 3 = 16 ∧
     rhoFreezeMin 7 = 256 ∧ rhoFreezeMin 10 = 2048) ∧
    (rhoNonfreezeMax 2 = 14 ∧ rhoNonfreezeMax 3 = 30 ∧
     rhoNonfreezeMax 7 = 510 ∧ rhoNonfreezeMax 10 = 4094) ∧
    (∀ (P : Nat), 1 ≤ P →
      (flRNENat P (rhoFreezeMin P + 1) = rhoFreezeMin P) ∧
      (∀ n : Nat, n < rhoFreezeMin P → flRNENat P (n + 1) = n + 1 ∧ flRNENat P (n + 1) ≠ n) ∧
      (flRNENat P (rhoNonfreezeMax P) = rhoNonfreezeMax P ∧
       flRNENat P (rhoNonfreezeMax P + 1) = 2 ^ (P + 2) ∧
       flRNENat P (rhoNonfreezeMax P + 1) ≠ rhoNonfreezeMax P) ∧
      (∀ S : Nat, 2 ^ (P + 2) ≤ S → flRNENat P S = S → flRNENat P (S + 1) = S)) ∧
    (∀ (P K : Nat), 1 ≤ P → 1 ≤ K → K ≤ P + 1 →
      seqRNE P ((rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1) = (rhoFreezeMin P : Int) ∧
      treeRNE P ((rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1) =
        (rhoFreezeMin P : Int) + ((2 ^ K - 2 : Nat) : Int) ∧
      treeRNE P (List.replicate (2 ^ K) 1) = ((2 ^ K : Nat) : Int) ∧
      rneAdd P (rhoFreezeMin P : Int) (treeRNE P (List.replicate (2 ^ K) 1)) =
        (rhoFreezeMin P : Int) + ((2 ^ K : Nat) : Int)) :=
  KahanNeumaierFp8.microbatch_rne_freeze_threshold_exact

theorem kahan_late_dipole_spike_total_erasure_vs_neumaier :
    (∀ (P mPre mPost e : Nat),
      1 ≤ P → 1 ≤ mPre → mPre + mPost ≤ 2 ^ (P + 1) → 2 ^ (P + 2) * mPre ≤ 2 ^ e →
      kahanSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = (mPost : Int) ∧
      neumaierSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = ((mPre + mPost : Nat) : Int)) ∧
    (∀ (P m e : Nat),
      1 ≤ P → 1 ≤ m → m ≤ 2 ^ (P + 1) → 2 ^ (P + 2) * m ≤ 2 ^ e →
      kahanSum P (dipoleStream m 0 ((2 ^ e : Nat) : Int)) = 0 ∧
      neumaierSum P (dipoleStream m 0 ((2 ^ e : Nat) : Int)) = (m : Int)) ∧
    (kahanSum 7 (dipoleStream 254 0 ((2 ^ 17 : Nat) : Int)) = 0 ∧
     neumaierSum 7 (dipoleStream 254 0 ((2 ^ 17 : Nat) : Int)) = 254) ∧
    (kahanSum 10 (dipoleStream 254 0 ((2 ^ 20 : Nat) : Int)) = 0 ∧
     neumaierSum 10 (dipoleStream 254 0 ((2 ^ 20 : Nat) : Int)) = 254) :=
  KahanNeumaierFp8.kahan_late_dipole_spike_total_erasure_vs_neumaier

theorem neumaier_self_swamping_ceiling_beats_by_kahan :
    (neumaierCeiling 2 = 16 ∧ neumaierCeiling 3 = 32 ∧
     neumaierCeiling 7 = 512 ∧ neumaierCeiling 10 = 4096) ∧
    (∀ (P M : Nat), 1 ≤ P → neumaierCeiling P ≤ M →
      neumaierSum P (List.replicate M 1) = (neumaierCeiling P : Int)) ∧
    (∀ (P : Nat), 1 ≤ P →
      neumaierSum P (List.replicate (neumaierCeiling P + 4) 1) = (neumaierCeiling P : Int) ∧
      kahanSum P (List.replicate (neumaierCeiling P + 4) 1) = ((neumaierCeiling P + 4 : Nat) : Int) ∧
      neumaierSum P (List.replicate (neumaierCeiling P + 4) 1) <
        kahanSum P (List.replicate (neumaierCeiling P + 4) 1)) ∧
    (neumaierSum 2 (List.replicate 64 1) = 16 ∧
     kahanSum 2 (List.replicate 64 1) = 64) :=
  KahanNeumaierFp8.neumaier_self_swamping_ceiling_beats_by_kahan

theorem fp8_e4m3fn_kulisch_int32_9362_exact :
    (∀ (M P deltaE : Nat) (xs : List Int),
      1 ≤ M → xs.length ≤ M →
      (∀ x ∈ xs, x.natAbs ≤ (2 ^ (P + 1) - 1) * 2 ^ deltaE) →
      (seqIntSum xs).natAbs < 2 ^ (kulischMinBits M P deltaE - 1)) ∧
    (fp8E4M3MinSubnormal.toUnits = 1 ∧ fp8E4M3MinSubnormal.toRat = 1 / 512 ∧
     fp8E4M3MaxFinite.toUnits = 229376 ∧ fp8E4M3MaxFinite.toRat = 448 ∧
     (2 ^ 31 - 1) / e4m3MaxUnits = e4m3MaxInt32Count) ∧
    (∀ (xs : List Fp8E4M3FN), xs.length ≤ e4m3MaxInt32Count →
      let s := seqIntSum (xs.map Fp8E4M3FN.toUnits)
      int32Min ≤ s ∧ s ≤ int32Max ∧
      ((xs.map (fun x => Int32.ofInt x.toUnits)).foldl (· + ·) (0 : Int32)).toInt = s ∧
      (xs.map Fp8E4M3FN.toRat).foldl (· + ·) (0 : Rat) = (s : Rat) / (512 : Rat)) ∧
    (∀ (xs ys : List Fp8E4M3FN),
      seqIntSum ((xs ++ ys).map Fp8E4M3FN.toUnits) =
        seqIntSum (xs.map Fp8E4M3FN.toUnits) + seqIntSum (ys.map Fp8E4M3FN.toUnits)) ∧
    (∀ (xs ys : List Fp8E4M3FN), List.Perm xs ys →
      seqIntSum (xs.map Fp8E4M3FN.toUnits) = seqIntSum (ys.map Fp8E4M3FN.toUnits)) ∧
    (seqIntSum ((List.replicate 9362 fp8E4M3MaxFinite).map Fp8E4M3FN.toUnits) ≤ int32Max ∧
     int32Max < seqIntSum ((List.replicate 9363 fp8E4M3MaxFinite).map Fp8E4M3FN.toUnits)) :=
  KahanNeumaierFp8.fp8_e4m3fn_kulisch_int32_9362_exact

theorem microbatch_xor_vdc_sr_zero_bias_and_stratification :
    (∀ (K u0 m : Nat), u0 < 2 ^ K → m < 2 ^ K →
      xorVdc K u0 m < 2 ^ K ∧
      bitrev K (u0 ^^^ xorVdc K u0 m) = m ∧
      xorVdc K u0 (bitrev K (u0 ^^^ m)) = m) ∧
    (∀ (K u0 a : Nat) (v r : Rat),
      u0 < 2 ^ K → a < 2 ^ K →
      (0 : Rat) ≤ v → v < 1 → (0 : Rat) ≤ r → r < 1 →
      let s := finSum (fun m : Fin (2 ^ K) => vdcIndicator (xorVdc K u0 m.val) a v r)
      s = (a : Rat) + (if v < r then (1 : Rat) else 0) ∧
      ratAbs (s - ((a : Rat) + r)) < 1) ∧
    (∀ (r : Rat),
      r * (1 - r) + (1 - r) * (-r) = 0 ∧
      r * ((1 - r) * (1 - r)) + (1 - r) * ((-r) * (-r)) = mseXorVdcSR r) ∧
    (∀ (M : Nat), 1 ≤ M →
      mseIndSRAvg M = (M : Rat) / 6 ∧
      mseXorVdcSRAvg = (1 : Rat) / 6 ∧
      mseIndSRAvg M / mseXorVdcSRAvg = (M : Rat)) ∧
    (∀ (M : Nat) (p : Rat),
      mseIndSR M p = (M : Rat) * mseXorVdcSR p) :=
  KahanNeumaierFp8.microbatch_xor_vdc_sr_zero_bias_and_stratification

theorem shared_exponent_int32_block_accum_associativity :
    (∀ (d : Nat) (gs hs : List (Fin d → Int)),
      blockAccum (gs ++ hs) = blockAdd (blockAccum gs) (blockAccum hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int)), List.Perm gs hs →
      blockAccum gs = blockAccum hs) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int32)),
      blockAccumInt32 (gs ++ hs) = blockAddInt32 (blockAccumInt32 gs) (blockAccumInt32 hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int32)), List.Perm gs hs →
      blockAccumInt32 gs = blockAccumInt32 hs) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int64)),
      blockAccumInt64 (gs ++ hs) = blockAddInt64 (blockAccumInt64 gs) (blockAccumInt64 hs)) ∧
    (∀ (d : Nat) (gs hs : List (Fin d → Int64)), List.Perm gs hs →
      blockAccumInt64 gs = blockAccumInt64 hs) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int32)),
      blockAccumInt32 gs.reverse = blockAccumInt32 gs) ∧
    (∀ (xs : List Int), treeIntSum xs = seqIntSum xs) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int)) (j : Fin d),
      int32Min ≤ blockAccum gs j → blockAccum gs j ≤ int32Max →
      (blockAccumInt32 (gs.map (fun g k => Int32.ofInt (g k))) j).toInt = blockAccum gs j) ∧
    (∀ (d : Nat) (gs : List (Fin d → Int)) (j : Fin d),
      int64Min ≤ blockAccum gs j → blockAccum gs j ≤ int64Max →
      (blockAccumInt64 (gs.map (fun g k => Int64.ofInt (g k))) j).toInt = blockAccum gs j) :=
  KahanNeumaierFp8.shared_exponent_int32_block_accum_associativity

end KahanNeumaierFp8Challenge
