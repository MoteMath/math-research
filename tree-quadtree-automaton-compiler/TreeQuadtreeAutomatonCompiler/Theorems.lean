import TreeQuadtreeAutomatonCompiler.Defs

namespace CertComp6
/-- General Soundness Meta-Theorem for Height-Timed Bottom-Up Binary Tree Automata. -/
theorem timedBTA_sound (A : TimedBTA)
    (good : Fin (A.r0 + A.p1 + 1) → Fin A.numStates → Bool)
    (cert : PhaseBitmaskCert (A.r0 + A.p1 + 1))
    (hcert : checkBTACert A good cert = true) :
    ∀ (k : Nat) (t : BTree (Fin A.numLeaves) k),
      good (phaseOfNat A.r0 A.p1 k) (evalBTA A t) = true := by
  have hinv := timedBTA_inv A good cert hcert
  unfold checkBTACert at hcert
  simp only [Bool.and_eq_true] at hcert
  have hsafe := hcert.2
  rw [allFin_iff] at hsafe
  intro k t
  have hph := hsafe (phaseOfNat A.r0 A.p1 k)
  simp only [List.all_eq_true, mem_bitsOfMask_iff] at hph
  exact hph (evalBTA A t) (hinv k t)

/-! ### Engine B: Height-Timed Bottom-Up Quadtree Automaton (`TimedQTA`) & Morton Compiler -/

theorem factoredQTA_sound (A : FactoredQTA) (good : Fin A.numStates → Bool)
    (cert : FactoredBitmaskCert) (hcert : checkFactoredQTACert A good cert = true) :
    ∀ (k : Nat) (q : QTree (Fin A.numLeaves) k),
      good (evalFactoredQTA A q) = true := by
  have hinv := factoredQTA_inv A good cert hcert
  unfold checkFactoredQTACert at hcert
  simp only [Bool.and_eq_true, List.all_eq_true, mem_bitsOfMask_iff] at hcert
  intro k q
  exact hcert.2 (evalFactoredQTA A q) (hinv k q)

/-! ### Engine D: Factored Monotone Order-Upset Quadtree Certificate Compiler (`MonotoneUpsetCert`) -/

theorem percEval_eq_QNet :
    ∀ {k : Nat} (q : QTree Bool k) (i j : Fin 4),
      bell4Rel (percEval q) i j = true ↔ QNet percLeafRel q i j := by
  intro k q
  induction q with
  | qleaf b => exact percLeaf_spec b
  | qnode nw ne sw se ihnw ihne ihsw ihse =>
    intro i j
    change bell4Rel (qcombExec (percEval nw) (percEval ne) (percEval sw) (percEval se)) i j = true ↔ _
    rw [qcombExec_spec]
    have h0 : (fun x y => bell4Rel (percEval nw) x y = true) = QNet percLeafRel nw := by
      funext x y; exact propext (ihnw x y)
    have h1 : (fun x y => bell4Rel (percEval ne) x y = true) = QNet percLeafRel ne := by
      funext x y; exact propext (ihne x y)
    have h2 : (fun x y => bell4Rel (percEval sw) x y = true) = QNet percLeafRel sw := by
      funext x y; exact propext (ihsw x y)
    have h3 : (fun x y => bell4Rel (percEval se) x y = true) = QNet percLeafRel se := by
      funext x y; exact propext (ihse x y)
    rw [h0, h1, h2, h3]; rfl

theorem quadtree_catalan14_planarity (k : Nat) (q : QTree Bool k) :
    percEval q ≠ CROSS4 ∧ trucEval q ≠ CROSS4 := by
  have hp := factoredQTA_sound percFactoredQTA isPlanar4 planarFactoredCert perc_planarCert_ok k (mapQTree boolToFin2 q)
  have ht := factoredQTA_sound trucFactoredQTA isPlanar4 planarFactoredCert truc_planarCert_ok k (mapQTree boolToFin2 q)
  change (percEval q != CROSS4) = true at hp
  change (trucEval q != CROSS4) = true at ht
  rw [bne_iff_ne] at hp ht
  exact ⟨hp, ht⟩

/-! ### Theorem 1B & 1C: Exact 33-State Coupled Super-Connectivity Dichotomy (`MonotoneUpsetQTA` on `G_8`) -/

theorem percolation_duality_D33 (k : Nat) (q : QTree Bool k) :
    inUpset pairLe certG8.gens (encPair (percEval q) (percEval (notQ q))) = true ∧
    superConnGood (encPair (percEval q) (percEval (notQ q))) = true := by
  let evalP : {m : Nat} → QTree (Fin 2) m → Fin 225 := fun t =>
    encPair (percEval (mapQTree fin2ToBool t)) (percEval (notQ (mapQTree fin2ToBool t)))
  have h := monotoneUpsetQTA_sound percPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe
    pairLe_trans pairMidLe_trans pairHTop_mono pairHBot_mono pairVGlue_mono
    planarPairMask superConnGood certG8 percG8_cert_ok evalP
    (fin2_forall rfl rfl)
    (by
      intro m nw ne sw se
      simp only [evalP, pairVGlue, pairHTop, pairHBot, mapQTree, notQ]
      rw [(decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decMid_encMid _ _).1, (decMid_encMid _ _).2,
          (decMid_encMid _ _).1, (decMid_encMid _ _).2]
      rfl)
    (by
      intro m t
      dsimp only [evalP]
      rw [bitSet_planarPairMask]
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨(quadtree_catalan14_planarity m _).1, (quadtree_catalan14_planarity m _).1⟩)
    k (mapQTree boolToFin2 q)
  simpa only [evalP, map_fin2ToBool_boolToFin2] using h

theorem truchet_duality_D33 (k : Nat) (q : QTree Bool k) :
    inUpset pairLe certG8.gens (encPair (trucEval q) (trucEval (notQ q))) = true ∧
    superConnGood (encPair (trucEval q) (trucEval (notQ q))) = true := by
  let evalT : {m : Nat} → QTree (Fin 2) m → Fin 225 := fun t =>
    encPair (trucEval (mapQTree fin2ToBool t)) (trucEval (notQ (mapQTree fin2ToBool t)))
  have h := monotoneUpsetQTA_sound trucPairLeaf pairHTop pairHBot pairVGlue pairLe pairMidLe
    pairLe_trans pairMidLe_trans pairHTop_mono pairHBot_mono pairVGlue_mono
    planarPairMask superConnGood certG8 trucG8_cert_ok evalT
    (fin2_forall rfl rfl)
    (by
      intro m nw ne sw se
      simp only [evalT, pairVGlue, pairHTop, pairHBot, mapQTree, notQ]
      rw [(decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decPair_encPair _ _).1, (decPair_encPair _ _).2,
          (decMid_encMid _ _).1, (decMid_encMid _ _).2,
          (decMid_encMid _ _).1, (decMid_encMid _ _).2]
      rfl)
    (by
      intro m t
      dsimp only [evalT]
      rw [bitSet_planarPairMask]
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨(quadtree_catalan14_planarity m _).2, (quadtree_catalan14_planarity m _).2⟩)
    k (mapQTree boolToFin2 q)
  simpa only [evalT, map_fin2ToBool_boolToFin2] using h

theorem two_component_barrier_percolation (k : Nat) (q : QTree Bool k)
    (hsplit : numComp4 (percEval q) ≥ 3) :
    ∀ i j : Fin 4, QNet percLeafRel (notQ q) i j := by
  have hgood := (percolation_duality_D33 k q).2
  unfold superConnGood at hgood
  rw [(decPair_encPair _ _).1, (decPair_encPair _ _).2] at hgood
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hgood
  have htop : percEval (notQ q) = TOP4 := by
    rcases hgood.2 with (ha | hb) | ⟨⟨hc, _⟩, _⟩
    · rw [ha, numComp4_TOP4] at hsplit; omega
    · exact hb
    · omega
  intro i j
  rw [← percEval_eq_QNet, htop]
  exact bell4Rel_TOP4 i j

theorem two_component_barrier_truchet (k : Nat) (q : QTree Bool k)
    (hsplit : numComp4 (trucEval q) ≥ 3) :
    ∀ i j : Fin 4, QNet trucLeafRel (notQ q) i j := by
  have hgood := (truchet_duality_D33 k q).2
  unfold superConnGood at hgood
  rw [(decPair_encPair _ _).1, (decPair_encPair _ _).2] at hgood
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hgood
  have htop : trucEval (notQ q) = TOP4 := by
    rcases hgood.2 with (ha | hb) | ⟨⟨hc, _⟩, _⟩
    · rw [ha, numComp4_TOP4] at hsplit; omega
    · exact hb
    · omega
  intro i j
  rw [← trucEval_eq_QNet, htop]
  exact bell4Rel_TOP4 i j

/-! ### Theorem 1E: Constructive 33/33 Exactness & Percolation–Truchet Attractor Equivalence -/

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem d33_exact_completeness_height2 :
    ((bitsOfMask 225 planarPairMask).all (fun x =>
      if inUpset pairLe certG8.gens x then
        d33Witnesses.any (fun w => w.1 == x)
      else true) = true) ∧
    (d33Witnesses.length = 33) ∧
    (d33Witnesses.all (fun w =>
      encPair (percEval (qtree4OfBits w.2.1)) (percEval (notQ (qtree4OfBits w.2.1))) == w.1 &&
      encPair (trucEval (qtree4OfBits w.2.2)) (trucEval (notQ (qtree4OfBits w.2.2))) == w.1) = true) := by
  decide

/-! ## Section 5: Family II — Exact `4^k`-Bit Hilbert Curve Mod-5 & Full-`D_4` Mod-15 Annihilation -/

theorem hilbert_D4_mod15_annihilation (k : Nat) (hk : 1 ≤ k) (q : QTree Bool k) :
    hilbertD4Sum q % 15 = 0 := by
  unfold hilbertD4Sum
  have h1 := (hilbertVal_antiTrans q).1
  have h2 := (hilbertVal_rot180 q).1
  have h3 := (hilbertVal_trans q).1
  have hf1 : hilbertVal ⟨0, by omega⟩ (rot90Q q) = hilbertVal ⟨1, by omega⟩ (flipHQ q) := by
    rw [← flipH_antiTrans_eq_rot90 q, (hilbertVal_antiTrans (flipHQ q)).1]
  have hf2 : hilbertVal ⟨0, by omega⟩ (flipVQ q) = hilbertVal ⟨2, by omega⟩ (flipHQ q) := by
    rw [← flipH_rot180_eq_flipV q, (hilbertVal_rot180 (flipHQ q)).1]
  have hf3 : hilbertVal ⟨0, by omega⟩ (rot270Q q) = hilbertVal ⟨3, by omega⟩ (flipHQ q) := by
    rw [← flipH_trans_eq_rot270 q, (hilbertVal_trans (flipHQ q)).1]
  rw [h1, h2, h3, hf1, hf2, hf3]
  have hm5_q := hilbert_mod5_quadruple_annihilation k hk q
  have hm5_fq := hilbert_mod5_quadruple_annihilation k hk (flipHQ q)
  have hm3_q := hilbert_mod3_orientation_invariance k q
  have hm3_fq := hilbert_mod3_orientation_invariance k (flipHQ q)
  have hneg := hilbert_flipH_mod3_neg k hk q
  omega

/-! ## Section 6: Family III — Period-2 Height-Timed Binary Tree Automaton (`2^k`-Bit CLA & Mod-7) -/

theorem cla_period2_mod7_law (k : Nat) (t : BTree (Bool × Bool) k) :
    (!((claGP t).1 && (claGP t).2) = true) ∧
    ((valX t + valY t) % 7 =
      (((valX t + valY t) % (2 ^ (2 ^ k))) % 7 +
        (if (claGP t).1 then (if k % 2 == 0 then 2 else 4) else 0)) % 7) ∧
    ((claGP t).2 = true → (valX t + valY t) % 7 = if k % 2 == 0 then 1 else 3) := by
  have hs := timedBTA_sound claMod7BTA claMod7Good claMod7Cert claMod7Cert_ok k (mapBTree pairBoolToFin4 t)
  change claMod7Good (phaseOfNat 0 1 k) (evalBTA claMod7BTA (mapBTree pairBoolToFin4 t)) = true at hs
  rw [evalBTA_claMod7_hom t] at hs
  have hph : (phaseOfNat 0 1 k).val = k % 2 := by unfold phaseOfNat; simp
  unfold claMod7Good at hs
  rw [(decCLA_encCLA _ _ _ _).1, (decCLA_encCLA _ _ _ _).2.1,
      (decCLA_encCLA _ _ _ _).2.2.1, (decCLA_encCLA _ _ _ _).2.2.2, hph] at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Nat.mod_mod] at hs
  refine ⟨?_, ?_, ?_⟩
  · simp [hs.1.1]
  · simpa only [beq_iff_eq] using hs.1.2
  · intro hp
    rcases hs.2 with hnp | ⟨h1, _⟩
    · rw [hp] at hnp; cases hnp
    · simpa only [beq_iff_eq] using h1

theorem morton_quadtree_cla_mod7_law (k : Nat) (q : QTree (Bool × Bool) k) :
    let t := qtreeToBTree q
    evalQTA mortonClaMod7QTA (mapQTree pairBoolToFin4 q) = evalBTA claMod7BTA (mapBTree pairBoolToFin4 t) ∧
    ((valX t + valY t) % 7 =
      (((valX t + valY t) % (2 ^ (2 ^ (2 * k)))) % 7 +
        (if (claGP t).1 then 2 else 0)) % 7) := by
  have hmap : mapBTree pairBoolToFin4 (qtreeToBTree q) = qtreeToBTree (mapQTree pairBoolToFin4 q) := by
    induction q with
    | qleaf a => rfl
    | qnode nw ne sw se ihnw ihne ihsw ihse =>
      simp only [qtreeToBTree, mapBTree, mapQTree, ihnw, ihne, ihsw, ihse]
  have heval : evalQTA mortonClaMod7QTA (mapQTree pairBoolToFin4 q) =
      evalBTA claMod7BTA (mapBTree pairBoolToFin4 (qtreeToBTree q)) := by
    rw [hmap]
    exact evalQTA_compilePeriod2BTAtoQTA claMod7BTA rfl rfl (mapQTree pairBoolToFin4 q)
  have hlaw := (cla_period2_mod7_law (2 * k) (qtreeToBTree q)).2.1
  have heven : (2 * k) % 2 == 0 := by
    have : (2 * k) % 2 = 0 := by omega
    simp [this]
  simp only [heven, ite_true] at hlaw
  exact ⟨heval, hlaw⟩

/-! ## Section 7: Kernel-Checked Negative / Hostile Mutation Tests (`checkCert bad = false`) -/

set_option maxRecDepth 2000 in
theorem nonvacuity_barrier_witnesses :
    (numComp4 (percEval (qtree4OfBits 0)) ≥ 3 ∧ percEval (notQ (qtree4OfBits 0)) = TOP4) ∧
    (numComp4 (trucEval (qtree4OfBits 32905)) ≥ 3 ∧ trucEval (notQ (qtree4OfBits 32905)) = TOP4) := by
  decide

theorem sharpness_and_nonvacuity_family3 :
    ((valX btree1_3_1 + valY btree1_3_1) % 7 = 4 ∧
     (((valX btree1_3_1 + valY btree1_3_1) % 4) + 2) % 7 = 2 ∧
     (claGP btree1_3_1).1 = true) ∧
    ((claGP (.leaf (true, false))).2 = true ∧ (valX (.leaf (true, false)) + valY (.leaf (true, false))) % 7 = 1) ∧
    ((claGP btree1_2_1).2 = true ∧ (valX btree1_2_1 + valY btree1_2_1) % 7 = 3) := by
  decide

end CertComp6
