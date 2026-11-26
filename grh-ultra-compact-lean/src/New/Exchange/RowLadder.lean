import New.Seesaw.PairTensorData
import New.Exchange.ChainNorms
noncomputable section
open BigOperators Finset Fintype Function Matrix
variable {P} {D' : Data P} (ϑ : D'.MFoldTwist) {ϑ' : D'.MFoldTwist} (g :
  ∀ p, GL (D'.NodeIndex p) (Data.gridModulus ϑ').ResRing) (n : ℕ)
namespace Data
abbrev EdgeTuple := ∀ e : _ × _,
  Matrix (D'.NodeIndex e.2) (D'.NodeIndex e.1) (gridModulus ϑ).ResRing
abbrev GridDatum := (EdgeTuple ϑ → ℂ) →ₗ[ℂ] ℂ
abbrev IsMuEdge (p q : Node) := p.1 ↔ p.2.1 ≠ q.2.1
def edgeChar (e : _ × _) := (gridModulus ϑ).charOfTamePart
  (gridTamePart ϑ (IsMuEdge e.1 e.2) (ite (e.1.2.1 = e.2.2.1) e.1.2.2 e.1.2.1))
def IsAdmissibleFamily {D : Data P} {ϑ : D.MFoldTwist} (g :
  ∀ p, GL (D.NodeIndex p) (gridModulus ϑ).ResRing) := (∀ z, g (z, 0, D.m) ∈ nodeLevel ..) ∧
  ∀ a, g (_, a, a) = blockInlGL (D.gridDiagEquiv a) (g (_, a, a))
def tupleAction (S : EdgeTuple ϑ') (e : Node × Node) := (g e.2)⁻¹.1 * S e * (g e.1).1
def edgeCharProd (w : Finset (Node × Node)) : ℂ := ∏ e ∈ w,
  (edgeChar ϑ' e).toUnitHom ((g e.2).det / (g e.1).det)
abbrev tupleBound := card (D'.gridModulus ϑ).ResRing ^ (2 * D'.n D'.m) ^ 2
abbrev LeftInvOnMuEdges (S : EdgeTuple ϑ') (w : Finset (Node × Node)) := ∀ e ∈ w, IsMuEdge e.1 e.2 →
  HasLeftInv (S e)
def IsShortSum (w : Finset (Node × Node)) (Λ : GridDatum ϑ') := ∃ X : Type, ∃ W,
  ∃ (c : X → ℂ) (s : X → _), #W ≤ tupleBound ϑ' ^ n ∧
  (∀ x, c x ≠ 0 → IsOfFinOrder (c x) ∧ LeftInvOnMuEdges (s x) w) ∧ ∀ f, Λ f = ∑ x ∈ W, c x * f (s x)
abbrev GridDatum.bind {D : Data P} {ϑ : D.MFoldTwist} (Λ : GridDatum ϑ) {X : Type} [Fintype X] (κ :
  _ → X → ℂ) (t : _ → X → _) := (Λ ∘ₗ .pi fun S ↦ ∑ x, κ S x • .proj (t S x) : GridDatum ϑ)
structure IsTidy {D : Data P} {ϑ : D.MFoldTwist} (n : ℕ) (w : Finset (Node × Node)) (Λ :
  GridDatum ϑ) where
  equivariant g : IsAdmissibleFamily g → ∀ f, Λ (f <| tupleAction g ·) = edgeCharProd g w * Λ f
  isShortSum : IsShortSum n w Λ
def IsLevelTidy (w : Finset (Node × Node)) (Λ : GridDatum ϑ') := IsShortSum n w Λ ∧ ∀ g, (∀ z, ∀ i ≤
  D'.m, g (z, 0, i) ∈ nodeLevel ..) → ∀ f, Λ (f <| tupleAction g ·) = edgeCharProd g w * Λ f
abbrev verticalEdge (z : Bool) (a b : ℕ) := ((z, a, b), z, a, b + 1)
abbrev rowEdge (z : Bool) (a b : ℕ) := ((z, a, b), z, a + 1, b)
def legEdges (z : Bool) (b : ℕ) := (Ico b D'.m).image (verticalEdge z 0)
def gridPath (z : Bool) (a b : ℕ) := (range a).image (rowEdge z · b) ∪ D'.legEdges z b
abbrev path := D'.gridPath false n n ∪ D'.gridPath true n n
variable {P : Parameters} {D : Data P} {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) (z : Bool) (b : ℕ) in
def legDescents b : D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z 0 b := if b < D.m then descentMove (S
  (verticalEdge ..)) ∘ₗ legDescents _ else
  Pi.single (M := (D.GridForm .. →ₗ[ℂ] D.GridForm z 0 ·)) _ .id b
variable {D : Data P} {ϑ : D.MFoldTwist} (S : EdgeTuple ϑ) (z : Bool) {j} (ϑ₁ : D.MFoldTwist) (w :
  Finset (Node × Node))
def gridPathMap : ∀ a b, D.GridForm z 0 D.m →ₗ[ℂ] D.GridForm z a b
  | 0, _ => legDescents S .. | _ + 1, _ => liftMove (S (rowEdge ..)) ∘ₗ gridPathMap ..
@[simp] def diagonalPeriodForm h g := (Space.periodPairing (isConjKernelPair_gridKernel ⟨h, h⟩) ⟨1,
  ⟨fun x ↦ .reindex (D.gridDiagEquiv j) _ (.sum (x, 1, (gridModulus ϑ₁).flipScalar ^ j)), by
  fun_prop⟩, ⟨1, 0, by simp⟩, _, fun _ ↦ gridSpace_diag h ▸ (Space.height_reindex ..).trans_le
  (Space.height_sum_le ..)⟩ g : D.GridForm .. →ₗ[ℂ] GridForm .. →ₗ[ℂ] ℂ)
@[simp] def gridPeriod (Λ : ∀ ϑ, D.GridDatum ϑ) (y : _ × _ × _) h g := Λ y.1 fun S ↦
  diagonalPeriodForm y.1 h g
  (gridPathMap S _ j j (levelIndex y.1 false 0 D.m • y.2.1)) (gridPathMap S _ j j y.2.2)
lemma edgeCharProd_mul g' : edgeCharProd (g * g') w =
  edgeCharProd g w * edgeCharProd g' w := by simp [edgeCharProd, field]
variable (S' : EdgeTuple ϑ) (z : Bool) (b a b' : ℕ) {j : ℕ}
lemma legDescents_congr (h : ∀ e ∈ D.legEdges z b, S e = S' e) : legDescents S z b =
  legDescents S' z b := by fun_induction legDescents S z b <;> grind [legEdges, legDescents]
lemma gridPathMap_congr (h : ∀ e ∈ D.gridPath z a b', S e = S' e) : gridPathMap S z a b' =
  gridPathMap S' z a b' := by induction a <;> grind [gridPath, gridPathMap, legDescents_congr]
lemma IsShortSum.bind {n k w w' X} [Fintype X] {κ : _ → X → ℂ} {t} {Λ : GridDatum ϑ} (N : card X ≤
  tupleBound ϑ ^ k) (H : ∀ S x, κ S x ≠ 0 → LeftInvOnMuEdges S w → IsOfFinOrder (κ S x) ∧
  LeftInvOnMuEdges (t S x) w') : IsShortSum n w Λ → IsShortSum
  (n + k) w' (Λ.bind κ t) | ⟨_, W, c, s, h⟩ => ⟨_, W ×ˢ ⊤, (c • κ ∘ s).uncurry, (t ∘
  s).uncurry, by simp [pow_add, mul_le_mul', sum_product, mul_sum, *]; grind [IsOfFinOrder.mul]⟩
lemma card_matrix_le_tupleBound {p q} (h : p.2 ≤ (D.m, D.m)) (h' : q.2 ≤ (D.m, D.m)) :
    card (Matrix (D.NodeIndex p) (D.NodeIndex q) (gridModulus ϑ).ResRing) ≤ tupleBound ϑ := by
  erw [card_fun, card_fun, ← pow_mul, tupleBound, sq]
  gcongr <;> apply_rules [Fintype.card_pos, card_gridIndex_le]
abbrev EndIndex := D.GridIndex z a D.m
def endWeightData : let ι := D.EndIndex z; Σ' κ, Σ' e : ℕ → _, (∀ j,
    IsLiftWeight (ι j) (ι (j + 1)) κ (D.gridWeight z j (ι (j + 1))) (e j) ∧ D.gridWeight z j (ι j) =
    e (j + 1)) ∧ ∀ j ≤ D.m, IsHCParam κ (e j) (-D.gridParam z 0 j D.m) := by
  intro ι; have hp j h := D.paramsCorrespond_grid true z 0 j _ rfl h .refl
  have s :=
    @strictMono_nat_of_lt_succ _ _ (Fintype.card <| ι ·) (by simp [ι, card_gridIndex, D.t_odd.pos])
  choose κ H using exists_isHCParam_of_le (e := D.gridWeight z 0 (ι 1)) (fun _ ↦
    (Set.range (Fintype.card <| ι ·)).indicator fun _ ↦ D.h - D.t - z.toNat)
    (D.hasGap_gridParam · z 0 D.m |>.neg) (hp 0 D.nat_le_of_hasLogBound · |>.rec (by
    simp [IsMatchedPair, pairSign, gridSigns_eq_one]; grind-ring -linarith -ac -order))
  refine ⟨κ, _, (⟨·, Nat.rec (fun _ ↦ H.1) (by grind [IsHCParam.paramsCorrespond_iff,
    gridSigns_eq_one])⟩) fun j ↦ .imp_left (⟨·, s (by simp), rfl⟩) ?_⟩
  simp +contextual [ι, H, FitsRanks, s.monotone.ne_of_lt_of_lt_nat j, funext_iff, s _, (s.monotone
    j.zero_le).trans_lt]; cases z <;> simp [gridWeight, card_gridIndex] <;> grind
abbrev endDetExp := (D.endWeightData z).2.1
def endLevel :=
  (gridModulus ϑ₁).levelOfSubgroup (n := EndIndex z b') (nodeLevel ϑ₁ (z, b', D.m)) deriving IsLevel
lemma endLevel_le_principalLevel : endLevel ϑ₁ z b' ≤ principalLevel _ gridLevelGen :=
  fun _ ⟨_, k, a⟩ ↦ a ▸ (Modulus.mem_principalLevel_iff gridModulus_one_ideal _).2
  ((Units.ext (Modulus.factor_reductionK₀ ..)).symm.trans
  (((ite_le_sup ..).trans_eq (bot_sup_eq _) : nodeLevel .. ≤ _) k))
def endKernel := have h := (endWeightData z).2.2.1 b'; thetaKernel h.1 (1 * P.jetScale D.s)
       (h.2 ▸ gridChar_hasWeight ϑ₁ ..) (gridChar_hasWeight ϑ₁ ..) (endLevel ϑ₁ z b')
lemma boxes_endWeightData_le (h : j ≤ D.m) : Fintype.card (D.EndIndex z j) ≤ 2 * D.n D.m ∧
  boxes (D.endWeightData z).1 (Fintype.card (D.EndIndex z j)) ≤ D.b₁ * D.r ^ 4 ∧ ∀ τ,
  (D.endDetExp z j τ).natAbs ≤ ⌈20 * D.b⌉₊ := by
  have := boxes_le_of_isHCParam ((D.endWeightData z).2.2.2 j h) (by simpa using
    (D.abs_gridParam_le · h le_rfl))
  grw [this.1, card_gridIndex_le] <;> simp [h, this]; exact D.nat_le_of_hasLogBound
def endBranching := Classical.indefiniteDescription _
  (exists_branching_pairing (D.gridDiagEquiv_spec le_rfl) (D.gridSigns_eq_one le_rfl)
  ((D.endWeightData _).2.2.2 _ le_rfl) ((D.endWeightData _).2.2.2 _ le_rfl) D.gridParam_interlace)
abbrev endPairing := (dotProductBilin ℂ ℂ).compl₂ (D.endBranching.1.map (↑)).mulVecLin
def endBlockPoint h := U.block (D.gridDiagEquiv D.m) (h, (gridModulus ϑ₁).flipScalar ^ D.m)
instance isStd_gridSpace {z i} : (D.gridSpace 0 z i D.m).IsStd := by cases z <;> cases i <;> first
  | apply isStd_spaceY | exact D.m_eq_two_mul_varrho_add_two ▸ isStd_signedSpace (gridSigns_eq_one _
    D.m_eq_two_mul_varrho_add_two.le)
def endToAlgForm := (D.gridSpace 0 z 0 _).toAlgForm ((D.endWeightData z).2.2.2 0 zero_le)
abbrev FixedByEndLevels (y : ∀ _, _) := ∀ z,
  D.endToAlgForm z (y z) ∈ levelSpace (algFormRep ..) (endLevel ϑ₁ ..)
def endDatum j := P.vacuumScale D.s ^ Fintype.card (D.EndIndex z j.succ × D.EndIndex z j) •
  vacuumDatum (stdSpace ..) (stdSpace ..) _ (Pi.single (S (rowEdge z j D.m)) 1)
abbrev endChain j F := chain (endKernel ϑ z) (endDatum S z) j (D.endToAlgForm z F)
def endPeriod (Λ : GridDatum ϑ) (y : ∀ _, _) := Λ fun S ↦ let c z := (endChain S z _ (y z)).1
  classIntegral stdRatPoints (endLevel ϑ ..) fun h ↦ D.endPairing (c _ h) (c _ (endBlockPoint ϑ h))
lemma IsTidy.exists_square_move {P} {D : Data P} {ϑ z a b n w} {Λ : GridDatum ϑ} {p v Q U R} r {T J}
  [Fintype T] (τ : D.GridIndex z a b ≃ D.NodeIndex U) (σ : D.NodeIndex p ⊕ T ≃ D.NodeIndex Q) (ρ :
  D.NodeIndex r ⊕ T ≃ D.NodeIndex R) (ψ : AddChar _ ℂ) {χ ε C} {L M : J → _} (q : ∀ i,
  SquareLaw χ ε C (L i) (M i)) (hQ : ∀ g, @IsAdmissibleFamily _ D ϑ g →
  g R = blockInlGL ρ (g r) ∧ ∀ k, let u := update (update g p k) Q (blockInlGL σ k)
  IsAdmissibleFamily u ∧ u p = k) (h : U ≠ v ∧ (IsMuEdge Q U ∧ ¬IsMuEdge U R ∨ IsMuEdge p v ∧
  ¬IsMuEdge v r) ∧ (∀ q ∈ [U, R, v, r], q.2 ≤ (D.m, D.m) ∧ q ∉ [p, Q]) ∧ ∀ e ∈ w, e.1 ∉ [p, Q] ∧ e.2
  ∉ [p, Q, R, r]) (H : IsTidy n (insert (p, v) (insert (Q, U) w)) Λ) (X : χ = (edgeChar ϑ (p, v) *
  edgeChar ϑ (Q, U))⁻¹ ∧ edgeChar ϑ (U, R) = edgeChar ϑ (p, v) ∧ edgeChar ϑ (v, r) = edgeChar ϑ (Q,
  U) := by simp [edgeChar]) : ∃ Φ, IsTidy (n + 2) (insert (U, R) (insert (v, r) w)) Φ ∧ ∀ f : _ →
  _ → J, DependsOn f w → Λ (fun S ↦ let x := (S (Q, U)).submatrix τ σ; ∑ k, ψ (k * x.toCols₂).trace
    * M (f S k) (fromRows (S (p, v)) x.toCols₁)) = C * Φ fun S ↦ let x := (S (U, R)).submatrix ρ τ
  L (f S x.toRows₂) (fromCols (S (v, r)) x.toRows₁) := by
  obtain ⟨⟨uv, μ, bQ, hw⟩, ⟨_, W, c, s, -, hc, hΛ⟩, d, d₁, d₄⟩ := h, H.2,
    exists_partner_kernel χ ε (Modulus.isValuationPair_resRing _)
  simp [-Prod.forall, LeftInvOnMuEdges] at hw hQ hc bQ
  let y (S : EdgeTuple ϑ) := fromRows (S (p, v)) ((S (Q, U)).submatrix τ σ).toCols₁
  let t S (M : _ × _) : EdgeTuple ϑ := w.piecewise S (update (update 0 (U, R) M.1) (v, r) M.2)
  let G (d : _ → ℂ) := Λ.bind (fun S M ↦ d (y S) * graphKernel χ ε (M.2.fromCols (M.1.submatrix ρ
    τ).toRows₁) (y S) * ψ ((M.1 * S (Q, U)).submatrix (ρ ∘ .inr) (σ ∘ .inr)).trace) t
  have I g (hg : IsAdmissibleFamily g) (k : GL (D.NodeIndex p) (gridModulus ϑ).ResRing) d f :
    G (d <| (blockGL (g v, reindexGL τ.symm (g U)))⁻¹.1 * · * k.1) (f <| tupleAction g ·) =
    edgeCharProd g (insert (U, R) (insert (v, r) w)) * G d f := by
    erw [(?_ : edgeCharProd .. = _ / _ * _), mul_assoc, ← H.1 _ ((hQ g hg).2 k).1]
    simp [G, hΛ, mul_sum, graphKernel_equivariant χ ε (blockGL (g v, reindexGL τ.symm (g U))) (g r)
      k _ (y (s _)), W.sum_comm, mul_assoc, mul_left_comm _ (_ / _), -coe_units_inv]
    rw [eq_comm, ← ((injective_gl_inv_mul_mul (g R) (g U)).prodMap
      (injective_gl_inv_mul_mul (g r) (g v))).bijective_of_finite.sum_comp]
    congr! 9 <;> simp [y, t, tupleAction, *, entrywise, ← Matrix.mul_assoc, ← map_inv,
      reindex_equiv σ, reindex_equiv ρ, reindex_equiv τ]
    ext1; simp [piecewise, update]
    split_ifs <;> subst_vars <;> simp [tupleAction, *, ← map_inv]
    simp +contextual [edgeCharProd, mt (hw _), *, MulChar.inv_apply_eq_inv', uv.symm]
    field [MulChar.apply_eq_zero_iff]
  have l S : HasLeftInv (S (Q, U)) → HasLeftInv (y S).toRows₂ := .imp' (·.submatrix (σ ∘ .inl) τ)
    (by simp_all [y, entrywise, reindex_equiv τ])
  refine ⟨G 1, ⟨(I · · 1 1), (LinearMap.ext fun f ↦ ?_ : G 1 = G d) ▸ H.2.bind (by
    simp [sq, mul_le_mul', card_matrix_le_tupleBound, *]) fun S M n m ↦ ?_⟩, fun f hL ↦ ?_⟩
  · simpa +unfoldPartialApp [tupleAction, edgeCharProd, G, hΛ, expect_sum_comm, d₁, ← expect_mul,
      ← mul_expect] using congr(𝔼 k, $(I 1 (by simp [IsAdmissibleFamily]) k d f))
  · simp +contextual [t, uv, mt (hw _), -Prod.forall, LeftInvOnMuEdges] at m ⊢
    obtain ⟨E, e', e⟩ := (d₁ ..).1 (left_ne_zero_of_mul n)
    use E.mul (ψ.toMonoidHom.isOfFinOrder (isMulTorsion_of_finite _)), fun _ ↦ (e' (m.1 (by
      lia))).imp' (·.fromCols 0 |>.submatrix τ.symm ρ.symm) (by simp [entrywise, reindex_equiv ρ,
      reindex_equiv τ]), fun _ ↦ e (l _ (m.2.1 (by lia))), m.2.2
  erw [hΛ, hΛ, mul_sum]; congr with i
  exact (or_not.imp_right (hc i)).elim (by simp [·]) fun ⟨_, m', m, _⟩ ↦ .trans congr(_ * ∑ k, _ *
    $(d₄ _ _ _ (q _) (y _) (μ.symm.imp (m' ·.1) (l _ <| m ·.1)))) (by
    simp [@hL (w.piecewise _ _) _ fun _ ↦ (ite_eq_left ·), t, uv, mt (hw _), sum_prod_type,
      reindex_equiv
      (reindex ρ τ), sum_eq_sum_fromRows, mul_comm (graphKernel ..), sum_eq_sum_fromCols, mul_sum,
      @sum_comm (Matrix T ..), mul_left_comm C, mul_assoc, trace, mul_apply, reindex_equiv τ])
end Data
end
section FoldSeg1
variable {P} {D : Data P} {a b}
lemma Data.exists_squareLaw_grid z (h : a < D.m) (m : b < D.m) : ∃ κ σ, ∃ c : _ → ℂˣ, D.CostsSquares
  1 (c ·) ∧ ∀ ϑ (l : _ × (GridForm z (a + 1) b →ₗ[ℂ] ℂ)), SquareLaw (edgeChar ϑ (verticalEdge z a
  b) * edgeChar ϑ (rowEdge z a b))⁻¹ σ (κ / c ϑ) (fun x ↦ l.2 (descentMove x.toCols₂
  (liftMove x.toCols₁ l.1))) fun y ↦ l.2 (liftMove y.toRows₂ (descentMove y.toRows₁ l.1)) := by
  have ⟨x, T⟩ := exists_isTameFor_costsSquares_one ⟨_, D.w _ + D.w _, _, D.t, by
    simpa [← zpow_add] using! (D.mu₀_hasWeight a.succ).mul
      (D.mu₀_hasWeight b.succ), by simp_all, by grind, by simp; grind, by simp; grind
    [w_le_two_mul_b]⟩ (D.omega_zpow_ne_one _) D.b₁ ⟨ite z a b + 1, by grind⟩
  have := one_square (D.gridSpace 0 z a b) (gridSpace ..) (gridSpace ..) (gridSpace ..)
    (isEdgeFamily_grid id false rfl) (isEdgeFamily_grid id _ rfl) (isEdgeFamily_grid _ _ rfl)
    (isEdgeFamily_grid _ _ rfl) (Fintype.equivOfCardEq ?_) ?_ D.t ?_ ?_ (by simp; grw
    [card_gridIndex_le, card_gridIndex_le, (D.nat_le_of_hasLogBound : D.n _ ≤ D.h₂)] <;> grind) x ?_
  choose C κ c n hc H using this
  use κ, ?_, (.mk0 _ <| n ·), T hc, fun ϑ l ↦ ?_; swap
  convert! ← H ..; rw [(?_ : _ * _ = _ * _)]
  ext; apply finprod_mul_distrib <;> toFinite_tac
  all_goals clear * -; cases z <;> intros <;> (try apply_fun Additive.ofMul) <;> simp_all [gridChar,
    liftChar, liftTamePart, card_gridIndex, rankTwist, TameChar.pow, twist_one_spec,
    card_neg_gridSigns, show (1 : D.Twist).ψ = 1 by rfl] <;> first | match_scalars <;> grind | grind
lemma Data.descent_past_gridPathMap {P} {D : Data P} {a b} (h : b < D.m) z (h' : a ≤ b) : ∃ κ, ∃ c :
    _ → ℂˣ, D.CostsSquares a (c ·) ∧ ∀ ϑ n w Λ,
  (∀ e ∈ w, z ∉ [e.1.1, e.2.1] ∨ ∃ i ≥ a, e = rowEdge z i b) → IsTidy n (w ∪ D.gridPath z a b) Λ →
  ∃ Φ, IsTidy (n + 2 * a) (insert (verticalEdge z a b) (D.gridPath z a (b + 1)) ∪ w) Φ ∧ ∀ F
  (l : EdgeTuple ϑ → _ →ₗ[ℂ] ℂ), DependsOn l w → Λ (fun S ↦ l S (gridPathMap S z a b F)) =
  κ / c ϑ * Φ fun S ↦ l S (descentMove (S (verticalEdge z a b)) (gridPathMap S z a _ F)) := by
  induction' a with a i
  · use 1, 1, .one, fun _ _ w Λ _ C ↦ ⟨Λ, by
      convert! C using 1; simp [gridPath, legEdges]; grind, by simp [gridPathMap,
      legDescents.eq_1 _ z b, h]⟩
  choose κ' c' g' H' using i (by lia)
  choose κ σ c g Q using exists_squareLaw_grid z (h.trans' h') h
  use κ' * κ, c' * c, g'.mul g .refl, fun ϑ n w Λ _ C ↦ ?_
  simp [gridPath, Finset.range_add_one] at C ⊢
  obtain ⟨Φ, C, M⟩ := H' ϑ _ _ Λ (by grind) (w.insert_union .. ▸ C)
  simp [↓Finset.insert_union, gridPath] at C
  refine (C.exists_square_move _ (.refl _) (.sumEmpty ..) (.sumEmpty _ Empty) 1 (Q ϑ) (by
    simp [IsAdmissibleFamily, Units.ext_iff, ← Matrix.ext_iff]; grind)
    (by simp [-Prod.forall]; grind [legEdges])).imp
    fun Φ' ↦ .imp_right fun M' F l hl ↦ (M F (l · ∘ₗ _) (by grind [DependsOn])).trans ?_
  simpa [Fintype.card_congr Matrix.of.symm, ← mul_assoc, div_mul_div_comm] using! congr(κ' / _ *
    $(M' (fun S _ ↦ (gridPathMap S z a _ F, l S)) (by clear * - hl; grind [DependsOn,
    gridPathMap_congr, gridPath])))
end FoldSeg1
