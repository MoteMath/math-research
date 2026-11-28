import OMAReductions.R_Erdos211_erdos_211_variants_one_sixth_R1

/-!
# Melchior's Inequality for Erdos211.erdos_211.variants.one_sixth.R1.H2

We prove that for any finite non-collinear point set `s : Finset ℝ²` with `2 ≤ s.card`,
the sum of line multiplicities satisfies
`∑ L ∈ determinedLines s, |s ∩ L| ≤ 3 * |determinedLines s|`
(in fact `≤ 3 * |determinedLines s| - 3`).

The proof is completely elementary and topology-free:
1. Translate the plane so no determined line passes through the origin, and apply
   polar duality `p ↦ { x ∈ ℝ × ℝ | dot p x = 1 }` to obtain a finite arrangement `A`
   of pairwise non-parallel affine lines whose intersection vertices biject with
   `determinedLines s`, preserving multiplicities.
2. Represent open regions of `A` as realizable sign vectors `σ : A → Bool`.
   Induction on `A` gives the exact region count `|F(A)| + |V(A)| = 1 + |A| + E(A)`
   and the exact central-arrangement count `|F₀(A)| = 2 * |A|`.
3. Double-counting adjacent walls `(σ, p)` gives `∑_{σ ∈ F(A)} |walls σ| = 2 * (E(A) + |A|)`.
4. The Convex Wall Lemma (`R_σ` is determined by its walls) yields `|walls σ| ≥ 3`
   for `σ ∉ F₀(A)`, `|walls σ| ≥ 2` for `σ ∈ F₀(A)`, and `|walls σ| + |walls (¬σ)| ≥ 5`
   for every antipodal pair in `F₀(A)`.
5. Combining (2)-(4) gives `2 (E + n) ≥ 3 (F - 2n) + 5n = 3 (1 + n + E - V) - n`,
   hence `E ≤ 3 V - 3 ≤ 3 V`.
-/

namespace OMA.Melchior

open EuclideanGeometry Erdos211
open scoped BigOperators Classical

/- ### Section 1: Elementary 2D linear algebra on `ℝ × ℝ` -/

abbrev Pt := ℝ × ℝ

def dot (p q : Pt) : ℝ := p.1 * q.1 + p.2 * q.2
def det2 (p q : Pt) : ℝ := p.1 * q.2 - p.2 * q.1

def padd (p q : Pt) : Pt := (p.1 + q.1, p.2 + q.2)
def psub (p q : Pt) : Pt := (p.1 - q.1, p.2 - q.2)
def smulPt (t : ℝ) (p : Pt) : Pt := (t * p.1, t * p.2)
def rot90 (p : Pt) : Pt := (-p.2, p.1)
def normSq (p : Pt) : ℝ := p.1 * p.1 + p.2 * p.2

noncomputable def interPt (p q : Pt) : Pt :=
  ((q.2 - p.2) / det2 p q, (p.1 - q.1) / det2 p q)

noncomputable def solve2 (p q : Pt) (a b : ℝ) : Pt :=
  ((a * q.2 - b * p.2) / det2 p q, (b * p.1 - a * q.1) / det2 p q)

lemma dot_comm (p q : Pt) : dot p q = dot q p := by
  dsimp [dot]; ring

lemma dot_padd (p a b : Pt) : dot p (padd a b) = dot p a + dot p b := by
  dsimp [dot, padd]; ring

lemma dot_psub (p a b : Pt) : dot p (psub a b) = dot p a - dot p b := by
  dsimp [dot, psub]; ring

lemma dot_smul (p : Pt) (t : ℝ) (x : Pt) : dot p (smulPt t x) = t * dot p x := by
  dsimp [dot, smulPt]; ring

lemma dot_rot90_self (p : Pt) : dot p (rot90 p) = 0 := by
  dsimp [dot, rot90]; ring

lemma dot_rot90 (q p : Pt) : dot q (rot90 p) = det2 p q := by
  dsimp [dot, rot90, det2]; ring

lemma det2_antisymm (p q : Pt) : det2 q p = -det2 p q := by
  dsimp [det2]; ring

lemma normSq_pos_of_ne_zero {p : Pt} (hp : p ≠ (0, 0)) : 0 < normSq p := by
  dsimp [normSq]
  by_contra h
  have h1 : p.1 * p.1 = 0 := by nlinarith
  have h2 : p.2 * p.2 = 0 := by nlinarith
  have hp1 : p.1 = 0 := mul_self_eq_zero.mp h1
  have hp2 : p.2 = 0 := mul_self_eq_zero.mp h2
  exact hp (Prod.ext hp1 hp2)

lemma ne_zero_of_det2_ne_zero {p q : Pt} (h : det2 p q ≠ 0) : p ≠ (0, 0) := by
  intro hp
  apply h
  rw [hp]
  dsimp [det2]; ring

lemma dot_interPt_left {p q : Pt} (h : det2 p q ≠ 0) : dot p (interPt p q) = 1 := by
  dsimp [dot, interPt, det2] at *
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]
  ring

lemma dot_interPt_right {p q : Pt} (h : det2 p q ≠ 0) : dot q (interPt p q) = 1 := by
  dsimp [dot, interPt, det2] at *
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]
  ring

lemma interPt_unique {p q x : Pt} (h : det2 p q ≠ 0) (hp : dot p x = 1) (hq : dot q x = 1) :
    x = interPt p q := by
  dsimp [dot, det2] at hp hq h
  apply Prod.ext <;> dsimp [interPt, det2] <;> rw [eq_div_iff h]
  · linear_combination q.2 * hp - p.2 * hq
  · linear_combination p.1 * hq - q.1 * hp

lemma dot_solve2_left {p q : Pt} (h : det2 p q ≠ 0) (a b : ℝ) :
    dot p (solve2 p q a b) = a := by
  dsimp [dot, solve2, det2] at *
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]
  ring

lemma dot_solve2_right {p q : Pt} (h : det2 p q ≠ 0) (a b : ℝ) :
    dot q (solve2 p q a b) = b := by
  dsimp [dot, solve2, det2] at *
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]
  ring

lemma solve2_unique {p q x : Pt} (h : det2 p q ≠ 0) :
    x = solve2 p q (dot p x) (dot q x) := by
  dsimp [det2] at h
  apply Prod.ext <;> dsimp [solve2, dot, det2] <;> rw [eq_div_iff h] <;> ring

/-- Any finite collection of nontrivial affine lines `a * x + b * y = c` leaves a point uncovered. -/
lemma exists_avoid_affine (F : Finset (ℝ × ℝ × ℝ))
    (hF : ∀ f ∈ F, f.1 ≠ 0 ∨ f.2.1 ≠ 0) :
    ∃ x : Pt, ∀ f ∈ F, f.1 * x.1 + f.2.1 * x.2 ≠ f.2.2 := by
  let xs : Finset ℝ := (F.filter (fun f => f.2.1 = 0)).image (fun f => f.2.2 / f.1)
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, ∀ r ∈ xs, r < x0 := by
    by_cases hxs : xs.Nonempty
    · exact ⟨xs.max' hxs + 1, fun r hr => by linarith [Finset.le_max' xs r hr]⟩
    · exact ⟨0, fun r hr => (hxs ⟨r, hr⟩).elim⟩
  let ys : Finset ℝ := (F.filter (fun f => f.2.1 ≠ 0)).image (fun f => (f.2.2 - f.1 * x0) / f.2.1)
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℝ, ∀ r ∈ ys, r < y0 := by
    by_cases hys : ys.Nonempty
    · exact ⟨ys.max' hys + 1, fun r hr => by linarith [Finset.le_max' ys r hr]⟩
    · exact ⟨0, fun r hr => (hys ⟨r, hr⟩).elim⟩
  refine ⟨(x0, y0), fun f hf heq => ?_⟩
  by_cases hb : f.2.1 = 0
  · have ha : f.1 ≠ 0 := (hF f hf).resolve_right (not_not.mpr hb)
    have hmem : f.2.2 / f.1 ∈ xs :=
      Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hb⟩, rfl⟩
    have hlt := hx0 _ hmem
    have : x0 = f.2.2 / f.1 := by
      rw [hb, zero_mul, add_zero] at heq
      field_simp [ha]; linarith
    linarith
  · have hmem : (f.2.2 - f.1 * x0) / f.2.1 ∈ ys :=
      Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hb⟩, rfl⟩
    have hlt := hy0 _ hmem
    have : y0 = (f.2.2 - f.1 * x0) / f.2.1 := by
      field_simp [hb]; linarith
    linarith

/-- Given a finite set of excluded points `E` and `x`, we can perturb `y` inside any open
neighborhood (defined by strict inequalities) so the line through `x` and `y'` avoids `E`. -/
lemma exists_perturb_avoid_pts (x y : Pt) (hxy : x ≠ y) (E : Finset Pt)
    (G : Finset (Pt × ℝ)) (hG : ∀ g ∈ G, 0 < dot g.1 y - g.2) :
    ∃ y' : Pt, (∀ g ∈ G, 0 < dot g.1 y' - g.2) ∧
      ∀ v ∈ E, v ≠ x → det2 (psub y' x) (psub v x) ≠ 0 := by
  let u := rot90 (psub y x)
  have hu_ne : det2 (psub y x) u ≠ 0 := by
    have hne : psub y x ≠ (0, 0) := by
      intro h
      apply hxy
      apply Prod.ext <;> dsimp [psub] at h <;> linarith [congrArg Prod.fst h, congrArg Prod.snd h]
    have hpos := normSq_pos_of_ne_zero hne
    dsimp [det2, u, rot90, normSq] at *
    nlinarith
  -- Perturb y' = padd y (smulPt ε u) for small ε > 0.
  -- Bad ε for E: det2 (y - x + ε u) (v - x) = det2 (y - x) (v - x) + ε * det2 u (v - x) = 0.
  -- If det2 u (v - x) = 0, then v - x is parallel to u, so det2 (y - x) (v - x) ≠ 0 already!
  let badE : Finset ℝ :=
    (E.filter (fun v => det2 u (psub v x) ≠ 0)).image
      (fun v => -(det2 (psub y x) (psub v x)) / det2 u (psub v x))
  -- Upper bound on ε > 0 from G: dot g.1 y - g.2 + ε * dot g.1 u > 0
  let capsG : Finset ℝ :=
    (G.filter (fun g => dot g.1 u < 0)).image (fun g => (dot g.1 y - g.2) / (-dot g.1 u))
  obtain ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ capsG, δ < r := by
    by_cases hne : capsG.Nonempty
    · let m := capsG.min' hne
      have hm_pos : 0 < m := by
        obtain ⟨g, hg, hgm⟩ := Finset.mem_image.mp (Finset.min'_mem capsG hne)
        obtain ⟨hgG, hgu⟩ := Finset.mem_filter.mp hg
        dsimp [m]; rw [← hgm]
        exact div_pos (hG g hgG) (by linarith)
      exact ⟨m / 2, by linarith, fun r hr => by linarith [Finset.min'_le capsG r hr]⟩
    · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
  -- Pick ε ∈ (0, δ) avoiding badE (finite set)
  obtain ⟨ε, hε_pos, hε_lt, hε_avoid⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ∉ badE := by
    -- Take ε = min of positive elements of badE (if any) halved, or δ/2
    let posBad := badE.filter (fun r => 0 < r)
    by_cases hpb : posBad.Nonempty
    · let m := min δ (posBad.min' hpb)
      have hm_pos : 0 < m := lt_min hδ_pos (Finset.mem_filter.mp (Finset.min'_mem posBad hpb)).2
      refine ⟨m / 2, by linarith, by linarith [min_le_left δ (posBad.min' hpb)], ?_⟩
      intro hmem
      have hmem' : m / 2 ∈ posBad := Finset.mem_filter.mpr ⟨hmem, by linarith⟩
      have := Finset.min'_le posBad (m / 2) hmem'
      have := min_le_right δ (posBad.min' hpb)
      linarith
    · refine ⟨δ / 2, by linarith, by linarith, ?_⟩
      intro hmem
      exact hpb ⟨δ / 2, Finset.mem_filter.mpr ⟨hmem, by linarith⟩⟩
  refine ⟨padd y (smulPt ε u), ?_, ?_⟩
  · intro g hg
    rw [dot_padd, dot_smul]
    by_cases hgu : dot g.1 u < 0
    · have hmem : (dot g.1 y - g.2) / (-dot g.1 u) ∈ capsG :=
        Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hgu⟩, rfl⟩
      have h1 : ε < (dot g.1 y - g.2) / (-dot g.1 u) := lt_trans hε_lt (hδ_le _ hmem)
      have h2 : 0 < -dot g.1 u := by linarith
      have h3 : ε * (-dot g.1 u) < dot g.1 y - g.2 := (lt_div_iff₀ h2).mp h1
      linarith
    · have h0 : 0 ≤ dot g.1 u := not_lt.mp hgu
      have h1 : 0 ≤ ε * dot g.1 u := mul_nonneg hε_pos.le h0
      linarith [hG g hg]
  · intro v hv hvx hdet
    have hlin : det2 (psub (padd y (smulPt ε u)) x) (psub v x) =
        det2 (psub y x) (psub v x) + ε * det2 u (psub v x) := by
      dsimp [det2, psub, padd, smulPt]; ring
    rw [hlin] at hdet
    by_cases hdu : det2 u (psub v x) = 0
    · rw [hdu, mul_zero, add_zero] at hdet
      -- Both det2 (y - x) (v - x) = 0 and det2 u (v - x) = 0, contradicting det2 (y - x) u ≠ 0
      have hvx : psub v x ≠ (0, 0) := by
        intro h0
        apply hvx
        apply Prod.ext <;> dsimp [psub] at h0 <;> linarith [congrArg Prod.fst h0, congrArg Prod.snd h0]
      have hns := normSq_pos_of_ne_zero hvx
      dsimp [det2, u, rot90, normSq] at hdet hdu hu_ne hns
      have hprod : ((psub y x).1 * (psub y x).1 + (psub y x).2 * (psub y x).2) *
          ((psub v x).1 * (psub v x).1 + (psub v x).2 * (psub v x).2) =
          ((psub y x).1 * (psub v x).2 - (psub y x).2 * (psub v x).1) ^ 2 +
          (-(psub y x).2 * (psub v x).2 - (psub y x).1 * (psub v x).1) ^ 2 := by ring
      have hpos_y : 0 < (psub y x).1 * (psub y x).1 + (psub y x).2 * (psub y x).2 := by
        have hne_y : (psub y x).1 * (psub y x).1 + (psub y x).2 * (psub y x).2 ≠ 0 :=
          fun h0 => hu_ne (by linarith)
        exact lt_of_le_of_ne (by nlinarith [sq_nonneg (psub y x).1, sq_nonneg (psub y x).2]) hne_y.symm
      nlinarith [mul_pos hpos_y hns]
    · apply hε_avoid
      refine Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hdu⟩, ?_⟩
      field_simp [hdu]
      linarith

/- ### Section 2: Pairwise non-parallel line arrangements and sign vectors -/

def NonParallel (A : Finset Pt) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → det2 p q ≠ 0

lemma NonParallel.subset {A B : Finset Pt} (hB : NonParallel B) (hAB : A ⊆ B) : NonParallel A :=
  fun p hp q hq hpq => hB p (hAB hp) q (hAB hq) hpq

lemma NonParallel.ne_zero {A : Finset Pt} (hA : NonParallel A) (hcard : 2 ≤ A.card)
    {p : Pt} (hp : p ∈ A) : p ≠ (0, 0) := by
  obtain ⟨q, hq, hpq⟩ : ∃ q ∈ A, q ≠ p := by
    have : 1 < A.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hap : a = p
    · exact ⟨b, hb, fun h => hab (hap.trans h.symm)⟩
    · exact ⟨a, ha, hap⟩
  exact ne_zero_of_det2_ne_zero (hA p hp q hq hpq.symm)

noncomputable def verts (A : Finset Pt) : Finset Pt :=
  A.offDiag.image (fun pq => interPt pq.1 pq.2)

noncomputable def inc (A : Finset Pt) (v : Pt) : ℕ :=
  (A.filter (fun p => dot p v = 1)).card

noncomputable def lineVerts (A : Finset Pt) (p : Pt) : Finset Pt :=
  (verts A).filter (fun v => dot p v = 1)

lemma mem_verts_iff {A : Finset Pt} (hA : NonParallel A) {v : Pt} :
    v ∈ verts A ↔ ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ dot p v = 1 ∧ dot q v = 1 := by
  simp only [verts, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, rfl⟩
    exact ⟨p, hp, q, hq, hpq, dot_interPt_left (hA p hp q hq hpq),
      dot_interPt_right (hA p hp q hq hpq)⟩
  · rintro ⟨p, hp, q, hq, hpq, hpv, hqv⟩
    exact ⟨(p, q), ⟨hp, hq, hpq⟩, (interPt_unique (hA p hp q hq hpq) hpv hqv).symm⟩

lemma double_count_inc (A : Finset Pt) :
    (∑ v ∈ verts A, inc A v) = ∑ p ∈ A, (lineVerts A p).card := by
  simp only [inc, lineVerts, Finset.card_filter]
  exact Finset.sum_comm

def signVal (b : Bool) (r : ℝ) : Prop := if b then 0 < r else r < 0

lemma signVal_iff (b : Bool) (r : ℝ) :
    signVal b r ↔ r ≠ 0 ∧ (0 < r ↔ b = true) := by
  cases b <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte, iff_false, iff_true]
  · constructor
    · intro h; exact ⟨ne_of_lt h, not_lt.mpr h.le⟩
    · rintro ⟨hne, hle⟩; exact lt_of_le_of_ne (not_lt.mp hle) hne
  · constructor
    · intro h; exact ⟨ne_of_gt h, h⟩
    · rintro ⟨_, h⟩; exact h

lemma signVal_neg (b : Bool) (r : ℝ) : signVal (!b) r ↔ signVal b (-r) := by
  cases b <;> simp [signVal]

lemma signVal_mul_pos {b : Bool} {r t : ℝ} (ht : 0 < t) :
    signVal b (t * r) ↔ signVal b r := by
  cases b <;> simp only [signVal, ↓reduceIte, Bool.false_eq_true]
  · constructor <;> intro h <;> nlinarith
  · exact mul_pos_iff_of_pos_left ht

lemma signVal_add {b : Bool} {r s : ℝ} (hr : signVal b r) (hs : signVal b s) :
    signVal b (r + s) := by
  cases b <;> simp only [signVal, ↓reduceIte, Bool.false_eq_true] at * <;> linarith

lemma signVal_ne_zero {b : Bool} {r : ℝ} (h : signVal b r) : r ≠ 0 :=
  ((signVal_iff b r).mp h).1

lemma signVal_unique {b₁ b₂ : Bool} {r : ℝ} (h₁ : signVal b₁ r) (h₂ : signVal b₂ r) :
    b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp only [signVal, ↓reduceIte, Bool.false_eq_true] at h₁ h₂ <;>
    first | rfl | linarith

def Realizes (A : Finset Pt) (σ : A → Bool) (x : Pt) : Prop :=
  ∀ p : A, signVal (σ p) (dot p.1 x - 1)

def Realizes0 (A : Finset Pt) (σ : A → Bool) (d : Pt) : Prop :=
  ∀ p : A, signVal (σ p) (dot p.1 d)

noncomputable def regions (A : Finset Pt) : Finset (A → Bool) :=
  Finset.univ.filter (fun σ => ∃ x : Pt, Realizes A σ x)

noncomputable def centralRegions (A : Finset Pt) : Finset (A → Bool) :=
  Finset.univ.filter (fun σ => ∃ d : Pt, Realizes0 A σ d)

noncomputable def walls (A : Finset Pt) (σ : A → Bool) : Finset A :=
  Finset.univ.filter (fun p : A =>
    ∃ x : Pt, dot p.1 x = 1 ∧ ∀ q : A, q ≠ p → signVal (σ q) (dot q.1 x - 1))

lemma mem_regions_iff {A : Finset Pt} {σ : A → Bool} :
    σ ∈ regions A ↔ ∃ x : Pt, Realizes A σ x := by
  simp [regions]

lemma mem_centralRegions_iff {A : Finset Pt} {σ : A → Bool} :
    σ ∈ centralRegions A ↔ ∃ d : Pt, Realizes0 A σ d := by
  simp [centralRegions]

lemma mem_walls_iff {A : Finset Pt} {σ : A → Bool} {p : A} :
    p ∈ walls A σ ↔ ∃ x : Pt, dot p.1 x = 1 ∧ ∀ q : A, q ≠ p → signVal (σ q) (dot q.1 x - 1) := by
  simp [walls]

/-- Every central sign vector is realized in the affine arrangement (take a large scalar multiple). -/
lemma centralRegions_subset_regions (A : Finset Pt) :
    centralRegions A ⊆ regions A := by
  intro σ hσ
  obtain ⟨d, hd⟩ := mem_centralRegions_iff.mp hσ
  rw [mem_regions_iff]
  let caps : Finset ℝ := A.attach.image (fun p => 1 / |dot p.1 d|)
  obtain ⟨M, hM_pos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ r ∈ caps, r < M := by
    by_cases hne : caps.Nonempty
    · refine ⟨max 1 (caps.max' hne + 1), by linarith [le_max_left 1 (caps.max' hne + 1)], ?_⟩
      intro r hr
      exact lt_of_lt_of_le (by linarith [Finset.le_max' caps r hr]) (le_max_right _ _)
    · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
  refine ⟨smulPt M d, fun p => ?_⟩
  rw [dot_smul]
  have hp := hd p
  have hne : dot p.1 d ≠ 0 := signVal_ne_zero hp
  have habs : 0 < |dot p.1 d| := abs_pos.mpr hne
  have hmem : 1 / |dot p.1 d| ∈ caps := Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩
  have hlt : 1 / |dot p.1 d| < M := hM _ hmem
  have h1 : 1 < M * |dot p.1 d| := by
    have := (div_lt_iff₀ habs).mp hlt
    linarith
  cases hb : σ p <;> simp only [signVal, hb, ↓reduceIte, Bool.false_eq_true] at hp ⊢
  · rw [abs_of_neg hp] at h1; linarith
  · rw [abs_of_pos hp] at h1; linarith

/- ### Section 3: Exact 1D interval counting and add-one-line region counts -/

/-- On a line `dot p x = 1` (with `p ≠ 0`), the set of sign vectors on `A` realized along
`dot p x = 1` away from intersections with `A` has cardinality `|lineVerts (insert p A) p| + 1`. -/
lemma card_line_slices {A : Finset Pt} {p : Pt} (hpA : p ∉ A)
    (hnp : NonParallel (insert p A)) (hp0 : p ≠ (0, 0)) :
    (Finset.univ.filter (fun τ : A → Bool =>
      ∃ x : Pt, dot p x = 1 ∧ Realizes A τ x)).card =
      (lineVerts (insert p A) p).card + 1 := by
  let S := Finset.univ.filter (fun τ : A → Bool => ∃ x : Pt, dot p x = 1 ∧ Realizes A τ x)
  let x0 : Pt := smulPt (1 / normSq p) p
  have hns : 0 < normSq p := normSq_pos_of_ne_zero hp0
  have hx0 : dot p x0 = 1 := by
    dsimp [dot, x0, smulPt, normSq] at hns ⊢
    have h1 : p.1 * (1 / (p.1 * p.1 + p.2 * p.2) * p.1) +
        p.2 * (1 / (p.1 * p.1 + p.2 * p.2) * p.2) =
        (p.1 * p.1 + p.2 * p.2) / (p.1 * p.1 + p.2 * p.2) := by ring
    rw [h1, div_self (ne_of_gt hns)]
  let γ : ℝ → Pt := fun t => padd x0 (smulPt t (rot90 p))
  have hγ_on : ∀ t : ℝ, dot p (γ t) = 1 := by
    intro t
    dsimp [γ]
    rw [dot_padd, hx0, dot_smul, dot_rot90_self, mul_zero, add_zero]
  have hγ_surj : ∀ x : Pt, dot p x = 1 → ∃ t : ℝ, γ t = x := by
    intro x hx
    refine ⟨dot x (rot90 p) / normSq p, ?_⟩
    dsimp [dot] at hx
    have hne : p.1 * p.1 + p.2 * p.2 ≠ 0 := ne_of_gt hns
    apply Prod.ext <;> dsimp [γ, padd, smulPt, rot90, x0, dot, normSq]
    · rw [one_div_mul_eq_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
      linear_combination -p.1 * hx
    · rw [one_div_mul_eq_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
      linear_combination -p.2 * hx
  -- For each q ∈ A, the unique intersection parameter t_q where dot q (γ t_q) = 1:
  have hdet_q : ∀ q : A, det2 p q.1 ≠ 0 := fun q =>
    hnp p (Finset.mem_insert_self _ _) q.1 (Finset.mem_insert_of_mem q.2) (fun h => hpA (h ▸ q.2))
  let tOf : A → ℝ := fun q => (1 - dot q.1 x0) / det2 p q.1
  have hγ_val : ∀ (q : A) (t : ℝ), dot q.1 (γ t) - 1 = det2 p q.1 * (t - tOf q) := by
    intro q t
    dsimp only [γ, tOf]
    rw [dot_padd, dot_smul q.1 t (rot90 p), dot_rot90, mul_sub, mul_div_cancel₀ _ (hdet_q q)]
    ring
  -- The finite set T of distinct crossing parameters on ℝ
  let T : Finset ℝ := A.attach.image tOf
  have hT_card : T.card = (lineVerts (insert p A) p).card := by
    refine Finset.card_bij (fun t _ => γ t) ?_ ?_ ?_
    · intro t ht
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
      rw [lineVerts, Finset.mem_filter]
      refine ⟨(mem_verts_iff hnp).mpr ⟨p, Finset.mem_insert_self _ _, q.1,
        Finset.mem_insert_of_mem q.2, fun h => hpA (h ▸ q.2), hγ_on _, ?_⟩, hγ_on _⟩
      have := hγ_val q (tOf q)
      linarith
    · intro t₁ _ t₂ _ heq
      have h1 := congrArg (fun x => dot x (rot90 p)) heq
      dsimp [γ, dot, padd, smulPt, rot90] at h1
      dsimp [normSq] at hns
      nlinarith
    · intro v hv
      rw [lineVerts, Finset.mem_filter] at hv
      obtain ⟨hvV, hvp⟩ := hv
      obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := (mem_verts_iff hnp).mp hvV
      -- One of a, b is not p, hence in A
      obtain ⟨q, hqA, hvq⟩ : ∃ q ∈ A, dot q v = 1 := by
        rcases Finset.mem_insert.mp ha with rfl | haA
        · rcases Finset.mem_insert.mp hb with rfl | hbA
          · exact (hab rfl).elim
          · exact ⟨b, hbA, hvb⟩
        · exact ⟨a, haA, hva⟩
      obtain ⟨t, ht⟩ := hγ_surj v hvp
      have hval := hγ_val ⟨q, hqA⟩ t
      rw [ht, hvq, sub_self] at hval
      have hteq : t = tOf ⟨q, hqA⟩ := by
        rcases mul_eq_zero.mp hval.symm with h0 | h0
        · exact (hdet_q ⟨q, hqA⟩ h0).elim
        · linarith
      exact ⟨tOf ⟨q, hqA⟩, Finset.mem_image.mpr ⟨⟨q, hqA⟩, Finset.mem_attach _ _, rfl⟩,
        hteq ▸ ht⟩
  -- Now prove S.card = T.card + 1 by bijection between S and Finset.range (T.card + 1):
  -- Actually even simpler: sort T into a strictly increasing list `L = T.sort (· ≤ ·)`,
  -- or directly map each `t ∉ T` to the count `(T.filter (· < t)).card ∈ Finset.range (T.card + 1)`!
  -- Check: two parameters t₁, t₂ ∉ T have the same sign vector on A IFF they have the same
  -- count of elements of T strictly below them!
  have hsame_count : ∀ t₁ t₂ : ℝ, t₁ ∉ T → t₂ ∉ T →
      ((∀ q : A, signVal (decide (0 < dot q.1 (γ t₁) - 1)) (dot q.1 (γ t₂) - 1)) ↔
       (T.filter (· < t₁)).card = (T.filter (· < t₂)).card) := by
    intro t₁ t₂ ht₁ ht₂
    have hneq1 : ∀ q : A, t₁ ≠ tOf q := fun q h => ht₁ (h ▸ Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
    have hneq2 : ∀ q : A, t₂ ≠ tOf q := fun q h => ht₂ (h ▸ Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
    have hsgn : ∀ q : A,
        signVal (decide (0 < dot q.1 (γ t₁) - 1)) (dot q.1 (γ t₂) - 1) ↔
        (tOf q < t₁ ↔ tOf q < t₂) := by
      intro q
      rw [hγ_val q t₁, hγ_val q t₂]
      have hd := hdet_q q
      have h1 := hneq1 q
      have h2 := hneq2 q
      rcases lt_or_gt_of_ne hd with hdn | hdp
      · by_cases hlt1 : tOf q < t₁
        · have hneg1 : ¬ (0 < det2 p q.1 * (t₁ - tOf q)) := by nlinarith
          simp only [decide_eq_false hneg1, signVal, Bool.false_eq_true, ↓reduceIte, hlt1, true_iff]
          constructor <;> intro h <;> nlinarith
        · have hpos1 : 0 < det2 p q.1 * (t₁ - tOf q) := by
            have : t₁ < tOf q := lt_of_le_of_ne (not_lt.mp hlt1) h1
            nlinarith
          simp only [decide_eq_true hpos1, signVal, ↓reduceIte, hlt1, false_iff]
          constructor <;> intro h
          · intro hlt2; nlinarith
          · have : t₂ < tOf q := lt_of_le_of_ne (not_lt.mp h) h2
            nlinarith
      · by_cases hlt1 : tOf q < t₁
        · have hpos1 : 0 < det2 p q.1 * (t₁ - tOf q) := by nlinarith
          simp only [decide_eq_true hpos1, signVal, ↓reduceIte, hlt1, true_iff]
          constructor <;> intro h <;> nlinarith
        · have hneg1 : ¬ (0 < det2 p q.1 * (t₁ - tOf q)) := by
            have : t₁ < tOf q := lt_of_le_of_ne (not_lt.mp hlt1) h1
            nlinarith
          simp only [decide_eq_false hneg1, signVal, Bool.false_eq_true, ↓reduceIte, hlt1, false_iff]
          constructor <;> intro h
          · intro hlt2; nlinarith
          · have : t₂ < tOf q := lt_of_le_of_ne (not_lt.mp h) h2
            nlinarith
    simp only [hsgn]
    constructor
    · intro hall
      congr 1
      ext r
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hr, hr1⟩
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
        exact ⟨hr, (hall q).mp hr1⟩
      · rintro ⟨hr, hr2⟩
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
        exact ⟨hr, (hall q).mpr hr2⟩
    · intro hcard q
      have hsub : T.filter (· < t₁) = T.filter (· < t₂) := by
        rcases le_total t₁ t₂ with hle | hle
        · exact Finset.eq_of_subset_of_card_le
            (fun r hr => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hr).1, lt_of_lt_of_le (Finset.mem_filter.mp hr).2 hle⟩)
            hcard.ge
        · exact (Finset.eq_of_subset_of_card_le
            (fun r hr => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hr).1, lt_of_lt_of_le (Finset.mem_filter.mp hr).2 hle⟩)
            hcard.le).symm
      have hmem : tOf q ∈ T := Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
      have hiff := Finset.ext_iff.mp hsub (tOf q)
      simpa [Finset.mem_filter, hmem] using hiff
  -- Every count k ∈ {0, ..., T.card} is realized by some t ∉ T!
  have hexists_t : ∀ k ≤ T.card, ∃ t : ℝ, t ∉ T ∧ (T.filter (· < t)).card = k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      by_cases hTne : T.Nonempty
      · refine ⟨T.min' hTne - 1, fun h => by linarith [Finset.min'_le T _ h], ?_⟩
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro r hr; linarith [Finset.min'_le T r hr]
      · refine ⟨0, fun h => hTne ⟨0, h⟩, by simp [Finset.not_nonempty_iff_eq_empty.mp hTne]⟩
    · -- Use T.orderEmbOfFin rfl : Fin T.card ↪o ℝ
      let e := T.orderEmbOfFin rfl
      have hkm1 : k - 1 < T.card := by omega
      by_cases hkend : k = T.card
      · subst hkend
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        refine ⟨T.max' hTne + 1, fun h => by linarith [Finset.le_max' T _ h], ?_⟩
        have : T.filter (· < T.max' hTne + 1) = T := by
          ext r; simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hr; linarith [Finset.le_max' T r hr]
        rw [this]
      · have hklt : k < T.card := by omega
        let a := e ⟨k - 1, hkm1⟩
        let b := e ⟨k, hklt⟩
        have hab : a < b := e.strictMono (by show (k - 1 : ℕ) < k; omega)
        let t := (a + b) / 2
        have hat : a < t := by dsimp [t]; linarith
        have htb : t < b := by dsimp [t]; linarith
        have htT : t ∉ T := by
          intro ht
          obtain ⟨i, hi⟩ : ∃ i : Fin T.card, e i = t := by
            have ht' : t ∈ (T : Set ℝ) := Finset.mem_coe.mpr ht
            rw [← Finset.range_orderEmbOfFin T rfl] at ht'
            exact Set.mem_range.mp ht'
          by_cases hik : i.1 < k
          · have : i ≤ ⟨k - 1, hkm1⟩ := by show i.1 ≤ k - 1; omega
            have : e i ≤ a := e.monotone this
            linarith
          · have : ⟨k, hklt⟩ ≤ i := by show k ≤ i.1; omega
            have : b ≤ e i := e.monotone this
            linarith
        refine ⟨t, htT, ?_⟩
        -- T.filter (· < t) = (Finset.univ.filter (fun i : Fin T.card => i.1 < k)).image e
        have hfilt : T.filter (· < t) = (Finset.univ.filter (fun i : Fin T.card => i.1 < k)).image e := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hrT, hrt⟩
            have hr' : r ∈ Set.range e := by
              rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hrT
            obtain ⟨i, rfl⟩ := hr'
            refine ⟨i, ?_, rfl⟩
            by_contra hge
            have : ⟨k, hklt⟩ ≤ i := by show k ≤ i.1; omega
            have : b ≤ e i := e.monotone this
            linarith
          · rintro ⟨i, hik, rfl⟩
            refine ⟨Finset.mem_coe.mp (by rw [← Finset.range_orderEmbOfFin T rfl]; exact Set.mem_range_self i), ?_⟩
            have : i ≤ ⟨k - 1, hkm1⟩ := by show i.1 ≤ k - 1; omega
            exact lt_of_le_of_lt (e.monotone this) hat
        rw [hfilt, Finset.card_image_of_injective _ e.injective]
        have hbij : (Finset.univ.filter (fun i : Fin T.card => i.1 < k)).card = (Finset.range k).card := by
          refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
          · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i₁ _ i₂ _ h; exact Fin.ext h
          · intro j hj
            have hjk := Finset.mem_range.mp hj
            exact ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
        rw [hbij, Finset.card_range]
  -- Now establish S.card = T.card + 1 via Finset.card_bij with Finset.range (T.card + 1)!
  rw [← hT_card, ← Finset.card_range (T.card + 1)]
  refine Finset.card_bij
    (fun τ hτ =>
      let x := (Finset.mem_filter.mp hτ).2.choose
      let hx := (Finset.mem_filter.mp hτ).2.choose_spec
      let t := (hγ_surj x hx.1).choose
      (T.filter (· < t)).card) ?_ ?_ ?_
  · intro τ hτ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_filter_le _ _))
  · intro τ₁ hτ₁ τ₂ hτ₂ hcard
    dsimp only at hcard
    set x₁ := (Finset.mem_filter.mp hτ₁).2.choose
    set hx₁ := (Finset.mem_filter.mp hτ₁).2.choose_spec
    set t₁ := (hγ_surj x₁ hx₁.1).choose
    have ht₁_eq : γ t₁ = x₁ := (hγ_surj x₁ hx₁.1).choose_spec
    set x₂ := (Finset.mem_filter.mp hτ₂).2.choose
    set hx₂ := (Finset.mem_filter.mp hτ₂).2.choose_spec
    set t₂ := (hγ_surj x₂ hx₂.1).choose
    have ht₂_eq : γ t₂ = x₂ := (hγ_surj x₂ hx₂.1).choose_spec
    have ht₁T : t₁ ∉ T := by
      intro hmem
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
      have h0 := hγ_val q t₁
      rw [hq, sub_self, mul_zero, ht₁_eq] at h0
      exact signVal_ne_zero (hx₁.2 q) h0
    have ht₂T : t₂ ∉ T := by
      intro hmem
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
      have h0 := hγ_val q t₂
      rw [hq, sub_self, mul_zero, ht₂_eq] at h0
      exact signVal_ne_zero (hx₂.2 q) h0
    have hall := (hsame_count t₁ t₂ ht₁T ht₂T).mpr hcard
    funext q
    have h1 : signVal (τ₁ q) (dot q.1 x₁ - 1) := hx₁.2 q
    have h2 : signVal (τ₂ q) (dot q.1 x₂ - 1) := hx₂.2 q
    rw [← ht₁_eq] at h1
    rw [← ht₂_eq] at h2
    have hdec : decide (0 < dot q.1 (γ t₁) - 1) = τ₁ q := by
      have := (signVal_iff (τ₁ q) (dot q.1 (γ t₁) - 1)).mp h1
      cases hb : τ₁ q <;> simp [hb] at this ⊢
      · exact this.2
      · exact this.2
    have hq' := hall q
    rw [hdec] at hq'
    exact signVal_unique hq' h2
  · intro k hk
    obtain ⟨t, htT, htk⟩ := hexists_t k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    let τ : A → Bool := fun q => decide (0 < dot q.1 (γ t) - 1)
    have hτS : τ ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, γ t, hγ_on t, fun q => ?_⟩
      have hne : dot q.1 (γ t) - 1 ≠ 0 := by
        rw [hγ_val q t]
        refine mul_ne_zero (hdet_q q) (sub_ne_zero.mpr ?_)
        intro h; exact htT (h ▸ Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
      rw [signVal_iff]
      refine ⟨hne, by simp [τ]⟩
    refine ⟨τ, hτS, ?_⟩
    dsimp only
    set x₁ := (Finset.mem_filter.mp hτS).2.choose
    set hx₁ := (Finset.mem_filter.mp hτS).2.choose_spec
    set t₁ := (hγ_surj x₁ hx₁.1).choose
    have ht₁_eq : γ t₁ = x₁ := (hγ_surj x₁ hx₁.1).choose_spec
    have ht₁T : t₁ ∉ T := by
      intro hmem
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
      have h0 := hγ_val q t₁
      rw [hq, sub_self, mul_zero, ht₁_eq] at h0
      exact signVal_ne_zero (hx₁.2 q) h0
    have hmatch : ∀ q : A, signVal (decide (0 < dot q.1 (γ t₁) - 1)) (dot q.1 (γ t) - 1) := by
      intro q
      have h1 : signVal (τ q) (dot q.1 x₁ - 1) := hx₁.2 q
      rw [← ht₁_eq] at h1
      have hdec : decide (0 < dot q.1 (γ t₁) - 1) = τ q := by
        have := (signVal_iff (τ q) (dot q.1 (γ t₁) - 1)).mp h1
        cases hb : τ q <;> simp [hb] at this ⊢
        · exact this.2
        · exact this.2
      rw [hdec]
      have hne : dot q.1 (γ t) - 1 ≠ 0 := by
        rw [hγ_val q t]
        refine mul_ne_zero (hdet_q q) (sub_ne_zero.mpr ?_)
        intro h; exact htT (h ▸ Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩)
      exact (signVal_iff _ _).mpr ⟨hne, by simp [τ]⟩
    rw [(hsame_count t₁ t ht₁T htT).mp hmatch, htk]

/-- Perturbing a point `x` on `dot p x = 1` along `±ε * p` realizes both signs on `p`
while preserving all strict signs on `A`. -/
lemma perturb_off_line {A : Finset Pt} {p : Pt} {τ : A → Bool} {x : Pt}
    (hp0 : p ≠ (0, 0)) (hx_on : dot p x = 1) (hx_real : Realizes A τ x) (b : Bool) :
    ∃ y : Pt, signVal b (dot p y - 1) ∧ Realizes A τ y := by
  have hns : 0 < normSq p := normSq_pos_of_ne_zero hp0
  let caps : Finset ℝ :=
    (A.attach.filter (fun q => dot q.1 p ≠ 0)).image (fun q => |dot q.1 x - 1| / |dot q.1 p|)
  obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ caps, ε < r := by
    by_cases hne : caps.Nonempty
    · let m := caps.min' hne
      have hm_pos : 0 < m := by
        obtain ⟨q, hq, hqm⟩ := Finset.mem_image.mp (Finset.min'_mem caps hne)
        have hqp := (Finset.mem_filter.mp hq).2
        dsimp [m]; rw [← hqm]
        exact div_pos (abs_pos.mpr (signVal_ne_zero (hx_real q))) (abs_pos.mpr hqp)
      exact ⟨m / 2, by linarith, fun r hr => by linarith [Finset.min'_le caps r hr]⟩
    · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
  let s : ℝ := if b then ε else -ε
  refine ⟨padd x (smulPt s p), ?_, ?_⟩
  · rw [dot_padd, hx_on, dot_smul]
    have hpp : dot p p = normSq p := rfl
    rw [hpp]
    cases b <;> simp only [s, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
  · intro q
    rw [dot_padd, dot_smul]
    have hq := hx_real q
    by_cases hqp : dot q.1 p = 0
    · rw [hqp, mul_zero, add_zero]; exact hq
    · have hmem : |dot q.1 x - 1| / |dot q.1 p| ∈ caps :=
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqp⟩, rfl⟩
      have hlt : ε < |dot q.1 x - 1| / |dot q.1 p| := hε_lt _ hmem
      have habs_qp : 0 < |dot q.1 p| := abs_pos.mpr hqp
      have h1 : ε * |dot q.1 p| < |dot q.1 x - 1| := (lt_div_iff₀ habs_qp).mp hlt
      have hs_abs : |s| = ε := by cases b <;> simp [s, abs_of_pos hε_pos]
      have h2 : |s * dot q.1 p| < |dot q.1 x - 1| := by
        rw [abs_mul, hs_abs]; exact h1
      cases hb : τ q <;> simp only [signVal, hb, ↓reduceIte, Bool.false_eq_true] at hq ⊢
      · rw [abs_of_neg hq] at h2
        have := (abs_lt.mp h2).2; linarith
      · rw [abs_of_pos hq] at h2
        have := (abs_lt.mp h2).1; linarith

/-- Linear interpolation: if `x₁` and `x₂` realize the same signs on `A` and opposite signs on `p`,
some convex combination lies on `dot p x = 1` and realizes the same signs on `A`. -/
lemma interpolate_on_line {A : Finset Pt} {p : Pt} {τ : A → Bool} {x₁ x₂ : Pt}
    (h₁ : Realizes A τ x₁) (h₂ : Realizes A τ x₂)
    (hp₁ : dot p x₁ - 1 < 0) (hp₂ : 0 < dot p x₂ - 1) :
    ∃ x : Pt, dot p x = 1 ∧ Realizes A τ x := by
  let a := 1 - dot p x₁
  let b := dot p x₂ - 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : 0 < a + b := by linarith
  let t := a / (a + b)
  have ht0 : 0 < t := div_pos ha hab
  have ht1 : 0 < 1 - t := by
    have : 1 - t = b / (a + b) := by dsimp [t]; field_simp [ne_of_gt hab]; ring
    rw [this]; exact div_pos hb hab
  let x := padd (smulPt (1 - t) x₁) (smulPt t x₂)
  refine ⟨x, ?_, ?_⟩
  · dsimp [x]
    rw [dot_padd, dot_smul, dot_smul]
    dsimp [t, a, b]
    have h1 : (1 - (1 - dot p x₁) / (1 - dot p x₁ + (dot p x₂ - 1))) * dot p x₁ +
        (1 - dot p x₁) / (1 - dot p x₁ + (dot p x₂ - 1)) * dot p x₂ =
        dot p x₁ + (1 - dot p x₁) * (dot p x₂ - dot p x₁) / (dot p x₂ - dot p x₁) := by ring
    rw [h1, mul_div_cancel_right₀ _ (by linarith : dot p x₂ - dot p x₁ ≠ 0)]
    ring
  · intro q
    dsimp [x]
    have hcomb : dot q.1 (padd (smulPt (1 - t) x₁) (smulPt t x₂)) - 1 =
        (1 - t) * (dot q.1 x₁ - 1) + t * (dot q.1 x₂ - 1) := by
      rw [dot_padd, dot_smul, dot_smul]; ring
    rw [hcomb]
    exact signVal_add ((signVal_mul_pos ht1).mpr (h₁ q)) ((signVal_mul_pos ht0).mpr (h₂ q))

/-- Exact add-one-line recurrence for `|regions A|`. -/
lemma card_regions_insert {A : Finset Pt} {p : Pt} (hpA : p ∉ A)
    (hnp : NonParallel (insert p A)) (hp0 : p ≠ (0, 0)) :
    (regions (insert p A)).card = (regions A).card + (lineVerts (insert p A) p).card + 1 := by
  let res : (↥(insert p A) → Bool) → (A → Bool) := fun σ q => σ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
  let S : Finset (A → Bool) :=
    Finset.univ.filter (fun τ => ∃ x : Pt, dot p x = 1 ∧ Realizes A τ x)
  have hmaps : (regions (insert p A) : Set (↥(insert p A) → Bool)).MapsTo res (regions A) := by
    intro σ hσ
    obtain ⟨x, hx⟩ := mem_regions_iff.mp (Finset.mem_coe.mp hσ)
    exact Finset.mem_coe.mpr (mem_regions_iff.mpr ⟨x, fun q => hx ⟨q.1, Finset.mem_insert_of_mem q.2⟩⟩)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ τ ∈ regions A,
      ((regions (insert p A)).filter (fun σ => res σ = τ)).card = if τ ∈ S then 2 else 1 := by
    intro τ hτ
    -- Every σ with res σ = τ is uniquely determined by its value at p:
    let extB : Bool → (↥(insert p A) → Bool) := fun b q =>
      if h : q.1 = p then b else τ ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left h⟩
    have hext_inj : Function.Injective extB := by
      intro b₁ b₂ h
      have := congrFun h ⟨p, Finset.mem_insert_self _ _⟩
      simpa [extB] using this
    have hext_res : ∀ b, res (extB b) = τ := by
      intro b; funext q
      have hqp : q.1 ≠ p := fun h => hpA (h ▸ q.2)
      simp [res, extB, hqp]
    have hmem_fib : ∀ σ, σ ∈ (regions (insert p A)).filter (fun σ => res σ = τ) ↔
        ∃ b : Bool, σ = extB b ∧ extB b ∈ regions (insert p A) := by
      intro σ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hσR, hσres⟩
        refine ⟨σ ⟨p, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
        · funext q
          by_cases hqp : q.1 = p
          · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
            subst hqeq; simp [extB]
          · simp only [extB, hqp, ↓reduceDIte]
            have := congrFun hσres ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
            simpa [res] using this
        · convert hσR using 1
          funext q
          by_cases hqp : q.1 = p
          · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
            subst hqeq; simp [extB]
          · simp only [extB, hqp, ↓reduceDIte]
            have := congrFun hσres ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
            simpa [res] using this.symm
      · rintro ⟨b, rfl, hb⟩
        exact ⟨hb, hext_res b⟩
    have hcard_eq : ((regions (insert p A)).filter (fun σ => res σ = τ)).card =
        (Finset.univ.filter (fun b : Bool => extB b ∈ regions (insert p A))).card := by
      refine Finset.card_bij (fun σ _ => σ ⟨p, Finset.mem_insert_self _ _⟩) ?_ ?_ ?_
      · intro σ hσ
        obtain ⟨b, rfl, hb⟩ := (hmem_fib σ).mp hσ
        simpa [extB] using hb
      · intro σ₁ hσ₁ σ₂ hσ₂ heq
        obtain ⟨b₁, rfl, _⟩ := (hmem_fib σ₁).mp hσ₁
        obtain ⟨b₂, rfl, _⟩ := (hmem_fib σ₂).mp hσ₂
        simp only [extB, ↓reduceDIte] at heq
        rw [heq]
      · intro b hb
        refine ⟨extB b, (hmem_fib _).mpr ⟨b, rfl, (Finset.mem_filter.mp hb).2⟩, by simp [extB]⟩
    rw [hcard_eq]
    by_cases hτS : τ ∈ S
    · rw [if_pos hτS]
      obtain ⟨x, hxp, hxτ⟩ := (Finset.mem_filter.mp hτS).2
      have hboth : ∀ b : Bool, extB b ∈ regions (insert p A) := by
        intro b
        obtain ⟨y, hyb, hyτ⟩ := perturb_off_line hp0 hxp hxτ b
        rw [mem_regions_iff]
        refine ⟨y, fun q => ?_⟩
        by_cases hqp : q.1 = p
        · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
          subst hqeq; simpa [extB] using hyb
        · simp only [extB, hqp, ↓reduceDIte]
          exact hyτ ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
      simp [hboth]
    · rw [if_neg hτS]
      -- At least one b works (from x realizing τ; if dot p x = 1 then τ ∈ S, contradiction!)
      obtain ⟨x, hxτ⟩ := mem_regions_iff.mp hτ
      have hxp_ne : dot p x ≠ 1 := fun h => hτS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, h, hxτ⟩)
      have hex1 : ∃ b : Bool, extB b ∈ regions (insert p A) := by
        refine ⟨decide (0 < dot p x - 1), mem_regions_iff.mpr ⟨x, fun q => ?_⟩⟩
        by_cases hqp : q.1 = p
        · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
          subst hqeq
          simp only [extB, ↓reduceDIte]
          exact (signVal_iff _ _).mpr ⟨sub_ne_zero.mpr hxp_ne, by simp⟩
        · simp only [extB, hqp, ↓reduceDIte]
          exact hxτ ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
      -- Cannot have BOTH true and false, else interpolate_on_line gives τ ∈ S!
      have hnotboth : ¬ (extB true ∈ regions (insert p A) ∧ extB false ∈ regions (insert p A)) := by
        rintro ⟨ht, hf⟩
        obtain ⟨x₂, hx₂⟩ := mem_regions_iff.mp ht
        obtain ⟨x₁, hx₁⟩ := mem_regions_iff.mp hf
        have hp₂ : 0 < dot p x₂ - 1 := by
          have := hx₂ ⟨p, Finset.mem_insert_self _ _⟩
          simpa [extB, signVal] using this
        have hp₁ : dot p x₁ - 1 < 0 := by
          have := hx₁ ⟨p, Finset.mem_insert_self _ _⟩
          simpa [extB, signVal] using this
        have hτ₁ : Realizes A τ x₁ := fun q => by
          have hqp : q.1 ≠ p := fun h => hpA (h ▸ q.2)
          simpa [extB, hqp] using hx₁ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
        have hτ₂ : Realizes A τ x₂ := fun q => by
          have hqp : q.1 ≠ p := fun h => hpA (h ▸ q.2)
          simpa [extB, hqp] using hx₂ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
        obtain ⟨z, hzp, hzτ⟩ := interpolate_on_line hτ₁ hτ₂ hp₁ hp₂
        exact hτS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hzp, hzτ⟩)
      obtain ⟨b, hb⟩ := hex1
      have hnb : extB (!b) ∉ regions (insert p A) := by
        intro h; cases b <;> exact hnotboth (by simp_all)
      have hfilt_eq : Finset.univ.filter (fun c : Bool => extB c ∈ regions (insert p A)) = {b} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hc
          by_contra hcb
          have : c = !b := by cases b <;> cases c <;> simp_all
          exact hnb (this ▸ hc)
        · rintro rfl; exact hb
      rw [hfilt_eq, Finset.card_singleton]
  rw [Finset.sum_congr rfl hfib]
  have hSsub : S ⊆ regions A := by
    intro τ hτ
    obtain ⟨x, hxp, hxτ⟩ := (Finset.mem_filter.mp hτ).2
    exact mem_regions_iff.mpr ⟨x, hxτ⟩
  have hsum_ite : (∑ τ ∈ regions A, if τ ∈ S then (2 : ℕ) else 1) =
      (regions A).card + S.card := by
    have hsplit : (∑ τ ∈ regions A, if τ ∈ S then (2 : ℕ) else 1) =
        (∑ τ ∈ regions A, 1) + (∑ τ ∈ regions A, if τ ∈ S then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> rfl
    rw [hsplit, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSsub]
  rw [hsum_ite, card_line_slices hpA hnp hp0]
  omega

/-- Exact Euler identity for any finite pairwise non-parallel arrangement `A` with no zero vector:
`|regions A| + |verts A| = 1 + |A| + ∑ v ∈ verts A, inc A v`. -/
lemma euler_regions (A : Finset Pt) (hnp : NonParallel A) (h0 : ∀ p ∈ A, p ≠ (0, 0)) :
    (regions A).card + (verts A).card = 1 + A.card + ∑ v ∈ verts A, inc A v := by
  induction A using Finset.induction_on with
  | empty =>
    have hreg : (regions ∅).card = 1 := by
      have : regions ∅ = Finset.univ := by
        ext σ; simp [regions, Realizes]
      rw [this, Finset.card_univ]; decide
    simp [hreg, verts]
  | @insert p A hpA ih =>
    have hnpA : NonParallel A := hnp.subset (Finset.subset_insert _ _)
    have h0A : ∀ q ∈ A, q ≠ (0, 0) := fun q hq => h0 q (Finset.mem_insert_of_mem hq)
    have hp0 : p ≠ (0, 0) := h0 p (Finset.mem_insert_self _ _)
    have hih := ih hnpA h0A
    rw [card_regions_insert hpA hnp hp0, Finset.card_insert_of_notMem hpA]
    -- Compare (∑ inc - |verts|) between A and insert p A:
    -- verts A ⊆ verts (insert p A)
    have hvsub : verts A ⊆ verts (insert p A) := by
      intro v hv
      obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := (mem_verts_iff hnpA).mp hv
      exact (mem_verts_iff hnp).mpr
        ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab, hva, hvb⟩
    -- New vertices v ∈ verts (insert p A) \ verts A all lie on p and have inc = 2!
    have hnew_on_p : verts (insert p A) \ verts A ⊆ lineVerts (insert p A) p := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := (mem_verts_iff hnp).mp hv1
      rw [lineVerts, Finset.mem_filter]
      refine ⟨hv1, ?_⟩
      rcases Finset.mem_insert.mp ha with rfl | haA
      · exact hva
      · rcases Finset.mem_insert.mp hb with rfl | hbA
        · exact hvb
        · exact (hv2 ((mem_verts_iff hnpA).mpr ⟨a, haA, b, hbA, hab, hva, hvb⟩)).elim
    have hnew_inc : ∀ v ∈ verts (insert p A) \ verts A, inc (insert p A) v = 2 := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      have hvp : dot p v = 1 := (Finset.mem_filter.mp (hnew_on_p hv)).2
      -- Exactly one q ∈ A has dot q v = 1!
      have hcardA : (A.filter (fun q => dot q v = 1)).card = 1 := by
        have hle1 : (A.filter (fun q => dot q v = 1)).card ≤ 1 := by
          by_contra! hgt
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hgt
          exact hv2 ((mem_verts_iff hnpA).mpr
            ⟨a, (Finset.mem_filter.mp ha).1, b, (Finset.mem_filter.mp hb).1, hab,
              (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩)
        have hge1 : 1 ≤ (A.filter (fun q => dot q v = 1)).card := by
          obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := (mem_verts_iff hnp).mp hv1
          rcases Finset.mem_insert.mp ha with rfl | haA
          · rcases Finset.mem_insert.mp hb with rfl | hbA
            · exact (hab rfl).elim
            · exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbA, hvb⟩⟩
          · exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨haA, hva⟩⟩
        omega
      dsimp [inc]
      rw [Finset.filter_insert, if_pos hvp, Finset.card_insert_of_notMem
        (fun h => hpA (Finset.mem_filter.mp h).1), hcardA]
    -- On old vertices v ∈ verts A: inc (insert p A) v = inc A v + (if dot p v = 1 then 1 else 0)
    have hold_inc : ∀ v ∈ verts A,
        inc (insert p A) v = inc A v + if dot p v = 1 then 1 else 0 := by
      intro v _
      dsimp [inc]
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun hm => hpA (Finset.mem_filter.mp hm).1)]
      · omega
    -- Split ∑ v ∈ verts (insert p A), inc (insert p A) v over verts A and verts (insert p A) \ verts A
    have hsum_split : (∑ v ∈ verts (insert p A), inc (insert p A) v) =
        (∑ v ∈ verts A, inc (insert p A) v) +
        (∑ v ∈ verts (insert p A) \ verts A, inc (insert p A) v) := by
      rw [add_comm, Finset.sum_sdiff hvsub]
    have hsum_old : (∑ v ∈ verts A, inc (insert p A) v) =
        (∑ v ∈ verts A, inc A v) + ((verts A).filter (fun v => dot p v = 1)).card := by
      rw [Finset.sum_congr rfl hold_inc, Finset.sum_add_distrib, Finset.card_filter]
    have hsum_new : (∑ v ∈ verts (insert p A) \ verts A, inc (insert p A) v) =
        2 * (verts (insert p A) \ verts A).card := by
      rw [Finset.sum_congr rfl hnew_inc, Finset.sum_const, smul_eq_mul, mul_comm]
    -- Partition lineVerts (insert p A) p into old (in verts A) and new (in verts \ verts A)
    have hlv_part : (lineVerts (insert p A) p).card =
        ((verts A).filter (fun v => dot p v = 1)).card + (verts (insert p A) \ verts A).card := by
      have hunion : lineVerts (insert p A) p =
          ((verts A).filter (fun v => dot p v = 1)) ∪ (verts (insert p A) \ verts A) := by
        ext v
        simp only [lineVerts, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨hv1, hvp⟩
          by_cases hvA : v ∈ verts A
          · exact Or.inl ⟨hvA, hvp⟩
          · exact Or.inr ⟨hv1, hvA⟩
        · rintro (⟨hvA, hvp⟩ | ⟨hv1, hvA⟩)
          · exact ⟨hvsub hvA, hvp⟩
          · exact ⟨hv1, (Finset.mem_filter.mp (hnew_on_p (Finset.mem_sdiff.mpr ⟨hv1, hvA⟩))).2⟩
      rw [hunion, Finset.card_union_of_disjoint]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact (Finset.mem_sdiff.mp hv2).2 (Finset.mem_filter.mp hv1).1
    have hcard_split : (verts (insert p A)).card =
        (verts A).card + (verts (insert p A) \ verts A).card := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card hvsub]
    omega

/-- Exact count of central regions: for `1 ≤ A.card`, `|centralRegions A| = 2 * |A|`. -/
lemma card_centralRegions (A : Finset Pt) (hnp : NonParallel A)
    (h0 : ∀ p ∈ A, p ≠ (0, 0)) (hne : 1 ≤ A.card) :
    (centralRegions A).card = 2 * A.card := by
  induction A using Finset.induction_on with
  | empty => simp at hne
  | @insert p A hpA ih =>
    have hp0 : p ≠ (0, 0) := h0 p (Finset.mem_insert_self _ _)
    by_cases hAempty : A = ∅
    · subst hAempty
      have hcard1 : (insert p (∅ : Finset Pt)).card = 1 := by simp
      rw [hcard1]
      have hall : centralRegions (insert p (∅ : Finset Pt)) = Finset.univ := by
        ext σ
        simp only [mem_centralRegions_iff, Finset.mem_univ, iff_true]
        let s : ℝ := if σ ⟨p, Finset.mem_insert_self p ∅⟩ then 1 else -1
        refine ⟨smulPt s p, fun q => ?_⟩
        have hqp : q = ⟨p, Finset.mem_insert_self p ∅⟩ :=
          Subtype.ext (Finset.mem_singleton.mp q.2)
        subst hqp
        rw [dot_smul]
        have hpp : dot p p = normSq p := rfl
        rw [hpp]
        have hns := normSq_pos_of_ne_zero hp0
        cases hb : σ ⟨p, Finset.mem_insert_self p ∅⟩ <;>
          simp only [s, hb, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
      rw [hall, Finset.card_univ]
      simp
    · have hAne : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
      have hnpA : NonParallel A := hnp.subset (Finset.subset_insert _ _)
      have h0A : ∀ q ∈ A, q ≠ (0, 0) := fun q hq => h0 q (Finset.mem_insert_of_mem hq)
      have hih := ih hnpA h0A hAne
      rw [Finset.card_insert_of_notMem hpA]
      -- Same fiber argument as card_regions_insert, except S₀ has exactly 2 elements:
      -- the sign vectors of +rot90 p and -rot90 p on A!
      let res : (↥(insert p A) → Bool) → (A → Bool) := fun σ q => σ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
      let S0 : Finset (A → Bool) :=
        Finset.univ.filter (fun τ => ∃ d : Pt, dot p d = 0 ∧ Realizes0 A τ d)
      have hmaps : (centralRegions (insert p A) : Set (↥(insert p A) → Bool)).MapsTo res (centralRegions A) := by
        intro σ hσ
        obtain ⟨d, hd⟩ := mem_centralRegions_iff.mp (Finset.mem_coe.mp hσ)
        exact Finset.mem_coe.mpr (mem_centralRegions_iff.mpr ⟨d, fun q => hd ⟨q.1, Finset.mem_insert_of_mem q.2⟩⟩)
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      -- Compute S0.card = 2 directly!
      have hdet_q : ∀ q : A, det2 p q.1 ≠ 0 := fun q =>
        hnp p (Finset.mem_insert_self _ _) q.1 (Finset.mem_insert_of_mem q.2) (fun h => hpA (h ▸ q.2))
      let τpos : A → Bool := fun q => decide (0 < det2 p q.1)
      let τneg : A → Bool := fun q => decide (0 < -det2 p q.1)
      have hτne : τpos ≠ τneg := by
        obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
        intro h
        have hq := congrFun h ⟨q0, hq0⟩
        have hd := hdet_q ⟨q0, hq0⟩
        rcases lt_or_gt_of_ne hd with hdn | hdp
        · dsimp only [τpos, τneg] at hq
          rw [decide_eq_false (not_lt.mpr hdn.le), decide_eq_true (neg_pos.mpr hdn)] at hq
          cases hq
        · dsimp only [τpos, τneg] at hq
          rw [decide_eq_true hdp, decide_eq_false (not_lt.mpr (neg_nonpos.mpr hdp.le))] at hq
          cases hq
      have hS0_eq : S0 = {τpos, τneg} := by
        ext τ
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨d, hdp, hdτ⟩
          -- Since dot p d = 0 and p ≠ 0, d = t * rot90 p for some t ≠ 0!
          have hns : 0 < normSq p := normSq_pos_of_ne_zero hp0
          let t := dot d (rot90 p) / normSq p
          have hdeq : d = smulPt t (rot90 p) := by
            dsimp [dot] at hdp
            dsimp [normSq] at hns
            apply Prod.ext <;> dsimp [t, smulPt, rot90, dot, normSq] <;>
              rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hns)]
            · linear_combination p.1 * hdp
            · linear_combination p.2 * hdp
          have htne : t ≠ 0 := by
            obtain ⟨q0, hq0⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
            intro ht0
            have hd0 : d = (0, 0) := by rw [hdeq, ht0]; simp [smulPt]
            have h0q : dot q0 d = 0 := by rw [hd0]; dsimp [dot]; ring
            exact signVal_ne_zero (hdτ ⟨q0, hq0⟩) h0q
          rcases lt_or_gt_of_ne htne with htn | htp
          · right
            funext q
            have hq := hdτ q
            rw [hdeq, dot_smul, dot_rot90] at hq
            have : t * det2 p q.1 = (-t) * (-det2 p q.1) := by ring
            rw [this] at hq
            have hq' := (signVal_mul_pos (by linarith : 0 < -t)).mp hq
            have := (signVal_iff (τ q) (-det2 p q.1)).mp hq'
            cases hb : τ q <;> simp [τneg, hb] at this ⊢
            · exact this.2
            · exact this.2
          · left
            funext q
            have hq := hdτ q
            rw [hdeq, dot_smul, dot_rot90] at hq
            have hq' := (signVal_mul_pos htp).mp hq
            have := (signVal_iff (τ q) (det2 p q.1)).mp hq'
            cases hb : τ q <;> simp [τpos, hb] at this ⊢
            · exact this.2
            · exact this.2
        · rintro (rfl | rfl)
          · refine ⟨rot90 p, dot_rot90_self p, fun q => ?_⟩
            rw [dot_rot90]
            exact (signVal_iff _ _).mpr ⟨hdet_q q, by simp [τpos]⟩
          · refine ⟨smulPt (-1) (rot90 p), by rw [dot_smul, dot_rot90_self, mul_zero], fun q => ?_⟩
            rw [dot_smul, dot_rot90, neg_one_mul]
            exact (signVal_iff _ _).mpr ⟨neg_ne_zero.mpr (hdet_q q), by simp [τneg]⟩
      have hS0_card : S0.card = 2 := by rw [hS0_eq, Finset.card_pair hτne]
      -- Perturbation & interpolation for centralRegions (exact linear analogue)
      have hfib : ∀ τ ∈ centralRegions A,
          ((centralRegions (insert p A)).filter (fun σ => res σ = τ)).card =
            if τ ∈ S0 then 2 else 1 := by
        intro τ hτ
        let extB : Bool → (↥(insert p A) → Bool) := fun b q =>
          if h : q.1 = p then b else τ ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left h⟩
        have hmem_fib : ∀ σ, σ ∈ (centralRegions (insert p A)).filter (fun σ => res σ = τ) ↔
            ∃ b : Bool, σ = extB b ∧ extB b ∈ centralRegions (insert p A) := by
          intro σ
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hσR, hσres⟩
            refine ⟨σ ⟨p, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
            · funext q
              by_cases hqp : q.1 = p
              · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
                subst hqeq; simp [extB]
              · simp only [extB, hqp, ↓reduceDIte]
                have := congrFun hσres ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
                simpa [res] using this
            · convert hσR using 1
              funext q
              by_cases hqp : q.1 = p
              · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
                subst hqeq; simp [extB]
              · simp only [extB, hqp, ↓reduceDIte]
                have := congrFun hσres ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
                simpa [res] using this.symm
          · rintro ⟨b, rfl, hb⟩
            refine ⟨hb, ?_⟩
            funext q
            have hqp : q.1 ≠ p := fun h => hpA (h ▸ q.2)
            simp [res, extB, hqp]
        have hcard_eq : ((centralRegions (insert p A)).filter (fun σ => res σ = τ)).card =
            (Finset.univ.filter (fun b : Bool => extB b ∈ centralRegions (insert p A))).card := by
          refine Finset.card_bij (fun σ _ => σ ⟨p, Finset.mem_insert_self _ _⟩) ?_ ?_ ?_
          · intro σ hσ
            obtain ⟨b, rfl, hb⟩ := (hmem_fib σ).mp hσ
            simpa [extB] using hb
          · intro σ₁ hσ₁ σ₂ hσ₂ heq
            obtain ⟨b₁, rfl, _⟩ := (hmem_fib σ₁).mp hσ₁
            obtain ⟨b₂, rfl, _⟩ := (hmem_fib σ₂).mp hσ₂
            simp only [extB, ↓reduceDIte] at heq; rw [heq]
          · intro b hb
            refine ⟨extB b, (hmem_fib _).mpr ⟨b, rfl, (Finset.mem_filter.mp hb).2⟩, by simp [extB]⟩
        rw [hcard_eq]
        by_cases hτS : τ ∈ S0
        · rw [if_pos hτS]
          obtain ⟨d, hdp, hdτ⟩ := (Finset.mem_filter.mp hτS).2
          have hboth : ∀ b : Bool, extB b ∈ centralRegions (insert p A) := by
            intro b
            have hns : 0 < normSq p := normSq_pos_of_ne_zero hp0
            let caps : Finset ℝ :=
              (A.attach.filter (fun q => dot q.1 p ≠ 0)).image (fun q => |dot q.1 d| / |dot q.1 p|)
            obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ caps, ε < r := by
              by_cases hne : caps.Nonempty
              · let m := caps.min' hne
                have hm_pos : 0 < m := by
                  obtain ⟨q, hq, hqm⟩ := Finset.mem_image.mp (Finset.min'_mem caps hne)
                  dsimp [m]; rw [← hqm]
                  exact div_pos (abs_pos.mpr (signVal_ne_zero (hdτ q)))
                    (abs_pos.mpr (Finset.mem_filter.mp hq).2)
                exact ⟨m / 2, by linarith, fun r hr => by linarith [Finset.min'_le caps r hr]⟩
              · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
            let s : ℝ := if b then ε else -ε
            rw [mem_centralRegions_iff]
            refine ⟨padd d (smulPt s p), fun q => ?_⟩
            by_cases hqp : q.1 = p
            · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
              subst hqeq
              simp only [extB, ↓reduceDIte]
              rw [dot_padd, hdp, zero_add, dot_smul]
              have hpp : dot p p = normSq p := rfl
              rw [hpp]
              cases b <;> simp only [s, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
            · simp only [extB, hqp, ↓reduceDIte]
              rw [dot_padd, dot_smul]
              let qA : A := ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
              have hq := hdτ qA
              by_cases hqp0 : dot q.1 p = 0
              · rw [hqp0, mul_zero, add_zero]; exact hq
              · have hmem : |dot q.1 d| / |dot q.1 p| ∈ caps :=
                  Finset.mem_image.mpr ⟨qA, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqp0⟩, rfl⟩
                have hlt : ε < |dot q.1 d| / |dot q.1 p| := hε_lt _ hmem
                have h1 : ε * |dot q.1 p| < |dot q.1 d| := (lt_div_iff₀ (abs_pos.mpr hqp0)).mp hlt
                have hs_abs : |s| = ε := by cases b <;> simp [s, abs_of_pos hε_pos]
                have h2 : |s * dot q.1 p| < |dot q.1 d| := by rw [abs_mul, hs_abs]; exact h1
                cases hb : τ qA <;> simp only [signVal, hb, ↓reduceIte, Bool.false_eq_true] at hq ⊢
                · rw [abs_of_neg hq] at h2; have := (abs_lt.mp h2).2; linarith
                · rw [abs_of_pos hq] at h2; have := (abs_lt.mp h2).1; linarith
          simp [hboth]
        · rw [if_neg hτS]
          obtain ⟨d, hdτ⟩ := mem_centralRegions_iff.mp hτ
          have hdp_ne : dot p d ≠ 0 := fun h => hτS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, h, hdτ⟩)
          have hex1 : ∃ b : Bool, extB b ∈ centralRegions (insert p A) := by
            refine ⟨decide (0 < dot p d), mem_centralRegions_iff.mpr ⟨d, fun q => ?_⟩⟩
            by_cases hqp : q.1 = p
            · have hqeq : q = ⟨p, Finset.mem_insert_self _ _⟩ := Subtype.ext hqp
              subst hqeq; simp only [extB, ↓reduceDIte]
              exact (signVal_iff _ _).mpr ⟨hdp_ne, by simp⟩
            · simp only [extB, hqp, ↓reduceDIte]
              exact hdτ ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left hqp⟩
          have hnotboth : ¬ (extB true ∈ centralRegions (insert p A) ∧
              extB false ∈ centralRegions (insert p A)) := by
            rintro ⟨ht, hf⟩
            obtain ⟨d₂, hd₂⟩ := mem_centralRegions_iff.mp ht
            obtain ⟨d₁, hd₁⟩ := mem_centralRegions_iff.mp hf
            have hp₂ : 0 < dot p d₂ := by
              simpa [extB, signVal] using hd₂ ⟨p, Finset.mem_insert_self _ _⟩
            have hp₁ : dot p d₁ < 0 := by
              simpa [extB, signVal] using hd₁ ⟨p, Finset.mem_insert_self _ _⟩
            let d0 := padd (smulPt (dot p d₂) d₁) (smulPt (-dot p d₁) d₂)
            have hdp0 : dot p d0 = 0 := by
              dsimp [d0]; rw [dot_padd, dot_smul, dot_smul]; ring
            refine hτS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, d0, hdp0, fun q => ?_⟩)
            dsimp [d0]; rw [dot_padd, dot_smul, dot_smul]
            have hqp : q.1 ≠ p := fun h => hpA (h ▸ q.2)
            have h1 : signVal (τ q) (dot q.1 d₁) := by
              simpa [extB, hqp] using hd₁ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
            have h2 : signVal (τ q) (dot q.1 d₂) := by
              simpa [extB, hqp] using hd₂ ⟨q.1, Finset.mem_insert_of_mem q.2⟩
            exact signVal_add ((signVal_mul_pos hp₂).mpr h1)
              ((signVal_mul_pos (by linarith : 0 < -dot p d₁)).mpr h2)
          obtain ⟨b, hb⟩ := hex1
          have hnb : extB (!b) ∉ centralRegions (insert p A) := by
            intro h; cases b <;> exact hnotboth (by simp_all)
          have hfilt_eq : Finset.univ.filter (fun c : Bool => extB c ∈ centralRegions (insert p A)) = {b} := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hc
              by_contra hcb
              have : c = !b := by cases b <;> cases c <;> simp_all
              exact hnb (this ▸ hc)
            · rintro rfl; exact hb
          rw [hfilt_eq, Finset.card_singleton]
      rw [Finset.sum_congr rfl hfib]
      have hSsub : S0 ⊆ centralRegions A := by
        intro τ hτ
        obtain ⟨d, _, hdτ⟩ := (Finset.mem_filter.mp hτ).2
        exact mem_centralRegions_iff.mpr ⟨d, hdτ⟩
      have hsum_ite : (∑ τ ∈ centralRegions A, if τ ∈ S0 then (2 : ℕ) else 1) =
          (centralRegions A).card + S0.card := by
        have hsplit : (∑ τ ∈ centralRegions A, if τ ∈ S0 then (2 : ℕ) else 1) =
            (∑ τ ∈ centralRegions A, 1) + (∑ τ ∈ centralRegions A, if τ ∈ S0 then 1 else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun τ _ => by split_ifs <;> rfl
        rw [hsplit, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter,
          Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSsub]
      rw [hsum_ite, hih, hS0_card]
      omega

/- ### Section 4: Double counting walls across all regions -/

lemma sum_walls_eq (A : Finset Pt) (hnp : NonParallel A) (h0 : ∀ p ∈ A, p ≠ (0, 0)) :
    (∑ σ ∈ regions A, (walls A σ).card) =
      2 * ((∑ v ∈ verts A, inc A v) + A.card) := by
  rw [double_count_inc, mul_add, Finset.mul_sum]
  -- Swap sum over σ ∈ regions A and p ∈ A.attach:
  have hswap : (∑ σ ∈ regions A, (walls A σ).card) =
      ∑ p ∈ A.attach, ((regions A).filter (fun σ => p ∈ walls A σ)).card := by
    have hl : ∀ σ ∈ regions A, (walls A σ).card =
        ∑ p ∈ A.attach, if p ∈ walls A σ then (1 : ℕ) else 0 := by
      intro σ _
      rw [← Finset.card_filter]
      congr 1; ext p; simp [Finset.mem_attach]
    rw [Finset.sum_congr rfl hl, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  rw [hswap]
  have hsumA : (∑ p ∈ A, 2 * (lineVerts A p).card) + 2 * A.card =
      ∑ p ∈ A.attach, 2 * ((lineVerts A p.1).card + 1) := by
    rw [Finset.sum_attach A (fun p => 2 * ((lineVerts A p).card + 1))]
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
    ring
  rw [hsumA]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- For fixed p ∈ A, let B = A.erase p. Then A = insert p.1 B.
  let B := A.erase p.1
  have hpB : p.1 ∉ B := Finset.notMem_erase p.1 A
  have hAB : insert p.1 B = A := Finset.insert_erase p.2
  have hnpB : NonParallel (insert p.1 B) := hAB.symm ▸ hnp
  let S : Finset (B → Bool) :=
    Finset.univ.filter (fun τ => ∃ x : Pt, dot p.1 x = 1 ∧ Realizes B τ x)
  have hScard : S.card = (lineVerts A p.1).card + 1 := by
    have := card_line_slices hpB hnpB (h0 p.1 p.2)
    simpa only [hAB] using this
  -- Bijection between (regions A).filter (p ∈ walls A σ) and S ×ˢ (Finset.univ : Finset Bool)!
  have hbij : ((regions A).filter (fun σ => p ∈ walls A σ)).card =
      (S ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij
      (fun σ _ => ((fun q : B => σ ⟨q.1, Finset.mem_of_mem_erase q.2⟩), σ p)) ?_ ?_ ?_
    · intro σ hσ
      have hpw := (Finset.mem_filter.mp hσ).2
      obtain ⟨x, hxp, hx⟩ := mem_walls_iff.mp hpw
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxp, fun q => ?_⟩,
        Finset.mem_univ _⟩
      have hne : (⟨q.1, Finset.mem_of_mem_erase q.2⟩ : A) ≠ p :=
        fun h => (Finset.ne_of_mem_erase q.2) (congrArg Subtype.val h)
      exact hx ⟨q.1, Finset.mem_of_mem_erase q.2⟩ hne
    · intro σ₁ _ σ₂ _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      funext q
      by_cases hqp : q = p
      · subst hqp; exact h2
      · have hqB : q.1 ∈ B := Finset.mem_erase.mpr ⟨fun h => hqp (Subtype.ext h), q.2⟩
        exact congrFun h1 ⟨q.1, hqB⟩
    · rintro ⟨τ, b⟩ htb
      have hτS := (Finset.mem_product.mp htb).1
      obtain ⟨x, hxp, hxτ⟩ := (Finset.mem_filter.mp hτS).2
      let σ : A → Bool := fun q =>
        if h : q = p then b else τ ⟨q.1, Finset.mem_erase.mpr ⟨fun he => h (Subtype.ext he), q.2⟩⟩
      have hσR : σ ∈ regions A := by
        obtain ⟨y, hyb, hyτ⟩ := perturb_off_line (h0 p.1 p.2) hxp hxτ b
        refine mem_regions_iff.mpr ⟨y, fun q => ?_⟩
        by_cases hqp : q = p
        · subst hqp; simpa [σ] using hyb
        · simp only [σ, hqp, ↓reduceDIte]
          exact hyτ ⟨q.1, Finset.mem_erase.mpr ⟨fun he => hqp (Subtype.ext he), q.2⟩⟩
      have hσW : p ∈ walls A σ := by
        refine mem_walls_iff.mpr ⟨x, hxp, fun q hqp => ?_⟩
        simp only [σ, hqp, ↓reduceDIte]
        exact hxτ ⟨q.1, Finset.mem_erase.mpr ⟨fun he => hqp (Subtype.ext he), q.2⟩⟩
      refine ⟨σ, Finset.mem_filter.mpr ⟨hσR, hσW⟩, ?_⟩
      apply Prod.ext
      · funext q
        have hne : (⟨q.1, Finset.mem_of_mem_erase q.2⟩ : A) ≠ p :=
          fun h => (Finset.ne_of_mem_erase q.2) (congrArg Subtype.val h)
        simp [σ, hne]
      · simp [σ]
  rw [hbij, Finset.card_product, hScard, Finset.card_univ, Fintype.card_bool, mul_comm]

/- ### Section 5: Convex Wall Lemma and wall-degree lower bounds -/

/-- Convex Wall Lemma: a point `y` satisfying the signs of `σ` on all walls of `σ`
automatically lies in the full region `R_σ`. -/
lemma mem_region_of_walls {A : Finset Pt} (hnp : NonParallel A) {σ : A → Bool}
    (hσ : σ ∈ regions A) {y : Pt}
    (hy : ∀ p ∈ walls A σ, signVal (σ p) (dot p.1 y - 1)) :
    Realizes A σ y := by
  by_contra hnot
  dsimp only [Realizes] at hnot
  push_neg at hnot
  obtain ⟨p₀, hp₀_fail⟩ := hnot
  obtain ⟨x, hx⟩ := mem_regions_iff.mp hσ
  have hxy : x ≠ y := fun h => hp₀_fail (h ▸ hx p₀)
  -- Move y slightly past p₀ if dot p₀ y = 1 so y strictly fails p₀,
  -- while staying strictly inside all walls of σ!
  obtain ⟨y₁, hy₁_walls, hy₁_fail⟩ : ∃ y₁ : Pt,
      (∀ p ∈ walls A σ, signVal (σ p) (dot p.1 y₁ - 1)) ∧
      signVal (!(σ p₀)) (dot p₀.1 y₁ - 1) := by
    by_cases h0 : dot p₀.1 y - 1 = 0
    · -- Perturb y along y - x by small ε > 0: since signVal (σ p₀) (dot p₀ x - 1),
      -- dot p₀ (y + ε (y - x)) - 1 = -ε (dot p₀ x - 1) has sign !(σ p₀)!
      let u := psub y x
      let caps : Finset ℝ :=
        ((walls A σ).filter (fun p => dot p.1 u ≠ 0)).image
          (fun p => |dot p.1 y - 1| / |dot p.1 u|)
      obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ caps, ε < r := by
        by_cases hne : caps.Nonempty
        · let m := caps.min' hne
          have hm_pos : 0 < m := by
            obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp (Finset.min'_mem caps hne)
            dsimp [m]; rw [← hpm]
            exact div_pos (abs_pos.mpr (signVal_ne_zero (hy p (Finset.mem_filter.mp hp).1)))
              (abs_pos.mpr (Finset.mem_filter.mp hp).2)
          exact ⟨m / 2, by linarith, fun r hr => by linarith [Finset.min'_le caps r hr]⟩
        · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
      refine ⟨padd y (smulPt ε u), ?_, ?_⟩
      · intro p hp
        rw [dot_padd, dot_smul]
        have hp_y := hy p hp
        by_cases hpu : dot p.1 u = 0
        · rw [hpu, mul_zero, add_zero]; exact hp_y
        · have hmem : |dot p.1 y - 1| / |dot p.1 u| ∈ caps :=
            Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpu⟩, rfl⟩
          have h1 : ε * |dot p.1 u| < |dot p.1 y - 1| :=
            (lt_div_iff₀ (abs_pos.mpr hpu)).mp (hε_lt _ hmem)
          have h2 : |ε * dot p.1 u| < |dot p.1 y - 1| := by
            rw [abs_mul, abs_of_pos hε_pos]; exact h1
          cases hb : σ p <;> simp only [signVal, hb, ↓reduceIte, Bool.false_eq_true] at hp_y ⊢
          · rw [abs_of_neg hp_y] at h2; have := (abs_lt.mp h2).2; linarith
          · rw [abs_of_pos hp_y] at h2; have := (abs_lt.mp h2).1; linarith
      · rw [dot_padd, dot_smul]
        have hu0 : dot p₀.1 u = -(dot p₀.1 x - 1) := by
          dsimp [u]; rw [dot_psub]; linarith
        have heq : dot p₀.1 y + ε * dot p₀.1 u - 1 = ε * (-(dot p₀.1 x - 1)) := by
          rw [hu0]; linarith
        rw [heq, signVal_mul_pos hε_pos, signVal_neg, neg_neg]
        exact hx p₀
    · refine ⟨y, hy, ?_⟩
      cases hb : σ p₀ <;> simp only [signVal, hb, ↓reduceIte, Bool.false_eq_true,
        Bool.not_false, Bool.not_true] at hp₀_fail ⊢
      · exact lt_of_le_of_ne (not_lt.mp hp₀_fail) (Ne.symm h0)
      · exact lt_of_le_of_ne (not_lt.mp hp₀_fail) h0
  have hxy₁ : x ≠ y₁ := fun h => by
    have h1 := hx p₀
    rw [h] at h1
    have := signVal_unique h1 hy₁_fail
    cases σ p₀ <;> simp at this
  -- Perturb y₁ to y' avoiding all lines through x and any vertex v ∈ verts A,
  -- while preserving all strict inequalities on walls A σ and !(σ p₀) on p₀!
  let G : Finset (Pt × ℝ) :=
    ((walls A σ).image (fun p => if σ p then (p.1, 1) else (smulPt (-1) p.1, -1))) ∪
    {if !(σ p₀) then (p₀.1, 1) else (smulPt (-1) p₀.1, -1)}
  have hG : ∀ g ∈ G, 0 < dot g.1 y₁ - g.2 := by
    intro g hg
    rcases Finset.mem_union.mp hg with hgW | hg0
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hgW
      have hpy := hy₁_walls p hp
      cases hb : σ p <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hpy ⊢
      · rw [dot_comm, dot_smul, dot_comm]; linarith
      · exact hpy
    · rw [Finset.mem_singleton.mp hg0]
      cases hb : σ p₀ <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true] at hy₁_fail ⊢
      · exact hy₁_fail
      · rw [dot_comm, dot_smul, dot_comm]; linarith
  obtain ⟨y', hy'G, hy'V⟩ := exists_perturb_avoid_pts x y₁ hxy₁ (verts A) G hG
  have hy'_walls : ∀ p ∈ walls A σ, signVal (σ p) (dot p.1 y' - 1) := by
    intro p hp
    have hmem : (if σ p then (p.1, 1) else (smulPt (-1) p.1, -1)) ∈ G :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have hpos := hy'G _ hmem
    cases hb : σ p <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hpos ⊢
    · rw [dot_comm, dot_smul, dot_comm] at hpos; linarith
    · exact hpos
  have hy'_fail : signVal (!(σ p₀)) (dot p₀.1 y' - 1) := by
    have hmem : (if !(σ p₀) then (p₀.1, 1) else (smulPt (-1) p₀.1, -1)) ∈ G :=
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hpos := hy'G _ hmem
    cases hb : σ p₀ <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true] at hpos ⊢
    · exact hpos
    · rw [dot_comm, dot_smul, dot_comm] at hpos; linarith
  -- Along the segment z(t) = (1 - t) x + t y' = x + t (y' - x):
  -- For any q : A, dot q (z t) - 1 = (dot q x - 1) + t * (dot q y' - dot q x).
  -- Crossing set C = { q : A | dot q y' - dot q x ≠ 0 ∧ 0 < t_q ∧ t_q ≤ 1 }
  let tCross : A → ℝ := fun q => (1 - dot q.1 x) / (dot q.1 y' - dot q.1 x)
  let C : Finset A := Finset.univ.filter (fun q => dot q.1 y' ≠ dot q.1 x ∧ 0 < tCross q ∧ tCross q ≤ 1)
  have hp₀C : p₀ ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hx0 := hx p₀
    have hy0 := hy'_fail
    cases hb : σ p₀ <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true] at hx0 hy0
    · refine ⟨by linarith, div_pos (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
    · refine ⟨by linarith, div_pos_of_neg_of_neg (by linarith) (by linarith), ?_⟩
      exact (div_le_iff_of_neg (by linarith)).mpr (by linarith)
  obtain ⟨qStar, hqStarC, hqStar_min⟩ := Finset.exists_min_image C tCross ⟨p₀, hp₀C⟩
  have hqStar_spec := (Finset.mem_filter.mp hqStarC).2
  set tStar := tCross qStar
  have htStar_pos : 0 < tStar := hqStar_spec.2.1
  have htStar_le1 : tStar ≤ 1 := hqStar_spec.2.2
  let z : Pt := padd x (smulPt tStar (psub y' x))
  have hz_on : dot qStar.1 z = 1 := by
    dsimp [z, tStar, tCross]
    rw [dot_padd, dot_smul, dot_psub]
    have hne : dot qStar.1 y' - dot qStar.1 x ≠ 0 := sub_ne_zero.mpr hqStar_spec.1
    field_simp [hne]; ring
  -- Show qStar ∈ walls A σ using z!
  have hqStar_wall : qStar ∈ walls A σ := by
    refine mem_walls_iff.mpr ⟨z, hz_on, fun q hqq => ?_⟩
    have hz_ne : dot q.1 z ≠ 1 := by
      intro hqz
      have hzV : z ∈ verts A := (mem_verts_iff hnp).mpr
        ⟨qStar.1, qStar.2, q.1, q.2, fun h => hqq (Subtype.ext h.symm), hz_on, hqz⟩
      have hzx : z ≠ x := fun h => by
        rw [h] at hz_on
        exact signVal_ne_zero (hx qStar) (sub_eq_zero.mpr hz_on)
      have hdet0 : det2 (psub y' x) (psub z x) = 0 := by
        dsimp [z, det2, psub, padd, smulPt]; ring
      exact hy'V z hzV hzx hdet0
    -- Since dot q z ≠ 1 and tStar ≤ tCross q (if q crosses), sign at z matches sign at x!
    by_contra hfail_q
    -- Then dot q z - 1 has opposite sign from dot q x - 1, so q crosses at some t' < tStar!
    have hqx := hx q
    have hdiff_ne : dot q.1 y' ≠ dot q.1 x := by
      intro heq
      have : dot q.1 z = dot q.1 x := by
        dsimp [z]; rw [dot_padd, dot_smul, dot_psub, heq, sub_self, mul_zero, add_zero]
      exact hfail_q (this ▸ hqx)
    have hqz_val : dot q.1 z - 1 = (dot q.1 x - 1) + tStar * (dot q.1 y' - dot q.1 x) := by
      dsimp [z]; rw [dot_padd, dot_smul, dot_psub]; ring
    have hq_in_C : q ∈ C ∧ tCross q < tStar := by
      cases hb : σ q <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hqx hfail_q
      · have hqz_pos : 0 < dot q.1 z - 1 := lt_of_le_of_ne (not_lt.mp hfail_q) (Ne.symm (sub_ne_zero.mpr hz_ne))
        have hslope_pos : 0 < dot q.1 y' - dot q.1 x := by nlinarith
        have hlt : tCross q < tStar := by
          dsimp [tCross]; rw [div_lt_iff₀ hslope_pos]; linarith
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_ne,
          div_pos (by linarith) hslope_pos, le_trans hlt.le htStar_le1⟩, hlt⟩
      · have hqz_neg : dot q.1 z - 1 < 0 := lt_of_le_of_ne (not_lt.mp hfail_q) (sub_ne_zero.mpr hz_ne)
        have hslope_neg : dot q.1 y' - dot q.1 x < 0 := by nlinarith
        have hlt : tCross q < tStar := by
          dsimp [tCross]; rw [div_lt_iff_of_neg hslope_neg]; linarith
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_ne,
          div_pos_of_neg_of_neg (by linarith) hslope_neg, le_trans hlt.le htStar_le1⟩, hlt⟩
    linarith [hqStar_min q hq_in_C.1]
  -- Contradiction! qStar ∈ walls A σ means x and y' have the SAME sign on qStar,
  -- so dot qStar z - 1 = (1 - tStar) (dot qStar x - 1) + tStar (dot qStar y' - 1) ≠ 0!
  have hsame_x := hx qStar
  have hsame_y := hy'_walls qStar hqStar_wall
  have hcomb : dot qStar.1 z - 1 =
      (1 - tStar) * (dot qStar.1 x - 1) + tStar * (dot qStar.1 y' - 1) := by
    dsimp [z]; rw [dot_padd, dot_smul, dot_psub]; ring
  rw [hz_on, sub_self] at hcomb
  rcases eq_or_lt_of_le htStar_le1 with h1 | hlt1
  · rw [h1, sub_self, zero_mul, zero_add, one_mul] at hcomb
    exact signVal_ne_zero hsame_y hcomb.symm
  · have hsum_sv := signVal_add ((signVal_mul_pos (by linarith : 0 < 1 - tStar)).mpr hsame_x)
      ((signVal_mul_pos htStar_pos).mpr hsame_y)
    exact signVal_ne_zero hsum_sv hcomb.symm

/-- Every region with at most 2 walls is a central (unbounded) region. -/
lemma central_of_walls_le_two {A : Finset Pt} (hnp : NonParallel A) (h0 : ∀ p ∈ A, p ≠ (0, 0))
    {σ : A → Bool} (hσ : σ ∈ regions A) (hle : (walls A σ).card ≤ 2) :
    σ ∈ centralRegions A := by
  obtain ⟨x, hx⟩ := mem_regions_iff.mp hσ
  -- Find a direction d such that: (1) ∀ p ∈ walls A σ, signVal (σ p) (dot p.1 d),
  -- and (2) ∀ p : A, dot p.1 d ≠ 0.
  -- Then for large t > 0, x + t d ∈ R_σ (by Convex Wall Lemma!), giving Realizes0 A σ d!
  have hex_d : ∃ d : Pt, (∀ p ∈ walls A σ, signVal (σ p) (dot p.1 d)) ∧
      ∀ p : A, dot p.1 d ≠ 0 := by
    have hcard_cases : (walls A σ).card = 0 ∨ (walls A σ).card = 1 ∨ (walls A σ).card = 2 := by omega
    rcases hcard_cases with h0w | h1w | h2w
    · have hempty : walls A σ = ∅ := Finset.card_eq_zero.mp h0w
      let F : Finset (ℝ × ℝ × ℝ) := A.image (fun p => (p.1, p.2, 0))
      have hF : ∀ f ∈ F, f.1 ≠ 0 ∨ f.2.1 ≠ 0 := by
        intro f hf
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
        by_contra h
        push_neg at h
        exact h0 p hp (Prod.ext h.1 h.2)
      obtain ⟨d, hd⟩ := exists_avoid_affine F hF
      refine ⟨d, by simp [hempty], fun p => ?_⟩
      exact hd (p.1.1, p.1.2, 0) (Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩)
    · obtain ⟨p₁, hp₁_eq⟩ := Finset.card_eq_one.mp h1w
      let d₀ := smulPt (if σ p₁ then 1 else -1) p₁.1
      have hd₀ : signVal (σ p₁) (dot p₁.1 d₀) := by
        dsimp [d₀]; rw [dot_smul]
        have hpp : dot p₁.1 p₁.1 = normSq p₁.1 := rfl
        rw [hpp]
        have hns := normSq_pos_of_ne_zero (h0 p₁.1 p₁.2)
        cases hb : σ p₁ <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
      -- Perturb d₀ along rot90 p₁.1 by small ε > 0 avoiding all dot q d = 0!
      let u := rot90 p₁.1
      let bad : Finset ℝ :=
        (A.attach.filter (fun q => dot q.1 u ≠ 0)).image (fun q => -(dot q.1 d₀) / dot q.1 u)
      obtain ⟨ε, hε_avoid⟩ : ∃ ε : ℝ, ε ∉ bad := by
        by_cases hne : bad.Nonempty
        · exact ⟨bad.max' hne + 1, fun h => by linarith [Finset.le_max' bad _ h]⟩
        · exact ⟨0, fun h => hne ⟨0, h⟩⟩
      let d := padd d₀ (smulPt ε u)
      refine ⟨d, ?_, ?_⟩
      · intro p hp
        rw [hp₁_eq, Finset.mem_singleton] at hp; rw [hp]
        dsimp only [d]; rw [dot_padd, dot_smul _ ε u]
        dsimp only [u]; rw [dot_rot90_self, mul_zero, add_zero]; exact hd₀
      · intro q hq0
        dsimp only [d] at hq0; rw [dot_padd, dot_smul _ ε u] at hq0
        by_cases hqu : dot q.1 u = 0
        · rw [hqu, mul_zero, add_zero] at hq0
          by_cases hqp : q = p₁
          · subst hqp; exact signVal_ne_zero hd₀ hq0
          · have hdet := hnp p₁.1 p₁.2 q.1 q.2 (fun h => hqp (Subtype.ext h.symm))
            dsimp only [u] at hqu; rw [dot_rot90] at hqu; exact hdet hqu
        · apply hε_avoid
          refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqu⟩, ?_⟩
          rw [div_eq_iff hqu]; linarith
    · obtain ⟨p₁, p₂, hp₁₂, hw_eq⟩ := Finset.card_eq_two.mp h2w
      have hdet : det2 p₁.1 p₂.1 ≠ 0 :=
        hnp p₁.1 p₁.2 p₂.1 p₂.2 (fun h => hp₁₂ (Subtype.ext h))
      let s₁ : ℝ := if σ p₁ then 1 else -1
      let s₂ : ℝ := if σ p₂ then 1 else -1
      let d₁ := solve2 p₁.1 p₂.1 s₁ s₂
      let u := solve2 p₁.1 p₂.1 1 0
      -- Perturb d₁ + ε u for ε ∈ (0, 1/2) avoiding all dot q (d₁ + ε u) = 0
      let bad : Finset ℝ :=
        (A.attach.filter (fun q => dot q.1 u ≠ 0)).image (fun q => -(dot q.1 d₁) / dot q.1 u)
      obtain ⟨ε, hε0, hε1, hε_avoid⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε ∉ bad := by
        let posBad := bad.filter (fun r => 0 < r)
        by_cases hpb : posBad.Nonempty
        · let m := min (1 / 2 : ℝ) (posBad.min' hpb)
          have hm_pos : 0 < m := lt_min (by norm_num) (Finset.mem_filter.mp (Finset.min'_mem posBad hpb)).2
          refine ⟨m / 2, by linarith, by linarith [min_le_left (1 / 2 : ℝ) (posBad.min' hpb)], ?_⟩
          intro hm
          have := Finset.min'_le posBad (m / 2) (Finset.mem_filter.mpr ⟨hm, by linarith⟩)
          have := min_le_right (1 / 2 : ℝ) (posBad.min' hpb)
          linarith
        · refine ⟨1 / 4, by norm_num, by norm_num, fun hm => hpb ⟨1 / 4, Finset.mem_filter.mpr ⟨hm, by norm_num⟩⟩⟩
      let d := padd d₁ (smulPt ε u)
      refine ⟨d, ?_, ?_⟩
      · intro p hp
        rw [hw_eq, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with hp | hp
        · rw [hp]; dsimp only [d, d₁, u]; rw [dot_padd, dot_smul, dot_solve2_left hdet, dot_solve2_left hdet]
          cases hb : σ p₁ <;> simp only [s₁, hb, signVal, ↓reduceIte, Bool.false_eq_true] <;> linarith
        · rw [hp]; dsimp only [d, d₁, u]; rw [dot_padd, dot_smul, dot_solve2_right hdet, dot_solve2_right hdet]
          cases hb : σ p₂ <;> simp only [s₂, hb, signVal, ↓reduceIte, Bool.false_eq_true] <;> linarith
      · intro q hq0
        dsimp only [d] at hq0; rw [dot_padd, dot_smul] at hq0
        by_cases hqu : dot q.1 u = 0
        · rw [hqu, mul_zero, add_zero] at hq0
          -- dot q u = 0 and dot q d₁ = 0 with u, d₁ linearly independent => q = 0, contradiction!
          have hdu : det2 d₁ u ≠ 0 := by
            have hs₂ : s₂ ≠ 0 := by dsimp only [s₂]; cases σ p₂ <;> norm_num
            have hmul : det2 p₁.1 p₂.1 * det2 d₁ u = -s₂ := by
              have hident : det2 p₁.1 p₂.1 * det2 d₁ u =
                  dot p₁.1 d₁ * dot p₂.1 u - dot p₁.1 u * dot p₂.1 d₁ := by
                dsimp [det2, dot]; ring
              rw [hident]
              dsimp only [d₁, u]
              rw [dot_solve2_left hdet, dot_solve2_right hdet, dot_solve2_left hdet, dot_solve2_right hdet]
              ring
            intro h0du
            rw [h0du, mul_zero] at hmul
            exact hs₂ (by linarith)
          have hqzero : q.1 = (0, 0) := by
            apply Prod.ext <;> dsimp [dot, det2] at hq0 hqu hdu
            · have : q.1.1 * (d₁.1 * u.2 - d₁.2 * u.1) = 0 := by linear_combination u.2 * hq0 - d₁.2 * hqu
              exact (mul_eq_zero.mp this).resolve_right hdu
            · have : q.1.2 * (d₁.1 * u.2 - d₁.2 * u.1) = 0 := by linear_combination d₁.1 * hqu - u.1 * hq0
              exact (mul_eq_zero.mp this).resolve_right hdu
          exact h0 q.1 q.2 hqzero
        · apply hε_avoid
          refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqu⟩, ?_⟩
          field_simp [hqu]; linarith
  obtain ⟨d, hd_walls, hd_ne⟩ := hex_d
  rw [mem_centralRegions_iff]
  refine ⟨d, fun p => ?_⟩
  -- For sufficiently large t > 0, x + t d lies in R_σ (since it satisfies all walls of σ!)
  let t : ℝ := |dot p.1 x - 1| / |dot p.1 d| + 1
  have ht_pos : 0 < t := by positivity
  have hxt : Realizes A σ (padd x (smulPt t d)) := by
    apply mem_region_of_walls hnp hσ
    intro q hq
    rw [dot_padd, dot_smul]
    have h1 : dot q.1 x + t * dot q.1 d - 1 = (dot q.1 x - 1) + t * dot q.1 d := by ring
    rw [h1]
    exact signVal_add (hx q) ((signVal_mul_pos ht_pos).mpr (hd_walls q hq))
  have hp_xt := hxt p
  rw [dot_padd, dot_smul] at hp_xt
  have habs_pd : 0 < |dot p.1 d| := abs_pos.mpr (hd_ne p)
  have hdom : |dot p.1 x - 1| < t * |dot p.1 d| := by
    dsimp [t]
    have : (|dot p.1 x - 1| / |dot p.1 d| + 1) * |dot p.1 d| = |dot p.1 x - 1| + |dot p.1 d| := by
      field_simp [ne_of_gt habs_pd]
    linarith
  cases hb : σ p <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hp_xt ⊢
  · by_contra hge
    have hpos : 0 < dot p.1 d := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm (hd_ne p))
    rw [abs_of_pos hpos] at hdom
    have := (abs_lt.mp hdom).1; linarith
  · by_contra hle
    have hneg : dot p.1 d < 0 := lt_of_le_of_ne (not_lt.mp hle) (hd_ne p)
    rw [abs_of_neg hneg] at hdom
    have := (abs_lt.mp hdom).2; linarith

/-- Every region of an arrangement with `3 ≤ A.card` pairwise non-parallel lines has at least 2 walls. -/
lemma two_le_walls {A : Finset Pt} (hnp : NonParallel A) (hcard : 3 ≤ A.card)
    {σ : A → Bool} (hσ : σ ∈ regions A) :
    2 ≤ (walls A σ).card := by
  by_contra hlt
  have hle1 : (walls A σ).card ≤ 1 := by omega
  obtain ⟨x, hx⟩ := mem_regions_iff.mp hσ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0w | h1w
  · have hempty : walls A σ = ∅ := Finset.card_eq_zero.mp h0w
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have h0p : p₀ ≠ (0, 0) := hnp.ne_zero (by omega) hp₀
    let d := smulPt (if σ ⟨p₀, hp₀⟩ then -1 else 1) p₀
    -- x + t d satisfies all walls (vacuously) so is in R_σ for all t > 0, contradicting sign on p₀!
    let t := (|dot p₀ x - 1| + 1) / normSq p₀
    have hns := normSq_pos_of_ne_zero h0p
    have hxt := mem_region_of_walls hnp hσ (y := padd x (smulPt t d)) (by simp [hempty]) ⟨p₀, hp₀⟩
    rw [dot_padd, dot_smul] at hxt
    have hpp : dot p₀ p₀ = normSq p₀ := rfl
    have hdp : dot p₀ d = (if σ ⟨p₀, hp₀⟩ then -1 else 1) * normSq p₀ := by
      dsimp [d]; rw [dot_smul, hpp]
    rw [hdp] at hxt
    have hmul : t * normSq p₀ = |dot p₀ x - 1| + 1 := by
      dsimp [t]; field_simp [ne_of_gt hns]
    cases hb : σ ⟨p₀, hp₀⟩ <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hxt
    · have := le_abs_self (dot p₀ x - 1); have := neg_le_abs (dot p₀ x - 1); nlinarith
    · have := le_abs_self (dot p₀ x - 1); have := neg_le_abs (dot p₀ x - 1); nlinarith
  · obtain ⟨p₁, hp₁_eq⟩ := Finset.card_eq_one.mp h1w
    -- Pick p₂ ≠ p₁ in A; move along ±rot90 p₁.1 (keeps dot p₁ constant, changes dot p₂ arbitrarily!)
    obtain ⟨p₂, hp₂, hp₁₂⟩ : ∃ p₂ ∈ A, p₂ ≠ p₁.1 := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      by_cases h : a = p₁.1
      · exact ⟨b, hb, fun hb1 => hab (h.trans hb1.symm)⟩
      · exact ⟨a, ha, h⟩
    have hdet : det2 p₁.1 p₂ ≠ 0 := hnp p₁.1 p₁.2 p₂ hp₂ hp₁₂.symm
    let u := rot90 p₁.1
    have hqu : dot p₂ u = det2 p₁.1 p₂ := dot_rot90 p₂ p₁.1
    let t := (if σ ⟨p₂, hp₂⟩ then -1 else 1) * (|dot p₂ x - 1| + 1) / det2 p₁.1 p₂
    have hxt := mem_region_of_walls hnp hσ (y := padd x (smulPt t u)) (by
      intro q hq
      rw [hp₁_eq, Finset.mem_singleton] at hq; rw [hq]
      rw [dot_padd, dot_smul, dot_rot90_self, mul_zero, add_zero]
      exact hx p₁) ⟨p₂, hp₂⟩
    rw [dot_padd, dot_smul, hqu] at hxt
    have hmul : t * det2 p₁.1 p₂ = (if σ ⟨p₂, hp₂⟩ then -1 else 1) * (|dot p₂ x - 1| + 1) := by
      dsimp [t]; field_simp [hdet]
    rw [hmul] at hxt
    cases hb : σ ⟨p₂, hp₂⟩ <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hxt
    · have := neg_le_abs (dot p₂ x - 1); linarith
    · have := le_abs_self (dot p₂ x - 1); linarith

/-- Antipodal unbounded wall-sum bound: if not all lines of `A` are concurrent,
every antipodal pair `{σ, ¬σ}` in `centralRegions A` has `|walls σ| + |walls (¬σ)| ≥ 5`. -/
lemma five_le_walls_add_neg {A : Finset Pt} (hnp : NonParallel A) (hcard : 3 ≤ A.card)
    (hnc : ∀ v : Pt, (A.filter (fun p => dot p v = 1)).card < A.card)
    {σ : A → Bool} (hσ : σ ∈ centralRegions A) :
    5 ≤ (walls A σ).card + (walls A (fun p => !(σ p))).card := by
  let σ' : A → Bool := fun p => !(σ p)
  have hσR : σ ∈ regions A := centralRegions_subset_regions A hσ
  have hσ'C : σ' ∈ centralRegions A := by
    obtain ⟨d, hd⟩ := mem_centralRegions_iff.mp hσ
    refine mem_centralRegions_iff.mpr ⟨smulPt (-1) d, fun p => ?_⟩
    rw [dot_smul, neg_one_mul]
    exact (signVal_neg (σ p) (-dot p.1 d)).mpr (by rw [neg_neg]; exact hd p)
  have hσ'R : σ' ∈ regions A := centralRegions_subset_regions A hσ'C
  have hw1 : 2 ≤ (walls A σ).card := two_le_walls hnp hcard hσR
  have hw2 : 2 ≤ (walls A σ').card := two_le_walls hnp hcard hσ'R
  by_contra hlt
  have hcard1 : (walls A σ).card = 2 := by dsimp only [σ'] at hw2; omega
  have hcard2 : (walls A σ').card = 2 := by dsimp only [σ'] at hw2 ⊢; omega
  obtain ⟨p₁, p₂, hp₁₂, hw1_eq⟩ := Finset.card_eq_two.mp hcard1
  have hdet : det2 p₁.1 p₂.1 ≠ 0 := hnp p₁.1 p₁.2 p₂.1 p₂.2 (fun h => hp₁₂ (Subtype.ext h))
  let v₀ := interPt p₁.1 p₂.1
  have hv₁ : dot p₁.1 v₀ = 1 := dot_interPt_left hdet
  have hv₂ : dot p₂.1 v₀ = 1 := dot_interPt_right hdet
  -- Step A: Show {p₁, p₂} ⊆ walls A σ', hence walls A σ' = {p₁, p₂}!
  let s₁ : ℝ := if σ p₁ then 1 else -1
  let s₂ : ℝ := if σ p₂ then 1 else -1
  let w₁ := solve2 p₁.1 p₂.1 0 s₂
  let w₂ := solve2 p₁.1 p₂.1 s₁ 0
  -- For any a > 0, b > 0, v₀ + a w₁ + b w₂ lies in R_σ (satisfies walls {p₁, p₂})!
  have hcone_in_R : ∀ a b : ℝ, 0 < a → 0 < b →
      Realizes A σ (padd v₀ (padd (smulPt a w₁) (smulPt b w₂))) := by
    intro a b ha hb
    apply mem_region_of_walls hnp hσR
    intro q hq
    rw [hw1_eq, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq
    · rw [hq, dot_padd, hv₁, dot_padd, dot_smul, dot_smul]
      dsimp only [w₁, w₂]; rw [dot_solve2_left hdet, dot_solve2_left hdet]
      cases h : σ p₁ <;> simp only [s₁, h, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
    · rw [hq, dot_padd, hv₂, dot_padd, dot_smul, dot_smul]
      dsimp only [w₁, w₂]; rw [dot_solve2_right hdet, dot_solve2_right hdet]
      cases h : σ p₂ <;> simp only [s₂, h, signVal, ↓reduceIte, Bool.false_eq_true] <;> nlinarith
  -- Deduce: for every q ≠ p₁, signVal (σ q) (dot q.1 w₁) holds!
  have hw₁_pos : ∀ q : A, q ≠ p₁ → signVal (σ q) (dot q.1 w₁) := by
    intro q hqp₁
    have hqw₁_ne : dot q.1 w₁ ≠ 0 := by
      intro h0
      have hw₁_p₁ : dot p₁.1 w₁ = 0 := dot_solve2_left hdet 0 s₂
      have hw₁_ne0 : w₁ ≠ (0, 0) := by
        intro hw0
        have : dot p₂.1 w₁ = 0 := by rw [hw0]; dsimp [dot]; ring
        rw [dot_solve2_right hdet] at this
        dsimp only [s₂] at this; split_ifs at this <;> norm_num at this
      have hdet_qp₁ : det2 p₁.1 q.1 ≠ 0 := hnp p₁.1 p₁.2 q.1 q.2 (fun h => hqp₁ (Subtype.ext h.symm))
      have : w₁ = (0, 0) := by
        apply Prod.ext <;> dsimp [dot, det2] at hw₁_p₁ h0 hdet_qp₁
        · have : w₁.1 * (p₁.1.1 * q.1.2 - p₁.1.2 * q.1.1) = 0 := by linear_combination q.1.2 * hw₁_p₁ - p₁.1.2 * h0
          exact (mul_eq_zero.mp this).resolve_right hdet_qp₁
        · have : w₁.2 * (p₁.1.1 * q.1.2 - p₁.1.2 * q.1.1) = 0 := by linear_combination p₁.1.1 * h0 - q.1.1 * hw₁_p₁
          exact (mul_eq_zero.mp this).resolve_right hdet_qp₁
      exact hw₁_ne0 this
    -- Take a huge and b = 1 in hcone_in_R!
    let a := (|dot q.1 v₀ - 1| + |dot q.1 w₂| + 1) / |dot q.1 w₁|
    have ha : 0 < a := div_pos (by positivity) (abs_pos.mpr hqw₁_ne)
    have hqR := hcone_in_R a 1 ha (by norm_num) q
    rw [dot_padd, dot_padd, dot_smul, dot_smul, one_mul] at hqR
    have hdom : a * |dot q.1 w₁| = |dot q.1 v₀ - 1| + |dot q.1 w₂| + 1 := by
      dsimp [a]; field_simp [ne_of_gt (abs_pos.mpr hqw₁_ne)]
    cases hb : σ q <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hqR ⊢
    · by_contra hge
      have hpos : 0 < dot q.1 w₁ := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hqw₁_ne)
      rw [abs_of_pos hpos] at hdom
      have := neg_le_abs (dot q.1 v₀ - 1); have := neg_le_abs (dot q.1 w₂); linarith
    · by_contra hle
      have hneg : dot q.1 w₁ < 0 := lt_of_le_of_ne (not_lt.mp hle) hqw₁_ne
      rw [abs_of_neg hneg] at hdom
      have := le_abs_self (dot q.1 v₀ - 1); have := le_abs_self (dot q.1 w₂); linarith
  -- Symmetrically, for every q ≠ p₂, signVal (σ q) (dot q.1 w₂) holds!
  have hw₂_pos : ∀ q : A, q ≠ p₂ → signVal (σ q) (dot q.1 w₂) := by
    intro q hqp₂
    have hqw₂_ne : dot q.1 w₂ ≠ 0 := by
      intro h0
      have hw₂_p₂ : dot p₂.1 w₂ = 0 := dot_solve2_right hdet s₁ 0
      have hw₂_ne0 : w₂ ≠ (0, 0) := by
        intro hw0
        have : dot p₁.1 w₂ = 0 := by rw [hw0]; dsimp [dot]; ring
        rw [dot_solve2_left hdet] at this
        dsimp only [s₁] at this; split_ifs at this <;> norm_num at this
      have hdet_qp₂ : det2 p₂.1 q.1 ≠ 0 := hnp p₂.1 p₂.2 q.1 q.2 (fun h => hqp₂ (Subtype.ext h.symm))
      have : w₂ = (0, 0) := by
        apply Prod.ext <;> dsimp [dot, det2] at hw₂_p₂ h0 hdet_qp₂
        · have : w₂.1 * (p₂.1.1 * q.1.2 - p₂.1.2 * q.1.1) = 0 := by linear_combination q.1.2 * hw₂_p₂ - p₂.1.2 * h0
          exact (mul_eq_zero.mp this).resolve_right hdet_qp₂
        · have : w₂.2 * (p₂.1.1 * q.1.2 - p₂.1.2 * q.1.1) = 0 := by linear_combination p₂.1.1 * h0 - q.1.1 * hw₂_p₂
          exact (mul_eq_zero.mp this).resolve_right hdet_qp₂
      exact hw₂_ne0 this
    let b := (|dot q.1 v₀ - 1| + |dot q.1 w₁| + 1) / |dot q.1 w₂|
    have hb_pos : 0 < b := div_pos (by positivity) (abs_pos.mpr hqw₂_ne)
    have hqR := hcone_in_R 1 b (by norm_num) hb_pos q
    rw [dot_padd, dot_padd, dot_smul, dot_smul, one_mul] at hqR
    have hdom : b * |dot q.1 w₂| = |dot q.1 v₀ - 1| + |dot q.1 w₁| + 1 := by
      dsimp [b]; field_simp [ne_of_gt (abs_pos.mpr hqw₂_ne)]
    cases hb : σ q <;> simp only [hb, signVal, ↓reduceIte, Bool.false_eq_true] at hqR ⊢
    · by_contra hge
      have hpos : 0 < dot q.1 w₂ := lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hqw₂_ne)
      rw [abs_of_pos hpos] at hdom
      have := neg_le_abs (dot q.1 v₀ - 1); have := neg_le_abs (dot q.1 w₁); linarith
    · by_contra hle
      have hneg : dot q.1 w₂ < 0 := lt_of_le_of_ne (not_lt.mp hle) hqw₂_ne
      rw [abs_of_neg hneg] at hdom
      have := le_abs_self (dot q.1 v₀ - 1); have := le_abs_self (dot q.1 w₁); linarith
  -- Now exhibit v₀ - t w₁ ∈ Λ_{p₁} witnessing p₁ ∈ walls A σ', and v₀ - t w₂ witnessing p₂ ∈ walls A σ'!
  have hp₁_in_w2 : p₁ ∈ walls A σ' := by
    let caps : Finset ℝ :=
      (A.attach.filter (fun q => q ≠ p₁)).image (fun q => |dot q.1 v₀ - 1| / |dot q.1 w₁|)
    obtain ⟨T, hT_pos, hT⟩ : ∃ T : ℝ, 0 < T ∧ ∀ r ∈ caps, r < T := by
      by_cases hne : caps.Nonempty
      · exact ⟨max 1 (caps.max' hne + 1), by linarith [le_max_left 1 (caps.max' hne + 1)],
          fun r hr => lt_of_lt_of_le (by linarith [Finset.le_max' caps r hr]) (le_max_right _ _)⟩
      · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
    refine mem_walls_iff.mpr ⟨padd v₀ (smulPt (-T) w₁), ?_, ?_⟩
    · rw [dot_padd, hv₁, dot_smul]; dsimp [w₁]; rw [dot_solve2_left hdet]; ring
    · intro q hqp₁
      rw [dot_padd, dot_smul]
      have hqw := hw₁_pos q hqp₁
      have hne : dot q.1 w₁ ≠ 0 := signVal_ne_zero hqw
      have hmem : |dot q.1 v₀ - 1| / |dot q.1 w₁| ∈ caps :=
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqp₁⟩, rfl⟩
      have hdom : |dot q.1 v₀ - 1| < T * |dot q.1 w₁| := by
        have := (div_lt_iff₀ (abs_pos.mpr hne)).mp (hT _ hmem); linarith
      dsimp [σ']
      cases hb : σ q <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true] at hqw ⊢
      · rw [abs_of_neg hqw] at hdom; have := neg_le_abs (dot q.1 v₀ - 1); linarith
      · rw [abs_of_pos hqw] at hdom; have := le_abs_self (dot q.1 v₀ - 1); linarith
  have hp₂_in_w2 : p₂ ∈ walls A σ' := by
    let caps : Finset ℝ :=
      (A.attach.filter (fun q => q ≠ p₂)).image (fun q => |dot q.1 v₀ - 1| / |dot q.1 w₂|)
    obtain ⟨T, hT_pos, hT⟩ : ∃ T : ℝ, 0 < T ∧ ∀ r ∈ caps, r < T := by
      by_cases hne : caps.Nonempty
      · exact ⟨max 1 (caps.max' hne + 1), by linarith [le_max_left 1 (caps.max' hne + 1)],
          fun r hr => lt_of_lt_of_le (by linarith [Finset.le_max' caps r hr]) (le_max_right _ _)⟩
      · exact ⟨1, by norm_num, fun r hr => (hne ⟨r, hr⟩).elim⟩
    refine mem_walls_iff.mpr ⟨padd v₀ (smulPt (-T) w₂), ?_, ?_⟩
    · rw [dot_padd, hv₂, dot_smul]; dsimp [w₂]; rw [dot_solve2_right hdet]; ring
    · intro q hqp₂
      rw [dot_padd, dot_smul]
      have hqw := hw₂_pos q hqp₂
      have hne : dot q.1 w₂ ≠ 0 := signVal_ne_zero hqw
      have hmem : |dot q.1 v₀ - 1| / |dot q.1 w₂| ∈ caps :=
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hqp₂⟩, rfl⟩
      have hdom : |dot q.1 v₀ - 1| < T * |dot q.1 w₂| := by
        have := (div_lt_iff₀ (abs_pos.mpr hne)).mp (hT _ hmem); linarith
      dsimp [σ']
      cases hb : σ q <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true] at hqw ⊢
      · rw [abs_of_neg hqw] at hdom; have := neg_le_abs (dot q.1 v₀ - 1); linarith
      · rw [abs_of_pos hqw] at hdom; have := le_abs_self (dot q.1 v₀ - 1); linarith
  have hw2_eq : walls A σ' = {p₁, p₂} := by
    have hsub : ({p₁, p₂} : Finset A) ⊆ walls A σ' := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq2
      · exact hp₁_in_w2
      · rw [Finset.mem_singleton.mp hq2]; exact hp₂_in_w2
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hp₁₂])).symm
  -- Step B: Pick q₃ ∈ A NOT passing through v₀ (exists by hnc v₀), and derive contradiction from v₀ ± t w!
  obtain ⟨q₃, hq₃A, hq₃_ne⟩ : ∃ q₃ ∈ A, dot q₃ v₀ ≠ 1 := by
    by_contra hall
    push_neg at hall
    have hfilt : A.filter (fun p => dot p v₀ = 1) = A := Finset.filter_true_of_mem hall
    have hlt := hnc v₀
    rw [hfilt] at hlt
    omega
  let w := padd w₁ w₂
  let t : ℝ := |dot q₃ v₀ - 1| / (|dot q₃ w| + 1)
  have ht_pos : 0 < t := div_pos (abs_pos.mpr (sub_ne_zero.mpr hq₃_ne)) (by positivity)
  have ht_small : t * |dot q₃ w| < |dot q₃ v₀ - 1| := by
    dsimp [t]
    have hden : 0 < |dot q₃ w| + 1 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    have habs : 0 < |dot q₃ v₀ - 1| := abs_pos.mpr (sub_ne_zero.mpr hq₃_ne)
    nlinarith
  -- v₀ + t w ∈ R_σ and v₀ - t w ∈ R_{σ'}!
  have hplus : Realizes A σ (padd v₀ (smulPt t w)) := by
    have heq : padd v₀ (smulPt t w) = padd v₀ (padd (smulPt t w₁) (smulPt t w₂)) := by
      apply Prod.ext <;> dsimp [w, padd, smulPt] <;> ring
    rw [heq]; exact hcone_in_R t t ht_pos ht_pos
  have hminus : Realizes A σ' (padd v₀ (smulPt (-t) w)) := by
    apply mem_region_of_walls hnp hσ'R
    intro q hq
    rw [hw2_eq, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq
    · rw [hq, dot_padd, hv₁, dot_smul]; dsimp only [w]; rw [dot_padd]
      dsimp only [w₁, w₂]; rw [dot_solve2_left hdet, dot_solve2_left hdet]
      dsimp only [σ']
      cases h : σ p₁ <;> simp only [s₁, h, signVal, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true] <;> nlinarith
    · rw [hq, dot_padd, hv₂, dot_smul]; dsimp only [w]; rw [dot_padd]
      dsimp only [w₁, w₂]; rw [dot_solve2_right hdet, dot_solve2_right hdet]
      dsimp only [σ']
      cases h : σ p₂ <;> simp only [s₂, h, signVal, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true] <;> nlinarith
  have hp3 := hplus ⟨q₃, hq₃A⟩
  have hm3 := hminus ⟨q₃, hq₃A⟩
  rw [dot_padd, dot_smul] at hp3 hm3
  have hbd : |t * dot q₃ w| < |dot q₃ v₀ - 1| := by rw [abs_mul, abs_of_pos ht_pos]; exact ht_small
  have hbd1 := (abs_lt.mp hbd).1
  have hbd2 := (abs_lt.mp hbd).2
  dsimp [σ'] at hm3
  cases hb : σ ⟨q₃, hq₃A⟩ <;> simp only [hb, signVal, Bool.not_false, Bool.not_true,
    ↓reduceIte, Bool.false_eq_true] at hp3 hm3
  · rcases lt_or_gt_of_ne (sub_ne_zero.mpr hq₃_ne) with hlt | hgt
    · rw [abs_of_neg hlt] at hbd1 hbd2; linarith
    · rw [abs_of_pos hgt] at hbd1 hbd2; linarith
  · rcases lt_or_gt_of_ne (sub_ne_zero.mpr hq₃_ne) with hlt | hgt
    · rw [abs_of_neg hlt] at hbd1 hbd2; linarith
    · rw [abs_of_pos hgt] at hbd1 hbd2; linarith

/- ### Section 6: Melchior's inequality for line arrangements and polar duality bridge -/

theorem melchior_arrangement (A : Finset Pt) (hnp : NonParallel A) (hcard : 3 ≤ A.card)
    (hnc : ∀ v : Pt, (A.filter (fun p => dot p v = 1)).card < A.card) :
    (∑ v ∈ verts A, inc A v) + 3 ≤ 3 * (verts A).card := by
  have h0 : ∀ p ∈ A, p ≠ (0, 0) := fun p hp => hnp.ne_zero (by omega) hp
  have heuler := euler_regions A hnp h0
  have hcent_card := card_centralRegions A hnp h0 (by omega)
  have hcent_sub : centralRegions A ⊆ regions A := centralRegions_subset_regions A
  have hsum_walls := sum_walls_eq A hnp h0
  -- Split ∑_{σ ∈ regions A} (walls A σ).card into (regions \ central) + central
  have hsplit : (∑ σ ∈ regions A, (walls A σ).card) =
      (∑ σ ∈ regions A \ centralRegions A, (walls A σ).card) +
      (∑ σ ∈ centralRegions A, (walls A σ).card) := by
    rw [Finset.sum_sdiff hcent_sub]
  -- Bound 1: on regions A \ centralRegions A, every σ has (walls A σ).card ≥ 3
  have hb1 : 3 * (regions A \ centralRegions A).card ≤
      ∑ σ ∈ regions A \ centralRegions A, (walls A σ).card := by
    have hconst : (∑ _σ ∈ regions A \ centralRegions A, (3 : ℕ)) =
        3 * (regions A \ centralRegions A).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hconst]
    refine Finset.sum_le_sum fun σ hσ => ?_
    obtain ⟨hσR, hσnotC⟩ := Finset.mem_sdiff.mp hσ
    by_contra hlt
    exact hσnotC (central_of_walls_le_two hnp h0 hσR (by omega))
  -- Bound 2: on centralRegions A, pair σ with ¬σ to get 2 * ∑ ≥ 5 * |centralRegions A|
  have hb2 : 5 * (centralRegions A).card ≤ 2 * ∑ σ ∈ centralRegions A, (walls A σ).card := by
    have hneg_sum : (∑ σ ∈ centralRegions A, (walls A (fun p => !(σ p))).card) =
        ∑ σ ∈ centralRegions A, (walls A σ).card := by
      refine Finset.sum_bij (fun σ _ => fun p => !(σ p)) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro σ hσ
        obtain ⟨d, hd⟩ := mem_centralRegions_iff.mp hσ
        refine mem_centralRegions_iff.mpr ⟨smulPt (-1) d, fun p => ?_⟩
        rw [dot_smul, neg_one_mul]
        exact (signVal_neg (σ p) (-dot p.1 d)).mpr (by rw [neg_neg]; exact hd p)
      · intro σ₁ _ σ₂ _ h
        funext p
        have := congrFun h p
        cases h1 : σ₁ p <;> cases h2 : σ₂ p <;> simp_all
      · intro σ hσ
        refine ⟨fun p => !(σ p), ?_, by funext p; simp⟩
        obtain ⟨d, hd⟩ := mem_centralRegions_iff.mp hσ
        refine mem_centralRegions_iff.mpr ⟨smulPt (-1) d, fun p => ?_⟩
        rw [dot_smul, neg_one_mul]
        exact (signVal_neg (σ p) (-dot p.1 d)).mpr (by rw [neg_neg]; exact hd p)
    have h2 : 2 * ∑ σ ∈ centralRegions A, (walls A σ).card =
        ∑ σ ∈ centralRegions A, ((walls A σ).card + (walls A (fun p => !(σ p))).card) := by
      rw [Finset.sum_add_distrib, hneg_sum]; omega
    rw [h2]
    have hconst : (∑ _σ ∈ centralRegions A, (5 : ℕ)) = 5 * (centralRegions A).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← hconst]
    exact Finset.sum_le_sum fun σ hσ => five_le_walls_add_neg hnp hcard hnc hσ
  have hcard_sdiff : (regions A \ centralRegions A).card + (centralRegions A).card =
      (regions A).card := Finset.card_sdiff_add_card_eq_card hcent_sub
  omega

/-- Bridge from `ℝ² = EuclideanSpace ℝ (Fin 2)` to `Pt = ℝ × ℝ`. -/
def toP (p : ℝ²) : Pt := (p 0, p 1)

lemma toP_injective : Function.Injective toP := by
  intro a b h
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma mem_line_iff_det2 {a b p : ℝ²} (hab : a ≠ b) :
    p ∈ line[ℝ, a, b] ↔ det2 (psub (toP p) (toP a)) (psub (toP b) (toP a)) = 0 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    simp only [det2, psub, toP, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  · intro hdet
    dsimp [det2, psub, toP] at hdet
    have hne : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hab
      ext i; fin_cases i
      · exact (sub_eq_zero.mp h.1).symm
      · exact (sub_eq_zero.mp h.2).symm
    rcases hne with hx | hy
    · refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
      ext i; fin_cases i
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
        rw [div_mul_cancel₀ _ hx]; ring
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
        rw [div_mul_eq_mul_div, ← eq_sub_iff_add_eq, div_eq_iff hx]
        linarith
    · refine ⟨(p 1 - a 1) / (b 1 - a 1), ?_⟩
      ext i; fin_cases i
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
        rw [div_mul_eq_mul_div, ← eq_sub_iff_add_eq, div_eq_iff hy]
        linarith
      · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
        rw [div_mul_cancel₀ _ hy]; ring

end OMA.Melchior

theorem OMA.solution : OMA.R_Erdos211_erdos_211_variants_one_sixth_R1.H2 := by
  classical
  open EuclideanGeometry Erdos211 OMA.Melchior in
  intro s hs hnc
  -- First note 3 ≤ s.card (if s.card = 2 then the unique line contains both points)
  have hs3 : 3 ≤ s.card := by
    by_contra hlt
    have hs2 : s.card = 2 := by omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs2
    have hL := hnc line[ℝ, a, b] (isLine_pair hab)
    have hfilt : ({a, b} : Finset ℝ²).filter (fun p => p ∈ line[ℝ, a, b]) = {a, b} := by
      ext p; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        and_iff_left_iff_imp]
      rintro (hp | hp)
      · rw [hp]; exact left_mem_affineSpan_pair ℝ a b
      · rw [hp]; exact right_mem_affineSpan_pair ℝ a b
    rw [hfilt] at hL
    omega
  -- Choose a translation point c : Pt avoiding every determined line L ∈ determinedLines s!
  let F : Finset (ℝ × ℝ × ℝ) :=
    (determinedLines s).attach.image (fun L =>
      let h := mem_determinedLines.mp L.2
      let a := h.choose
      let b := h.choose_spec.2.choose
      (b 1 - a 1, -(b 0 - a 0), a 0 * (b 1 - a 1) - a 1 * (b 0 - a 0)))
  have hF : ∀ f ∈ F, f.1 ≠ 0 ∨ f.2.1 ≠ 0 := by
    intro f hf
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp hf
    set h := mem_determinedLines.mp L.2
    set a := h.choose
    set b := h.choose_spec.2.choose
    have hab : a ≠ b := h.choose_spec.2.choose_spec.2.1
    by_contra h0
    push_neg at h0
    apply hab
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith [h0.2]
    · simp only [Fin.mk_one, Fin.isValue]; linarith [h0.1]
  obtain ⟨c, hc⟩ := exists_avoid_affine F hF
  -- Map each p ∈ s to psub (toP p) c : Pt
  let shift : ℝ² → Pt := fun p => psub (toP p) c
  have hshift_inj : Function.Injective shift := by
    intro a b h
    apply toP_injective
    apply Prod.ext <;> dsimp [shift, psub] at h <;> linarith [congrArg Prod.fst h, congrArg Prod.snd h]
  let A : Finset Pt := s.image shift
  have hA_card : A.card = s.card := Finset.card_image_of_injective s hshift_inj
  -- For any distinct a, b ∈ s, det2 (shift a) (shift b) ≠ 0 (because c avoids line[a, b]!)
  have hdet_ab : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → det2 (shift a) (shift b) ≠ 0 := by
    intro a ha b hb hab hdet0
    let L := line[ℝ, a, b]
    have hL : L ∈ determinedLines s := mem_determinedLines.mpr ⟨a, ha, b, hb, hab, rfl⟩
    set h := mem_determinedLines.mp hL
    set a' := h.choose
    set b' := h.choose_spec.2.choose
    have ha'b' : a' ≠ b' := h.choose_spec.2.choose_spec.2.1
    have hLeq : line[ℝ, a', b'] = L := h.choose_spec.2.choose_spec.2.2
    have haL : a ∈ line[ℝ, a', b'] := hLeq ▸ left_mem_affineSpan_pair ℝ a b
    have hbL : b ∈ line[ℝ, a', b'] := hLeq ▸ right_mem_affineSpan_pair ℝ a b
    have hda := (mem_line_iff_det2 ha'b').mp haL
    have hdb := (mem_line_iff_det2 ha'b').mp hbL
    have hc_ne := hc _ (Finset.mem_image.mpr ⟨⟨L, hL⟩, Finset.mem_attach _ _, rfl⟩)
    -- det2 (shift a) (shift b) = 0 means c lies on line[a, b] = line[a', b'], contradicting hc_ne!
    dsimp [det2, shift, psub, toP] at hdet0 hda hdb hc_ne
    have hne_ab : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
      by_contra h0; push_neg at h0; apply hab; ext i; fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]; linarith [h0.1]
      · simp only [Fin.mk_one, Fin.isValue]; linarith [h0.2]
    -- Linear algebra: a, b lie on (b'1 - a'1) x - (b'0 - a'0) y = const, and c is collinear with a, b
    have hlin : (b 1 - a 1) * c.1 - (b 0 - a 0) * c.2 = a 0 * (b 1 - a 1) - a 1 * (b 0 - a 0) := by
      linarith
    have hpar : (b' 1 - a' 1) * (b 0 - a 0) = (b' 0 - a' 0) * (b 1 - a 1) := by linarith
    rcases hne_ab with hx | hy
    · have : (b 0 - a 0) * ((b' 1 - a' 1) * c.1 + -(b' 0 - a' 0) * c.2 -
          (a' 0 * (b' 1 - a' 1) - a' 1 * (b' 0 - a' 0))) = 0 := by
        linear_combination (b' 0 - a' 0) * hlin + (c.1 - a 0) * hpar + (b 0 - a 0) * hda
      exact hc_ne (by linarith [(mul_eq_zero.mp this).resolve_left hx])
    · have : (b 1 - a 1) * ((b' 1 - a' 1) * c.1 + -(b' 0 - a' 0) * c.2 -
          (a' 0 * (b' 1 - a' 1) - a' 1 * (b' 0 - a' 0))) = 0 := by
        linear_combination (b' 1 - a' 1) * hlin + (c.2 - a 1) * hpar + (b 1 - a 1) * hda
      exact hc_ne (by linarith [(mul_eq_zero.mp this).resolve_left hy])
  have hnp : NonParallel A := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact hdet_ab a ha b hb (fun h => hpq (congrArg shift h))
  -- Polar duality equivalence: for a ≠ b ∈ s and p ∈ s,
  -- p ∈ line[ℝ, a, b] ↔ dot (shift p) (interPt (shift a) (shift b)) = 1!
  have hpolar : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ p : ℝ²,
      p ∈ line[ℝ, a, b] ↔ dot (shift p) (interPt (shift a) (shift b)) = 1 := by
    intro a ha b hb hab p
    rw [mem_line_iff_det2 hab]
    have hd := hdet_ab a ha b hb hab
    dsimp [dot, interPt, det2, shift, psub, toP] at hd ⊢
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hd]
    constructor <;> intro h <;> linarith
  -- Non-concurrency of A: every v ∈ ℝ×ℝ has |{p ∈ A | dot p v = 1}| < A.card
  have hncA : ∀ v : Pt, (A.filter (fun p => dot p v = 1)).card < A.card := by
    intro v
    by_cases hle1 : (A.filter (fun p => dot p v = 1)).card ≤ 1
    · omega
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (A.filter (fun p => dot p v = 1)).card)
      obtain ⟨hpA, hpv⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqA, hqv⟩ := Finset.mem_filter.mp hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hqA
      have hab : a ≠ b := fun h => hpq (congrArg shift h)
      have hv_eq : v = interPt (shift a) (shift b) :=
        interPt_unique (hdet_ab a ha b hb hab) hpv hqv
      have hcard_eq : (A.filter (fun p => dot p v = 1)).card =
          (s.filter (fun p => p ∈ line[ℝ, a, b])).card := by
        refine Finset.card_bij (fun p hp => (Finset.mem_image.mp (Finset.mem_filter.mp hp).1).choose) ?_ ?_ ?_
        · intro p hp
          obtain ⟨hpA', hpv'⟩ := Finset.mem_filter.mp hp
          set x := (Finset.mem_image.mp hpA').choose
          have hx := (Finset.mem_image.mp hpA').choose_spec
          refine Finset.mem_filter.mpr ⟨hx.1, (hpolar a ha b hb hab x).mpr ?_⟩
          rw [hx.2, ← hv_eq]; exact hpv'
        · intro p₁ hp₁ p₂ hp₂ heq
          have hx₁ := (Finset.mem_image.mp (Finset.mem_filter.mp hp₁).1).choose_spec.2
          have hx₂ := (Finset.mem_image.mp (Finset.mem_filter.mp hp₂).1).choose_spec.2
          rw [← hx₁, ← hx₂, heq]
        · intro x hx
          obtain ⟨hxs, hxL⟩ := Finset.mem_filter.mp hx
          have hmem : shift x ∈ A.filter (fun p => dot p v = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hxs, rfl⟩,
              hv_eq ▸ (hpolar a ha b hb hab x).mp hxL⟩
          refine ⟨shift x, hmem, ?_⟩
          exact hshift_inj (Finset.mem_image.mp (Finset.mem_filter.mp hmem).1).choose_spec.2
      rw [hcard_eq, hA_card]
      exact hnc line[ℝ, a, b] (isLine_pair hab)
  -- Bijection between determinedLines s and verts A preserving multiplicities!
  let toV : AffineSubspace ℝ ℝ² → Pt := fun L =>
    if h : L ∈ determinedLines s then
      let m := mem_determinedLines.mp h
      interPt (shift m.choose) (shift m.choose_spec.2.choose)
    else (0, 0)
  have htoV_eq : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      toV line[ℝ, a, b] = interPt (shift a) (shift b) := by
    intro a ha b hb hab
    have hL : line[ℝ, a, b] ∈ determinedLines s := mem_determinedLines.mpr ⟨a, ha, b, hb, hab, rfl⟩
    dsimp [toV]
    rw [dif_pos hL]
    set m := mem_determinedLines.mp hL
    set a' := m.choose
    set b' := m.choose_spec.2.choose
    have ha' := m.choose_spec.1
    have hb' := m.choose_spec.2.choose_spec.1
    have ha'b' := m.choose_spec.2.choose_spec.2.1
    have hLeq := m.choose_spec.2.choose_spec.2.2
    have haL : a ∈ line[ℝ, a', b'] := hLeq ▸ left_mem_affineSpan_pair ℝ a b
    have hbL : b ∈ line[ℝ, a', b'] := hLeq ▸ right_mem_affineSpan_pair ℝ a b
    exact interPt_unique (hdet_ab a ha b hb hab)
      ((hpolar a' ha' b' hb' ha'b' a).mp haL)
      ((hpolar a' ha' b' hb' ha'b' b).mp hbL)
  have hverts_card : (determinedLines s).card = (verts A).card := by
    refine Finset.card_bij (fun L _ => toV L) ?_ ?_ ?_
    · intro L hL
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_determinedLines.mp hL
      rw [htoV_eq a ha b hb hab]
      exact (mem_verts_iff hnp).mpr
        ⟨shift a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
         shift b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
         fun h => hab (hshift_inj h),
         dot_interPt_left (hdet_ab a ha b hb hab),
         dot_interPt_right (hdet_ab a ha b hb hab)⟩
    · intro L₁ hL₁ L₂ hL₂ heq
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁, hL₁eq⟩ := mem_determinedLines.mp hL₁
      obtain ⟨a₂, ha₂, b₂, hb₂, hab₂, hL₂eq⟩ := mem_determinedLines.mp hL₂
      rw [← hL₁eq, ← hL₂eq, htoV_eq a₁ ha₁ b₁ hb₁ hab₁, htoV_eq a₂ ha₂ b₂ hb₂ hab₂] at heq
      have ha₁L₂ : a₁ ∈ line[ℝ, a₂, b₂] :=
        (hpolar a₂ ha₂ b₂ hb₂ hab₂ a₁).mpr (heq ▸ dot_interPt_left (hdet_ab a₁ ha₁ b₁ hb₁ hab₁))
      have hb₁L₂ : b₁ ∈ line[ℝ, a₂, b₂] :=
        (hpolar a₂ ha₂ b₂ hb₂ hab₂ b₁).mpr (heq ▸ dot_interPt_right (hdet_ab a₁ ha₁ b₁ hb₁ hab₁))
      rw [← hL₁eq, ← hL₂eq]
      exact line_pair_eq (isLine_pair hab₂) ha₁L₂ hb₁L₂ hab₁
    · intro v hv
      obtain ⟨p, hpA, q, hqA, hpq, hpv, hqv⟩ := (mem_verts_iff hnp).mp hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hqA
      have hab : a ≠ b := fun h => hpq (congrArg shift h)
      exact ⟨line[ℝ, a, b], mem_determinedLines.mpr ⟨a, ha, b, hb, hab, rfl⟩,
        (htoV_eq a ha b hb hab).trans (interPt_unique (hdet_ab a ha b hb hab) hpv hqv).symm⟩
  have hsum_eq : (∑ L ∈ determinedLines s, (s.filter (fun p => p ∈ L)).card) =
      ∑ v ∈ verts A, inc A v := by
    refine Finset.sum_bij (fun L _ => toV L) ?_ ?_ ?_ ?_
    · intro L hL
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_determinedLines.mp hL
      rw [htoV_eq a ha b hb hab]
      exact (mem_verts_iff hnp).mpr
        ⟨shift a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
         shift b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
         fun h => hab (hshift_inj h),
         dot_interPt_left (hdet_ab a ha b hb hab),
         dot_interPt_right (hdet_ab a ha b hb hab)⟩
    · intro L₁ hL₁ L₂ hL₂ heq
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁, hL₁eq⟩ := mem_determinedLines.mp hL₁
      obtain ⟨a₂, ha₂, b₂, hb₂, hab₂, hL₂eq⟩ := mem_determinedLines.mp hL₂
      rw [← hL₁eq, ← hL₂eq, htoV_eq a₁ ha₁ b₁ hb₁ hab₁, htoV_eq a₂ ha₂ b₂ hb₂ hab₂] at heq
      have ha₁L₂ : a₁ ∈ line[ℝ, a₂, b₂] :=
        (hpolar a₂ ha₂ b₂ hb₂ hab₂ a₁).mpr (heq ▸ dot_interPt_left (hdet_ab a₁ ha₁ b₁ hb₁ hab₁))
      have hb₁L₂ : b₁ ∈ line[ℝ, a₂, b₂] :=
        (hpolar a₂ ha₂ b₂ hb₂ hab₂ b₁).mpr (heq ▸ dot_interPt_right (hdet_ab a₁ ha₁ b₁ hb₁ hab₁))
      rw [← hL₁eq, ← hL₂eq]
      exact line_pair_eq (isLine_pair hab₂) ha₁L₂ hb₁L₂ hab₁
    · intro v hv
      obtain ⟨p, hpA, q, hqA, hpq, hpv, hqv⟩ := (mem_verts_iff hnp).mp hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hqA
      have hab : a ≠ b := fun h => hpq (congrArg shift h)
      exact ⟨line[ℝ, a, b], mem_determinedLines.mpr ⟨a, ha, b, hb, hab, rfl⟩,
        (htoV_eq a ha b hb hab).trans (interPt_unique (hdet_ab a ha b hb hab) hpv hqv).symm⟩
    · intro L hL
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_determinedLines.mp hL
      rw [htoV_eq a ha b hb hab]
      dsimp [inc]
      refine Finset.card_bij (fun p _ => shift p) ?_ ?_ ?_
      · intro p hp
        obtain ⟨hps, hpL⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hps, rfl⟩,
          (hpolar a ha b hb hab p).mp hpL⟩
      · intro p₁ _ p₂ _ h; exact hshift_inj h
      · intro q hq
        obtain ⟨hqA, hqv⟩ := Finset.mem_filter.mp hq
        obtain ⟨p, hps, rfl⟩ := Finset.mem_image.mp hqA
        exact ⟨p, Finset.mem_filter.mpr ⟨hps, (hpolar a ha b hb hab p).mpr hqv⟩, rfl⟩
  have hnat : (∑ L ∈ determinedLines s, (s.filter (fun p => p ∈ L)).card) ≤
      3 * (determinedLines s).card := by
    rw [hsum_eq, hverts_card]
    have hm := melchior_arrangement A hnp (hA_card ▸ hs3) hncA
    omega
  exact_mod_cast hnat
