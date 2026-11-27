/-!
# Bitwise-Weighted Binomial & Lucas-Mask Fractal Engine (adic-9)

A standalone, zero-Mathlib, pure-silicon Lean 4.34.1 formalization of a reusable
three-stage infinite proof engine for bitwise-filtered binomial sums over the
Lucas submask cube `{k : Nat | k &&& n = k}`:

- **Stage 1 (`BitSliceEngine`):** A closed 2-state LSB bit-slice induction engine
  proving the universal 2-adic divisibility of shifted Lucas-mask Mobius
  derivatives `Delta(n, j, c)` and compiling their exact mod-2 leading bits into
  a 2-state finite-state bitmask transducer whose closed form is the run-endpoint
  bitmask `E(n) = n &&& ((n <<< 1) ^^^ (n >>> 1))`.
- **Stage 2 (`BitSmoothAlgebra`):** A reusable abstract algebraic filtration
  `BitSmooth n E f` and `BitUnit n s f` on the Boolean submask lattice of `n`,
  proving:
  1. Bit-smooth excess product closure,
  2. Pointwise multiplication -> bitwise XOR spike-mask homomorphism (`E1 ^^^ E2`),
  3. Squaring Jump Law (`BitSmooth n E f -> BitUnit n 2 (f^2)`),
  4. Higher Squaring Lift (`BitUnit n s g -> BitUnit n (s + 1) (g^2)`),
  5. Exponent Lifting Compiler for arbitrary `r >= 1` parameterized by `v2(r)`.
- **Stage 3 (`WalshBridge`):** A bit-slice spectral bridge lifting `BitSmooth`
  and `BitUnit` memberships to exact 2-adic congruences and exact `v_2` valuations
  for all Walsh-weighted binomial sums over `k <=_2 n`, yielding four sharp
  infinite theorems, a Lucas-Mask Mod-4 theorem, kernel-checked non-vacuity
  witnesses, and kernel-checked sharpness counterexamples.
-/

namespace LucasMaskEngine

/-! ## Section 0: Pure-Silicon Bitmask & Sum Primitives -/

/-- Strong induction on `Nat` (standalone core Lean 4 wrapper around `Nat.strongRecOn`). -/
theorem nat_strong_ind {P : Nat → Prop} (step : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n :=
  Nat.strongRecOn n step

/-- Structurally recursive fuel-based popcount so concrete instances reduce in `decide`. -/
def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else (n % 2) + popcountAux fuel (n / 2)

/-- Exact binary popcount (Hamming weight). -/
def popcount (n : Nat) : Nat := popcountAux n n

theorem popcountAux_ge (fuel n : Nat) (h : n ≤ fuel) :
    popcountAux (fuel + 1) n = popcountAux fuel n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn; rfl
  | succ f ih =>
    unfold popcountAux
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      rw [ih (n / 2) (by omega)]

theorem popcountAux_eq_of_ge {f1 f2 n : Nat} (h1 : n ≤ f1) (h2 : n ≤ f2) :
    popcountAux f1 n = popcountAux f2 n := by
  have hgen : ∀ d f, n ≤ f → popcountAux (f + d) n = popcountAux f n := by
    intro d; induction d with
    | zero => intro f _; rfl
    | succ d ih =>
      intro f hf
      have : f + (d + 1) = (f + d) + 1 := by omega
      rw [this, popcountAux_ge (f + d) n (by omega), ih f hf]
  have e1 := hgen (f1 - n) n (Nat.le_refl n)
  have e2 := hgen (f2 - n) n (Nat.le_refl n)
  rw [Nat.add_sub_of_le h1] at e1
  rw [Nat.add_sub_of_le h2] at e2
  rw [e1, e2]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_pos_eq (n : Nat) (hn : n ≠ 0) :
    popcount n = (n % 2) + popcount (n / 2) := by
  unfold popcount
  have h1 : n = (n - 1) + 1 := by omega
  conv => lhs; rw [h1]; unfold popcountAux
  rw [← h1]
  simp only [hn, ↓reduceIte]
  rw [popcountAux_eq_of_ge (f1 := n - 1) (f2 := n / 2) (by omega) (Nat.le_refl _)]

theorem popcount_two_mul (m : Nat) : popcount (2 * m) = popcount m := by
  by_cases hm : m = 0
  · subst hm; rfl
  · rw [popcount_pos_eq (2 * m) (by omega)]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m) / 2 = m := by omega
    rw [h1, h2, Nat.zero_add]

theorem popcount_two_mul_add_one (m : Nat) : popcount (2 * m + 1) = popcount m + 1 := by
  rw [popcount_pos_eq (2 * m + 1) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, Nat.add_comm]

/-- Structurally recursive 2-adic valuation of positive natural numbers (`v2Nat 0 = 0`). -/
def v2NatAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, r => if r = 0 then 0 else if r % 2 = 0 then 1 + v2NatAux fuel (r / 2) else 0

def v2Nat (r : Nat) : Nat := v2NatAux r r

/-- The Lucas submask relation `k <=_2 n` (`k & ~n = 0`, equivalently `k &&& n = k`). -/
def Submask (k n : Nat) : Prop := k &&& n = k

instance (k n : Nat) : Decidable (Submask k n) :=
  inferInstanceAs (Decidable (k &&& n = k))

/-- Run-endpoint bitmask: bit `i` is set iff bit `i` is an endpoint of a run of
    at least two consecutive `1`-bits in `n`. -/
def endpointMask (n : Nat) : Nat :=
  n &&& ((n <<< 1) ^^^ (n >>> 1))

theorem testBit_two_mul_zero (m : Nat) : (2 * m).testBit 0 = false := by
  rw [Nat.testBit_zero]; simp [Nat.mul_mod_right]

theorem testBit_two_mul_succ (m j : Nat) : (2 * m).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  have h : (2 * m) / 2 = m := by omega
  rw [h]

theorem testBit_two_mul_add_one_zero (m : Nat) : (2 * m + 1).testBit 0 = true := by
  rw [Nat.testBit_zero]
  have h : (2 * m + 1) % 2 = 1 := by omega
  simp [h]

theorem testBit_two_mul_add_one_succ (m j : Nat) : (2 * m + 1).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  have h : (2 * m + 1) / 2 = m := by omega
  rw [h]

theorem submask_iff_testBit {k n : Nat} :
    Submask k n ↔ ∀ i, k.testBit i = true → n.testBit i = true := by
  unfold Submask
  constructor
  · intro h i hk
    have hb := congrArg (fun x => x.testBit i) h
    rw [Nat.testBit_and, hk] at hb
    simpa using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hk : k.testBit i
    · simp
    · simp [h i hk]

theorem submask_zero (n : Nat) : Submask 0 n := by
  rw [submask_iff_testBit]; intro i h; simp at h

theorem submask_two_mul_iff (k m : Nat) :
    Submask k (2 * m) ↔ k % 2 = 0 ∧ Submask (k / 2) m := by
  rw [submask_iff_testBit, submask_iff_testBit]
  constructor
  · intro h
    constructor
    · by_cases hpar : k % 2 = 0
      · exact hpar
      · exfalso
        have h1 : k.testBit 0 = true := by
          rw [Nat.testBit_zero]
          have : k % 2 = 1 := by omega
          simp [this]
        have h2 := h 0 h1
        rw [testBit_two_mul_zero] at h2
        contradiction
    · intro i hi
      have h1 : k.testBit (i + 1) = true := by
        rw [Nat.testBit_succ]; exact hi
      have h2 := h (i + 1) h1
      rw [testBit_two_mul_succ] at h2
      exact h2
  · rintro ⟨hpar, hdiv⟩ i hi
    cases i with
    | zero =>
      rw [Nat.testBit_zero] at hi
      simp [hpar] at hi
    | succ j =>
      rw [testBit_two_mul_succ]
      rw [Nat.testBit_succ] at hi
      exact hdiv j hi

theorem submask_two_mul_add_one_iff (k m : Nat) :
    Submask k (2 * m + 1) ↔ Submask (k / 2) m := by
  rw [submask_iff_testBit, submask_iff_testBit]
  constructor
  · intro h i hi
    have h1 : k.testBit (i + 1) = true := by
      rw [Nat.testBit_succ]; exact hi
    have h2 := h (i + 1) h1
    rw [testBit_two_mul_add_one_succ] at h2
    exact h2
  · intro h i hi
    cases i with
    | zero => rw [testBit_two_mul_add_one_zero]
    | succ j =>
      rw [testBit_two_mul_add_one_succ]
      rw [Nat.testBit_succ] at hi
      exact h j hi

theorem submask_two_mul_left_two_mul_right (a b : Nat) :
    Submask (2 * a) (2 * b) ↔ Submask a b := by
  rw [submask_two_mul_iff]
  have h1 : (2 * a) % 2 = 0 := by omega
  have h2 : (2 * a) / 2 = a := by omega
  simp [h2]

theorem submask_two_mul_left_odd_right (a b : Nat) :
    Submask (2 * a) (2 * b + 1) ↔ Submask a b := by
  rw [submask_two_mul_add_one_iff]
  have h : (2 * a) / 2 = a := by omega
  rw [h]

theorem submask_odd_left_odd_right (a b : Nat) :
    Submask (2 * a + 1) (2 * b + 1) ↔ Submask a b := by
  rw [submask_two_mul_add_one_iff]
  have h : (2 * a + 1) / 2 = a := by omega
  rw [h]

theorem submask_le {k n : Nat} (h : Submask k n) : k ≤ n := by
  induction n using nat_strong_ind generalizing k with
  | step n ih =>
    by_cases hn : n = 0
    · subst hn
      have : k = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        cases hk : k.testBit i
        · simp
        · have := (submask_iff_testBit.mp h) i hk; simp at this
      omega
    · by_cases hp : n % 2 = 0
      · have h2 : n = 2 * (n / 2) := by omega
        rw [h2] at h
        obtain ⟨hk0, hdiv⟩ := (submask_two_mul_iff k (n / 2)).mp h
        have hle := ih (n / 2) (by omega) hdiv
        omega
      · have h2 : n = 2 * (n / 2) + 1 := by omega
        rw [h2] at h
        have hdiv := (submask_two_mul_add_one_iff k (n / 2)).mp h
        have hle := ih (n / 2) (by omega) hdiv
        omega

theorem dvd_two_pow_mono {a b : Nat} {x : Int} (hab : a ≤ b)
    (h : (2 : Int) ^ b ∣ x) : (2 : Int) ^ a ∣ x := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨(2 : Int) ^ (b - a) * q, ?_⟩
  rw [← Int.mul_assoc, ← Int.pow_add, Nat.add_sub_of_le hab]

theorem dvd_two_pow_mul_left (a b : Nat) {x : Int} (h : (2 : Int) ^ b ∣ x) :
    (2 : Int) ^ (a + b) ∣ (2 : Int) ^ a * x := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨q, ?_⟩
  rw [Int.pow_add, Int.mul_assoc]

theorem dvd_two_mul_of_dvd {e : Nat} {x : Int} (h : (2 : Int) ^ e ∣ x) :
    (2 : Int) ^ (e + 1) ∣ 2 * x := by
  have h1 := dvd_two_pow_mul_left 1 e h
  rw [Nat.add_comm] at h1
  simpa using h1

theorem dvd_add_of_dvd {d a b : Int} (ha : d ∣ a) (hb : d ∣ b) : d ∣ (a + b) := by
  obtain ⟨qa, rfl⟩ := ha
  obtain ⟨qb, rfl⟩ := hb
  exact ⟨qa + qb, by rw [Int.mul_add]⟩

theorem two_pow_succ_mul_eq_add (e : Nat) (x : Int) :
    (2 : Int) ^ (e + 1) * x = (2 : Int) ^ e * x + (2 : Int) ^ e * x := by
  rw [Int.pow_succ, Int.mul_assoc, Int.mul_comm 2 x, ← Int.mul_assoc]
  have h2 : ∀ z : Int, z * 2 = z + z := fun z => by omega
  exact h2 ((2 : Int) ^ e * x)

theorem beq_two_mul_eq (a b : Nat) : (2 * a == 2 * b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : 2 * a ≠ 2 * b := by omega
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

/-- Finite sum `∑_{i=0}^{n-1} g i`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, g => sumRange n g + g n

theorem sumRange_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp only [sumRange, ih]; omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp only [sumRange, ih, Int.mul_add]

theorem sumRange_even_odd (n : Nat) (f : Nat → Int) :
    sumRange (2 * n) f = sumRange n (fun i => f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1]
    simp only [sumRange]
    rw [ih]
    omega

/-- Standard explicit Lucas-mask filtered sum `∑_{k=0}^{n} [k &&& n = k] * f k`. -/
def sumLucasFiltered (n : Nat) (f : Nat → Int) : Int :=
  sumRange (n + 1) (fun k => if k &&& n = k then f k else 0)

/-- Structurally recursive fuel-based submask sum so concrete instances reduce in `decide`. -/
def sumSubmasksAux : Nat → Nat → (Nat → Int) → Int
  | 0, _, f => f 0
  | fuel + 1, j, f =>
    if j = 0 then f 0
    else if j % 2 = 0 then sumSubmasksAux fuel (j / 2) (fun k => f (2 * k))
    else sumSubmasksAux fuel (j / 2) (fun k => f (2 * k) + f (2 * k + 1))

/-- Pure-silicon bit-sliced recursive sum over all submasks `k <=_2 j`. -/
def sumSubmasks (j : Nat) (f : Nat → Int) : Int := sumSubmasksAux j j f

theorem sumSubmasksAux_ge (fuel j : Nat) (f : Nat → Int) (h : j ≤ fuel) :
    sumSubmasksAux (fuel + 1) j f = sumSubmasksAux fuel j f := by
  induction fuel generalizing j f with
  | zero =>
    have hj : j = 0 := by omega
    subst hj; rfl
  | succ fl ih =>
    unfold sumSubmasksAux
    by_cases hj : j = 0
    · simp [hj]
    · by_cases hp : j % 2 = 0
      · simp only [hj, hp, ↓reduceIte]
        exact ih (j / 2) (fun k => f (2 * k)) (by omega)
      · simp only [hj, hp, ↓reduceIte]
        exact ih (j / 2) (fun k => f (2 * k) + f (2 * k + 1)) (by omega)

theorem sumSubmasksAux_eq_of_ge {f1 f2 j : Nat} {g : Nat → Int} (h1 : j ≤ f1) (h2 : j ≤ f2) :
    sumSubmasksAux f1 j g = sumSubmasksAux f2 j g := by
  have hgen : ∀ d fl, j ≤ fl → sumSubmasksAux (fl + d) j g = sumSubmasksAux fl j g := by
    intro d; induction d with
    | zero => intro fl _; rfl
    | succ d ih =>
      intro fl hfl
      have : fl + (d + 1) = (fl + d) + 1 := by omega
      rw [this, sumSubmasksAux_ge (fl + d) j g (by omega), ih fl hfl]
  have e1 := hgen (f1 - j) j (Nat.le_refl j)
  have e2 := hgen (f2 - j) j (Nat.le_refl j)
  rw [Nat.add_sub_of_le h1] at e1
  rw [Nat.add_sub_of_le h2] at e2
  rw [e1, e2]

theorem sumSubmasks_zero (f : Nat → Int) : sumSubmasks 0 f = f 0 := rfl

theorem sumSubmasks_two_mul (m : Nat) (f : Nat → Int) :
    sumSubmasks (2 * m) f = sumSubmasks m (fun k => f (2 * k)) := by
  by_cases hm : m = 0
  · subst hm; rfl
  · unfold sumSubmasks
    have h1 : 2 * m = (2 * m - 1) + 1 := by omega
    conv => lhs; rw [h1]; unfold sumSubmasksAux
    have hne : (2 * m - 1) + 1 ≠ 0 := by omega
    have hpar : ((2 * m - 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * m - 1) + 1) / 2 = m := by omega
    simp only [hne, hpar, hdiv, ↓reduceIte]
    exact sumSubmasksAux_eq_of_ge (f1 := 2 * m - 1) (f2 := m) (by omega) (Nat.le_refl m)

theorem sumSubmasks_two_mul_add_one (m : Nat) (f : Nat → Int) :
    sumSubmasks (2 * m + 1) f = sumSubmasks m (fun k => f (2 * k) + f (2 * k + 1)) := by
  conv => lhs; unfold sumSubmasks; unfold sumSubmasksAux
  have hne : 2 * m + 1 ≠ 0 := by omega
  have hpar : (2 * m + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp only [hne, hpar, hdiv, ↓reduceIte]
  exact sumSubmasksAux_eq_of_ge (f1 := 2 * m) (f2 := m) (by omega) (Nat.le_refl m)

/-- Exact equivalence between the bit-sliced `sumSubmasks` and the explicit filtered sum
    `∑_{k=0}^{n} [k &&& n = k] * f k`. -/
theorem sumSubmasks_eq_sumLucasFiltered (n : Nat) (f : Nat → Int) :
    sumSubmasks n f = sumLucasFiltered n f := by
  induction n using nat_strong_ind generalizing f with
  | step n ih =>
    by_cases hn : n = 0
    · subst hn
      simp [sumSubmasks_zero, sumLucasFiltered, sumRange]
    · by_cases hp : n % 2 = 0
      · have h2 : n = 2 * (n / 2) := by omega
        rw [h2, sumSubmasks_two_mul, ih (n / 2) (by omega)]
        unfold sumLucasFiltered
        have hlast : sumRange (2 * (n / 2) + 1)
            (fun k => if k &&& (2 * (n / 2)) = k then f k else 0) =
            sumRange (2 * (n / 2 + 1))
            (fun k => if k &&& (2 * (n / 2)) = k then f k else 0) := by
          have hs : 2 * (n / 2 + 1) = (2 * (n / 2) + 1) + 1 := by omega
          rw [hs]
          simp only [sumRange]
          have hno : ¬ Submask (2 * (n / 2) + 1) (2 * (n / 2)) := by
            rw [submask_two_mul_iff]; omega
          have hno' : ¬ ((2 * (n / 2) + 1) &&& (2 * (n / 2)) = 2 * (n / 2) + 1) := hno
          simp [hno']
        rw [hlast, sumRange_even_odd]
        apply sumRange_congr
        intro k _
        have hev : ((2 * k) &&& (2 * (n / 2)) = 2 * k) ↔ (k &&& (n / 2) = k) :=
          submask_two_mul_left_two_mul_right k (n / 2)
        have hodd : ¬ ((2 * k + 1) &&& (2 * (n / 2)) = 2 * k + 1) := by
          change ¬ Submask (2 * k + 1) (2 * (n / 2))
          rw [submask_two_mul_iff]; omega
        by_cases hk : k &&& (n / 2) = k
        · have hk' := hev.mpr hk
          simp [hk, hk', hodd]
        · have hk' : ¬ ((2 * k) &&& (2 * (n / 2)) = 2 * k) := fun h => hk (hev.mp h)
          simp [hk, hk', hodd]
      · have h2 : n = 2 * (n / 2) + 1 := by omega
        rw [h2, sumSubmasks_two_mul_add_one, ih (n / 2) (by omega)]
        unfold sumLucasFiltered
        have hs : 2 * (n / 2) + 1 + 1 = 2 * (n / 2 + 1) := by omega
        rw [hs, sumRange_even_odd]
        apply sumRange_congr
        intro k _
        have hev : ((2 * k) &&& (2 * (n / 2) + 1) = 2 * k) ↔ (k &&& (n / 2) = k) :=
          submask_two_mul_left_odd_right k (n / 2)
        have hodd : ((2 * k + 1) &&& (2 * (n / 2) + 1) = 2 * k + 1) ↔ (k &&& (n / 2) = k) :=
          submask_odd_left_odd_right k (n / 2)
        by_cases hk : k &&& (n / 2) = k
        · simp [hk, hev.mpr hk, hodd.mpr hk]
        · have h1 : ¬ ((2 * k) &&& (2 * (n / 2) + 1) = 2 * k) := fun h => hk (hev.mp h)
          have h2' : ¬ ((2 * k + 1) &&& (2 * (n / 2) + 1) = 2 * k + 1) := fun h => hk (hodd.mp h)
          simp [hk, h1, h2']

theorem sumSubmasks_congr {j : Nat} {f g : Nat → Int}
    (h : ∀ k, Submask k j → f k = g k) : sumSubmasks j f = sumSubmasks j g := by
  rw [sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  apply sumRange_congr
  intro k _
  by_cases hk : k &&& j = k
  · simp [hk, h k hk]
  · simp [hk]

theorem sumSubmasks_add (j : Nat) (f g : Nat → Int) :
    sumSubmasks j (fun k => f k + g k) = sumSubmasks j f + sumSubmasks j g := by
  rw [sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  rw [← sumRange_add]
  apply sumRange_congr
  intro k _; dsimp only; split <;> omega

theorem sumSubmasks_mul_left (j : Nat) (c : Int) (f : Nat → Int) :
    sumSubmasks j (fun k => c * f k) = c * sumSubmasks j f := by
  rw [sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  rw [← sumRange_mul_left]
  apply sumRange_congr
  intro k _; dsimp only; split <;> simp

/-- Exact Boolean Mobius derivative on the Lucas cube of `j`:
    `mobius f j = ∑_{k <=_2 j} (-1)^popcount(j ^^^ k) * f k`. -/
def mobius (f : Nat → Int) (j : Nat) : Int :=
  sumSubmasks j (fun k => (if popcount (j ^^^ k) % 2 = 0 then 1 else -1) * f k)

/-- Exact Walsh-Hadamard transform on the Lucas cube of `n`:
    `walsh n m f = ∑_{k <=_2 n} (-1)^popcount(k &&& m) * f k`. -/
def walsh (n m : Nat) (f : Nat → Int) : Int :=
  sumSubmasks n (fun k => (if popcount (k &&& m) % 2 = 0 then 1 else -1) * f k)

theorem xor_two_mul_two_mul (a b : Nat) : (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_xor, testBit_two_mul_zero, testBit_two_mul_zero, testBit_two_mul_zero]; rfl
  | succ j => rw [Nat.testBit_xor, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ, Nat.testBit_xor]

theorem xor_odd_two_mul (a b : Nat) : (2 * a + 1) ^^^ (2 * b) = 2 * (a ^^^ b) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_xor, testBit_two_mul_add_one_zero, testBit_two_mul_zero, testBit_two_mul_add_one_zero]; rfl
  | succ j => rw [Nat.testBit_xor, testBit_two_mul_add_one_succ, testBit_two_mul_succ, testBit_two_mul_add_one_succ, Nat.testBit_xor]

theorem xor_odd_odd (a b : Nat) : (2 * a + 1) ^^^ (2 * b + 1) = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_xor, testBit_two_mul_add_one_zero, testBit_two_mul_add_one_zero, testBit_two_mul_zero]; rfl
  | succ j => rw [Nat.testBit_xor, testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ, testBit_two_mul_succ, Nat.testBit_xor]

theorem and_two_mul_two_mul (a b : Nat) : (2 * a) &&& (2 * b) = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_and, testBit_two_mul_zero, testBit_two_mul_zero, testBit_two_mul_zero]; rfl
  | succ j => rw [Nat.testBit_and, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ, Nat.testBit_and]

theorem mobius_zero (f : Nat → Int) : mobius f 0 = f 0 := by
  unfold mobius
  rw [sumSubmasks_zero]
  simp [popcount_zero]

theorem mobius_two_mul (f : Nat → Int) (h : Nat) :
    mobius f (2 * h) = mobius (fun k => f (2 * k)) h := by
  unfold mobius
  rw [sumSubmasks_two_mul]
  apply sumSubmasks_congr
  intro k _
  rw [xor_two_mul_two_mul, popcount_two_mul]

theorem mobius_two_mul_add_one (f : Nat → Int) (h : Nat) :
    mobius f (2 * h + 1) = mobius (fun k => f (2 * k + 1) - f (2 * k)) h := by
  unfold mobius
  rw [sumSubmasks_two_mul_add_one]
  apply sumSubmasks_congr
  intro k _
  rw [xor_odd_two_mul, xor_odd_odd, popcount_two_mul_add_one, popcount_two_mul]
  by_cases hp : popcount (h ^^^ k) % 2 = 0
  · have hp1 : (popcount (h ^^^ k) + 1) % 2 ≠ 0 := by omega
    simp [hp, hp1]; omega
  · have hp1 : (popcount (h ^^^ k) + 1) % 2 = 0 := by omega
    simp [hp, hp1]; omega

theorem mobius_add (f g : Nat → Int) (j : Nat) :
    mobius (fun k => f k + g k) j = mobius f j + mobius g j := by
  unfold mobius
  rw [← sumSubmasks_add]
  apply sumSubmasks_congr
  intro k _; rw [Int.mul_add]

theorem mobius_mul_left (c : Int) (f : Nat → Int) (j : Nat) :
    mobius (fun k => c * f k) j = c * mobius f j := by
  unfold mobius
  rw [← sumSubmasks_mul_left]
  apply sumSubmasks_congr
  intro k _
  rw [← Int.mul_assoc, Int.mul_comm _ c, Int.mul_assoc]

/-- Exact integer-indexed binomial coefficient (`0` outside `0 <= k <= n`). -/
def binomZ : Nat → Int → Int
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => binomZ n k + binomZ n (k - 1)

/-- Standard `Nat` Pascal binomial coefficient, proved equal to `binomZ`. -/
def binomNat : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomNat n (k + 1) + binomNat n k

/-- Even-indexed binomial extractor corresponding to `[x^b] (1 + x^2)^a`. -/
def binomZEven (a : Nat) (b : Int) : Int :=
  if b % 2 = 0 then binomZ a (b / 2) else 0

/-- Shifted Lucas-mask Mobius derivative of binomial coefficients:
    `Delta n j c = ∑_{k <=_2 j} (-1)^popcount(j ^^^ k) * C(n, k - c)`. -/
def Delta (n j : Nat) (c : Int) : Int :=
  mobius (fun k => binomZ n ((k : Int) - c)) j

/-! ### Exact Bit-Slice Recurrences for `Delta` -/

/-- Closed-form indicator for State 0 leading bit `alpha(N, j) = [j <=_2 E(N)]`. -/
def alphaCF (N j : Nat) : Bool :=
  (j &&& endpointMask N) == j

/-- Structurally recursive lowest set bit `N & -N` (`0` if `N = 0`). -/
def lowBitAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, N => if N = 0 then 0 else if N % 2 = 0 then 2 * lowBitAux fuel (N / 2) else 1

def lowBit (N : Nat) : Nat := lowBitAux N N

/-- Closed-form indicator for State 1 leading bit `beta(N, j)`:
    `j` contains `lowBit N` and `(j ^^^ lowBit N) <=_2 E(N)` (and `false` for `N = 0`). -/
def betaCF (N j : Nat) : Bool :=
  if N == 0 then false
  else ((j &&& lowBit N) != 0) && (((j ^^^ lowBit N) &&& endpointMask N) == (j ^^^ lowBit N))

def boolToInt (b : Bool) : Int := if b then 1 else 0

/-- Excess-`s` 2-adic bit-smoothness on the Lucas cube of `n`:
    `∀ j <=_2 n, 2^(popcount j + s) | mobius f j`. -/
def BitExcess (n s : Nat) (f : Nat → Int) : Prop :=
  ∀ j, Submask j n → (2 : Int) ^ (popcount j + s) ∣ mobius f j

/-- Rank-0 Bit-Smooth Unit with spike mask `E <=_2 n`:
    `∀ j <=_2 n, mobius f j ≡ 2^(popcount j) * [j <=_2 E]  (mod 2^(popcount j + 1))`. -/
def BitSmooth (n E : Nat) (f : Nat → Int) : Prop :=
  Submask E n ∧
  ∀ j, Submask j n →
    (2 : Int) ^ (popcount j + 1) ∣
      (mobius f j - (2 : Int) ^ (popcount j) * boolToInt ((j &&& E) == j))

/-- Rank-`s` Bit-Smooth Unit (`s >= 1`):
    `f 0 = 1` (exact unit normalization) and `∀ 0 ≠ j <=_2 n, 2^(popcount j + s) | mobius f j`. -/
def BitUnit (n s : Nat) (f : Nat → Int) : Prop :=
  f 0 = 1 ∧
  ∀ j, Submask j n → j ≠ 0 → (2 : Int) ^ (popcount j + s) ∣ mobius f j

theorem bitExcess_mono {n s1 s2 : Nat} {f : Nat → Int} (hle : s1 ≤ s2)
    (h : BitExcess n s2 f) : BitExcess n s1 f := by
  intro j hj
  exact dvd_two_pow_mono (by omega) (h j hj)

theorem bitExcess_add {n s : Nat} {f g : Nat → Int}
    (hf : BitExcess n s f) (hg : BitExcess n s g) :
    BitExcess n s (fun k => f k + g k) := by
  intro j hj
  rw [mobius_add]
  exact dvd_add_of_dvd (hf j hj) (hg j hj)

theorem bitExcess_scale_two {n s : Nat} {f : Nat → Int}
    (hf : BitExcess n s f) :
    BitExcess n (s + 1) (fun k => 2 * f k) := by
  intro j hj
  rw [mobius_mul_left]
  exact dvd_two_mul_of_dvd (hf j hj)

theorem bitSmooth_to_bitExcess0 {n E : Nat} {f : Nat → Int}
    (h : BitSmooth n E f) : BitExcess n 0 f := by
  intro j hj
  have h1 := dvd_two_pow_mono (a := popcount j) (b := popcount j + 1) (by omega) (h.2 j hj)
  have h2 : (2 : Int) ^ popcount j ∣ (2 : Int) ^ popcount j * boolToInt ((j &&& E) == j) := ⟨_, rfl⟩
  have hsum := dvd_add_of_dvd h1 h2
  simpa [Int.sub_add_cancel] using hsum

/-- **Stage 2 Law 1 (Core Bit-Slice Product Divisibility):**
    `BitExcess n s1 u` and `BitExcess n s2 v` imply `BitExcess n (s1 + s2) (u * v)`. -/
theorem bitExcess_mul {n s1 s2 : Nat} {u v : Nat → Int}
    (hu : BitExcess n s1 u) (hv : BitExcess n s2 v) :
    BitExcess n (s1 + s2) (fun k => u k * v k) := by
  induction n using nat_strong_ind generalizing s1 s2 u v with
  | step n ih =>
    intro j hj
    by_cases hn : n = 0
    · subst hn
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (submask_le hj)
      subst hj0
      rw [mobius_zero, popcount_zero, Nat.zero_add]
      have hu0 := hu 0 (submask_zero 0); rw [mobius_zero, popcount_zero, Nat.zero_add] at hu0
      have hv0 := hv 0 (submask_zero 0); rw [mobius_zero, popcount_zero, Nat.zero_add] at hv0
      obtain ⟨qu, hqu⟩ := hu0
      obtain ⟨qv, hqv⟩ := hv0
      refine ⟨qu * qv, ?_⟩
      rw [hqu, hqv, Int.pow_add]
      rw [Int.mul_assoc, ← Int.mul_assoc qu, Int.mul_comm qu, Int.mul_assoc, ← Int.mul_assoc]
    · by_cases hnp : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by omega
        rw [hnm] at hj hu hv
        obtain ⟨hj0, hjm⟩ := (submask_two_mul_iff j m).mp hj
        let h := j / 2
        have hjh : j = 2 * h := by omega
        rw [hjh, popcount_two_mul, mobius_two_mul]
        have hu0 : BitExcess m s1 (fun k => u (2 * k)) := by
          intro a ha
          have := hu (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have hv0 : BitExcess m s2 (fun k => v (2 * k)) := by
          intro a ha
          have := hv (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        exact ih m (by omega) hu0 hv0 h hjm
      · let m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        rw [hnm] at hj hu hv
        have hjm : Submask (j / 2) m := (submask_two_mul_add_one_iff j m).mp hj
        let h := j / 2
        have hu0 : BitExcess m s1 (fun k => u (2 * k)) := by
          intro a ha
          have := hu (2 * a) ((submask_two_mul_left_odd_right a m).mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have hv0 : BitExcess m s2 (fun k => v (2 * k)) := by
          intro a ha
          have := hv (2 * a) ((submask_two_mul_left_odd_right a m).mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have hdu : BitExcess m (s1 + 1) (fun k => u (2 * k + 1) - u (2 * k)) := by
          intro a ha
          have := hu (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
          rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
          exact dvd_two_pow_mono (by omega) this
        have hdv : BitExcess m (s2 + 1) (fun k => v (2 * k + 1) - v (2 * k)) := by
          intro a ha
          have := hv (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
          rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
          exact dvd_two_pow_mono (by omega) this
        by_cases hjp : j % 2 = 0
        · have hjh : j = 2 * h := by omega
          rw [hjh, popcount_two_mul, mobius_two_mul]
          exact ih m (by omega) hu0 hv0 h hjm
        · have hjh : j = 2 * h + 1 := by omega
          rw [hjh, popcount_two_mul_add_one, mobius_two_mul_add_one]
          have hdecomp : (fun k => u (2 * k + 1) * v (2 * k + 1) - u (2 * k) * v (2 * k)) =
              (fun k => u (2 * k) * (v (2 * k + 1) - v (2 * k)) +
                        (u (2 * k + 1) - u (2 * k)) * v (2 * k) +
                        (u (2 * k + 1) - u (2 * k)) * (v (2 * k + 1) - v (2 * k))) := by
            funext k
            rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_sub, Int.mul_sub]
            omega
          rw [hdecomp, mobius_add, mobius_add]
          have h1 := ih m (by omega) hu0 hdv h hjm
          have h2 := ih m (by omega) hdu hv0 h hjm
          have h3 := ih m (by omega) hdu hdv h hjm
          exact dvd_add_of_dvd
            (dvd_add_of_dvd (dvd_two_pow_mono (by omega) h1) (dvd_two_pow_mono (by omega) h2))
            (dvd_two_pow_mono (by omega) h3)

/-- Helper: Slicing a `BitSmooth (2*m+1) E f` function into `f_0` and `d_f`. -/
theorem bitSmooth_slice_even {m E : Nat} {f : Nat → Int}
    (hf : BitSmooth (2 * m + 1) E f) :
    BitSmooth m (E / 2) (fun k => f (2 * k)) := by
  refine ⟨(submask_two_mul_add_one_iff E m).mp hf.1, fun h hh => ?_⟩
  have h1 := hf.2 (2 * h) ((submask_two_mul_left_odd_right h m).mpr hh)
  rw [popcount_two_mul, mobius_two_mul] at h1
  have hmask : ((2 * h &&& E) == 2 * h) = ((h &&& (E / 2)) == h) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    change Submask (2 * h) E ↔ Submask h (E / 2)
    by_cases hEp : E % 2 = 0
    · have hE2 : E = 2 * (E / 2) := by omega
      conv => lhs; rw [hE2]
      exact submask_two_mul_left_two_mul_right h (E / 2)
    · have hE2 : E = 2 * (E / 2) + 1 := by omega
      conv => lhs; rw [hE2]
      exact submask_two_mul_left_odd_right h (E / 2)
  rwa [hmask] at h1

theorem bitSmooth_slice_diff_evenE {m E : Nat} {f : Nat → Int}
    (hE : E % 2 = 0) (hf : BitSmooth (2 * m + 1) E f) :
    BitExcess m 2 (fun k => f (2 * k + 1) - f (2 * k)) := by
  intro h hh
  have h1 := hf.2 (2 * h + 1) ((submask_odd_left_odd_right h m).mpr hh)
  rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
  have hmask : ((2 * h + 1 &&& E) == 2 * h + 1) = false := by
    simp only [beq_eq_false_iff_ne]
    change ¬ Submask (2 * h + 1) E
    have hE2 : E = 2 * (E / 2) := by omega
    rw [hE2, submask_two_mul_iff]; omega
  rw [hmask] at h1
  simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero] at h1
  exact dvd_two_pow_mono (by omega) h1

/-- **Stage 2 Law 2 (Squaring Jump Law):**
    For ANY `f ∈ BitSmooth n E` with `f 0 = 1`, its square `f^2` jumps straight to `BitUnit n 2`! -/
theorem bitSmooth_sq_jump {n E : Nat} {f : Nat → Int}
    (hf0 : f 0 = 1) (hf : BitSmooth n E f) :
    BitUnit n 2 (fun k => f k * f k) := by
  refine ⟨by simp [hf0], ?_⟩
  induction n using nat_strong_ind generalizing E f with
  | step n ih =>
    intro j hj hjne
    by_cases hn : n = 0
    · subst hn
      exact absurd (Nat.eq_zero_of_le_zero (submask_le hj)) hjne
    · by_cases hnp : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by omega
        rw [hnm] at hj hf
        obtain ⟨hj0, hjm⟩ := (submask_two_mul_iff j m).mp hj
        obtain ⟨hE0, hEm⟩ := (submask_two_mul_iff E m).mp hf.1
        let h := j / 2
        have hjh : j = 2 * h := by omega
        have hne : h ≠ 0 := by omega
        rw [hjh, popcount_two_mul, mobius_two_mul]
        have hf' : BitSmooth m (E / 2) (fun k => f (2 * k)) := by
          refine ⟨hEm, fun a ha => ?_⟩
          have h1 := hf.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha)
          rw [popcount_two_mul, mobius_two_mul] at h1
          have hE2 : E = 2 * (E / 2) := by omega
          have hmask : ((2 * a &&& E) == 2 * a) = ((a &&& (E / 2)) == a) := by
            conv => lhs; rw [hE2, and_two_mul_two_mul]
            exact beq_two_mul_eq (a &&& (E / 2)) a
          rwa [hmask] at h1
        exact ih m (by omega) (by simpa using hf0) hf' h hjm hne
      · let m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        rw [hnm] at hj hf
        have hjm : Submask (j / 2) m := (submask_two_mul_add_one_iff j m).mp hj
        let h := j / 2
        have hf_ev := bitSmooth_slice_even hf
        by_cases hjp : j % 2 = 0
        · have hjh : j = 2 * h := by omega
          have hne : h ≠ 0 := by omega
          rw [hjh, popcount_two_mul, mobius_two_mul]
          exact ih m (by omega) (by simpa using hf0) hf_ev h hjm hne
        · have hjh : j = 2 * h + 1 := by omega
          rw [hjh, popcount_two_mul_add_one, mobius_two_mul_add_one]
          have hfact : (fun k => f (2 * k + 1) * f (2 * k + 1) - f (2 * k) * f (2 * k)) =
              (fun k => (f (2 * k + 1) - f (2 * k)) * (2 * f (2 * k) + (f (2 * k + 1) - f (2 * k)))) := by
            funext k
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_sub]
            have hc1 : f (2 * k + 1) * (2 * f (2 * k)) = 2 * (f (2 * k) * f (2 * k + 1)) := by
              rw [Int.mul_comm (f (2 * k + 1)), ← Int.mul_assoc, Int.mul_assoc 2]
            have hc2 : f (2 * k) * (2 * f (2 * k)) = 2 * (f (2 * k) * f (2 * k)) := by
              rw [Int.mul_comm (f (2 * k)), Int.mul_assoc]
            have hc3 : f (2 * k + 1) * f (2 * k) = f (2 * k) * f (2 * k + 1) := Int.mul_comm _ _
            omega
          rw [hfact]
          by_cases hEp : E % 2 = 0
          · have hdf := bitSmooth_slice_diff_evenE hEp hf
            have h2f0 := bitExcess_scale_two (bitSmooth_to_bitExcess0 hf_ev)
            have hsum := bitExcess_add h2f0 (bitExcess_mono (by omega) hdf)
            have hprod := bitExcess_mul hdf hsum h hjm
            exact dvd_two_pow_mono (by omega) hprod
          · have hdf : BitExcess m 1 (fun k => f (2 * k + 1) - f (2 * k)) := by
              intro a ha
              have h1 := bitSmooth_to_bitExcess0 hf (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
              rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
              exact dvd_two_pow_mono (by omega) h1
            have hsum : BitExcess m 2 (fun k => 2 * f (2 * k) + (f (2 * k + 1) - f (2 * k))) := by
              intro a ha
              rw [mobius_add, mobius_mul_left]
              have h0 := dvd_two_mul_of_dvd (hf_ev.2 a ha)
              have h1 := hf.2 (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
              rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
              have hE2 : E = 2 * (E / 2) + 1 := by omega
              have hmask : ((2 * a + 1 &&& E) == 2 * a + 1) = ((a &&& (E / 2)) == a) := by
                apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
                change Submask (2 * a + 1) E ↔ Submask a (E / 2)
                conv => lhs; rw [hE2]
                exact submask_odd_left_odd_right a (E / 2)
              rw [hmask] at h1
              have hadd := dvd_add_of_dvd h0 h1
              have hpow : (2 : Int) * (2 : Int) ^ popcount a = (2 : Int) ^ (popcount a + 1) := by
                rw [Int.pow_succ, Int.mul_comm]
              have h2b : (2 : Int) ^ (popcount a + 1 + 1) ∣
                  ((2 : Int) ^ (popcount a + 1) * boolToInt ((a &&& (E / 2)) == a) +
                   (2 : Int) ^ (popcount a + 1) * boolToInt ((a &&& (E / 2)) == a)) := by
                exact ⟨boolToInt ((a &&& (E / 2)) == a), (two_pow_succ_mul_eq_add _ _).symm⟩
              have htot := dvd_add_of_dvd hadd h2b
              have hsimp : 2 * (mobius (fun k => f (2 * k)) a - (2 : Int) ^ popcount a * boolToInt ((a &&& (E / 2)) == a)) +
                  (mobius (fun k => f (2 * k + 1) - f (2 * k)) a - (2 : Int) ^ (popcount a + 1) * boolToInt ((a &&& (E / 2)) == a)) +
                  ((2 : Int) ^ (popcount a + 1) * boolToInt ((a &&& (E / 2)) == a) +
                   (2 : Int) ^ (popcount a + 1) * boolToInt ((a &&& (E / 2)) == a)) =
                  2 * mobius (fun k => f (2 * k)) a + mobius (fun k => f (2 * k + 1) - f (2 * k)) a := by
                rw [Int.mul_sub, ← Int.mul_assoc, hpow]; omega
              rw [hsimp] at htot
              exact dvd_two_pow_mono (by omega) htot
            have hprod := bitExcess_mul hdf hsum h hjm
            exact dvd_two_pow_mono (by omega) hprod

/-- Sharpness CE-4: In the abstract Squaring Jump Law (`bitSmooth_sq_jump`), assuming ONLY
    `BitExcess n 0 f` (without the exact spike-mask law `[j <=_2 E]`) is INSUFFICIENT:
    `f_ce = [1, 3, 1, 7]` on `n = 3` satisfies `BitExcess 3 0 f_ce` and `f_ce 0 = 1`,
    yet `mobius (f_ce^2) 3 = 40` is NOT divisible by `2^(popcount 3 + 2) = 16`. -/
def f_ce (k : Nat) : Int :=
  match k with
  | 0 => 1
  | 1 => 3
  | 2 => 1
  | 3 => 7
  | _ => 0

end LucasMaskEngine

/-! ## Section 8: Kernel Axiom Audits -/
