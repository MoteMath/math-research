import TwoAdicCarryFirewallCovers.Defs

/-!
# Verified Lean 4 2-Adic Compactness & Carry-Firewall Binary-Prefix-Tree Cover Engine

Standalone Lean 4.34.1 (zero Mathlib, zero `sorry`, zero custom axioms, pure kernel `decide`).

## Architecture
1. **Layer 1 (`CoverTree`)**: Universal 2-adic compactness meta-theorem lifting any
   local leaf invariant over clopen balls `B(r, d) = {r + q * 2^d | q : Nat}` to `∀ n : Nat`,
   plus exact dyadic Haar partition-of-unity (`treeHaarNum D t = 2^D`).
2. **Layer 2 (`Expr` Reflection Compiler)**: Reflected pure-silicon bitwise-arithmetic AST
   (`var`, `const`, `add`, `mul`, `xor`, `and`, `or`, `shl`, `shr`, `clearBit`, `comp`) with
   exact structural modulus-demand analyzer `need` (capturing 2-adic contraction under `shl`,
   expansion under `shr`, compositional lookahead under `comp`, and the Carry-Firewall
   lookahead reduction `need (clearBit e k) (k + 1) = need e k`), discharging universal
   non-collision (`∀ n, eval f n ≠ eval g n`) and exact piecewise-constant 2-adic valuation
   ceilings (`∀ n, ¬ (2^(M+1) ∣ eval f n)`).
3. **Layer 3 (`FirewallDescent`)**: Local Carry-Firewall + Affine-Lipschitz descent engine
   for any 1-Lipschitz silicon odd-step core with linear upper envelope, certifying
   universal bounded stopping times (`∀ n ≥ N0, ∃ t ≤ S, f^[t] n < n`) and lifting via
   well-founded strong induction to global convergence (`∀ n, ∃ m, f^[m] n < N0`).
-/

namespace AdicCompactness

/-! ## Section 0: Fundamental Pure-Silicon Bitwise & Modular Lemmas -/


theorem pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

theorem clearBitNat_le (x k : Nat) : clearBitNat x k ≤ x := by
  unfold clearBitNat
  have h1 : x % 2 ^ k ≤ x % 2 ^ (k + 1) := by
    have hdiv : 2 ^ k ∣ 2 ^ (k + 1) := ⟨2, by rw [Nat.pow_succ]⟩
    have hmod : x % 2 ^ k = (x % 2 ^ (k + 1)) % 2 ^ k := by
      rw [Nat.mod_mod_of_dvd x hdiv]
    rw [hmod]
    exact Nat.mod_le _ _
  have h2 : (x / 2 ^ (k + 1)) * 2 ^ (k + 1) + x % 2 ^ (k + 1) = x := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x (2 ^ (k + 1))
  omega

/-- **The Carry-Firewall Congruence Lemma**:
Clearing bit `k` forces bit `k` to `0`, so `clearBitNat x k % 2^(k+1) = x % 2^k`!
Thus `k + 1` low bits of `clearBitNat x k` depend ONLY on `k` low bits of `x`. -/
theorem clearBitNat_mod_succ (x k : Nat) :
    clearBitNat x k % 2 ^ (k + 1) = x % 2 ^ k := by
  unfold clearBitNat
  rw [Nat.mul_add_mod_self_right]
  have hlt : x % 2 ^ k < 2 ^ (k + 1) := by
    have h1 : x % 2 ^ k < 2 ^ k := Nat.mod_lt x (pow2_pos k)
    have h2 : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    omega
  exact Nat.mod_eq_of_lt hlt

/-- Below bit `k`, clearing bit `k` has no effect on the low `d` bits. -/
theorem clearBitNat_mod_le (x k d : Nat) (h : d ≤ k) :
    clearBitNat x k % 2 ^ d = x % 2 ^ d := by
  unfold clearBitNat
  have hd1 : 2 ^ d ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ_of_le h)
  have hd2 : 2 ^ d ∣ 2 ^ k := Nat.pow_dvd_pow 2 h
  rcases hd1 with ⟨m, hm⟩
  rw [hm]
  have hmul : (x / (2 ^ d * m)) * (2 ^ d * m) = 2 ^ d * ((x / (2 ^ d * m)) * m) := by
    rw [Nat.mul_left_comm]
  rw [hmul, Nat.mul_add_mod]
  exact Nat.mod_mod_of_dvd x hd2

/-- Above bit `k`, `clearBitNat x k % 2^d` depends only on `x % 2^d`. -/
theorem clearBitNat_mod_gt (x k d : Nat) (h : k + 1 ≤ d) :
    clearBitNat x k % 2 ^ d = clearBitNat (x % 2 ^ d) k := by
  unfold clearBitNat
  have hdiv1 : 2 ^ (k + 1) ∣ 2 ^ d := Nat.pow_dvd_pow 2 h
  have hdiv0 : 2 ^ k ∣ 2 ^ d := Nat.pow_dvd_pow 2 (Nat.le_of_succ_le h)
  rcases hdiv1 with ⟨m, hm⟩
  have hq : (x / 2 ^ (k + 1)) % m = (x % 2 ^ d) / 2 ^ (k + 1) := by
    rw [hm, Nat.mod_mul_right_div_self]
  have hlt : ((x % 2 ^ d) / 2 ^ (k + 1)) * 2 ^ (k + 1) + (x % 2 ^ d) % 2 ^ k < 2 ^ d := by
    have hle : ((x % 2 ^ d) / 2 ^ (k + 1)) * 2 ^ (k + 1) + (x % 2 ^ d) % 2 ^ k ≤ x % 2 ^ d := by
      exact clearBitNat_le (x % 2 ^ d) k
    have hlt2 : x % 2 ^ d < 2 ^ d := Nat.mod_lt x (pow2_pos d)
    omega
  have hmodk : x % 2 ^ k = (x % 2 ^ d) % 2 ^ k := by
    rw [Nat.mod_mod_of_dvd x hdiv0]
  have hsplit : x / 2 ^ (k + 1) = m * (x / 2 ^ (k + 1) / m) + (x / 2 ^ (k + 1)) % m := by
    exact (Nat.div_add_mod (x / 2 ^ (k + 1)) m).symm
  calc
    ((x / 2 ^ (k + 1)) * 2 ^ (k + 1) + x % 2 ^ k) % 2 ^ d
      = ((m * (x / 2 ^ (k + 1) / m) + (x / 2 ^ (k + 1)) % m) * 2 ^ (k + 1) + x % 2 ^ k) % 2 ^ d := by
          rw [← hsplit]
    _ = (2 ^ d * (x / 2 ^ (k + 1) / m) + ((x / 2 ^ (k + 1)) % m * 2 ^ (k + 1) + x % 2 ^ k)) % 2 ^ d := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (x / 2 ^ (k + 1) / m) (2 ^ (k + 1)),
              ← Nat.mul_assoc, Nat.mul_comm m (2 ^ (k + 1)), ← hm, Nat.add_assoc]
    _ = (((x / 2 ^ (k + 1)) % m) * 2 ^ (k + 1) + x % 2 ^ k) % 2 ^ d := by
          rw [Nat.mul_add_mod]
    _ = (((x % 2 ^ d) / 2 ^ (k + 1)) * 2 ^ (k + 1) + (x % 2 ^ d) % 2 ^ k) % 2 ^ d := by
          rw [hq, hmodk]
    _ = ((x % 2 ^ d) / 2 ^ (k + 1)) * 2 ^ (k + 1) + (x % 2 ^ d) % 2 ^ k := by
          exact Nat.mod_eq_of_lt hlt

/-- Bit-level characterization of `clearBitNat`: identical to clearing wire `k`. -/
theorem testBit_clearBitNat (x k i : Nat) :
    (clearBitNat x k).testBit i = (decide (i ≠ k) && x.testBit i) := by
  by_cases hi : i < k
  · have hmod := clearBitNat_mod_le x k (i + 1) (Nat.succ_le_of_lt hi)
    have h1 : (clearBitNat x k).testBit i = (clearBitNat x k % 2 ^ (i + 1)).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    have h2 : x.testBit i = (x % 2 ^ (i + 1)).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    have hne : i ≠ k := by omega
    rw [h1, h2, hmod]; simp [hne]
  · by_cases heq : i = k
    · subst heq
      have h1 : (clearBitNat x i).testBit i = (clearBitNat x i % 2 ^ (i + 1)).testBit i := by
        rw [Nat.testBit_mod_two_pow]; simp
      rw [h1, clearBitNat_mod_succ]
      have hlt : x % 2 ^ i < 2 ^ i := Nat.mod_lt x (pow2_pos i)
      rw [Nat.testBit_lt_two_pow hlt]; simp
    · have hne : i ≠ k := heq
      simp only [hne, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
      have hdiv : clearBitNat x k / 2 ^ (k + 1) = x / 2 ^ (k + 1) := by
        unfold clearBitNat
        rw [Nat.mul_comm, Nat.mul_add_div (pow2_pos (k + 1))]
        have hlt : x % 2 ^ k < 2 ^ (k + 1) := by
          have h1 := Nat.mod_lt x (pow2_pos k)
          have h2 : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
          omega
        rw [Nat.div_eq_of_lt hlt, Nat.add_zero]
      have hi_eq : i = (k + 1) + (i - (k + 1)) := by omega
      have hpow : 2 ^ i = 2 ^ (k + 1) * 2 ^ (i - (k + 1)) := by
        calc
          2 ^ i = 2 ^ ((k + 1) + (i - (k + 1))) := by rw [← hi_eq]
          _ = 2 ^ (k + 1) * 2 ^ (i - (k + 1)) := Nat.pow_add 2 (k + 1) (i - (k + 1))
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow,
          ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

/-- Standard bitwise upper bound `a ^^^ b ≤ a + b` proved cleanly by strong induction. -/
theorem xor_le_add (a b : Nat) : a ^^^ b ≤ a + b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha; simp
    · have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by decide)
      have hih := ih (a / 2) hlt (b / 2)
      have hsplit : a ^^^ b = 2 * ((a / 2) ^^^ (b / 2)) + ((a % 2) ^^^ (b % 2)) := by
        apply Nat.eq_of_testBit_eq
        intro i
        cases i with
        | zero =>
          simp [Nat.testBit_zero]
        | succ j =>
          have hbit : ((a % 2) ^^^ (b % 2)) < 2 := by
            have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
            have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
            rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> simp [ha2, hb2]
          rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
          rw [Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt hbit, Nat.add_zero]
          rw [Nat.testBit_xor]
      have hbit_le : ((a % 2) ^^^ (b % 2)) ≤ a % 2 + b % 2 := by
        have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> simp [ha2, hb2]
      omega

/-- Helper identities for splitting a clopen ball `B(r, d)` into even/odd sub-balls. -/
theorem ball_split_even (r d q : Nat) (hq : q % 2 = 0) :
    r + q * 2 ^ d = r + (q / 2) * 2 ^ (d + 1) := by
  have h1 : q = (q / 2) * 2 := by omega
  calc
    r + q * 2 ^ d = r + ((q / 2) * 2) * 2 ^ d := by rw [← h1]
    _ = r + (q / 2) * (2 ^ d * 2) := by rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ d)]
    _ = r + (q / 2) * 2 ^ (d + 1) := by rw [← Nat.pow_succ]

theorem ball_split_odd (r d q : Nat) (hq : q % 2 ≠ 0) :
    r + q * 2 ^ d = (r + 2 ^ d) + (q / 2) * 2 ^ (d + 1) := by
  have h1 : q = (q / 2) * 2 + 1 := by omega
  calc
    r + q * 2 ^ d = r + ((q / 2) * 2 + 1) * 2 ^ d := by rw [← h1]
    _ = r + ((q / 2) * (2 ^ d * 2) + 2 ^ d) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ d)]
    _ = r + (2 ^ d + (q / 2) * 2 ^ (d + 1)) := by
          rw [← Nat.pow_succ, Nat.add_comm ((q / 2) * 2 ^ (d + 1)) (2 ^ d)]
    _ = (r + 2 ^ d) + (q / 2) * 2 ^ (d + 1) := (Nat.add_assoc _ _ _).symm

/-- Bitwise monotonicity of `mod 2^d` for XOR, AND, OR, SHL, SHR. -/
theorem xor_mod_two_pow (a b d : Nat) :
    (a ^^^ b) % 2 ^ d = (a % 2 ^ d) ^^^ (b % 2 ^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases h : i < d <;> simp [h]

theorem and_mod_two_pow (a b d : Nat) :
    (a &&& b) % 2 ^ d = (a % 2 ^ d) &&& (b % 2 ^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_and]
  by_cases h : i < d <;> simp [h]

theorem or_mod_two_pow (a b d : Nat) :
    (a ||| b) % 2 ^ d = (a % 2 ^ d) ||| (b % 2 ^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases h : i < d <;> simp [h]

theorem shl_mod_two_pow (a s d : Nat) :
    (a <<< s) % 2 ^ d = ((a % 2 ^ (d - s)) <<< s) % 2 ^ d := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases h1 : i < d
  · by_cases h2 : s ≤ i
    · have h3 : i - s < d - s := by omega
      simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

theorem shr_mod_two_pow (a s d : Nat) :
    (a >>> s) % 2 ^ d = (a % 2 ^ (d + s)) >>> s := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h : i < d
  · have h2 : s + i < d + s := by omega
    simp [h, h2]
  · have h2 : ¬ (s + i < d + s) := by omega
    simp [h, h2]

theorem mod_pow2_of_le {a d1 d2 : Nat} (h : d1 ≤ d2) :
    (a % 2 ^ d2) % 2 ^ d1 = a % 2 ^ d1 :=
  Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 2 h)

/-! ## Section 1: Layer 1 — Universal 2-Adic Compactness Cover Engine (`CoverTree`) -/


/-- Preorder linear-time decoder (`0` = branch, `c + 1` = leaf `c`). -/
def parsePreorderStep (tok : Nat) (stk : List (CoverTree Nat)) : List (CoverTree Nat) :=
  match tok with
  | 0 => match stk with
    | l :: r :: rest => CoverTree.branch l r :: rest
    | _ => []
  | c + 1 => CoverTree.leaf c :: stk

def decodeCoverTree (toks : List Nat) : CoverTree Nat :=
  match toks.foldr parsePreorderStep [] with
  | [t] => t
  | _ => CoverTree.leaf 0


/-- Number of leaves in a cover tree. -/
def treeLeaves {L : Type} : CoverTree L → Nat
  | CoverTree.leaf _ => 1
  | CoverTree.branch t0 t1 => treeLeaves t0 + treeLeaves t1

/-- Maximum depth of a cover tree. -/
def treeMaxDepth {L : Type} : CoverTree L → Nat
  | CoverTree.leaf _ => 0
  | CoverTree.branch t0 t1 => 1 + max (treeMaxDepth t0) (treeMaxDepth t1)

/-- Maximum `Nat` certificate label across all leaves. -/
def treeMaxLabel : CoverTree Nat → Nat
  | CoverTree.leaf c => c
  | CoverTree.branch t0 t1 => max (treeMaxLabel t0) (treeMaxLabel t1)

/-- Scaled 2-adic Haar measure numerator at resolution `2^D`: `∑_{leaf(d)} 2^(D - d)`. -/
def treeHaarNum {L : Type} (D : Nat) (d : Nat := 0) : CoverTree L → Nat
  | CoverTree.leaf _ => 2 ^ (D - d)
  | CoverTree.branch t0 t1 => treeHaarNum D (d + 1) t0 + treeHaarNum D (d + 1) t1

/-- Exact 2-adic partition-of-unity: every finite cover tree has Haar measure `1`. -/
theorem coverTree_haar_aux {L : Type} (t : CoverTree L) :
    ∀ D d, d + treeMaxDepth t ≤ D → treeHaarNum D d t = 2 ^ (D - d) := by
  induction t with
  | leaf _ =>
    intro D d _
    rfl
  | branch t0 t1 ih0 ih1 =>
    intro D d hD
    simp only [treeMaxDepth] at hD
    have h0 : d + 1 + treeMaxDepth t0 ≤ D := by omega
    have h1 : d + 1 + treeMaxDepth t1 ≤ D := by omega
    simp only [treeHaarNum, ih0 D (d + 1) h0, ih1 D (d + 1) h1]
    have hpos : D - d = (D - (d + 1)) + 1 := by omega
    rw [hpos, Nat.pow_succ]
    omega

theorem coverTree_haar_partition {L : Type} (t : CoverTree L) (D : Nat)
    (hD : treeMaxDepth t ≤ D) : treeHaarNum D 0 t = 2 ^ D := by
  have h := coverTree_haar_aux t D 0 (by omega)
  simpa using h

/-- Inductive soundness over any clopen ball `B(r, d) = {r + q * 2^d | q : Nat}`
with `r < 2^d`. -/
theorem coverTree_sound_aux {L : Type} {P : Nat → Prop}
    (valid : Nat → Nat → L → Bool)
    (hleaf : ∀ r d cert, r < 2 ^ d → valid r d cert = true → ∀ q, P (r + q * 2 ^ d)) :
    ∀ (t : CoverTree L) (r d : Nat),
      r < 2 ^ d → checkCover valid r d t = true → ∀ q, P (r + q * 2 ^ d) := by
  intro t
  induction t with
  | leaf cert =>
    intro r d hr hchk q
    exact hleaf r d cert hr hchk q
  | branch t0 t1 ih0 ih1 =>
    intro r d hr hchk q
    simp only [checkCover, Bool.and_eq_true] at hchk
    rcases hchk with ⟨h0, h1⟩
    have hr0 : r < 2 ^ (d + 1) := by
      have : 2 ^ d ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ d)
      omega
    have hr1 : r + 2 ^ d < 2 ^ (d + 1) := by
      rw [Nat.pow_succ]; omega
    by_cases hq : q % 2 = 0
    · rw [ball_split_even r d q hq]
      exact ih0 r (d + 1) hr0 h0 (q / 2)
    · rw [ball_split_odd r d q hq]
      exact ih1 (r + 2 ^ d) (d + 1) hr1 h1 (q / 2)

/-- **Universal 2-Adic Compactness Soundness Meta-Theorem**:
Any checked finite binary prefix tree discharges `∀ n : Nat, P n`. -/
theorem coverTree_sound {L : Type} {P : Nat → Prop}
    (valid : Nat → Nat → L → Bool)
    (hleaf : ∀ r d cert, r < 2 ^ d → valid r d cert = true → ∀ q, P (r + q * 2 ^ d))
    (t : CoverTree L) (hchk : checkCover valid 0 0 t = true) :
    ∀ n : Nat, P n := by
  intro n
  have h := coverTree_sound_aux valid hleaf t 0 0 (by decide) hchk n
  simpa using h

/-! ## Section 2: Layer 2 — Reflected 2-Adic `Expr` Compiler & Lookahead `need` -/



/-- Structural 2-adic lookahead / modulus-demand function:
`eval e n % 2^d` depends ONLY on `n % 2^(need e d)`.
Captures:
- 2-adic contraction (`shl e s` reduces demand to `d - s`),
- 2-adic expansion (`shr e s` increases demand to `d + s`),
- Carry-Firewall boundary (`clearBit e k` at `d = k + 1` needs only `need e k`!),
- Compositional lookahead (`comp e1 e2` composes demands). -/
def Expr.need : Expr → Nat → Nat
  | .var, d => d
  | .const _, _ => 0
  | .add e1 e2, d => max (e1.need d) (e2.need d)
  | .mul e1 e2, d => max (e1.need d) (e2.need d)
  | .xor e1 e2, d => max (e1.need d) (e2.need d)
  | .and e1 e2, d => max (e1.need d) (e2.need d)
  | .or e1 e2, d => max (e1.need d) (e2.need d)
  | .shl e s, d => e.need (d - s)
  | .shr e s, d => e.need (d + s)
  | .clearBit e k, d => if d = k + 1 then e.need k else e.need d
  | .comp e1 e2, d => e2.need (e1.need d)

/-- Soundness of `Expr.need`: changing `n` at bit positions `≥ e.need d` leaves
`e.eval n % 2^d` invariant. -/
theorem Expr.eval_mod_pow2_eq (e : Expr) :
    ∀ d n m, n % 2 ^ (e.need d) = m % 2 ^ (e.need d) →
      e.eval n % 2 ^ d = e.eval m % 2 ^ d := by
  induction e with
  | var =>
    intro d n m h
    exact h
  | const c =>
    intro d n m _
    rfl
  | add e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    have h1 : n % 2 ^ (e1.need d) = m % 2 ^ (e1.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d))]
    have h2 : n % 2 ^ (e2.need d) = m % 2 ^ (e2.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d))]
    simp only [Expr.eval]
    rw [Nat.add_mod, ih1 d n m h1, ih2 d n m h2, ← Nat.add_mod]
  | mul e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    have h1 : n % 2 ^ (e1.need d) = m % 2 ^ (e1.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d))]
    have h2 : n % 2 ^ (e2.need d) = m % 2 ^ (e2.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d))]
    simp only [Expr.eval]
    rw [Nat.mul_mod, ih1 d n m h1, ih2 d n m h2, ← Nat.mul_mod]
  | xor e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    have h1 : n % 2 ^ (e1.need d) = m % 2 ^ (e1.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d))]
    have h2 : n % 2 ^ (e2.need d) = m % 2 ^ (e2.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d))]
    simp only [Expr.eval]
    rw [xor_mod_two_pow, ih1 d n m h1, ih2 d n m h2, ← xor_mod_two_pow]
  | and e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    have h1 : n % 2 ^ (e1.need d) = m % 2 ^ (e1.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d))]
    have h2 : n % 2 ^ (e2.need d) = m % 2 ^ (e2.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d))]
    simp only [Expr.eval]
    rw [and_mod_two_pow, ih1 d n m h1, ih2 d n m h2, ← and_mod_two_pow]
  | or e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    have h1 : n % 2 ^ (e1.need d) = m % 2 ^ (e1.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_left (e1.need d) (e2.need d))]
    have h2 : n % 2 ^ (e2.need d) = m % 2 ^ (e2.need d) := by
      rw [← mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d)), h,
          mod_pow2_of_le (Nat.le_max_right (e1.need d) (e2.need d))]
    simp only [Expr.eval]
    rw [or_mod_two_pow, ih1 d n m h1, ih2 d n m h2, ← or_mod_two_pow]
  | shl e s ih =>
    intro d n m h
    simp only [Expr.need] at h
    simp only [Expr.eval]
    rw [shl_mod_two_pow, ih (d - s) n m h, ← shl_mod_two_pow]
  | shr e s ih =>
    intro d n m h
    simp only [Expr.need] at h
    simp only [Expr.eval]
    rw [shr_mod_two_pow, ih (d + s) n m h, ← shr_mod_two_pow]
  | clearBit e k ih =>
    intro d n m h
    simp only [Expr.need] at h
    simp only [Expr.eval]
    by_cases hdk : d = k + 1
    · subst hdk
      simp only [↓reduceIte] at h
      rw [clearBitNat_mod_succ, clearBitNat_mod_succ]
      exact ih k n m h
    · simp only [hdk, ↓reduceIte] at h
      by_cases hle : d ≤ k
      · rw [clearBitNat_mod_le _ _ _ hle, clearBitNat_mod_le _ _ _ hle]
        exact ih d n m h
      · have hgt : k + 1 ≤ d := by omega
        rw [clearBitNat_mod_gt _ _ _ hgt, clearBitNat_mod_gt _ _ _ hgt, ih d n m h]
  | comp e1 e2 ih1 ih2 =>
    intro d n m h
    simp only [Expr.need] at h
    simp only [Expr.eval]
    exact ih1 d (e2.eval n) (e2.eval m) (ih2 (e1.need d) n m h)

/-- Helper: on any ball `B(r, d)`, if `k ≤ d` and `r < 2^d`, then `(r + q * 2^d) % 2^k = r % 2^k`. -/
theorem ball_mod_eq {r d k q : Nat} (hk : k ≤ d) :
    (r + q * 2 ^ d) % 2 ^ k = r % 2 ^ k := by
  have hdiv : 2 ^ k ∣ 2 ^ d := Nat.pow_dvd_pow 2 hk
  rcases hdiv with ⟨m, hm⟩
  rw [hm]
  have hmul : q * (2 ^ k * m) = 2 ^ k * (q * m) := by
    rw [Nat.mul_left_comm]
  rw [hmul, Nat.add_mul_mod_self_left]

/-! ### Layer 2A: Adaptive Non-Collision / Separation Compiler (`neqCover`) -/

def validNeq (f g : Expr) (r d k : Nat) : Bool :=
  decide (f.need k ≤ d) && decide (g.need k ≤ d) &&
    decide (f.eval r % 2 ^ k ≠ g.eval r % 2 ^ k)

/-- **Non-Collision Soundness Meta-Theorem**:
Any checked `CoverTree` of witness bit-depths certifies `∀ n : Nat, f.eval n ≠ g.eval n`. -/
theorem neqCover_sound (f g : Expr) (t : CoverTree Nat)
    (hchk : checkCover (validNeq f g) 0 0 t = true) :
    ∀ n : Nat, f.eval n ≠ g.eval n := by
  refine coverTree_sound (P := fun n => f.eval n ≠ g.eval n) (validNeq f g) ?_ t hchk
  intro r d k _ hval q
  simp only [validNeq, Bool.and_eq_true, decide_eq_true_eq] at hval
  rcases hval with ⟨⟨hf, hg⟩, hneq⟩
  have hfeq : f.eval (r + q * 2 ^ d) % 2 ^ k = f.eval r % 2 ^ k :=
    f.eval_mod_pow2_eq k (r + q * 2 ^ d) r (ball_mod_eq hf)
  have hgeq : g.eval (r + q * 2 ^ d) % 2 ^ k = g.eval r % 2 ^ k :=
    g.eval_mod_pow2_eq k (r + q * 2 ^ d) r (ball_mod_eq hg)
  intro heq
  apply hneq
  rw [← hfeq, ← hgeq, heq]

/-! ### Layer 2B: Adaptive Exact 2-Adic Valuation Ceiling Compiler (`valCover`) -/

def validVal (f : Expr) (r d v : Nat) : Bool :=
  decide (f.need (v + 1) ≤ d) && decide (f.eval r % 2 ^ (v + 1) = 2 ^ v)

/-- **Exact 2-Adic Valuation Soundness Meta-Theorem**:
If a finite `CoverTree` checks under `validVal f`, then EVERY leaf `(r, d, v)` certifies
the EXACT 2-adic valuation `v_2(f(n)) = v` on `B(r, d)`, yielding the global non-divisibility
ceiling `∀ n : Nat, ¬ (2 ^ (treeMaxLabel t + 1) ∣ f.eval n)` (and `f.eval n ≠ 0`). -/
theorem valCover_sound_aux (f : Expr) (M : Nat) :
    ∀ (t : CoverTree Nat) (r d : Nat),
      r < 2 ^ d → treeMaxLabel t ≤ M → checkCover (validVal f) r d t = true →
      ∀ q, ¬ (2 ^ (M + 1) ∣ f.eval (r + q * 2 ^ d)) := by
  intro t
  induction t with
  | leaf v =>
    intro r d _ hle hchk q hdvd
    simp only [treeMaxLabel] at hle
    simp only [checkCover, validVal, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hneed, hmodr⟩
    have hmodeq : f.eval (r + q * 2 ^ d) % 2 ^ (v + 1) = 2 ^ v := by
      rw [f.eval_mod_pow2_eq (v + 1) (r + q * 2 ^ d) r (ball_mod_eq hneed), hmodr]
    have hdiv : 2 ^ (v + 1) ∣ 2 ^ (M + 1) := Nat.pow_dvd_pow 2 (Nat.succ_le_succ hle)
    have hdiv2 : 2 ^ (v + 1) ∣ f.eval (r + q * 2 ^ d) := Nat.dvd_trans hdiv hdvd
    have hzero : f.eval (r + q * 2 ^ d) % 2 ^ (v + 1) = 0 := Nat.mod_eq_zero_of_dvd hdiv2
    rw [hmodeq] at hzero
    have hpos : 0 < 2 ^ v := pow2_pos v
    omega
  | branch t0 t1 ih0 ih1 =>
    intro r d hr hle hchk q
    simp only [treeMaxLabel] at hle
    simp only [checkCover, Bool.and_eq_true] at hchk
    rcases hchk with ⟨h0, h1⟩
    have hr0 : r < 2 ^ (d + 1) := by
      have : 2 ^ d ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ d)
      omega
    have hr1 : r + 2 ^ d < 2 ^ (d + 1) := by
      rw [Nat.pow_succ]; omega
    by_cases hq : q % 2 = 0
    · rw [ball_split_even r d q hq]
      exact ih0 r (d + 1) hr0 (by omega) h0 (q / 2)
    · rw [ball_split_odd r d q hq]
      exact ih1 (r + 2 ^ d) (d + 1) hr1 (by omega) h1 (q / 2)

theorem valCover_sound (f : Expr) (t : CoverTree Nat)
    (hchk : checkCover (validVal f) 0 0 t = true) :
    ∀ n : Nat, ¬ (2 ^ (treeMaxLabel t + 1) ∣ f.eval n) := by
  intro n
  have h := valCover_sound_aux f (treeMaxLabel t) t 0 0 (by decide) (Nat.le_refl _) hchk n
  simpa using h

theorem valCover_ne_zero (f : Expr) (t : CoverTree Nat)
    (hchk : checkCover (validVal f) 0 0 t = true) :
    ∀ n : Nat, f.eval n ≠ 0 := by
  intro n h0
  have hndvd := valCover_sound f t hchk n
  rw [h0] at hndvd
  exact hndvd (Nat.dvd_zero _)

/-! ## Section 3: Layer 3 — Carry-Firewall + Affine-Lipschitz Descent Compiler -/



theorem iterNat_succ_right (f : Nat → Nat) (t n : Nat) :
    iterNat f (t + 1) n = f (iterNat f t n) := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
    simp only [iterNat]
    exact ih (f n)

theorem iterNat_add (f : Nat → Nat) (a b n : Nat) :
    iterNat f (a + b) n = iterNat f b (iterNat f a n) := by
  induction a generalizing n with
  | zero => simp [iterNat]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [iterNat]
    exact ih (f n)

/-- Symbolic state of the Carry-Firewall Affine-Lipschitz simulator over a clopen ball. -/
structure SimState where
  cur  : Nat
  prec : Nat
  A    : Nat
  B    : Nat
  pow2 : Nat
  deriving Repr, DecidableEq

/-- One symbolic step on `B(r, d)` using the Carry-Firewall precision boost when `prec = k`. -/
def simStep (oddCore : Nat → Nat) (k slope offset : Nat) (st : SimState) : Option SimState :=
  match st.prec with
  | 0 => none
  | p + 1 =>
    if st.cur % 2 = 0 then
      some { cur := st.cur / 2, prec := p, A := st.A, B := st.B, pow2 := 2 * st.pow2 }
    else
      let y := oddCore st.cur
      let nextCur :=
        if p + 1 = k then (y % 2 ^ k) / 2
        else if k < p + 1 then (clearBitNat y k / 2) % 2 ^ p
        else (y / 2) % 2 ^ p
      let nextPrec := if p + 1 = k then k else p
      some {
        cur  := nextCur,
        prec := nextPrec,
        A    := slope * st.A,
        B    := slope * st.B + offset * st.pow2,
        pow2 := 2 * st.pow2
      }

def simSteps (oddCore : Nat → Nat) (k slope offset : Nat) :
    Nat → SimState → Option SimState
  | 0, st => some st
  | t + 1, st =>
    match simStep oddCore k slope offset st with
    | none => none
    | some st' => simSteps oddCore k slope offset t st'

/-- Helper: `(a / 2) % 2^p = (a % 2^(p + 1)) / 2`. -/
theorem div2_mod_pow2 (a p : Nat) : (a / 2) % 2 ^ p = (a % 2 ^ (p + 1)) / 2 := by
  have h : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [h, Nat.mod_mul_right_div_self]

/-- Single-step soundness of the Carry-Firewall + Affine-Lipschitz invariant. -/
theorem simStep_sound
    (oddCore : Nat → Nat) (k slope offset : Nat)
    (hlip : ∀ d x, oddCore x % 2 ^ d = oddCore (x % 2 ^ d) % 2 ^ d)
    (hbound : ∀ x, oddCore x ≤ slope * x + offset)
    {n x : Nat} {st st' : SimState}
    (hmod : x % 2 ^ st.prec = st.cur)
    (hle : st.pow2 * x ≤ st.A * n + st.B)
    (hstep : simStep oddCore k slope offset st = some st') :
    firewallStep oddCore k x % 2 ^ st'.prec = st'.cur ∧
    st'.pow2 * firewallStep oddCore k x ≤ st'.A * n + st'.B := by
  cases hp : st.prec with
  | zero =>
    simp [simStep, hp] at hstep
  | succ p =>
    rw [hp] at hmod
    simp only [simStep, hp] at hstep
    have hpar : x % 2 = st.cur % 2 := by
      have h1 : 2 ^ 1 ∣ 2 ^ (p + 1) := Nat.pow_dvd_pow 2 (Nat.succ_le_succ (Nat.zero_le p))
      have h2 := Nat.mod_mod_of_dvd x h1
      rw [hmod] at h2
      simpa using h2.symm
    by_cases heven : st.cur % 2 = 0
    · simp only [heven, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hxeven : x % 2 = 0 := by omega
      simp only [firewallStep, hxeven, ↓reduceIte]
      constructor
      · rw [div2_mod_pow2, hmod]
      · have h2 : 2 * (x / 2) = x := by omega
        calc
          2 * st.pow2 * (x / 2) = st.pow2 * (2 * (x / 2)) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm]
          _ = st.pow2 * x := by rw [h2]
          _ ≤ st.A * n + st.B := hle
    · simp only [heven, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hxodd : x % 2 ≠ 0 := by omega
      simp only [firewallStep, hxodd, ↓reduceIte]
      constructor
      · -- Congruence with Carry-Firewall precision boost!
        by_cases hpk : p + 1 = k
        · simp only [hpk, ↓reduceIte]
          rw [div2_mod_pow2, clearBitNat_mod_succ, hlip k x, ← hpk, hmod]
        · by_cases hklt : k < p + 1
          · simp only [hpk, hklt, ↓reduceIte]
            rw [div2_mod_pow2]
            have hge : k + 1 ≤ p + 1 := Nat.succ_le_of_lt hklt
            rw [clearBitNat_mod_gt (oddCore x) k (p + 1) hge]
            rw [hlip (p + 1) x, hmod]
            rw [← clearBitNat_mod_gt (oddCore st.cur) k (p + 1) hge, div2_mod_pow2]
          · simp only [hpk, hklt, ↓reduceIte]
            have hle_k : p + 1 ≤ k := by omega
            rw [div2_mod_pow2, clearBitNat_mod_le (oddCore x) k (p + 1) hle_k]
            rw [hlip (p + 1) x, hmod, ← div2_mod_pow2]
      · -- Affine-Lipschitz upper envelope
        have hcb : clearBitNat (oddCore x) k ≤ oddCore x := clearBitNat_le (oddCore x) k
        have hcore : oddCore x ≤ slope * x + offset := hbound x
        have hdiv2 : 2 * (clearBitNat (oddCore x) k / 2) ≤ clearBitNat (oddCore x) k :=
          Nat.mul_div_le _ 2
        calc
          2 * st.pow2 * (clearBitNat (oddCore x) k / 2)
            = st.pow2 * (2 * (clearBitNat (oddCore x) k / 2)) := by
                rw [Nat.mul_assoc, Nat.mul_left_comm]
          _ ≤ st.pow2 * (slope * x + offset) :=
                Nat.mul_le_mul_left st.pow2 (Nat.le_trans hdiv2 (Nat.le_trans hcb hcore))
          _ = slope * (st.pow2 * x) + offset * st.pow2 := by
                rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm st.pow2 offset]
          _ ≤ slope * (st.A * n + st.B) + offset * st.pow2 :=
                Nat.add_le_add_right (Nat.mul_le_mul_left slope hle) _
          _ = slope * st.A * n + (slope * st.B + offset * st.pow2) := by
                rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Multi-step soundness of `simSteps`. -/
theorem simSteps_sound
    (oddCore : Nat → Nat) (k slope offset : Nat)
    (hlip : ∀ d x, oddCore x % 2 ^ d = oddCore (x % 2 ^ d) % 2 ^ d)
    (hbound : ∀ x, oddCore x ≤ slope * x + offset) :
    ∀ t n x st st',
      x % 2 ^ st.prec = st.cur →
      st.pow2 * x ≤ st.A * n + st.B →
      simSteps oddCore k slope offset t st = some st' →
      iterNat (firewallStep oddCore k) t x % 2 ^ st'.prec = st'.cur ∧
      st'.pow2 * iterNat (firewallStep oddCore k) t x ≤ st'.A * n + st'.B := by
  intro t
  induction t with
  | zero =>
    intro n x st st' hmod hle hsim
    simp only [simSteps, Option.some.injEq] at hsim
    subst hsim
    exact ⟨hmod, hle⟩
  | succ t ih =>
    intro n x st st' hmod hle hsim
    simp only [simSteps] at hsim
    cases h1 : simStep oddCore k slope offset st with
    | none => simp [h1] at hsim
    | some st1 =>
      simp only [h1] at hsim
      have ⟨hmod1, hle1⟩ := simStep_sound oddCore k slope offset hlip hbound hmod hle h1
      exact ih n (firewallStep oddCore k x) st1 st' hmod1 hle1 hsim

/-- Check finitely many small `q < bound` in `B(r, d)` where the affine envelope
has not yet crossed `n` (`diff * n ≤ B`). -/
def checkSmallQ (oddCore : Nat → Nat) (k N0 r d steps : Nat) : Nat → Bool
  | 0 => true
  | q + 1 =>
    let n := r + q * 2 ^ d
    (decide (n < N0) || decide (iterNat (firewallStep oddCore k) steps n < n)) &&
      checkSmallQ oddCore k N0 r d steps q

theorem checkSmallQ_sound (oddCore : Nat → Nat) (k N0 r d steps : Nat) :
    ∀ bound, checkSmallQ oddCore k N0 r d steps bound = true →
      ∀ q, q < bound → N0 ≤ r + q * 2 ^ d →
        iterNat (firewallStep oddCore k) steps (r + q * 2 ^ d) < r + q * 2 ^ d := by
  intro bound
  induction bound with
  | zero => intro _ q hq; omega
  | succ b ih =>
    intro hchk q hq hN0
    simp only [checkSmallQ, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hthis, hrest⟩
    by_cases hqb : q = b
    · subst hqb
      rcases hthis with hlt | hdrop
      · omega
      · exact hdrop
    · exact ih hrest q (by omega) hN0

/-- Local Carry-Firewall + Affine-Lipschitz leaf verifier for `B(r, d)`.
Checks:
1. `steps > 0`,
2. `simSteps` succeeds with strict contraction `st'.A < st'.pow2`,
3. All finitely many `q` with `(st'.pow2 - st'.A) * (r + q * 2^d) ≤ st'.B` satisfy descent! -/
def validDescent (oddCore : Nat → Nat) (k slope offset N0 : Nat)
    (r d steps : Nat) : Bool :=
  if steps = 0 then false
  else
    let init : SimState := { cur := r, prec := d, A := 1, B := 0, pow2 := 1 }
    match simSteps oddCore k slope offset steps init with
    | none => false
    | some st' =>
      if st'.A < st'.pow2 then
        let diff := st'.pow2 - st'.A
        -- Upper bound on `q` such that `diff * (r + q * 2^d) ≤ st'.B`:
        -- Since `2^d ≥ 1` and `diff ≥ 1`, `q ≤ st'.B / (diff * 2^d)`.
        let qBound := st'.B / (diff * 2 ^ d) + 1
        checkSmallQ oddCore k N0 r d steps qBound
      else false

/-- **Carry-Firewall Descent Soundness Meta-Theorem**:
Any checked `CoverTree` proves universal bounded stopping time
`∀ n ≥ N0, ∃ t, 1 ≤ t ∧ t ≤ treeMaxLabel t ∧ firewallStep^[t] n < n`. -/
theorem descentCover_sound_aux
    (oddCore : Nat → Nat) (k slope offset N0 M : Nat)
    (hlip : ∀ d x, oddCore x % 2 ^ d = oddCore (x % 2 ^ d) % 2 ^ d)
    (hbound : ∀ x, oddCore x ≤ slope * x + offset) :
    ∀ (t : CoverTree Nat) (r d : Nat),
      r < 2 ^ d → treeMaxLabel t ≤ M →
      checkCover (validDescent oddCore k slope offset N0) r d t = true →
      ∀ q, N0 ≤ r + q * 2 ^ d →
        ∃ steps, 1 ≤ steps ∧ steps ≤ M ∧
          iterNat (firewallStep oddCore k) steps (r + q * 2 ^ d) < r + q * 2 ^ d := by
  intro t
  induction t with
  | leaf steps =>
    intro r d hr hM hchk q hN0
    simp only [treeMaxLabel] at hM
    simp only [checkCover, validDescent] at hchk
    by_cases hsz : steps = 0
    · simp [hsz] at hchk
    · simp only [hsz, ↓reduceIte] at hchk
      cases hsim : simSteps oddCore k slope offset steps { cur := r, prec := d, A := 1, B := 0, pow2 := 1 } with
      | none => simp [hsim] at hchk
      | some st' =>
        simp only [hsim] at hchk
        split at hchk
        · rename_i hlt
          let diff := st'.pow2 - st'.A
          let qBound := st'.B / (diff * 2 ^ d) + 1
          refine ⟨steps, by omega, hM, ?_⟩
          by_cases hq : q < qBound
          · exact checkSmallQ_sound oddCore k N0 r d steps qBound hchk q hq hN0
          · -- Asymptotic regime: `q ≥ qBound` implies `(pow2 - A) * (r + q * 2^d) > B`!
            have hqge : st'.B / (diff * 2 ^ d) + 1 ≤ q := by omega
            have hdpos : 0 < diff * 2 ^ d := Nat.mul_pos (by omega) (pow2_pos d)
            have hmul_gt : st'.B < q * (diff * 2 ^ d) := by
              have hdivlt : st'.B < (st'.B / (diff * 2 ^ d) + 1) * (diff * 2 ^ d) := by
                have := Nat.div_add_mod st'.B (diff * 2 ^ d)
                have := Nat.mod_lt st'.B hdpos
                rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (diff * 2 ^ d)] at *
                omega
              exact Nat.lt_of_lt_of_le hdivlt (Nat.mul_le_mul_right _ hqge)
            have hdiff_gt : st'.B < diff * (r + q * 2 ^ d) := by
              have h1 : q * (diff * 2 ^ d) = diff * (q * 2 ^ d) := by
                rw [Nat.mul_left_comm]
              have h2 : diff * (q * 2 ^ d) ≤ diff * (r + q * 2 ^ d) :=
                Nat.mul_le_mul_left diff (Nat.le_add_left _ _)
              omega
            have hinit_mod : (r + q * 2 ^ d) % 2 ^ d = r := by
              rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
            have hinit_le : 1 * (r + q * 2 ^ d) ≤ 1 * (r + q * 2 ^ d) + 0 := by omega
            have ⟨_, haff⟩ := simSteps_sound oddCore k slope offset hlip hbound
              steps (r + q * 2 ^ d) (r + q * 2 ^ d) _ st' hinit_mod hinit_le hsim
            -- From `pow2 * y ≤ A * n + B` and `B < (pow2 - A) * n`, deduce `y < n`!
            have hstrict : st'.pow2 * iterNat (firewallStep oddCore k) steps (r + q * 2 ^ d) <
                st'.pow2 * (r + q * 2 ^ d) := by
              have hexp : diff * (r + q * 2 ^ d) + st'.A * (r + q * 2 ^ d) =
                  st'.pow2 * (r + q * 2 ^ d) := by
                rw [← Nat.add_mul]
                have : diff + st'.A = st'.pow2 := by omega
                rw [this]
              omega
            exact Nat.lt_of_mul_lt_mul_left hstrict
        · simp at hchk
  | branch t0 t1 ih0 ih1 =>
    intro r d hr hM hchk q hN0
    simp only [treeMaxLabel] at hM
    simp only [checkCover, Bool.and_eq_true] at hchk
    rcases hchk with ⟨h0, h1⟩
    have hr0 : r < 2 ^ (d + 1) := by
      have : 2 ^ d ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ d)
      omega
    have hr1 : r + 2 ^ d < 2 ^ (d + 1) := by
      rw [Nat.pow_succ]; omega
    by_cases hq : q % 2 = 0
    · rw [ball_split_even r d q hq] at hN0 ⊢
      exact ih0 r (d + 1) hr0 (by omega) h0 (q / 2) hN0
    · rw [ball_split_odd r d q hq] at hN0 ⊢
      exact ih1 (r + 2 ^ d) (d + 1) hr1 (by omega) h1 (q / 2) hN0

theorem descentCover_sound
    (oddCore : Nat → Nat) (k slope offset N0 : Nat)
    (hlip : ∀ d x, oddCore x % 2 ^ d = oddCore (x % 2 ^ d) % 2 ^ d)
    (hbound : ∀ x, oddCore x ≤ slope * x + offset)
    (t : CoverTree Nat)
    (hchk : checkCover (validDescent oddCore k slope offset N0) 0 0 t = true) :
    ∀ n, N0 ≤ n →
      ∃ steps, 1 ≤ steps ∧ steps ≤ treeMaxLabel t ∧
        iterNat (firewallStep oddCore k) steps n < n := by
  intro n hN0
  have h := descentCover_sound_aux oddCore k slope offset N0 (treeMaxLabel t)
    hlip hbound t 0 0 (by decide) (Nat.le_refl _) hchk n (by simpa using hN0)
  simpa using h

/-- **Well-Founded Global Convergence Lift**:
Universal finite-step descent above `N0` automatically proves global convergence
into `{0, ..., N0 - 1}` for ALL `n : Nat` by strong induction! -/
theorem converges_below_of_descent (f : Nat → Nat) (N0 : Nat)
    (hdesc : ∀ n, N0 ≤ n → ∃ steps, iterNat f steps n < n) :
    ∀ n : Nat, ∃ m : Nat, iterNat f m n < N0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < N0
    · exact ⟨0, hlt⟩
    · have hge : N0 ≤ n := by omega
      rcases hdesc n hge with ⟨s, hs⟩
      rcases ih (iterNat f s n) hs with ⟨m, hm⟩
      refine ⟨s + m, ?_⟩
      rw [iterNat_add]
      exact hm

end AdicCompactness


/-! ## Section 4: Concrete Pure-Silicon Families, Certificates & Discharged Infinite Theorems -/

namespace AdicCompactness


theorem collatzCore_lip (d x : Nat) :
    collatzCore x % 2 ^ d = collatzCore (x % 2 ^ d) % 2 ^ d := by
  have h := Expr.eval_mod_pow2_eq (.add (.mul (.const 3) .var) (.const 1)) d x (x % 2 ^ d)
    (by simp [Expr.need])
  simpa [Expr.eval, collatzCore] using h

theorem collatzCore_bound (x : Nat) : collatzCore x ≤ 3 * x + 1 := Nat.le_refl _


theorem xorCollatzCore_lip (c d x : Nat) :
    xorCollatzCore c x % 2 ^ d = xorCollatzCore c (x % 2 ^ d) % 2 ^ d := by
  have hneed : (Expr.add (.xor .var (.shl .var 1)) (.const c)).need d = d := by
    simp [Expr.need]
  have h := Expr.eval_mod_pow2_eq (.add (.xor .var (.shl .var 1)) (.const c)) d x (x % 2 ^ d)
    (by rw [hneed, Nat.mod_mod])
  simpa [Expr.eval, xorCollatzCore] using h

theorem xorCollatzCore_bound (c x : Nat) : xorCollatzCore c x ≤ 3 * x + c := by
  unfold xorCollatzCore
  have hshl : x <<< 1 = 2 * x := by
    rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  have hxor : x ^^^ (x <<< 1) ≤ x + (x <<< 1) := xor_le_add x (x <<< 1)
  omega


/-! ### Synthesized Preorder Certificate Tokens (verified bit-identically by `explore_and_verify.py`) -/

def certT1Tokens : List Nat := [
  0, 2, 3
]

def certT2Tokens : List Nat := [
  0, 2, 0, 3, 5
]

def certT3Tokens : List Nat := [
  0, 2, 0, 3, 0, 6, 0, 0, 0, 0, 8, 9, 0, 9, 8, 0, 0, 8, 9, 0, 9, 8, 0, 0,
  0, 9, 8, 0, 9, 8, 0, 0, 9, 8, 0, 8, 9
]

def certT4Tokens : List Nat := [
  0, 2, 0, 3, 0, 0, 5, 6, 0, 6, 8
]

def certT5Tokens : List Nat := [
  0, 2, 0, 3, 0, 0, 5, 0, 6, 0, 0, 0, 9, 0, 0, 0, 0, 14, 13, 0, 14, 13, 0, 0,
  14, 13, 0, 14, 13, 0, 0, 0, 14, 13, 0, 13, 14, 0, 0, 14, 13, 0, 13, 14, 0, 0, 0, 0,
  0, 13, 14, 0, 14, 13, 0, 0, 14, 13, 0, 14, 13, 0, 0, 0, 14, 13, 0, 14, 13, 0, 0, 14,
  13, 0, 13, 14, 9, 0, 0, 9, 0, 0, 0, 0, 13, 14, 0, 14, 13, 0, 0, 13, 14, 0, 14, 13,
  0, 0, 0, 13, 14, 0, 13, 14, 0, 0, 13, 14, 0, 14, 13, 0, 9, 0, 0, 0, 0, 13, 14, 0,
  14, 13, 0, 0, 14, 13, 0, 14, 13, 0, 0, 0, 13, 14, 0, 14, 13, 0, 0, 13, 14, 0, 14, 13,
  0, 0, 9, 6, 0, 0, 0, 0, 0, 0, 0, 0, 14, 13, 0, 13, 14, 11, 0, 0, 0, 14, 13, 0,
  13, 14, 11, 0, 0, 11, 0, 0, 14, 13, 0, 14, 13, 0, 11, 0, 0, 14, 13, 0, 14, 13, 0, 0,
  0, 11, 0, 0, 13, 14, 0, 13, 14, 0, 11, 0, 0, 13, 14, 0, 13, 14, 0, 0, 0, 0, 14, 13,
  0, 14, 13, 11, 0, 0, 0, 14, 13, 0, 14, 13, 11, 0, 0, 0, 0, 11, 0, 0, 14, 13, 0, 13,
  14, 0, 0, 0, 14, 13, 0, 13, 14, 11, 0, 0, 11, 0, 0, 13, 14, 0, 14, 13, 0, 11, 0, 0,
  13, 14, 0, 14, 13, 0, 0, 0, 0, 0, 14, 13, 0, 13, 14, 11, 0, 11, 0, 0, 13, 14, 0, 13,
  14, 0, 0, 0, 0, 13, 14, 0, 14, 13, 11, 0, 0, 0, 13, 14, 0, 14, 13, 11, 0, 0, 0, 0,
  0, 0, 13, 0, 0, 14, 0, 0, 16, 17, 0, 17, 16, 0, 0, 0, 17, 16, 0, 16, 17, 14, 0, 13,
  0, 0, 14, 0, 0, 17, 16, 0, 16, 17, 0, 14, 0, 0, 16, 17, 0, 17, 16, 0, 0, 13, 0, 0,
  0, 0, 17, 16, 0, 16, 17, 14, 0, 14, 0, 0, 17, 16, 0, 17, 16, 0, 13, 0, 0, 0, 0, 16,
  17, 0, 17, 16, 14, 0, 0, 0, 17, 16, 0, 16, 17, 14, 0, 0, 0, 0, 0, 14, 0, 0, 16, 17,
  0, 17, 16, 0, 14, 0, 0, 17, 16, 0, 16, 17, 13, 0, 13, 0, 0, 0, 0, 16, 17, 0, 17, 16,
  14, 0, 0, 0, 17, 16, 0, 16, 17, 14, 0, 0, 13, 0, 0, 14, 0, 0, 17, 16, 0, 16, 17, 0,
  14, 0, 0, 16, 17, 0, 17, 16, 0, 13, 0, 0, 0, 0, 16, 17, 0, 16, 17, 14, 0, 14, 0, 0,
  17, 16, 0, 16, 17, 0, 0, 0, 0, 13, 0, 0, 0, 0, 17, 16, 0, 17, 16, 14, 0, 0, 0, 16,
  17, 0, 16, 17, 14, 0, 0, 0, 0, 0, 16, 17, 0, 16, 17, 14, 0, 14, 0, 0, 17, 16, 0, 16,
  17, 13, 0, 0, 13, 0, 0, 14, 0, 0, 16, 17, 0, 17, 16, 0, 14, 0, 0, 17, 16, 0, 16, 17,
  0, 0, 0, 14, 0, 0, 17, 16, 0, 16, 17, 0, 0, 0, 16, 17, 0, 17, 16, 14, 13, 0, 0, 0,
  13, 0, 0, 14, 0, 0, 16, 17, 0, 17, 16, 0, 14, 0, 0, 17, 16, 0, 16, 17, 0, 13, 0, 0,
  0, 0, 17, 16, 0, 17, 16, 14, 0, 14, 0, 0, 16, 17, 0, 17, 16, 0, 0, 13, 0, 0, 14, 0,
  0, 16, 17, 0, 16, 17, 0, 0, 0, 17, 16, 0, 17, 16, 14, 0, 0, 0, 0, 0, 17, 16, 0, 17,
  16, 14, 0, 0, 0, 16, 17, 0, 16, 17, 14, 13, 0, 0, 0, 0, 0, 13, 0, 0, 14, 0, 0, 17,
  16, 0, 17, 16, 0, 14, 0, 0, 16, 17, 0, 16, 17, 0, 0, 0, 14, 0, 0, 16, 17, 0, 16, 17,
  0, 0, 0, 17, 16, 0, 17, 16, 14, 13, 0, 0, 0, 0, 0, 0, 16, 17, 0, 17, 16, 14, 0, 14,
  0, 0, 16, 17, 0, 16, 17, 13, 0, 0, 0, 0, 0, 17, 16, 0, 16, 17, 14, 0, 0, 0, 16, 17,
  0, 17, 16, 14, 13, 0, 0, 0, 0, 0, 0, 0, 17, 16, 0, 17, 16, 14, 0, 0, 0, 16, 17, 0,
  16, 17, 14, 13, 0, 0, 0, 14, 0, 0, 16, 17, 0, 16, 17, 0, 0, 0, 17, 16, 0, 17, 16, 14,
  13, 0, 0, 0, 0, 0, 0, 16, 17, 0, 17, 16, 14, 0, 14, 0, 0, 16, 17, 0, 16, 17, 13, 0,
  13, 0, 0, 14, 0, 0, 17, 16, 0, 17, 16, 0, 0, 0, 16, 17, 0, 16, 17, 14, 0, 0, 0, 0,
  13, 0, 0, 0, 0, 16, 17, 0, 16, 17, 14, 0, 14, 0, 0, 17, 16, 0, 16, 17, 0, 0, 0, 14,
  0, 0, 17, 16, 0, 16, 17, 0, 14, 0, 0, 16, 17, 0, 17, 16, 13, 0, 0, 0, 0, 0, 0, 16,
  17, 0, 16, 17, 14, 0, 0, 0, 17, 16, 0, 17, 16, 14, 13, 0, 0, 0, 14, 0, 0, 17, 16, 0,
  17, 16, 0, 0, 0, 16, 17, 0, 16, 17, 14, 13, 0, 0, 0, 13, 0, 0, 14, 0, 0, 16, 17, 0,
  16, 17, 0, 14, 0, 0, 17, 16, 0, 17, 16, 0, 0, 0, 14, 0, 0, 17, 16, 0, 17, 16, 0, 0,
  0, 16, 17, 0, 16, 17, 14, 13, 0, 0, 13, 0, 0, 0, 0, 17, 16, 0, 17, 16, 14, 0, 0, 0,
  16, 17, 0, 16, 17, 14, 0, 0, 0, 0, 0, 16, 17, 0, 16, 17, 14, 0, 14, 0, 0, 17, 16, 0,
  16, 17, 13
]

def certX21Tokens : List Nat := [
  0, 2, 0, 3, 5
]

def certX33Tokens : List Nat := [
  0, 2, 0, 0, 5, 6, 3
]

def certGQ1Tokens : List Nat := [
  0, 0, 0, 2, 2, 1, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 7, 7, 0, 7, 7, 0, 0, 0,
  0, 0, 0, 11, 11, 0, 11, 11, 0, 0, 0, 12, 12, 0, 12, 12, 0, 0, 12, 12, 0, 12, 12, 0,
  0, 10, 10, 0, 10, 10, 0, 0, 9, 9, 0, 9, 9, 0, 0, 0, 0, 10, 10, 0, 10, 10, 0, 0,
  0, 11, 11, 0, 11, 11, 0, 0, 11, 11, 0, 11, 11, 0, 0, 0, 10, 10, 0, 10, 10, 0, 0, 10,
  10, 0, 10, 10, 0, 0, 6, 6, 0, 6, 6, 0, 0, 5, 5, 0, 5, 5, 1
]

def certGQ2Tokens : List Nat := [
  0, 0, 0, 0, 3, 3, 0, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 7, 7, 0, 7, 7, 0, 0,
  0, 0, 0, 10, 10, 0, 10, 10, 0, 0, 0, 0, 0, 0, 14, 14, 0, 14, 14, 0, 0, 0, 15, 15,
  0, 15, 15, 0, 0, 15, 15, 0, 15, 15, 0, 0, 13, 13, 0, 13, 13, 0, 0, 12, 12, 0, 12, 12,
  0, 0, 0, 12, 12, 0, 12, 12, 0, 0, 12, 12, 0, 12, 12, 0, 0, 9, 9, 0, 9, 9, 0, 0,
  0, 9, 9, 0, 9, 9, 0, 0, 9, 9, 0, 9, 9, 0, 0, 6, 6, 0, 6, 6, 0, 0, 0, 0,
  0, 0, 9, 9, 0, 9, 9, 0, 0, 0, 10, 10, 0, 10, 10, 0, 0, 10, 10, 0, 10, 10, 0, 0,
  8, 8, 0, 8, 8, 0, 0, 7, 7, 0, 7, 7, 0, 0, 0, 7, 7, 0, 7, 7, 0, 0, 7, 7,
  0, 7, 7, 0, 3, 3, 1
]

def treeT1  : CoverTree Nat := decodeCoverTree certT1Tokens
def treeT2  : CoverTree Nat := decodeCoverTree certT2Tokens
def treeT3  : CoverTree Nat := decodeCoverTree certT3Tokens
def treeT4  : CoverTree Nat := decodeCoverTree certT4Tokens
def treeT5  : CoverTree Nat := decodeCoverTree certT5Tokens
def treeX21 : CoverTree Nat := decodeCoverTree certX21Tokens
def treeX33 : CoverTree Nat := decodeCoverTree certX33Tokens
def treeGQ1 : CoverTree Nat := decodeCoverTree certGQ1Tokens
def treeGQ2 : CoverTree Nat := decodeCoverTree certGQ2Tokens

/-- Map leaf labels of a `CoverTree` (used to turn a valuation tree `v` into a
non-collision witness-bit tree `v + 1`). -/
def mapTree {α β : Type} (f : α → β) : CoverTree α → CoverTree β
  | CoverTree.leaf c => CoverTree.leaf (f c)
  | CoverTree.branch t0 t1 => CoverTree.branch (mapTree f t0) (mapTree f t1)

/-! ### Kernel-Verified Certificate Metrics & Non-Vacuity / Compression Witnesses -/

theorem treeT3_metrics :
    treeLeaves treeT3 = 19 ∧ treeMaxDepth treeT3 = 7 ∧ treeMaxLabel treeT3 = 8 := by decide

theorem treeT4_metrics :
    treeLeaves treeT4 = 6 ∧ treeMaxDepth treeT4 = 4 ∧ treeMaxLabel treeT4 = 7 := by decide

theorem treeT5_metrics :
    treeLeaves treeT5 = 506 ∧ treeMaxDepth treeT5 = 15 ∧ treeMaxLabel treeT5 = 16 := by decide

theorem treeGQ1_metrics :
    treeLeaves treeGQ1 = 58 ∧ treeMaxDepth treeGQ1 = 13 ∧ treeMaxLabel treeGQ1 = 11 := by decide

theorem treeGQ2_metrics :
    treeLeaves treeGQ2 = 88 ∧ treeMaxDepth treeGQ2 = 16 ∧ treeMaxLabel treeGQ2 = 14 := by decide

theorem treeT5_haar_one : treeHaarNum 15 0 treeT5 = 2 ^ 15 :=
  coverTree_haar_partition treeT5 15 (by decide)

theorem treeGQ2_haar_one : treeHaarNum 16 0 treeGQ2 = 2 ^ 16 :=
  coverTree_haar_partition treeGQ2 16 (by decide)

/-! ### Theorem Family 1: Global Termination of Bit-`k`-Cleared Collatz Maps `T_1 .. T_5` -/

theorem T1_descent : ∀ n, 2 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 2 ∧ iterNat (TCollatz 1) s n < n :=
  descentCover_sound collatzCore 1 3 1 2 collatzCore_lip collatzCore_bound treeT1 (by decide)

theorem T1_global_convergence : ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 1) m n ≤ 1 := by
  intro n
  have h := converges_below_of_descent (TCollatz 1) 2
    (fun x hx => let ⟨s, _, _, hs⟩ := T1_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

theorem T2_descent : ∀ n, 1 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 4 ∧ iterNat (TCollatz 2) s n < n :=
  descentCover_sound collatzCore 2 3 1 1 collatzCore_lip collatzCore_bound treeT2 (by decide)

theorem T2_global_convergence_to_zero : ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 2) m n = 0 := by
  intro n
  have h := converges_below_of_descent (TCollatz 2) 1
    (fun x hx => let ⟨s, _, _, hs⟩ := T2_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

theorem T3_descent : ∀ n, 2 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 8 ∧ iterNat (TCollatz 3) s n < n :=
  descentCover_sound collatzCore 3 3 1 2 collatzCore_lip collatzCore_bound treeT3 (by decide)

theorem T3_global_convergence : ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 3) m n ≤ 1 := by
  intro n
  have h := converges_below_of_descent (TCollatz 3) 2
    (fun x hx => let ⟨s, _, _, hs⟩ := T3_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

theorem T4_descent : ∀ n, 2 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 7 ∧ iterNat (TCollatz 4) s n < n :=
  descentCover_sound collatzCore 4 3 1 2 collatzCore_lip collatzCore_bound treeT4 (by decide)

theorem T4_global_convergence : ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 4) m n ≤ 1 := by
  intro n
  have h := converges_below_of_descent (TCollatz 4) 2
    (fun x hx => let ⟨s, _, _, hs⟩ := T4_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

/-- **Flagship Non-Uniform 2-Adic Compactness Descent Theorem (`T_5`)**:
Certified by a 506-leaf non-uniform prefix tree of max depth 15 (`64.8x` compression over
uniform `2^15 = 32,768`): every `n ≥ 2` drops strictly below `n` in at most 16 steps. -/
theorem T5_descent : ∀ n, 2 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 16 ∧ iterNat (TCollatz 5) s n < n :=
  descentCover_sound collatzCore 5 3 1 2 collatzCore_lip collatzCore_bound treeT5 (by decide)

theorem T5_global_convergence : ∀ n : Nat, ∃ m : Nat, iterNat (TCollatz 5) m n ≤ 1 := by
  intro n
  have h := converges_below_of_descent (TCollatz 5) 2
    (fun x hx => let ⟨s, _, _, hs⟩ := T5_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

/-! ### Theorem Family 2: Nonlinear Bit-`k`-Cleared Carryless/XOR-Collatz Maps `X_{k,c}` -/

theorem X21_descent : ∀ n, 1 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 4 ∧ iterNat (TXorCollatz 2 1) s n < n :=
  descentCover_sound (xorCollatzCore 1) 2 3 1 1 (xorCollatzCore_lip 1) (xorCollatzCore_bound 1)
    treeX21 (by decide)

theorem X21_global_convergence_to_zero : ∀ n : Nat, ∃ m : Nat, iterNat (TXorCollatz 2 1) m n = 0 := by
  intro n
  have h := converges_below_of_descent (TXorCollatz 2 1) 1
    (fun x hx => let ⟨s, _, _, hs⟩ := X21_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

theorem X33_descent : ∀ n, 1 ≤ n → ∃ s, 1 ≤ s ∧ s ≤ 5 ∧ iterNat (TXorCollatz 3 3) s n < n :=
  descentCover_sound (xorCollatzCore 3) 3 3 3 1 (xorCollatzCore_lip 3) (xorCollatzCore_bound 3)
    treeX33 (by decide)

theorem X33_global_convergence_to_zero : ∀ n : Nat, ∃ m : Nat, iterNat (TXorCollatz 3 3) m n = 0 := by
  intro n
  have h := converges_below_of_descent (TXorCollatz 3 3) 1
    (fun x hx => let ⟨s, _, _, hs⟩ := X33_descent x hx; ⟨s, hs⟩) n
  rcases h with ⟨m, hm⟩
  exact ⟨m, by omega⟩

/-! ### Theorem Family 3: Gray-Quadratic Exact 2-Adic Valuation Ceilings & Non-Collision -/

/-- Certified by a 58-leaf tree of max depth 13 (`141.2x` compression over `2^13 = 8,192`):
`2^12` never divides `(n ^^^ (n >>> 1))^2 + n + 10` for any `n : Nat`. -/
theorem grayQuad1_val_ceiling :
    ∀ n : Nat, ¬ (2 ^ 12 ∣ (n ^^^ (n >>> 1)) * (n ^^^ (n >>> 1)) + 1 * n + 10) :=
  valCover_sound (grayQuadExpr 1 10) treeGQ1 (by decide)

/-- **Flagship Reflected `Expr` Theorem (`744.7x` Compression)**:
Certified by an 88-leaf tree of max depth 16 (vs uniform `2^16 = 65,536`):
`2^15` never divides `(n ^^^ (n >>> 1))^2 + 3 * n + 60` for any `n : Nat`. -/
theorem grayQuad2_val_ceiling :
    ∀ n : Nat, ¬ (2 ^ 15 ∣ (n ^^^ (n >>> 1)) * (n ^^^ (n >>> 1)) + 3 * n + 60) :=
  valCover_sound (grayQuadExpr 3 60) treeGQ2 (by decide)

/-- Non-Collision via Layer 2A (`neqCover_sound`):
`(n ^^^ (n >>> 1))^2 + 3 * n + 60 ≠ (n <<< 15)` for all `n : Nat`, exploiting
2-adic contraction `need (shl var 15) k = 0` for all `k ≤ 15`! -/
theorem grayQuad2_neq_shift15 :
    ∀ n : Nat, (n ^^^ (n >>> 1)) * (n ^^^ (n >>> 1)) + 3 * n + 60 ≠ (n <<< 15) :=
  neqCover_sound (grayQuadExpr 3 60) shift15Expr (mapTree (· + 1) treeGQ2) (by decide)

/-! ## Section 5: Kernel-Checked Sharpness & Phase-Transition Counterexamples -/

/-- Incremental checker verifying `n0 < iterNat f t cur` for all `1 ≤ t ≤ bound`
in `O(bound)` single steps (zero quadratic re-evaluation). -/
def allStepsGtFrom (f : Nat → Nat) (n0 cur : Nat) : Nat → Bool
  | 0 => true
  | bound + 1 =>
    let nxt := f cur
    decide (n0 < nxt) && allStepsGtFrom f n0 nxt bound

theorem allStepsGtFrom_sound (f : Nat → Nat) (n0 : Nat) :
    ∀ bound cur, allStepsGtFrom f n0 cur bound = true →
      ∀ t, 1 ≤ t → t ≤ bound → n0 < iterNat f t cur := by
  intro bound
  induction bound with
  | zero => intro _ _ t ht1 ht2; omega
  | succ b ih =>
    intro cur hchk t ht1 ht2
    simp only [allStepsGtFrom, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨h1, hrest⟩
    cases t with
    | zero => omega
    | succ s =>
      simp only [iterNat]
      cases s with
      | zero => exact h1
      | succ s' => exact ih (f cur) hrest (s' + 1) (by omega) (by omega)

/-- **Phase Transition at `k = 6`**: `n = 290,743,719` follows the expanding 2-adic 4-cycle
`[39, 27, 9, 14]` (growth `27/16 > 1`), staying strictly above `290,743,719` for all
`1 ≤ t ≤ 48` and reaching `155,037,103,245` (`> 533 * n`). -/
theorem T6_step12_1 : iterNat (TCollatz 6) 12 290743719 = 1397145447 := by decide
theorem T6_step12_2 : iterNat (TCollatz 6) 12 1397145447 = 6713870503 := by decide
theorem T6_step12_3 : iterNat (TCollatz 6) 12 6713870503 = 32262966823 := by decide
theorem T6_step12_4 : iterNat (TCollatz 6) 12 32262966823 = 155037103245 := by decide

theorem T6_explosion_48 :
    iterNat (TCollatz 6) 48 290743719 = 155037103245 := by
  have h24 : iterNat (TCollatz 6) 24 290743719 = 6713870503 := by
    have : (24 : Nat) = 12 + 12 := rfl
    rw [this, iterNat_add, T6_step12_1, T6_step12_2]
  have h36 : iterNat (TCollatz 6) 36 290743719 = 32262966823 := by
    have : (36 : Nat) = 24 + 12 := rfl
    rw [this, iterNat_add, h24, T6_step12_3]
  have : (48 : Nat) = 36 + 12 := rfl
  rw [this, iterNat_add, h36, T6_step12_4]

theorem T6_no_drop_48 :
    ∀ t, 1 ≤ t → t ≤ 48 → 290743719 < iterNat (TCollatz 6) t 290743719 := by
  have hc1 := allStepsGtFrom_sound (TCollatz 6) 290743719 12 290743719 (by decide)
  have hc2 := allStepsGtFrom_sound (TCollatz 6) 290743719 12 1397145447 (by decide)
  have hc3 := allStepsGtFrom_sound (TCollatz 6) 290743719 12 6713870503 (by decide)
  have hc4 := allStepsGtFrom_sound (TCollatz 6) 290743719 12 32262966823 (by decide)
  have h24 : iterNat (TCollatz 6) 24 290743719 = 6713870503 := by
    have : (24 : Nat) = 12 + 12 := rfl
    rw [this, iterNat_add, T6_step12_1, T6_step12_2]
  have h36 : iterNat (TCollatz 6) 36 290743719 = 32262966823 := by
    have : (36 : Nat) = 24 + 12 := rfl
    rw [this, iterNat_add, h24, T6_step12_3]
  intro t ht1 ht2
  by_cases h1 : t ≤ 12
  · exact hc1 t ht1 h1
  · by_cases h2 : t ≤ 24
    · have ht : t = 12 + (t - 12) := by omega
      rw [ht, iterNat_add, T6_step12_1]
      exact hc2 (t - 12) (by omega) (by omega)
    · by_cases h3 : t ≤ 36
      · have ht : t = 24 + (t - 24) := by omega
        rw [ht, iterNat_add, h24]
        exact hc3 (t - 24) (by omega) (by omega)
      · have ht : t = 36 + (t - 36) := by omega
        rw [ht, iterNat_add, h36]
        exact hc4 (t - 36) (by omega) (by omega)

/-- **Positive Integer 6-Cycle at `k = 8`**:
`975 → 1335 → 1875 → 2685 → 3900 → 1950 → 975`, proving global convergence to `{0, 1, 2}`
genuinely fails for `T_8`! -/
theorem T8_cycle6_period : iterNat (TCollatz 8) 6 975 = 975 := by decide

theorem iterNat_mod_period (f : Nat → Nat) (x p : Nat) (hper : iterNat f p x = x) :
    ∀ m : Nat, iterNat f m x = iterNat f (m % p) x := by
  intro m
  by_cases hp : p = 0
  · subst hp; simp
  · induction m using Nat.strongRecOn with
    | ind m ih =>
      by_cases hlt : m < p
      · rw [Nat.mod_eq_of_lt hlt]
      · have hsub : m = p + (m - p) := by omega
        have hlt2 : m - p < m := by omega
        have hmod : m % p = (m - p) % p := by
          calc
            m % p = (p + (m - p)) % p := by rw [← hsub]
            _ = (m - p) % p := Nat.add_mod_left p (m - p)
        rw [hmod]
        calc
          iterNat f m x = iterNat f (p + (m - p)) x := by rw [← hsub]
          _ = iterNat f (m - p) (iterNat f p x) := iterNat_add f p (m - p) x
          _ = iterNat f (m - p) x := by rw [hper]
          _ = iterNat f ((m - p) % p) x := ih (m - p) hlt2

theorem T8_nontrivial_6cycle_never_drops :
    ∀ m : Nat, 975 ≤ iterNat (TCollatz 8) m 975 := by
  intro m
  rw [iterNat_mod_period (TCollatz 8) 975 6 T8_cycle6_period m]
  have hlt : m % 6 < 6 := Nat.mod_lt m (by decide)
  have hcases : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> rw [h] <;> decide

/-- **XOR-Collatz Sharpness (`c = 1` vs `c = 3` at `k = 3`)**:
`3` is a fixed point of `X_{3,1}`, so `X_{3,1}` never converges to `0` from `3`,
whereas `X_{3,3}` drives every `n : Nat` to `0`! -/
theorem X31_fixed_point_3 : ∀ m : Nat, iterNat (TXorCollatz 3 1) m 3 = 3 := by
  intro m
  have h1 : iterNat (TXorCollatz 3 1) 1 3 = 3 := by decide
  rw [iterNat_mod_period (TXorCollatz 3 1) 3 1 h1 m, Nat.mod_one]
  rfl

/-- **Exact Sharpness of Gray-Quadratic Valuation Ceilings**:
`2^11` DOES divide `F_1(549)`, and `2^14` DOES divide `F_2(4385)`! -/
theorem grayQuad1_sharp_witness :
    2 ^ 11 ∣ (549 ^^^ (549 >>> 1)) * (549 ^^^ (549 >>> 1)) + 1 * 549 + 10 := by
  refine ⟨331, by decide⟩

theorem grayQuad2_sharp_witness :
    2 ^ 14 ∣ (4385 ^^^ (4385 >>> 1)) * (4385 ^^^ (4385 >>> 1)) + 3 * 4385 + 60 := by
  refine ⟨2641, by decide⟩

/-- **Parameter Sharpness for `G(n)^2 + 3n + b`**: shifting `b = 60` to `b = 56` or `b = 64`
breaks the finite cover and yields divisibility by `2^20`! -/
theorem grayQuad2_param_sharp_56 :
    ((430824 ^^^ (430824 >>> 1)) * (430824 ^^^ (430824 >>> 1)) + 3 * 430824 + 56) % 2 ^ 20 = 0 := by
  decide

theorem grayQuad2_param_sharp_64 :
    ((600384 ^^^ (600384 >>> 1)) * (600384 ^^^ (600384 >>> 1)) + 3 * 600384 + 64) % 2 ^ 20 = 0 := by
  decide

/-! ## Section 6: Kernel-Checked Negative / Mutation Tests (Broken Certificates Rejected!) -/

theorem neg_test_1_T4_cert_on_T5 :
    checkCover (validDescent collatzCore 5 3 1 2) 0 0 treeT4 = false := by decide

theorem neg_test_2_T5_cert_on_T6 :
    checkCover (validDescent collatzCore 6 3 1 2) 0 0 treeT5 = false := by decide

theorem neg_test_3_truncated_T3_branch :
    checkCover (validDescent collatzCore 3 3 1 2) 0 0
      (CoverTree.branch (CoverTree.leaf 1) (CoverTree.leaf 1)) = false := by decide

theorem neg_test_4_zero_step_leaf :
    checkCover (validDescent collatzCore 4 3 1 2) 0 0
      (CoverTree.branch (CoverTree.leaf 0) (CoverTree.leaf 2)) = false := by decide

theorem neg_test_5_corrupted_GQ2_val_leaf :
    checkCover (validVal (grayQuadExpr 3 60)) 0 0
      (CoverTree.branch (CoverTree.leaf 0) (CoverTree.leaf 0)) = false := by decide

theorem neg_test_6_GQ1_cert_on_GQ2 :
    checkCover (validVal (grayQuadExpr 3 60)) 0 0 treeGQ1 = false := by decide

theorem neg_test_7_insufficient_lookahead_neq :
    checkCover (validNeq (grayQuadExpr 3 60) shift15Expr) 0 0 (CoverTree.leaf 1) = false := by decide

end AdicCompactness
