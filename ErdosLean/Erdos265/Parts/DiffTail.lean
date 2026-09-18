import ErdosLean.Erdos265.Parts.RatTails

/-!
# Erdős #265 — Part U2: the difference tail `Dt n = ∑_{k≥n} 1/(a_k(a_k-1))`

* `Dt n = V n - T n`, `Dt n = 1/(a_n(a_n-1)) + Dt (n+1)`, `0 < Dt n`;
* `Dt n ≤ 1/(a_n - 1)` (strict monotonicity: `∑_{k≥n} 1/(a_k(a_k-1)) ≤ ∑_{m≥a_n} 1/(m(m-1))`,
  telescoping);
* `1/a_n² ≤ Dt n`;
* integrality: `(b d) P n Ps n · Dt n = a_n-free integer combination > 0`, hence
  `1 ≤ K · P n² · Dt n` with `K = b d` (using `Ps n ≤ P n`).
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

lemma recipD_eq (ha : IsRationalPair a) (n : ℕ) : recipD a n = recipS a n - recip a n := by
  have h2 : (2 : ℝ) ≤ a n := by exact_mod_cast two_le_of ha n
  have h1 : (a n : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (a n : ℝ) ≠ 0 := by linarith
  unfold recipD recipS recip
  field_simp
  ring

lemma recipD_pos (ha : IsRationalPair a) (n : ℕ) : 0 < recipD a n := by
  have h2 : (2 : ℝ) ≤ a n := by exact_mod_cast two_le_of ha n
  unfold recipD
  have : 0 < (a n : ℝ) * ((a n : ℝ) - 1) := by nlinarith
  positivity

lemma summable_recipD (ha : IsRationalPair a) : Summable (recipD a) := by
  have : recipD a = fun k => recipS a k - recip a k := funext (recipD_eq ha)
  rw [this]
  exact (summable_recipS ha).sub (summable_recip ha)

theorem Dt_eq_V_sub_T (ha : IsRationalPair a) (n : ℕ) : Dt a n = V a n - T a n := by
  unfold Dt V T tail
  have h1 : Summable (fun k => recipS a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recipS ha)
  have h2 : Summable (fun k => recip a (k + n)) :=
    (summable_nat_add_iff n).mpr (summable_recip ha)
  rw [← h1.tsum_sub h2]
  exact tsum_congr (fun k => recipD_eq ha (k + n))

theorem Dt_succ (ha : IsRationalPair a) (n : ℕ) : Dt a n = recipD a n + Dt a (n + 1) :=
  tail_eq_add_tail_succ (summable_recipD ha) n

theorem Dt_pos (ha : IsRationalPair a) (n : ℕ) : 0 < Dt a n := by
  unfold Dt tail
  exact ((summable_nat_add_iff n).mpr (summable_recipD ha)).tsum_pos
    (fun k => (recipD_pos ha (k + n)).le) 0 (recipD_pos ha (0 + n))

lemma recipD_le_tele (ha : IsRationalPair a) (n k : ℕ) :
    recipD a (k + n) ≤ 1 / ((a n : ℝ) + k - 1) - 1 / ((a n : ℝ) + k) := by
  have h2 : (2 : ℝ) ≤ a n := by exact_mod_cast two_le_of ha n
  have hle : ((a n : ℝ) + k) ≤ a (k + n) := by
    have := ha.1.add_le_nat k n
    exact_mod_cast (by omega : a n + k ≤ a (k + n))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA : (0:ℝ) < ((a n : ℝ) + k) * ((a n : ℝ) + k - 1) := by nlinarith
  have hrhs : 1 / ((a n : ℝ) + k - 1) - 1 / ((a n : ℝ) + k)
      = 1 / (((a n : ℝ) + k) * ((a n : ℝ) + k - 1)) := by
    have : (a n : ℝ) + k - 1 ≠ 0 := by linarith
    have : (a n : ℝ) + k ≠ 0 := by linarith
    field_simp
    ring
  rw [hrhs]
  unfold recipD
  apply one_div_le_one_div_of_le hA
  apply mul_le_mul hle (by linarith) (by linarith) (by linarith)

theorem Dt_le (ha : IsRationalPair a) (n : ℕ) : Dt a n ≤ 1 / ((a n : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ a n := by exact_mod_cast two_le_of ha n
  unfold Dt tail
  apply Real.tsum_le_of_sum_range_le (fun k => (recipD_pos ha (k + n)).le)
  intro N
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, recipD a (k + n)
      ≤ 1 / ((a n : ℝ) - 1) - 1 / ((a n : ℝ) + N - 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := recipD_le_tele ha n N
      push_cast
      have e : (a n : ℝ) + ((N : ℝ) + 1) - 1 = (a n : ℝ) + N := by ring
      rw [e]
      linarith
  have hpos : 0 ≤ 1 / ((a n : ℝ) + N - 1) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    apply div_nonneg zero_le_one; linarith
  linarith [key N]

theorem inv_sq_le_Dt (ha : IsRationalPair a) (n : ℕ) : 1 / (a n : ℝ) ^ 2 ≤ Dt a n := by
  have h2 : (2 : ℝ) ≤ a n := by exact_mod_cast two_le_of ha n
  rw [Dt_succ ha n]
  have hD := Dt_pos ha (n + 1)
  have : 1 / (a n : ℝ) ^ 2 ≤ recipD a n := by
    unfold recipD
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  linarith

/-- The rational gap for the difference tail. -/
theorem Dt_lower (ha : IsRationalPair a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n, 1 ≤ K * (P a n : ℝ) ^ 2 * Dt a n := by
  obtain ⟨b, d, hb, hd, hT, hV⟩ := int_scale ha
  refine ⟨(b : ℝ) * d, ?_, ?_⟩
  · have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  intro n
  obtain ⟨z1, hz1⟩ := hT n
  obtain ⟨z2, hz2⟩ := hV n
  push_cast at hz1 hz2
  have hPpos : 0 < P a n := by
    unfold P
    exact Finset.prod_pos (fun k _ => by have := two_le_of ha k; omega)
  have hPspos : 0 < Ps a n := by
    unfold Ps
    exact Finset.prod_pos (fun k _ => by have := two_le_of ha k; omega)
  have hPsle : Ps a n ≤ P a n := by
    unfold Ps P
    exact Finset.prod_le_prod (fun k _ => Nat.sub_le _ _)
  have hD := Dt_pos ha n
  have hint : (b : ℝ) * d * (P a n) * (Ps a n) * Dt a n
      = (b : ℝ) * (P a n) * z2 - (d : ℝ) * (Ps a n) * z1 := by
    rw [Dt_eq_V_sub_T ha n, ← hz1, ← hz2]; ring
  set m : ℤ := (b : ℤ) * (P a n) * z2 - (d : ℤ) * (Ps a n) * z1 with hm
  have hmR : ((m : ℤ) : ℝ) = (b : ℝ) * d * (P a n) * (Ps a n) * Dt a n := by
    rw [hint, hm]; push_cast; ring
  have hposR : (0 : ℝ) < (b : ℝ) * d * (P a n) * (Ps a n) * Dt a n := by
    have : (0 : ℝ) < b := by exact_mod_cast hb
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < P a n := by exact_mod_cast hPpos
    have : (0 : ℝ) < Ps a n := by exact_mod_cast hPspos
    positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : (0 : ℤ) < m := by exact_mod_cast (hmR ▸ hposR)
    exact_mod_cast (show (1 : ℤ) ≤ m by omega)
  have hle : (Ps a n : ℝ) ≤ P a n := by exact_mod_cast hPsle
  have hbd : (0 : ℝ) ≤ (b : ℝ) * d * (P a n) * Dt a n := by positivity
  have : (b : ℝ) * d * (P a n) * (Ps a n) * Dt a n ≤ (b : ℝ) * d * (P a n : ℝ) ^ 2 * Dt a n := by
    have := mul_le_mul_of_nonneg_left hle hbd
    nlinarith
  linarith

end Erdos265
