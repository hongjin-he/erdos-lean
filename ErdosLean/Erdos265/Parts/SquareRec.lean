import ErdosLean.Erdos265.Parts.DiffTail

/-!
# Erdős #265 — Part U3: the square recurrence for the tail envelope

With `Henv n = P n / √(Dt n)` and `1 ≤ K P_n² D_n` (Part U2):
`Henv (n+1) ≤ 4 √K · Henv n ²`.  Two cases, `D = Dt n`, `D' = Dt (n+1)`, `x = a_n`:
* head dominates (`D/2 ≤ 1/(x(x-1))`): `x² ≤ 4/D`, and `1/√D' ≤ √K · P x`, so
  `P x / √D' ≤ √K P² x² ≤ 4√K P²/D`;
* tail dominates: `D' ≥ D/2`, and `x ≤ 1 + 1/D ≤ 2/D` (from `D ≤ 1/(x-1)`, `D ≤ 1`),
  `1/√D ≤ √K P`, so `P x/√D' ≤ √2 P x/√D ≤ 2√2 P/ D^{3/2} ≤ 4√K P²/D`.
Also `Henv n ≥ P n ≥ 1` since `Dt n ≤ 1`.

In the formal proof we square everything: the key inequality is `x² D² ≤ 16 K P² D'`
(`sq_rec_key`), from which `Henv (n+1)² ≤ (4√K · Henv n²)²`.
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

/-- `1 ≤ P n` (all factors are `≥ 2`). -/
theorem one_le_P_real (ha : IsRationalPair a) (n : ℕ) : (1 : ℝ) ≤ (P a n : ℝ) := by
  have : 1 ≤ P a n := by
    unfold P
    rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro k _
    have := two_le_of ha k
    omega
  exact_mod_cast this

theorem P_succ_real (n : ℕ) : (P a (n + 1) : ℝ) = (P a n : ℝ) * (a n : ℝ) := by
  unfold P
  rw [Finset.prod_range_succ]
  push_cast
  ring

/-- `Dt n ≤ 1`. -/
theorem Dt_le_one (ha : IsRationalPair a) (n : ℕ) : Dt a n ≤ 1 := by
  have h1 := Dt_le ha n
  have h2 : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have h3 : 1 / ((a n : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

theorem one_le_Henv (ha : IsRationalPair a) (n : ℕ) : 1 ≤ Henv a n := by
  unfold Henv
  have hD := Dt_pos ha n
  have hs : 0 < Real.sqrt (Dt a n) := Real.sqrt_pos.mpr hD
  have hs1 : Real.sqrt (Dt a n) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact Dt_le_one ha n
  have hP := one_le_P_real ha n
  rw [le_div_iff₀ hs]
  nlinarith

/-- The real-arithmetic core of the square recurrence. -/
theorem sq_rec_key (X D D' Q : ℝ) (hX : 2 ≤ X) (hD : D = 1 / (X * (X - 1)) + D')
    (hD' : 0 < D') (hle : D ≤ 1 / (X - 1)) (h1 : 1 ≤ Q * D) (h2 : 1 ≤ Q * X ^ 2 * D') :
    X ^ 2 * D ^ 2 ≤ 16 * Q * D' := by
  have hX1 : 0 < X - 1 := by linarith
  have hXX : 0 < X * (X - 1) := by positivity
  set h := 1 / (X * (X - 1)) with hh
  have hpos : 0 < h := by positivity
  have hhX : h * (X * (X - 1)) = 1 := by rw [hh]; field_simp
  have hDpos : 0 < D := by linarith
  have hQ : 0 < Q := by
    by_contra hc; push Not at hc; nlinarith
  rcases le_or_gt D' h with hc | hc
  · -- head dominates
    have hD2 : D ≤ 2 * h := by linarith
    -- X² h ≤ 2
    have hXh : X ^ 2 * h ≤ 2 := by nlinarith
    -- X² D² ≤ 4 X² h² ≤ 8 h ; and X² h ≤ 2, so X^2 * (8h) ≤ 16
    have e1 : X ^ 2 * D ^ 2 ≤ 4 * (X ^ 2 * h) * h := by
      have : D ^ 2 ≤ (2 * h) ^ 2 := by
        apply pow_le_pow_left₀ hDpos.le hD2
      nlinarith [sq_nonneg X]
    have e2 : X ^ 2 * D ^ 2 ≤ 8 * h := by nlinarith
    -- 8 h X² ≤ 16 ≤ 16 Q X² D'
    have e3 : X ^ 2 * (8 * h) ≤ X ^ 2 * (16 * Q * D') := by nlinarith
    have hX2 : 0 < X ^ 2 := by positivity
    have e4 : 8 * h ≤ 16 * Q * D' := le_of_mul_le_mul_left e3 hX2
    linarith
  · -- tail dominates
    have hD2 : D ≤ 2 * D' := by linarith
    have hle' : D * (X - 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hle hX1.le
      rwa [div_mul_cancel₀ _ hX1.ne'] at this
    have hD1 : D ≤ 1 := by nlinarith
    have hXD : X * D ≤ 2 := by nlinarith
    have hXD0 : 0 ≤ X * D := by positivity
    have e1 : X ^ 2 * D ^ 2 ≤ 4 := by nlinarith
    nlinarith

theorem Henv_sq_rec (ha : IsRationalPair a) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, Henv a (n + 1) ≤ K * Henv a n ^ 2 := by
  obtain ⟨K, hK1, hK⟩ := Dt_lower ha
  have hK0 : 0 < K := by linarith
  refine ⟨4 * Real.sqrt K, by positivity, fun n => ?_⟩
  have hX : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  set X : ℝ := (a n : ℝ) with hXdef
  set D := Dt a n with hDdef
  set D' := Dt a (n + 1) with hD'def
  set p : ℝ := (P a n : ℝ) with hpdef
  have hDpos : 0 < D := Dt_pos ha n
  have hD'pos : 0 < D' := Dt_pos ha (n + 1)
  have hp : 1 ≤ p := one_le_P_real ha n
  have hsucc : D = 1 / (X * (X - 1)) + D' := by
    rw [hDdef, hD'def, Dt_succ ha n]; rfl
  have hle : D ≤ 1 / (X - 1) := Dt_le ha n
  have h1 : 1 ≤ (K * p ^ 2) * D := hK n
  have h2 : 1 ≤ (K * p ^ 2) * X ^ 2 * D' := by
    have := hK (n + 1)
    rw [P_succ_real] at this
    calc (1 : ℝ) ≤ K * (p * X) ^ 2 * D' := this
      _ = (K * p ^ 2) * X ^ 2 * D' := by ring
  have key := sq_rec_key X D D' (K * p ^ 2) hX hsucc hD'pos hle h1 h2
  -- square both sides
  have lhs_sq : Henv a (n + 1) ^ 2 = p ^ 2 * X ^ 2 / D' := by
    unfold Henv
    rw [P_succ_real, div_pow, Real.sq_sqrt hD'pos.le]
    ring
  have rhs_sq : (4 * Real.sqrt K * Henv a n ^ 2) ^ 2 = 16 * K * p ^ 4 / D ^ 2 := by
    unfold Henv
    rw [div_pow, Real.sq_sqrt hDpos.le, mul_pow, mul_pow, Real.sq_sqrt hK0.le]
    rw [div_pow]
    ring
  have hL : 0 ≤ Henv a (n + 1) := by
    unfold Henv; positivity
  have hR : 0 ≤ 4 * Real.sqrt K * Henv a n ^ 2 := by positivity
  rw [← pow_le_pow_iff_left₀ hL hR (two_ne_zero)]
  rw [lhs_sq, rhs_sq]
  rw [div_le_div_iff₀ hD'pos (by positivity)]
  have hp2 : 0 < p ^ 2 := by positivity
  have : p ^ 2 * (X ^ 2 * D ^ 2) ≤ p ^ 2 * (16 * (K * p ^ 2) * D') :=
    mul_le_mul_of_nonneg_left key hp2.le
  nlinarith

end Erdos265
