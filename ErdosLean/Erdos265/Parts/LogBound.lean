import ErdosLean.Erdos265.Parts.SquareRec

/-!
# Erdős #265 — Part U5: `a_n ≤ Henv (n+1)`

`Henv (n+1) = P (n+1)/√(Dt (n+1)) ≥ P (n+1) = P n · a_n ≥ a_n`
(because `Dt (n+1) ≤ 1`).
-/

open Filter Topology

namespace Erdos265

variable {a : ℕ → ℕ}

theorem lb_one_le_P_of (ha : IsRationalPair a) (n : ℕ) : 1 ≤ P a n := by
  unfold P
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have := two_le_of ha n
    nlinarith

theorem lb_a_le_P_succ (ha : IsRationalPair a) (n : ℕ) : (a n : ℝ) ≤ (P a (n + 1) : ℝ) := by
  have h1 := lb_one_le_P_of ha n
  have hP : P a (n + 1) = P a n * a n := by
    unfold P; rw [Finset.prod_range_succ]
  rw [hP]
  push_cast
  have : (1 : ℝ) ≤ (P a n : ℝ) := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ (a n : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem lb_Dt_le_one (ha : IsRationalPair a) (n : ℕ) : Dt a n ≤ 1 := by
  have h := Dt_le ha n
  have h2 : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  have hpos : (0 : ℝ) < (a n : ℝ) - 1 := by linarith
  calc Dt a n ≤ 1 / ((a n : ℝ) - 1) := h
    _ ≤ 1 := by rw [div_le_one hpos]; linarith

theorem lb_a_le_Henv_succ (ha : IsRationalPair a) (n : ℕ) :
    (a n : ℝ) ≤ Henv a (n + 1) := by
  have hD := Dt_pos ha (n + 1)
  have hD1 := lb_Dt_le_one ha (n + 1)
  have hs : 0 < Real.sqrt (Dt a (n + 1)) := Real.sqrt_pos.mpr hD
  have hs1 : Real.sqrt (Dt a (n + 1)) ≤ 1 := Real.sqrt_le_one.mpr hD1
  have hP := lb_a_le_P_succ ha n
  have hP0 : (0 : ℝ) ≤ (P a (n + 1) : ℝ) := Nat.cast_nonneg _
  unfold Henv
  rw [le_div_iff₀ hs]
  nlinarith [Nat.cast_nonneg (α := ℝ) (a n)]

theorem log_a_le_log_Henv_succ (ha : IsRationalPair a) (n : ℕ) :
    Real.log (a n : ℝ) ≤ Real.log (Henv a (n + 1)) := by
  have h2 : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  exact Real.log_le_log (by linarith) (lb_a_le_Henv_succ ha n)

theorem log_a_nonneg (ha : IsRationalPair a) (n : ℕ) : 0 ≤ Real.log (a n : ℝ) := by
  have h2 : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast two_le_of ha n
  exact Real.log_nonneg (by linarith)

end Erdos265
