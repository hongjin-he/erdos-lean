import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: lower bound for `|f(z)/zⁿ|` through the shift
`f z / zⁿ = ∑_{k ≤ n} aₖ z^{k-n} + z · shift f (n+1) z`, and `|z^{k-n}| ≤ 1` for `|z| ≥ 1`,
so `C = ∑_{k ≤ n} ‖aₖ‖` works.  Purely algebraic: no hypothesis on `f`. -/

namespace Erdos514

lemma alt_expand (f : ℂ → ℂ) (m : ℕ) (z : ℂ) :
    f z = (∑ k ∈ Finset.range m, shift f k 0 * z ^ k) + z ^ m * shift f m z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := sub_smul_dslope (shift f m) 0 z
    simp only [sub_zero, smul_eq_mul] at h
    nth_rewrite 1 [ih]
    rw [Finset.sum_range_succ, shift_succ]
    linear_combination (-(z ^ m)) * h

theorem ratio_bound (f : ℂ → ℂ) (n : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ * ‖shift f (n + 1) z‖ - C ≤ ‖f z / z ^ n‖ := by
  refine ⟨∑ k ∈ Finset.range (n+1), ‖shift f k 0‖, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz0
  have hexp := alt_expand f (n+1) z
  set S := ∑ k ∈ Finset.range (n+1), shift f k 0 * z ^ k with hSdef
  set s := shift f (n+1) z with hsdef
  have key : f z / z ^ n = S / z ^ n + z * s := by
    rw [hexp]; field_simp; ring
  have hS : ‖S / z ^ n‖ ≤ ∑ k ∈ Finset.range (n+1), ‖shift f k 0‖ := by
    rw [norm_div, div_le_iff₀ (by positivity)]
    calc ‖S‖ ≤ ∑ k ∈ Finset.range (n+1), ‖shift f k 0 * z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), ‖shift f k 0‖ * ‖z ^ n‖ := by
        apply Finset.sum_le_sum; intro k hk
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [norm_pow, norm_pow]
        exact pow_le_pow_right₀ hz (by simp at hk; omega)
      _ = _ := by rw [Finset.sum_mul]
  have h3 : ‖z * s‖ ≤ ‖f z / z ^ n‖ + ‖S / z ^ n‖ := by
    rw [key]
    have := norm_sub_le (S / z ^ n + z * s) (S / z ^ n)
    simpa using this
  rw [norm_mul] at h3
  linarith

end Erdos514
