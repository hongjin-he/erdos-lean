import ErdosLean.Erdos956.Parts.BodySupport

/-!
# Erdős #956 — Part 7: `dist(γ(t), D) = 1` (note, Lemma 2)

`‖γ(t) - p(t)‖ = ‖ν(t)‖ = 1`, and for `z ∈ D`,
`‖γ(t) - z‖ ≥ ⟨γ(t) - z, ν(t)⟩ ≥ ⟨γ(t) - p(t), ν(t)⟩ = 1` (Cauchy–Schwarz in coordinates:
`(v₀ t + v₁)² ≤ (v₀² + v₁²)(t² + 1)`).
-/

namespace Erdos956

private lemma norm_eq_sqrt_coords (v : E) : ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]

lemma norm_γ_sub_pp (e t : ℝ) : ‖γ e t - pp e t‖ = 1 := by
  rw [norm_eq_sqrt_coords]
  simp only [PiLp.sub_apply, γ_zero, γ_one, pp_zero, pp_one]
  have hr := rr_pos t
  have hsq := rr_sq t
  have h : (t - (t - t / rr t)) ^ 2 + (1 + e - t ^ 2 / 2 - (1 + e - t ^ 2 / 2 - 1 / rr t)) ^ 2
      = 1 := by
    have : (t - (t - t / rr t)) ^ 2 + (1 + e - t ^ 2 / 2 - (1 + e - t ^ 2 / 2 - 1 / rr t)) ^ 2
        = (t ^ 2 + 1) / rr t ^ 2 := by
      field_simp; ring
    rw [this, hsq]; field_simp; ring
  rw [h, Real.sqrt_one]

lemma one_le_norm_γ_sub {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (htW : t ≤ W k)
    {z : E} (hz : z ∈ D k) : 1 ≤ ‖γ (η k) t - z‖ := by
  have hsup := mem_D_support hk ht0 htW hz
  have hr := rr_pos t
  have hsq := rr_sq t
  set v : E := γ (η k) t - z with hv
  have hv0 : v 0 = t - z 0 := by simp [hv]
  have hv1 : v 1 = 1 + η k - t ^ 2 / 2 - z 1 := by simp [hv]
  -- ⟨v, (t,1)⟩ ≥ ⟨γ - p, (t,1)⟩ = r
  have hp0 : pp (η k) t 0 = t - t / rr t := rfl
  have hp1 : pp (η k) t 1 = 1 + η k - t ^ 2 / 2 - 1 / rr t := rfl
  have hkey : t / rr t * t + 1 / rr t = rr t := by
    field_simp; nlinarith [hsq]
  have hdot : rr t ≤ v 0 * t + v 1 := by
    rw [hv0, hv1]; rw [hp0, hp1] at hsup; nlinarith [hsup, hkey]
  -- Cauchy–Schwarz: (v0 t + v1)^2 ≤ (v0^2+v1^2)(t^2+1) = ‖v‖^2 r^2
  have hn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [norm_eq_sqrt_coords, Real.sq_sqrt (by positivity)]
  have hcs : (v 0 * t + v 1) ^ 2 ≤ (‖v‖ * rr t) ^ 2 := by
    rw [mul_pow, hn, hsq]; nlinarith [sq_nonneg (v 0 - v 1 * t)]
  have hnn : 0 ≤ ‖v‖ * rr t := mul_nonneg (norm_nonneg _) hr.le
  have hle : v 0 * t + v 1 ≤ ‖v‖ * rr t := abs_le_of_sq_le_sq' hcs hnn |>.2
  have : rr t * 1 ≤ rr t * ‖v‖ := by nlinarith
  exact le_of_mul_le_mul_left this hr

end Erdos956
