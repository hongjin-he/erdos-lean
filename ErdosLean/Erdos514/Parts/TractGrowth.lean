import ErdosLean.Erdos514.Parts.PolyOfGrowth
import ErdosLean.Erdos514.Parts.TractUnbounded
import ErdosLean.Erdos514.Parts.CircleCrossing
import ErdosLean.Erdos514.Parts.CarlemanGrowth

/-! # Erdős #514 — Part: every tract of a transcendental entire function grows faster than
`|z|`

Suppose `‖g z‖ ≤ A (1 + ‖z‖)` on `D = tract g K z₀`.
* If `superlevel g K ⊆ D`, then `‖g z‖ ≤ (|A| + K)(1 + ‖z‖)` everywhere, so `g` is a
  polynomial (`poly_of_norm_le`), contradiction.
* Otherwise pick `w ∈ superlevel g K \ D`.  `W = tract g K w` is disjoint from `D`,
  preconnected and unbounded (`tract_not_bounded`), so it meets every circle of radius
  `≥ ‖w‖` (`exists_mem_norm_eq`) in points outside `D`.  `carleman_growth` then gives
  `z ∈ D` with `c √r ≤ log(‖g z‖/K) ≤ log(A(1+r)/K)` for all large `r`, contradiction. -/

namespace Erdos514

/-- `log (B (1 + r)) < c √r` for all large `r`. -/
lemma alt_log_lt_sqrt {B c : ℝ} (hB : 0 < B) (hc : 0 < c) :
    ∃ R : ℝ, ∀ r ≥ R, Real.log (B * (1 + r)) < c * Real.sqrt r := by
  refine ⟨1 + 512 * B / c ^ 4, fun r hr => ?_⟩
  have hc4 : 0 < c ^ 4 := by positivity
  have hBc : 0 ≤ 512 * B / c ^ 4 := by positivity
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set x := B * (1 + r) with hx
  have hxpos : 0 < x := by positivity
  clear_value x
  -- log x = 4 log (√√x) < 4 √√x
  have hlog : Real.log x < 4 * Real.sqrt (Real.sqrt x) := by
    have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hxpos.le]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (Real.sqrt x) by positivity)
    rw [h1]; linarith
  -- 4 √√x ≤ c √r
  have hkey : 4 * Real.sqrt (Real.sqrt x) ≤ c * Real.sqrt r := by
    -- square twice: 256 x ≤ c^4 r^2
    have hx2 : 256 * x ≤ c ^ 4 * r ^ 2 := by
      have hrB : 512 * B ≤ c ^ 4 * r := by
        have : 512 * B / c ^ 4 ≤ r := by linarith
        rw [div_le_iff₀ hc4] at this; linarith
      have : 1 + r ≤ 2 * r := by linarith
      calc 256 * x = 256 * B * (1 + r) := by rw [hx]; ring
        _ ≤ 256 * B * (2 * r) := by gcongr
        _ = (512 * B) * r := by ring
        _ ≤ (c ^ 4 * r) * r := by gcongr
        _ = c ^ 4 * r ^ 2 := by ring
    have hs1 : 16 * Real.sqrt x ≤ c ^ 2 * r := by
      have h := Real.sqrt_le_sqrt hx2
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 256) x, show (256 : ℝ) = 16 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num), show c ^ 4 * r ^ 2 = (c ^ 2 * r) ^ 2 by ring,
        Real.sqrt_sq (by positivity)] at h
      exact h
    have h := Real.sqrt_le_sqrt hs1
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16) (Real.sqrt x),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4),
      Real.sqrt_mul (sq_nonneg c) r, Real.sqrt_sq hc.le] at h
    exact h
  linarith

theorem tract_growth {g : ℂ → ℂ} (hg : IsTranscendentalEntire g) {K : ℝ} (hK : 0 < K) {z₀ : ℂ}
    (hz₀ : K < ‖g z₀‖) (A : ℝ) : ∃ z ∈ tract g K z₀, A * (1 + ‖z‖) < ‖g z‖ := by
  by_contra hcon
  push Not at hcon
  -- hcon : ∀ z ∈ tract g K z₀, ‖g z‖ ≤ A * (1 + ‖z‖)
  by_cases hsub : superlevel g K ⊆ tract g K z₀
  · -- polynomial growth everywhere
    apply hg.2
    refine poly_of_norm_le (m := 1) (A := |A| + K) hg.1 (fun z => ?_)
    rw [pow_one]
    have hz1 : 0 ≤ ‖z‖ := norm_nonneg z
    by_cases hz : z ∈ superlevel g K
    · have := hcon z (hsub hz)
      have : A * (1 + ‖z‖) ≤ |A| * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
      nlinarith [abs_nonneg A]
    · have : ‖g z‖ ≤ K := not_lt.mp hz
      nlinarith [abs_nonneg A]
  · rw [Set.not_subset] at hsub
    obtain ⟨w, hw, hwD⟩ := hsub
    have hw' : K < ‖g w‖ := hw
    -- the tract through `w` is disjoint from `D`
    have hdisj : ∀ z ∈ tract g K w, z ∉ tract g K z₀ := by
      intro z hzW hzD
      apply hwD
      have h1 : tract g K w = tract g K z := connectedComponentIn_eq hzW
      have h2 : tract g K z₀ = tract g K z := connectedComponentIn_eq hzD
      rw [h2, ← h1]
      exact mem_tract_self hw'
    have hcross : ∃ r₀ : ℝ, ∀ r ≥ r₀, ∃ w' : ℂ, ‖w'‖ = r ∧ w' ∉ tract g K z₀ := by
      refine ⟨‖w‖, fun r hr => ?_⟩
      obtain ⟨z, hzW, hzr⟩ := exists_mem_norm_eq (isPreconnected_tract g K w)
        (tract_not_bounded hg.1 hw') (mem_tract_self hw') hr
      exact ⟨z, hzr, hdisj z hzW⟩
    obtain ⟨c, hc, r₁, hr₁⟩ := carleman_growth hg.1 hK hz₀ hcross
    -- `A > 0`
    have hA : 0 < A := by
      have := hcon z₀ (mem_tract_self hz₀)
      by_contra hA
      push Not at hA
      have : A * (1 + ‖z₀‖) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hA (by linarith [norm_nonneg z₀])
      linarith
    obtain ⟨R, hR⟩ := alt_log_lt_sqrt (B := A / K) (div_pos hA hK) hc
    obtain ⟨z, hzD, hzr, hzc⟩ := hr₁ (max r₁ (max R 0)) (le_max_left _ _)
    set r := max r₁ (max R 0)
    have hrR : R ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
    have hlt := hR r hrR
    have hgz := hcon z hzD
    have hgK : K < ‖g z‖ := tract_subset_superlevel g K z₀ hzD
    have hle : Real.log (‖g z‖ / K) ≤ Real.log (A / K * (1 + r)) := by
      apply Real.log_le_log (div_pos (hK.trans hgK) hK)
      rw [← hzr, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hgz hK.le
    linarith

end Erdos514
