import ErdosLean.Erdos514.Defs

/-! # Erdős #514 — Part: entire functions of polynomial growth are polynomials.
Cauchy estimates: the `k`-th Taylor coefficient is
`≤ A (1+r)^m / r^k → 0` for `k > m`; then `f = ∑_{k ≤ m} aₖ zᵏ` by the power series of an
entire function (`Complex.hasSum_taylorSeries_of_entire` or
`Differentiable.hasFPowerSeriesOnBall`). -/

namespace Erdos514

/-- The difference quotient at `0` of an entire function is entire. -/
lemma alt_differentiable_dslope {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (dslope g 0) := by
  have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
    Filter.univ_mem).mpr hg.differentiableOn
  exact fun z => (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem

theorem poly_of_norm_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {A : ℝ} {m : ℕ}
    (hA : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ m) : ∃ p : Polynomial ℂ, ∀ z, g z = p.eval z := by
  induction m generalizing g A with
  | zero =>
    have hb : Bornology.IsBounded (Set.range g) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨A, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa using hA z
    refine ⟨Polynomial.C (g 0), fun z => ?_⟩
    simp [hg.apply_eq_apply_of_bounded hb z 0]
  | succ m ih =>
    set h := dslope g 0 with hh
    have hdh : Differentiable ℂ h := alt_differentiable_dslope hg
    have hA0 : 0 ≤ A := by
      have := hA 0
      simp at this
      exact (norm_nonneg _).trans this
    -- bound on the closed unit ball
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      hdh.continuous.continuousOn
    have hbound : ∀ z, ‖h z‖ ≤ (max B 0 + 2 * A + ‖g 0‖) * (1 + ‖z‖) ^ m := by
      intro z
      have hpow : 1 ≤ (1 + ‖z‖) ^ m := one_le_pow₀ (by linarith [norm_nonneg z])
      by_cases hz : ‖z‖ ≤ 1
      · have h1 := hB z (by simpa using hz)
        have : ‖h z‖ ≤ max B 0 + 2 * A + ‖g 0‖ := by
          have := le_max_left B 0
          nlinarith [norm_nonneg (g 0)]
        calc ‖h z‖ ≤ max B 0 + 2 * A + ‖g 0‖ := this
          _ ≤ (max B 0 + 2 * A + ‖g 0‖) * (1 + ‖z‖) ^ m := by
            have : 0 ≤ max B 0 + 2 * A + ‖g 0‖ := by
              have := le_max_right B 0; nlinarith [norm_nonneg (g 0)]
            nlinarith
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hz; linarith
        have hzpos : 0 < ‖z‖ := by linarith
        have hform : ‖z‖ * ‖h z‖ = ‖g z - g 0‖ := by
          have := sub_smul_dslope g 0 z
          rw [sub_zero, smul_eq_mul] at this
          rw [← norm_mul, this]
        have hgz := hA z
        have key : ‖z‖ * ‖h z‖ ≤ ‖z‖ * ((2 * A + ‖g 0‖) * (1 + ‖z‖) ^ m) := by
          rw [hform]
          calc ‖g z - g 0‖ ≤ ‖g z‖ + ‖g 0‖ := norm_sub_le _ _
            _ ≤ A * (1 + ‖z‖) ^ (m + 1) + ‖g 0‖ := by linarith
            _ ≤ ‖z‖ * ((2 * A + ‖g 0‖) * (1 + ‖z‖) ^ m) := by
              rw [pow_succ]
              have h2 : A * ((1 + ‖z‖) ^ m * (1 + ‖z‖)) ≤ ‖z‖ * (2 * A * (1 + ‖z‖) ^ m) := by
                have : (1 + ‖z‖) ≤ 2 * ‖z‖ := by linarith
                have hp0 : 0 ≤ A * (1 + ‖z‖) ^ m := mul_nonneg hA0 (by positivity)
                nlinarith
              have h3 : ‖g 0‖ ≤ ‖z‖ * (‖g 0‖ * (1 + ‖z‖) ^ m) := by
                have : ‖g 0‖ ≤ ‖g 0‖ * (1 + ‖z‖) ^ m := by nlinarith [norm_nonneg (g 0)]
                nlinarith [norm_nonneg (g 0)]
              nlinarith
        have := le_of_mul_le_mul_left key hzpos
        have hB0 : 0 ≤ max B 0 := le_max_right B 0
        nlinarith
    obtain ⟨p, hp⟩ := ih hdh hbound
    refine ⟨Polynomial.C (g 0) + Polynomial.X * p, fun z => ?_⟩
    have := sub_smul_dslope g 0 z
    rw [sub_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    rw [← hp z]
    linear_combination -this

end Erdos514
