import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 4: the second-moment (Chung–Erdős) lemma

KM §5 (Cauchy–Schwarz for `Q(α) = ∑ 1_{A_q}(α)`):
`μ(⋃_{q∈F} A_q) ≥ (∑_F μ(A_q))² / ∑_{F²} μ(A_q ∩ A_r)`.
-/

open MeasureTheory Filter

namespace DuffinSchaeffer

/-- Finite Chung–Erdős inequality in "quadratic" form: for every real `t`,
`0 ≤ ∑∑ μ(A_n ∩ A_m) - 2 t ∑ μ(A_n) + t² μ(⋃_F A_n)`. -/
theorem chungErdos_quadratic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (F : Finset ℕ)
    (t : ℝ) :
    0 ≤ ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) - 2 * t * ∑ n ∈ F, μ.real (A n)
      + t ^ 2 * μ.real (⋃ n ∈ F, A n) := by
  set U := ⋃ n ∈ F, A n with hUdef
  have hU : MeasurableSet U := Finset.measurableSet_biUnion F (fun n _ => hA n)
  have hint : ∀ s : Set Ω, MeasurableSet s → Integrable (s.indicator (1 : Ω → ℝ)) μ :=
    fun s hs => (integrable_const (1 : ℝ)).indicator hs
  let g : Ω → ℝ := fun x =>
    (∑ n ∈ F, ∑ m ∈ F, (A n ∩ A m).indicator 1 x) - 2 * t * ∑ n ∈ F, (A n).indicator 1 x
      + t ^ 2 * U.indicator 1 x
  have hg : 0 ≤ ∫ x, g x ∂μ := by
    apply integral_nonneg
    intro x
    simp only [g, Pi.zero_apply]
    have hsq : (∑ n ∈ F, ∑ m ∈ F, (A n ∩ A m).indicator (1 : Ω → ℝ) x)
        = (∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      by_cases hn : x ∈ A n <;> by_cases hm : x ∈ A m <;> simp [hn, hm]
    rw [hsq]
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      have := sq_nonneg (∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x - t)
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have h0 : ∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x = 0 := by
        refine Finset.sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
        intro hxn
        exact hx (Set.mem_biUnion hn hxn)
      rw [h0]
      simp
  have hcalc : ∫ x, g x ∂μ = ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m)
      - 2 * t * ∑ n ∈ F, μ.real (A n) + t ^ 2 * μ.real U := by
    simp only [g]
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul,
      integral_finsetSum, integral_finsetSum, integral_indicator_one hU]
    · congr 2
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun m _ => integral_indicator_one ((hA n).inter (hA m))
        · exact fun m _ => hint _ ((hA n).inter (hA m))
      · congr 1
        exact Finset.sum_congr rfl fun n _ => integral_indicator_one (hA n)
    · exact fun n _ => hint _ (hA n)
    · exact fun n _ => integrable_finsetSum _ fun m _ => hint _ ((hA n).inter (hA m))
    · exact integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
        hint _ ((hA n).inter (hA m))
    · exact (integrable_finsetSum _ fun n _ => hint _ (hA n)).const_mul _
    · exact (integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
        hint _ ((hA n).inter (hA m))).sub
        ((integrable_finsetSum _ fun n _ => hint _ (hA n)).const_mul _)
    · exact (hint _ hU).const_mul _
  rw [← hcalc]
  exact hg

/-- Finite Chung–Erdős: if `0 < S = ∑_F μ(A_n)` and `D = ∑∑ μ(A_n ∩ A_m) ≤ C S²`,
then `1/C ≤ μ(⋃_F A_n)`. -/
theorem one_div_le_measure_biUnion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (F : Finset ℕ)
    (C : ℝ) (hC : 0 < C) (hS : 0 < ∑ n ∈ F, μ.real (A n))
    (hD : ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) ≤ C * (∑ n ∈ F, μ.real (A n)) ^ 2) :
    1 / C ≤ μ.real (⋃ n ∈ F, A n) := by
  set S := ∑ n ∈ F, μ.real (A n)
  set D := ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m)
  set V := μ.real (⋃ n ∈ F, A n)
  have hq : ∀ t : ℝ, 0 ≤ V * (t * t) + (-2 * S) * t + D := by
    intro t
    have := chungErdos_quadratic μ A hA F t
    nlinarith
  have hdisc := discrim_le_zero hq
  rw [discrim] at hdisc
  have hV : 0 ≤ V := measureReal_nonneg
  have h1 : S ^ 2 ≤ C * S ^ 2 * V := by nlinarith
  have h2 : 1 ≤ C * V := by
    have hS2 : 0 < S ^ 2 := by positivity
    nlinarith
  rw [div_le_iff₀ hC]
  linarith

/-- If for every `N` there is a finite set `F ⊆ [N, ∞)` with `0 < ∑_F μ(A_n)` and
`∑_{F×F} μ(A_n ∩ A_m) ≤ C (∑_F μ(A_n))²`, then `μ(limsup A_n) ≥ 1/C`. -/
theorem measure_limsup_ge_of_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (C : ℝ)
    (h : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, N ≤ n) ∧ 0 < ∑ n ∈ F, μ.real (A n) ∧
      ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) ≤ C * (∑ n ∈ F, μ.real (A n)) ^ 2) :
    1 / C ≤ μ.real (limsup A atTop) := by
  rcases le_or_gt C 0 with hC | hC
  · exact le_trans (div_nonpos_of_nonneg_of_nonpos zero_le_one hC) measureReal_nonneg
  set V : ℕ → Set Ω := fun N => ⋃ i ≥ N, A i with hVdef
  have hlim : limsup A atTop = ⋂ N, V N := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, V]
  have hanti : Antitone V := by
    intro a b hab x hx
    simp only [V, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, le_trans hab hi, hx⟩
  have hmeas : ∀ N, NullMeasurableSet (V N) μ := fun N =>
    (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hA i).nullMeasurableSet
  have hmu : μ (limsup A atTop) = ⨅ N, μ (V N) := by
    rw [hlim, hanti.measure_iInter hmeas ⟨0, measure_ne_top μ _⟩]
  have hbound : ∀ N, ENNReal.ofReal (1 / C) ≤ μ (V N) := by
    intro N
    obtain ⟨F, hFN, hS, hD⟩ := h N
    have h1 := one_div_le_measure_biUnion μ A hA F C hC hS hD
    have hsub : (⋃ n ∈ F, A n) ⊆ V N := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨n, hn, hx⟩ := hx
      simp only [V, Set.mem_iUnion]
      exact ⟨n, hFN n hn, hx⟩
    calc ENNReal.ofReal (1 / C) ≤ ENNReal.ofReal (μ.real (⋃ n ∈ F, A n)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = μ (⋃ n ∈ F, A n) := ENNReal.ofReal_toReal (measure_ne_top μ _)
      _ ≤ μ (V N) := measure_mono hsub
  have hfinal : ENNReal.ofReal (1 / C) ≤ μ (limsup A atTop) := by
    rw [hmu]
    exact le_iInf hbound
  rw [Measure.real]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hfinal

end DuffinSchaeffer
