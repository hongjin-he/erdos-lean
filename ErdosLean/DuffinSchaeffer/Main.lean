import ErdosLean.DuffinSchaeffer.Parts.Convergence
import ErdosLean.DuffinSchaeffer.Parts.CircleTransfer
import ErdosLean.DuffinSchaeffer.Parts.Truncation
import ErdosLean.DuffinSchaeffer.Parts.SecondMoment
import ErdosLean.DuffinSchaeffer.Parts.MeasureLower
import ErdosLean.DuffinSchaeffer.Parts.Overlap
import ErdosLean.DuffinSchaeffer.Parts.PairSum

/-!
# The Duffin–Schaeffer theorem (JSP-000832, Erdős #999): main theorem

Koukoulopoulos–Maynard, Ann. of Math. 192 (2020), Theorem 1, together with the easy converse
(1.5).  This file only assembles the parts in `Parts/`, following KM §5.

Divergence direction (`divergence_full`):
1. cap `ψ` to `ψ̃ = capψ ψ` (`w̃ = min(w, 1/2)`, still divergent, radius `→ 0`);
2. on each window `[N, Y]` with `∑ w̃ ∈ [1,2]`: `∑ λ(A_q) ≥ c` (`measure_Aq_ge`) and
   `∑∑ λ(A_q ∩ A_r) ≤ 4 + C₁ C₂` (`volume_Aq_le`, `measure_inter_Aq_le`, `pair_sum_bound`);
3. second moment ⇒ `λ(limsup A_q) > 0`; Gallagher's 0-1 law (Mathlib) ⇒ full measure on the
   circle; monotonicity and `ae_solutions_of_ae_circle` ⇒ full measure on `ℝ`.
-/

open MeasureTheory Filter Topology Finset

namespace DuffinSchaeffer

/-- The divergence direction (KM Theorem 1), with strict inequality, on `ℝ`. -/
theorem divergence_full (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hdiv : ¬ Summable (weight ψ)) :
    ∀ᵐ α : ℝ, (solutions ψ α).Infinite := by
  set ψ' := capψ ψ with hψ'def
  have hψ' : ∀ q, 0 ≤ ψ' q := capψ_nonneg ψ hψ
  have hw' : ∀ q, weight ψ' q ≤ 1 / 2 := weight_capψ_le_half ψ hψ
  have hdiv' : ¬ Summable (weight ψ') := not_summable_weight_capψ ψ hψ hdiv
  have hwnn : ∀ q, 0 ≤ weight ψ' q := fun q => by
    unfold weight; have := hψ' q; positivity
  obtain ⟨c, hc, hlow⟩ := measure_Aq_ge
  obtain ⟨C₁, hC₁, hov⟩ := measure_inter_Aq_le
  obtain ⟨C₂, hC₂, hps⟩ := pair_sum_bound
  set K : ℝ := (4 + C₁ * C₂) / c ^ 2 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ C₁ * C₂ := mul_nonneg hC₁.le hC₂
    positivity
  -- the second-moment hypothesis on windows
  have hwin : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, N ≤ n) ∧
      0 < ∑ n ∈ F, volume.real (Aq ψ' n) ∧
      ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤
        K * (∑ n ∈ F, volume.real (Aq ψ' n)) ^ 2 := by
    intro N
    obtain ⟨Y, h1, h2⟩ := exists_window ψ' hψ' hw' hdiv' (max N 1)
    set F := Icc (max N 1) Y with hF
    have hFpos : ∀ n ∈ F, 0 < n := fun n hn =>
      lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) (mem_Icc.1 hn).1)
    have hS1 : c ≤ ∑ n ∈ F, volume.real (Aq ψ' n) := by
      calc c ≤ c * ∑ n ∈ F, weight ψ' n := by nlinarith
        _ = ∑ n ∈ F, c * weight ψ' n := by rw [Finset.mul_sum]
        _ ≤ ∑ n ∈ F, volume.real (Aq ψ' n) :=
          Finset.sum_le_sum fun n hn => hlow ψ' hψ' n (hFpos n hn) (hw' n)
    have hS2 : ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤ 4 + C₁ * C₂ := by
      have hterm : ∀ n ∈ F, ∀ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤
          (if n = m then 2 * weight ψ' n else 0) +
            C₁ * (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m) := by
        intro n hn m hm
        by_cases hnm : n = m
        · subst hnm
          simp only [ite_true, Set.inter_self, mul_zero, add_zero]
          exact volume_Aq_le ψ' hψ' n (hFpos n hn)
        · simp only [hnm, ite_false, zero_add]
          have := hov ψ' hψ' n m (hFpos n hn) (hFpos m hm) hnm
          linarith
      calc ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m)
          ≤ ∑ n ∈ F, ∑ m ∈ F, ((if n = m then 2 * weight ψ' n else 0) +
              C₁ * (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m)) :=
            Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
        _ = ∑ n ∈ F, 2 * weight ψ' n + C₁ * ∑ n ∈ F, ∑ m ∈ F,
              (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.sum_ite_eq F n (fun _ => 2 * weight ψ' n)]
            simp [hn]
        _ ≤ 4 + C₁ * C₂ := by
            have hA : ∑ n ∈ F, 2 * weight ψ' n ≤ 4 := by
              rw [← Finset.mul_sum]; linarith
            have hB := hps ψ' hψ' (max N 1) Y (le_max_right N 1) h2
            have hB' : C₁ * (∑ n ∈ F, ∑ m ∈ F,
                (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m)) ≤ C₁ * C₂ :=
              mul_le_mul_of_nonneg_left hB hC₁.le
            linarith
    refine ⟨F, fun n hn => le_trans (le_max_left N 1) (mem_Icc.1 hn).1,
      lt_of_lt_of_le hc hS1, ?_⟩
    calc ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤ 4 + C₁ * C₂ := hS2
      _ = K * c ^ 2 := by rw [hK]; field_simp
      _ ≤ K * (∑ n ∈ F, volume.real (Aq ψ' n)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          exact pow_le_pow_left₀ hc.le hS1 2
  have hlim := measure_limsup_ge_of_second_moment (volume : Measure UnitAddCircle) (Aq ψ')
    (measurableSet_Aq ψ') K hwin
  rw [limsup_Aq_eq] at hlim
  set E := addWellApproximable UnitAddCircle (fun n => ψ' n / n) with hE
  have hEpos : volume E ≠ 0 := by
    intro h0
    have : volume.real E = 0 := by simp [Measure.real, h0]
    rw [this] at hlim
    have : 0 < 1 / K := by positivity
    linarith
  -- Gallagher's 0-1 law
  have hfull : ∀ᵐ x : UnitAddCircle, x ∈ E := by
    rcases AddCircle.addWellApproximable_ae_empty_or_univ (T := 1) (fun n => ψ' n / n)
        (tendsto_capψ_div ψ hψ) with h | h
    · exact absurd (measure_eq_zero_iff_ae_notMem.2 h) hEpos
    · exact h
  have hmono : E ⊆ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    addWellApproximable_mono fun n =>
      div_le_div_of_nonneg_right (capψ_le ψ n) (Nat.cast_nonneg n)
  exact ae_solutions_of_ae_circle ψ (hfull.mono fun x hx => hmono hx)

/-- Two contradictory almost-everywhere statements are impossible for a nonzero measure. -/
theorem not_ae_and_ae_not {α : Type*} [MeasurableSpace α] (μ : Measure α) (hμ : μ ≠ 0)
    {P : α → Prop} (h₁ : ∀ᵐ a ∂μ, P a) (h₂ : ∀ᵐ a ∂μ, ¬ P a) : False := by
  have : (ae μ).NeBot := ae_neBot.2 hμ
  obtain ⟨a, ha, ha'⟩ := (h₁.and h₂).exists
  exact ha' ha

theorem solutions_subset_solutionsLe (ψ : ℕ → ℝ) (α : ℝ) :
    solutions ψ α ⊆ solutionsLe ψ α :=
  fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.le⟩

/-- **The Duffin–Schaeffer theorem** (Koukoulopoulos–Maynard). -/
theorem duffin_schaeffer : DuffinSchaefferStatement := by
  intro ψ hψ
  have hdiv : DSSeriesDiverges ψ → ∀ᵐ α : ℝ, (solutions ψ α).Infinite :=
    divergence_full ψ hψ
  have hconv : ¬ DSSeriesDiverges ψ → ∀ᵐ α : ℝ, (solutionsLe ψ α).Finite := fun h =>
    convergence_null ψ hψ (not_not.1 h)
  have hconv' : ¬ DSSeriesDiverges ψ → ∀ᵐ α : ℝ, (solutions ψ α).Finite := fun h =>
    (hconv h).mono fun α hα => hα.subset (solutions_subset_solutionsLe ψ α)
  have hvol : (volume : Measure ℝ) ≠ 0 := NeZero.ne _
  have hvolI : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    simp
  refine ⟨⟨fun h => ?_, hdiv⟩, ⟨fun h => ?_, fun hd => ?_⟩, ⟨fun h => ?_, fun hd => ?_⟩, hconv⟩
  · by_contra hn
    exact not_ae_and_ae_not _ hvol h ((hconv' hn).mono fun α hα => Set.not_infinite.2 hα)
  · by_contra hn
    exact not_ae_and_ae_not _ hvol h ((hconv hn).mono fun α hα => Set.not_infinite.2 hα)
  · exact (hdiv hd).mono fun α hα => hα.mono (solutions_subset_solutionsLe ψ α)
  · by_contra hn
    exact not_ae_and_ae_not _ hvolI h
      (ae_restrict_of_ae ((hconv' hn).mono fun α hα => Set.not_infinite.2 hα))
  · exact ae_restrict_of_ae (hdiv hd)

/-- **Erdős #999**, in the literal `f : ℕ → ℕ` wording of erdosproblems.com. -/
theorem erdos_999 : Erdos999Statement := fun f =>
  (duffin_schaeffer (fun q => (f q : ℝ)) (fun q => Nat.cast_nonneg (f q))).1

end DuffinSchaeffer
