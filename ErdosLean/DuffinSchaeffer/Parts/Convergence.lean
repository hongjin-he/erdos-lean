import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 1: the convergence direction (KM (1.5))

`λ(A_q) ≤ 2 w(q)` (union bound over the `φ(q)` arcs of length
`2ψ(q)/q`) and the first Borel–Cantelli lemma, transferred from `ℝ/ℤ` to `ℝ` by periodicity.
-/

open MeasureTheory Filter

namespace DuffinSchaeffer

/-- `A_q` is open, hence measurable. -/
theorem measurableSet_Aq (ψ : ℕ → ℝ) (q : ℕ) : MeasurableSet (Aq ψ q) :=
  Metric.isOpen_thickening.measurableSet

/-- The closed `δ`-neighbourhood of the `φ(q)` points of order `q` has measure `≤ 2δ φ(q)`. -/
theorem alt_volume_cthickening_le (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (Metric.cthickening δ {y : UnitAddCircle | addOrderOf y = q}) ≤
      ENNReal.ofReal (2 * δ * Nat.totient q) := by
  have hfin : {y : UnitAddCircle | addOrderOf y = q}.Finite :=
    AddCircle.finite_setOfPred_addOrderOf_eq 1 hq
  have hcard : hfin.toFinset.card = Nat.totient q := by
    rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact AddCircle.card_addOrderOf_eq_totient 1
  rw [hfin.isCompact.cthickening_eq_biUnion_closedBall hδ]
  have h1 : (⋃ x ∈ {y : UnitAddCircle | addOrderOf y = q}, Metric.closedBall x δ) =
      ⋃ x ∈ hfin.toFinset, Metric.closedBall x δ := by
    simp
  rw [h1]
  calc volume (⋃ x ∈ hfin.toFinset, Metric.closedBall x δ)
      ≤ ∑ x ∈ hfin.toFinset, volume (Metric.closedBall x δ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hfin.toFinset, ENNReal.ofReal (2 * δ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [AddCircle.volume_closedBall]
        exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal (2 * δ * Nat.totient q) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]

/-- `λ(A_q) ≤ 2 φ(q) ψ(q) / q` (the `φ(q)` arcs have length `≤ 2ψ(q)/q` each). -/
theorem volume_Aq_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) (hq : 0 < q) :
    volume.real (Aq ψ q) ≤ 2 * weight ψ q := by
  have hδ : 0 ≤ ψ q / q := div_nonneg (hψ q) (Nat.cast_nonneg q)
  have hsub : Aq ψ q ⊆ Metric.cthickening (ψ q / q) {y : UnitAddCircle | addOrderOf y = q} :=
    Metric.thickening_subset_cthickening _ _
  have h := (measure_mono hsub).trans (alt_volume_cthickening_le q hq _ hδ)
  have heq : 2 * (ψ q / q) * Nat.totient q = 2 * weight ψ q := by
    unfold weight; ring
  rw [heq] at h
  exact ENNReal.toReal_le_of_le_ofReal (by
    unfold weight; exact mul_nonneg zero_le_two
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q)) (Nat.cast_nonneg _))) h

/-- The closed sets used for Borel–Cantelli on the circle. -/
noncomputable def alt_Cq (ψ : ℕ → ℝ) (q : ℕ) : Set UnitAddCircle :=
  if 0 < q then Metric.cthickening (ψ q / q) {y : UnitAddCircle | addOrderOf y = q} else ∅

theorem alt_ae_eventually_not_mem_Cq (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hs : Summable (weight ψ)) :
    ∀ᵐ x : UnitAddCircle, ∀ᶠ q in atTop, x ∉ alt_Cq ψ q := by
  apply ae_eventually_notMem
  have hw : ∀ q, 0 ≤ 2 * weight ψ q := fun q => by
    unfold weight; exact mul_nonneg zero_le_two
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q)) (Nat.cast_nonneg _))
  have hle : ∀ q, volume (alt_Cq ψ q) ≤ ENNReal.ofReal (2 * weight ψ q) := by
    intro q
    unfold alt_Cq
    split_ifs with hq
    · have h := alt_volume_cthickening_le q hq (ψ q / q) (div_nonneg (hψ q) (Nat.cast_nonneg q))
      have heq : 2 * (ψ q / q) * Nat.totient q = 2 * weight ψ q := by
        unfold weight; ring
      rwa [heq] at h
    · simp
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' q, 2 * weight ψ q)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hw (hs.mul_left 2)]
  exact ENNReal.tsum_le_tsum hle

/-- Every reduced solution `(a,q)` puts `α mod 1` in `C_q`. -/
theorem alt_mem_Cq (ψ : ℕ → ℝ) (α : ℝ) (s : ℤ × ℕ) (hs : s ∈ solutionsLe ψ α) :
    ((α : ℝ) : UnitAddCircle) ∈ alt_Cq ψ s.2 := by
  obtain ⟨hq, hg, habs⟩ := hs
  simp only [alt_Cq, hq, ↓reduceIte]
  refine Metric.mem_cthickening_of_dist_le _ (((s.1 : ℝ) / s.2 * 1 : ℝ) : UnitAddCircle) _ _ ?_ ?_
  · exact AddCircle.addOrderOf_div_of_gcd_eq_one' hq (by simpa [Int.gcd] using hg)
  · rw [dist_eq_norm, ← AddCircle.coe_sub, mul_one]
    exact (QuotientAddGroup.norm_mk_le_norm).trans (by rw [Real.norm_eq_abs]; exact habs)

theorem alt_solutionsLe_subset (ψ : ℕ → ℝ) (α : ℝ) :
    solutionsLe ψ α ⊆ ⋃ q ∈ {q : ℕ | ((α : ℝ) : UnitAddCircle) ∈ alt_Cq ψ q},
      (Set.Icc ⌊q * α - ψ q⌋ ⌈q * α + ψ q⌉ ×ˢ {q}) := by
  intro s hs
  have hmem := alt_mem_Cq ψ α s hs
  obtain ⟨hq, -, habs⟩ := hs
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨s.2, hmem, ?_⟩
  have hq' : (0 : ℝ) < s.2 := by exact_mod_cast hq
  have h2 : |s.2 * α - s.1| ≤ ψ s.2 := by
    have : s.2 * α - s.1 = s.2 * (α - s.1 / s.2) := by field_simp
    rw [this, abs_mul, abs_of_pos hq']
    calc (s.2 : ℝ) * |α - s.1 / s.2| ≤ s.2 * (ψ s.2 / s.2) :=
          mul_le_mul_of_nonneg_left habs hq'.le
      _ = ψ s.2 := by field_simp
  rw [abs_le] at h2
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · exact Int.cast_le.1 ((Int.floor_le _).trans (by linarith))
  · exact Int.cast_le.1 ((show (s.1 : ℝ) ≤ s.2 * α + ψ s.2 by linarith).trans (Int.le_ceil _))

/-- **KM (1.5)**: if `∑ φ(q)ψ(q)/q < ∞`, then almost every real `α` has only finitely many
reduced solutions of `|α - a/q| ≤ ψ(q)/q`. -/
theorem convergence_null (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hs : Summable (weight ψ)) :
    ∀ᵐ α : ℝ, (solutionsLe ψ α).Finite := by
  have hBC := alt_ae_eventually_not_mem_Cq ψ hψ hs
  have hR : ∀ᵐ α : ℝ, ∀ᶠ q in atTop, ((α : ℝ) : UnitAddCircle) ∉ alt_Cq ψ q := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_add_intCast (0 : ℝ),
      ae_restrict_iUnion_iff]
    intro n
    exact (AddCircle.measurePreserving_mk (1 : ℝ) (0 + n)).quasiMeasurePreserving.ae hBC
  filter_upwards [hR] with α hα
  refine Set.Finite.subset ?_ (alt_solutionsLe_subset ψ α)
  have hfin : {q : ℕ | ((α : ℝ) : UnitAddCircle) ∈ alt_Cq ψ q}.Finite := by
    rw [← Nat.cofinite_eq_atTop] at hα
    simpa using hα
  exact hfin.biUnion fun q _ => (Set.finite_Icc _ _).prod (Set.finite_singleton q)

end DuffinSchaeffer
