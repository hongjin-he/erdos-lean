import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P3: the body K, its width and the upper boundary function

Basic facts on `K = {infDist · D ≤ 1}`, `w = wid D` and `g = gUp D` for a separated configuration.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

/-! ### Auxiliary facts -/

lemma coord0_continuous : Continuous (fun v : E => v 0) := by fun_prop
lemma coord1_continuous : Continuous (fun v : E => v 1) := by fun_prop

lemma pt2_eta (v : E) : pt2 (v 0) (v 1) = v := by
  ext i; fin_cases i <;> rfl

lemma pt2_add_smul (t s : ℝ) : pt2 t s = pt2 t 0 + s • pt2 0 1 := by
  ext i; fin_cases i <;> simp

lemma pt2_continuous (t : ℝ) : Continuous (fun s : ℝ => pt2 t s) := by
  have : (fun s : ℝ => pt2 t s) = fun s => pt2 t 0 + s • pt2 0 1 := by
    funext s; exact pt2_add_smul t s
  rw [this]; fun_prop

lemma norm_pt2_01 : ‖pt2 0 1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]

lemma exists_near (hS : SepConfig D X) {v : E} (hv : v ∈ Kset D) :
    ∃ a ∈ D, ‖v - a‖ ≤ 1 := by
  obtain ⟨a, ha, hd⟩ := hS.compact.exists_infDist_eq_dist ⟨0, hS.zero_mem⟩ v
  refine ⟨a, ha, ?_⟩
  rw [← dist_eq_norm, ← hd]; exact hv

lemma kset_isClosed : IsClosed (Kset D) :=
  isClosed_le (continuous_infDist_pt D) continuous_const

lemma kset_isCompact (hS : SepConfig D X) : IsCompact (Kset D) := by
  refine Metric.isCompact_of_isClosed_isBounded kset_isClosed ?_
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hS.compact.isBounded
  refine (isBounded_iff_forall_norm_le).2 ⟨1 + R, fun v hv => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_near hS hv
  have := norm_le_norm_add_norm_sub' v a
  have h2 := hR a ha
  rw [norm_sub_rev] at this
  linarith [norm_sub_rev v a]

lemma zero_mem_kset (hS : SepConfig D X) : (0 : E) ∈ Kset D := by
  show infDist 0 D ≤ 1
  rw [infDist_zero_of_mem hS.zero_mem]; norm_num

lemma wid_bdd (hS : SepConfig D X) : BddAbove ((fun v : E => v 0) '' Kset D) :=
  ((kset_isCompact hS).image coord0_continuous).bddAbove

lemma wid_attained (hS : SepConfig D X) : ∃ p ∈ Kset D, p 0 = wid D := by
  have := ((kset_isCompact hS).image coord0_continuous).sSup_mem
    ⟨_, Set.mem_image_of_mem _ (zero_mem_kset hS)⟩
  obtain ⟨p, hp, h⟩ := this
  exact ⟨p, hp, h⟩

lemma slice_bdd (hS : SepConfig D X) (t : ℝ) : BddAbove {s : ℝ | pt2 t s ∈ Kset D} := by
  obtain ⟨B, hB⟩ := ((kset_isCompact hS).image coord1_continuous).bddAbove
  refine ⟨B, fun s hs => ?_⟩
  have := hB ⟨pt2 t s, hs, rfl⟩
  simpa using this

/-- `K` is convex. -/
theorem kset_convex (hS : SepConfig D X) : Convex ℝ (Kset D) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨p, hp, hup⟩ := exists_near hS hu
  obtain ⟨q, hq, hvq⟩ := exists_near hS hv
  have hm : a • p + b • q ∈ D := hS.convex hp hq ha hb hab
  show infDist _ D ≤ 1
  refine (infDist_le_dist_of_mem hm).trans ?_
  rw [dist_eq_norm]
  have : a • u + b • v - (a • p + b • q) = a • (u - p) + b • (v - q) := by
    simp only [smul_sub]; abel
  rw [this]
  calc ‖a • (u - p) + b • (v - q)‖ ≤ ‖a • (u - p)‖ + ‖b • (v - q)‖ := norm_add_le _ _
    _ = a * ‖u - p‖ + b * ‖v - q‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

/-- `K` is centrally symmetric. -/
theorem kset_neg (hS : SepConfig D X) {v : E} (hv : v ∈ Kset D) : -v ∈ Kset D := by
  obtain ⟨a, ha, h⟩ := exists_near hS hv
  show infDist _ D ≤ 1
  refine (infDist_le_dist_of_mem (hS.neg_mem a ha)).trans ?_
  rw [dist_eq_norm, show -v - -a = -(v - a) by abel, norm_neg]; exact h

/-- `w ≥ 1` (the unit disc lies in `K` since `0 ∈ D`). -/
theorem one_le_wid (hS : SepConfig D X) : 1 ≤ wid D := by
  have hmem : pt2 1 0 ∈ Kset D := by
    show infDist _ D ≤ 1
    refine (infDist_le_dist_of_mem hS.zero_mem).trans (le_of_eq ?_)
    rw [dist_zero_right, EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  have := le_csSup (wid_bdd hS) (Set.mem_image_of_mem (fun v : E => v 0) hmem)
  exact this

/-- Points of `K` have `|v₀| ≤ w`. -/
theorem abs_le_wid (hS : SepConfig D X) {v : E} (hv : v ∈ Kset D) : |v 0| ≤ wid D := by
  have h1 := le_csSup (wid_bdd hS) (Set.mem_image_of_mem (fun v : E => v 0) hv)
  have h2 := le_csSup (wid_bdd hS) (Set.mem_image_of_mem (fun v : E => v 0) (kset_neg hS hv))
  simp only [PiLp.neg_apply] at h2
  change -v 0 ≤ wid D at h2
  change v 0 ≤ wid D at h1
  rw [abs_le]; constructor <;> linarith

/-- For `|t| < w` the supremum defining `g t` is attained. -/
theorem pt2_gUp_mem (hS : SepConfig D X) {t : ℝ} (ht : |t| < wid D) :
    pt2 t (gUp D t) ∈ Kset D := by
  obtain ⟨p, hp, hpw⟩ := wid_attained hS
  have hw : 0 < wid D := by linarith [one_le_wid hS]
  have hnp := kset_neg hS hp
  set θ : ℝ := (1 + t / wid D) / 2 with hθ
  have htw := abs_lt.1 ht
  have hq1 : t / wid D < 1 := (div_lt_one hw).2 htw.2
  have hq2 : -1 < t / wid D := by rw [lt_div_iff₀ hw]; linarith
  have h0 : 0 ≤ θ := by rw [hθ]; linarith
  have h1 : 0 ≤ 1 - θ := by rw [hθ]; linarith
  have hq := kset_convex hS hp hnp h0 h1 (by ring)
  have hx : (θ • p + (1 - θ) • -p) 0 = t := by
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, hpw, hθ]
    field_simp; ring
  have hne : {s : ℝ | pt2 t s ∈ Kset D}.Nonempty := by
    refine ⟨(θ • p + (1 - θ) • -p) 1, ?_⟩
    show pt2 t _ ∈ Kset D
    rw [← hx, pt2_eta]; exact hq
  have hcl : IsClosed {s : ℝ | pt2 t s ∈ Kset D} :=
    kset_isClosed.preimage (pt2_continuous t)
  exact hcl.csSup_mem hne (slice_bdd hS t)

/-- Points of `K` lie below the upper boundary. -/
theorem le_gUp (hS : SepConfig D X) {v : E} (hv : v ∈ Kset D) (_ht : |v 0| < wid D) :
    v 1 ≤ gUp D (v 0) := by
  refine le_csSup (slice_bdd hS _) ?_
  show pt2 (v 0) (v 1) ∈ Kset D
  rw [pt2_eta]; exact hv

/-- Points of the upper arc are unit vectors. -/
theorem onUpper_unit (hS : SepConfig D X) {v : E} (hv : OnUpper D v) : infDist v D = 1 := by
  obtain ⟨ht, hg⟩ := hv
  have hmem : v ∈ Kset D := by
    have := pt2_gUp_mem hS ht
    rw [← hg, pt2_eta] at this; exact this
  refine le_antisymm hmem ?_
  by_contra hlt
  rw [not_le] at hlt
  set ε := 1 - infDist v D with hε
  have hεpos : 0 < ε := by linarith
  have hk : pt2 (v 0) (v 1 + ε) ∈ Kset D := by
    show infDist _ D ≤ 1
    refine (infDist_le_infDist_add_dist (y := v)).trans ?_
    have : dist (pt2 (v 0) (v 1 + ε)) v = ε := by
      have e : pt2 (v 0) (v 1 + ε) = v + ε • pt2 0 1 := by
        ext i; fin_cases i <;> simp
      rw [e, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_pt2_01,
        Real.norm_of_nonneg hεpos.le, mul_one]
    rw [this, hε]; linarith
  have := le_csSup (slice_bdd hS (v 0)) hk
  change v 1 + ε ≤ gUp D (v 0) at this
  rw [← hg] at this; linarith

/-- `g` is concave on `(-w, w)`. -/
theorem gUp_concaveOn (hS : SepConfig D X) :
    ConcaveOn ℝ (Set.Ioo (-wid D) (wid D)) (gUp D) := by
  refine ⟨convex_Ioo _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy := (convex_Ioo (-wid D) (wid D)) hx hy ha hb hab
  have habs : |a • x + b • y| < wid D := abs_lt.2 ⟨hxy.1, hxy.2⟩
  have hxk := pt2_gUp_mem hS (abs_lt.2 ⟨hx.1, hx.2⟩)
  have hyk := pt2_gUp_mem hS (abs_lt.2 ⟨hy.1, hy.2⟩)
  have hk := kset_convex hS hxk hyk ha hb hab
  have e0 : (a • pt2 x (gUp D x) + b • pt2 y (gUp D y)) 0 = a • x + b • y := by simp
  have e1 : (a • pt2 x (gUp D x) + b • pt2 y (gUp D y)) 1 =
      a • gUp D x + b • gUp D y := by simp
  have := le_gUp hS hk (by rw [e0]; exact habs)
  rw [e0, e1] at this; exact this

/-- `g` is continuous on `(-w, w)`. -/
theorem gUp_continuousOn (hS : SepConfig D X) :
    ContinuousOn (gUp D) (Set.Ioo (-wid D) (wid D)) :=
  (gUp_concaveOn hS).continuousOn isOpen_Ioo

end Erdos956Upper
