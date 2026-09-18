import ErdosLean.Erdos956Upper.Parts.FlatOverlap

/-!
# Erdős #956 upper bound — P14: the upper drawing

Vertices `X`; for each centre `c ∈ X` the points of `X` on the curve of `c` are joined consecutively.  The drawing is valid, simple (P9) and no vertex lies inside an arc; and `#upperPairs ≤ #edges + n`.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

lemma onUpper_sub_iff' {p c : E} (h : OnUpper D (p - c)) :
    |p 0 - c 0| < wid D ∧ p 1 - c 1 = gUp D (p 0 - c 0) := by
  have h1 := h.1; have h2 := h.2
  simp only [PiLp.sub_apply] at h1 h2
  exact ⟨h1, h2⟩

lemma curve_eq_of_onUpper {p c : E} (h : OnUpper D (p - c)) : curve D c (p 0) = p 1 := by
  have h2 := (onUpper_sub_iff' h).2
  unfold curve; linarith

lemma pt2_curve_eq {p c : E} (h : OnUpper D (p - c)) : pt2 (p 0) (curve D c (p 0)) = p := by
  rw [curve_eq_of_onUpper h, pt2_eta]

lemma mem_upperEdges {e : E × E × E} (he : e ∈ upperEdges D X) :
    e.1 ∈ X ∧ e.2.1 ∈ X ∧ e.2.2 ∈ X ∧ Consec D X e.1 e.2.1 e.2.2 := by
  classical
  unfold upperEdges at he
  simp only [Finset.mem_filter, Finset.mem_product] at he
  exact ⟨he.1.1, he.1.2.1, he.1.2.2, he.2⟩

theorem upperEdges_valid (hS : SepConfig D X) :
    ∀ e ∈ upperEdges D X, (upperArc D e).Valid := by
  intro e he
  obtain ⟨_, _, _, h1, h2, hlt, _⟩ := mem_upperEdges he
  refine ⟨hlt, ?_⟩
  show ContinuousOn (fun x => e.1 1 + gUp D (x - e.1 0)) (Set.Icc (e.2.1 0) (e.2.2 0))
  refine continuousOn_const.add ((gUp_continuousOn hS).comp
    (continuousOn_id.sub continuousOn_const) ?_)
  intro x hx
  have a1 := abs_lt.1 (onUpper_sub_iff' h1).1
  have a2 := abs_lt.1 (onUpper_sub_iff' h2).1
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem upperEdges_ends (hS : SepConfig D X) :
    ∀ e ∈ upperEdges D X, (upperArc D e).left ∈ X ∧ (upperArc D e).right ∈ X := by
  intro e he
  obtain ⟨_, hp, hq, h1, h2, _, _⟩ := mem_upperEdges he
  refine ⟨?_, ?_⟩
  · show pt2 (e.2.1 0) (curve D e.1 (e.2.1 0)) ∈ X
    rw [pt2_curve_eq h1]; exact hp
  · show pt2 (e.2.2 0) (curve D e.1 (e.2.2 0)) ∈ X
    rw [pt2_curve_eq h2]; exact hq

theorem upperEdges_avoid (hS : SepConfig D X) :
    ∀ e ∈ upperEdges D X, ∀ z ∈ X, (upperArc D e).Avoids z := by
  intro e he z hz ⟨hzI, hz1⟩
  obtain ⟨_, _, _, h1, h2, _, hmin⟩ := mem_upperEdges he
  change z 0 ∈ Set.Ioo (e.2.1 0) (e.2.2 0) at hzI
  change z 1 = curve D e.1 (z 0) at hz1
  apply hmin z hz _ hzI
  have a1 := abs_lt.1 (onUpper_sub_iff' h1).1
  have a2 := abs_lt.1 (onUpper_sub_iff' h2).1
  refine ⟨?_, ?_⟩
  · simp only [PiLp.sub_apply]
    rw [abs_lt]; constructor <;> linarith [hzI.1, hzI.2]
  · simp only [PiLp.sub_apply]
    unfold curve at hz1; linarith

theorem upperEdges_simple (hS : SepConfig D X) :
    ∀ e ∈ upperEdges D X, ∀ e' ∈ upperEdges D X, (upperArc D e).left = (upperArc D e').left →
      (upperArc D e).right = (upperArc D e').right → e = e' := by
  rintro ⟨c, p, q⟩ he ⟨c', p', q'⟩ he' hl hr
  obtain ⟨hc, hp, hq, h1, h2, hlt, _⟩ := mem_upperEdges he
  obtain ⟨hc', _, _, h1', h2', _, _⟩ := mem_upperEdges he'
  change pt2 (p 0) (curve D c (p 0)) = pt2 (p' 0) (curve D c' (p' 0)) at hl
  change pt2 (q 0) (curve D c (q 0)) = pt2 (q' 0) (curve D c' (q' 0)) at hr
  rw [pt2_curve_eq h1, pt2_curve_eq h1'] at hl
  rw [pt2_curve_eq h2, pt2_curve_eq h2'] at hr
  subst hl hr
  by_cases hcc : c = c'
  · subst hcc; rfl
  · have hpq : p ≠ q := by
      intro h; rw [h] at hlt; exact lt_irrefl _ hlt
    exact (no_two_common_points hS hc hc' hp hq hcc hpq h1 h2 h1' h2').elim

theorem upperPairs_card_le (hS : SepConfig D X) :
    (upperPairs D X).card ≤ (upperEdges D X).card + X.card := by
  classical
  set B := (upperPairs D X).filter
    (fun r => ∀ z ∈ X, OnUpper D (z - r.1) → z 0 ≤ r.2 0) with hB
  have hsub : upperPairs D X ⊆ (upperEdges D X).image (fun e => (e.1, e.2.1)) ∪ B := by
    intro r hr
    by_cases hrB : r ∈ B
    · exact Finset.mem_union_right _ hrB
    · apply Finset.mem_union_left
      have hr' := hr
      unfold upperPairs at hr'
      simp only [Finset.mem_filter, Finset.mem_product] at hr'
      obtain ⟨⟨hx, hy⟩, _, hup⟩ := hr'
      have : ¬ ∀ z ∈ X, OnUpper D (z - r.1) → z 0 ≤ r.2 0 := by
        intro h; exact hrB (Finset.mem_filter.2 ⟨hr, h⟩)
      push Not at this
      obtain ⟨z0, hz0X, hz0u, hz0lt⟩ := this
      set Z := X.filter (fun z => OnUpper D (z - r.1) ∧ r.2 0 < z 0) with hZ
      have hZne : Z.Nonempty := ⟨z0, Finset.mem_filter.2 ⟨hz0X, hz0u, hz0lt⟩⟩
      obtain ⟨q, hqZ, hqmin⟩ := Finset.exists_min_image Z (fun z : E => z 0) hZne
      obtain ⟨hqX, hqu, hqlt⟩ := Finset.mem_filter.1 hqZ
      refine Finset.mem_image.2 ⟨(r.1, r.2, q), ?_, rfl⟩
      unfold upperEdges
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hx, hy, hqX⟩, hup, hqu, hqlt, ?_⟩
      rintro z hzX hzu ⟨h1, h2⟩
      have := hqmin z (Finset.mem_filter.2 ⟨hzX, hzu, h1⟩)
      linarith
  have hBcard : B.card ≤ X.card := by
    refine Finset.card_le_card_of_injOn (fun r => r.1) ?_ ?_
    · intro r hr
      have := (Finset.mem_filter.1 hr).1
      unfold upperPairs at this
      simp only [Finset.mem_filter, Finset.mem_product] at this
      exact this.1.1
    · intro r hr s hs hrs
      simp only at hrs
      obtain ⟨hr1, hr2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hr)
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hs)
      unfold upperPairs at hr1 hs1
      simp only [Finset.mem_filter, Finset.mem_product] at hr1 hs1
      have hru := hr1.2.2
      have hsu := hs1.2.2
      rw [hrs] at hru hr2
      have e1 := hr2 s.2 hs1.1.2 hsu
      have e2 := hs2 r.2 hr1.1.2 hru
      have hx : r.2 0 = s.2 0 := le_antisymm e2 e1
      have hy : r.2 1 = s.2 1 := by
        rw [← curve_eq_of_onUpper hru, ← curve_eq_of_onUpper hsu, hx]
      have h2 : r.2 = s.2 := by
        rw [← pt2_eta r.2, ← pt2_eta s.2, hx, hy]
      exact Prod.ext hrs h2
  calc (upperPairs D X).card
      ≤ ((upperEdges D X).image (fun e => (e.1, e.2.1)) ∪ B).card := Finset.card_le_card hsub
    _ ≤ ((upperEdges D X).image (fun e => (e.1, e.2.1))).card + B.card := Finset.card_union_le _ _
    _ ≤ (upperEdges D X).card + X.card := add_le_add Finset.card_image_le hBcard

end Erdos956Upper
