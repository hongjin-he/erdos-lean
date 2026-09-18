import ErdosLean.Erdos956Upper.Parts.UpperArc
import ErdosLean.Erdos956Upper.Parts.SegmentLemma

/-!
# Erdős #956 upper bound — P7: side pairs are O(n)

For fixed `x`, at most two `y ∈ X` have `y - x` on the right side `{w} × [s₁, s₂]` of `∂K`: three would give, via the half-chord lemma, a difference in `D`.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

/-- A point of `K` with first coordinate `w` is a unit vector. -/
theorem side_unit (hS : SepConfig D X) {v : E} (hv : v ∈ Kset D) (h0 : v 0 = wid D) :
    infDist v D = 1 := by
  by_contra hne
  have hlt : infDist v D < 1 := lt_of_le_of_ne hv hne
  set ε := 1 - infDist v D with hε
  have hεpos : 0 < ε := by linarith
  set u : E := v + ε • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) with hu
  have hdist : dist u v = ε := by
    rw [dist_eq_norm, hu, add_sub_cancel_left, norm_smul, PiLp.norm_single,
      norm_one, mul_one, Real.norm_eq_abs, abs_of_pos hεpos]
  have huK : u ∈ Kset D := by
    show infDist u D ≤ 1
    have := infDist_le_infDist_add_dist (x := u) (y := v) (s := D)
    linarith
  have h1 := abs_le_wid hS huK
  have hu0 : u 0 = wid D + ε := by
    simp [hu, h0]
  rw [hu0] at h1
  have := le_abs_self (wid D + ε)
  linarith

/-- Three points on the side over a common base point are impossible. -/
theorem side_three (hS : SepConfig D X) {x p q r : E} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hpS : OnSide D (p - x)) (hqS : OnSide D (q - x)) (hrS : OnSide D (r - x))
    (hpq : p 1 < q 1) (hqr : q 1 < r 1) : False := by
  obtain ⟨hp0, hp1⟩ := hpS
  obtain ⟨hq0, hq1⟩ := hqS
  obtain ⟨hr0, hr1⟩ := hrS
  have hp0' : p 0 - x 0 = wid D := by simpa using hp0
  have hq0' : q 0 - x 0 = wid D := by simpa using hq0
  have hr0' : r 0 - x 0 = wid D := by simpa using hr0
  set a := p - x
  set b := r - x
  have hK : Convex ℝ (Kset D) := kset_convex hS
  have haK : a ∈ Kset D := by show infDist a D ≤ 1; rw [hp1]
  have hbK : b ∈ Kset D := by show infDist b D ≤ 1; rw [hr1]
  have hmK : midpoint ℝ a b ∈ Kset D := hK.segment_subset haK hbK (midpoint_mem_segment a b)
  have hm0 : (midpoint ℝ a b) 0 = wid D := by
    rw [midpoint_eq_smul_add]
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    rw [hp0, hr0]
    simp [invOf_eq_inv]
    ring
  have hm1 : infDist (midpoint ℝ a b) D = 1 := side_unit hS hmK hm0
  have hba : b - a = r - p := by simp [a, b]
  have hne : D.Nonempty := ⟨0, hS.zero_mem⟩
  have hden : 0 < r 1 - p 1 := by linarith
  set t := (q 1 - p 1) / (r 1 - p 1) with ht
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t < 1 := (div_lt_one hden).2 (by linarith)
  have hqp : q - p = t • (r - p) := by
    ext i
    fin_cases i
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      simp
      rw [show (q 0 - p 0) = 0 by linarith, show (r 0 - p 0) = 0 by linarith, mul_zero]
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      simp
      rw [ht]
      field_simp
  rcases le_or_gt t (1 / 2) with hle | hgt
  · have hmem := smul_chord_mem hS.compact hS.convex hS.zero_mem hS.neg_mem hp1 hr1 hm1
      (t := t) (by rw [abs_of_pos ht0]; exact hle)
    rw [hba, ← hqp] at hmem
    exact hS.sep p hp q hq (by intro h; rw [h] at hpq; exact lt_irrefl _ hpq) hmem
  · have hmem := smul_chord_mem hS.compact hS.convex hS.zero_mem hS.neg_mem hp1 hr1 hm1
      (t := 1 - t) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [hba] at hmem
    have hrq : r - q = (1 - t) • (r - p) := by
      rw [sub_smul, one_smul, ← hqp]; abel
    rw [← hrq] at hmem
    exact hS.sep q hq r hr (by intro h; rw [h] at hqr; exact lt_irrefl _ hqr) hmem

theorem sidePairs_card_le (hS : SepConfig D X) : (sidePairs D X).card ≤ 2 * X.card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) ?_ 2 ?_
  · intro q hq
    unfold sidePairs at hq
    exact (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
  · intro x _
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, v, hv, z, hz, huv, huz, hvz⟩ := Finset.two_lt_card.1 hlt
    have key : ∀ q ∈ (sidePairs D X).filter (fun q => q.1 = x),
        q.2 ∈ X ∧ OnSide D (q.2 - x) := by
      intro q hq
      unfold sidePairs at hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨⟨_, h2⟩, _, hs⟩, rfl⟩ := hq
      exact ⟨h2, hs⟩
    have hfst : ∀ q ∈ (sidePairs D X).filter (fun q => q.1 = x), q.1 = x := by
      intro q hq
      exact (Finset.mem_filter.1 hq).2
    obtain ⟨huX, huS⟩ := key u hu
    obtain ⟨hvX, hvS⟩ := key v hv
    obtain ⟨hzX, hzS⟩ := key z hz
    -- distinct pairs with equal first coordinate have distinct second-coordinate heights
    have hsec : ∀ {a b : E × E}, a ∈ (sidePairs D X).filter (fun q => q.1 = x) →
        b ∈ (sidePairs D X).filter (fun q => q.1 = x) → a ≠ b → a.2 1 ≠ b.2 1 := by
      intro a b ha hb hab h
      apply hab
      obtain ⟨_, ha'⟩ := key a ha
      obtain ⟨_, hb'⟩ := key b hb
      have e0a := ha'.1
      have e0b := hb'.1
      simp only [PiLp.sub_apply] at e0a e0b
      have h2 : a.2 = b.2 := by
        ext i
        fin_cases i
        · simp; linarith
        · simpa using h
      exact Prod.ext ((hfst a ha).trans (hfst b hb).symm) h2
    have h1 := hsec hu hv huv
    have h2 := hsec hu hz huz
    have h3 := hsec hv hz hvz
    have T := fun {p q r : E} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
      (hpS : OnSide D (p - x)) (hqS : OnSide D (q - x)) (hrS : OnSide D (r - x))
      (a : p 1 < q 1) (b : q 1 < r 1) => side_three hS hp hq hr hpS hqS hrS a b
    rcases h1.lt_or_gt with a1 | a1 <;> rcases h2.lt_or_gt with a2 | a2 <;>
      rcases h3.lt_or_gt with a3 | a3
    · exact T huX hvX hzX huS hvS hzS a1 a3
    · exact T huX hzX hvX huS hzS hvS a2 a3
    · linarith
    · exact T hzX huX hvX hzS huS hvS a2 a1
    · exact T hvX huX hzX hvS huS hzS a1 a2
    · linarith
    · exact T hvX hzX huX hvS hzS huS a3 a2
    · exact T hzX hvX huX hzS hvS huS a3 a1

end Erdos956Upper
