import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P6: the half-chord lemma

If `a`, `b` and their midpoint are unit vectors, then `(b - a)/2 ∈ D`: with nearest points `dₐ, d_b`, strict convexity of the Euclidean norm forces `a - dₐ = b - d_b`, so `(b - a)/2 = (d_b + (-dₐ))/2 ∈ D`.
-/

namespace Erdos956Upper

open Erdos956 Metric

theorem half_chord_mem {D : Set E} (hD : IsCompact D) (hDc : Convex ℝ D) (hne : D.Nonempty)
    (hneg : ∀ v ∈ D, -v ∈ D) {a b : E} (ha : infDist a D = 1) (hb : infDist b D = 1)
    (hm : infDist (midpoint ℝ a b) D = 1) : ((1 : ℝ) / 2) • (b - a) ∈ D := by
  obtain ⟨pa, hpa, hda⟩ := hD.exists_infDist_eq_dist hne a
  obtain ⟨pb, hpb, hdb⟩ := hD.exists_infDist_eq_dist hne b
  set x : E := a - pa with hx
  set y : E := b - pb with hy
  have hxn : ‖x‖ = 1 := by rw [hx, ← dist_eq_norm, ← hda, ha]
  have hyn : ‖y‖ = 1 := by rw [hy, ← dist_eq_norm, ← hdb, hb]
  have hq : midpoint ℝ pa pb ∈ D := hDc.midpoint_mem hpa hpb
  have hle : infDist (midpoint ℝ a b) D ≤ dist (midpoint ℝ a b) (midpoint ℝ pa pb) :=
    infDist_le_dist_of_mem hq
  have hdist : dist (midpoint ℝ a b) (midpoint ℝ pa pb) = ‖x + y‖ / 2 := by
    rw [dist_eq_norm, midpoint_eq_smul_add, midpoint_eq_smul_add, ← smul_sub, norm_smul]
    have : a + b - (pa + pb) = x + y := by rw [hx, hy]; abel
    rw [this]; norm_num; ring
  have h2 : 2 ≤ ‖x + y‖ := by linarith
  have hpar := parallelogram_law_with_norm ℝ x y
  have hxy0 : ‖x - y‖ * ‖x - y‖ ≤ 0 := by
    rw [hxn, hyn] at hpar
    nlinarith [norm_nonneg (x + y)]
  have hxy : x = y := by
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hba : b - a = pb + -pa := by
    have : a - pa = b - pb := hxy
    rw [sub_eq_add_neg]
    have h' : b = a - pa + pb := by rw [this]; abel
    rw [h']; abel
  rw [hba]
  have := hDc.midpoint_mem hpb (hneg pa hpa)
  rw [midpoint_eq_smul_add] at this
  convert this using 2
  norm_num

/-- Every parallel vector of at most half the length lies in `D`. -/
theorem smul_chord_mem {D : Set E} (hD : IsCompact D) (hDc : Convex ℝ D) (h0 : (0 : E) ∈ D)
    (hneg : ∀ v ∈ D, -v ∈ D) {a b : E} (ha : infDist a D = 1) (hb : infDist b D = 1)
    (hm : infDist (midpoint ℝ a b) D = 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    t • (b - a) ∈ D := by
  have hv := half_chord_mem hD hDc ⟨0, h0⟩ hneg ha hb hm
  set v : E := ((1 : ℝ) / 2) • (b - a) with hvdef
  have hbt : t • (b - a) = (2 * t) • v := by
    rw [hvdef, smul_smul]; congr 1; ring
  rw [hbt]
  have habs : |2 * t| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  rcases le_total 0 t with h | h
  · exact hDc.smul_mem_of_zero_mem h0 hv ⟨by linarith, by linarith [le_abs_self (2 * t)]⟩
  · have hnv := hneg v hv
    have := hDc.smul_mem_of_zero_mem h0 hnv
      (t := -(2 * t)) ⟨by linarith, by linarith [neg_abs_le (2 * t)]⟩
    rwa [smul_neg, neg_smul, neg_neg] at this

end Erdos956Upper
