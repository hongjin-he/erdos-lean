import ErdosLean.Erdos956Upper.Parts.UpperArc

/-!
# Erdős #956 upper bound — P8: translates of a concave graph cross at most once

For concave `g` and `h ≥ 0`, `y ↦ g(y + h) - g(y)` is antitone; hence the difference of two translated curves is monotone.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

/-- For convex `F`, increments over a fixed step `h ≥ 0` are monotone. -/
lemma convex_incr_mono {s : Set ℝ} {F : ℝ → ℝ} (hF : ConvexOn ℝ s F) {u v h : ℝ}
    (hu : u ∈ s) (hv : v ∈ s) (huh : u + h ∈ s) (hvh : v + h ∈ s) (hh : 0 ≤ h) (huv : u ≤ v) :
    F (u + h) - F u ≤ F (v + h) - F v := by
  rcases eq_or_lt_of_le hh with h0 | hh
  · subst h0; simp
  rcases eq_or_lt_of_le huv with rfl | huv
  · exact le_rfl
  have s1 := hF.secant_mono hu huh hvh (by linarith) (by linarith) (by linarith)
  have s2 := hF.secant_mono hvh hu hv (by linarith) (by linarith) huv.le
  have e1 : u + h - u = h := by ring
  have e2 : v - (v + h) = -h := by ring
  rw [e1] at s1
  rw [e2] at s2
  have e3 : (F u - F (v + h)) / (u - (v + h)) = (F (v + h) - F u) / (v + h - u) := by
    rw [← neg_sub (F (v + h)), ← neg_sub (v + h) u, neg_div_neg_eq]
  have e4 : (F v - F (v + h)) / -h = (F (v + h) - F v) / h := by
    rw [← neg_sub (F (v + h)), neg_div_neg_eq]
  rw [e3, e4] at s2
  have key := s1.trans s2
  exact (div_le_div_iff_of_pos_right hh).mp key

theorem curve_sub_antitoneOn (hS : SepConfig D X) {c c' : E} (hcc : c 0 ≤ c' 0) :
    AntitoneOn (fun x => curve D c x - curve D c' x)
      {x | |x - c 0| < wid D ∧ |x - c' 0| < wid D} := by
  intro x hx y hy hxy
  have hF := (gUp_concaveOn hS).neg
  have mem : ∀ t : ℝ, |t| < wid D → t ∈ Set.Ioo (-wid D) (wid D) := fun t ht =>
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have key := convex_incr_mono hF (u := x - c' 0) (v := y - c' 0) (h := c' 0 - c 0)
    (mem _ hx.2) (mem _ hy.2) (by rw [show x - c' 0 + (c' 0 - c 0) = x - c 0 by ring]; exact mem _ hx.1)
    (by rw [show y - c' 0 + (c' 0 - c 0) = y - c 0 by ring]; exact mem _ hy.1)
    (by linarith) (by linarith)
  rw [show x - c' 0 + (c' 0 - c 0) = x - c 0 by ring,
    show y - c' 0 + (c' 0 - c 0) = y - c 0 by ring] at key
  simp only [Pi.neg_apply] at key
  simp only [curve]
  linarith

end Erdos956Upper
