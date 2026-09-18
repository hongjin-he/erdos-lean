import ErdosLean.Erdos956Upper.Parts.UpperArc
import ErdosLean.Erdos956Upper.Parts.SupportHalfplane

/-!
# Erdős #956 upper bound — P4: orientation of unit vectors

Every unit vector lies on the upper arc or the right side, up to sign.  For `|v₀| < w` and `v` strictly inside the vertical chord, the supporting normal would be horizontal, forcing `|v₀| = w`.
-/

namespace Erdos956Upper

open Erdos956 Metric

variable {D : Set E} {X : Finset E}

lemma inner_coord_P4 (x y : E) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma infDist_neg_le_P4 (hS : SepConfig D X) (x : E) : infDist (-x) D ≤ infDist x D := by
  obtain ⟨d, hd, hdd⟩ := hS.compact.exists_infDist_eq_dist ⟨0, hS.zero_mem⟩ x
  calc infDist (-x) D ≤ dist (-x) (-d) := infDist_le_dist_of_mem (hS.neg_mem d hd)
    _ = infDist x D := by rw [dist_neg_neg, hdd]

theorem unit_orientation (hS : SepConfig D X) {v : E} (hv : infDist v D = 1) :
    OnSide D v ∨ OnSide D (-v) ∨ OnUpper D v ∨ OnUpper D (-v) := by
  have hK : v ∈ Kset D := le_of_eq hv
  have hKn : -v ∈ Kset D := kset_neg hS hK
  have hvn : infDist (-v) D = 1 := by
    apply le_antisymm (hv ▸ infDist_neg_le_P4 hS v)
    have := infDist_neg_le_P4 hS (-v)
    rw [neg_neg] at this; linarith
  have habs := abs_le_wid hS hK
  by_cases heq : |v 0| = wid D
  · rcases abs_eq_abs.mp (heq.trans (abs_of_pos (lt_of_lt_of_le one_pos (one_le_wid hS))).symm)
      with h | h
    · exact Or.inl ⟨h, hv⟩
    · exact Or.inr (Or.inl ⟨by simp [h], hvn⟩)
  have hv0 : |v 0| < wid D := lt_of_le_of_ne habs heq
  have hv0' : |(-v) 0| < wid D := by simpa using hv0
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨-, -, hU, hUn⟩ := hcon
  have h1 : v 1 < gUp D (v 0) :=
    lt_of_le_of_ne (le_gUp hS hK hv0) (fun h => hU ⟨hv0, h⟩)
  have h2 : (-v) 1 < gUp D ((-v) 0) :=
    lt_of_le_of_ne (le_gUp hS hKn hv0') (fun h => hUn ⟨hv0', h⟩)
  simp only [PiLp.neg_apply] at h2
  obtain ⟨d, -, hnorm, hsup⟩ := exists_support hS.compact hS.convex ⟨0, hS.zero_mem⟩ hv
  have hu1 := hsup _ (pt2_gUp_mem hS hv0)
  have hmem2 := kset_neg hS (pt2_gUp_mem hS (by simpa using hv0 : |-v 0| < wid D))
  have hu2 := hsup _ hmem2
  rw [inner_coord_P4] at hu1 hu2
  simp only [PiLp.sub_apply, PiLp.neg_apply, pt2_zero, pt2_one] at hu1 hu2
  have hn1 : v 1 - d 1 = 0 := by
    apply le_antisymm
    · nlinarith
    · nlinarith
  have hn : (v 0 - d 0) ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq (v - d)
    rw [hnorm, inner_coord_P4] at h
    simp only [PiLp.sub_apply] at h
    rw [hn1] at h; nlinarith
  have hbound : ∀ u ∈ Kset D, u 0 ≤ |v 0| := by
    intro u hu
    have a := hsup u hu
    have b := hsup (-u) (kset_neg hS hu)
    rw [inner_coord_P4] at a b
    simp only [PiLp.sub_apply, PiLp.neg_apply, hn1, mul_zero, add_zero] at a b
    have : v 0 - d 0 = 1 ∨ v 0 - d 0 = -1 := by
      have : (v 0 - d 0 - 1) * (v 0 - d 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · rw [h] at a; linarith [le_abs_self (v 0)]
    · rw [h] at b; linarith [neg_le_abs (v 0)]
  have : wid D ≤ |v 0| := by
    unfold wid
    apply csSup_le (⟨v 0, v, hK, rfl⟩ : ((fun v : E => v 0) '' Kset D).Nonempty)
    rintro _ ⟨u, hu, rfl⟩
    exact hbound u hu
  linarith

end Erdos956Upper
