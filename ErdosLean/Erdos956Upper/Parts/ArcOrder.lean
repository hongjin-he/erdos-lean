import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P10: vertical order of non-crossing arcs

On the common open interval of two valid non-crossing arcs the sign of `a.f - b.f` is constant (intermediate value theorem).
-/

namespace Erdos956Upper

open Erdos956 Metric

theorem Arc.lt_of_lt_of_not_crosses {a b : Arc} (ha : a.Valid) (hb : b.Valid)
    (hnc : ¬ a.Crosses b) {x y : ℝ} (hxa : x ∈ Set.Ioo a.l a.r) (hxb : x ∈ Set.Ioo b.l b.r)
    (hya : y ∈ Set.Ioo a.l a.r) (hyb : y ∈ Set.Ioo b.l b.r) (hlt : a.f x < b.f x) :
    a.f y < b.f y := by
  by_contra hge
  rw [not_lt] at hge
  have hsa : Set.uIcc x y ⊆ Set.Ioo a.l a.r := Set.OrdConnected.uIcc_subset inferInstance hxa hya
  have hsb : Set.uIcc x y ⊆ Set.Ioo b.l b.r := Set.OrdConnected.uIcc_subset inferInstance hxb hyb
  have hca : ContinuousOn a.f (Set.uIcc x y) :=
    ha.2.mono (hsa.trans Set.Ioo_subset_Icc_self)
  have hcb : ContinuousOn b.f (Set.uIcc x y) :=
    hb.2.mono (hsb.trans Set.Ioo_subset_Icc_self)
  have hc : ContinuousOn (fun t => b.f t - a.f t) (Set.uIcc x y) := hcb.sub hca
  have h0 : (0 : ℝ) ∈ Set.uIcc ((fun t => b.f t - a.f t) x) ((fun t => b.f t - a.f t) y) := by
    simp only
    rw [Set.mem_uIcc]
    right
    constructor <;> linarith
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hc h0
  exact hnc ⟨z, hsa hz, hsb hz, by simp only at hz0; linarith⟩

end Erdos956Upper
