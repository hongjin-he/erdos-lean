import ErdosLean.Erdos790.Defs

/-! Part: passing from `ℕ`-indices to `Fin (topIdx A + 1)` keeps `idx (dyIdx a) ∉ idx '' F(a)`. -/

namespace Erdos790

theorem idx_not_mem_image_Fset {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    idx A (dyIdx a) ∉ (Fset A a).image (idx A) := by
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨j, hj, heq⟩ := h
  unfold Fset at hj
  rw [Finset.mem_erase, Finset.mem_biUnion] at hj
  obtain ⟨hne, δ, _, hw⟩ := hj
  unfold window at hw
  rw [Finset.mem_filter, Finset.mem_range] at hw
  have hda : dyIdx a < topIdx A + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := dyIdx) ha)
  have hv := congrArg Fin.val heq
  simp only [idx, Fin.val_ofNat] at hv
  rw [Nat.mod_eq_of_lt hw.1, Nat.mod_eq_of_lt hda] at hv
  exact hne hv

end Erdos790
