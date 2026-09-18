import ErdosLean.Erdos612.Parts.Degree

/-!
# Erdős 612, part: minimum degree of the blow-up from window conditions

Proof plan: `DegQ` + `degree_add_wt` give `δ ≤ degree v` for all `v`
(`le_minDegree_of_forall_le_degree`);
the `TightQ` window gives a clump `w ∈ lay ℓ` with `δ + w = nbr ℓ`; `PosQ` makes `w > 0`, so
the clump has a vertex of degree exactly `δ` (`minDegree_le_degree`).
-/

open SimpleGraph

namespace Erdos612

lemma nbr_eq_window (L : Layers) (ℓ : ℕ) :
    L.nbr ℓ = (L.lft ℓ).sum + (L.lay ℓ).sum + (L.lay (ℓ + 1)).sum := rfl

lemma wt_mem_lay (L : Layers) (c : Clump L) : L.wt c.1 c.2 ∈ L.lay c.1 := by
  unfold Layers.wt
  have hj : (c.2 : ℕ) < (L.lay c.1).length := c.2.2
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem minDegree_blowup (L : Layers) (δ : ℕ) (hpos : AllWin PosQ L)
    (hdeg : AllWin (DegQ δ) L) (ht : SomeWin (TightQ δ) L) :
    (blowup L).minDegree = δ := by
  obtain ⟨ℓ, hℓ, w, hw, hwt⟩ := ht
  obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.1 hw
  have hwpos : 0 < w := (hpos ℓ hℓ).2 w hw
  let c : Clump L := ⟨⟨ℓ, hℓ⟩, ⟨j, hj⟩⟩
  have hcw : L.wt c.1 c.2 = w := by
    show L.wt ℓ j = w
    unfold Layers.wt
    rw [List.getD_eq_getElem _ _ hj, hjw]
  let v : Vtx L := ⟨c, ⟨0, by rw [hcw]; exact hwpos⟩⟩
  have : Nonempty (Vtx L) := ⟨v⟩
  have hv : (blowup L).degree v = δ := by
    have h := degree_add_wt L v
    have h2 : L.nbr v.1.1 = δ + w := by rw [nbr_eq_window]; exact hwt.symm
    rw [h2] at h
    have : L.wt v.1.1 v.1.2 = w := hcw
    omega
  apply le_antisymm
  · rw [← hv]; exact minDegree_le_degree _ _
  · apply le_minDegree_of_forall_le_degree
    intro u
    have h := degree_add_wt L u
    have hd := hdeg u.1.1 u.1.1.2 _ (wt_mem_lay L u.1)
    rw [← nbr_eq_window] at hd
    omega

end Erdos612
