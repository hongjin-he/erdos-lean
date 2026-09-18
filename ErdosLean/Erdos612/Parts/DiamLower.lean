import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: diameter lower bound

Along an edge the layer changes by at most one, so `dist u v ≥ layer v - layer u`
(induction on walks).  Taking `u` in layer `0` and `v` in the last layer gives
`L.length - 1 ≤ dist u v ≤ diam` (`SimpleGraph.dist_le_diam`, finite + connected ⇒
`ediam ≠ ⊤`).
-/

namespace Erdos612

theorem layer_le_walk_length (L : Layers) {u v : Vtx L} (p : (blowup L).Walk u v) :
    v.layer ≤ u.layer + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [SimpleGraph.Walk.length_cons]
    have := h.2.2
    omega

theorem layer_sub_le_dist (L : Layers) (u v : Vtx L) (h : (blowup L).Reachable u v) :
    v.layer - u.layer ≤ (blowup L).dist u v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  have := layer_le_walk_length L p
  omega

/-- A vertex in any layer `ℓ < L.length`, under `AllWin PosQ L`. -/
theorem exists_vtx_layer (L : Layers) (hpos : AllWin PosQ L) (ℓ : ℕ) (hℓ : ℓ < L.length) :
    ∃ v : Vtx L, v.layer = ℓ := by
  obtain ⟨hne, hw⟩ := hpos ℓ hℓ
  have hc : 0 < L.cnt ℓ := by
    unfold Layers.cnt; exact List.length_pos_of_ne_nil hne
  have hwt : 0 < L.wt ℓ 0 := by
    unfold Layers.wt
    apply hw
    rw [List.getD_eq_getElem _ _ hc]
    exact List.getElem_mem _
  exact ⟨⟨⟨⟨ℓ, hℓ⟩, ⟨0, hc⟩⟩, ⟨0, hwt⟩⟩, rfl⟩

theorem length_le_diam (L : Layers) (hpos : AllWin PosQ L) (hc : (blowup L).Connected) :
    L.length ≤ (blowup L).diam + 1 := by
  rcases Nat.eq_zero_or_pos L.length with h0 | hl
  · omega
  obtain ⟨u, hu⟩ := exists_vtx_layer L hpos 0 hl
  obtain ⟨v, hv⟩ := exists_vtx_layer L hpos (L.length - 1) (by omega)
  have h1 := layer_sub_le_dist L u v (hc.preconnected u v)
  have := hc.nonempty
  have hne : (blowup L).ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hc
  have h2 := SimpleGraph.dist_le_diam (u := u) (v := v) hne
  omega

end Erdos612
