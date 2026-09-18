import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: connectivity of the blow-up

Assume at least two layers, every layer nonempty and every weight positive.  Vertices in
consecutive layers are always adjacent (they lie in different clumps), and so are vertices of
different clumps in one layer.  Proof plan: fix a vertex `x₀` of layer `0`; show by induction
on `ℓ` that every vertex of layer `ℓ` is reachable from `x₀` (layer `ℓ+1` vertices are adjacent
to any vertex of layer `ℓ`; layer `0` vertices are adjacent to any vertex of layer `1`, which
exists because `2 ≤ L.length`).
-/

namespace Erdos612

/-- Vertices in consecutive layers are adjacent. -/
theorem blowup_adj_of_succ {L : Layers} (u v : Vtx L) (h : u.layer + 1 = v.layer) :
    (blowup L).Adj u v := by
  refine ⟨?_, by omega, by omega⟩
  intro huv
  have : u.layer = v.layer := by
    unfold Vtx.layer; rw [huv]
  omega

/-- A canonical vertex in layer `ℓ`. -/
def canonVtx (L : Layers) (hpos : AllWin PosQ L) (ℓ : ℕ) (hℓ : ℓ < L.length) : Vtx L :=
  have hne : L.lay ℓ ≠ [] := (hpos ℓ hℓ).1
  have hc : 0 < L.cnt ℓ := by
    unfold Layers.cnt; exact List.length_pos_iff.mpr hne
  have hw : 0 < L.wt ℓ 0 := by
    unfold Layers.wt
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hne
    have := (hpos ℓ hℓ).2 a (by rw [ht]; exact List.mem_cons_self)
    rw [ht]; simpa using this
  ⟨⟨⟨ℓ, hℓ⟩, ⟨0, hc⟩⟩, ⟨0, hw⟩⟩

theorem canonVtx_layer (L : Layers) (hpos : AllWin PosQ L) (ℓ : ℕ) (hℓ : ℓ < L.length) :
    (canonVtx L hpos ℓ hℓ).layer = ℓ := rfl

theorem connected_blowup (L : Layers) (hlen : 2 ≤ L.length) (hpos : AllWin PosQ L) :
    (blowup L).Connected := by
  have h0 : 0 < L.length := by omega
  set x₀ := canonVtx L hpos 0 h0
  have hreach : ∀ ℓ (hℓ : ℓ < L.length), (blowup L).Reachable x₀ (canonVtx L hpos ℓ hℓ) := by
    intro ℓ
    induction ℓ with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      intro hℓ
      exact (ih (by omega)).trans
        (blowup_adj_of_succ _ _ (by simp [canonVtx_layer])).reachable
  have hall : ∀ v : Vtx L, (blowup L).Reachable x₀ v := by
    intro v
    have hv : v.layer < L.length := v.1.1.2
    rcases Nat.eq_zero_or_pos v.layer with h | h
    · have h1 : 1 < L.length := by omega
      have r1 := hreach 1 h1
      exact r1.trans ((blowup_adj_of_succ v _ (by simp [canonVtx_layer, h])).symm.reachable)
    · have r := hreach (v.layer - 1) (by omega)
      exact r.trans (blowup_adj_of_succ _ v (by simp [canonVtx_layer]; omega)).reachable
  have : Nonempty (Vtx L) := ⟨x₀⟩
  exact SimpleGraph.Connected.mk (fun u v => (hall u).symm.trans (hall v))

end Erdos612
