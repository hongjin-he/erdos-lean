import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: from graphs on `Fin n` to graphs on any finite type

Given `G` on a finite type `V` with the hypotheses of `DiamBoundType`, let
`e := Fintype.equivFin V` and `G' := G.map e.toEmbedding` on `Fin (Fintype.card V)`, with
`φ := SimpleGraph.Iso.map e G : G ≃g G'` (Mathlib, `Maps.lean`).  Then
* `Iso.connected_iff φ` transfers connectivity;
* `cliqueFree_map_iff` (`Clique.lean`, needs `Nonempty V`, from connectivity) transfers
  `CliqueFree`;
* `Iso.minDegree_eq φ` (`Finite.lean`) transfers the minimum degree (any `DecidableRel`
  instance on `G'`, e.g. `Classical.decRel`; instances are subsingletons);
* `G.diam ≤ G'.diam`: take `u v` with `G.dist u v = G.diam` (`exists_dist_eq_diam`), map a
  shortest `G'`-walk from `e u` to `e v` back along `φ.symm` (`Walk.map`, `Walk.length_map`,
  `dist_le`), and bound `G'.dist ≤ G'.diam` by `dist_le_diam` with
  `connected_iff_ediam_ne_top`.
-/

namespace Erdos612

theorem diamBoundType_of_diamBound {s m : ℕ} {c : ℝ} (h : DiamBound s m c) :
    DiamBoundType s m c := by
  classical
  intro d hd hm
  obtain ⟨C, hC⟩ := h d hd hm
  refine ⟨C, ?_⟩
  intro V _ G _ hconn hcf hmin
  have : Nonempty V := hconn.nonempty
  let e := Fintype.equivFin V
  let G' : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  let φ : G ≃g G' := SimpleGraph.Iso.map e G
  have h1 : G'.Connected := (SimpleGraph.Iso.connected_iff φ).mp hconn
  have h2 : G'.CliqueFree s := SimpleGraph.cliqueFree_map_iff.mpr hcf
  have h3 : G'.minDegree = d := by rw [← SimpleGraph.Iso.minDegree_eq φ]; exact hmin
  have key := hC (Fintype.card V) G' h1 h2 h3
  have : Nonempty (Fin (Fintype.card V)) := h1.nonempty
  have hdiam : G.diam ≤ G'.diam := by
    obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    obtain ⟨p, hp⟩ := h1.exists_walk_length_eq_dist (φ u) (φ v)
    let q : G.Walk u v := (p.map φ.symm.toHom).copy (φ.symm_apply_apply u) (φ.symm_apply_apply v)
    have hq : G.dist u v ≤ G'.dist (φ u) (φ v) := by
      have := SimpleGraph.dist_le q
      simpa [q, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map, hp] using this
    rw [← huv]
    exact hq.trans (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp h1))
  calc (G.diam : ℝ) ≤ (G'.diam : ℝ) := by exact_mod_cast hdiam
    _ ≤ _ := key

end Erdos612
