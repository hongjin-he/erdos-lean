import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: order of the blow-up and length/weight of periodic families

Proof plan: `Fintype.card_sigma` twice, then `Fin.sum_univ_eq_sum_range` /
`List.sum_ofFn`-style rewriting of `∑ j : Fin (cnt ℓ), wt ℓ j` to `(L.lay ℓ).sum` and of
`∑ ℓ : Fin L.length, tot ℓ` to `(L.map List.sum).sum`.
-/

namespace Erdos612

private theorem sum_fin_getD (l : List ℕ) :
    ∑ j : Fin l.length, l.getD (j : ℕ) 0 = l.sum := by
  have : ∀ j : Fin l.length, l.getD (j : ℕ) 0 = l[(j : ℕ)] := fun j =>
    List.getD_eq_getElem _ _ j.2
  simp only [this]
  exact Fin.sum_univ_getElem l

private theorem sum_fin_lay (L : Layers) :
    ∑ ℓ : Fin L.length, (L.lay ℓ).sum = L.total := by
  have : ∀ ℓ : Fin L.length, (L.lay ℓ).sum = (L.map List.sum)[(ℓ : ℕ)]'(by simp) := by
    intro ℓ
    simp [Layers.lay]
  simp only [this, Layers.total]
  rw [← Fin.sum_univ_getElem (L.map List.sum)]
  exact (Fintype.sum_equiv (finCongr (by simp)) _ _ (fun _ => rfl))

theorem card_vtx (L : Layers) : Fintype.card (Vtx L) = L.total := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fintype.sum_sigma]
  rw [← sum_fin_lay]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  exact sum_fin_getD (L.lay ℓ)

theorem length_fam (pre per suf : Layers) (p : ℕ) :
    (fam pre per suf p).length = pre.length + p * per.length + suf.length := by
  simp [fam, List.length_flatten, List.sum_replicate]; ring

theorem total_fam (pre per suf : Layers) (p : ℕ) :
    (fam pre per suf p).total = pre.total + p * per.total + suf.total := by
  simp [fam, Layers.total, List.map_flatten, List.sum_flatten, List.map_replicate,
    List.sum_replicate]; ring

end Erdos612
