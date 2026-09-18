import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: clique-freeness of the blow-up

A clique of the blow-up meets each clump at most once (clumps are independent) and its layers
span at most two consecutive layers `m, m+1` (with `m` the least layer).  So it has at most
`cnt m + cnt (m+1) < s` vertices.

Proof plan: for `t : Finset (Vtx L)` an `s`-clique, the map `v ↦ v.1` is injective on `t` and
lands in the clumps with layer in `{m, m+1}`; that finset has card `cnt m + cnt (m+1)`.
-/

namespace Erdos612

private theorem clump_eq {L : Layers} (c d : Clump L) (h1 : c.1.val = d.1.val)
    (h2 : c.2.val = d.2.val) : c = d := by
  obtain ⟨a, i⟩ := c
  obtain ⟨b, j⟩ := d
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : i = j := Fin.ext h2
  rfl

theorem cliqueFree_blowup (L : Layers) (s : ℕ) (hne : L ≠ [])
    (h : AllWin (CliqQ s) L) : (blowup L).CliqueFree s := by
  intro t ht
  have hs : 0 < s := by
    have := h 0 (List.length_pos_iff.mpr hne)
    unfold CliqQ at this; omega
  have htne : t.Nonempty := by
    rw [← Finset.card_pos, ht.card_eq]; exact hs
  set m := (t.image Vtx.layer).min' (htne.image _) with hm
  obtain ⟨w, hwt, hwm⟩ := Finset.mem_image.mp ((t.image Vtx.layer).min'_mem (htne.image _))
  rw [← hm] at hwm
  have hlo : ∀ v ∈ t, m ≤ v.layer := fun v hv =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv)
  have hhi : ∀ v ∈ t, v.layer ≤ m + 1 := by
    intro v hv
    by_cases hvw : v = w
    · subst hvw; omega
    · have := ht.isClique hv hwt hvw
      exact hwm ▸ this.2.1
  have hmlt : m < L.length := by
    rw [← hwm]; exact w.1.1.isLt
  have hQ : L.cnt m + L.cnt (m + 1) < s := h m hmlt
  let f : Vtx L → ℕ := fun v => if v.layer = m then v.1.2.val else L.cnt m + v.1.2.val
  have hbd : ∀ v ∈ t, f v ∈ Finset.range (L.cnt m + L.cnt (m + 1)) := by
    intro v hv
    have hlt : v.1.2.val < L.cnt v.1.1 := v.1.2.isLt
    have h1 := hlo v hv
    have h2 := hhi v hv
    simp only [Finset.mem_range, f]
    split_ifs with he
    · have : L.cnt v.1.1 = L.cnt m := by rw [← he]; rfl
      omega
    · have he' : v.layer = m + 1 := by omega
      have : L.cnt v.1.1 = L.cnt (m + 1) := by rw [← he']; rfl
      omega
  have hinj : Set.InjOn f t := by
    intro u hu v hv huv
    by_contra hne'
    have hadj := ht.isClique hu hv hne'
    apply hadj.1
    have hlu : u.1.2.val < L.cnt u.1.1 := u.1.2.isLt
    have hlv : v.1.2.val < L.cnt v.1.1 := v.1.2.isLt
    have h1 := hlo u hu
    have h2 := hhi u hu
    have h3 := hlo v hv
    have h4 := hhi v hv
    simp only [f] at huv
    have hL : u.layer = v.layer ∧ u.1.2.val = v.1.2.val := by
      split_ifs at huv with ha hb hb
      · exact ⟨by omega, huv⟩
      · have : L.cnt u.1.1 = L.cnt m := by rw [← ha]; rfl
        omega
      · have : L.cnt v.1.1 = L.cnt m := by rw [← hb]; rfl
        omega
      · exact ⟨by omega, by omega⟩
    exact clump_eq _ _ hL.1 hL.2
  have := Finset.card_le_card_of_injOn f hbd hinj
  rw [Finset.card_range, ht.card_eq] at this
  omega

end Erdos612
