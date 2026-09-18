import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part C2 (Tao): uniqueness fails for `|A| = 2k`.

If `|A| = 2k` and `Σ A = 0`, complementation `S ↦ A \ S` is a bijection of the `k`-subsets and
`Σ S = -Σ (A \ S)`, so `A_k = (-A)_k`.  Take `A = {1, …, 2k-1, -(1 + ⋯ + (2k-1))}`; then
`-A ≠ A` (`-1 ∉ A`). -/

namespace Erdos494

open Finset

/-- If `|A| = 2k` and `Σ A = 0`, then `(-A)_k = A_k`. -/
theorem sumMultiset_neg_of_sum_zero (A : Finset ℂ) (k : ℕ) (hc : A.card = 2 * k)
    (hs : A.sum id = 0) :
    sumMultiset (A.map (Equiv.neg ℂ).toEmbedding) k = sumMultiset A k := by
  unfold sumMultiset
  rw [Finset.powersetCard_map, Finset.map_val, Multiset.map_map]
  have key : ∀ t ∈ (A.powersetCard k).val,
      ((fun s : Finset ℂ => s.sum id) ∘
        (Finset.mapEmbedding (Equiv.neg ℂ).toEmbedding).toEmbedding) t = (A \ t).sum id := by
    intro t ht
    rw [Finset.mem_val, Finset.mem_powersetCard] at ht
    have h1 := Finset.sum_sdiff ht.1 (f := id)
    rw [hs] at h1
    simp only [Function.comp, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply,
      Finset.sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, id]
    rw [Finset.sum_neg_distrib]
    simp only [id] at h1
    linear_combination -h1
  rw [Multiset.map_congr rfl key]
  have hperm : (A.powersetCard k).val.map (fun t => A \ t) = (A.powersetCard k).val := by
    rw [Multiset.Nodup.ext]
    · intro u
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_powersetCard]
      constructor
      · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
        refine ⟨Finset.sdiff_subset, ?_⟩
        rw [Finset.card_sdiff_of_subset ht1, hc, ht2]; omega
      · rintro ⟨hu1, hu2⟩
        refine ⟨A \ u, ⟨Finset.sdiff_subset, ?_⟩, Finset.sdiff_sdiff_eq_self hu1⟩
        rw [Finset.card_sdiff_of_subset hu1, hc, hu2]; omega
    · refine Multiset.Nodup.map_on ?_ (A.powersetCard k).nodup
      intro x hx y hy hxy
      rw [Finset.mem_val, Finset.mem_powersetCard] at hx hy
      rw [← Finset.sdiff_sdiff_eq_self hx.1, ← Finset.sdiff_sdiff_eq_self hy.1]
      exact congrArg (A \ ·) hxy
    · exact (A.powersetCard k).nodup
  calc ((A.powersetCard k).val.map fun t => (A \ t).sum id)
      = (((A.powersetCard k).val.map fun t => A \ t).map fun s => s.sum id) := by
        rw [Multiset.map_map]; rfl
    _ = _ := by rw [hperm]

theorem tao_counterexample : ∀ k > 2, ¬Erdos494Unique k (2 * k) := by
  intro k hk hU
  set I : Finset ℕ := Finset.Icc 1 (2 * k - 1) with hI
  set N : ℕ := ∑ i ∈ I, i with hN
  set B : Finset ℂ := I.image (fun i : ℕ => (i : ℂ)) with hB
  set A : Finset ℂ := insert (-(N : ℂ)) B with hA
  have hinj : Function.Injective (fun i : ℕ => (i : ℂ)) := Nat.cast_injective
  have hBcard : B.card = 2 * k - 1 := by
    rw [hB, Finset.card_image_of_injective _ hinj, hI, Nat.card_Icc]; omega
  have hmemB : ∀ z ∈ B, 0 < z.re := by
    intro z hz
    rw [hB, Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    rw [hI, Finset.mem_Icc] at hi
    simp only [Complex.natCast_re, Nat.cast_pos]; omega
  have hNpos : 2 ≤ N := by
    rw [hN]
    have h2 : (2 : ℕ) ∈ I := by rw [hI, Finset.mem_Icc]; omega
    exact Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) h2
  have hnotin : -(N : ℂ) ∉ B := by
    intro h
    have := hmemB _ h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  have hAcard : A.card = 2 * k := by
    rw [hA, Finset.card_insert_of_notMem hnotin, hBcard]; omega
  have hBsum : B.sum id = (N : ℂ) := by
    rw [hB, Finset.sum_image (fun x _ y _ h => hinj h), hN]; simp
  have hAsum : A.sum id = 0 := by
    rw [hA, Finset.sum_insert hnotin, hBsum]; simp
  have hneg := sumMultiset_neg_of_sum_zero A k hAcard hAsum
  have hAcard' : (A.map (Equiv.neg ℂ).toEmbedding).card = 2 * k := by
    rw [Finset.card_map, hAcard]
  have heq := hU _ _ hAcard' hAcard hneg
  -- `1 ∈ A`, so `-1 ∈ A`, contradiction.
  have h1 : (1 : ℂ) ∈ A := by
    rw [hA]; apply Finset.mem_insert_of_mem
    rw [hB, Finset.mem_image]
    exact ⟨1, by rw [hI, Finset.mem_Icc]; omega, by simp⟩
  have hm1 : (-1 : ℂ) ∈ A.map (Equiv.neg ℂ).toEmbedding := by
    rw [Finset.mem_map]; exact ⟨1, h1, by simp⟩
  rw [heq, hA, Finset.mem_insert] at hm1
  rcases hm1 with h | h
  · have : (N : ℂ) = 1 := by linear_combination h
    have : N = 1 := by exact_mod_cast this
    omega
  · have := hmemB _ h
    norm_num at this

end Erdos494
