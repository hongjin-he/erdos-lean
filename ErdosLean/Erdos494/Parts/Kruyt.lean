import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part C1 (Kruyt): uniqueness fails for `|A| = k`.

`A_k` is the one-point multiset `{Σ A}`.  We take `A = {0,1,…,k-1}` and
`B = {0 + i, 1 - i, 2, …, k-1}` (same total, `A ≠ B` since `0 ∈ A \ B`). -/

namespace Erdos494

open Complex

/-- If `|C| = k` then `C_k = {Σ C}`. -/
lemma sumMultiset_of_card_eq (C : Finset ℂ) (k : ℕ) (hC : C.card = k) :
    sumMultiset C k = {C.sum id} := by
  subst hC
  unfold sumMultiset
  rw [Finset.powersetCard_self]
  rfl

theorem kruyt_counterexample : ∀ k > 2, ¬Erdos494Unique k k := by
  intro k hk hU
  let c : ℕ → ℂ := fun i => (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)
  let f : ℕ → ℂ := fun i => (i : ℂ)
  let g : ℕ → ℂ := fun i => (i : ℂ) + I * c i
  have hcre : ∀ i, (I * c i).re = 0 := by
    intro i
    simp only [c]
    split_ifs <;> simp
  have hf : Function.Injective f := by
    intro a b h
    simp only [f] at h
    exact_mod_cast h
  have hg : Function.Injective g := by
    intro a b h
    have h2 := congrArg Complex.re h
    simp only [g, Complex.add_re, hcre, add_zero, Complex.natCast_re] at h2
    exact_mod_cast h2
  set A := (Finset.range k).image f with hAdef
  set B := (Finset.range k).image g with hBdef
  have hA : A.card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_range]
  have hB : B.card = k := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_range]
  have hc : ∑ i ∈ Finset.range k, c i = 0 := by
    simp only [c]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    have h1 : 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
    simp [h0, h1]
  have hsum : A.sum id = B.sum id := by
    rw [Finset.sum_image (fun a _ b _ h => hf h), Finset.sum_image (fun a _ b _ h => hg h)]
    simp only [id, g, f]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc, mul_zero, add_zero]
  have hAB : A = B := hU A B hA hB (by
    rw [sumMultiset_of_card_eq A k hA, sumMultiset_of_card_eq B k hB, hsum])
  have h0A : (0 : ℂ) ∈ A := by
    rw [hAdef, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr (by omega), by simp [f]⟩
  have h0B : (0 : ℂ) ∉ B := by
    rw [hBdef, Finset.mem_image]
    rintro ⟨i, _, hi⟩
    have hre := congrArg Complex.re hi
    simp only [g, Complex.add_re, hcre, add_zero, Complex.natCast_re, Complex.zero_re] at hre
    have hi0 : i = 0 := by exact_mod_cast hre
    subst hi0
    have him := congrArg Complex.im hi
    simp [g, c] at him
  exact h0B (hAB ▸ h0A)

end Erdos494
