import ErdosLean.Erdos790.Defs

/-! Part: `|F(a)| ≤ K(|A|)` and `F(a) ⊆ [0, topIdx A]`. -/

namespace Erdos790

theorem fs_card_window_le (N : ℕ) (δ : ℤ) (M : ℕ) :
    (window N δ M).card ≤ Nat.clog 2 N + 5 := by
  rcases (window N δ M).eq_empty_or_nonempty with h | hne
  · simp [h]
  set j0 := (window N δ M).min' hne with hj0def
  have hj0 : j0 ∈ window N δ M := Finset.min'_mem _ _
  have hsub : window N δ M ⊆ Finset.Ico j0 (j0 + (Nat.clog 2 N + 4)) := by
    intro j hj
    have hle : j0 ≤ j := Finset.min'_le _ _ hj
    simp only [window, Finset.mem_filter] at hj hj0
    rw [Finset.mem_Ico]
    refine ⟨hle, ?_⟩
    have hN : (N : ℤ) ≤ 2 ^ Nat.clog 2 N := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) N
    have h1 : (2:ℤ) ^ j ≤ 2 ^ (j0 + Nat.clog 2 N + 3) := by
      calc (2:ℤ) ^ j ≤ 2 * δ := hj.2.2
        _ ≤ 2 * (2 * N * 2 ^ (j0 + 1)) := by linarith [hj0.2.1]
        _ = 8 * N * 2 ^ j0 := by ring
        _ ≤ 8 * 2 ^ Nat.clog 2 N * 2 ^ j0 := by gcongr
        _ = 2 ^ (j0 + Nat.clog 2 N + 3) := by ring
    have := (pow_le_pow_iff_right₀ (by norm_num : (1:ℤ) < 2)).1 h1
    omega
  calc _ ≤ (Finset.Ico j0 (j0 + (Nat.clog 2 N + 4))).card := Finset.card_le_card hsub
    _ = Nat.clog 2 N + 4 := by simp
    _ ≤ _ := by omega

theorem card_Dplus_le (A : Finset ℤ) (a : ℤ) :
    (Dplus A a).card ≤ Nat.clog 2 A.card + 1 := by
  unfold Dplus
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  unfold Dset
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem card_Fset_le (A : Finset ℤ) (hA : 1 ≤ A.card) (a : ℤ) :
    (Fset A a).card ≤ K A.card := by
  unfold Fset K
  calc _ ≤ ((Dplus A a).biUnion (fun δ => window A.card δ (topIdx A))).card :=
        Finset.card_erase_le
    _ ≤ ∑ δ ∈ Dplus A a, (window A.card δ (topIdx A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _δ ∈ Dplus A a, (Nat.clog 2 A.card + 5) :=
        Finset.sum_le_sum fun δ _ => fs_card_window_le _ _ _
    _ = (Dplus A a).card * (Nat.clog 2 A.card + 5) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_Dplus_le A a)

theorem lt_of_mem_Fset {A : Finset ℤ} {a : ℤ} {j : ℕ} (hj : j ∈ Fset A a) :
    j < topIdx A + 1 := by
  unfold Fset at hj
  obtain ⟨_, hj⟩ := Finset.mem_erase.1 hj
  obtain ⟨δ, _, hj⟩ := Finset.mem_biUnion.1 hj
  unfold window at hj
  exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

theorem dyIdx_not_mem_Fset (A : Finset ℤ) (a : ℤ) : dyIdx a ∉ Fset A a := by
  unfold Fset
  exact Finset.notMem_erase _ _

theorem fs_mem_Fset_of {A : Finset ℤ} {a δ : ℤ} {j : ℕ} (hδ : δ ∈ Dplus A a)
    (hj : j ∈ window A.card δ (topIdx A)) (hne : j ≠ dyIdx a) : j ∈ Fset A a := by
  unfold Fset
  exact Finset.mem_erase.2 ⟨hne, Finset.mem_biUnion.2 ⟨δ, hδ, hj⟩⟩

end Erdos790
