import ErdosLean.Erdos790.Defs

/-! Part: derandomised union bound.  If each `a` forbids a set `G a` of at most `m/2` colour
positions (not containing its own position `g a`), some colouring `χ : ι → Fin m` makes at
least half of the `a` good. -/

namespace Erdos790

open Classical in
/-- For distinct positions `j ≠ k`, exactly a `1/m` fraction of colourings agree at `j`, `k`. -/
theorem card_coloring_eq_mul {ι : Type*} [Fintype ι] (m : ℕ) {j k : ι} (hjk : j ≠ k) :
    m * (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ k)).card =
      Fintype.card (ι → Fin m) := by
  set e := Equiv.funSplitAt j (Fin m)
  have hk : k ≠ j := fun h => hjk h.symm
  have h1 : (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ k)).card =
      Fintype.card ({ i // i ≠ j } → Fin m) := by
    rw [Finset.card_filter, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    have : ∀ (b : Fin m) (f : { i // i ≠ j } → Fin m),
        (if (e.symm (b, f)) j = (e.symm (b, f)) k then 1 else 0 : ℕ) =
          if f ⟨k, hk⟩ = b then 1 else 0 := by
      intro b f
      simp only [e, Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, hk, dite_false,
        dite_true]
      by_cases h : b = f ⟨k, hk⟩
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
  rw [h1, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]

open Classical in
theorem exists_coloring_many_good {α ι : Type*} [Fintype ι] (S : Finset α) (g : α → ι)
    (G : α → Finset ι) (m : ℕ) (hm : 0 < m) (hg : ∀ a ∈ S, g a ∉ G a)
    (hG : ∀ a ∈ S, 2 * (G a).card ≤ m) :
    ∃ χ : ι → Fin m, S.card ≤ 2 * (S.filter (fun a => ∀ j ∈ G a, χ j ≠ χ (g a))).card := by
  set N := Fintype.card (ι → Fin m) with hN
  have hNpos : 0 < N := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact Fintype.card_pos
  let good : (ι → Fin m) → ℕ := fun χ => (S.filter (fun a => ∀ j ∈ G a, χ j ≠ χ (g a))).card
  let bad : (ι → Fin m) → ℕ := fun χ => (S.filter (fun a => ¬ ∀ j ∈ G a, χ j ≠ χ (g a))).card
  have hgb : ∀ χ, good χ + bad χ = S.card := fun χ => Finset.card_filter_add_card_filter_not _
  -- bad χ ≤ Σ_{a ∈ S} Σ_{j ∈ G a} [χ j = χ (g a)]
  have hbad : ∀ χ : ι → Fin m, bad χ ≤
      ∑ a ∈ S, ∑ j ∈ G a, (if χ j = χ (g a) then 1 else 0 : ℕ) := by
    intro χ
    show (S.filter _).card ≤ _
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro a _
    by_cases h : ∀ j ∈ G a, χ j ≠ χ (g a)
    · rw [if_neg (not_not_intro h)]; exact Nat.zero_le _
    · rw [if_pos h]
      push Not at h
      obtain ⟨j, hj, hjeq⟩ := h
      have := Finset.single_le_sum (f := fun j => (if χ j = χ (g a) then 1 else 0 : ℕ))
        (fun _ _ => Nat.zero_le _) hj
      simp only [hjeq, ite_true] at this
      exact this
  have hsum : m * ∑ χ, bad χ ≤ ∑ a ∈ S, (G a).card * N := by
    calc m * ∑ χ, bad χ ≤ m * ∑ χ : ι → Fin m,
          ∑ a ∈ S, ∑ j ∈ G a, (if χ j = χ (g a) then 1 else 0 : ℕ) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun χ _ => hbad χ)
      _ = ∑ a ∈ S, ∑ j ∈ G a,
          m * (Finset.univ.filter (fun χ : ι → Fin m => χ j = χ (g a))).card := by
          simp_rw [Finset.mul_sum, Finset.card_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
      _ = ∑ a ∈ S, (G a).card * N := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Finset.sum_congr rfl fun j hj =>
            card_coloring_eq_mul m (j := j) (k := g a)
              (fun h => hg a ha (by rw [← h]; exact hj))]
          simp [hN]
  have hsum2 : 2 * ∑ χ, bad χ ≤ S.card * N := by
    have : m * (2 * ∑ χ, bad χ) ≤ m * (S.card * N) := by
      calc m * (2 * ∑ χ, bad χ) = 2 * (m * ∑ χ, bad χ) := by ring
        _ ≤ 2 * ∑ a ∈ S, (G a).card * N := Nat.mul_le_mul_left _ hsum
        _ = ∑ a ∈ S, (2 * (G a).card) * N := by rw [Finset.mul_sum]; simp [mul_assoc]
        _ ≤ ∑ a ∈ S, m * N := Finset.sum_le_sum fun a ha => Nat.mul_le_mul_right _ (hG a ha)
        _ = m * (S.card * N) := by rw [Finset.sum_const, smul_eq_mul]; ring
    exact Nat.le_of_mul_le_mul_left this hm
  have htot : ∑ χ, good χ + ∑ χ, bad χ = S.card * N := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun χ _ => hgb χ, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, hN, mul_comm]
  by_contra hcon
  push Not at hcon
  have hlt : ∑ χ : ι → Fin m, 2 * good χ < ∑ χ : ι → Fin m, S.card := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
    · intro χ _; exact hcon χ
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hN] at hlt
  nlinarith [hsum2, htot, hlt]

end Erdos790
