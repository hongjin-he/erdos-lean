import ErdosLean.Erdos612.Defs

/-!
# Erdős 612, part: periodic window reduction

For `p ≥ 2` copies of a period, every three-layer window of `fam pre per suf p` occurs in
`fam pre per suf 2` (this needs `2 ≤ per.length`), and conversely (this only needs
`per ≠ []`).  Hence local properties checked by `decide` on the two-period instance hold for
every `p + 2`.

**Correction.**  The original statement of `window_reduce` assumed only `per ≠ []`; it is false
for a period of length one: with `pre = suf = []`, `per = [[1]]`, the family with three periods
has the window `([1], [1], [1])` at layer `1`, while the windows of the two-period family
`[[1], [1]]` are `([], [1], [1])` and `([1], [1], [])` (see `window_reduce_counterexample`).
The hypothesis is therefore strengthened to `2 ≤ per.length` (both periods used in `Main.lean`
have length `7` resp. more, so `by decide` still discharges it).

Proof: one period is removed at a time.  Layers below `pre.length + k * per.length` of the
`k`- and `(k+1)`-period families agree; above `pre.length` the `(k+1)`-period family is the
`k`-period family shifted by `per.length`.
-/

namespace Erdos612

private lemma fam_eq (pre per suf : Layers) (k : ℕ) :
    fam pre per suf k = pre ++ ((List.replicate k per).flatten ++ suf) := by
  simp [fam, List.append_assoc]

private lemma len_flat (per : Layers) (k : ℕ) :
    ((List.replicate k per).flatten).length = k * per.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- Prefix agreement. -/
private lemma fam_prefix (pre per suf : Layers) (k m i : ℕ)
    (hi : i < pre.length + k * per.length) :
    (fam pre per suf (k + m))[i]? = (fam pre per suf k)[i]? := by
  have h1 : fam pre per suf (k + m) =
      (pre ++ (List.replicate k per).flatten) ++ ((List.replicate m per).flatten ++ suf) := by
    rw [fam, List.replicate_add, List.flatten_append]; simp only [List.append_assoc]
  have h2 : fam pre per suf k = (pre ++ (List.replicate k per).flatten) ++ suf := rfl
  have hl : i < (pre ++ (List.replicate k per).flatten).length := by
    simp only [List.length_append, len_flat]; exact hi
  rw [h1, h2, List.getElem?_append_left hl, List.getElem?_append_left hl]

/-- Shift agreement. -/
private lemma fam_shift (pre per suf : Layers) (k m i : ℕ) (hi : pre.length ≤ i) :
    (fam pre per suf (k + m))[i + m * per.length]? = (fam pre per suf k)[i]? := by
  have h1 : fam pre per suf (k + m) =
      (pre ++ (List.replicate m per).flatten) ++ ((List.replicate k per).flatten ++ suf) := by
    rw [fam, Nat.add_comm k m, List.replicate_add, List.flatten_append]
    simp only [List.append_assoc]
  have hl : (pre ++ (List.replicate m per).flatten).length ≤ i + m * per.length := by
    simp only [List.length_append, len_flat]; omega
  rw [h1, fam_eq, List.getElem?_append_right hl, List.getElem?_append_right hi]
  congr 1
  simp only [List.length_append, len_flat]; omega

private lemma lay_eq {L M : Layers} {i j : ℕ} (h : L[i]? = M[j]?) : L.lay i = M.lay j := by
  simp only [Layers.lay, List.getD_eq_getElem?_getD, h]

private lemma win_of {L M : Layers} {ℓ ℓ' : ℕ} (h0 : ℓ = 0 ↔ ℓ' = 0)
    (hl : ∀ i i', ℓ = i + 1 → ℓ' = i' + 1 → L[i]? = M[i']?)
    (h1 : L[ℓ]? = M[ℓ']?) (h2 : L[ℓ + 1]? = M[ℓ' + 1]?) :
    L.lft ℓ = M.lft ℓ' ∧ L.lay ℓ = M.lay ℓ' ∧ L.lay (ℓ + 1) = M.lay (ℓ' + 1) := by
  refine ⟨?_, lay_eq h1, lay_eq h2⟩
  rcases ℓ with _ | i <;> rcases ℓ' with _ | i'
  · rfl
  · simp at h0
  · simp at h0
  · simp only [Layers.lft, List.getD_cons_succ]
    exact lay_eq (hl i i' rfl rfl)

private lemma len_fam (pre per suf : Layers) (k : ℕ) :
    (fam pre per suf k).length = pre.length + k * per.length + suf.length := by
  simp only [fam, List.length_append, len_flat]

/-- Removing one period (`k ≥ 2`, `per.length ≥ 2`). -/
private lemma window_step {pre per suf : Layers} (hper : 2 ≤ per.length) (k ℓ : ℕ)
    (hk : 2 ≤ k) (hℓ : ℓ < (fam pre per suf (k + 1)).length) :
    ∃ ℓ', ℓ' < (fam pre per suf k).length ∧
      (fam pre per suf (k + 1)).lft ℓ = (fam pre per suf k).lft ℓ' ∧
      (fam pre per suf (k + 1)).lay ℓ = (fam pre per suf k).lay ℓ' ∧
      (fam pre per suf (k + 1)).lay (ℓ + 1) = (fam pre per suf k).lay (ℓ' + 1) := by
  rw [len_fam] at hℓ
  have hkn : 2 * per.length ≤ k * per.length := Nat.mul_le_mul_right _ hk
  by_cases hc : ℓ + 1 < pre.length + k * per.length
  · refine ⟨ℓ, by rw [len_fam]; omega, win_of Iff.rfl ?_ ?_ ?_⟩
    · intro i i' hi hi'
      have : i = i' := by omega
      subst this
      exact fam_prefix pre per suf k 1 i (by omega)
    · exact fam_prefix pre per suf k 1 ℓ (by omega)
    · exact fam_prefix pre per suf k 1 (ℓ + 1) (by omega)
  · refine ⟨ℓ - per.length, ?_, win_of ?_ ?_ ?_ ?_⟩
    · rw [len_fam]
      have : (k + 1) * per.length = k * per.length + per.length := Nat.succ_mul _ _
      omega
    · omega
    · intro i i' hi hi'
      have := fam_shift pre per suf k 1 i' (by omega)
      rw [one_mul] at this
      rw [show i = i' + per.length by omega, this]
    · have := fam_shift pre per suf k 1 (ℓ - per.length) (by omega)
      rw [one_mul, Nat.sub_add_cancel (by omega)] at this
      exact this
    · have := fam_shift pre per suf k 1 (ℓ - per.length + 1) (by omega)
      rw [one_mul, show ℓ - per.length + 1 + per.length = ℓ + 1 by omega] at this
      exact this

/-- Every window of the `(p+2)`-period family is a window of the `2`-period family
(requires a period of length at least `2`; see `window_reduce_counterexample`). -/
theorem window_reduce {pre per suf : Layers} (hper : 2 ≤ per.length) (p ℓ : ℕ)
    (hℓ : ℓ < (fam pre per suf (p + 2)).length) :
    ∃ ℓ', ℓ' < (fam pre per suf 2).length ∧
      (fam pre per suf (p + 2)).lft ℓ = (fam pre per suf 2).lft ℓ' ∧
      (fam pre per suf (p + 2)).lay ℓ = (fam pre per suf 2).lay ℓ' ∧
      (fam pre per suf (p + 2)).lay (ℓ + 1) = (fam pre per suf 2).lay (ℓ' + 1) := by
  induction p generalizing ℓ with
  | zero => exact ⟨ℓ, hℓ, rfl, rfl, rfl⟩
  | succ p ih =>
    rw [show p + 1 + 2 = (p + 2) + 1 by omega] at hℓ ⊢
    obtain ⟨ℓ₁, hℓ₁, a1, a2, a3⟩ := window_step hper (p + 2) ℓ (by omega) hℓ
    obtain ⟨ℓ', hℓ', b1, b2, b3⟩ := ih ℓ₁ hℓ₁
    exact ⟨ℓ', hℓ', a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- The hypothesis `2 ≤ per.length` of `window_reduce` cannot be weakened to `per ≠ []`. -/
theorem window_reduce_counterexample :
    ¬ ∃ ℓ', ℓ' < (fam [] [[1]] [] 2).length ∧
      (fam [] [[1]] [] (1 + 2)).lft 1 = (fam [] [[1]] [] 2).lft ℓ' ∧
      (fam [] [[1]] [] (1 + 2)).lay 1 = (fam [] [[1]] [] 2).lay ℓ' ∧
      (fam [] [[1]] [] (1 + 2)).lay (1 + 1) = (fam [] [[1]] [] 2).lay (ℓ' + 1) := by
  decide

/-- Windows well inside a common prefix agree. -/
private theorem lift_win_prefix (A X Y : Layers) (ℓ : ℕ) (h : ℓ + 1 < A.length) :
    (A ++ X).lft ℓ = (A ++ Y).lft ℓ ∧ (A ++ X).lay ℓ = (A ++ Y).lay ℓ ∧
      (A ++ X).lay (ℓ + 1) = (A ++ Y).lay (ℓ + 1) := by
  simp only [Layers.lft, Layers.lay]
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.cons_append, ← List.cons_append,
      List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

/-- Windows inside a common suffix (not at its first layer) agree. -/
private theorem lift_win_suffix (X Y C : Layers) (j : ℕ) (hj : 1 ≤ j) :
    (X ++ C).lft (X.length + j) = (Y ++ C).lft (Y.length + j) ∧
      (X ++ C).lay (X.length + j) = (Y ++ C).lay (Y.length + j) ∧
      (X ++ C).lay (X.length + j + 1) = (Y ++ C).lay (Y.length + j + 1) := by
  simp only [Layers.lft, Layers.lay]
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.cons_append, ← List.cons_append,
      List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1; simp; omega
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega

/-- Every window of the `2`-period family is a window of the `(p+2)`-period family. -/
theorem window_lift {pre per suf : Layers} (hper : per ≠ []) (p ℓ' : ℕ)
    (hℓ' : ℓ' < (fam pre per suf 2).length) :
    ∃ ℓ, ℓ < (fam pre per suf (p + 2)).length ∧
      (fam pre per suf (p + 2)).lft ℓ = (fam pre per suf 2).lft ℓ' ∧
      (fam pre per suf (p + 2)).lay ℓ = (fam pre per suf 2).lay ℓ' ∧
      (fam pre per suf (p + 2)).lay (ℓ + 1) = (fam pre per suf 2).lay (ℓ' + 1) := by
  have hpl : 0 < per.length := List.length_pos_iff.mpr hper
  have e2 : fam pre per suf 2 = (pre ++ per ++ per) ++ suf := by
    simp [fam, List.replicate_succ, List.append_assoc]
  have e2' : fam pre per suf 2 = pre ++ (per ++ per ++ suf) := by
    simp [fam, List.replicate_succ, List.append_assoc]
  have ep : fam pre per suf (p + 2) =
      (pre ++ per ++ per) ++ ((List.replicate p per).flatten ++ suf) := by
    simp only [fam, List.replicate_succ, List.flatten_cons, List.append_assoc]
  have ep' : fam pre per suf (p + 2) =
      (pre ++ (List.replicate p per).flatten) ++ (per ++ per ++ suf) := by
    rw [fam, List.replicate_add]
    simp only [List.flatten_append, List.replicate_succ, List.replicate_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
  have hlen2 : (fam pre per suf 2).length =
      pre.length + per.length + per.length + suf.length := by
    rw [e2]; simp only [List.length_append]
  rw [hlen2] at hℓ'
  by_cases hc : ℓ' < pre.length + per.length
  · refine ⟨ℓ', ?_, ?_⟩
    · rw [ep]; simp only [List.length_append]; omega
    · rw [ep, e2]
      exact lift_win_prefix _ _ _ ℓ' (by simp only [List.length_append]; omega)
  · obtain ⟨j, rfl⟩ : ∃ j, ℓ' = pre.length + j := ⟨ℓ' - pre.length, by omega⟩
    refine ⟨(pre ++ (List.replicate p per).flatten).length + j, ?_, ?_⟩
    · rw [ep']; simp only [List.length_append] at hℓ' ⊢; omega
    · rw [ep', e2']
      exact lift_win_suffix _ pre (per ++ per ++ suf) j (by omega)

theorem allWin_fam {Q : List ℕ → List ℕ → List ℕ → Prop} {pre per suf : Layers}
    (hper : 2 ≤ per.length) (h : AllWin Q (fam pre per suf 2)) (p : ℕ) :
    AllWin Q (fam pre per suf (p + 2)) := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', h1, h2, h3⟩ := window_reduce hper p ℓ hℓ
  rw [h1, h2, h3]; exact h ℓ' hℓ'

theorem someWin_fam {Q : List ℕ → List ℕ → List ℕ → Prop} {pre per suf : Layers}
    (hper : per ≠ []) (h : SomeWin Q (fam pre per suf 2)) (p : ℕ) :
    SomeWin Q (fam pre per suf (p + 2)) := by
  obtain ⟨ℓ', hℓ', hQ⟩ := h
  obtain ⟨ℓ, hℓ, h1, h2, h3⟩ := window_lift hper p ℓ' hℓ'
  exact ⟨ℓ, hℓ, by rw [h1, h2, h3]; exact hQ⟩

end Erdos612
