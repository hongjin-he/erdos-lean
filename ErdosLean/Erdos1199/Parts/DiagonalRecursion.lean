import ErdosLean.Erdos1199.Parts.UltraBasics

/-!
# Erdős #1199 — Part 3: diagonal recursion

Paper: arXiv:2607.17333, Lemma 3.4.
-/

namespace Erdos1199

open Filter

/-- Lemma 3.4: if `A ∈ p + p` and `A ∈ D p` for a nonprincipal `p`, then there is a strictly
increasing sequence `v` with `v i + v j ∈ A` for all `i ≤ j`. -/
theorem diagonal_recursion {p : Ultrafilter ℕ} (hp : Nonprincipal p) {A : Set ℕ}
    (h1 : A ∈ p + p) (h2 : A ∈ dbl p) :
    ∃ v : ℕ → ℕ, StrictMono v ∧ ∀ i j, i ≤ j → v i + v j ∈ A := by
  classical
  set K : Set ℕ := {m : ℕ | {m' : ℕ | m + m' ∈ A} ∈ p} with hKdef
  set H : Set ℕ := {n : ℕ | 2 * n ∈ A} with hHdef
  have hK : K ∈ p := (mem_add_iff A p p).1 h1
  have hH : H ∈ p := (mem_dbl_iff A p).1 h2
  let E : Finset ℕ → Set ℕ := fun F =>
    H ∩ K ∩ ⋂ x ∈ F, {n : ℕ | x ∈ K → x + n ∈ A}
  have hE : ∀ F : Finset ℕ, E F ∈ p := by
    intro F
    refine Filter.inter_mem (Filter.inter_mem hH hK) ?_
    refine (Filter.biInter_finset_mem F).2 ?_
    intro x _
    by_cases hx : x ∈ K
    · exact Filter.mem_of_superset (show {m' : ℕ | x + m' ∈ A} ∈ p from hx)
        (fun n hn _ => hn)
    · exact Filter.mem_of_superset Filter.univ_mem (fun n _ h => absurd h hx)
  have hstep : ∀ F : Finset ℕ, ∃ n ∈ E F, F.sup id + 1 ≤ n :=
    fun F => hp.exists_ge (hE F) _
  choose f hfE hfle using hstep
  let g : ℕ → Finset ℕ := fun s => Nat.rec (∅ : Finset ℕ) (fun _ F => insert (f F) F) s
  have hg : ∀ s, g (s + 1) = insert (f (g s)) (g s) := fun s => rfl
  have hmem : ∀ i j, i < j → f (g i) ∈ g j := by
    intro i j hij
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j ih =>
      rw [hg]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact Finset.mem_insert_of_mem (ih h)
      · subst h; exact Finset.mem_insert_self _ _
  have hlt : ∀ i j, i < j → f (g i) < f (g j) := by
    intro i j hij
    have h1 : f (g i) ≤ (g j).sup id := Finset.le_sup (f := id) (hmem i j hij)
    have h2 := hfle (g j)
    omega
  refine ⟨fun s => f (g s), fun i j hij => hlt i j hij, ?_⟩
  intro i j hij
  rcases lt_or_eq_of_le hij with h | h
  · have hj := hfE (g j)
    have hi := hfE (g i)
    have hiK : f (g i) ∈ K := hi.1.2
    have := Set.mem_iInter₂.1 hj.2 (f (g i)) (hmem i j h)
    exact this hiK
  · subst h
    have hi := (hfE (g i)).1.1
    have : f (g i) + f (g i) = 2 * f (g i) := by ring
    simp only
    rw [this]
    exact hi

end Erdos1199
