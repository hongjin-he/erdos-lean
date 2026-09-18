import Mathlib

/-!
# Erdős #1199 — Part 11: infinite Ramsey theorem for pairs (finitely many colours)

Used in Appendix A of arXiv:2607.17333 (Graham–Rothschild–Spencer, Ch. 1, Thm 5).

Proof via a nonprincipal ultrafilter `U ∋ S`: each `i` has a `U`-typical colour `c i`,
some colour `k` is `U`-typical for `c`, and we pick the sequence greedily inside a
decreasing chain of `U`-large sets.
-/

namespace Erdos1199

open Filter

/-- Infinite Ramsey for pairs: any finite colouring `χ` of pairs `i < j` of an infinite set
`S ⊆ ℕ` has an infinite homogeneous subsequence. -/
theorem ramsey_pairs {κ : Type*} [Finite κ] (χ : ℕ → ℕ → κ) (S : Set ℕ) (hS : S.Infinite) :
    ∃ (k : κ) (u : ℕ → ℕ), StrictMono u ∧ (∀ i, u i ∈ S) ∧
      ∀ i j, i < j → χ (u i) (u j) = k := by
  have := hS.cofinite_inf_principal_neBot
  let U : Ultrafilter ℕ := Ultrafilter.of (cofinite ⊓ 𝓟 S)
  have hUle : (U : Filter ℕ) ≤ cofinite ⊓ 𝓟 S := Ultrafilter.of_le _
  have hSU : S ∈ U := (le_trans hUle inf_le_right) (mem_principal_self S)
  have hIoi : ∀ n : ℕ, Set.Ioi n ∈ U := fun n =>
    (le_trans hUle inf_le_left) (Nat.cofinite_eq_atTop ▸ Ioi_mem_atTop n)
  -- typical colour at each point
  have hc : ∀ i, ∃ a : κ, U.map (χ i) = pure a := fun i => Ultrafilter.eq_pure_of_finite _
  choose c hc using hc
  have hcU : ∀ i, {j | χ i j = c i} ∈ U := by
    intro i
    have : ({c i} : Set κ) ∈ U.map (χ i) := by rw [hc i]; exact Ultrafilter.mem_pure.2 rfl
    exact this
  obtain ⟨k, hk⟩ := Ultrafilter.eq_pure_of_finite (U.map c)
  have hA : {i | c i = k} ∈ U := by
    have : ({k} : Set κ) ∈ U.map c := by rw [hk]; exact Ultrafilter.mem_pure.2 rfl
    exact this
  let A : Set ℕ := S ∩ {i | c i = k}
  have hAU : A ∈ U := Filter.inter_mem hSU hA
  -- recursion on U-large subsets of A
  let T := {B : Set ℕ // B ∈ U ∧ B ⊆ A}
  have hne : ∀ B : T, B.1.Nonempty := fun B => Ultrafilter.nonempty_of_mem B.2.1
  let pick : T → ℕ := fun B => (hne B).some
  have hpick : ∀ B : T, pick B ∈ B.1 := fun B => (hne B).some_mem
  let step : T → T := fun B =>
    ⟨B.1 ∩ {j | χ (pick B) j = k} ∩ Set.Ioi (pick B), by
      refine ⟨Filter.inter_mem (Filter.inter_mem B.2.1 ?_) (hIoi _), fun x hx => B.2.2 hx.1.1⟩
      have hp : c (pick B) = k := (B.2.2 (hpick B)).2
      simpa [hp] using hcU (pick B)⟩
  let Bs : ℕ → T := fun n => step^[n] ⟨A, hAU, le_rfl⟩
  have hBs : ∀ n, Bs (n + 1) = step (Bs n) := fun n => by
    simp only [Bs]; rw [Function.iterate_succ_apply']
  let u : ℕ → ℕ := fun n => pick (Bs n)
  have hsub : ∀ m n, m ≤ n → (Bs n).1 ⊆ (Bs m).1 := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih =>
      rw [hBs]
      exact fun x hx => ih hx.1.1
  have key : ∀ i j, i < j → χ (u i) (u j) = k ∧ u i < u j := by
    intro i j hij
    have h1 : u j ∈ (Bs (i + 1)).1 := hsub _ _ hij (hpick _)
    rw [hBs] at h1
    exact ⟨h1.1.2, h1.2⟩
  refine ⟨k, u, fun i j hij => (key i j hij).2, fun i => ((Bs i).2.2 (hpick _)).1,
    fun i j hij => (key i j hij).1⟩

end Erdos1199

