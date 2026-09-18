import Mathlib

/-! # Erdős #514 — Part: a path running through a nested chain of domains

Pick `pₙ ∈ D n`; `D n` is open and connected, hence path-connected
(`IsOpen.isConnected_iff_isPathConnected`), and `p_{n+1} ∈ D (n+1) ⊆ D n`, so there is a
path `σₙ` in `D n` from `pₙ` to `p_{n+1}`.  Define `γ t = σ_{⌊t⌋}(t - ⌊t⌋)` for `t ≥ 0`
and `γ t = p₀` for `t ≤ 0`; it is continuous (the pieces agree at integers), and for
`t ≥ n`, `γ t ∈ D ⌊t⌋ ⊆ D n`. -/

namespace Erdos514

theorem path_through_nested (D : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsPreconnected (D n)) (hne : ∀ n, (D n).Nonempty)
    (hsub : ∀ n, D (n + 1) ⊆ D n) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ ∀ n : ℕ, ∀ t : ℝ, (n : ℝ) ≤ t → γ t ∈ D n := by
  have hpc : ∀ n, IsPathConnected (D n) := fun n =>
    (hopen n).isConnected_iff_isPathConnected.mp ⟨hne n, hconn n⟩
  choose p hp using hne
  have hanti : Antitone D := antitone_nat_of_succ_le hsub
  have hj : ∀ n, JoinedIn (D n) (p n) (p (n+1)) := fun n =>
    (hpc n).joinedIn _ (hp n) _ (hsub n (hp (n+1)))
  let σ : ∀ n, Path (p n) (p (n+1)) := fun n => (hj n).somePath
  have hσ : ∀ n (t : unitInterval), σ n t ∈ D n := fun n t => (hj n).somePath_mem t
  let γ : ℝ → ℂ := fun t => (σ ⌊t⌋₊).extend (t - ⌊t⌋₊)
  have hγ : ∀ (m : ℕ) (t : ℝ), ⌊t⌋₊ = m → γ t = (σ m).extend (t - m) := by
    intro m t h; subst h; rfl
  have hc : ∀ m : ℕ, Continuous (fun t : ℝ => (σ m).extend (t - m)) := fun m =>
    (σ m).continuous_extend.comp (continuous_id.sub continuous_const)
  refine ⟨γ, ?_, ?_⟩
  · have hlf : LocallyFinite (fun n : ℕ => Set.Icc (n:ℝ) (n+1)) := by
      intro x
      refine ⟨Set.Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      apply (Set.finite_le_nat ⌈x+1⌉₊).subset
      rintro n ⟨y, ⟨h1, h2⟩, h3, h4⟩
      simp only [Set.mem_ofPred_eq]
      have : (n:ℝ) ≤ ⌈x+1⌉₊ := by linarith [Nat.le_ceil (x+1)]
      exact_mod_cast this
    refine (hlf.option_elim' (Set.Iic 0)).continuous ?_ ?_ ?_
    · refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ?_
      by_cases ht : t ≤ 0
      · exact ⟨none, ht⟩
      · push Not at ht
        exact ⟨some ⌊t⌋₊, Nat.floor_le ht.le, (Nat.lt_floor_add_one t).le⟩
    · rintro (_ | n)
      · exact isClosed_Iic
      · exact isClosed_Icc
    · rintro (_ | n)
      · refine (hc 0).continuousOn.congr
          (fun t (ht : t ≤ 0) => ?_)
        rw [hγ 0 t (Nat.floor_of_nonpos ht)]
      · refine (hc n).continuousOn.congr
          (fun t (ht : t ∈ Set.Icc (n:ℝ) (n+1)) => ?_)
        rcases ht with ⟨h1, h2⟩
        rcases h2.lt_or_eq with h2 | h2
        · rw [hγ n t ((Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])).2 ⟨h1, h2⟩)]
        · have hf : ⌊t⌋₊ = n + 1 := by
            rw [h2]; exact_mod_cast Nat.floor_natCast (R := ℝ) (n+1)
          rw [hγ (n+1) t hf]
          rw [h2]
          push_cast
          simp
  · intro n t ht
    exact hanti (Nat.le_floor ht) (hσ _ _)

end Erdos514
