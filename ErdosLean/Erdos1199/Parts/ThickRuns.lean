import ErdosLean.Erdos1199.Parts.ActLaws

/-!
# Erdős #1199 — Part 9: the coded colouring has a thick colour class

Paper: arXiv:2607.17333, last assertion of Lemma 2.10 and Proposition 3.7(ii).
-/

namespace Erdos1199

open Filter

/-- If `G ≡ true` on a minimal subsystem `M ⊆ ω(x)` and `h n = G (Tⁿ x)` codes `G` along
ultrafilters, then `h` has arbitrarily long runs of `true` arbitrarily far to the right. -/
theorem thick_of_minimal (x : Pt) (M : Set Pt) (hM : IsMinimalSub x M) (G : Pt → Bool)
    (hG : ∀ y ∈ M, G y = true)
    (hcode : ∀ q : Ultrafilter ℕ,
      {n : ℕ | G (act (pure n) x) = true} ∈ q ↔ G (act q x) = true) :
    ∀ L N : ℕ, ∃ n, N ≤ n ∧ ∀ j ≤ L, G (act (pure (n + j)) x) = true := by
  intro L N
  obtain ⟨y, hyM⟩ := hM.1
  obtain ⟨p, hp, rfl⟩ := hM.2.2.1 hyM
  have hj : ∀ j : ℕ, {m : ℕ | G (act (pure (m + j)) x) = true} ∈ p := by
    intro j
    have h1 : G (act (pure j + p) x) = true := by
      rw [act_add]; exact hG _ (hM.2.2.2.1 _ _ hyM)
    have h2 := (hcode (pure j + p)).2 h1
    rw [mem_add_iff, Ultrafilter.mem_pure] at h2
    simpa [Nat.add_comm] using h2
  have hall : (⋂ j ∈ Finset.range (L + 1), {m : ℕ | G (act (pure (m + j)) x) = true}) ∈ p :=
    (Filter.biInter_finset_mem _).2 fun j _ => hj j
  obtain ⟨n, hn, hNn⟩ := hp.exists_ge hall N
  refine ⟨n, hNn, fun j hjL => ?_⟩
  simp only [Set.mem_iInter, Finset.mem_range] at hn
  exact hn j (by omega)

end Erdos1199
