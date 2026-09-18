import ErdosLean.Erdos1199.Parts.ActLaws

/-!
# Erdős #1199 — Part 5: existence of a minimal subsystem of `ω(x)`

Paper: arXiv:2607.17333, §2.1 (Zorn) and Lemma 2.8 (`ω(x) = ℕ* x`).
-/

namespace Erdos1199

open Filter

/-- `ω(x)` is closed. -/
theorem isClosed_omega (x : Pt) : IsClosed (Omega x) := by
  have hc : IsCompact {p : Ultrafilter ℕ | Nonprincipal p} :=
    isClosed_nonprincipal.isCompact
  have : Omega x = (fun p : Ultrafilter ℕ => act p x) '' {p | Nonprincipal p} := by
    ext y; simp [Omega]
  rw [this]
  exact (hc.image (continuous_act x)).isClosed

/-- `ω(x)` is nonempty. -/
theorem omega_nonempty (x : Pt) : (Omega x).Nonempty := by
  obtain ⟨p, hp, -⟩ := exists_nonprincipal_mem (Set.infinite_univ (α := ℕ))
  exact ⟨act p x, p, hp, rfl⟩

/-- `ω(x)` is invariant. -/
theorem omega_invariant (x : Pt) (p : Ultrafilter ℕ) {y : Pt} (hy : y ∈ Omega x) :
    act p y ∈ Omega x := by
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨p + q, nonprincipal_add hq, act_add p q x⟩

/-- Every `ω(x)` contains a minimal subsystem (in the sense of `IsMinimalSub`). -/
theorem exists_minimal (x : Pt) : ∃ M : Set Pt, IsMinimalSub x M := by
  let S : Set (Set Pt) := {K | K.Nonempty ∧ IsClosed K ∧ K ⊆ Omega x ∧
    ∀ p : Ultrafilter ℕ, ∀ y ∈ K, act p y ∈ K}
  have hΩ : Omega x ∈ S :=
    ⟨omega_nonempty x, isClosed_omega x, le_rfl, fun p y hy => omega_invariant x p hy⟩
  obtain ⟨M, -, hM⟩ := zorn_superset_nonempty S (by
    intro c hcS hchain hcne
    have : Nonempty c := hcne.to_subtype
    refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun a ha b hb => (hchain.total ha hb).elim
          (fun h => ⟨a, ha, subset_rfl, h⟩) (fun h => ⟨b, hb, h, subset_rfl⟩)) (fun U hU => (hcS hU).1)
        (fun U hU => (hcS hU).2.1.isCompact) (fun U hU => (hcS hU).2.1)
    · exact isClosed_sInter fun U hU => (hcS hU).2.1
    · obtain ⟨U, hU⟩ := hcne
      exact (Set.sInter_subset_of_mem hU).trans (hcS hU).2.2.1
    · intro p y hy
      exact Set.mem_sInter.2 fun U hU => (hcS hU).2.2.2 p y (Set.mem_sInter.1 hy U hU))
    (Omega x) hΩ
  obtain ⟨hne, hcl, hsub, hinv⟩ := hM.prop
  refine ⟨M, hne, hcl, hsub, hinv, ?_⟩
  intro y hy z hz
  let K : Set Pt := Set.range fun q : Ultrafilter ℕ => act q y
  have hKM : K ⊆ M := by
    rintro _ ⟨q, rfl⟩; exact hinv q y hy
  have hKS : K ∈ S := by
    refine ⟨⟨y, ?_⟩, ?_, hKM.trans hsub, ?_⟩
    · -- `y = act (pure 0) y`
      refine ⟨pure 0, ?_⟩
      funext i
      show act (pure 0) y i = y i
      rw [act_pure_apply]
      simp
    · exact (isCompact_range (continuous_act y)).isClosed
    · rintro p _ ⟨q, rfl⟩
      exact ⟨p + q, act_add p q y⟩
  have hMK : M ⊆ K := hM.2 hKS hKM
  obtain ⟨q, hq⟩ := hMK hz
  exact ⟨q, hq⟩

end Erdos1199
