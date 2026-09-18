import ErdosLean.Erdos1199.Defs

/-!
# Erdős #1199 — Part 7: a finitely-determined `J`-odd separating function

Replaces Lemma 2.9 (clopen fundamental domain) of arXiv:2607.17333: since `J` acts on every
finite coordinate projection `Bool^F` without fixed points, the fundamental domain can be built
on `Bool^F` directly.
-/

namespace Erdos1199

open Filter

/-- If `M` is closed and `J y ∉ M` for all `y ∈ M`, there is `G : Pt → Bool` depending only on
finitely many coordinates, with `G (J u) = ¬ G u` for every `u`, and `G ≡ true` on `M`.
(`H = G⁻¹(true)` is then a clopen set with `Pt = H ⊔ J H` and `M ⊆ H`.) -/
theorem finite_separation (M : Set Pt) (hM : IsClosed M) (hdisj : ∀ y ∈ M, cmpl y ∉ M) :
    ∃ (G : Pt → Bool) (F : Finset Idx),
      (∀ u v : Pt, (∀ i ∈ F, u i = v i) → G u = G v) ∧
      (∀ u : Pt, G (cmpl u) = !(G u)) ∧
      (∀ y ∈ M, G y = true) := by
  classical
  have hMc : IsCompact M := hM.isCompact
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset Idx, ∀ y ∈ M, ∀ z ∈ M, ∃ i ∈ F₀, y i = z i := by
    have hK : IsCompact (M ×ˢ M) := hMc.prod hMc
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : Idx => {p : Pt × Pt | p.1 i = p.2 i})
      (fun i => (isOpen_discrete {q : Bool × Bool | q.1 = q.2}).preimage
        (by fun_prop : Continuous fun p : Pt × Pt => (p.1 i, p.2 i)))
      (by
        rintro ⟨y, z⟩ ⟨hy, hz⟩
        by_contra h
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at h
        apply hdisj z hz
        have hyz : y = cmpl z := funext fun i => by
          have hi := h i
          simp only [cmpl]
          cases hyi : y i <;> cases hzi : z i <;> simp_all
        exact hyz ▸ hy)
    refine ⟨t, fun y hy z hz => ?_⟩
    have hmem := ht (Set.mk_mem_prod hy hz)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
    obtain ⟨i, hi, h⟩ := hmem
    exact ⟨i, hi, h⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Pt → Prop, A = fun u => ∃ y ∈ M, ∀ i ∈ F₀, y i = u i := ⟨_, rfl⟩
  let i₀ : Idx := (0, 0)
  have hcc : ∀ u, cmpl (cmpl u) = u := fun u => funext fun i => by simp [cmpl]
  have hexcl : ∀ u, A u → ¬ A (cmpl u) := by
    intro u h1 h2
    rw [hAdef] at h1 h2
    obtain ⟨y, hy, hyu⟩ := h1
    obtain ⟨y', hy', hyu'⟩ := h2
    obtain ⟨i, hi, h⟩ := hF₀ y hy y' hy'
    have e1 := hyu i hi
    have e2 := hyu' i hi
    simp only [cmpl] at e2
    rw [e1, e2] at h
    cases u i <;> simp at h
  have hAcongr : ∀ u v : Pt, (∀ i ∈ F₀, u i = v i) → (A u ↔ A v) := by
    intro u v huv
    rw [hAdef]
    refine exists_congr fun y => and_congr_right fun _ => forall₂_congr fun i hi => ?_
    rw [huv i hi]
  refine ⟨fun u => if A u then true else if A (cmpl u) then false else u i₀,
    insert i₀ F₀, ?_, ?_, ?_⟩
  · intro u v huv
    have hA : A u ↔ A v := hAcongr u v fun i hi => huv i (Finset.mem_insert_of_mem hi)
    have hA' : A (cmpl u) ↔ A (cmpl v) := hAcongr _ _ fun i hi => by
      simp only [cmpl]; rw [huv i (Finset.mem_insert_of_mem hi)]
    have h0 : u i₀ = v i₀ := huv i₀ (Finset.mem_insert_self _ _)
    simp only [hA, hA', h0]
  · intro u
    simp only [hcc]
    by_cases h1 : A u
    · simp [h1, hexcl u h1]
    · by_cases h2 : A (cmpl u)
      · simp [h1, h2]
      · simp [h1, h2, cmpl]
  · intro y hy
    have : A y := by rw [hAdef]; exact ⟨y, hy, fun _ _ => rfl⟩
    simp [this]

end Erdos1199
