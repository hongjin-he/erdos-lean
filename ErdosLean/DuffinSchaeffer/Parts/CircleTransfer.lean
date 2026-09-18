import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 2: from `ℝ/ℤ` to `ℝ`

Mathlib's Gallagher 0-1 law (`AddCircle.addWellApproximable_ae_empty_or_univ`)
lives on the circle; our statement lives on `ℝ`.
-/

open MeasureTheory Filter

namespace DuffinSchaeffer

/-- `limsup_{q→∞} A_q = addWellApproximable (ℝ/ℤ) (q ↦ ψ(q)/q)` (the `blimsup` over `0 < n` in
Mathlib's definition agrees with the plain `limsup` since `0 < n` eventually). -/
theorem limsup_Aq_eq (ψ : ℕ → ℝ) :
    limsup (Aq ψ) atTop = addWellApproximable UnitAddCircle (fun n => ψ n / n) := by
  unfold addWellApproximable
  rw [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq, cofinite.blimsup_set_eq]
  ext x
  simp only [Set.mem_ofPred_eq]
  have hsub1 : {n | 0 < n ∧ x ∈ approxAddOrderOf UnitAddCircle n (ψ n / n)} ⊆
      {n | x ∈ Aq ψ n} := fun n hn => hn.2
  have hsub2 : {n | x ∈ Aq ψ n} ⊆
      insert 0 {n | 0 < n ∧ x ∈ approxAddOrderOf UnitAddCircle n (ψ n / n)} := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hn⟩
  constructor
  · intro h
    by_contra hfin
    exact h ((Set.not_infinite.1 hfin).insert 0 |>.subset hsub2)
  · intro h
    exact h.mono hsub1

/-- Monotonicity of `addWellApproximable` in the radii. -/
theorem addWellApproximable_mono {δ δ' : ℕ → ℝ} (h : ∀ n, δ n ≤ δ' n) :
    addWellApproximable UnitAddCircle δ ⊆ addWellApproximable UnitAddCircle δ' := by
  intro x hx
  rw [UnitAddCircle.mem_addWellApproximable_iff] at hx ⊢
  apply hx.mono
  rintro q ⟨p, hpq, hcop, hdist⟩
  exact ⟨p, hpq, hcop, hdist.trans_le (h q)⟩

/-- If a.e. point of the circle is `ψ(q)/q`-well approximable, then a.e. real `α` has infinitely
many reduced solutions `(a, q)` of `|α - a/q| < ψ(q)/q`. -/
theorem ae_solutions_of_ae_circle (ψ : ℕ → ℝ)
    (h : ∀ᵐ x : UnitAddCircle, x ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n)) :
    ∀ᵐ α : ℝ, (solutions ψ α).Infinite := by
  -- pointwise statement
  have hpt : ∀ α : ℝ, ((α : UnitAddCircle) ∈
      addWellApproximable UnitAddCircle (fun n => ψ n / n)) → (solutions ψ α).Infinite := by
    intro α hα
    rw [UnitAddCircle.mem_addWellApproximable_iff] at hα
    by_contra hfin
    rw [Set.not_infinite] at hfin
    apply hα
    refine (hfin.image Prod.snd).subset ?_
    rintro q ⟨p, hpq, hcop, hdist⟩
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hpq
    set k : ℤ := round (α - (p : ℝ) / q) with hk
    refine ⟨((p : ℤ) + k * q, q), ⟨hq, ?_, ?_⟩, rfl⟩
    · -- gcd
      have h1 : Int.gcd ((p : ℤ) + k * q) (q : ℤ) = Int.gcd (p : ℤ) (q : ℤ) := by
        simp
      simp only
      rw [h1, Int.gcd_natCast_natCast]
      exact hcop
    · have hn : ‖((α - (p : ℝ) / q : ℝ) : UnitAddCircle)‖ < ψ q / q := by
        simpa [AddCircle.coe_sub] using hdist
      rw [UnitAddCircle.norm_eq] at hn
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have : α - ((((p : ℤ) + k * q : ℤ) : ℝ) / ((q : ℕ) : ℝ)) =
          α - (p : ℝ) / q - (k : ℝ) := by
        push_cast
        field_simp
        ring
      simp only
      rw [this]
      exact hn
  -- transfer the a.e. statement
  have hloc : ∀ n : ℤ, ∀ᵐ (α : ℝ) ∂(volume.restrict (Set.Ioc (n : ℝ) (n + 1))),
      (α : UnitAddCircle) ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    fun n => (AddCircle.measurePreserving_mk (1 : ℝ) (n : ℝ)).quasiMeasurePreserving.ae h
  have hall : ∀ᵐ (α : ℝ) ∂(volume.restrict (⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1))),
      (α : UnitAddCircle) ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    (ae_restrict_iUnion_iff _ _).2 hloc
  have hU : (⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1)) = Set.univ := by
    simpa [zero_add] using iUnion_Ioc_add_intCast (0 : ℝ)
  rw [hU, Measure.restrict_univ] at hall
  exact hall.mono fun α hα => hpt α hα


end DuffinSchaeffer
