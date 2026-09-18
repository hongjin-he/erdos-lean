import ErdosLean.Erdos1199.Parts.ActLaws

/-!
# Erdős #1199 — Part 6: `M ∩ J M = ∅`

Paper: arXiv:2607.17333, Proposition 3.6.  Stated abstractly: only `Δ₂ x = x` and the key
identity (Proposition 3.2) are used.
-/

namespace Erdos1199

open Filter

/-- Proposition 3.6: if `Δ₂ x = x` and `(p+p) x = J((D p) x)` for all `p ∈ ℕ*`, then no
minimal subsystem `M ⊆ ω(x)` meets its image `J M`. -/
theorem disjoint_minimal (x : Pt) (hdil : dil x = x)
    (hkey : ∀ p : Ultrafilter ℕ, Nonprincipal p → act (p + p) x = cmpl (act (dbl p) x))
    (M : Set Pt) (hM : IsMinimalSub x M) :
    ∀ y ∈ M, cmpl y ∉ M := by
  intro y₀ hy₀ hJy₀
  obtain ⟨_, hMcl, hMΩ, hMinv, hMreach⟩ := hM
  -- Step 1: the compact subsemigroup `I = {p ∈ ℕ* | p x ∈ M}` and an idempotent in it.
  set I : Set (Ultrafilter ℕ) := {p | Nonprincipal p} ∩ (fun p => act p x) ⁻¹' M with hI
  have hIcl : IsClosed I :=
    isClosed_nonprincipal.inter (hMcl.preimage (continuous_act x))
  have hIne : I.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hMΩ hy₀
    exact ⟨p, hp, by simp [hpx, hy₀]⟩
  have hIadd : ∀ a ∈ I, ∀ b ∈ I, a + b ∈ I := by
    intro a ha b hb
    refine ⟨nonprincipal_add hb.1, ?_⟩
    show act (a + b) x ∈ M
    rw [act_add]
    exact hMinv a _ hb.2
  obtain ⟨e, heI, hee⟩ := exists_idempotent_in_compact_add_subsemigroup
    continuous_add_const I hIne hIcl.isCompact hIadd
  -- Step 2
  set y := act e x with hy
  have hyM : y ∈ M := heI.2
  have hDe : act (dbl e) x = cmpl y := by
    have h := hkey e heI.1
    rw [hee] at h
    rw [hy, h, cmpl_cmpl]
  -- Step 3
  obtain ⟨q₁, hq₁⟩ := hMreach y₀ hy₀ y hyM
  have hJyM : cmpl y ∈ M := by
    have := hMinv q₁ _ hJy₀
    rwa [act_cmpl, hq₁] at this
  obtain ⟨s, hs⟩ := hMreach y hyM (cmpl y) hJyM
  -- Step 4
  have hq : Nonprincipal (s + e) := nonprincipal_add heI.1
  have hqx : act (s + e) x = cmpl y := by rw [act_add, ← hy, hs]
  have hey : act e y = y := by rw [hy, ← act_add, hee]
  have hqq : act ((s + e) + (s + e)) x = y := by
    rw [act_add, hqx, act_add, act_cmpl, hey, act_cmpl, hs, cmpl_cmpl]
  -- Step 5
  have hdily : dil y = cmpl y := by rw [hy, dil_act, hdil, hDe]
  have hDq : act (dbl (s + e)) x = y := by
    conv_lhs => rw [← hdil]
    rw [← dil_act, hqx, dil_cmpl, hdily, cmpl_cmpl]
  -- Step 6
  have h := hkey (s + e) hq
  rw [hqq, hDq] at h
  exact cmpl_ne_self y h.symm

end Erdos1199
