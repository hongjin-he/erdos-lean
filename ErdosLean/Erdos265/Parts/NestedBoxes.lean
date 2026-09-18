import ErdosLean.Erdos265.Defs

/-!
# Erdős #265 — Part L4: nested boxes (abstract successive approximation)

Cf. the end of the proof of Theorem 2.8 in KT v4 §7.  Choose `c k` recursively so that the
remainder `ρ_n = x - ∑_{k<n} G k (c k) - ∑_{k≥n} s k` lies in the box `R_n = [-r1 n, r1 n] ×
[-r2 n, r2 n]`: at step `n` apply `hstep` to `δ = ρ_n`.  Since `r_n → 0` and the tails of
`∑ s` tend to `0`, the partial sums converge to `x`; nonnegativity upgrades this to `HasSum`.
-/

open Filter Topology

namespace Erdos265

theorem nested_boxes {ι : Type*} (G : ℕ → ι → ℝ × ℝ) (adm : ℕ → ι → Prop)
    (s : ℕ → ℝ × ℝ) (r1 r2 : ℕ → ℝ)
    (hs1 : Summable (fun k ↦ (s k).1)) (hs2 : Summable (fun k ↦ (s k).2))
    (hr1 : Tendsto r1 atTop (𝓝 0)) (hr2 : Tendsto r2 atTop (𝓝 0))
    (hG : ∀ k i, adm k i → 0 ≤ (G k i).1 ∧ 0 ≤ (G k i).2)
    (hstep : ∀ k (δ : ℝ × ℝ), |δ.1| ≤ r1 k → |δ.2| ≤ r2 k →
      ∃ i, adm k i ∧ |(s k).1 + δ.1 - (G k i).1| ≤ r1 (k + 1) ∧
        |(s k).2 + δ.2 - (G k i).2| ≤ r2 (k + 1))
    (x : ℝ × ℝ) (hx1 : |x.1 - ∑' k, (s k).1| ≤ r1 0) (hx2 : |x.2 - ∑' k, (s k).2| ≤ r2 0) :
    ∃ c : ℕ → ι, (∀ k, adm k (c k)) ∧ HasSum (fun k ↦ (G k (c k)).1) x.1 ∧
      HasSum (fun k ↦ (G k (c k)).2) x.2 := by
  classical
  set ρ0 : ℝ × ℝ := (x.1 - ∑' k, (s k).1, x.2 - ∑' k, (s k).2) with hρ0
  obtain ⟨i0, -⟩ := hstep 0 ρ0 hx1 hx2
  let g : ℕ → ℝ × ℝ → ι := fun k δ =>
    if h : |δ.1| ≤ r1 k ∧ |δ.2| ≤ r2 k then Classical.choose (hstep k δ h.1 h.2) else i0
  have hg : ∀ k (δ : ℝ × ℝ), |δ.1| ≤ r1 k ∧ |δ.2| ≤ r2 k →
      adm k (g k δ) ∧ |(s k).1 + δ.1 - (G k (g k δ)).1| ≤ r1 (k + 1) ∧
        |(s k).2 + δ.2 - (G k (g k δ)).2| ≤ r2 (k + 1) := by
    intro k δ h
    simp only [g, h, and_self, dite_true]
    exact Classical.choose_spec (hstep k δ h.1 h.2)
  let ρ : ℕ → ℝ × ℝ := fun n =>
    Nat.rec (motive := fun _ => ℝ × ℝ) ρ0 (fun k δ => s k + δ - G k (g k δ)) n
  have hρs : ∀ n, ρ (n + 1) = s n + ρ n - G n (g n (ρ n)) := fun n => rfl
  have box : ∀ n, |(ρ n).1| ≤ r1 n ∧ |(ρ n).2| ≤ r2 n := by
    intro n
    induction n with
    | zero => exact ⟨hx1, hx2⟩
    | succ n ih =>
      obtain ⟨-, h1, h2⟩ := hg n (ρ n) ih
      rw [hρs]
      simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add]
      exact ⟨h1, h2⟩
  have tele : ∀ n, (∑ k ∈ Finset.range n, (G k (g k (ρ k))).1 =
        ∑ k ∈ Finset.range n, (s k).1 + ρ0.1 - (ρ n).1) ∧
      (∑ k ∈ Finset.range n, (G k (g k (ρ k))).2 =
        ∑ k ∈ Finset.range n, (s k).2 + ρ0.2 - (ρ n).2) := by
    intro n
    induction n with
    | zero =>
      have h0 : ρ 0 = ρ0 := rfl
      simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih.1, ih.2, hρs]
      simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add]
      constructor <;> ring
  have hρ1 : Tendsto (fun n => (ρ n).1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (box n).1) hr1
  have hρ2 : Tendsto (fun n => (ρ n).2) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (box n).2) hr2
  refine ⟨fun k => g k (ρ k), fun k => (hg k (ρ k) (box k)).1, ?_, ?_⟩
  · rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (hG k _ (hg k (ρ k) (box k)).1).1)]
    have hlim := (hs1.hasSum.tendsto_sum_nat.add_const ρ0.1).sub hρ1
    have hx : ∑' k, (s k).1 + ρ0.1 - 0 = x.1 := by simp [hρ0]
    rw [hx] at hlim
    exact hlim.congr (fun n => (tele n).1.symm)
  · rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (hG k _ (hg k (ρ k) (box k)).1).2)]
    have hlim := (hs2.hasSum.tendsto_sum_nat.add_const ρ0.2).sub hρ2
    have hx : ∑' k, (s k).2 + ρ0.2 - 0 = x.2 := by simp [hρ0]
    rw [hx] at hlim
    exact hlim.congr (fun n => (tele n).2.symm)

end Erdos265
