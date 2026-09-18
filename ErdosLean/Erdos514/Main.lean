import ErdosLean.Erdos514.Statement
import ErdosLean.Erdos514.Parts.RatioBound
import ErdosLean.Erdos514.Parts.NestedChain
import ErdosLean.Erdos514.Parts.PathThroughNested

/-!
# Erdős Problem 514 (JSP-000412): main theorem

Every transcendental entire function has a path to infinity along which `|f(z)/zⁿ| → ∞`
for every `n`.  Assembly: a nested chain of tracts
`D n` of the Taylor shifts `shift f (n+1)` (`nested_chain`), a path running through it
(`path_through_nested`), and the algebraic lower bound `ratio_bound`.
-/

open Filter

namespace Erdos514

theorem erdos_514 : Erdos514Statement := by
  intro f hf
  obtain ⟨D, hD, hsub, hmem⟩ := nested_chain hf
  obtain ⟨γ, hγc, hγD⟩ := path_through_nested D (fun n => (hD n).1) (fun n => (hD n).2.1)
    (fun n => (hD n).2.2) hsub
  -- `‖γ t‖ > n` as soon as `t ≥ n`
  have hnorm : Tendsto (fun t => ‖γ t‖) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop ((⌈b⌉₊ : ℕ) : ℝ)] with t ht
    exact (Nat.le_ceil b).trans (hmem _ _ (hγD _ t ht)).1.le
  refine ⟨γ, hγc, hnorm, fun n => ?_⟩
  obtain ⟨C, hC⟩ := ratio_bound f n
  have hlow : ∀ᶠ t in atTop, ‖γ t‖ - C ≤ ‖f (γ t) / γ t ^ n‖ := by
    filter_upwards [eventually_ge_atTop ((n : ℝ) + 1)] with t ht
    have h1 : γ t ∈ D (n + 1) := hγD (n + 1) t (by exact_mod_cast ht)
    have h2 : γ t ∈ D n := hγD n t (by linarith)
    have hbig : ((n + 1 : ℕ) : ℝ) < ‖γ t‖ := (hmem _ _ h1).1
    have hone : (1 : ℝ) ≤ ‖γ t‖ := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      linarith
    have hs : 1 < ‖shift f (n + 1) (γ t)‖ := (hmem _ _ h2).2
    have key := hC (γ t) hone
    have : ‖γ t‖ ≤ ‖γ t‖ * ‖shift f (n + 1) (γ t)‖ := by
      have h0 : 0 ≤ ‖γ t‖ := norm_nonneg _
      nlinarith
    linarith
  exact tendsto_atTop_mono' atTop hlow (tendsto_atTop_add_const_right atTop (-C) hnorm |>.congr
    (fun t => by ring))

end Erdos514
