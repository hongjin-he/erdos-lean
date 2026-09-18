import ErdosLean.Erdos956.Statement
import ErdosLean.Erdos956.Parts.Disjoint
import ErdosLean.Erdos956.Parts.GridCard
import ErdosLean.Erdos956.Parts.Count
import ErdosLean.Erdos956.Parts.Padding
import ErdosLean.Erdos956.Parts.HBound
import ErdosLean.Erdos956.Parts.Asymptotic
import ErdosLean.Erdos956.Parts.Exponents

/-!
# Erdős Problem 956 (JSP-000796): main theorem

`h(n) ≫ n^{4/3}`; in particular `h(n) > n^{1+c}` for every `c < 1/3` and all large `n`, which
answers the question of erdosproblems.com/956 affirmatively.  Together with the (published, not
formalised here) Erdős–Pach bound `h(n) ≪ n^{4/3}` this determines `h(n) = Θ(n^{4/3})`
(`erdos956_theta_of_upper`).  Assembly of the parts in `Parts/`.
-/

namespace Erdos956

open Filter Asymptotics

/-- The grid configuration of parameter `k`, padded to size `n`, has `≥ M_k` unit pairs. -/
theorem grid_bound : ∀ k ≥ 2, ∀ n ≥ nk k, Mk k ≤ h n := by
  intro k hk n hn
  have hadm := admissible_X hk
  have hcard : (X k).card = nk k := card_X (by omega)
  obtain ⟨Y, hXY, hYc, hY⟩ := exists_padding hadm (n := n) (by rw [hcard]; exact hn)
  calc Mk k ≤ (unitPairs (C k) (X k)).card := Mk_le_card_unitPairs (by omega)
    _ ≤ (unitPairs (C k) Y).card := Finset.card_le_card (unitPairs_mono hXY)
    _ ≤ h Y.card := le_h hY
    _ = h n := by rw [hYc]

/-- `h(n) ≫ n^{4/3}`. -/
theorem erdos956_lowerBound : Erdos956LowerBound := lower_of_grid h grid_bound

/-- `h(n) > n^{1+c}` eventually, for every `c < 1/3`. -/
theorem erdos956_allExponents : Erdos956AllExponents :=
  exponents_of_lower h erdos956_lowerBound

/-- **Erdős #956** as posed: there is `c > 0` with `h(n) > n^{1+c}` for all large `n`. -/
theorem erdos956 : Erdos956Statement :=
  ⟨1 / 6, by norm_num, erdos956_allExponents (1 / 6) (by norm_num)⟩

/-- Everything proved here, bundled. -/
theorem erdos956_main : Erdos956Statement ∧ Erdos956LowerBound ∧ Erdos956AllExponents :=
  ⟨erdos956, erdos956_lowerBound, erdos956_allExponents⟩

/-- With the Erdős–Pach upper bound (assumed as a hypothesis, not proved here) the order of
magnitude is determined: `h(n) = Θ(n^{4/3})`. -/
theorem erdos956_theta_of_upper (hup : ErdosPachUpperBound) :
    (fun n : ℕ => (h n : ℝ)) =Θ[atTop] fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3) := by
  obtain ⟨c₀, hc₀, hev⟩ := erdos956_lowerBound
  obtain ⟨K, hK⟩ := hup
  refine ⟨IsBigO.of_bound K ?_, IsBigO.of_bound (1 / c₀) ?_⟩
  · filter_upwards with n
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact hK n
  · filter_upwards [hev] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      one_div_mul_eq_div, le_div_iff₀ hc₀, mul_comm]
    exact hn

end Erdos956
