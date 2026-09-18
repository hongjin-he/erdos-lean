/-
This file contains material adapted from `src/latest/ErdosProblems/Erdos1165/SecondMoment.lean`
in plby/lean-proofs (https://github.com/plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e), which carries the following notice:

  Copyright 2026 The Formal Conjectures Authors.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

Modifications (2026, HongJin HE): the second-moment lemmas were renamed with the prefix
`alt_ml_`, placed in the namespace `DuffinSchaeffer`, and adapted to the Lean/Mathlib version
of this repository; the remainder of the file is original to this project.
-/

import ErdosLean.DuffinSchaeffer.Parts.UnitPairCount

/-!
# Duffin–Schaeffer — Part 8: `λ(A_q) ≫ w(q)` when `w(q) ≤ 1/2`

For `ψ(q) ≤ 1/2` the arcs are disjoint and `λ(A_q) = 2w(q)`.  In
general (only `w(q) ≤ 1/2`) use Cauchy–Schwarz with `N(x) = #{a : ‖x - a/q‖ < ψ(q)/q}`:
`λ(A_q) ≥ (∫N)² / ∫N²`, `∫N = 2w(q)`, and `∫N² ≤ 2w(q) + C w(q)²` by `card_unit_pairs_le`
with `q = r` plus `∑_{0<|h|≤H} gcd(h,q)/φ(gcd(h,q)) ≪ H`.

The bound `∑_{h ≤ K} gcd(h,q)/φ(gcd(h,q)) ≤ 4K` is proved elementarily
(`alt_ml_sum_gcd_ratio_le`), via `d/φ(d) ≤ 2 ∑_{e | d} 1/e`.
The `alt_ml_` second-moment lemmas are adapted from `ErdosProblems/Erdos1165/SecondMoment.lean`
in plby/lean-proofs (Copyright 2026 The Formal Conjectures Authors, Apache-2.0); see the
notice at the top of this file and `NOTICE`.
-/

open MeasureTheory

namespace DuffinSchaeffer

section AltMLSecondMoment

open Set

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Omega ι : Type*}

/-- The real-valued indicator of an event. -/
def alt_ml_eventIndicator (A : Set Omega) (omega : Omega) : ℝ :=
  if omega ∈ A then 1 else 0

@[simp] lemma alt_ml_eventIndicator_apply (A : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega = if omega ∈ A then 1 else 0 := rfl

@[simp] lemma alt_ml_eventIndicator_of_mem {A : Set Omega} {omega : Omega} (h : omega ∈ A) :
    alt_ml_eventIndicator A omega = 1 := by simp [alt_ml_eventIndicator, h]

@[simp] lemma alt_ml_eventIndicator_of_not_mem {A : Set Omega} {omega : Omega} (h : omega ∉ A) :
    alt_ml_eventIndicator A omega = 0 := by simp [alt_ml_eventIndicator, h]

lemma alt_ml_eventIndicator_nonneg (A : Set Omega) (omega : Omega) :
    0 ≤ alt_ml_eventIndicator A omega := by
  by_cases h : omega ∈ A <;> simp [alt_ml_eventIndicator, h]

@[simp] lemma alt_ml_eventIndicator_mul (A B : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega * alt_ml_eventIndicator B omega = alt_ml_eventIndicator (A ∩ B) omega := by
  by_cases hA : omega ∈ A <;> by_cases hB : omega ∈ B <;>
    simp [alt_ml_eventIndicator, hA, hB]

@[simp] lemma alt_ml_eventIndicator_sq (A : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega ^ 2 = alt_ml_eventIndicator A omega := by
  by_cases hA : omega ∈ A <;> simp [alt_ml_eventIndicator, hA]

lemma alt_ml_measurable_eventIndicator [MeasurableSpace Omega] {A : Set Omega}
    (hA : MeasurableSet A) :
    Measurable (alt_ml_eventIndicator A) := by
  exact Measurable.ite hA measurable_const measurable_const

/-- The number of events in a finite family which occur, represented as a real number. -/
def alt_ml_indicatorCount (I : Finset ι) (A : ι → Set Omega) (omega : Omega) : ℝ :=
  ∑ i ∈ I, alt_ml_eventIndicator (A i) omega

lemma alt_ml_indicatorCount_nonneg (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 ≤ alt_ml_indicatorCount I A omega := by
  exact Finset.sum_nonneg fun i hi => alt_ml_eventIndicator_nonneg (A i) omega

lemma alt_ml_measurable_indicatorCount [MeasurableSpace Omega]
    (I : Finset ι) (A : ι → Set Omega)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Measurable (alt_ml_indicatorCount I A) := by
  classical
  unfold alt_ml_indicatorCount
  exact Finset.measurable_sum _ fun i hi => alt_ml_measurable_eventIndicator (hA i hi)

lemma alt_ml_indicatorCount_eq_card_filter (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    alt_ml_indicatorCount I A omega = ((I.filter fun i => omega ∈ A i).card : ℝ) := by
  classical
  simp [alt_ml_indicatorCount, alt_ml_eventIndicator]

lemma alt_ml_one_le_indicatorCount_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    1 ≤ alt_ml_indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  classical
  rw [alt_ml_indicatorCount_eq_card_filter]
  norm_num
  exact Finset.filter_nonempty_iff

lemma alt_ml_indicatorCount_pos_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 < alt_ml_indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  rw [← alt_ml_one_le_indicatorCount_iff I A omega]
  rw [alt_ml_indicatorCount_eq_card_filter]
  norm_num

lemma alt_ml_indicatorCount_sq_expand (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    alt_ml_indicatorCount I A omega ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, alt_ml_eventIndicator (A i ∩ A j) omega := by
  classical
  simp only [alt_ml_indicatorCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simpa [mul_comm] using alt_ml_eventIndicator_mul (A i) (A j) omega

/-! ## Exact indicator moment expansions -/

variable [MeasurableSpace Omega] {mu : Measure Omega}

lemma alt_ml_integral_eventIndicator [IsFiniteMeasure mu] {A : Set Omega}
    (hA : MeasurableSet A) :
    ∫ omega, alt_ml_eventIndicator A omega ∂mu = mu.real A := by
  change ∫ omega, A.indicator (fun _ => (1 : ℝ)) omega ∂mu = mu.real A
  rw [integral_indicator hA]
  simp

lemma alt_ml_integrable_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (alt_ml_indicatorCount I A) mu := by
  apply integrable_finsetSum I
  intro i hi
  apply Integrable.of_bound (alt_ml_measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun omega => by
    by_cases h : omega ∈ A i <;> simp [alt_ml_eventIndicator, h]

lemma alt_ml_integral_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, alt_ml_indicatorCount I A omega ∂mu =
      ∑ i ∈ I, mu.real (A i) := by
  classical
  simp only [alt_ml_indicatorCount]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact alt_ml_integral_eventIndicator (hA i hi)
  · intro i hi
    apply Integrable.of_bound (alt_ml_measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i <;> simp [alt_ml_eventIndicator, h]

lemma alt_ml_integrable_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (fun omega => alt_ml_indicatorCount I A omega ^ 2) mu := by
  rw [show (fun omega => alt_ml_indicatorCount I A omega ^ 2) =
      (fun omega => alt_ml_indicatorCount I A omega * alt_ml_indicatorCount I A omega) by
    funext omega
    rw [pow_two]]
  refine Integrable.of_bound (C := (I.card : ℝ) ^ 2) ?_ ?_
  · exact ((alt_ml_measurable_indicatorCount I A hA).mul
      (alt_ml_measurable_indicatorCount I A hA)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega => by
      rw [← pow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (alt_ml_indicatorCount_nonneg I A omega)
        (by
          rw [alt_ml_indicatorCount_eq_card_filter]
          exact_mod_cast Finset.card_filter_le I _) 2

lemma alt_ml_integral_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, alt_ml_indicatorCount I A omega ^ 2 ∂mu =
      ∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j) := by
  classical
  simp_rw [alt_ml_indicatorCount_sq_expand]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact alt_ml_integral_eventIndicator ((hA i hi).inter (hA j hj))
    · intro j hj
      apply Integrable.of_bound
        (alt_ml_measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ A i ∩ A j <;> simp [alt_ml_eventIndicator, h]
  · intro i hi
    apply integrable_finsetSum I
    intro j hj
    apply Integrable.of_bound
      (alt_ml_measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i ∩ A j <;> simp [alt_ml_eventIndicator, h]

omit [MeasurableSpace Omega] in
lemma alt_ml_indicatorCount_positive_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 0 < alt_ml_indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [alt_ml_indicatorCount_pos_iff]

omit [MeasurableSpace Omega] in
lemma alt_ml_indicatorCount_one_le_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 1 ≤ alt_ml_indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [alt_ml_one_le_indicatorCount_iff]

/-! ## Finite second-moment inequalities -/

lemma alt_ml_finite_secondMoment_mul (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i) ^ 2 ≤
      ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  classical
  let g : ι → ℝ := fun i => if 0 < f i then 1 else 0
  have hfg : ∀ i ∈ S, f i * g i = f i := by
    intro i hi
    by_cases hpos : 0 < f i
    · simp [g, hpos]
    · have hz : f i = 0 := le_antisymm (not_lt.mp hpos) (hf i hi)
      simp [g, hz]
  have hg : ∑ i ∈ S, g i ^ 2 = ((S.filter fun i => 0 < f i).card : ℝ) := by
    simp [g]
  have hsum : ∑ i ∈ S, f i * g i = ∑ i ∈ S, f i :=
    Finset.sum_congr rfl hfg
  calc
    (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ S, f i * g i) ^ 2 := by rw [hsum]
    _ ≤ (∑ i ∈ S, f i ^ 2) * ∑ i ∈ S, g i ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S f g
    _ = ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
      rw [hg, mul_comm]

lemma alt_ml_finite_secondMoment_ratio (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hsecond : 0 < ∑ i ∈ S, f i ^ 2) :
    (∑ i ∈ S, f i) ^ 2 / (∑ i ∈ S, f i ^ 2) ≤
      ((S.filter fun i => 0 < f i).card : ℝ) := by
  rw [div_le_iff₀ hsecond]
  simpa [mul_comm] using alt_ml_finite_secondMoment_mul S f hf

/-! ## Integral Cauchy--Schwarz and Paley--Zygmund -/

/-- Squared Cauchy--Schwarz for real Bochner integrals. -/
lemma alt_ml_integral_mul_sq_le_integral_sq_mul_integral_sq
    (f g : Omega → ℝ)
    (hf : Integrable (fun omega => f omega ^ 2) mu)
    (hg : Integrable (fun omega => g omega ^ 2) mu)
    (hfg : Integrable (fun omega => f omega * g omega) mu) :
    (∫ omega, f omega * g omega ∂mu) ^ 2 ≤
      (∫ omega, f omega ^ 2 ∂mu) * (∫ omega, g omega ^ 2 ∂mu) := by
  have h_cauchy_schwarz :
      0 ≤ ∫ omega,
        (f omega -
          (∫ omega, f omega * g omega ∂mu) /
            (∫ omega, g omega ^ 2 ∂mu) * g omega) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases h : ∫ omega, g omega ^ 2 ∂mu = 0 <;>
      simp only [h, sub_sq, mul_pow] at h_cauchy_schwarz ⊢
  · rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)] at h
    · have hgzero : g =ᵐ[mu] 0 := h.mono fun omega homega => by
        simp only [Pi.zero_apply]
        exact sq_eq_zero_iff.mp (by simpa using homega)
      have hfgzero : ∫ omega, f omega * g omega ∂mu = 0 := by
        apply integral_eq_zero_of_ae
        exact hgzero.mono fun omega homega => by simp [homega]
      simp [hfgzero]
    · exact hg
  · rw [integral_add, integral_sub] at h_cauchy_schwarz
    · simp only [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm,
        integral_mul_const] at h_cauchy_schwarz ⊢
      simp only [← mul_assoc, integral_mul_const] at h_cauchy_schwarz ⊢
      have hfn : 0 ≤ ∫ omega, f omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (f omega)
      have hgn : 0 ≤ ∫ omega, g omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (g omega)
      nlinarith [inv_mul_cancel_left₀ h (∫ omega, f omega * g omega ∂mu),
        inv_mul_cancel₀ h]
    · exact hf
    · convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · refine Integrable.sub hf ?_
      convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · exact hg.const_mul _

/-- Division-free second-moment inequality.  For a nonnegative random
variable, the square of its first moment is bounded by its second moment
times the measure of its positive support. -/
theorem alt_ml_integral_secondMoment_mul [IsFiniteMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    (∫ omega, Z omega ∂mu) ^ 2 ≤
      (∫ omega, Z omega ^ 2 ∂mu) * mu.real {omega | 0 < Z omega} := by
  let support : Set Omega := {omega | 0 < Z omega}
  let oneSupport : Omega → ℝ := alt_ml_eventIndicator support
  have hsupport : MeasurableSet support :=
    measurableSet_lt measurable_const hZmeas
  have hone : Integrable oneSupport mu := by
    apply Integrable.of_bound
      (alt_ml_measurable_eventIndicator hsupport).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ support <;> simp [alt_ml_eventIndicator, h]
  have hone2 : Integrable (fun omega => oneSupport omega ^ 2) mu :=
    hone.congr (Filter.Eventually.of_forall fun omega => by
      exact (alt_ml_eventIndicator_sq support omega).symm)
  have hprod : Integrable (fun omega => Z omega * oneSupport omega) mu :=
    hZint.mul_bdd (c := 1) (alt_ml_measurable_eventIndicator hsupport).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ support <;> simp [oneSupport, h])
  have hmul := alt_ml_integral_mul_sq_le_integral_sq_mul_integral_sq
    Z oneSupport hZ2 hone2 hprod
  have hfirst : (∫ omega, Z omega * oneSupport omega ∂mu) = ∫ omega, Z omega ∂mu := by
    apply integral_congr_ae
    filter_upwards with omega
    by_cases hpos : 0 < Z omega
    · simp [oneSupport, support, hpos]
    · have hz : Z omega = 0 := le_antisymm (not_lt.mp hpos) (hZ omega)
      simp [hz]
  have hsecond : (∫ omega, oneSupport omega ^ 2 ∂mu) = mu.real support := by
    calc
      (∫ omega, oneSupport omega ^ 2 ∂mu) = ∫ omega, oneSupport omega ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => alt_ml_eventIndicator_sq support omega
      _ = mu.real support := alt_ml_integral_eventIndicator hsupport
  simpa only [hfirst, hsecond, support] using hmul

/-- The second-moment estimate for a finite sum of indicators, written
entirely in terms of one-point and pair probabilities. -/
theorem alt_ml_indicatorCount_secondMoment_bound [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∑ i ∈ I, mu.real (A i)) ^ 2 ≤
      (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) *
        mu.real (⋃ i ∈ I, A i) := by
  have h := alt_ml_integral_secondMoment_mul (mu := mu) (alt_ml_indicatorCount I A)
    (alt_ml_indicatorCount_nonneg I A) (alt_ml_measurable_indicatorCount I A hA)
    (alt_ml_integrable_indicatorCount I A hA)
    (alt_ml_integrable_indicatorCount_sq I A hA)
  rwa [alt_ml_integral_indicatorCount I A hA, alt_ml_integral_indicatorCount_sq I A hA,
    alt_ml_indicatorCount_positive_set I A] at h


end

end AltMLSecondMoment

open Finset

/-- Telescoping: `∏_{n ∈ S} n²/(n²-1) ≤ 2N/(N+1)` for `S ⊆ [2, N]`. -/
theorem alt_ml_prod_sq_div_le (N : ℕ) (hN : 1 ≤ N) : ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n ∧ n ≤ N) →
    ∏ n ∈ S, ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ≤ 2 * (N : ℝ) / ((N : ℝ) + 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro S hS
    have hSe : S = ∅ := by
      ext n
      simp only [Finset.notMem_empty, iff_false]
      intro hn
      have := hS n hn
      omega
    subst hSe
    norm_num
  | succ N hN ih =>
    intro S hS
    have hS' : ∀ n ∈ S.erase (N + 1), 2 ≤ n ∧ n ≤ N := by
      intro n hn
      obtain ⟨hne, hn⟩ := Finset.mem_erase.1 hn
      have := hS n hn
      omega
    have h1 := ih _ hS'
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hmono : 2 * (N : ℝ) / (N + 1) ≤ 2 * ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    by_cases hmem : N + 1 ∈ S
    · rw [← Finset.mul_prod_erase S _ hmem]
      have hfac : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) := by
        push_cast
        apply div_nonneg (by positivity)
        nlinarith
      calc ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) *
            ∏ x ∈ S.erase (N + 1), ((x : ℝ) ^ 2 / ((x : ℝ) ^ 2 - 1))
          ≤ ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) * (2 * (N : ℝ) / ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h1 hfac
        _ = 2 * ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            have hd : ((N : ℝ) + 1) ^ 2 - 1 = N * (N + 2) := by ring
            rw [hd]
            have hN0 : (N : ℝ) ≠ 0 := by positivity
            field_simp
            ring
    · rw [Finset.erase_eq_of_notMem hmem] at h1
      exact h1.trans hmono

/-- For a finite set of primes, `∏ p²/(p²-1) ≤ 2`. -/
theorem alt_ml_prod_primes_sq_div_le_two (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) ≤ 2 := by
  set N := max (S.sup id) 1 with hNdef
  have hN : 1 ≤ N := le_max_right _ _
  have h := alt_ml_prod_sq_div_le N hN S (fun n hn => ⟨(hS n hn).two_le,
    le_trans (Finset.le_sup (f := id) hn) (le_max_left _ _)⟩)
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Euler factor identity: `(1 - 1/p)⁻¹ = (1 + 1/p) · p²/(p²-1)`. -/
theorem alt_ml_inv_one_sub_eq (p : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ = (1 + 1 / (p : ℝ)) * ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp3 : (p : ℝ) + 1 ≠ 0 := by linarith
  have : (p : ℝ) ^ 2 - 1 = (p - 1) * (p + 1) := by ring
  rw [this]
  field_simp

/-- `m/φ(m) = ∏_{p | m} (1 - 1/p)⁻¹`. -/
theorem alt_ml_div_totient_eq (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / Nat.totient m = ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have hq := Nat.totient_eq_mul_prod_factors m
  have hr : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hq
    push_cast at this
    exact this
  rw [hr, Finset.prod_inv_distrib]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [one_div]
  field_simp

/-- `d/φ(d) ≤ 2 ∑_{e | d} 1/e`. -/
theorem alt_ml_div_totient_le (d : ℕ) (hd : 0 < d) :
    (d : ℝ) / Nat.totient d ≤ 2 * ∑ e ∈ d.divisors, (1 : ℝ) / e := by
  rw [alt_ml_div_totient_eq d hd]
  have hprod : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) *
        ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact alt_ml_inv_one_sub_eq p (Nat.prime_of_mem_primeFactors hp)
  have h1 : ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ)) ≤ ∑ e ∈ d.divisors, (1 : ℝ) / e := by
    rw [Finset.prod_one_add]
    have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (d.primeFactors.powerset : Set _) := by
      intro t1 ht1 t2 ht2 heq
      have hp1 : ∀ p ∈ t1, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.1 ht1) hp)
      have hp2 : ∀ p ∈ t2, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.1 ht2) hp)
      have := congrArg Nat.primeFactors heq
      simp only at this
      rwa [Nat.primeFactors_prod hp1, Nat.primeFactors_prod hp2] at this
    have heq : ∑ t ∈ d.primeFactors.powerset, ∏ p ∈ t, (1 / (p : ℝ)) =
        ∑ e ∈ d.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p), (1 : ℝ) / e := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro t _
      push_cast
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 he
      rw [Nat.mem_divisors]
      refine ⟨dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.1 ht))
        (Nat.prod_primeFactors_dvd d), hd.ne'⟩
    · intro e _ _
      positivity
  have h2 := alt_ml_prod_primes_sq_div_le_two d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h0 : 0 ≤ ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  rw [hprod]
  calc (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) *
        ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1))
      ≤ (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) * 2 := mul_le_mul_of_nonneg_left h2 h0
    _ ≤ (∑ e ∈ d.divisors, (1 : ℝ) / e) * 2 := mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ = 2 * ∑ e ∈ d.divisors, (1 : ℝ) / e := mul_comm _ _

/-- `∑_{1 ≤ h ≤ K} gcd(h,q)/φ(gcd(h,q)) ≤ 4K`. -/
theorem alt_ml_sum_gcd_ratio_le (q K : ℕ) (hq : 0 < q) :
    ∑ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q) ≤ 4 * K := by
  have hstep : ∀ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q) ≤
      2 * ∑ e ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) := by
    intro h hh
    obtain ⟨h1, hK⟩ := Finset.mem_Icc.1 hh
    have hh0 : h ≠ 0 := by omega
    refine (alt_ml_div_totient_le _ (Nat.gcd_pos_of_pos_right h hq)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      have he' := Nat.dvd_trans (Nat.dvd_of_mem_divisors he) (Nat.gcd_dvd_left h q)
      have hle := Nat.le_of_dvd (by omega) he'
      have hpos := Nat.pos_of_mem_divisors he
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, he'⟩
    · intro e _ _
      positivity
  calc ∑ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q)
      ≤ ∑ h ∈ Icc 1 K, 2 * ∑ e ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) :=
        Finset.sum_le_sum hstep
    _ = 2 * ∑ e ∈ Icc 1 K, ∑ h ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 2 * ∑ e ∈ Icc 1 K, ((1 : ℝ) / e) * (((Icc 1 K).filter (fun h => e ∣ h)).card : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * ∑ e ∈ Icc 1 K, ((1 : ℝ) / e) * ((K : ℝ) / e) := by
        gcongr with e he
        have hc : ((Icc 1 K).filter (fun h => e ∣ h)).card = K / e := by
          rw [← Nat.Ioc_filter_dvd_card_eq_div K e]
          rfl
        rw [hc]
        exact Nat.cast_div_le
    _ = 2 * K * ∑ e ∈ Icc 1 K, ((e : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        field_simp
    _ ≤ 2 * K * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
        have hI : Icc 1 K = Ioo 0 (K + 1) := by
          ext e; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
        rw [hI]
        refine h.trans ?_
        norm_num
    _ = 4 * K := by ring

/-- Volume of a ball in the unit circle. -/
theorem alt_ml_volumeReal_ball_eq (x : UnitAddCircle) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume.real (Metric.ball x ρ) = min 1 (2 * ρ) := by
  rw [measureReal_def]
  have hvolume : volume (Metric.ball x ρ) = ENNReal.ofReal (min 1 (2 * ρ)) := by
    rw [measure_congr AddCircle.closedBall_ae_eq_ball.symm, AddCircle.volume_closedBall]
  rw [hvolume, ENNReal.toReal_ofReal]
  exact le_min (by norm_num) (mul_nonneg (by norm_num) hρ)

/-- The fibre of `card_unit_pairs_le` for `q = r`. -/
def alt_ml_fiber (q : ℕ) (h : ℤ) : Finset (ℕ × ℕ) :=
  ((range q) ×ˢ (range q)).filter (fun ab : ℕ × ℕ =>
    Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 q ∧
    (ab.1 : ℤ) * ((q / Nat.gcd q q : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q q : ℕ) : ℤ) ≡ h
      [ZMOD (Nat.lcm q q : ℤ)])

theorem alt_ml_card_fiber_le (q : ℕ) (hq : 0 < q) (n : ℕ) (s : ℤ) (hs : s = n ∨ s = -n) :
    ((alt_ml_fiber q s).card : ℝ) ≤
      (q : ℝ) * ((Nat.totient q : ℝ) / q) ^ 2 *
        ((Nat.gcd n q : ℝ) / Nat.totient (Nat.gcd n q)) := by
  have h1 : ((alt_ml_fiber q s).card : ℝ) ≤
      (if Int.gcd s (coprimePart q q) = 1 then 1 else 0) *
        ((Nat.gcd q q : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient q : ℝ) / q) *
          ((coprimePart q q : ℝ) / Nat.totient (coprimePart q q)) *
          ((Int.gcd s (Nat.gcd q q) : ℝ) / Nat.totient (Int.gcd s (Nat.gcd q q)))) :=
    card_unit_pairs_le q q hq hq s
  have hcp : coprimePart q q = 1 := by
    simp [coprimePart, Nat.gcd_self, Nat.div_self hq]
  have hgs : Int.gcd s (Nat.gcd q q) = Nat.gcd n q := by
    rw [Nat.gcd_self]
    rcases hs with rfl | rfl
    · exact Int.gcd_natCast_natCast n q
    · rw [Int.neg_gcd]; exact Int.gcd_natCast_natCast n q
  rw [hcp, hgs] at h1
  simp only [Nat.cast_one, Int.gcd_one_right, if_true, one_mul, Nat.totient_one, div_one,
    mul_one, Nat.gcd_self] at h1
  exact h1.trans (le_of_eq (by ring))

theorem measure_Aq_ge : ∃ c : ℝ, 0 < c ∧ ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q) → ∀ q : ℕ, 0 < q →
    weight ψ q ≤ 1 / 2 → c * weight ψ q ≤ volume.real (Aq ψ q) := by
  classical
  set Cs : ℝ := 4 with hCsdef
  have hCs : (0 : ℝ) < Cs := by norm_num
  refine ⟨4 / (2 + 4 * Cs), by positivity, ?_⟩
  intro ψ hψ q hq hw
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set δ : ℝ := ψ q / q with hδdef
  have hδ0 : 0 ≤ δ := div_nonneg (hψ q) hqR.le
  set R : Finset ℕ := (range q).filter (fun a => Nat.Coprime a q) with hRdef
  have hRcard : (R.card : ℝ) = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 2
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  set B : ℕ → Set UnitAddCircle := fun a => Metric.ball ((((a : ℝ) / q : ℝ)) : UnitAddCircle) δ
    with hBdef
  have hBmeas : ∀ a ∈ R, MeasurableSet (B a) := fun a _ => Metric.isOpen_ball.measurableSet
  have hsub : (⋃ a ∈ R, B a) ⊆ Aq ψ q := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨haq, hcop⟩ := Finset.mem_filter.1 ha
    rw [Aq, UnitAddCircle.mem_approxAddOrderOf_iff hq]
    refine ⟨a, Finset.mem_range.1 haq, hcop, ?_⟩
    have := hx
    rw [hBdef, Metric.mem_ball, dist_eq_norm] at this
    exact this
  have hw0 : 0 ≤ weight ψ q := by
    unfold weight; have := hψ q; positivity
  have hwdef : weight ψ q = (Nat.totient q : ℝ) * δ := by
    rw [weight, hδdef]; ring
  have hc2 : 4 / (2 + 4 * Cs) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases hw0.lt_or_eq with hwpos | hwzero
  swap
  · rw [← hwzero, mul_zero]; exact measureReal_nonneg
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < R.card := by
      rw [hRcard]; exact_mod_cast Nat.totient_pos.2 hq
    exact_mod_cast this
  by_cases hδ : 1 / 2 ≤ δ
  · obtain ⟨a, ha⟩ := hRne
    have h1 : volume.real (B a) = 1 := by
      rw [hBdef]
      simp only
      rw [alt_ml_volumeReal_ball_eq _ _ hδ0, min_eq_left (by linarith)]
    have h2 : volume.real (B a) ≤ volume.real (Aq ψ q) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro x hx
      apply hsub
      simp only [Set.mem_iUnion]
      exact ⟨a, ha, hx⟩
    calc 4 / (2 + 4 * Cs) * weight ψ q ≤ 2 * (1 / 2) :=
          mul_le_mul hc2 hw (le_of_lt hwpos) (by norm_num)
      _ = volume.real (B a) := by rw [h1]; norm_num
      _ ≤ volume.real (Aq ψ q) := h2
  push Not at hδ
  -- first moment
  have hvolB : ∀ a, volume.real (B a) = 2 * δ := by
    intro a
    rw [hBdef]
    simp only
    rw [alt_ml_volumeReal_ball_eq _ _ hδ0, min_eq_right (by linarith)]
  have hfirst : ∑ a ∈ R, volume.real (B a) = 2 * weight ψ q := by
    simp only [hvolB, Finset.sum_const, nsmul_eq_mul, hRcard, hwdef]
    ring
  -- off-diagonal near pairs
  set P : Finset (ℕ × ℕ) := (R ×ˢ R).filter (fun ab : ℕ × ℕ => ab.1 ≠ ab.2 ∧
      ∃ k : ℤ, |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < 2 * δ) with hPdef
  have hpoint : ∀ a ∈ R, ∀ b ∈ R, volume.real (B a ∩ B b) ≤
      (if a = b then 2 * δ else 0) +
        (if (a ≠ b ∧ ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ) then 2 * δ else 0) := by
    intro a _ b _
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, Set.inter_self, hvolB]
      have : 0 ≤ (if (a ≠ a ∧ ∃ k : ℤ, |(a : ℝ) / q - (a : ℝ) / q - k| < 2 * δ)
          then 2 * δ else 0) := by split_ifs <;> linarith
      linarith
    · rw [if_neg hab, zero_add]
      by_cases hne : (B a ∩ B b).Nonempty
      · have hnear : ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ := by
          obtain ⟨x, hxa, hxb⟩ := hne
          rw [hBdef, Metric.mem_ball, dist_eq_norm] at hxa hxb
          set t : ℝ := (a : ℝ) / q - (b : ℝ) / q with ht
          refine ⟨round t, ?_⟩
          have he : ((t : ℝ) : UnitAddCircle) =
              (x - ((((b : ℝ) / q : ℝ)) : UnitAddCircle)) -
                (x - ((((a : ℝ) / q : ℝ)) : UnitAddCircle)) := by
            rw [ht, AddCircle.coe_sub]
            abel
          have hn : ‖((t : ℝ) : UnitAddCircle)‖ < 2 * δ := by
            rw [he]
            calc _ ≤ ‖x - ((((b : ℝ) / q : ℝ)) : UnitAddCircle)‖ +
                  ‖x - ((((a : ℝ) / q : ℝ)) : UnitAddCircle)‖ := norm_sub_le _ _
              _ < δ + δ := add_lt_add hxb hxa
              _ = 2 * δ := by ring
          rw [UnitAddCircle.norm_eq] at hn
          exact hn
        rw [if_pos ⟨hab, hnear⟩]
        refine (measureReal_mono Set.inter_subset_left (measure_ne_top _ _)).trans ?_
        rw [hvolB]
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, measureReal_empty]
        split_ifs <;> linarith
  have hsecond_raw : ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b) ≤
      2 * weight ψ q + 2 * δ * (P.card : ℝ) := by
    calc ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b)
        ≤ ∑ a ∈ R, ∑ b ∈ R, ((if a = b then 2 * δ else 0) +
          (if (a ≠ b ∧ ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ) then 2 * δ
            else 0)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpoint a ha b hb
      _ = ∑ a ∈ R, 2 * δ + ∑ ab ∈ R ×ˢ R,
          (if (ab.1 ≠ ab.2 ∧ ∃ k : ℤ, |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < 2 * δ)
            then 2 * δ else 0) := by
          rw [Finset.sum_product]
          simp only [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_ite_eq R a (fun _ => 2 * δ), if_pos ha]
      _ = 2 * weight ψ q + 2 * δ * (P.card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hRcard, hwdef, hPdef]
          ring
  -- counting the near pairs
  set K : ℕ := ⌊2 * ψ q⌋₊ with hKdef
  set wt : ℕ → ℝ := fun n => (Nat.gcd n q : ℝ) / Nat.totient (Nat.gcd n q) with hwt
  have hPsub : P ⊆ (Icc 1 K).biUnion
      (fun n => alt_ml_fiber q (n : ℤ) ∪ alt_ml_fiber q (-(n : ℤ))) := by
    intro ab hab
    rw [hPdef, Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hne, k, hk⟩ := hab
    obtain ⟨haq, hacop⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbq, hbcop⟩ := Finset.mem_filter.1 hb
    have haq' := Finset.mem_range.1 haq
    have hbq' := Finset.mem_range.1 hbq
    set h : ℤ := (ab.1 : ℤ) - ab.2 - k * q with hhdef
    have hhR : (h : ℝ) = q * ((ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k) := by
      rw [hhdef]; push_cast; field_simp
    have habs : |(h : ℝ)| < 2 * ψ q := by
      rw [hhR, abs_mul, abs_of_pos hqR]
      calc (q : ℝ) * |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < q * (2 * δ) :=
            mul_lt_mul_of_pos_left hk hqR
        _ = 2 * ψ q := by rw [hδdef]; field_simp
    have hK : h.natAbs ≤ K := by
      apply Nat.le_floor
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact habs.le
    have hh0 : h ≠ 0 := by
      intro h0
      apply hne
      have e : (ab.1 : ℤ) - ab.2 = k * q := by rw [hhdef] at h0; linarith
      have hq' : (0 : ℤ) < q := by exact_mod_cast hq
      have ha1 : (ab.1 : ℤ) < q := by exact_mod_cast haq'
      have hb1 : (ab.2 : ℤ) < q := by exact_mod_cast hbq'
      have ha0 : (0 : ℤ) ≤ ab.1 := by positivity
      have hb0 : (0 : ℤ) ≤ ab.2 := by positivity
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with hk | hk | hk
        · have : k * q ≤ -q := by nlinarith
          omega
        · exact hk
        · have : q ≤ k * q := by nlinarith
          omega
      rw [hk0, zero_mul] at e
      omega
    have hmem : ab ∈ alt_ml_fiber q h := by
      simp only [alt_ml_fiber, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨haq', hbq'⟩, hacop, hbcop, ?_⟩
      rw [Nat.gcd_self, Nat.div_self hq, Nat.lcm_self, Int.modEq_iff_dvd]
      exact ⟨-k, by rw [hhdef]; push_cast; ring⟩
    rw [Finset.mem_biUnion]
    refine ⟨h.natAbs, Finset.mem_Icc.2 ⟨by omega, hK⟩, ?_⟩
    rcases lt_or_gt_of_ne hh0 with hneg | hpos
    · apply Finset.mem_union_right
      have : h = -((h.natAbs : ℕ) : ℤ) := by omega
      rw [← this]; exact hmem
    · apply Finset.mem_union_left
      have : h = ((h.natAbs : ℕ) : ℤ) := by omega
      rw [← this]; exact hmem
  set A0 : ℝ := (q : ℝ) * ((Nat.totient q : ℝ) / q) ^ 2 with hA0
  have hPcard : (P.card : ℝ) ≤ 2 * A0 * ∑ n ∈ Icc 1 K, wt n := by
    have h1 : P.card ≤ ∑ n ∈ Icc 1 K,
        ((alt_ml_fiber q (n : ℤ)).card + (alt_ml_fiber q (-(n : ℤ))).card) := by
      refine (Finset.card_le_card hPsub).trans ?_
      refine Finset.card_biUnion_le.trans ?_
      gcongr with n hn
      exact Finset.card_union_le _ _
    have h2 : (P.card : ℝ) ≤ ∑ n ∈ Icc 1 K,
        (((alt_ml_fiber q (n : ℤ)).card : ℝ) + ((alt_ml_fiber q (-(n : ℤ))).card : ℝ)) := by
      exact_mod_cast h1
    refine h2.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have e1 := alt_ml_card_fiber_le q hq n (n : ℤ) (Or.inl rfl)
    have e2 := alt_ml_card_fiber_le q hq n (-(n : ℤ)) (Or.inr rfl)
    rw [← hA0] at e1 e2
    have : 2 * A0 * wt n = A0 * wt n + A0 * wt n := by ring
    rw [this]
    exact add_le_add e1 e2
  have hsum : ∑ n ∈ Icc 1 K, wt n ≤ Cs * (2 * ψ q) := by
    have h1 := alt_ml_sum_gcd_ratio_le q K hq
    have hK : (K : ℝ) ≤ 2 * ψ q := by
      rw [hKdef]; exact Nat.floor_le (by have := hψ q; positivity)
    calc ∑ n ∈ Icc 1 K, wt n ≤ 4 * K := h1
      _ ≤ Cs * (2 * ψ q) := by rw [hCsdef]; linarith
  have hsecond : ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b) ≤
      (2 + 4 * Cs) * weight ψ q := by
    have hwsq : 8 * Cs * weight ψ q ^ 2 ≤ 4 * Cs * weight ψ q := by
      have : weight ψ q ^ 2 ≤ weight ψ q * (1 / 2) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hw hw0
      nlinarith
    have hA0nn : 0 ≤ A0 := by positivity
    have hoff : 2 * δ * (P.card : ℝ) ≤ 8 * Cs * weight ψ q ^ 2 := by
      calc 2 * δ * (P.card : ℝ) ≤ 2 * δ * (2 * A0 * (Cs * (2 * ψ q))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hPcard.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
        _ = 8 * Cs * weight ψ q ^ 2 := by
            rw [hA0, weight, hδdef]
            field_simp
            ring
    linarith
  -- Cauchy–Schwarz
  have hCS := alt_ml_indicatorCount_secondMoment_bound (mu := volume) R B hBmeas
  rw [hfirst] at hCS
  have hU : volume.real (⋃ a ∈ R, B a) ≤ volume.real (Aq ψ q) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have h3 : (2 * weight ψ q) ^ 2 ≤ ((2 + 4 * Cs) * weight ψ q) * volume.real (Aq ψ q) :=
    hCS.trans (mul_le_mul hsecond hU measureReal_nonneg (by positivity))
  have h4 : 4 * weight ψ q ≤ (2 + 4 * Cs) * volume.real (Aq ψ q) := by
    have : weight ψ q * (4 * weight ψ q) ≤ weight ψ q * ((2 + 4 * Cs) * volume.real (Aq ψ q)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hwpos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith



end DuffinSchaeffer
