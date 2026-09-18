import ErdosLean.Erdos995.Parts.Params
import ErdosLean.Erdos996.Parts.Asm.SpikeMeasure
import ErdosLean.Erdos996.Parts.SpikeFourierSupport
import ErdosLean.Erdos996.Parts.Asm.Atoms

/-!
# Erdős 995, part L5 (Atoms): Fourier-disjointness of the atoms

Adapted from `ErdosLean/Erdos996/Parts/Asm/Atoms.lean` with `A` deleted. The generic lemmas
`Erdos996.Asm.alt_integrable_spike`, `Erdos996.Asm.alt_fourierCoeff_spike_zero`,
`Erdos996.fourierCoeff_spike_dilate_eq_zero`, `Erdos996.fourierCoeff_nsmul_comp_mul` are reused.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos995
namespace Con

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

lemma blk_eq_sum_atom (k : ℕ) (x : 𝕋) :
    blk k x = Real.sqrt (lam k / blockLen k) * ∑ q ∈ Finset.Icc 1 (blockLen k), atom k q x := by
  rfl

/-! ### Band separation -/

lemma shift_mono' : Monotone shift := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  show shift n ≤ shift n + blockLen n * spacing n + depth n
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

lemma band_sep (k k' q q' : ℕ) (hk : k < k') (hq : q ≤ blockLen k) :
    shift k + q * spacing k + depth k ≤ shift k' + q' * spacing k' := by
  have h1 : shift (k + 1) ≤ shift k' := shift_mono' (by omega)
  have h2 : shift (k + 1) = shift k + blockLen k * spacing k + depth k := rfl
  have h3 : q * spacing k ≤ blockLen k * spacing k := Nat.mul_le_mul_right _ hq
  generalize q * spacing k = a at *
  generalize blockLen k * spacing k = b at *
  generalize q' * spacing k' = c at *
  omega

lemma band_sep_same (k q q' : ℕ) (hq : q < q') :
    shift k + q * spacing k + depth k ≤ shift k + q' * spacing k := by
  have h1 : (q + 1) * spacing k ≤ q' * spacing k := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * spacing k = q * spacing k + (depth k + 2) := by
    rw [add_mul, one_mul]; rfl
  generalize q * spacing k = a at *
  generalize q' * spacing k = c at *
  omega

lemma integrable_atom (k q : ℕ) : Integrable (fun x : 𝕋 => (atom k q x : ℂ)) μ𝕋 := by
  have hn : ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) ≠ 0 := by positivity
  have hmp : MeasurePreserving (fun x : 𝕋 => ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) • x)
      μ𝕋 μ𝕋 := Measure.measurePreserving_zsmul μ𝕋 hn
  have e : (fun x : 𝕋 => (atom k q x : ℂ)) =
      (fun y : 𝕋 => (Erdos996.spike (depth k) y : ℂ)) ∘
      (fun x : 𝕋 => ((2 ^ (shift k + q * spacing k) : ℕ) : ℤ) • x) := by
    funext x
    simp only [Function.comp, atom, natCast_zsmul]
  rw [e]
  exact Integrable.comp_measurable
    (by rw [hmp.map_eq]; exact Erdos996.Asm.alt_integrable_spike _) hmp.measurable

lemma fourierCoeff_atom_zero (k q : ℕ) : fourierCoeff (fun x => (atom k q x : ℂ)) 0 = 0 := by
  have hmeas : AEStronglyMeasurable (fun y : 𝕋 => (Erdos996.spike (depth k) y : ℂ)) μ𝕋 :=
    (Complex.measurable_ofReal.comp (Erdos996.measurable_spike _)).aestronglyMeasurable
  have h := Erdos996.fourierCoeff_nsmul_comp_mul (2 ^ (shift k + q * spacing k)) (by positivity)
    (fun y : 𝕋 => (Erdos996.spike (depth k) y : ℂ)) hmeas 0
  rw [mul_zero] at h
  exact h.trans (Erdos996.Asm.alt_fourierCoeff_spike_zero _)

lemma fourierCoeff_blk (k : ℕ) (r : ℤ) :
    fourierCoeff (fun x => (blk k x : ℂ)) r =
      (Real.sqrt (lam k / blockLen k) : ℂ) *
        ∑ q ∈ Finset.Icc 1 (blockLen k), fourierCoeff (fun x => (atom k q x : ℂ)) r := by
  have hfun : (fun x => (blk k x : ℂ)) = fun x => (Real.sqrt (lam k / blockLen k) : ℂ) *
      (∑ q ∈ Finset.Icc 1 (blockLen k), fun x : 𝕋 => (atom k q x : ℂ)) x := by
    funext x
    rw [blk_eq_sum_atom, Finset.sum_apply]
    push_cast
    rfl
  rw [hfun, fourierCoeff.const_mul,
    fourierCoeff.sum _ _ (fun q _ => integrable_atom k q), Finset.sum_apply]

/-- Distinct atoms have disjoint Fourier supports. -/
lemma fourierCoeff_atom_disjoint (k q k' q' : ℕ) (r : ℤ)
    (hq : q ∈ Finset.Icc 1 (blockLen k)) (hq' : q' ∈ Finset.Icc 1 (blockLen k'))
    (hne : (k, q) ≠ (k', q')) :
    fourierCoeff (fun x => (atom k q x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (atom k' q' x : ℂ)) r = 0 := by
  by_cases hr : r = 0
  · subst hr; left; exact fourierCoeff_atom_zero k q
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have e1 : (2 : ℤ) ^ (shift k + q * spacing k) ∣ r ∧
      ¬ (2 : ℤ) ^ (shift k + q * spacing k + depth k) ∣ r := by
    by_contra h
    exact h1 (Erdos996.fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  have e2 : (2 : ℤ) ^ (shift k' + q' * spacing k') ∣ r ∧
      ¬ (2 : ℤ) ^ (shift k' + q' * spacing k' + depth k') ∣ r := by
    by_contra h
    exact h2 (Erdos996.fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  rw [Finset.mem_Icc] at hq hq'
  have sep : shift k + q * spacing k + depth k ≤ shift k' + q' * spacing k' ∨
      shift k' + q' * spacing k' + depth k' ≤ shift k + q * spacing k := by
    rcases lt_trichotomy k k' with hk | rfl | hk
    · exact Or.inl (band_sep k k' q q' hk hq.2)
    · have hqq : q ≠ q' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hqq with h | h
      · exact Or.inl (band_sep_same k q q' h)
      · exact Or.inr (band_sep_same k q' q h)
    · exact Or.inr (band_sep k' k q' q hk hq'.2)
  rcases sep with h | h
  · exact e1.2 (dvd_trans (pow_dvd_pow 2 h) e2.1)
  · exact e2.2 (dvd_trans (pow_dvd_pow 2 h) e1.1)

end Con
end Erdos995
