import ErdosLean.Erdos494.Defs
import ErdosLean.Erdos494.Parts.GfsRecursion

/-! # Erdős 494, part A3: the Selfridge–Straus linearisation.

If `|A| = |B| = n` and `p_l(A) = p_l(B)` for `1 ≤ l < j`, then
`p_j(A_s) - p_j(B_s) = f_s(n,j) · (p_j(A) - p_j(B))`.

Route (power series in `ℂ⟦t⟧`): put `E_A = Σ_{a∈A} exp(a t)`; the `s`-th elementary symmetric
function of `(exp(a t))_{a∈A}` is `Σ_{S⊆A,|S|=s} exp((ΣS) t)`, whose `t^j`-coefficient is
`p_j(A_s)/j!`.  Newton (`MvPolynomial.mul_esymm_eq_sum`, evaluated at `x_a = exp(a t)`):
`k e_k = Σ_{i=1}^k (-1)^{i+1} e_{k-i} · E(i t)`.  All differences `e_k^A - e_k^B` and
`E_A(i t) - E_B(i t)` vanish below order `t^j`; comparing `t^j`-coefficients gives the
recursion of `gfs_recursion`, whence the coefficient is `f_k(n,j) (p_j A - p_j B)/j!`.
(Also valid for `s > n`, where both sides vanish.)  Verified numerically for `n ≤ 7`. -/

namespace Erdos494

namespace KSumAux

open Finset PowerSeries

/-- `exp(c t)` as a power series. -/
noncomputable def E (c : ℂ) : ℂ⟦X⟧ := rescale c (exp ℂ)

lemma E_add (a b : ℂ) : E a * E b = E (a + b) := exp_mul_exp_eq_exp_add a b

lemma E_zero : E 0 = 1 := by
  simp [E, constantCoeff_exp]

lemma prod_E {ι : Type*} (t : Finset ι) (c : ι → ℂ) : ∏ i ∈ t, E (c i) = E (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [E_zero]
  | insert x t hx ih => rw [prod_insert hx, sum_insert hx, ih, E_add]

lemma E_pow (c : ℂ) (i : ℕ) : E c ^ i = E ((i : ℂ) * c) := by
  induction i with
  | zero => simp [E_zero]
  | succ i ih => rw [pow_succ, ih, E_add]; push_cast; ring_nf

lemma coeff_E (c : ℂ) (m : ℕ) : coeff m (E c) = c ^ m / (m.factorial : ℂ) := by
  rw [E, coeff_rescale, coeff_exp]; simp [div_eq_mul_inv]

/-- `Σ_{S ⊆ A, |S| = k} exp((ΣS) t)`. -/
noncomputable def G (A : Finset ℂ) (k : ℕ) : ℂ⟦X⟧ := ∑ S ∈ A.powersetCard k, E (S.sum id)

/-- `Σ_{a ∈ A} exp(i a t)`. -/
noncomputable def P (A : Finset ℂ) (i : ℕ) : ℂ⟦X⟧ := ∑ a ∈ A, E ((i : ℂ) * a)

lemma sum_powersetCard_subtype {M : Type*} [AddCommMonoid M] (A : Finset ℂ) (r : ℕ)
    (F : ℂ → M) :
    ∑ t ∈ (univ : Finset A).powersetCard r, F (∑ i ∈ t, (i : ℂ)) =
      ∑ S ∈ A.powersetCard r, F (S.sum id) := by
  have hA : A.powersetCard r = ((univ : Finset A).powersetCard r).map
      (mapEmbedding (Function.Embedding.subtype (· ∈ A))).toEmbedding := by
    rw [← powersetCard_map, univ_eq_attach, attach_map_val]
  rw [hA, sum_map]
  refine sum_congr rfl fun t _ => ?_
  simp [mapEmbedding_apply, sum_map]

lemma newton (A : Finset ℂ) (k : ℕ) :
    (k : ℂ⟦X⟧) * G A k = ∑ i ∈ Icc 1 k, (-1) ^ (i + 1) * G A (k - i) * P A i := by
  have h := congrArg (MvPolynomial.aeval (fun a : A => E (a : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum A ℂ k)
  have hes : ∀ r, MvPolynomial.aeval (fun a : A => E (a : ℂ)) (MvPolynomial.esymm A ℂ r)
      = G A r := by
    intro r
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X, prod_E]
    exact sum_powersetCard_subtype A r E
  have hps : ∀ i, MvPolynomial.aeval (fun a : A => E (a : ℂ)) (MvPolynomial.psum A ℂ i)
      = P A i := by
    intro i
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, E_pow]
    exact sum_coe_sort A (fun a => E ((i : ℂ) * a))
  simp only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, hes, hps] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_nbij' (fun a => a.2) (fun i => (k - i, i)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    simp only [mem_Icc]; omega
  · intro i hi
    simp only [mem_Icc] at hi
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal]; omega
  · intro a ha
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    ext
    · simp; omega
    · simp
  · intro i _; rfl
  · intro a ha
    obtain ⟨a1, a2⟩ := a
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    obtain ⟨rfl, _⟩ := ha
    simp only
    have e1 : a1 + a2 - a2 = a1 := by omega
    rw [e1]
    have e2 : ((-1 : ℂ⟦X⟧) ^ (a1 + a2 + 1)) * (-1) ^ a1 = (-1) ^ (a2 + 1) := by
      rw [← pow_add, show a1 + a2 + 1 + a1 = 2 * a1 + (a2 + 1) by ring, pow_add, pow_mul,
        neg_one_sq, one_pow, one_mul]
    rw [← e2]; ring

/-- `q A k m = Σ_{S ⊆ A, |S| = k} (ΣS)^m`. -/
noncomputable def q (A : Finset ℂ) (k m : ℕ) : ℂ := ∑ S ∈ A.powersetCard k, (S.sum id) ^ m

lemma ksumPsum_eq (A : Finset ℂ) (k m : ℕ) : ksumPsum A k m = q A k m := by
  unfold ksumPsum sumMultiset q
  rw [Multiset.map_map]; rfl

lemma coeff_G (A : Finset ℂ) (k m : ℕ) : coeff m (G A k) = q A k m / (m.factorial : ℂ) := by
  simp only [G, map_sum, coeff_E, q, Finset.sum_div]

lemma coeff_P (A : Finset ℂ) (i v : ℕ) :
    coeff v (P A i) = (i : ℂ) ^ v * psum A v / (v.factorial : ℂ) := by
  simp only [P, map_sum, coeff_E, psum, Finset.mul_sum, Finset.sum_div, mul_pow]

lemma coeff_G_zero (A : Finset ℂ) (k : ℕ) : coeff 0 (G A k) = (A.card.choose k : ℂ) := by
  rw [coeff_G, q]; simp [card_powersetCard]

lemma coeff_P_zero (A : Finset ℂ) (i : ℕ) : coeff 0 (P A i) = (A.card : ℂ) := by
  rw [coeff_P]; simp [psum]

lemma G_zero (A : Finset ℂ) : G A 0 = 1 := by
  simp [G, E_zero]

/-- Coefficient form of Newton's identity. -/
lemma newton_coeff (A : Finset ℂ) (k m : ℕ) :
    (k : ℂ) * coeff m (G A k) = ∑ i ∈ Icc 1 k, (-1) ^ (i + 1) *
      ∑ x ∈ antidiagonal m, coeff x.1 (G A (k - i)) * coeff x.2 (P A i) := by
  have h := congrArg (coeff m) (newton A k)
  rw [← map_natCast (C (R := ℂ)) k, coeff_C_mul] at h
  rw [h, map_sum]
  refine sum_congr rfl fun i _ => ?_
  have : ((-1 : ℂ⟦X⟧) ^ (i + 1)) * G A (k - i) * P A i
      = C ((-1 : ℂ) ^ (i + 1)) * (G A (k - i) * P A i) := by
    simp [mul_assoc]
  rw [this, coeff_C_mul, coeff_mul]

end KSumAux

open KSumAux Finset PowerSeries in
theorem ksum_power_sum (A B : Finset ℂ) (n s j : ℕ) (hA : A.card = n) (hB : B.card = n)
    (hj : 1 ≤ j) (h : ∀ l, 1 ≤ l → l < j → psum A l = psum B l) :
    ksumPsum A s j - ksumPsum B s j = (gfsPoly s n j : ℂ) * (psum A j - psum B j) := by
  -- equality of the `P`-coefficients below order `j`
  have hP : ∀ i v, v < j → coeff v (P A i) = coeff v (P B i) := by
    intro i v hv
    rw [coeff_P, coeff_P]
    rcases Nat.eq_zero_or_pos v with rfl | hv0
    · simp [psum, hA, hB]
    · rw [h v hv0 hv]
  -- step 1: equality of the `G`-coefficients below order `j`
  have hlow : ∀ k, ∀ m, m < j → coeff m (G A k) = coeff m (G B k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [G_zero]
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk'
      rw [newton_coeff, newton_coeff]
      refine sum_congr rfl fun i hi => ?_
      have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
      congr 1
      refine sum_congr rfl fun x hx => ?_
      have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
      rw [ih (k - i) (by omega) x.1 (by omega), hP i x.2 (by omega)]
  -- step 2: the `t^j` coefficient
  set Δ := psum A j - psum B j with hΔ
  have hmain : ∀ k, coeff j (G A k) - coeff j (G B k) =
      (gfsPoly k n j : ℂ) * Δ / (j.factorial : ℂ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [G_zero, gfsPoly, coeff_one, show j ≠ 0 by omega]
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk'
      rw [mul_sub, newton_coeff, newton_coeff, ← sum_sub_distrib]
      have hrec := congrArg (fun z : ℤ => (z : ℂ)) (gfs_recursion n j k hj hk)
      push_cast at hrec
      have hterm : ∀ i ∈ Icc 1 k,
          (-1 : ℂ) ^ (i + 1) * ∑ x ∈ antidiagonal j, coeff x.1 (G A (k - i)) * coeff x.2 (P A i)
          - (-1 : ℂ) ^ (i + 1) *
            ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i)) * coeff x.2 (P B i)
          = (-1 : ℂ) ^ (i + 1) * ((n : ℂ) * (gfsPoly (k - i) n j : ℂ) +
              (n.choose (k - i) : ℂ) * (i : ℂ) ^ j) * Δ / (j.factorial : ℂ) := by
        intro i hi
        have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
        have hsplit : ∑ x ∈ antidiagonal j, coeff x.1 (G A (k - i)) * coeff x.2 (P A i)
            - ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i)) * coeff x.2 (P B i)
            = ∑ x ∈ antidiagonal j, (coeff x.1 (G A (k - i)) - coeff x.1 (G B (k - i)))
                * coeff x.2 (P A i)
              + ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i))
                * (coeff x.2 (P A i) - coeff x.2 (P B i)) := by
          rw [← sum_add_distrib, ← sum_sub_distrib]
          refine sum_congr rfl fun x _ => ?_
          ring
        have h1 : ∑ x ∈ antidiagonal j, (coeff x.1 (G A (k - i)) - coeff x.1 (G B (k - i)))
            * coeff x.2 (P A i) = (coeff j (G A (k - i)) - coeff j (G B (k - i))) * n := by
          rw [sum_eq_single (j, 0)]
          · simp [coeff_P_zero, hA]
          · intro x hx hne
            have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
            have : x.1 < j := by
              rcases Nat.lt_or_ge x.1 j with h' | h'
              · exact h'
              · exact absurd (Prod.ext (by simp; omega) (by simp; omega)) hne
            rw [hlow _ _ this, sub_self, zero_mul]
          · intro hn; exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn
        have h2 : ∑ x ∈ antidiagonal j, coeff x.1 (G B (k - i))
            * (coeff x.2 (P A i) - coeff x.2 (P B i))
            = (n.choose (k - i) : ℂ) * ((i : ℂ) ^ j * Δ / (j.factorial : ℂ)) := by
          rw [sum_eq_single (0, j)]
          · simp only [coeff_G_zero, hB, coeff_P, hΔ]
            ring
          · intro x hx hne
            have hx' := HasAntidiagonal.mem_antidiagonal.mp hx
            have : x.2 < j := by
              rcases Nat.lt_or_ge x.2 j with h' | h'
              · exact h'
              · exact absurd (Prod.ext (by simp; omega) (by simp; omega)) hne
            rw [hP _ _ this, sub_self, mul_zero]
          · intro hn; exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn
        rw [← mul_sub, hsplit, h1, h2, ih (k - i) (by omega)]
        ring
      rw [sum_congr rfl hterm]
      rw [← sum_div, ← sum_mul, mul_div_assoc, mul_div_assoc, ← mul_assoc]
      congr 1
      rw [hrec]
  have hfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hs := hmain s
  rw [coeff_G, coeff_G, ← sub_div, div_left_inj' hfac] at hs
  rw [ksumPsum_eq, ksumPsum_eq, hs]

end Erdos494
