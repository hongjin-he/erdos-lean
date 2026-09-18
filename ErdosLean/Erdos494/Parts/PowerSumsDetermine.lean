import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part A1: power sums `p_1, …, p_n` determine an `n`-element subset of `ℂ`.

Route: Newton's identities (`MvPolynomial.psum_eq_mul_esymm_sub_sum`,
`MvPolynomial.mul_esymm_eq_sum`) give `e_1, …, e_n` from `p_1, …, p_n` (char 0), hence
`∏_{a∈A} (X - a) = ∏_{b∈B} (X - b)` (`Multiset.prod_X_sub_C_eq_sum_esymm`), hence
`A.val = B.val` via `Polynomial.roots_multiset_prod_X_sub_C`. -/

namespace Erdos494

open Finset

/-- Newton's identity for a finite subset of `ℂ`, stated with `Multiset.esymm` and `psum`. -/
lemma newton_finset (S : Finset ℂ) (k : ℕ) :
    (k : ℂ) * S.val.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * S.val.esymm a.1 * psum S a.2 := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : S => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum S ℂ k)
  have hv : (Finset.univ : Finset S).val.map (fun x : S => (x : ℂ)) = S.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val _
  have he : ∀ m, MvPolynomial.aeval (fun x : S => (x : ℂ)) (MvPolynomial.esymm S ℂ m)
      = S.val.esymm m := by
    intro m; rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hv]
  have hp : ∀ m, MvPolynomial.aeval (fun x : S => (x : ℂ)) (MvPolynomial.psum S ℂ m)
      = psum S m := by
    intro m
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, psum]
    exact Finset.sum_coe_sort S (fun a => a ^ m)
  simpa [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, he, hp] using h

theorem power_sums_determine (A B : Finset ℂ) (n : ℕ) (hA : A.card = n) (hB : B.card = n)
    (h : ∀ j, 1 ≤ j → j ≤ n → psum A j = psum B j) : A = B := by
  -- elementary symmetric functions agree up to `n`
  have hE : ∀ k, k ≤ n → A.val.esymm k = B.val.esymm k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [Multiset.esymm]
      have hA' := newton_finset A k
      have hB' := newton_finset B k
      have hsum : ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * A.val.esymm a.1 * psum A a.2
          = ∑ a ∈ antidiagonal k with a.1 < k, (-1 : ℂ) ^ a.1 * B.val.esymm a.1 * psum B a.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [ih a.1 ha.2 (by omega), h a.2 (by omega) (by omega)]
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
      apply mul_left_cancel₀ hk0
      rw [hA', hB', hsum]
  -- hence the monic polynomials `∏ (X - a)` agree
  have hpoly : (A.val.map fun t => Polynomial.X - Polynomial.C t).prod
      = (B.val.map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    have hcA : Multiset.card A.val = n := hA
    have hcB : Multiset.card B.val = n := hB
    rw [hcA, hcB]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hE j (by simpa [Nat.lt_succ_iff] using hj)]
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  exact Finset.val_inj.mp hroots

end Erdos494
