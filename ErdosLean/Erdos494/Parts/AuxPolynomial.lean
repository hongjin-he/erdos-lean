import ErdosLean.Erdos494.Defs

/-! # Erdős 494, part D4: the auxiliary polynomial (Siegel's lemma).

With `θ = (b/a)^{1/r}` and `t = 1/(2√r)`: for `16 r ≤ r2 ≤ r1` there is a nonzero integer
polynomial of bidegree `≤ (r1, r2)`, height `≤ K^{r1+r2}`, all of whose Hasse derivatives of
weight `i1/r1 + i2/r2 < t` vanish at `(θ, θ)`.

Route: each derivative at `(θ,θ)` is `Σ_e L_e(c) θ^e`; reduce `θ^e = (b/a)^{⌊e/r⌋} θ^{e mod r}`
and require the `r` rational coordinates to vanish (sufficient, even if `θ` has degree `< r`);
clear denominators by `a^{⌊(r1+r2)/r⌋}`.  #conditions `≤ r (t r1 + 1)(t r2 + 1) ≤ (9/16)^2 r1 r2`
`< (r1+1)(r2+1)/2`, entries `≤ 2^{r1+r2} (ab)^{r1+r2+1}`; apply
`Int.Matrix.exists_ne_zero_int_vec_norm_le` (Mathlib, `NumberTheory/SiegelsLemma`). -/

namespace Erdos494

open Finset Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

lemma binRoot_pow' (r a b : ℕ) (hr : 1 ≤ r) : binRoot r a b ^ r = (b : ℝ) / a := by
  unfold binRoot
  rw [one_div]
  exact Real.rpow_inv_natCast_pow (by positivity) (by omega)

lemma binRoot_pos' (r a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < binRoot r a b := by
  unfold binRoot
  exact Real.rpow_pos_of_pos (div_pos (by exact_mod_cast hb) (by exact_mod_cast ha)) _

/-- Integer matrix entry: row `(s, i1, i2)`, column `(k1, k2)`. -/
def auxEntryN (r a b r1 r2 : ℕ) (s i1 i2 k1 k2 : ℕ) : ℕ :=
  if (k1 + k2) % r = s then
    k1.choose i1 * k2.choose i2 * b ^ ((k1 + k2) / r) * a ^ ((r1 + r2) / r - (k1 + k2) / r)
  else 0

lemma auxEntryN_le (r a b r1 r2 s i1 i2 k1 k2 : ℕ) (ha : 0 < a) (hk1 : k1 ≤ r1) (hk2 : k2 ≤ r2) :
    auxEntryN r a b r1 r2 s i1 i2 k1 k2 ≤ (2 * max a b) ^ (r1 + r2) := by
  unfold auxEntryN
  split_ifs
  · set q := (k1 + k2) / r
    set Q := (r1 + r2) / r
    have hqQ : q ≤ Q := Nat.div_le_div_right (by omega)
    have hQ : Q ≤ r1 + r2 := Nat.div_le_self _ _
    have hM : 1 ≤ max a b := le_trans ha (le_max_left _ _)
    have h1 : k1.choose i1 ≤ 2 ^ r1 :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hk1)
    have h2 : k2.choose i2 ≤ 2 ^ r2 :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hk2)
    have h3 : b ^ q ≤ max a b ^ q := Nat.pow_le_pow_left (le_max_right _ _) _
    have h4 : a ^ (Q - q) ≤ max a b ^ (Q - q) := Nat.pow_le_pow_left (le_max_left _ _) _
    have h5 : max a b ^ q * max a b ^ (Q - q) ≤ max a b ^ (r1 + r2) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hM (by omega)
    calc k1.choose i1 * k2.choose i2 * b ^ q * a ^ (Q - q)
        = (k1.choose i1 * k2.choose i2) * (b ^ q * a ^ (Q - q)) := by ring
      _ ≤ (2 ^ r1 * 2 ^ r2) * (max a b ^ q * max a b ^ (Q - q)) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
      _ ≤ (2 ^ r1 * 2 ^ r2) * max a b ^ (r1 + r2) := Nat.mul_le_mul le_rfl h5
      _ = (2 * max a b) ^ (r1 + r2) := by rw [mul_pow, ← pow_add]
  · exact Nat.zero_le _

lemma aux_col_identity (r a b r1 r2 i1 i2 k1 k2 : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (_hb : 0 < b)
    (hk : k1 + k2 ≤ r1 + r2) :
    ∑ s : Fin r, binRoot r a b ^ (s : ℕ) * ((auxEntryN r a b r1 r2 s i1 i2 k1 k2 : ℕ) : ℝ) =
      (a : ℝ) ^ ((r1 + r2) / r) * binRoot r a b ^ (i1 + i2) *
        ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ) * binRoot r a b ^ (k1 - i1) *
          binRoot r a b ^ (k2 - i2)) := by
  set θ := binRoot r a b with hθ
  set q := (k1 + k2) / r
  set Q := (r1 + r2) / r
  have hqQ : q ≤ Q := Nat.div_le_div_right hk
  have hmod : (k1 + k2) % r < r := Nat.mod_lt _ (by omega)
  rw [Finset.sum_eq_single (⟨(k1 + k2) % r, hmod⟩ : Fin r)]
  · simp only [auxEntryN]
    by_cases h1 : i1 ≤ k1
    · by_cases h2 : i2 ≤ k2
      · have hθk : θ ^ (i1 + i2) * (θ ^ (k1 - i1) * θ ^ (k2 - i2)) = θ ^ (k1 + k2) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        have he : θ ^ (k1 + k2) = ((b : ℝ) / a) ^ q * θ ^ ((k1 + k2) % r) := by
          rw [← binRoot_pow' r a b hr, ← pow_mul, ← pow_add, Nat.div_add_mod]
        have hQq : (a : ℝ) ^ Q = (a : ℝ) ^ (Q - q) * (a : ℝ) ^ q := by
          rw [← pow_add, Nat.sub_add_cancel hqQ]
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
        calc θ ^ ((k1 + k2) % r) *
              (((k1.choose i1 * k2.choose i2 * b ^ q * a ^ (Q - q) : ℕ)) : ℝ)
            = (a : ℝ) ^ (Q - q) * ((a : ℝ) ^ q * ((b : ℝ) / a) ^ q) * θ ^ ((k1 + k2) % r) *
                ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ)) := by
              rw [← mul_pow, mul_div_cancel₀ _ ha']; push_cast; ring
          _ = (a : ℝ) ^ Q * (θ ^ (i1 + i2) * (θ ^ (k1 - i1) * θ ^ (k2 - i2))) *
                ((k1.choose i1 : ℝ) * (k2.choose i2 : ℝ)) := by
              rw [hθk, he, hQq]; ring
          _ = _ := by ring
      · have : k2.choose i2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [this]
    · have : k1.choose i1 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  · intro s _ hs
    have : (k1 + k2) % r ≠ (s : ℕ) := by
      intro h; apply hs; ext; exact h.symm
    simp [auxEntryN, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem aux_polynomial (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r1 r2 : ℕ, 16 * r ≤ r2 → r2 ≤ r1 →
      ∃ c : ℕ → ℕ → ℤ, BoxNonzero r1 r2 c ∧ (∀ k1 k2, |(c k1 k2 : ℝ)| ≤ K ^ (r1 + r2)) ∧
        ∀ i1 i2 : ℕ, ((i1 : ℝ) / r1 + (i2 : ℝ) / r2) * (2 * Real.sqrt r) < 1 →
          hasseEval r1 r2 c i1 i2 (binRoot r a b) (binRoot r a b) = 0 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  refine ⟨4 * ((max a b : ℕ) : ℝ), ?_, ?_⟩
  · have : (a : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_left a b
    linarith
  intro r1 r2 h16 h21
  set θ := binRoot r a b with hθ
  have hθpos : 0 < θ := binRoot_pos' r a b ha hb
  set sr := Real.sqrt (r : ℝ) with hsr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsr1 : 1 ≤ sr := by rw [hsr]; exact Real.one_le_sqrt.mpr hrR
  have hsrsq : sr * sr = r := Real.mul_self_sqrt (by positivity)
  have hsr_le : sr ≤ r := by nlinarith
  have hr1R : (16 : ℝ) * r ≤ r2 := by exact_mod_cast h16
  have hr21R : (r2 : ℝ) ≤ r1 := by exact_mod_cast h21
  set N1 := ⌈(r1 : ℝ) / (2 * sr)⌉₊ with hN1
  set N2 := ⌈(r2 : ℝ) / (2 * sr)⌉₊ with hN2
  have h2sr : 0 < 2 * sr := by linarith
  have hN1pos : 0 < N1 := Nat.ceil_pos.mpr (div_pos (by linarith) h2sr)
  have hN2pos : 0 < N2 := Nat.ceil_pos.mpr (div_pos (by linarith) h2sr)
  have hN1le : (N1 : ℝ) ≤ (r1 : ℝ) / (2 * sr) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hN2le : (N2 : ℝ) ≤ (r2 : ℝ) / (2 * sr) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  -- counting
  have hcountR : 2 * ((r : ℝ) * N1 * N2) ≤ ((r1 : ℝ) + 1) * ((r2 : ℝ) + 1) := by
    set x := (r1 : ℝ) / (2 * sr) with hx
    set y := (r2 : ℝ) / (2 * sr) with hy
    have hx2 : x * (2 * sr) = r1 := div_mul_cancel₀ _ h2sr.ne'
    have hy2 : y * (2 * sr) = r2 := div_mul_cancel₀ _ h2sr.ne'
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hb1 : (r : ℝ) * N1 * N2 ≤ r * (x + 1) * (y + 1) := by
      have := mul_le_mul hN1le hN2le (Nat.cast_nonneg _) (by positivity)
      calc (r : ℝ) * N1 * N2 = r * (N1 * N2) := by ring
        _ ≤ r * ((x + 1) * (y + 1)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hb2 : 4 * ((r : ℝ) * (x + 1) * (y + 1)) =
        r1 * r2 + 2 * sr * (r1 + r2) + 4 * r := by
      rw [← hx2, ← hy2, ← hsrsq]; ring
    have h16sr : 16 * sr ≤ r2 := by linarith
    nlinarith
  have hcount : 2 * (r * N1 * N2) ≤ (r1 + 1) * (r2 + 1) := by exact_mod_cast hcountR
  -- the matrix
  let A : Matrix (Fin r × Fin N1 × Fin N2) (Fin (r1 + 1) × Fin (r2 + 1)) ℤ :=
    fun p k => ((auxEntryN r a b r1 r2 p.1 p.2.1 p.2.2 k.1 k.2 : ℕ) : ℤ)
  have hcardα : Fintype.card (Fin r × Fin N1 × Fin N2) = r * N1 * N2 := by
    simp [Fintype.card_prod, mul_assoc]
  have hcardβ : Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) = (r1 + 1) * (r2 + 1) := by
    simp [Fintype.card_prod]
  have hm : 0 < Fintype.card (Fin r × Fin N1 × Fin N2) := by
    rw [hcardα]; positivity
  have hn : Fintype.card (Fin r × Fin N1 × Fin N2) < Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) := by
    rw [hcardα, hcardβ]
    have : 0 < r * N1 * N2 := by positivity
    omega
  obtain ⟨t, ht0, hAt, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm
  -- norm bound on A
  set M : ℕ := max a b with hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans ha (le_max_left a b)
  have hAnorm : ‖A‖ ≤ ((2 : ℝ) * M) ^ (r1 + r2) := by
    rw [Matrix.norm_le_iff (by positivity)]
    intro p k
    simp only [A, Int.norm_natCast]
    have := auxEntryN_le r a b r1 r2 p.1 p.2.1 p.2.2 k.1 k.2 ha (Nat.lt_succ_iff.mp k.1.isLt)
      (Nat.lt_succ_iff.mp k.2.isLt)
    exact_mod_cast this
  have hexp : ((Fintype.card (Fin r × Fin N1 × Fin N2) : ℕ) : ℝ) /
      ((Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) : ℕ) - (Fintype.card (Fin r × Fin N1 × Fin N2) : ℕ)) ≤ 1 := by
    rw [hcardα, hcardβ]
    have hc : (2 : ℝ) * ((r * N1 * N2 : ℕ) : ℝ) ≤ (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hpos : (0 : ℝ) < ((r * N1 * N2 : ℕ) : ℝ) := by
      have : 0 < r * N1 * N2 := by positivity
      exact_mod_cast this
    rw [div_le_one (by linarith)]
    linarith
  have hnle : (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r1 + r2) := by
    have h1 : r1 + 1 ≤ 2 ^ r1 := Nat.lt_two_pow_self
    have h2 : r2 + 1 ≤ 2 ^ r2 := Nat.lt_two_pow_self
    have : (r1 + 1) * (r2 + 1) ≤ 2 ^ (r1 + r2) := by
      rw [pow_add]; exact Nat.mul_le_mul h1 h2
    exact_mod_cast this
  have hbase1 : (1 : ℝ) ≤ (Fintype.card (Fin (r1 + 1) × Fin (r2 + 1)) : ℝ) * max 1 ‖A‖ := by
    rw [hcardβ]
    have : (1 : ℝ) ≤ (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) := by
      have : 1 ≤ (r1 + 1) * (r2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    nlinarith [le_max_left (1 : ℝ) ‖A‖]
  have htn' : ‖t‖ ≤ (4 * (M : ℝ)) ^ (r1 + r2) := by
    refine htn.trans ?_
    refine (Real.rpow_le_rpow_of_exponent_le hbase1 hexp).trans ?_
    rw [Real.rpow_one, hcardβ]
    have hmax : max 1 ‖A‖ ≤ ((2 : ℝ) * M) ^ (r1 + r2) :=
      max_le (one_le_pow₀ (by linarith)) hAnorm
    calc (((r1 + 1) * (r2 + 1) : ℕ) : ℝ) * max 1 ‖A‖
        ≤ (2 : ℝ) ^ (r1 + r2) * ((2 : ℝ) * M) ^ (r1 + r2) :=
          mul_le_mul hnle hmax (by positivity) (by positivity)
      _ = (4 * (M : ℝ)) ^ (r1 + r2) := by rw [← mul_pow]; ring
  -- the polynomial
  let c : ℕ → ℕ → ℤ := fun k1 k2 =>
    if h : k1 ≤ r1 ∧ k2 ≤ r2 then t (⟨k1, Nat.lt_succ_of_le h.1⟩, ⟨k2, Nat.lt_succ_of_le h.2⟩)
    else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · -- nonzero
    obtain ⟨⟨k1, k2⟩, hk⟩ := Function.ne_iff.mp ht0
    refine ⟨k1, Nat.lt_succ_iff.mp k1.isLt, k2, Nat.lt_succ_iff.mp k2.isLt, ?_⟩
    simp only [c, dif_pos (And.intro (Nat.lt_succ_iff.mp k1.isLt) (Nat.lt_succ_iff.mp k2.isLt))]
    simpa using hk
  · intro k1 k2
    simp only [c]
    split_ifs with h
    · have := (norm_le_pi_norm t (⟨k1, Nat.lt_succ_of_le h.1⟩, ⟨k2, Nat.lt_succ_of_le h.2⟩)).trans htn'
      rw [Int.norm_eq_abs] at this
      exact this
    · simp only [Int.cast_zero, abs_zero]; positivity
  · intro i1 i2 hw
    have hr1pos : (0 : ℝ) < r1 := by linarith
    have hr2pos : (0 : ℝ) < r2 := by linarith
    have hi1 : i1 < N1 := by
      rw [hN1, Nat.lt_ceil, lt_div_iff₀ h2sr]
      have : (i1 : ℝ) / r1 * (2 * sr) < 1 := by
        have : 0 ≤ (i2 : ℝ) / r2 * (2 * sr) := by positivity
        nlinarith
      rw [div_mul_eq_mul_div, div_lt_one hr1pos] at this
      exact this
    have hi2 : i2 < N2 := by
      rw [hN2, Nat.lt_ceil, lt_div_iff₀ h2sr]
      have : (i2 : ℝ) / r2 * (2 * sr) < 1 := by
        have : 0 ≤ (i1 : ℝ) / r1 * (2 * sr) := by positivity
        nlinarith
      rw [div_mul_eq_mul_div, div_lt_one hr2pos] at this
      exact this
    have hrow : ∀ s : Fin r, (A *ᵥ t) (s, ⟨i1, hi1⟩, ⟨i2, hi2⟩) = 0 := fun s => by
      rw [hAt]; rfl
    have hH : hasseEval r1 r2 c i1 i2 θ θ =
        ∑ k : Fin (r1 + 1) × Fin (r2 + 1), (t k : ℝ) *
          ((((k.1 : ℕ).choose i1 : ℕ) : ℝ) * (((k.2 : ℕ).choose i2 : ℕ) : ℝ) *
            θ ^ ((k.1 : ℕ) - i1) * θ ^ ((k.2 : ℕ) - i2)) := by
      unfold hasseEval
      rw [Fintype.sum_prod_type, Finset.sum_range]
      refine Finset.sum_congr rfl fun k1 _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun k2 _ => ?_
      simp only [c, dif_pos (And.intro (Nat.lt_succ_iff.mp k1.isLt) (Nat.lt_succ_iff.mp k2.isLt))]
      ring
    have hkey : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) * hasseEval r1 r2 c i1 i2 θ θ =
        ∑ s : Fin r, θ ^ (s : ℕ) * (((A *ᵥ t) (s, ⟨i1, hi1⟩, ⟨i2, hi2⟩) : ℤ) : ℝ) := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      rw [Finset.sum_comm, hH, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (k.1 : ℕ) + k.2 ≤ r1 + r2 := by
        have := k.1.isLt; have := k.2.isLt; omega
      have hcol := aux_col_identity r a b r1 r2 i1 i2 k.1 k.2 hr ha hb hk
      rw [← hθ] at hcol
      simp only [A, Int.cast_natCast]
      calc (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) *
            ((t k : ℝ) * ((((k.1 : ℕ).choose i1 : ℕ) : ℝ) * (((k.2 : ℕ).choose i2 : ℕ) : ℝ) *
              θ ^ ((k.1 : ℕ) - i1) * θ ^ ((k.2 : ℕ) - i2)))
          = (t k : ℝ) * ∑ s : Fin r, θ ^ (s : ℕ) *
              ((auxEntryN r a b r1 r2 s i1 i2 k.1 k.2 : ℕ) : ℝ) := by
            rw [hcol]; ring
        _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
    have hzero : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) * hasseEval r1 r2 c i1 i2 θ θ = 0 := by
      rw [hkey]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hrow s]; simp
    have hne : (a : ℝ) ^ ((r1 + r2) / r) * θ ^ (i1 + i2) ≠ 0 := by
      have : (0 : ℝ) < a := by linarith
      positivity
    exact (mul_eq_zero.mp hzero).resolve_left hne

end Erdos494
