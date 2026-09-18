import ErdosLean.Erdos494.Defs
import ErdosLean.Erdos494.Parts.AuxPolynomial
import ErdosLean.Erdos494.Parts.RothLemmaTwo
import ErdosLean.Erdos494.Parts.TaylorUpperBound
import ErdosLean.Erdos494.Parts.RationalLowerBound

/-! # Erdős 494, part D3: a Thue–Siegel–Dyson theorem for `θ = (b/a)^{1/r}`.

`|θ - p/q| < q^{-κ}` has only finitely many solutions when `κ ≥ 10 √r`.  (True by Roth for
every `κ > 2`; we prove the weak exponent `10√r` by Roth's method with **two** variables,
where Roth's lemma has the elementary Wronskian proof.)

Assembly: put `t = 1/(2√r)`, pick `η` with `4√η ≤ t/10`, `η ≤ 1`.  From an
infinite set of solutions extract two reduced solutions `p1/q1`, `p2/q2` with `q1` large and
`log q2 ≥ (2/η) log q1`.  Choose `r1` large and `r2 = ⌈r1 log q1 / log q2⌉`, so that
`16 r ≤ r2 ≤ η r1`, `q1^{r1} ≤ q2^{r2} ≤ q1^{(1+η) r1}`.  `aux_polynomial` gives `c` with
height `K^{r1+r2}` and index `≥ t` at `(θ,θ)`; `roth_lemma_two` gives `(i1,i2)` of weight
`< 4√η` with `D^{(i1,i2)}P(ξ) ≠ 0`; `rational_lower_bound` gives `|D P(ξ)| ≥ q1^{-(2+η) r1}`,
`taylor_upper_bound` with `Λ = q1^{-κ r1}` gives `|D P(ξ)| ≤ C^{r1} q1^{-κ r1 (t - 4√η)}`.
Since `κ (t - 4√η) ≥ 4.5 > 2 + η`, this is absurd for `q1` large. -/

namespace Erdos494

namespace DysonAux

/-- The solution predicate. -/
def Sol (θ κ : ℝ) (pq : ℤ × ℕ) : Prop :=
  0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ θ ∧ |θ - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)

lemma pow_eq_exp (y : ℝ) (hy : 0 < y) (n : ℕ) : y ^ n = Real.exp (n * Real.log y) := by
  rw [Real.exp_nat_mul, Real.exp_log hy]

lemma box_finite (T : Set (ℤ × ℕ)) (B : ℝ)
    (h : ∀ v ∈ T, |(v.1 : ℝ)| ≤ B ∧ (v.2 : ℝ) ≤ B) : T.Finite := by
  apply ((Set.finite_Icc (-(⌈B⌉₊ : ℤ)) (⌈B⌉₊ : ℤ)).prod (Set.finite_Iic ⌈B⌉₊)).subset
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  have h1' : ((|v.1| : ℤ) : ℝ) ≤ ((⌈B⌉₊ : ℤ) : ℝ) := by
    push_cast; exact h1.trans (Nat.le_ceil B)
  have h1'' : |v.1| ≤ (⌈B⌉₊ : ℤ) := by exact_mod_cast h1'
  have h2' : v.2 ≤ ⌈B⌉₊ := by exact_mod_cast h2.trans (Nat.le_ceil B)
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp h1''), Set.mem_Iic.mpr h2'⟩

lemma sol_abs_le (θ κ : ℝ) (hκ : 0 ≤ κ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (h : |θ - (p : ℝ) / q| < (q : ℝ) ^ (-κ)) : |(p : ℝ)| ≤ (|θ| + 1) * q := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq' (by linarith)
  have h2 : |(p : ℝ) / q| ≤ |θ| + 1 := by
    have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) θ
    rw [abs_sub_comm] at this
    linarith
  rw [abs_div, Nat.abs_cast, div_le_iff₀ (by linarith)] at h2
  exact h2

/-- Choice of the degrees `r1, r2`. -/
lemma choose_degrees (r : ℕ) (hr1 : (1 : ℝ) ≤ r) (η L1 L2 : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηM : η * (12800 * r) = 2) (hL1 : 0 < L1) (hcon : 12800 * (r : ℝ) * L1 ≤ L2) :
    ∃ r1 r2 : ℕ, 16 * r ≤ r2 ∧ r2 ≤ r1 ∧ 1 ≤ r1 ∧ 1 ≤ r2 ∧
      (r1 : ℝ) * L1 ≤ r2 * L2 ∧ (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) ∧ (r2 : ℝ) ≤ η * r1 := by
  have hM1 : (12800 : ℝ) ≤ 12800 * r := by linarith
  have hL2 : 0 < L2 := by
    have := mul_pos (by positivity : (0 : ℝ) < 12800 * r) hL1
    linarith
  set r1 := ⌈12800 * (r : ℝ) * (L2 / L1)⌉₊ with hr1def
  set r2 := ⌈(r1 : ℝ) * L1 / L2⌉₊ with hr2def
  have hρ : 12800 * (r : ℝ) ≤ L2 / L1 := (le_div_iff₀ hL1).mpr hcon
  have hR1 : 12800 * (r : ℝ) * (L2 / L1) ≤ r1 := Nat.le_ceil _
  have hR1L : 12800 * (r : ℝ) * L2 ≤ r1 * L1 := by
    have := mul_le_mul_of_nonneg_right hR1 hL1.le
    rwa [mul_assoc, div_mul_cancel₀ _ hL1.ne'] at this
  have hR1ge : 12800 * (r : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ L2 / L1 by linarith)
      (by positivity : (0 : ℝ) ≤ 12800 * r)
    linarith
  have hR2a : (r1 : ℝ) * L1 / L2 ≤ r2 := Nat.le_ceil _
  have hR2b : (r2 : ℝ) < r1 * L1 / L2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq12L : (r1 : ℝ) * L1 ≤ r2 * L2 := (div_le_iff₀ hL2).mp hR2a
  have hR2L2 : (r2 : ℝ) * L2 < r1 * L1 + L2 := by
    have := mul_lt_mul_of_pos_right hR2b hL2
    rwa [add_mul, div_mul_cancel₀ _ hL2.ne', one_mul] at this
  have hL2η : L2 ≤ η * (r1 * L1) := by
    have e : η * (12800 * r * L2) = 2 * L2 := by rw [← mul_assoc, hηM]
    have := mul_le_mul_of_nonneg_left hR1L hη0.le
    linarith
  have hR1L1 : 0 ≤ (r1 : ℝ) * L1 := by positivity
  have hupper : (r2 : ℝ) * L2 ≤ 2 * (r1 * L1) := by
    linarith [mul_le_mul_of_nonneg_right hη1 hR1L1]
  have hR2ge : 12800 * (r : ℝ) ≤ r2 := by
    have : 12800 * (r : ℝ) ≤ r1 * L1 / L2 := (le_div_iff₀ hL2).mpr hR1L
    linarith
  have hR2η : (r2 : ℝ) ≤ η * r1 := by
    have hsm : (r1 : ℝ) * L1 / L2 ≤ η * r1 / 2 := by
      rw [div_le_iff₀ hL2]
      have hL1le : L1 ≤ η / 2 * L2 := by
        have := mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ η / 2)
        have e : η / 2 * (12800 * r * L1) = L1 := by
          rw [show η / 2 * (12800 * r * L1) = (η * (12800 * r)) / 2 * L1 by ring, hηM]; ring
        linarith
      have := mul_le_mul_of_nonneg_left hL1le (by positivity : (0 : ℝ) ≤ r1)
      linarith
    have hηr1 : 2 ≤ η * r1 := by
      have := mul_le_mul_of_nonneg_left hR1ge hη0.le
      linarith
    linarith
  have hR21 : (r2 : ℝ) ≤ r1 := by
    have := mul_le_mul_of_nonneg_right hη1 (by positivity : (0 : ℝ) ≤ r1)
    linarith
  have h16 : 16 * r ≤ r2 := by
    have : ((16 * r : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  have h21 : r2 ≤ r1 := by exact_mod_cast hR21
  have hr1' : 1 ≤ r1 := by
    have : ((1 : ℕ) : ℝ) ≤ r1 := by push_cast; linarith
    exact_mod_cast this
  have hr2' : 1 ≤ r2 := by
    have : ((1 : ℕ) : ℝ) ≤ r2 := by push_cast; linarith
    exact_mod_cast this
  exact ⟨r1, r2, h16, h21, hr1', hr2', hq12L, hupper, hR2η⟩

/-- The final numerical contradiction. -/
lemma key_lt (r1 r2 q1 q2 : ℕ) (hq1R : (0 : ℝ) < q1) (hq2R : (0 : ℝ) < q2)
    (K θ κ t : ℝ) (hK1 : 1 ≤ K) (hR1pos : (0 : ℝ) < r1) (hR21 : (r2 : ℝ) ≤ r1)
    (hupper : (r2 : ℝ) * Real.log q2 ≤ 2 * (r1 * Real.log q1))
    (hκt : 9 / 2 ≤ κ * t)
    (hL1X : 8 + 4 * (Real.log 8 + Real.log K + Real.log (|θ| + 1)) < 3 * Real.log q1)
    (hL1 : 0 ≤ Real.log q1) :
    (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 *
      (((r1 : ℝ) + 1) ^ 2 * ((r2 : ℝ) + 1) ^ 2 * 8 ^ (r1 + r2) * K ^ (r1 + r2) *
        (|θ| + 1) ^ (r1 + r2) * ((q1 : ℝ) ^ (-(κ * r1))) ^ t) < 1 := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogθ : 0 ≤ Real.log (|θ| + 1) := Real.log_nonneg (by linarith [abs_nonneg θ])
  have hR1L1 : 0 ≤ (r1 : ℝ) * Real.log q1 := mul_nonneg hR1pos.le hL1
  have hb1 : ((r1 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r1) := by
    rw [show (2 : ℝ) * r1 = ((2 : ℕ) : ℝ) * r1 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r1 : ℝ)]
  have hb2 : ((r2 : ℝ) + 1) ^ 2 ≤ Real.exp (2 * r2) := by
    rw [show (2 : ℝ) * r2 = ((2 : ℕ) : ℝ) * r2 by norm_num, Real.exp_nat_mul]
    gcongr
    linarith [Real.add_one_le_exp (r2 : ℝ)]
  rw [pow_eq_exp _ hq1R, pow_eq_exp _ hq2R, pow_eq_exp 8 (by norm_num),
    pow_eq_exp K (by linarith), pow_eq_exp (|θ| + 1) (by positivity),
    ← Real.rpow_mul hq1R.le, Real.rpow_def_of_pos hq1R]
  calc _ ≤ Real.exp (r1 * Real.log q1) * Real.exp (r2 * Real.log q2) *
        (Real.exp (2 * r1) * Real.exp (2 * r2) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log 8) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log K) *
          Real.exp (((r1 + r2 : ℕ) : ℝ) * Real.log (|θ| + 1)) *
          Real.exp (Real.log q1 * (-(κ * r1) * t))) := by
        gcongr
    _ < 1 := by
        simp only [← Real.exp_add]
        rw [Real.exp_lt_one_iff]
        push_cast
        have e1 := mul_le_mul_of_nonneg_right hR21 hlog8
        have e2 := mul_le_mul_of_nonneg_right hR21 hlogK
        have e3 := mul_le_mul_of_nonneg_right hR21 hlogθ
        have e4 := mul_le_mul_of_nonneg_right hκt hR1L1
        have e5 := mul_lt_mul_of_pos_left hL1X hR1pos
        linarith

/-- The core: two reduced solutions with `q1` large force `log q2 < 12800 r log q1`. -/
lemma core (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) (κ : ℝ)
    (hκ : 10 * Real.sqrt r ≤ κ) :
    ∃ A : ℝ, ∀ (p1 p2 : ℤ) (q1 q2 : ℕ), 0 < q1 → 0 < q2 → IsCoprime p1 (q1 : ℤ) →
      IsCoprime p2 (q2 : ℤ) →
      |binRoot r a b - (p1 : ℝ) / q1| < (q1 : ℝ) ^ (-κ) →
      |binRoot r a b - (p2 : ℝ) / q2| < (q2 : ℝ) ^ (-κ) →
      A ≤ Real.log q1 → Real.log q2 < 12800 * r * Real.log q1 := by
  obtain ⟨K, hK1, hK⟩ := aux_polynomial r a b hr ha hb
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = binRoot r a b := ⟨_, rfl⟩
  rw [← hθ] at hK
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (r : ℝ) := ⟨_, rfl⟩
  rw [← hs] at hK hκ
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by linarith)
  have hss : s * s = r := by rw [hs]; exact Real.mul_self_sqrt (by linarith)
  have hκ0 : 0 < κ := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (6400 * r) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by positivity)]; linarith
  have hηM : η * (12800 * r) = 2 := by
    rw [hη, div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]; ring
  have hsqη : Real.sqrt η = 1 / (80 * s) := by
    rw [show η = (1 / (80 * s)) ^ 2 by rw [hη, ← hss]; ring]
    exact Real.sqrt_sq (by positivity)
  have hΘt : 4 * Real.sqrt η ≤ 1 / (2 * s) := by
    rw [hsqη, show 4 * (1 / (80 * s)) = 1 / (20 * s) by ring]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hκt : 9 / 2 ≤ κ * (1 / (2 * s) - 4 * Real.sqrt η) := by
    rw [hsqη, show 1 / (2 * s) - 4 * (1 / (80 * s)) = 9 / (20 * s) by field_simp; ring,
      ← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlogθ : 0 ≤ Real.log (|θ| + 1) := Real.log_nonneg (by linarith [abs_nonneg θ])
  have hlog64 : 0 ≤ Real.log 64 := Real.log_nonneg (by norm_num)
  set X := Real.log 8 + Real.log K + Real.log (|θ| + 1) with hX
  have hX0 : 0 ≤ X := by linarith
  refine ⟨1 + (Real.log 64 + 2 * Real.log K) / η + (8 + 4 * X) / 3, ?_⟩
  intro p1 p2 q1 q2 hq1 hq2 hcop1 hcop2 h1 h2 hA
  rw [← hθ] at h1 h2
  by_contra hcon
  push_neg at hcon
  have hq1R : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
  set L1 := Real.log (q1 : ℝ) with hL1def
  set L2 := Real.log (q2 : ℝ) with hL2def
  have hA1 : 0 ≤ (Real.log 64 + 2 * Real.log K) / η := by positivity
  have hA2 : 0 ≤ (8 + 4 * X) / 3 := by positivity
  have hL1 : 0 < L1 := by linarith
  have hηL1 : Real.log 64 + 2 * Real.log K ≤ η * L1 := by
    have : (Real.log 64 + 2 * Real.log K) / η ≤ L1 := by linarith
    rw [div_le_iff₀ hη0] at this; linarith
  have hL1X : 8 + 4 * X < 3 * L1 := by
    have : (8 + 4 * X) / 3 < L1 := by linarith
    linarith
  have hM1 : (12800 : ℝ) ≤ 12800 * r := by linarith
  have hL2 : 0 < L2 := by
    have := mul_pos (by positivity : (0 : ℝ) < 12800 * r) hL1
    linarith
  -- choice of r1, r2
  obtain ⟨r1, r2, h16, h21, hr1', hr2', hq12L, hupper, hR2η⟩ :=
    choose_degrees r hr1 η L1 L2 hη0 hη1 hηM hL1 hcon
  have hR21 : (r2 : ℝ) ≤ r1 := by exact_mod_cast h21
  have hR1L1 : 0 ≤ (r1 : ℝ) * L1 := by positivity
  have hR1pos : (0 : ℝ) < r1 := by exact_mod_cast hr1'
  have hR2pos : (0 : ℝ) < r2 := by exact_mod_cast hr2'
  -- auxiliary polynomial
  obtain ⟨c, hcnz, hcH, hcvan⟩ := hK r1 r2 h16 h21
  -- Roth's lemma
  have hq12 : (q1 : ℝ) ^ r1 ≤ (q2 : ℝ) ^ r2 := by
    rw [pow_eq_exp _ hq1R, pow_eq_exp _ hq2R]
    exact Real.exp_le_exp.mpr hq12L
  have hbig : (64 : ℝ) ^ r1 * K ^ (r1 + r2) ≤ (q1 : ℝ) ^ (η * r1) := by
    rw [pow_eq_exp 64 (by norm_num), pow_eq_exp K (by linarith), ← Real.exp_add,
      Real.rpow_def_of_pos hq1R]
    apply Real.exp_le_exp.mpr
    push_cast
    have e1 := mul_le_mul_of_nonneg_left hηL1 hR1pos.le
    have e2 := mul_le_mul_of_nonneg_right hR21 hlogK
    rw [← hL1def]
    linarith
  obtain ⟨i1, -, i2, -, hwt, hne⟩ := roth_lemma_two r1 r2 c (K ^ (r1 + r2)) η p1 p2 q1 q2
    hr2' hη0 hη1 hR2η hcnz hcH hq1 hq2 hcop1 hcop2 hq12 hbig
  -- Taylor upper bound
  have hvan : ∀ j1 j2 : ℕ, (j1 : ℝ) / r1 + (j2 : ℝ) / r2 < 1 / (2 * s) →
      hasseEval r1 r2 c j1 j2 θ θ = 0 := by
    intro j1 j2 hj
    exact hcvan j1 j2 ((lt_div_iff₀ (by positivity)).mp hj)
  have hΛ0 : 0 < (q1 : ℝ) ^ (-(κ * r1)) := Real.rpow_pos_of_pos hq1R _
  have hΛ1 : (q1 : ℝ) ^ (-(κ * r1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq1) (by nlinarith)
  have hx : |(p1 : ℝ) / q1 - θ| ≤ ((q1 : ℝ) ^ (-(κ * r1))) ^ ((1 : ℝ) / r1) := by
    rw [← Real.rpow_mul hq1R.le, show -(κ * (r1 : ℝ)) * (1 / r1) = -κ by field_simp,
      abs_sub_comm]
    exact h1.le
  have hy : |(p2 : ℝ) / q2 - θ| ≤ ((q1 : ℝ) ^ (-(κ * r1))) ^ ((1 : ℝ) / r2) := by
    rw [← Real.rpow_mul hq1R.le, abs_sub_comm]
    refine h2.le.trans ?_
    rw [Real.rpow_def_of_pos hq2R, Real.rpow_def_of_pos hq1R]
    apply Real.exp_le_exp.mpr
    rw [← hL1def, ← hL2def,
      show L1 * (-(κ * (r1 : ℝ)) * (1 / r2)) = -(κ * (r1 * L1)) / r2 by field_simp,
      le_div_iff₀ hR2pos]
    linarith [mul_le_mul_of_nonneg_left hq12L hκ0.le]
  have hT := taylor_upper_bound r1 r2 hr1' hr2' c (K ^ (r1 + r2)) hcH θ (1 / (2 * s))
    (4 * Real.sqrt η) ((q1 : ℝ) ^ (-(κ * r1))) hvan i1 i2 hwt.le hΘt hΛ0 hΛ1 _ _ hx hy
  have hL := rational_lower_bound r1 r2 c i1 i2 p1 p2 q1 q2 hq1 hq2 hne
  set D := hasseEval r1 r2 c i1 i2 ((p1 : ℝ) / q1) ((p2 : ℝ) / q2)
  have hQ0 : 0 ≤ (q1 : ℝ) ^ r1 * (q2 : ℝ) ^ r2 := by positivity
  have key := key_lt r1 r2 q1 q2 hq1R hq2R K θ κ (1 / (2 * s) - 4 * Real.sqrt η) hK1 hR1pos
    hR21 hupper hκt hL1X hL1.le
  have := mul_le_mul_of_nonneg_left hT hQ0
  linarith

end DysonAux

open DysonAux in
theorem dyson_binomial (r a b : ℕ) (hr : 1 ≤ r) (ha : 0 < a) (hb : 0 < b) (κ : ℝ)
    (hκ : 10 * Real.sqrt r ≤ κ) :
    {pq : ℤ × ℕ | 0 < pq.2 ∧ (pq.1 : ℝ) / pq.2 ≠ binRoot r a b ∧
        |binRoot r a b - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-κ)}.Finite := by
  obtain ⟨A, hA⟩ := core r a b hr ha hb κ hκ
  have hκ0 : 0 < κ := by
    have : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
    linarith
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = binRoot r a b := ⟨_, rfl⟩
  rw [← hθ] at hA ⊢
  change {pq : ℤ × ℕ | Sol θ κ pq}.Finite
  set R : Set (ℤ × ℕ) := {pq | Sol θ κ pq ∧ IsCoprime pq.1 (pq.2 : ℤ)} with hR
  have hRbd : ∃ B : ℝ, ∀ v ∈ R, (v.2 : ℝ) ≤ B := by
    by_cases h : ∃ v ∈ R, A ≤ Real.log v.2
    · obtain ⟨⟨p1, q1⟩, ⟨⟨hq1, -, h1⟩, hc1⟩, hL⟩ := h
      refine ⟨Real.exp (12800 * r * Real.log q1), ?_⟩
      rintro ⟨p2, q2⟩ ⟨⟨hq2, -, h2⟩, hc2⟩
      have := hA p1 p2 q1 q2 hq1 hq2 hc1 hc2 h1 h2 hL
      have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
      rw [← Real.exp_log hq2R]
      exact (Real.exp_lt_exp.mpr this).le
    · push_neg at h
      refine ⟨Real.exp A, ?_⟩
      rintro ⟨p, q⟩ hv
      have hqR : (0 : ℝ) < q := by exact_mod_cast hv.1.1
      rw [← Real.exp_log hqR]
      exact (Real.exp_lt_exp.mpr (h _ hv)).le
  obtain ⟨B, hB⟩ := hRbd
  have hRfin : R.Finite := by
    apply box_finite R ((|θ| + 1) * |B| + |B|)
    rintro ⟨p, q⟩ hv
    have hq := hB _ hv
    have hqB : (q : ℝ) ≤ |B| := hq.trans (le_abs_self B)
    have hp := sol_abs_le θ κ hκ0.le p q hv.1.1 hv.1.2.2
    have : (|θ| + 1) * (q : ℝ) ≤ (|θ| + 1) * |B| :=
      mul_le_mul_of_nonneg_left hqB (by positivity)
    have : 0 ≤ (|θ| + 1) * |B| := by positivity
    exact ⟨by simp only; linarith [abs_nonneg B], by simp only; linarith⟩
  -- fibres
  let F : ℤ × ℕ → Set (ℤ × ℕ) :=
    fun v => {w | Sol θ κ w ∧ (w.1 : ℝ) / w.2 = (v.1 : ℝ) / v.2}
  have hFfin : ∀ v ∈ R, (F v).Finite := by
    rintro ⟨p0, q0⟩ hv
    have hδ : 0 < |θ - (p0 : ℝ) / q0| :=
      abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hv.1.2.1))
    set E := Real.exp (-Real.log |θ - (p0 : ℝ) / q0| / κ) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    apply box_finite _ ((|θ| + 1) * E + E)
    rintro ⟨p, q⟩ ⟨hw, hpq⟩
    simp only at hpq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hw.1
    have hlt : |θ - (p0 : ℝ) / q0| < (q : ℝ) ^ (-κ) := by rw [← hpq]; exact hw.2.2
    have hlog : Real.log |θ - (p0 : ℝ) / q0| < Real.log q * (-κ) := by
      rw [← Real.exp_lt_exp, Real.exp_log hδ, ← Real.rpow_def_of_pos hqR]; exact hlt
    have hlq : Real.log q < -Real.log |θ - (p0 : ℝ) / q0| / κ := by
      rw [lt_div_iff₀ hκ0]; linarith
    have hqE : (q : ℝ) ≤ E := by
      rw [← Real.exp_log hqR, hE]; exact (Real.exp_lt_exp.mpr hlq).le
    have hp := sol_abs_le θ κ hκ0.le p q hw.1 hw.2.2
    have : (|θ| + 1) * (q : ℝ) ≤ (|θ| + 1) * E :=
      mul_le_mul_of_nonneg_left hqE (by positivity)
    have : 0 ≤ (|θ| + 1) * E := by positivity
    exact ⟨by simp only; linarith, by simp only; linarith⟩
  refine (hRfin.biUnion hFfin).subset ?_
  rintro ⟨p, q⟩ hw
  have hq : 0 < q := hw.1
  set x : ℚ := Rat.divInt p q with hx
  have hval : (x.num : ℝ) / (x.den : ℝ) = (p : ℝ) / q := by
    rw [← Rat.cast_def, hx, ← Rat.intCast_div_eq_divInt]
    push_cast; rfl
  have hden : x.den ≤ q := by
    have h1 : ((x.den : ℤ)) ∣ (q : ℤ) := Rat.den_dvd p q
    have h2 : (x.den : ℤ) ≤ (q : ℤ) := Int.le_of_dvd (by exact_mod_cast hq) h1
    exact_mod_cast h2
  have hdenpos : 0 < x.den := x.den_pos
  refine Set.mem_biUnion (x := (x.num, x.den)) ?_ ?_
  · refine ⟨⟨hdenpos, ?_, ?_⟩, Rat.isCoprime_num_den x⟩
    · show (x.num : ℝ) / (x.den : ℝ) ≠ θ
      rw [hval]; exact hw.2.1
    · show |θ - (x.num : ℝ) / (x.den : ℝ)| < ((x.den : ℕ) : ℝ) ^ (-κ)
      rw [hval]
      refine lt_of_lt_of_le hw.2.2 ?_
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hdenpos)
        (by exact_mod_cast hden) (by linarith)
  · exact ⟨hw, hval.symm⟩

end Erdos494
