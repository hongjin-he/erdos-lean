import ErdosLean.DuffinSchaeffer.Defs

/-!
# Duffin–Schaeffer — Part 6: counting pairs of reduced residues (CRT)

With `g = gcd(q,r)`, `q = g q'`, `r = g r'`, `m = q' r'`, the number
`N(h)` of pairs `(a mod q, b mod r)` of reduced residues with `a r' - b q' ≡ h (mod lcm(q,r))`
vanishes unless `gcd(h, m) = 1`, and then
`N(h) ≤ g · (φ(q)/q) · (φ(r)/r) · (m/φ(m)) · (d/φ(d))`, `d = gcd(h, g)`.
(Exact CRT count: `a` is fixed mod `q'`, and the `g` lifts are constrained only mod primes `p | g`.)
The case `q = r` (`g = q`, `m = 1`) is used for the lower bound on `λ(A_q)`.

Proof outline.  If `(a₀, b₀)` is one solution, every solution is
`((a₀ + q' t) mod q, (b₀ + r' t) mod r)` for some `t ∈ [0, g)`, and `t` must avoid, for every
prime `p | g`, the roots mod `p` of `F(t) = (a₀ + q' t)(b₀ + r' t)`.  A CRT sieve counts these
`t` exactly as `(g / rad g) ∏_{p | g} #{x < p : p ∤ F x}`; there is at least one root mod `p`, and
two distinct ones unless `p | q' r' h`.  The right-hand side equals
`g ∏_{p | g} (1 - 1/p)^2 / (the factors (1 - 1/p) for p | q', p | r', p | d)`.
-/

open Finset

namespace DuffinSchaeffer

namespace UnitPairCountAux

/-- Counting in blocks: a condition depending only on `s mod d`. -/
lemma card_filter_range_mul_mod (Q : ℕ → Prop) [DecidablePred Q] (d k : ℕ) :
    ((range (d * k)).filter (fun s => Q (s % d))).card = k * ((range d).filter Q).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, Finset.card_filter, Finset.sum_range_add, ← Finset.card_filter, ih,
      Finset.card_filter (p := Q)]
    have : ∀ x ∈ range d, (if Q ((d * k + x) % d) then 1 else 0) = (if Q x then 1 else 0) := by
      intro x hx
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx)]
    rw [Finset.sum_congr rfl this]
    ring

/-- The Chinese remainder theorem for counting. -/
lemma card_filter_crt (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (co : Nat.Coprime m n)
    (Q1 Q2 : ℕ → Prop) [DecidablePred Q1] [DecidablePred Q2] :
    ((range (m * n)).filter (fun s => Q1 (s % m) ∧ Q2 (s % n))).card =
      ((range m).filter Q1).card * ((range n).filter Q2).card := by
  rw [← card_product]
  refine card_bij (fun s _ => (s % m, s % n)) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_range, mem_product] at hs ⊢
    exact ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), hs.2.1⟩,
      Nat.mod_lt _ (Nat.pos_of_ne_zero hn), hs.2.2⟩
  · intro s1 hs1 s2 hs2 heq
    simp only [mem_filter, mem_range, Prod.mk.injEq] at hs1 hs2 heq
    exact ((Nat.modEq_and_modEq_iff_modEq_mul co).1 ⟨heq.1, heq.2⟩).eq_of_lt_of_lt hs1.1 hs2.1
  · rintro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_range, mem_product] at hxy
    obtain ⟨⟨hx, hQ1⟩, hy, hQ2⟩ := hxy
    have h1 : (Nat.chineseRemainder co x y : ℕ) % m = x :=
      Eq.trans (Nat.chineseRemainder co x y).prop.1 (Nat.mod_eq_of_lt hx)
    have h2 : (Nat.chineseRemainder co x y : ℕ) % n = y :=
      Eq.trans (Nat.chineseRemainder co x y).prop.2 (Nat.mod_eq_of_lt hy)
    refine ⟨Nat.chineseRemainder co x y, ?_, ?_⟩
    · simp only [mem_filter, mem_range, h1, h2]
      exact ⟨Nat.chineseRemainder_lt_mul co x y hm hn, hQ1, hQ2⟩
    · simp only [h1, h2]

/-- A CRT sieve over a finite set of primes. -/
lemma sieve (F : ℕ → ℕ) (hF : ∀ p s, p ∣ F s ↔ p ∣ F (s % p)) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ((range (∏ p ∈ P, p)).filter (fun s => ∀ p ∈ P, ¬ p ∣ F s)).card =
        ∏ p ∈ P, ((range p).filter (fun x => ¬ p ∣ F x)).card := by
  intro P
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hP
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hR0 : (∏ q ∈ P, q) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun q hq => (hP' q hq).ne_zero)
    have co : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (hP' q hq)).2 (fun h => hpP (h ▸ hq))
    rw [prod_insert hpP, prod_insert hpP, ← ih hP',
      ← card_filter_crt p _ hp.ne_zero hR0 co (fun x => ¬ p ∣ F x)
        (fun y => ∀ q ∈ P, ¬ q ∣ F y)]
    congr 1
    apply filter_congr
    intro s _
    simp only [mem_insert, forall_eq_or_imp]
    apply and_congr
    · rw [hF p s]
    · apply forall₂_congr
      intro q hq
      have hqR : q ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem _ hq
      rw [hF q s, hF q (s % ∏ q ∈ P, q), Nat.mod_mod_of_dvd _ hqR]

/-- A linear polynomial `c + e x` with `p ∤ e` has a root mod `p`. -/
lemma exists_root (p c e : ℕ) (hp : p.Prime) (he : ¬ p ∣ e) : ∃ x < p, p ∣ c + e * x := by
  have := Fact.mk hp
  have he' : (e : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact he
  refine ⟨((-(c : ZMod p)) / e).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [mul_comm, div_mul_cancel₀ _ he']
  exact add_neg_cancel _

/-- The local factor `1 - 1/p`. -/
noncomputable def fA (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹

/-- The local factor of the right-hand side. -/
noncomputable def cfac (x y z p : ℕ) : ℝ :=
  fA p ^ 2 / ((if p ∣ x then fA p else 1) * (if p ∣ y then fA p else 1) *
    (if p ∣ z then fA p else 1))

lemma fA_pos {p : ℕ} (hp : p.Prime) : 0 < fA p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hi0 : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
  have := mul_le_mul_of_nonneg_left hp2 hi0.le
  unfold fA; linarith

lemma prod_fA_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : 0 < ∏ p ∈ s, fA p :=
  prod_pos (fun p hp => fA_pos (hs p hp))

lemma prod_ite_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (x : ℕ) :
    0 < ∏ p ∈ s, (if p ∣ x then fA p else 1) := by
  apply prod_pos
  intro p hp
  split_ifs
  · exact fA_pos (hs p hp)
  · exact one_pos

lemma per_prime (p x y z good : ℕ) (hp : p.Prime) (h1 : good + 1 ≤ p)
    (h2 : ¬ p ∣ x → ¬ p ∣ y → ¬ p ∣ z → good + 2 ≤ p) :
    (good : ℝ) / p ≤ cfac x y z p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hf0 : 0 < fA p := fA_pos hp
  have hf1 : fA p ≤ 1 := by
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    unfold fA; linarith
  have hI : ∀ (P : Prop) [Decidable P],
      0 < (if P then fA p else 1) ∧ (if P then fA p else 1) ≤ 1 := by
    intro P _
    split_ifs <;> constructor <;> linarith
  have b1 := hI (p ∣ x)
  have b2 := hI (p ∣ y)
  have b3 := hI (p ∣ z)
  have e1 : p ∣ x → (if p ∣ x then fA p else 1) = fA p := fun h => by simp [h]
  have e2 : p ∣ y → (if p ∣ y then fA p else 1) = fA p := fun h => by simp [h]
  have e3 : p ∣ z → (if p ∣ z then fA p else 1) = fA p := fun h => by simp [h]
  have e1' : ¬ p ∣ x → (if p ∣ x then fA p else 1) = 1 := fun h => by simp [h]
  have e2' : ¬ p ∣ y → (if p ∣ y then fA p else 1) = 1 := fun h => by simp [h]
  have e3' : ¬ p ∣ z → (if p ∣ z then fA p else 1) = 1 := fun h => by simp [h]
  unfold cfac
  generalize (if p ∣ x then fA p else 1) = i1 at b1 e1 e1' ⊢
  generalize (if p ∣ y then fA p else 1) = i2 at b2 e2 e2' ⊢
  generalize (if p ∣ z then fA p else 1) = i3 at b3 e3 e3' ⊢
  by_cases hall : ¬ p ∣ x ∧ ¬ p ∣ y ∧ ¬ p ∣ z
  · rw [e1' hall.1, e2' hall.2.1, e3' hall.2.2, mul_one, mul_one, div_one]
    have hg2 : (good:ℝ) + 2 ≤ p := by exact_mod_cast h2 hall.1 hall.2.1 hall.2.2
    rw [div_le_iff₀ hpos]
    have e : fA p ^ 2 * p = p - 2 * ((p:ℝ)⁻¹ * p) + (p:ℝ)⁻¹ * ((p:ℝ)⁻¹ * p) := by
      unfold fA; ring
    rw [e, hinv]
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    linarith
  · have hJ0 : 0 < i1 * i2 * i3 := mul_pos (mul_pos b1.1 b2.1) b3.1
    have hJ : i1 * i2 * i3 ≤ fA p := by
      by_cases hx : p ∣ x
      · rw [e1 hx]
        have := mul_le_mul_of_nonneg_left (mul_le_one₀ b2.2 b3.1.le b3.2) hf0.le
        nlinarith
      · by_cases hy : p ∣ y
        · rw [e2 hy]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b3.1.le b3.2) hf0.le
          nlinarith
        · have hz : p ∣ z := by
            by_contra hz; exact hall ⟨hx, hy, hz⟩
          rw [e3 hz]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b2.1.le b2.2) hf0.le
          nlinarith
    have hg1 : (good:ℝ) + 1 ≤ p := by exact_mod_cast h1
    have hA : (good:ℝ) / p ≤ fA p := by
      rw [div_le_iff₀ hpos]; unfold fA; rw [sub_mul, hinv]; linarith
    have hB : fA p ≤ fA p ^ 2 / (i1 * i2 * i3) := by
      rw [le_div_iff₀ hJ0]; nlinarith
    linarith

lemma totient_div_eq (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / n = ∏ p ∈ n.primeFactors, fA p := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' : ((Nat.totient n : ℚ) : ℝ) =
      ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [mul_div_cancel_left₀ _ this]
  rfl

lemma prod_inter_ite (g x : ℕ) (hx : x ≠ 0) (f : ℕ → ℝ) :
    ∏ p ∈ g.primeFactors ∩ x.primeFactors, f p =
      ∏ p ∈ g.primeFactors, (if p ∣ x then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_inter, mem_filter, Nat.mem_primeFactors]
  tauto

lemma prod_of_dvd (g d : ℕ) (hg : g ≠ 0) (hdg : d ∣ g) (f : ℕ → ℝ) :
    ∏ p ∈ d.primeFactors, f p = ∏ p ∈ g.primeFactors, (if p ∣ d then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primeFactors]
  have hd : d ≠ 0 := by rintro rfl; exact hg (Nat.eq_zero_of_zero_dvd hdg)
  constructor
  · rintro ⟨hp, hpd, _⟩; exact ⟨⟨hp, hpd.trans hdg, hg⟩, hpd⟩
  · rintro ⟨⟨hp, _, _⟩, hpd⟩; exact ⟨hp, hpd, hd⟩

end UnitPairCountAux

open UnitPairCountAux in
theorem card_unit_pairs_le (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (h : ℤ) :
    ((((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) ≡ h
          [ZMOD (Nat.lcm q r : ℤ)])).card : ℝ) ≤
      (if Int.gcd h (coprimePart q r) = 1 then 1 else 0) *
        ((Nat.gcd q r : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
          ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) *
          ((Int.gcd h (Nat.gcd q r) : ℝ) / Nat.totient (Int.gcd h (Nat.gcd q r)))) := by
  classical
  have hg0 : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have hq'0 : 0 < q / Nat.gcd q r := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg0
  have hr'0 : 0 < r / Nat.gcd q r := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg0
  have cop : Nat.Coprime (q / Nat.gcd q r) (r / Nat.gcd q r) := Nat.coprime_div_gcd_div_gcd hg0
  have hqg : q = Nat.gcd q r * (q / Nat.gcd q r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)).symm
  have hrg : r = Nat.gcd q r * (r / Nat.gcd q r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)).symm
  have hmdef : coprimePart q r = (q / Nat.gcd q r) * (r / Nat.gcd q r) := rfl
  have hdg : Int.gcd h (Nat.gcd q r) ∣ Nat.gcd q r := by
    have := Int.gcd_dvd_right h (Nat.gcd q r : ℤ)
    exact_mod_cast this
  have hgl := Nat.gcd_mul_lcm q r
  generalize Nat.gcd q r = g at *
  generalize q / g = q' at *
  generalize r / g = r' at *
  obtain ⟨d, hdgcd⟩ : ∃ d, Int.gcd h g = d := ⟨_, rfl⟩
  rw [hdgcd] at hdg ⊢
  have hlcm : Nat.lcm q r = g * q' * r' := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    rw [hgl, hqg, hrg]
    ring
  have hlcmZ : ((Nat.lcm q r : ℕ) : ℤ) = (g : ℤ) * q' * r' := by rw [hlcm]; push_cast; ring
  have hcopZ : IsCoprime (q' : ℤ) (r' : ℤ) := Nat.isCoprime_iff_coprime.2 cop
  have hq'Z : (q' : ℤ) ≠ 0 := by exact_mod_cast hq'0.ne'
  have hr'Z : (r' : ℤ) ≠ 0 := by exact_mod_cast hr'0.ne'
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hg0.ne' (Nat.eq_zero_of_zero_dvd hdg)
  rw [hlcmZ]
  rcases Finset.eq_empty_or_nonempty (((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * (r' : ℤ) - (ab.2 : ℤ) * (q' : ℤ) ≡ h [ZMOD (g : ℤ) * q' * r'])) with
    hE | ⟨⟨a0, b0⟩, h0⟩
  · rw [hE, card_empty, Nat.cast_zero]
    apply mul_nonneg (by split_ifs <;> norm_num)
    positivity
  simp only [mem_filter, mem_product, mem_range] at h0
  obtain ⟨⟨ha0, hb0⟩, hca0, hcb0, hm0⟩ := h0
  obtain ⟨k, hk⟩ := hm0.dvd
  -- Step A: `gcd(h, m) = 1`.
  have hA : IsCoprime h (q' : ℤ) := by
    have h1 : IsCoprime ((a0 : ℤ) * r') (q' : ℤ) := by
      apply IsCoprime.mul_left _ hcopZ.symm
      exact Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left g hqg.symm) hca0)
    have h2 := h1.add_mul_left_left (-(b0 : ℤ) + g * r' * k)
    convert h2 using 1
    linear_combination hk
  have hB : IsCoprime h (r' : ℤ) := by
    have h1 : IsCoprime (-((b0 : ℤ) * q')) (r' : ℤ) := by
      apply IsCoprime.neg_left
      apply IsCoprime.mul_left _ hcopZ
      exact Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left g hrg.symm) hcb0)
    have h2 := h1.add_mul_left_left ((a0 : ℤ) + g * q' * k)
    convert h2 using 1
    linear_combination hk
  have hgcd : Int.gcd h (coprimePart q r) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, hmdef, Nat.cast_mul]
    exact hA.mul_right hB
  rw [if_pos hgcd, one_mul]
  -- Step B: parametrise the solutions.
  obtain ⟨Fe, hFe⟩ : ∃ Fe : ℕ → ℕ, ∀ t, Fe t = (a0 + q' * t) * (b0 + r' * t) :=
    ⟨_, fun t => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
      T = (range g).filter (fun t => ∀ p ∈ g.primeFactors, ¬ p ∣ Fe t) := ⟨_, rfl⟩
  have hsub : ((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * (r' : ℤ) - (ab.2 : ℤ) * (q' : ℤ) ≡ h [ZMOD (g : ℤ) * q' * r']) ⊆
      T.image (fun t => ((a0 + q' * t) % q, (b0 + r' * t) % r)) := by
    rintro ⟨a, b⟩ hab
    simp only [mem_filter, mem_product, mem_range] at hab
    obtain ⟨⟨ha, hb⟩, hca, hcb, hm⟩ := hab
    have hd := (hm0.trans hm.symm).dvd
    have hd' : ((g : ℤ) * q' * r') ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' := by
      have e : ((a : ℤ) * r' - b * q') - (a0 * r' - b0 * q') =
          ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' := by ring
      rw [← e]; exact hd
    have h1 : (q' : ℤ) ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' :=
      dvd_trans ⟨g * r', by ring⟩ hd'
    have h2 : (q' : ℤ) ∣ ((a : ℤ) - a0) * r' := by
      have := dvd_add h1 (dvd_mul_left (q' : ℤ) ((b : ℤ) - b0))
      rwa [sub_add_cancel] at this
    obtain ⟨u, hu⟩ := hcopZ.dvd_of_dvd_mul_right h2
    have h1' : (r' : ℤ) ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' :=
      dvd_trans ⟨g * q', by ring⟩ hd'
    have h2' : (r' : ℤ) ∣ ((b : ℤ) - b0) * q' := by
      have := dvd_sub (dvd_mul_left (r' : ℤ) ((a : ℤ) - a0)) h1'
      rwa [sub_sub_cancel] at this
    obtain ⟨v, hv⟩ := hcopZ.symm.dvd_of_dvd_mul_right h2'
    have hguv : (g : ℤ) ∣ u - v := by
      rw [hu, hv] at hd'
      have hqr : ((q' : ℤ) * r') ≠ 0 := mul_ne_zero hq'Z hr'Z
      rw [← mul_dvd_mul_iff_right hqr]
      have e : (u - v) * ((q' : ℤ) * r') = q' * u * r' - r' * v * q' := by ring
      rw [e, ← mul_assoc]; exact hd'
    obtain ⟨t, htZ⟩ : ∃ t : ℕ, (t : ℤ) = u % g :=
      ⟨(u % g).toNat, Int.toNat_of_nonneg (Int.emod_nonneg u hgZ.ne')⟩
    have htg : t < g := by
      have := Int.emod_lt_of_pos u hgZ
      rw [← htZ] at this; exact_mod_cast this
    have hut : (g : ℤ) ∣ u - t := by
      rw [htZ, Int.emod_def]; exact ⟨u / g, by ring⟩
    have hvt : (g : ℤ) ∣ v - t := by
      have := dvd_sub hut hguv
      convert this using 1; ring
    have haeq : a = (a0 + q' * t) % q := by
      have hmod : a ≡ a0 + q' * t [MOD q] := by
        rw [← Int.natCast_modEq_iff]
        apply Int.modEq_of_dvd
        obtain ⟨w, hw⟩ := hut
        refine ⟨-w, ?_⟩
        rw [hqg]; push_cast
        linear_combination -hu - (q' : ℤ) * hw
      have := hmod
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt ha] at this
      exact this
    have hbeq : b = (b0 + r' * t) % r := by
      have hmod : b ≡ b0 + r' * t [MOD r] := by
        rw [← Int.natCast_modEq_iff]
        apply Int.modEq_of_dvd
        obtain ⟨w, hw⟩ := hvt
        refine ⟨-w, ?_⟩
        rw [hrg]; push_cast
        linear_combination -hv - (r' : ℤ) * hw
      have := hmod
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt hb] at this
      exact this
    rw [mem_image]
    refine ⟨t, ?_, Prod.ext haeq.symm hbeq.symm⟩
    rw [hT, mem_filter, mem_range]
    refine ⟨htg, ?_⟩
    intro p hp hpF
    obtain ⟨hpp, hpg, -⟩ := Nat.mem_primeFactors.1 hp
    rw [hFe] at hpF
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h' | h'
    · have hpq : p ∣ q := hpg.trans (Dvd.intro q' hqg.symm)
      have hpa : p ∣ a := by rw [haeq]; exact (Nat.dvd_mod_iff hpq).2 h'
      have := Nat.dvd_gcd hpa hpq
      rw [Nat.Coprime.gcd_eq_one hca] at this
      exact hpp.not_dvd_one this
    · have hpr : p ∣ r := hpg.trans (Dvd.intro r' hrg.symm)
      have hpb : p ∣ b := by rw [hbeq]; exact (Nat.dvd_mod_iff hpr).2 h'
      have := Nat.dvd_gcd hpb hpr
      rw [Nat.Coprime.gcd_eq_one hcb] at this
      exact hpp.not_dvd_one this
  have hcard1 := (card_le_card hsub).trans card_image_le
  -- Step C: count `T` with the CRT sieve.
  have hFmod : ∀ p s, p ∣ Fe s ↔ p ∣ Fe (s % p) := by
    intro p s
    rw [hFe, hFe, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
    have hs : s % p ≡ s [MOD p] := Nat.mod_modEq s p
    have : ((a0 + q' * (s % p)) * (b0 + r' * (s % p))) % p =
        ((a0 + q' * s) * (b0 + r' * s)) % p :=
      ((hs.mul_left q').add_left a0).mul ((hs.mul_left r').add_left b0)
    rw [this]
  have hGprime : ∀ p ∈ g.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hRg : (∏ p ∈ g.primeFactors, p) ∣ g := Nat.prod_primeFactors_dvd g
  have hR0 : (∏ p ∈ g.primeFactors, p) ≠ 0 :=
    prod_ne_zero_iff.2 (fun p hp => (hGprime p hp).ne_zero)
  have hTcard : T.card = (g / ∏ p ∈ g.primeFactors, p) *
      ∏ p ∈ g.primeFactors, ((range p).filter (fun x => ¬ p ∣ Fe x)).card := by
    have key := card_filter_range_mul_mod (fun y => ∀ p ∈ g.primeFactors, ¬ p ∣ Fe y)
      (∏ p ∈ g.primeFactors, p) (g / ∏ p ∈ g.primeFactors, p)
    rw [Nat.mul_div_cancel' hRg, sieve Fe hFmod _ hGprime] at key
    rw [← key, hT]
    congr 1
    apply filter_congr
    intro s _
    apply forall₂_congr
    intro p hp
    have hpR : p ∣ ∏ p ∈ g.primeFactors, p := Finset.dvd_prod_of_mem _ hp
    rw [hFmod p s, hFmod p (s % ∏ p ∈ g.primeFactors, p), Nat.mod_mod_of_dvd _ hpR]
  have hTR : (T.card : ℝ) = g * ∏ p ∈ g.primeFactors,
      ((((range p).filter (fun x => ¬ p ∣ Fe x)).card : ℝ) / p) := by
    rw [hTcard, Nat.cast_mul, Nat.cast_div hRg (by exact_mod_cast hR0), Nat.cast_prod,
      Nat.cast_prod, prod_div_distrib]
    ring
  -- Step D: local bounds.
  have hnot : ∀ p, p.Prime → p ∣ q' → p ∣ r' → False := by
    intro p hp h1 h2
    have := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one cop] at this
    exact hp.not_dvd_one this
  have hper : ∀ p ∈ g.primeFactors,
      ((((range p).filter (fun x => ¬ p ∣ Fe x)).card : ℝ) / p) ≤ cfac q' r' d p := by
    intro p hp
    obtain ⟨hpp, hpg, -⟩ := Nat.mem_primeFactors.1 hp
    apply per_prime p q' r' d _ hpp
    · obtain ⟨x, hxp, hx⟩ : ∃ x < p, p ∣ Fe x := by
        by_cases hr' : p ∣ r'
        · obtain ⟨x, hxp, hx⟩ := exists_root p a0 q' hpp (fun hq' => hnot p hpp hq' hr')
          exact ⟨x, hxp, by rw [hFe]; exact dvd_mul_of_dvd_left hx _⟩
        · obtain ⟨x, hxp, hx⟩ := exists_root p b0 r' hpp hr'
          exact ⟨x, hxp, by rw [hFe]; exact dvd_mul_of_dvd_right hx _⟩
      have hs : (range p).filter (fun x => ¬ p ∣ Fe x) ⊆ (range p).erase x := by
        intro y hy
        rw [mem_filter] at hy
        rw [mem_erase]
        exact ⟨fun hyx => hy.2 (by rw [hyx]; exact hx), hy.1⟩
      have := card_le_card hs
      rw [card_erase_of_mem (mem_range.2 hxp), card_range] at this
      have := hpp.two_le
      omega
    · intro hq' hr' hd'
      obtain ⟨x1, hx1p, hx1⟩ := exists_root p a0 q' hpp hq'
      obtain ⟨x2, hx2p, hx2⟩ := exists_root p b0 r' hpp hr'
      have hne : x1 ≠ x2 := by
        rintro rfl
        have hpA : (p : ℤ) ∣ (a0 : ℤ) + q' * x1 := by exact_mod_cast hx1
        have hpB : (p : ℤ) ∣ (b0 : ℤ) + r' * x1 := by exact_mod_cast hx2
        have hpX : (p : ℤ) ∣ (a0 : ℤ) * r' - b0 * q' := by
          have := dvd_sub (dvd_mul_of_dvd_left hpA (r' : ℤ)) (dvd_mul_of_dvd_left hpB (q' : ℤ))
          convert this using 1; ring
        have hpgZ : (p : ℤ) ∣ (g : ℤ) := by exact_mod_cast hpg
        have hph : (p : ℤ) ∣ h := by
          have hpL : (p : ℤ) ∣ (g : ℤ) * q' * r' * k :=
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpgZ _) _) _
          have e : h = (h - ((a0 : ℤ) * r' - b0 * q')) + ((a0 : ℤ) * r' - b0 * q') := by ring
          rw [e, hk]
          exact dvd_add hpL hpX
        exact hd' (hdgcd ▸ Int.dvd_gcd hph hpgZ)
      have hs : (range p).filter (fun x => ¬ p ∣ Fe x) ⊆ ((range p).erase x1).erase x2 := by
        intro y hy
        rw [mem_filter] at hy
        rw [mem_erase, mem_erase]
        refine ⟨fun hyx => hy.2 ?_, fun hyx => hy.2 ?_, hy.1⟩
        · rw [hyx, hFe]; exact dvd_mul_of_dvd_right hx2 _
        · rw [hyx, hFe]; exact dvd_mul_of_dvd_left hx1 _
      have := card_le_card hs
      rw [card_erase_of_mem (mem_erase.2 ⟨hne.symm, mem_range.2 hx2p⟩),
        card_erase_of_mem (mem_range.2 hx1p), card_range] at this
      have := hpp.two_le
      omega
  -- Step E: the right-hand side as a product over `p | g`.
  have hpfq : q.primeFactors = g.primeFactors ∪ q'.primeFactors := by
    rw [hqg]; exact Nat.primeFactors_mul hg0.ne' hq'0.ne'
  have hpfr : r.primeFactors = g.primeFactors ∪ r'.primeFactors := by
    rw [hrg]; exact Nat.primeFactors_mul hg0.ne' hr'0.ne'
  have hGpos := prod_fA_pos g.primeFactors hGprime
  have hQpos := prod_fA_pos q'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hRpos := prod_fA_pos r'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hIq := prod_ite_pos g.primeFactors hGprime q'
  have hIr := prod_ite_pos g.primeFactors hGprime r'
  have hId := prod_ite_pos g.primeFactors hGprime d
  have hq_eq : (Nat.totient q : ℝ) / q = (∏ p ∈ g.primeFactors, fA p) *
      (∏ p ∈ q'.primeFactors, fA p) / ∏ p ∈ g.primeFactors, (if p ∣ q' then fA p else 1) := by
    rw [totient_div_eq q hq.ne', hpfq, ← prod_inter_ite g q' hq'0.ne']
    apply eq_div_of_mul_eq (by rw [prod_inter_ite g q' hq'0.ne']; exact hIq.ne')
    exact prod_union_inter
  have hr_eq : (Nat.totient r : ℝ) / r = (∏ p ∈ g.primeFactors, fA p) *
      (∏ p ∈ r'.primeFactors, fA p) / ∏ p ∈ g.primeFactors, (if p ∣ r' then fA p else 1) := by
    rw [totient_div_eq r hr.ne', hpfr, ← prod_inter_ite g r' hr'0.ne']
    apply eq_div_of_mul_eq (by rw [prod_inter_ite g r' hr'0.ne']; exact hIr.ne')
    exact prod_union_inter
  have hm_eq : (coprimePart q r : ℝ) / Nat.totient (coprimePart q r) =
      1 / ((∏ p ∈ q'.primeFactors, fA p) * (∏ p ∈ r'.primeFactors, fA p)) := by
    rw [← totient_div_eq q' hq'0.ne', ← totient_div_eq r' hr'0.ne', hmdef, Nat.totient_mul cop]
    have h1 : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'0.ne'
    have h2 : (r' : ℝ) ≠ 0 := by exact_mod_cast hr'0.ne'
    have h3 : (Nat.totient q' : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hq'0).ne'
    have h4 : (Nat.totient r' : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hr'0).ne'
    push_cast
    field_simp
  have hd_eq : (d : ℝ) / Nat.totient d =
      1 / ∏ p ∈ g.primeFactors, (if p ∣ d then fA p else 1) := by
    rw [← prod_of_dvd g d hg0.ne' hdg, ← totient_div_eq d hd0]
    have h1 : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have h3 : (Nat.totient d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0)).ne'
    field_simp
  have hRHS : (g : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
      ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) * ((d : ℝ) / Nat.totient d) =
      g * ∏ p ∈ g.primeFactors, cfac q' r' d p := by
    rw [hq_eq, hr_eq, hm_eq, hd_eq]
    simp only [cfac]
    rw [prod_div_distrib, prod_pow, prod_mul_distrib, prod_mul_distrib]
    field_simp
  rw [hRHS]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard1
    _ = _ := hTR
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod₀
      · intro p _; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact hper

end DuffinSchaeffer
