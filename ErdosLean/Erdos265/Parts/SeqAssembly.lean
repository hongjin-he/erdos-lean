import ErdosLean.Erdos265.Parts.Params

/-!
# Erdős #265 — Part L5: from admissible block offsets to an admissible sequence

* block values are nonnegative and the centres are summable (`s_k = O(1/N_k)`);
* `seqOf c` is strictly increasing with `seqOf c 0 ≥ 2` (Part L3: `2M_k < N_k`,
  `2N_k + M_k + M_{k+1} < N_{k+1}`);
* `∑ₙ 1/aₙ = ∑_k (blockVal k (c k)).1` and `∑ₙ 1/(aₙ(aₙ-1)) = ∑_k (blockVal k (c k)).2`
  (split `ℕ` into even and odd indices, `HasSum.even_add_odd`-style), and
  `1/(aₙ - 1) = 1/aₙ + 1/(aₙ(aₙ-1))`; so rational `x₁, x₂` give rational sums `x₁`,
  `x₁ + x₂`.
-/

open Filter Topology

namespace Erdos265

private lemma f_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f1 x ∧ 0 ≤ f2 x := by
  unfold f1 f2
  exact ⟨div_nonneg zero_le_one (by linarith),
    div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))⟩

private lemma f1_le_geom {x : ℝ} {k : ℕ} (hx : (4 : ℝ) ^ k ≤ x) : f1 x ≤ (1 / 4 : ℝ) ^ k := by
  unfold f1
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hx

private lemma f2_le_f1 {x : ℝ} (hx : 2 ≤ x) : f2 x ≤ f1 x := by
  unfold f1 f2
  apply one_div_le_one_div_of_le (by linarith)
  nlinarith

private lemma adm_int {k : ℕ} {c : ℤ × ℤ} (hc : Adm k c) :
    -(MM k : ℤ) ≤ c.1 ∧ c.1 ≤ MM k ∧ -(MM k : ℤ) ≤ c.2 ∧ c.2 ≤ MM k ∧
    2 * (MM k : ℤ) < NN k ∧ (64 : ℤ) ≤ NN k := by
  obtain ⟨h1, h2⟩ := hc
  rw [abs_le] at h1 h2
  have h3 := two_MM_lt k
  have h4 := NN_ge k
  exact ⟨h1.1, h1.2, h2.1, h2.2, by exact_mod_cast h3, by exact_mod_cast h4⟩

theorem blockVal_nonneg {k : ℕ} {c : ℤ × ℤ} (hc : Adm k c) :
    0 ≤ (blockVal k c).1 ∧ 0 ≤ (blockVal k c).2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int hc
  have e1 : (1 : ℝ) ≤ (NN k : ℝ) + (c.1 : ℝ) := by
    have : (1 : ℤ) ≤ (NN k : ℤ) + c.1 := by omega
    exact_mod_cast this
  have e2 : (1 : ℝ) ≤ 2 * (NN k : ℝ) + (c.2 : ℝ) := by
    have : (1 : ℤ) ≤ 2 * (NN k : ℤ) + c.2 := by omega
    exact_mod_cast this
  obtain ⟨p1, p2⟩ := f_nonneg e1
  obtain ⟨q1, q2⟩ := f_nonneg e2
  exact ⟨add_nonneg p1 q1, add_nonneg p2 q2⟩

private lemma mSeq_ge_self (k : ℕ) : k ≤ mSeq k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ n ih => simp only [mSeq]; omega

private lemma NN_ge_pow (k : ℕ) : (4 : ℝ) ^ k ≤ (NN k : ℝ) := by
  have : 4 ^ k ≤ NN k := Nat.pow_le_pow_right (by norm_num) (mSeq_ge_self k)
  exact_mod_cast this

theorem center_summable :
    Summable (fun k ↦ (center k).1) ∧ Summable (fun k ↦ (center k).2) := by
  have hg : Summable (fun k : ℕ ↦ 2 * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  have hN : ∀ k, (4 : ℝ) ^ k ≤ (NN k : ℝ) := NN_ge_pow
  have hN2 : ∀ k, (4 : ℝ) ^ k ≤ 2 * (NN k : ℝ) := fun k ↦ by
    have := hN k; have : (0 : ℝ) ≤ NN k := Nat.cast_nonneg _; linarith
  have h64 : ∀ k, (64 : ℝ) ≤ (NN k : ℝ) := fun k ↦ by exact_mod_cast NN_ge k
  have c1 : ∀ k, (center k).1 = f1 (NN k : ℝ) + f1 (2 * (NN k : ℝ)) := fun k ↦ by
    simp [center, blockVal]
  have c2 : ∀ k, (center k).2 = f2 (NN k : ℝ) + f2 (2 * (NN k : ℝ)) := fun k ↦ by
    simp [center, blockVal]
  have b1 : ∀ k, (center k).1 ≤ 2 * (1 / 4 : ℝ) ^ k := fun k ↦ by
    rw [c1]; have := f1_le_geom (hN k); have := f1_le_geom (hN2 k); linarith
  have b2 : ∀ k, (center k).2 ≤ (center k).1 := fun k ↦ by
    rw [c1, c2]
    have := h64 k
    have := f2_le_f1 (x := (NN k : ℝ)) (by linarith)
    have := f2_le_f1 (x := 2 * (NN k : ℝ)) (by linarith)
    linarith
  have n1 : ∀ k, 0 ≤ (center k).1 ∧ 0 ≤ (center k).2 := fun k ↦
    blockVal_nonneg (k := k) (c := (0, 0)) ⟨by simp, by simp⟩
  have s1 : Summable (fun k ↦ (center k).1) :=
    Summable.of_nonneg_of_le (fun k ↦ (n1 k).1) b1 hg
  exact ⟨s1, Summable.of_nonneg_of_le (fun k ↦ (n1 k).2) b2 s1⟩

private lemma seqOf_even (c : ℕ → ℤ × ℤ) (k : ℕ) :
    seqOf c (2 * k) = ((NN k : ℤ) + (c k).1).toNat := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : (2 * k) / 2 = k := by omega
  simp [seqOf, h1, h2]

private lemma seqOf_odd (c : ℕ → ℤ × ℤ) (k : ℕ) :
    seqOf c (2 * k + 1) = (2 * (NN k : ℤ) + (c k).2).toNat := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [seqOf, h1, h2]

private lemma seqOf_even_int {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) (k : ℕ) :
    ((seqOf c (2 * k) : ℕ) : ℤ) = (NN k : ℤ) + (c k).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
  rw [seqOf_even, Int.toNat_of_nonneg (by omega)]

private lemma seqOf_odd_int {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) (k : ℕ) :
    ((seqOf c (2 * k + 1) : ℕ) : ℤ) = 2 * (NN k : ℤ) + (c k).2 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
  rw [seqOf_odd, Int.toNat_of_nonneg (by omega)]

private lemma seqOf_even_real {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) (k : ℕ) :
    ((seqOf c (2 * k) : ℕ) : ℝ) = (NN k : ℝ) + ((c k).1 : ℝ) := by
  have h := seqOf_even_int hc k
  have : (((seqOf c (2 * k) : ℕ) : ℤ) : ℝ) = (((NN k : ℤ) + (c k).1 : ℤ) : ℝ) := by rw [h]
  push_cast at this
  exact this

private lemma seqOf_odd_real {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) (k : ℕ) :
    ((seqOf c (2 * k + 1) : ℕ) : ℝ) = 2 * (NN k : ℝ) + ((c k).2 : ℝ) := by
  have h := seqOf_odd_int hc k
  have : (((seqOf c (2 * k + 1) : ℕ) : ℤ) : ℝ) = ((2 * (NN k : ℤ) + (c k).2 : ℤ) : ℝ) := by
    rw [h]
  push_cast at this
  exact this

private lemma hasSum_of_pairs {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {x : ℝ}
    (h : HasSum (fun k ↦ f (2 * k) + f (2 * k + 1)) x) : HasSum f x := by
  have se : Summable (fun k ↦ f (2 * k)) :=
    Summable.of_nonneg_of_le (fun k ↦ hf _) (fun k ↦ le_add_of_nonneg_right (hf _)) h.summable
  have so : Summable (fun k ↦ f (2 * k + 1)) :=
    Summable.of_nonneg_of_le (fun k ↦ hf _) (fun k ↦ le_add_of_nonneg_left (hf _)) h.summable
  have hx := h.unique (se.hasSum.add so.hasSum)
  rw [hx]
  exact se.hasSum.even_add_odd so.hasSum

theorem isRationalPair_of_blocks {c : ℕ → ℤ × ℤ} (hc : ∀ k, Adm k (c k)) {x1 x2 : ℚ}
    (h1 : HasSum (fun k ↦ (blockVal k (c k)).1) (x1 : ℝ))
    (h2 : HasSum (fun k ↦ (blockVal k (c k)).2) (x2 : ℝ)) :
    IsRationalPair (seqOf c) := by
  have ge2 : ∀ n, 2 ≤ seqOf c n := by
    intro n
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have := seqOf_even_int hc k
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
      omega
    · have := seqOf_odd_int hc k
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
      omega
  have mono : StrictMono (seqOf c) := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have e1 := seqOf_even_int hc k
      have e2 := seqOf_odd_int hc k
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
      omega
    · have e1 := seqOf_odd_int hc k
      have e2 := seqOf_even_int hc (k + 1)
      have e : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [e]
      have g := block_gap k
      have g' : 2 * (NN k : ℤ) + MM k + MM (k + 1) < NN (k + 1) := by exact_mod_cast g
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := adm_int (hc k)
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := adm_int (hc (k + 1))
      omega
  have ge2r : ∀ n, (2 : ℝ) ≤ (seqOf c n : ℝ) := fun n ↦ by exact_mod_cast ge2 n
  set f : ℕ → ℝ := fun n ↦ 1 / (seqOf c n : ℝ) with hfdef
  set g : ℕ → ℝ := fun n ↦ 1 / ((seqOf c n : ℝ) * ((seqOf c n : ℝ) - 1)) with hgdef
  have fn : ∀ n, 0 ≤ f n := fun n ↦ (f_nonneg (x := (seqOf c n : ℝ)) (by linarith [ge2r n])).1
  have gn : ∀ n, 0 ≤ g n := fun n ↦ (f_nonneg (x := (seqOf c n : ℝ)) (by linarith [ge2r n])).2
  have hf : HasSum f (x1 : ℝ) := by
    apply hasSum_of_pairs fn
    convert h1 using 1
    funext k
    simp only [hfdef, blockVal, f1, seqOf_even_real hc, seqOf_odd_real hc]
  have hg : HasSum g (x2 : ℝ) := by
    apply hasSum_of_pairs gn
    convert h2 using 1
    funext k
    simp only [hgdef, blockVal, f2, seqOf_even_real hc, seqOf_odd_real hc]
  have hs : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((seqOf c n : ℝ) - 1)) ((x1 : ℝ) + x2) := by
    convert hf.add hg using 1
    funext n
    have h2n := ge2r n
    have hne : (seqOf c n : ℝ) ≠ 0 := by linarith
    have hne' : (seqOf c n : ℝ) - 1 ≠ 0 := by linarith
    simp only [hfdef, hgdef]
    field_simp
    ring
  refine ⟨mono, ge2 0, hf.summable, hs.summable, ⟨x1, hf.tsum_eq⟩, ⟨x1 + x2, ?_⟩⟩
  rw [hs.tsum_eq]
  push_cast
  ring

end Erdos265
