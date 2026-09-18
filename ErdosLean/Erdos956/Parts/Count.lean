import ErdosLean.Erdos956.Parts.UnitWitness
import ErdosLean.Erdos956.Parts.TriplesCard

/-!
# Erdős #956 — Part 12: at least `M_k` unit pairs (note, Lemma 4)

`pairOf` is injective on `triples k` (the lower endpoint has `y < 1`, the upper one `y ≥ 1`, so a
`Sym2` equality matches endpoints; the lower endpoint recovers `(r, s)`, the difference recovers
`i`), and maps into `unitPairs (C k) (X k)` by Part 10.
-/

namespace Erdos956

lemma altCount_a_pos {k : ℕ} (hk : 1 ≤ k) : 0 < a k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold a α; exact div_pos (by norm_num) (pow_pos hk0 2)

lemma altCount_b_pos {k : ℕ} (hk : 1 ≤ k) : 0 < b k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold b α; exact div_pos (by norm_num) (by positivity)

lemma altCount_lowY_lt_one {k s : ℕ} (hk : 1 ≤ k) (hs : s ≤ k ^ 2) : (s : ℝ) * b k < 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hs' : (s : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hs
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hb := altCount_b_pos hk
  have heq : (k : ℝ) ^ 2 * b k = (1 / 200) / (k : ℝ) ^ 2 := by
    unfold b α; field_simp; ring
  calc (s : ℝ) * b k ≤ (k : ℝ) ^ 2 * b k := mul_le_mul_of_nonneg_right hs' hb.le
    _ = (1 / 200) / (k : ℝ) ^ 2 := heq
    _ ≤ 1 / 200 := div_le_self (by norm_num) hk2
    _ < 1 := by norm_num

lemma altCount_upY_ge_one {k : ℕ} (hk : 1 ≤ k) (s : ℕ) : 1 ≤ 1 + η k + (s : ℝ) * b k := by
  have hb := altCount_b_pos hk
  have hη : 0 ≤ η k := by unfold η α; positivity
  have : 0 ≤ (s : ℝ) * b k := mul_nonneg (Nat.cast_nonneg _) hb.le
  linarith

lemma altCount_lowPt_ne_upPt {k r s r' s' : ℕ} (hk : 1 ≤ k) (hs : s ≤ k ^ 2) :
    lowPt k r s ≠ upPt k r' s' := by
  intro h
  have h1 := congrArg (fun p : E => p 1) h
  simp only [lowPt, upPt, pt_one] at h1
  have := altCount_lowY_lt_one hk hs
  have := altCount_upY_ge_one hk s'
  linarith

lemma pairOf_injOn {k : ℕ} (hk : 1 ≤ k) : Set.InjOn (pairOf k) (triples k : Set _) := by
  rintro ⟨i, r, s⟩ hq ⟨i', r', s'⟩ hq' h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, triples, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hq hq'
  have hs : s ≤ k ^ 2 := by omega
  have hs' : s' ≤ k ^ 2 := by omega
  simp only [pairOf] at h
  rcases Sym2.eq_iff.mp h with ⟨hL, hU⟩ | ⟨hL, _⟩
  · have ha := altCount_a_pos hk
    have hb := altCount_b_pos hk
    have h0 := congrArg (fun p : E => p 0) hL
    have h1 := congrArg (fun p : E => p 1) hL
    have h2 := congrArg (fun p : E => p 0) hU
    simp only [lowPt, upPt, pt_zero, pt_one] at h0 h1 h2
    have er : (r : ℝ) = r' := mul_right_cancel₀ ha.ne' h0
    have es : (s : ℝ) = s' := mul_right_cancel₀ hb.ne' h1
    have ei : ((r + i : ℕ) : ℝ) = ((r' + i' : ℕ) : ℝ) := mul_right_cancel₀ ha.ne' h2
    have er' : r = r' := by exact_mod_cast er
    have es' : s = s' := by exact_mod_cast es
    have ei' : r + i = r' + i' := by exact_mod_cast ei
    have : i = i' := by omega
    subst er' es' this
    rfl
  · exact absurd hL (altCount_lowPt_ne_upPt hk hs)

lemma pairOf_mem_unitPairs {k : ℕ} (hk : 1 ≤ k) {q : ℕ × ℕ × ℕ} (hq : q ∈ triples k) :
    pairOf k q ∈ unitPairs (C k) (X k) := by
  classical
  have hd := setDist_pairOf hk hq
  obtain ⟨i, r, s⟩ := q
  have hq2 := hq
  simp only [triples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hq2
  have hs : s ≤ k ^ 2 := by omega
  unfold unitPairs
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [pairOf]
    rw [Finset.mk_mem_sym2_iff]
    constructor
    · apply Finset.mem_union_left
      unfold lowGrid
      exact Finset.mem_image.mpr ⟨(r, s), by
        simp only [idx, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
    · apply Finset.mem_union_right
      unfold upGrid
      exact Finset.mem_image.mpr ⟨(r + i, s - i ^ 2), by
        simp only [idx, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
  · exact ⟨_, _, rfl, altCount_lowPt_ne_upPt hk hs, hd⟩

theorem Mk_le_card_unitPairs {k : ℕ} (hk : 1 ≤ k) : Mk k ≤ (unitPairs (C k) (X k)).card := by
  rw [← card_triples]
  apply Finset.card_le_card_of_injOn (pairOf k)
  · intro q hq
    exact pairOf_mem_unitPairs hk hq
  · exact pairOf_injOn hk


end Erdos956
