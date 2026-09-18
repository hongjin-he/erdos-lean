import ErdosLean.Erdos956.Parts.BodyBox
import ErdosLean.Erdos956.Parts.HalfBody
import ErdosLean.Erdos956.Parts.SetDist

/-!
# Erdős #956 — Part 9: the translates `C + x`, `x ∈ X_k`, are pairwise disjoint (note, Lemma 3)

A non-zero difference of two points of `X_k` is `(m a, ℓ b)` (same grid, `(m,ℓ) ≠ 0`) or has
`|y|`-coordinate `≥ 1 + η - k² b` (different grids); none lies in the box of Part 5, because
`W³/2 < a`, `η < b` and `η < 1 + η - k² b` for `k ≥ 2`, `α = 1/10`.

-/

namespace Erdos956

lemma altDisjoint_a_gt {k : ℕ} (hk : 2 ≤ k) : W k ^ 3 / 2 < a k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have e : W k ^ 3 / 2 = a k * (1 / (200 * (k : ℝ))) := by
    unfold W a α; field_simp; ring
  have ha : 0 < a k := by unfold a α; positivity
  rw [e]
  apply mul_lt_of_lt_one_right ha
  rw [div_lt_one (by positivity)]; linarith

lemma altDisjoint_b_pos (k : ℕ) (hk : 2 ≤ k) : 0 < b k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  unfold b α; positivity

lemma alt_η_lt_b {k : ℕ} (hk : 2 ≤ k) : η k < b k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have e : η k = b k * (1 / 50) := by unfold η b α; field_simp; ring
  rw [e]; have := altDisjoint_b_pos k hk; linarith

lemma alt_η_nonneg (k : ℕ) : 0 ≤ η k := by unfold η α; positivity

lemma altDisjoint_k2b_lt_one {k : ℕ} (hk : 2 ≤ k) : (k : ℝ) ^ 2 * b k < 1 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have e : (k : ℝ) ^ 2 * b k = 1 / (200 * (k : ℝ) ^ 2) := by unfold b α; field_simp; ring
  rw [e, div_lt_one (by positivity)]; nlinarith

lemma altDisjoint_step {c t : ℝ} (hc : 0 < c) (ht : t < c) {m n : ℕ}
    (h : |(m : ℝ) * c - n * c| ≤ t) : m = n := by
  by_contra hne
  rw [abs_le] at h
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
    nlinarith
  · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h'
    nlinarith

lemma altDisjoint_mem_X {k : ℕ} {x : E} (hx : x ∈ X k) :
    ∃ r s : ℕ, r ≤ k ∧ s ≤ k ^ 2 ∧ (x = lowPt k r s ∨ x = upPt k r s) := by
  simp only [X, lowGrid, upGrid, idx, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_range] at hx
  rcases hx with ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩ | ⟨⟨r, s⟩, ⟨hr, hs⟩, rfl⟩
  · exact ⟨r, s, by omega, by omega, Or.inl rfl⟩
  · exact ⟨r, s, by omega, by omega, Or.inr rfl⟩

lemma altDisjoint_not_box {k : ℕ} (hk : 2 ≤ k) {x y : E} (hx : x ∈ X k) (hy : y ∈ X k) (hxy : x ≠ y)
    (h0 : |(y - x) 0| ≤ W k ^ 3 / 2) (h1 : |(y - x) 1| ≤ η k) : False := by
  have ha := altDisjoint_a_gt hk
  have hapos : 0 < a k := by have := altDisjoint_b_pos k hk; unfold a α at *; positivity
  have hb := altDisjoint_b_pos k hk
  have hηb := alt_η_lt_b hk
  have hη0 := alt_η_nonneg k
  have hkb := altDisjoint_k2b_lt_one hk
  obtain ⟨r, s, hr, hs, rfl | rfl⟩ := altDisjoint_mem_X hx <;>
  obtain ⟨r', s', hr', hs', rfl | rfl⟩ := altDisjoint_mem_X hy <;>
  simp only [lowPt, upPt, PiLp.sub_apply, pt_zero, pt_one] at h0 h1 <;>
  have hs1 : (s : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hs
  · have e1 := altDisjoint_step hapos ha h0
    have e2 := altDisjoint_step hb hηb h1
    subst e1; subst e2; exact hxy rfl
  · rw [abs_le] at h1
    have : (0 : ℝ) ≤ s' := by positivity
    nlinarith
  · rw [abs_le] at h1
    have hs1' : (s' : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hs'
    have : (0 : ℝ) ≤ s := by positivity
    nlinarith
  · have e1 := altDisjoint_step hapos ha h0
    have h1' : |(s' : ℝ) * b k - s * b k| ≤ η k := by
      convert h1 using 2; ring
    have e2 := altDisjoint_step hb hηb h1'
    subst e1; subst e2; exact hxy rfl

theorem admissible_X {k : ℕ} (hk : 2 ≤ k) : Admissible (C k) (X k) := by
  refine ⟨C_isCompact k, C_convex k, C_nonempty (by omega), ?_⟩
  intro x hx y hy hxy
  apply translate_disjoint
  intro c hc c' hc' heq
  obtain ⟨h0, h1⟩ := mem_D_bounds (by omega) (sub_mem_D hc hc')
  rw [heq] at h0 h1
  exact altDisjoint_not_box hk hx hy hxy h0 h1


end Erdos956
