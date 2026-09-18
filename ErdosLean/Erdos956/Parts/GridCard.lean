import ErdosLean.Erdos956.Defs

/-!
# Erdős #956 — Part 13: `|X_k| = 2(k+1)(k²+1)` (note, (7))

`lowPt k`, `upPt k` are injective on `idx k` (since `a, b > 0`), and `L ∩ U = ∅`
(`y < 1` versus `y > 1`).
-/

namespace Erdos956

open Finset

lemma altGridCard_pt_inj {x y x' y' : ℝ} (h : pt x y = pt x' y') : x = x' ∧ y = y' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (fun v : E => v 0) h; simpa using this
  · have := congrArg (fun v : E => v 1) h; simpa using this

theorem card_X {k : ℕ} (hk : 1 ≤ k) : (X k).card = nk k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a k := by unfold a α; positivity
  have hb : 0 < b k := by unfold b α; positivity
  have hη : 0 < η k := by unfold η α; positivity
  have hidx : (idx k).card = (k + 1) * (k ^ 2 + 1) := by
    simp [idx, card_product]
  have hL : (lowGrid k).card = (k + 1) * (k ^ 2 + 1) := by
    rw [lowGrid, card_image_of_injective _ ?_, hidx]
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    obtain ⟨h1, h2⟩ := altGridCard_pt_inj h
    have e1 : (r : ℝ) = r' := mul_right_cancel₀ ha.ne' h1
    have e2 : (s : ℝ) = s' := mul_right_cancel₀ hb.ne' h2
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  have hU : (upGrid k).card = (k + 1) * (k ^ 2 + 1) := by
    rw [upGrid, card_image_of_injective _ ?_, hidx]
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    obtain ⟨h1, h2⟩ := altGridCard_pt_inj h
    have e1 : (r : ℝ) = r' := mul_right_cancel₀ ha.ne' h1
    have e2 : (s : ℝ) = s' := mul_right_cancel₀ hb.ne' (by linarith)
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  have hdisj : Disjoint (lowGrid k) (upGrid k) := by
    rw [Finset.disjoint_left]
    intro p hpL hpU
    simp only [lowGrid, upGrid, mem_image] at hpL hpU
    obtain ⟨⟨r, s⟩, hq, rfl⟩ := hpL
    obtain ⟨⟨r', s'⟩, -, h⟩ := hpU
    obtain ⟨-, h2⟩ := altGridCard_pt_inj h
    simp only [idx, mem_product, mem_range] at hq
    have hs : (s : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hq.2
    have hbd : (s : ℝ) * b k < 1 := by
      have : (k : ℝ) ^ 2 * b k < 1 := by
        unfold b α
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        rw [show (k : ℝ) ^ 2 * ((1 / 10) ^ 2 / (2 * (k : ℝ) ^ 4))
            = (1 / 200) / (k : ℝ) ^ 2 by field_simp; ring]
        rw [div_lt_one (by positivity)]
        nlinarith
      calc (s : ℝ) * b k ≤ (k : ℝ) ^ 2 * b k := mul_le_mul_of_nonneg_right hs hb.le
        _ < 1 := this
    have : (0 : ℝ) ≤ (s' : ℝ) * b k := by positivity
    linarith
  rw [X, card_union_of_disjoint hdisj, hL, hU, nk]
  ring

end Erdos956
