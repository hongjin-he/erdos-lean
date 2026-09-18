import ErdosLean.Erdos494.Defs
import ErdosLean.Erdos494.Parts.RidoutSmooth

/-! # Erdős 494, part D1: gaps between `P`-smooth numbers (non-coprime form).

From `ridout_smooth` (applied with `δ/2`): write `g = gcd(x,y)`, `x = g x'`, `y = g y'`.
If `max(x',y') ≤ B` and `x ≠ y` then `|x - y| ≥ g ≥ max(x,y)/B`, which beats `y^{1-δ}` for
`y` large.  Otherwise `(max/g)^{1-δ/2} ≤ |x'-y'| = |x-y|/g ≤ y^{1-δ}/g`, impossible for `y`
large.  (Note `|x-y| ≤ y^{1-δ}` implies `x ≤ 2y`.) -/

namespace Erdos494

theorem smooth_gap (P : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X0 : ℕ, ∀ x y : ℕ, x ∈ Nat.smoothNumbers P → y ∈ Nat.smoothNumbers P → X0 < y →
      |(x : ℝ) - y| ≤ (y : ℝ) ^ (1 - δ) → x = y := by
  set e : ℝ := min δ 1 with he_def
  have he0 : 0 < e := lt_min hδ one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heδ : e ≤ δ := min_le_left _ _
  obtain ⟨B, hB⟩ := ridout_smooth P (e / 2) (by positivity)
  refine ⟨max 1 ⌈((B : ℝ) + 1) ^ (1 / e)⌉₊, ?_⟩
  intro x y hx hy hy0 hxy
  by_contra hne
  have hy1 : 1 < y := lt_of_le_of_lt (le_max_left _ _) hy0
  have hyR : (1 : ℝ) < y := by exact_mod_cast hy1
  have hy0R : (0 : ℝ) < y := by linarith
  have hxy' : |(x : ℝ) - y| ≤ (y : ℝ) ^ (1 - e) :=
    hxy.trans (Real.rpow_le_rpow_of_exponent_le hyR.le (by linarith))
  have hgpos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_right _ (by omega)
  set g := Nat.gcd x y with hg
  have hxg : x = g * (x / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)).symm
  have hyg : y = g * (y / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)).symm
  have hcop : Nat.Coprime (x / g) (y / g) := Nat.coprime_div_gcd_div_gcd hgpos
  set a := x / g
  set b := y / g
  have ha : a ∈ Nat.smoothNumbers P := Nat.mem_smoothNumbers_of_dvd hx (Dvd.intro_left _ hxg.symm)
  have hb : b ∈ Nat.smoothNumbers P := Nat.mem_smoothNumbers_of_dvd hy (Dvd.intro_left _ hyg.symm)
  have hab : a ≠ b := by
    intro h; apply hne; rw [hxg, hyg, h]
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hgpos
  have hxR : (x : ℝ) = g * a := by rw [hxg]; push_cast; ring
  have hyR' : (y : ℝ) = g * b := by rw [hyg]; push_cast; ring
  have habs : |(x : ℝ) - y| = g * |(a : ℝ) - b| := by
    rw [hxR, hyR', ← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ g)]
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hpow_pos : (0 : ℝ) < (y : ℝ) ^ (1 - e) := Real.rpow_pos_of_pos hy0R _
  rcases le_or_gt (max a b) B with hM | hM
  · -- small cofactors
    have hbB : (b : ℝ) ≤ B := by exact_mod_cast (le_max_right a b).trans hM
    have hg_le : (g : ℝ) ≤ (y : ℝ) ^ (1 - e) := by
      calc (g : ℝ) = g * 1 := by ring
        _ ≤ g * |(a : ℝ) - b| := by gcongr
        _ = |(x : ℝ) - y| := habs.symm
        _ ≤ _ := hxy'
    have hyc : (⌈((B : ℝ) + 1) ^ (1 / e)⌉₊ : ℝ) < y := by
      exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hy0
    have hye : ((B : ℝ) + 1) < (y : ℝ) ^ e := by
      have h2 : ((B : ℝ) + 1) ^ (1 / e) < y := lt_of_le_of_lt (Nat.le_ceil _) hyc
      have h3 := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) h2 he0
      rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ he0.ne', Real.rpow_one]
        at h3
    have hsplit : (y : ℝ) = (y : ℝ) ^ (1 - e) * (y : ℝ) ^ e := by
      rw [← Real.rpow_add hy0R]; simp
    have : (y : ℝ) ≤ (y : ℝ) ^ (1 - e) * B := by
      calc (y : ℝ) = g * b := hyR'
        _ ≤ (y : ℝ) ^ (1 - e) * B := by
          apply mul_le_mul hg_le hbB (by positivity) hpow_pos.le
    have : (y : ℝ) ^ (1 - e) * B < (y : ℝ) ^ (1 - e) * (y : ℝ) ^ e := by
      apply mul_lt_mul_of_pos_left _ hpow_pos; linarith
    linarith
  · -- large cofactors: Ridout
    have hR := hB a b ha hb hcop hM
    have hlt : (y : ℝ) ^ (1 - e) < (y : ℝ) ^ (1 - e / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt hyR (by linarith)
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hbM : (b : ℝ) ≤ ((max a b : ℕ) : ℝ) := by exact_mod_cast le_max_right a b
    have hge : (y : ℝ) ^ (1 - e / 2) ≤ |(x : ℝ) - y| := by
      rw [habs, hyR', Real.mul_rpow (by linarith) hb0]
      calc (g : ℝ) ^ (1 - e / 2) * (b : ℝ) ^ (1 - e / 2)
          ≤ (g : ℝ) * ((max a b : ℕ) : ℝ) ^ (1 - e / 2) := by
            apply mul_le_mul
            · calc (g : ℝ) ^ (1 - e / 2) ≤ (g : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le hgR (by linarith)
                _ = g := Real.rpow_one _
            · exact Real.rpow_le_rpow hb0 hbM (by linarith)
            · exact Real.rpow_nonneg hb0 _
            · linarith
        _ ≤ g * |(a : ℝ) - b| := by gcongr
    linarith

end Erdos494
