import ErdosLean.Erdos612.Defs
import ErdosLean.Erdos612.Parts.Data
import ErdosLean.Erdos612.Parts.Periodic
import ErdosLean.Erdos612.Parts.Card
import ErdosLean.Erdos612.Parts.MinDegree
import ErdosLean.Erdos612.Parts.CliqueFree
import ErdosLean.Erdos612.Parts.Connected
import ErdosLean.Erdos612.Parts.DiamLower
import ErdosLean.Erdos612.Parts.Transfer
import ErdosLean.Erdos612.Parts.Uniform
import ErdosLean.Erdos612.Parts.Growth
import ErdosLean.Erdos612.Parts.Coeff

/-!
# Erdős Problem 612 (JSP-000497): main theorem

Both parts of the Erdős–Pach–Pollack–Tuza conjecture are false:
* part (i) at `r = 2` (`K₄`-free, `8 ∣ δ`, coefficient `16/7`) is refuted by the blow-ups of
  the Czabarka–Singgih–Székely layer sequences with `δ = 24`;
* part (ii) at `r = 4` (`K₉`-free, `11 ∣ δ`, coefficient `11/4`) is refuted by the blow-ups of
  the Chen–Chen layer sequences with `δ = 8778`.

The generic engine `not_diamBound_of_fam` turns a periodic layer sequence whose two-period
instance passes the `decide` checks of `Parts/Data.lean`, and whose period has
`c · (period weight) < (period length) · δ`, into a refutation of `DiamBound`.

The headline theorem is `erdos_612 : Erdos612Answer`, which refutes each part separately (in
both readings of `O(1)`).  `erdos_612_false : ¬ Erdos612Conjecture` is a corollary.
-/

open SimpleGraph

namespace Erdos612

/-- **Engine.**  A periodic family of layered blow-ups refutes `DiamBound s m c`. -/
theorem not_diamBound_of_fam {s m δ : ℕ} {c : ℝ} (pre per suf : Layers) (hper2 : 2 ≤ per.length)
    (hδ : 2 ≤ δ) (hm : m ∣ δ)
    (hpos : AllWin PosQ (fam pre per suf 2)) (hdeg : AllWin (DegQ δ) (fam pre per suf 2))
    (ht : SomeWin (TightQ δ) (fam pre per suf 2)) (hcl : AllWin (CliqQ s) (fam pre per suf 2))
    (hgrow : c * (per.total : ℝ) < (per.length : ℝ) * δ) :
    ¬ DiamBound s m c := by
  intro H
  obtain ⟨C, hC⟩ := diamBoundType_of_diamBound H δ hδ hm
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
  have hper : per ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hperlen : 1 ≤ per.length := by omega
  apply linear_escape (per.length : ℝ) (c * per.total / δ)
    ((pre.length + 2 * per.length + suf.length : ℕ) : ℝ)
    (c * ((pre.total + 2 * per.total + suf.total : ℕ) : ℝ) / δ + C + 1)
  · rw [div_lt_iff₀ hδ0]; exact hgrow
  intro p
  set L := fam pre per suf (p + 2) with hL
  have hlen : L.length = pre.length + (p + 2) * per.length + suf.length := length_fam _ _ _ _
  have hlen2 : 2 ≤ L.length := by rw [hlen]; nlinarith
  have hpos' := allWin_fam hper2 hpos p
  have hconn : (blowup L).Connected := connected_blowup L hlen2 hpos'
  have hcf : (blowup L).CliqueFree s :=
    cliqueFree_blowup L s (List.ne_nil_of_length_pos (by omega)) (allWin_fam hper2 hcl p)
  have hmin : (blowup L).minDegree = δ :=
    minDegree_blowup L δ hpos' (allWin_fam hper2 hdeg p) (someWin_fam hper ht p)
  have key := hC (Vtx L) (blowup L) hconn hcf hmin
  rw [card_vtx, hL, total_fam] at key
  have hd := length_le_diam L hpos' hconn
  rw [hlen] at hd
  have hd' : ((pre.length + (p + 2) * per.length + suf.length : ℕ) : ℝ)
      ≤ ((blowup L).diam : ℝ) + 1 := by exact_mod_cast hd
  push_cast at hd' key ⊢
  have e : c * ((pre.total : ℝ) + ((p : ℝ) + 2) * per.total + suf.total) / δ
      = c * per.total / δ * p + c * (pre.total + 2 * per.total + suf.total) / δ := by
    field_simp; ring
  rw [e] at key
  nlinarith

/-- Part (i) fails at `r = 2`. -/
theorem not_evenConjAt_two : ¬ EvenConjAt 2 := by
  unfold EvenConjAt
  rw [evenCoeff_two]
  refine not_diamBound_of_fam (δ := 24) cssPre cssPer cssSuf
    (by rw [cssPer_len]; norm_num) (by norm_num) (by norm_num) css_pos css_deg css_tight css_cliq ?_
  rw [show cssPer.total = 73 from cssPer_sum, cssPer_len]
  norm_num

/-- Part (ii) fails at `r = 4`. -/
theorem not_oddConjAt_four : ¬ OddConjAt 4 := by
  unfold OddConjAt
  rw [oddCoeff_four]
  refine not_diamBound_of_fam (δ := 8778) ccPre ccPer ccSuf
    (by rw [ccPer_len]; norm_num) (by norm_num) (by norm_num) cc_pos cc_deg cc_tight cc_cliq ?_
  rw [show ccPer.total = 60647 from ccPer_sum, ccPer_len]
  norm_num

/-- **Erdős #612**: both parts of the conjecture are false, in the weak and in the uniform
reading of `O(1)`. -/
theorem erdos_612 : Erdos612Answer := by
  refine ⟨fun h => not_evenConjAt_two (h 2 le_rfl), fun h => not_oddConjAt_four (h 4 (by norm_num)),
    fun h => not_evenConjAt_two (diamBound_of_uniform (h 2 le_rfl)),
    fun h => not_oddConjAt_four (diamBound_of_uniform (h 4 (by norm_num))),
    not_evenConjAt_two, not_oddConjAt_four⟩

/-- The negation of the conjecture as stated. -/
theorem erdos_612_false : ¬ Erdos612Conjecture := fun h => erdos_612.1 h.1

end Erdos612
