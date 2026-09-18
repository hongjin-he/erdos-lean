import ErdosLean.Erdos612.Defs

/-!
# Erdős 612: the two concrete periodic families and their `decide` checks

* `cssPre/cssPer/cssSuf`: Czabarka–Singgih–Székely, J. Combin. Theory Ser. B 151 (2021)
  38–45, doi:10.1016/j.jctb.2021.06.001; numbering as in the preprint arXiv:2009.02611v1
  (*On the maximum diameter of k-colorable graphs*), §3, Figure 1, Lemma 5 and Theorem 6,
  with `r = 2`, `s = r - 1 = 1`, `δ = 24` (so `⌊δ/2s⌋ = 12`, remainder `0`):
  the block `C_{1,24}` has layers `1 | 12,11 | 12 | 1 | 12 | 12,11 | 1`; the first and last
  blocks carry the `+1` modification.  The blow-up is `3`-colourable, hence `K₄`-free.
* `ccPre/ccPer/ccSuf`: H. Chen–Y. Chen (arXiv:2609.03346v1, §2, the graph `J_{p,r}` of
  Theorem 2.7) with `r = 4`,
  `δ = 8778 = 6(6r-5)(2r-1)(3r-1)`: `τ = 7`, `x = δ/τ = 1254`, `λ = ⌈δ/11⌉ = 798`,
  `a₁ = a₃ = 1254`, `η = 7973`, `z = 1703`, `g = 5`, `b_i = δ - 1254 i`, `c_i = 1254 (i+1)`.
  Weights inside a layer are the balanced split (`⌈·⌉` first).  The blow-up is
  `8`-colourable, hence `K₉`-free.
All checks are kernel `decide` (no compiled evaluation).
-/

namespace Erdos612

/-- CSS21 first (modified) block, `δ = 24`. -/
def cssPre : Layers := [[1], [12, 12], [12], [1], [12], [12, 11], [1]]
/-- CSS21 repeated block `C_{1,24}`. -/
def cssPer : Layers := [[1], [12, 11], [12], [1], [12], [12, 11], [1]]
/-- CSS21 last (modified) block. -/
def cssSuf : Layers := [[1], [12, 11], [12], [1], [12], [12, 12], [1]]

/-- CC26 prefix `L₁, L₂` (`r = 4`, `δ = 8778`). -/
def ccPre : Layers := [List.replicate 7 8778, [8778]]
/-- CC26 period `L₃, …, L₂₁` (`19 = 6r - 5` layers). -/
def ccPer : Layers :=
  [[1], List.replicate 6 1254, [1254, 1254], [1], List.replicate 5 1254,
    [1254, 1254, 1254], [1], [1254, 1254, 1254, 1254], [1254, 1254, 1254, 1254], [1],
    [1254, 1254, 1254], List.replicate 5 1254, [1], [1254, 1254], List.replicate 6 1254,
    [1], [418, 418, 418], [1595, 1595, 1595, 1594, 1594], [418, 418, 418]]
/-- CC26 suffix: right-hand junction, `L_{19p+4}`, `L_{19p+5}`. -/
def ccSuf : Layers := [[1], [8778], List.replicate 7 8778]

theorem cssPer_len : cssPer.length = 7 := rfl
theorem cssPer_sum : (cssPer.map List.sum).sum = 73 := by decide
theorem cssPre_sum : (cssPre.map List.sum).sum = 74 := by decide
theorem cssSuf_sum : (cssSuf.map List.sum).sum = 74 := by decide
theorem ccPer_len : ccPer.length = 19 := rfl
theorem ccPer_sum : (ccPer.map List.sum).sum = 60647 := by decide
theorem ccPre_sum : (ccPre.map List.sum).sum = 70224 := by decide
theorem ccSuf_sum : (ccSuf.map List.sum).sum = 70225 := by decide

theorem css_pos : AllWin PosQ (fam cssPre cssPer cssSuf 2) := by decide
theorem css_deg : AllWin (DegQ 24) (fam cssPre cssPer cssSuf 2) := by decide
theorem css_tight : SomeWin (TightQ 24) (fam cssPre cssPer cssSuf 2) := by decide
theorem css_cliq : AllWin (CliqQ 4) (fam cssPre cssPer cssSuf 2) := by decide

theorem cc_pos : AllWin PosQ (fam ccPre ccPer ccSuf 2) := by decide
theorem cc_deg : AllWin (DegQ 8778) (fam ccPre ccPer ccSuf 2) := by decide
theorem cc_tight : SomeWin (TightQ 8778) (fam ccPre ccPer ccSuf 2) := by decide
theorem cc_cliq : AllWin (CliqQ 9) (fam ccPre ccPer ccSuf 2) := by decide

end Erdos612
