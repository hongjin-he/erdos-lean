import ErdosLean.Erdos956Upper.Defs

/-!
# Erdős #956 upper bound — P12: binomial subset averages

`∑_{T ⊆ S ⊆ V} p^{|S|} (1-p)^{|V|-|S|} = p^{|T|}` (`Finset.prod_add`).
-/

namespace Erdos956Upper

open Erdos956 Metric

theorem sum_weight_subset {α : Type*} [DecidableEq α] (V T : Finset α) (hT : T ⊆ V) (p : ℝ) :
    ∑ S ∈ V.powerset, (if T ⊆ S then p ^ S.card * (1 - p) ^ (V.card - S.card) else 0) =
      p ^ T.card := by
  rw [← Finset.sum_filter]
  have hre : ∑ S ∈ V.powerset.filter (fun S => T ⊆ S), p ^ S.card * (1 - p) ^ (V.card - S.card)
      = ∑ U ∈ (V \ T).powerset,
          p ^ (T ∪ U).card * (1 - p) ^ (V.card - (T ∪ U).card) := by
    symm
    apply Finset.sum_nbij' (fun U => T ∪ U) (fun S => S \ T)
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      exact ⟨Finset.union_subset hT (hU.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact Finset.sdiff_subset_sdiff hS.1 le_rfl
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      have hd : Disjoint T U := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        subst hab
        have := hU hb
        simp [Finset.mem_sdiff] at this
        exact this.2 ha
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hd.symm]
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.union_sdiff_of_subset hS.2
    · intro U hU
      rfl
  rw [hre]
  have key : ∀ U ∈ (V \ T).powerset,
      p ^ (T ∪ U).card * (1 - p) ^ (V.card - (T ∪ U).card)
        = p ^ T.card * (p ^ U.card * (1 - p) ^ ((V \ T).card - U.card)) := by
    intro U hU
    rw [Finset.mem_powerset] at hU
    have hd : Disjoint T U := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      have := hU hb
      simp [Finset.mem_sdiff] at this
      exact this.2 ha
    rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hT, pow_add]
    have : V.card - (T.card + U.card) = V.card - T.card - U.card := by omega
    rw [this]; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
  simp
