import ErdosLean.Erdos996.Defs

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

namespace DigitIndep

/-- Haar measure on `𝕋` computed on `[0,1)` in `ℝ`. -/
lemma haar_eq (U : Set 𝕋) (hU : MeasurableSet U) :
    μ𝕋 U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' U)) := by
  have h1 : (volume : Measure 𝕋) = μ𝕋 := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma digit_mk (j : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 (y : 𝕋) : ℝ)) =
      Int.fract ((2 : ℝ) ^ j * y) := by
  rw [coe_equivIco_mk_apply, div_one, mul_one]
  have hy : Int.fract y = y - ⌊y⌋ := rfl
  have : (2 : ℝ) ^ j * ⌊y⌋ = ((2 ^ j * ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [hy, mul_sub, this, Int.fract_sub_intCast]

lemma digit_shift {A j : ℕ} (hj : A ≤ j) (m : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A)) = Int.fract ((2 : ℝ) ^ j * y) := by
  have h : (2 : ℝ) ^ j = 2 ^ (j - A) * 2 ^ A := by rw [← pow_add, Nat.sub_add_cancel hj]
  have : (2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A) = 2 ^ j * y + ((m * 2 ^ (j - A) : ℕ) : ℝ) := by
    rw [h]; push_cast; field_simp
  rw [this, Int.fract_add_natCast]

lemma fract_lt_half_iff (u : ℝ) : Int.fract u < 2⁻¹ ↔ ⌊2 * u⌋ % 2 = 0 := by
  have h1 := Int.fract_nonneg u
  have h2 := Int.fract_lt_one u
  have h3 : (⌊u⌋ : ℝ) + Int.fract u = u := Int.floor_add_fract u
  by_cases hf : Int.fract u < 2⁻¹
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp [hf]
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp only [hf, false_iff]; omega

lemma floor_le_of_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (hy : (m : ℝ) ≤ 2 ^ A * y') (hy' : 2 ^ A * y < m + 1) :
    ⌊2 * (2 ^ j * y)⌋ ≤ ⌊2 * (2 ^ j * y')⌋ := by
  by_contra hlt
  push_neg at hlt
  have e1 : 2 * (2 ^ j * y') < (⌊2 * (2 ^ j * y')⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have e2 : ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) ≤ 2 * (2 ^ j * y) :=
    (Int.cast_le.mpr (Int.add_one_le_of_lt hlt)).trans (Int.floor_le _)
  have hA : (2 : ℝ) ^ A = 2 * 2 ^ j * 2 ^ (A - j - 1) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (A - j - 1) := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) :=
    ⟨2 ^ (A - j - 1) * (⌊2 * (2 ^ j * y')⌋ + 1), by push_cast; ring⟩
  have h1 : (m : ℝ) < c :=
    calc (m : ℝ) ≤ 2 ^ A * y' := hy
      _ = 2 ^ (A - j - 1) * (2 * (2 ^ j * y')) := by rw [hA]; ring
      _ < 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left e1 hpos
      _ = c := hc.symm
  have h2 : (c : ℝ) < m + 1 :=
    calc (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) := by
          rw [hc]; push_cast; ring
      _ ≤ 2 ^ (A - j - 1) * (2 * (2 ^ j * y)) := mul_le_mul_of_nonneg_left e2 hpos.le
      _ = 2 ^ A * y := by rw [hA]; ring
      _ < m + 1 := hy'
  have h1' : m < c := by exact_mod_cast h1
  have h2' : c < m + 1 := by exact_mod_cast h2
  omega

lemma digit_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (h1 : (m : ℝ) ≤ 2 ^ A * y) (h2 : 2 ^ A * y < m + 1)
    (h1' : (m : ℝ) ≤ 2 ^ A * y') (h2' : 2 ^ A * y' < m + 1) :
    Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * y') < 2⁻¹ := by
  rw [fract_lt_half_iff, fract_lt_half_iff,
    le_antisymm (floor_le_of_block hj h1' h2) (floor_le_of_block hj h1 h2')]

/-- Intended reading of `DeterminedByWindow` (with the `↔` inside the window binder). -/
def StrongDet (a b : ℕ) (E : Set 𝕋) : Prop :=
  ∀ x y : 𝕋, (∀ j, a ≤ j → j < b →
      (Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹)) → (x ∈ E ↔ y ∈ E)

/-- The point keeping the binary digits of `y` in the window `[a,b)` and zeroing the others. -/
noncomputable def proj (a b : ℕ) (y : ℝ) : ℝ :=
  ((⌊(2 : ℝ) ^ b * y⌋ - 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ : ℤ) : ℝ) / 2 ^ b

lemma proj_digits {a b : ℕ} (hab : a ≤ b) (y : ℝ) (j : ℕ) :
    (a ≤ j → j < b → (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹)) ∧
    (¬(a ≤ j ∧ j < b) → Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹) := by
  have hK1 : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := Int.floor_le _
  have hK2 : (2 : ℝ) ^ b * y < ⌊(2 : ℝ) ^ b * y⌋ + 1 := Int.lt_floor_add_one _
  have hL1 : (⌊(2 : ℝ) ^ a * y⌋ : ℝ) ≤ 2 ^ a * y := Int.floor_le _
  have hL2 : (2 : ℝ) ^ a * y < ⌊(2 : ℝ) ^ a * y⌋ + 1 := Int.lt_floor_add_one _
  have hba : (2 : ℝ) ^ b = 2 ^ (b - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hpb : (0 : ℝ) < 2 ^ b := by positivity
  have hpba : (0 : ℝ) < 2 ^ (b - a) := by positivity
  have hN0 : 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ ≤ ⌊(2 : ℝ) ^ b * y⌋ := by
    rw [Int.le_floor]; push_cast; rw [hba, mul_assoc]
    exact mul_le_mul_of_nonneg_left hL1 hpba.le
  have hN1 : ⌊(2 : ℝ) ^ b * y⌋ < 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) := by
    have : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) <
        ((2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) : ℤ) : ℝ) := by
      push_cast
      calc (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := hK1
        _ = 2 ^ (b - a) * (2 ^ a * y) := by rw [hba]; ring
        _ < 2 ^ (b - a) * ((⌊(2 : ℝ) ^ a * y⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left hL2 hpba
        _ = _ := by ring
    exact_mod_cast this
  set K := ⌊(2 : ℝ) ^ b * y⌋ with hK
  set L := ⌊(2 : ℝ) ^ a * y⌋ with hL
  set N : ℤ := K - 2 ^ (b - a) * L with hN
  have hN0' : (0 : ℝ) ≤ N := by
    have : (0 : ℤ) ≤ N := by rw [hN]; linarith
    exact_mod_cast this
  have hN1' : (N : ℝ) + 1 ≤ 2 ^ (b - a) := by
    have : N + 1 ≤ 2 ^ (b - a) := by rw [hN]; linarith
    exact_mod_cast this
  have hp : proj a b y = (N : ℝ) / 2 ^ b := rfl
  constructor
  · intro h1 h2
    have hja : (2 : ℝ) ^ j = 2 ^ (j - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h1]
    have e : (2 : ℝ) ^ j * proj a b y = 2 ^ j * ((K : ℝ) / 2 ^ b) - ((2 ^ (j - a) * L : ℤ) : ℝ) := by
      rw [hp, hN]; push_cast; rw [hja, hba]; field_simp
    rw [e, Int.fract_sub_intCast]
    have e2 : (2 : ℝ) ^ b * ((K : ℝ) / 2 ^ b) = K := by field_simp
    exact digit_block h2 (m := K) hK1 hK2 (le_of_eq e2.symm) (by rw [e2]; linarith)
  · intro hj
    by_cases hjb : b ≤ j
    · have hjb' : (2 : ℝ) ^ j = 2 ^ (j - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hjb]
      have e : (2 : ℝ) ^ j * proj a b y = ((N * 2 ^ (j - b) : ℤ) : ℝ) := by
        rw [hp, hjb']; push_cast; field_simp
      rw [e, Int.fract_intCast]; norm_num
    · have hja : j < a := by omega
      have h2j : (2 : ℝ) * 2 ^ j ≤ 2 ^ a := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hja
      have hlt : 2 * (2 ^ j * (N : ℝ)) < 2 ^ b :=
        calc 2 * (2 ^ j * (N : ℝ)) = (2 * 2 ^ j) * N := by ring
          _ ≤ 2 ^ a * N := mul_le_mul_of_nonneg_right h2j hN0'
          _ < 2 ^ a * 2 ^ (b - a) := mul_lt_mul_of_pos_left (by linarith) hpa
          _ = 2 ^ b := by rw [hba]; ring
      have h0 : 0 ≤ (2 : ℝ) ^ j * proj a b y := by
        rw [hp]; exact mul_nonneg (by positivity) (div_nonneg hN0' hpb.le)
      have hhalf : (2 : ℝ) ^ j * proj a b y < 2⁻¹ := by
        rw [hp, ← mul_div_assoc, div_lt_iff₀ hpb]; linarith
      rw [Int.fract_eq_self.mpr ⟨h0, by linarith⟩]
      exact hhalf

lemma strong_of_det {a b : ℕ} {E : Set 𝕋} (hE : DeterminedByWindow a b E) : StrongDet a b E := by
  intro x x' hxx'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective x'
  by_cases hab : a ≤ b
  · have key : ∀ w : ℝ, (∀ j, a ≤ j → j < b →
        (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * w) < 2⁻¹)) →
        (((w : ℝ) : 𝕋) ∈ E ↔ ((proj a b y : ℝ) : 𝕋) ∈ E) := by
      intro w hw
      apply hE
      intro j
      rw [digit_mk, digit_mk]
      by_cases hj : a ≤ j ∧ j < b
      · have hc := (hw j hj.1 hj.2).symm.trans ((proj_digits hab y j).1 hj.1 hj.2)
        constructor
        · intro h; exact hc.1 (h hj.1 hj.2)
        · intro h _ _; exact hc.2 h
      · have := (proj_digits hab y j).2 hj
        constructor
        · intro _; exact this
        · intro _ h1 h2; exact absurd ⟨h1, h2⟩ hj
    refine (key y (fun j _ _ => Iff.rfl)).trans (key y' (fun j h1 h2 => ?_)).symm
    have := hxx' j h1 h2
    rwa [digit_mk, digit_mk] at this
  · have key : ∀ w : ℝ, (((w : ℝ) : 𝕋) ∈ E ↔ (((0 : ℝ) : ℝ) : 𝕋) ∈ E) := by
      intro w
      apply hE
      intro j
      rw [digit_mk, digit_mk, mul_zero, Int.fract_zero]
      constructor
      · intro _; norm_num
      · intro _ h1 h2; omega
    exact (key y).trans (key y').symm

/-- The dyadic interval `[m/2^A, (m+1)/2^A)`. -/
def dyBlock (A m : ℕ) : Set ℝ := {y | (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1}

lemma mem_dyBlock {A m : ℕ} {y : ℝ} :
    y ∈ dyBlock A m ↔ (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1 := Iff.rfl

lemma measurableSet_dyBlock (A m : ℕ) : MeasurableSet (dyBlock A m) :=
  show MeasurableSet ({y : ℝ | (m : ℝ) ≤ 2 ^ A * y} ∩ {y : ℝ | 2 ^ A * y < m + 1}) from
    (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)

lemma Ico_decomp (A : ℕ) (X : Set ℝ) (hX : MeasurableSet X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ X) = ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ X) := by
  have hpos : (0 : ℝ) < 2 ^ A := by positivity
  have hset : Set.Ico (0 : ℝ) 1 ∩ X = ⋃ m ∈ range (2 ^ A), (dyBlock A m ∩ X) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop,
      mem_dyBlock]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      have hnn : 0 ≤ (2 : ℝ) ^ A * y := mul_nonneg hpos.le h0
      refine ⟨⌊(2 : ℝ) ^ A * y⌋₊, ?_, ⟨Nat.floor_le hnn, Nat.lt_floor_add_one _⟩, hx⟩
      rw [Nat.floor_lt hnn]; push_cast
      calc (2 : ℝ) ^ A * y < 2 ^ A * 1 := mul_lt_mul_of_pos_left h1 hpos
        _ = 2 ^ A := mul_one _
    · rintro ⟨m, hm, ⟨h1, h2⟩, hx⟩
      have hm' : (m : ℝ) + 1 ≤ 2 ^ A := by exact_mod_cast Nat.succ_le_of_lt hm
      refine ⟨⟨?_, ?_⟩, hx⟩
      · by_contra h
        push_neg at h
        have := mul_neg_of_pos_of_neg hpos h
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      · by_contra h
        push_neg at h
        have := mul_le_mul_of_nonneg_left h hpos.le
        linarith
  rw [hset, measure_biUnion_finset]
  · intro m _ m' _ hne
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨⟨a1, a2⟩, _⟩ ⟨⟨b1, b2⟩, _⟩
    have e1 : (m : ℝ) < m' + 1 := by linarith
    have e2 : (m' : ℝ) < m + 1 := by linarith
    have e1' : m < m' + 1 := by exact_mod_cast e1
    have e2' : m' < m + 1 := by exact_mod_cast e2
    exact hne (by omega)
  · intro m _
    exact (measurableSet_dyBlock A m).inter hX

lemma dyBlock_shift (A m : ℕ) (X : Set ℝ) (hinv : ∀ y : ℝ, y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (dyBlock A m ∩ X) = volume (dyBlock A 0 ∩ X) := by
  have : dyBlock A 0 ∩ X = (fun y => y + (m : ℝ) / 2 ^ A) ⁻¹' (dyBlock A m ∩ X) := by
    ext y
    have e : (2 : ℝ) ^ A * (y + m / 2 ^ A) = 2 ^ A * y + m := by
      rw [mul_add]; congr 1; field_simp
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_dyBlock, e, hinv, Nat.cast_zero]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [this, measure_preimage_add_right]

open Classical in
lemma sum_formula (A : ℕ) (G X : Set ℝ) (hG : MeasurableSet G) (hX : MeasurableSet X)
    (hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ G) ∨ (∀ y ∈ dyBlock A m, y ∉ G))
    (hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ (G ∩ X)) =
      ((range (2 ^ A)).filter (fun m => ∀ y ∈ dyBlock A m, y ∈ G)).card *
        volume (dyBlock A 0 ∩ X) := by
  rw [Ico_decomp A _ (hG.inter hX)]
  calc ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ (G ∩ X))
      = ∑ m ∈ range (2 ^ A),
          (if (∀ y ∈ dyBlock A m, y ∈ G) then volume (dyBlock A 0 ∩ X) else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases h : ∀ y ∈ dyBlock A m, y ∈ G
        · rw [if_pos h, ← dyBlock_shift A m X (hinv m)]
          congr 1
          ext y
          constructor
          · rintro ⟨hy, _, hx⟩; exact ⟨hy, hx⟩
          · rintro ⟨hy, hx⟩; exact ⟨hy, h y hy, hx⟩
        · rw [if_neg h]
          have h' := (hblock m).resolve_left h
          have : dyBlock A m ∩ (G ∩ X) = ∅ :=
            Set.subset_empty_iff.mp (fun y hy => (h' y hy.1 hy.2.1).elim)
          rw [this, measure_empty]
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma ennreal_aux (cG cU u t : ENNReal) (h : cU * u = 1) : cG * t = cG * u * (cU * t) := by
  calc cG * t = cG * t * (cU * u) := by rw [h, mul_one]
    _ = cG * u * (cU * t) := by ring

/-- Two-window independence: a set determined by digits `[0,A)` and a set determined by
digits `[A,B)` are independent. -/
lemma indep_two {A B : ℕ} {F E : Set 𝕋} (hF : StrongDet 0 A F)
    (hE : StrongDet A B E) (mF : MeasurableSet F) (mE : MeasurableSet E) :
    μ𝕋 (F ∩ E) = μ𝕋 F * μ𝕋 E := by
  have hG : MeasurableSet (((↑) : ℝ → 𝕋) ⁻¹' F) := AddCircle.measurable_mk' mF
  have hX : MeasurableSet (((↑) : ℝ → 𝕋) ⁻¹' E) := AddCircle.measurable_mk' mE
  have hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → 𝕋) ⁻¹' F) ∨
      (∀ y ∈ dyBlock A m, y ∉ ((↑) : ℝ → 𝕋) ⁻¹' F) := by
    intro m
    by_cases h : ∃ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → 𝕋) ⁻¹' F
    · left
      obtain ⟨y0, hy0, hy0G⟩ := h
      intro y hy
      rw [mem_dyBlock] at hy0 hy
      exact (hF (y0 : 𝕋) (y : 𝕋) (fun j _ hj => by
        rw [digit_mk, digit_mk]
        exact digit_block hj (m := (m : ℤ)) (by exact_mod_cast hy0.1) (by exact_mod_cast hy0.2)
          (by exact_mod_cast hy.1) (by exact_mod_cast hy.2))).1 hy0G
    · right
      push_neg at h
      exact h
  have hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ ((↑) : ℝ → 𝕋) ⁻¹' E ↔
      y ∈ ((↑) : ℝ → 𝕋) ⁻¹' E := by
    intro m y
    apply hE
    intro j hj _
    rw [digit_mk, digit_mk, digit_shift hj]
  have hinvU : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ (Set.univ : Set ℝ) ↔
      y ∈ (Set.univ : Set ℝ) := fun _ _ => Iff.rfl
  have hblockU : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ (Set.univ : Set ℝ)) ∨
      (∀ y ∈ dyBlock A m, y ∉ (Set.univ : Set ℝ)) := fun _ => Or.inl fun _ _ => trivial
  have kFE := sum_formula A _ _ hG hX hblock hinv
  have kF := sum_formula A _ _ hG MeasurableSet.univ hblock hinvU
  have kE := sum_formula A _ _ MeasurableSet.univ hX hblockU hinv
  have kU := sum_formula A _ _ MeasurableSet.univ MeasurableSet.univ hblockU hinvU
  rw [haar_eq _ (mF.inter mE), haar_eq _ mF, haar_eq _ mE]
  have e1 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' (F ∩ E))) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → 𝕋) ⁻¹' F) ∩ (((↑) : ℝ → 𝕋) ⁻¹' E))) := rfl
  have e2 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' F)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → 𝕋) ⁻¹' F) ∩ Set.univ)) := by
    rw [Set.inter_univ]
  have e3 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → 𝕋) ⁻¹' E)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ (Set.univ ∩ (((↑) : ℝ → 𝕋) ⁻¹' E))) := by
    rw [Set.univ_inter]
  have e4 : volume (Set.Ico (0 : ℝ) 1 ∩ ((Set.univ : Set ℝ) ∩ Set.univ)) = 1 := by simp
  rw [e1, e2, e3, kFE, kF, kE]
  rw [kU] at e4
  exact ennreal_aux _ _ _ _ e4

lemma det_mono {a b a' b' : ℕ} {E : Set 𝕋} (h : StrongDet a b E)
    (hw : ∀ j, a ≤ j → j < b → a' ≤ j ∧ j < b') : StrongDet a' b' E :=
  fun x y hxy => h x y (fun j h1 h2 => hxy j (hw j h1 h2).1 (hw j h1 h2).2)

lemma det_iInter {ι : Type*} {a b : ℕ} (s : Finset ι) (E : ι → Set 𝕋)
    (h : ∀ i ∈ s, StrongDet a b (E i)) : StrongDet a b (⋂ i ∈ s, E i) := by
  intro x y hxy
  simp only [Set.mem_iInter]
  exact forall₂_congr fun i hi => h i hi x y hxy

end DigitIndep

open DigitIndep in
/-- Sets determined by pairwise disjoint digit windows are independent under Haar measure. -/
lemma measure_iInter_of_disjoint_windows {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (E : ι → Set 𝕋) (hE : ∀ i ∈ s, DeterminedByWindow (a i) (b i) (E i))
    (hmeas : ∀ i ∈ s, MeasurableSet (E i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    μ𝕋 (⋂ i ∈ s, E i) = ∏ i ∈ s, μ𝕋 (E i) := by
  classical
  have hE' : ∀ i ∈ s, StrongDet (a i) (b i) (E i) := fun i hi => strong_of_det (hE i hi)
  clear hE
  revert hE' hmeas hdisj
  induction s using Finset.induction_on_max_value (f := b) with
  | empty => intro _ _ _; simp
  | insert i s hi hmax ih =>
    intro hmeas hdisj hE
    rw [Finset.prod_insert hi, Finset.set_biInter_insert, Set.inter_comm]
    have hF : StrongDet 0 (a i) (⋂ j ∈ s, E j) := by
      refine det_iInter s E (fun j hj => det_mono (hE j (Finset.mem_insert_of_mem hj)) ?_)
      intro k hk1 hk2
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hb := hmax j hj
      rcases hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) hij with h | h
      · omega
      · omega
    rw [indep_two hF (hE i (Finset.mem_insert_self i s))
      (Finset.measurableSet_biInter s (fun j hj => hmeas j (Finset.mem_insert_of_mem hj)))
      (hmeas i (Finset.mem_insert_self i s))]
    rw [ih (fun j hj => hmeas j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj => hE j (Finset.mem_insert_of_mem hj)),
      mul_comm]

end Erdos996
