module

public import GroupDimension.TaharaProof.Decode11

@[expose] public section

/-!
# `g = gen τ`

The `A₃ ⊕ A₄` part of the combination of the relations is the symbol of Tahara's generator
`gen τ` modulo (I); by the injectivity of the symbol, `g = gen τ` (`eq_gen`).
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4) (ho4 : ∀ q, 1 < o4 q)

local notation "TF" => Tframe h4 hT hy4
local notation "TC" => Tframe_class4 h4 hT hy4 ho4

/-! ## The `A₃ ⊕ A₄` part of the combination -/

section Proj

variable (p : Fin T.u → ℤ) (U : Fin T.s × Fin T.s → ℤ) (V V' : Fin T.s × Fin T.t → ℤ)
  (W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ)

include ho4 in
theorem sI_mem_RI : sI h4 hT hy4 p ∈ (TF).RI := by
  unfold sI
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
  rw [← gI_T h4 hT hy4 ho4 l]
  exact Frame.gI_mem_RI (by simp)

theorem proj_sI : (TF).proj (sI h4 hT hy4 p) = sI h4 hT hy4 p := by
  simp [sI]

theorem proj_sII : (TF).proj (sII h4 hT hy4 U) =
    ∑ x, U x • (if x.1 < x.2 then
      -(T.q x.1 x.2 • (TF).S (tc (T.x₁ x.1 ^ T.d x.1) (T.x₁ x.2))) else 0) := by
  simp only [sII, map_sum, map_zsmul, map_ite0, map_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · simp [XII, Frame.proj_S, cc_ℓ1]
  · rfl

theorem proj_sIII : (TF).proj (sIII h4 hT hy4 V) =
    ∑ x, V x • ∑ m, T.b x.1 m • (if x.2 < m then (TF).A4 (tc (T.x₂ m) (T.x₂ x.2)) else 0) := by
  simp only [sIII, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [XIII, map_ite', map_ite0]

theorem proj_sIV : (TF).proj (sIV h4 hT hy4 V') = 0 := by
  simp [sIV, XIV]

theorem proj_sV : (TF).proj (sV h4 hT hy4 W5) =
    ∑ x, W5 x • (if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then
      (TF).A4 (tc (tc (T.x₁ x.1 ^ T.d x.1) (T.x₁ x.2.1)) (T.x₁ x.2.2)) else 0) := by
  simp only [sV, map_sum, map_zsmul, map_ite0, map_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · simp [XV, cc_ℓ1]
  · rfl

theorem proj_sVI : (TF).proj (sVI h4 hT hy4 W6) = 0 := by
  simp [sVI, XVI, map_ite0]

theorem proj_sVII : (TF).proj (sVII h4 hT hy4 W7) = 0 := by
  simp [sVII, XVII, map_ite0]

end Proj

/-! ## The symbol of `gen τ` -/

theorem mkQ_ite {M : Type*} [AddCommGroup M] [Module ℤ M] (N : Submodule ℤ M) (P : Prop)
    [Decidable P] (a : M) : N.mkQ (if P then a else 0) = if P then N.mkQ a else 0 := by
  split_ifs <;> simp

include hT in
theorem tc11_mem (i j : Fin T.s) :
    tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  ExpThree.tc_mem (i := 1) (j := 0) (by norm_num) ((IsLayerBasis.layerNF hT.basis₁).pow_mem i)
    (hT.basis₁.mem j)

include hT in
theorem tc22_mem (l k : Fin T.t) : tc (T.x₂ l) (T.x₂ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
  ExpThree.tc_mem (i := 1) (j := 1) (by norm_num) (hT.basis₂.mem l) (hT.basis₂.mem k)

include hT in
theorem tc111_mem (i j k : Fin T.s) :
    tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
  ExpThree.tc_mem (i := 2) (j := 0) (by norm_num) (tc11_mem hT i j) (hT.basis₁.mem k)

include ho4

theorem mkQ_S_ite_zpow (P : Prop) [Decidable P] {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (n : ℤ) : (TF).RI.mkQ ((TF).S (if P then z ^ n else 1)) =
      if P then n • (TF).RI.mkQ ((TF).S z) else 0 := by
  split_ifs
  · exact Frame.mkQ_S_zpow TC hz n
  · simp [Frame.S_one]

include h4 hT hy4 in
theorem genA_mem (τ : Coeffs T.s T.t) : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  Frame.ofFn_mem TC _ fun i => Frame.ofFn_mem TC _ fun j => by
    split_ifs
    · exact zpow_mem (tc11_mem hT i j) _
    · exact one_mem _

include h4 hT hy4 in
theorem genB_mem (τ : Coeffs T.s T.t) : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  Frame.ofFn_mem TC _ fun i => Frame.ofFn_mem TC _ fun k =>
    zpow_mem (Frame.ofFn_mem TC _ fun l => by
      split_ifs
      · exact zpow_mem (lcs_mem_of_le (by norm_num) (tc22_mem hT l k)) _
      · exact one_mem _) _

include h4 hT hy4 in
theorem genC_mem (τ : Coeffs T.s T.t) : T.genC τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  Frame.ofFn_mem TC _ fun i => Frame.ofFn_mem TC _ fun j => Frame.ofFn_mem TC _ fun k => by
    split_ifs
    · exact zpow_mem (lcs_mem_of_le (by norm_num) (tc111_mem hT i j k)) _
    · exact one_mem _

include h4 hT hy4 in
theorem gen_mem (τ : Coeffs T.s T.t) : T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  mul_mem (mul_mem (genA_mem h4 hT hy4 ho4 τ) (genB_mem h4 hT hy4 ho4 τ))
    (genC_mem h4 hT hy4 ho4 τ)

theorem mkQ_S_genA (τ : Coeffs T.s T.t) : (TF).RI.mkQ ((TF).S (T.genA τ)) =
    ∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) •
      (TF).RI.mkQ ((TF).S (tc (T.x₁ i ^ T.d i) (T.x₁ j))) else 0 := by
  unfold Data.genA
  rw [Frame.mkQ_S_ofFn TC _ fun i => Frame.ofFn_mem TC _ fun j => by
    split_ifs
    · exact zpow_mem (tc11_mem hT i j) _
    · exact one_mem _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Frame.mkQ_S_ofFn TC _ fun j => by
    split_ifs
    · exact zpow_mem (tc11_mem hT i j) _
    · exact one_mem _]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact mkQ_S_ite_zpow h4 hT hy4 ho4 _ (tc11_mem hT i j) _

theorem mkQ_S_genB (τ : Coeffs T.s T.t) : (TF).RI.mkQ ((TF).S (T.genB τ)) =
    ∑ i, ∑ k, τ.v i k • ∑ l, if k < l then T.b i l •
      (TF).RI.mkQ ((TF).A4 (tc (T.x₂ l) (T.x₂ k))) else 0 := by
  have h3 : ∀ l k : Fin T.t, tc (T.x₂ l) (T.x₂ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := fun l k =>
    lcs_mem_of_le (by norm_num) (tc22_mem hT l k)
  have hin : ∀ i k, (List.ofFn fun l => if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b i l
      else 1).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := fun i k => Frame.ofFn_mem TC _ fun l => by
    split_ifs
    · exact zpow_mem (h3 l k) _
    · exact one_mem _
  unfold Data.genB
  rw [Frame.mkQ_S_ofFn TC _ fun i => Frame.ofFn_mem TC _ fun k => zpow_mem (hin i k) _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Frame.mkQ_S_ofFn TC _ fun k => zpow_mem (hin i k) _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Frame.mkQ_S_zpow TC (hin i k), Frame.mkQ_S_ofFn TC _ fun l => by
    split_ifs
    · exact zpow_mem (h3 l k) _
    · exact one_mem _]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mkQ_S_ite_zpow h4 hT hy4 ho4 _ (h3 l k), Frame.S_of_mem4 TC (tc22_mem hT l k)]

theorem mkQ_S_genC (τ : Coeffs T.s T.t) : (TF).RI.mkQ ((TF).S (T.genC τ)) =
    ∑ i, ∑ j, ∑ k, if i ≤ j ∧ j ≤ k then τ.w i j k •
      (TF).RI.mkQ ((TF).A4 (tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k))) else 0 := by
  have h3 : ∀ i j k : Fin T.s, tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := fun i j k =>
    lcs_mem_of_le (by norm_num) (tc111_mem hT i j k)
  unfold Data.genC
  rw [Frame.mkQ_S_ofFn TC _ fun i => Frame.ofFn_mem TC _ fun j => Frame.ofFn_mem TC _ fun k => by
    split_ifs
    · exact zpow_mem (h3 i j k) _
    · exact one_mem _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Frame.mkQ_S_ofFn TC _ fun j => Frame.ofFn_mem TC _ fun k => by
    split_ifs
    · exact zpow_mem (h3 i j k) _
    · exact one_mem _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Frame.mkQ_S_ofFn TC _ fun k => by
    split_ifs
    · exact zpow_mem (h3 i j k) _
    · exact one_mem _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mkQ_S_ite_zpow h4 hT hy4 ho4 _ (h3 i j k), Frame.S_of_mem4 TC (tc111_mem hT i j k)]

/-! ## `g = gen τ` -/

variable {p : Fin T.u → ℤ} {U : Fin T.s × Fin T.s → ℤ} {V V' : Fin T.s × Fin T.t → ℤ}
  {W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ} {g : G}

set_option maxHeartbeats 1000000 in
theorem eq_gen (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (hS : (TF).S g = combx h4 hT hy4 p U V V' W5 W6 W7) :
    g = T.gen (tau U V V' W5 W6 W7) := by
  -- the symbol of `g`, modulo (I)
  have hR : (TF).S g = sI h4 hT hy4 p + (sII h4 hT hy4 U + sIII h4 hT hy4 V + sIV h4 hT hy4 V' +
      sV h4 hT hy4 W5 + sVI h4 hT hy4 W6 + sVII h4 hT hy4 W7) := by
    rw [hS, combx_eq]; abel
  have hP : (TF).S g = sI h4 hT hy4 p + (TF).proj (sII h4 hT hy4 U + sIII h4 hT hy4 V +
      sIV h4 hT hy4 V' + sV h4 hT hy4 W5 + sVI h4 hT hy4 W6 + sVII h4 hT hy4 W7) := by
    have := congrArg (TF).proj hR
    rw [Frame.proj_S, map_add, proj_sI] at this
    rw [this]
  have hg1 : (TF).RI.mkQ ((TF).S g) =
      (∑ x, U x • (if x.1 < x.2 then
        -(T.q x.1 x.2 • (TF).RI.mkQ ((TF).S (tc (T.x₁ x.1 ^ T.d x.1) (T.x₁ x.2)))) else 0)) +
      (∑ x, V x • ∑ m, T.b x.1 m • (if x.2 < m then
        (TF).RI.mkQ ((TF).A4 (tc (T.x₂ m) (T.x₂ x.2))) else 0)) +
      (∑ x, W5 x • (if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then
        (TF).RI.mkQ ((TF).A4 (tc (tc (T.x₁ x.1 ^ T.d x.1) (T.x₁ x.2.1)) (T.x₁ x.2.2)))
          else 0)) := by
    have h0 : (TF).RI.mkQ (sI h4 hT hy4 p) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact sI_mem_RI h4 hT hy4 ho4 p
    rw [hP, map_add, h0, zero_add]
    simp only [map_add, proj_sII, proj_sIII, proj_sIV, proj_sV, proj_sVI, proj_sVII, add_zero,
      map_sum, map_zsmul, _root_.map_neg, mkQ_ite]
  -- the symbol of `gen (tau U V V' W5 W6 W7)`, modulo (I)
  have hg2 : (TF).RI.mkQ ((TF).S (T.gen (tau U V V' W5 W6 W7))) = (TF).RI.mkQ ((TF).S g) := by
    rw [Data.gen, Frame.mkQ_S_mul TC (mul_mem (genA_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7))
      (genB_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7))) (genC_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7)), Frame.mkQ_S_mul TC
      (genA_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7)) (genB_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7)), mkQ_S_genA h4 hT hy4 ho4,
      mkQ_S_genB h4 hT hy4 ho4, mkQ_S_genC h4 hT hy4 ho4, hg1]
    congr 1; congr 1
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · show ((-U (i, j)) * T.q i j) • _ = U (i, j) • -(T.q i j • _)
        rw [mul_smul, neg_smul, zsmul_neg]
      · exact (zsmul_zero _).symm
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      show V (i, k) • _ = V (i, k) • _
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · rfl
      · exact (zsmul_zero _).symm
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      split_ifs
      · rfl
      · exact (zsmul_zero _).symm
  -- injectivity
  have hgen := gen_mem h4 hT hy4 ho4 (tau U V V' W5 W6 W7)
  have h0 : (TF).S (g * (T.gen (tau U V V' W5 W6 W7))⁻¹) ∈ (TF).RI := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
      Frame.mkQ_S_mul TC hg (inv_mem hgen)]
    have hinv := Frame.S_inv TC hgen
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_add] at hinv
    rw [eq_neg_of_add_eq_zero_left hinv, ← hg2, add_neg_cancel]
  exact mul_inv_eq_one.mp (Frame.eq_one_of_S_mem TC (mul_mem hg (inv_mem hgen)) h0)

end TFrame

end TaharaProof

end GroupDimension
