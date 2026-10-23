module

public import GroupDimension.TaharaProof.Decode7

@[expose] public section

/-!
# Coordinates of the explicit relations

The coordinates of the explicit forms `XII, …, XVII` of the relations at Tahara's basis vectors.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

local notation "TF" => Tframe h4 hT hy4

attribute [-simp] Tframe_o1 Tframe_o2 Tframe_o3 Tframe_o4

theorem map_ite' {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) (P : Prop)
    [Decidable P] (a b : M) : f (if P then a else b) = if P then f a else f b := by
  split_ifs <;> rfl

macro "coord_tac" : tactic => `(tactic| (
  simp [XII, XIII, XIV, XV, XVI, XVII, ℓ1_inj,
    ℓ2_inj, ℓ3_inj, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    map_ite']
  try (split_ifs <;> simp_all <;> ring)))

/-! ## `E3` -/

theorem cE3_XII (x1 x2 a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XII h4 hT hy4 x1 x2) =
      (if a = x1 ∧ b = x1 ∧ c = x2 then T.q x1 x2 * ((T.d x1).choose 2 : ℤ) else 0) -
      (if a = x1 ∧ b = x2 ∧ c = x2 then ((T.d x2).choose 2 : ℤ) else 0) := by
  coord_tac

@[simp] theorem cE3_XIII (x1 : Fin T.s) (x2 : Fin T.t) (a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XIII h4 hT hy4 x1 x2) = 0 := by
  coord_tac

@[simp] theorem cE3_XIV (x1 : Fin T.s) (x2 : Fin T.t) (a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XIV h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cE3_XV (x1 x2 x3 a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XV h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 ∧ c = x3 then -(T.d x1 : ℤ) else 0 := by
  coord_tac

theorem cE3_XVI (x1 x2 x3 a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XVI h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 ∧ c = x3 then -(T.d x2 : ℤ) else 0 := by
  coord_tac

theorem cE3_XVII (x1 x2 x3 a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (XVII h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 ∧ c = x3 then -(T.d x3 : ℤ) else 0 := by
  coord_tac

/-! ## `E12` -/

theorem cE12_XII (x1 x2 i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XII h4 hT hy4 x1 x2) =
      (if i = x1 then T.b x2 k else 0) - (if i = x2 then T.q x1 x2 * T.b x1 k else 0) := by
  coord_tac

theorem cE12_XIII (x1 : Fin T.s) (x2 : Fin T.t) (i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XIII h4 hT hy4 x1 x2) =
      if i = x1 ∧ k = x2 then -(T.d x1 : ℤ) else 0 := by
  coord_tac

theorem cE12_XIV (x1 : Fin T.s) (x2 : Fin T.t) (i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XIV h4 hT hy4 x1 x2) =
      if i = x1 ∧ k = x2 then -(T.e x2 : ℤ) else 0 := by
  coord_tac

@[simp] theorem cE12_XV (x1 x2 x3 i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XV h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

@[simp] theorem cE12_XVI (x1 x2 x3 i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XVI h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

@[simp] theorem cE12_XVII (x1 x2 x3 i : Fin T.s) (k : Fin T.t) :
    (TF).cE12 (ℓ1 i, ℓ2 k) (XVII h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

/-! ## `S4` -/

theorem cS4_XII (x1 x2 a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XII h4 hT hy4 x1 x2) =
      (if a = x1 ∧ b = x1 ∧ c = x1 ∧ d = x2 then
        ((T.q x1 x2 * ((T.d x1).choose 3 : ℤ) : ℤ) : ZMod _) else 0) -
      (if a = x1 ∧ b = x2 ∧ c = x2 ∧ d = x2 then (((T.d x2).choose 3 : ℤ) : ZMod _)
        else 0) := by
  coord_tac

@[simp] theorem cS4_XIII (x1 : Fin T.s) (x2 : Fin T.t) (a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XIII h4 hT hy4 x1 x2) = 0 := by
  coord_tac

@[simp] theorem cS4_XIV (x1 : Fin T.s) (x2 : Fin T.t) (a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XIV h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cS4_XV (x1 x2 x3 a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XV h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x1 ∧ c = x2 ∧ d = x3 then -((((T.d x1).choose 2 : ℤ)) : ZMod _)
        else 0 := by
  coord_tac

theorem cS4_XVI (x1 x2 x3 a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XVI h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 ∧ c = x2 ∧ d = x3 then -((((T.d x2).choose 2 : ℤ)) : ZMod _)
        else 0 := by
  coord_tac

theorem cS4_XVII (x1 x2 x3 a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (XVII h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 ∧ c = x3 ∧ d = x3 then -((((T.d x3).choose 2 : ℤ)) : ZMod _)
        else 0 := by
  coord_tac

/-! ## `S22` -/

@[simp] theorem cS22_XII (x1 x2 a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XII h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cS22_XIII (x1 : Fin T.s) (x2 : Fin T.t) (a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XIII h4 hT hy4 x1 x2) =
      if a = x1 ∧ b = x1 ∧ m = x2 then
        -((((T.d x1).choose 2 : ℤ)) : ZMod _) else 0 := by
  coord_tac

@[simp] theorem cS22_XIV (x1 : Fin T.s) (x2 : Fin T.t) (a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XIV h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cS22_XV (x1 x2 x3 a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XV h4 hT hy4 x1 x2 x3) =
      if a = x2 ∧ b = x3 then ((T.b x1 m : ℤ) : ZMod _) else 0 := by
  coord_tac

theorem cS22_XVI (x1 x2 x3 a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XVI h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x3 then ((T.b x2 m : ℤ) : ZMod _) else 0 := by
  coord_tac

theorem cS22_XVII (x1 x2 x3 a b : Fin T.s) (m : Fin T.t) :
    (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (XVII h4 hT hy4 x1 x2 x3) =
      if a = x1 ∧ b = x2 then ((T.b x3 m : ℤ) : ZMod _) else 0 := by
  coord_tac

/-! ## `T13` -/

theorem cT13_XII (x1 x2 i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XII h4 hT hy4 x1 x2) =
      (if i = x1 then ((T.c x2 l : ℤ) : ZMod _) else 0) -
      (if i = x2 then ((T.q x1 x2 * (T.c x1 l + T.α x1 x2 l) : ℤ) : ZMod _)
        else 0) := by
  coord_tac
  split_ifs <;> ring

@[simp] theorem cT13_XIII (x1 : Fin T.s) (x2 : Fin T.t) (i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XIII h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cT13_XIV (x1 : Fin T.s) (x2 : Fin T.t) (i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XIV h4 hT hy4 x1 x2) =
      if i = x1 then ((T.dd x2 l : ℤ) : ZMod _) else 0 := by
  coord_tac

theorem cT13_XV (x1 x2 x3 i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XV h4 hT hy4 x1 x2 x3) =
      (if i = x2 then ((T.α x1 x3 l : ℤ) : ZMod _) else 0) +
      (if i = x3 then ((T.α x1 x2 l : ℤ) : ZMod _) else 0) := by
  coord_tac

theorem cT13_XVI (x1 x2 x3 i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XVI h4 hT hy4 x1 x2 x3) =
      if i = x1 then ((T.α x2 x3 l : ℤ) : ZMod _) else 0 := by
  coord_tac

@[simp] theorem cT13_XVII (x1 x2 x3 i : Fin T.s) (l : Fin T.u) :
    (TF).cT13 (ℓ1 i) (ℓ3 l) (XVII h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

/-! ## `S2'` -/

@[simp] theorem cS2'_XII (x1 x2 : Fin T.s) (k m : Fin T.t) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XII h4 hT hy4 x1 x2) = 0 := by
  coord_tac

theorem cS2'_XIII (x1 : Fin T.s) (x2 : Fin T.t) {k m : Fin T.t} (hkm : k ≤ m) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XIII h4 hT hy4 x1 x2) =
      (if x2 = k then ((T.b x1 m : ℤ) : ZMod _) else 0) +
      (if x2 = m ∧ k < m then ((T.b x1 k : ℤ) : ZMod _) else 0) := by
  simp only [XIII, map_add, _root_.map_sub, map_sum, map_zsmul, map_ite', Frame.cS2'_S2p,
    Frame.cS2'_A4, Frame.cS2'_E12, Frame.cS2'_S22, map_zero, ite_self, smul_zero,
    Finset.sum_const_zero, add_zero, sub_zero, Prod.mk.injEq, ℓ2_inj]
  by_cases h1 : x2 = k
  · subst h1
    rw [Finset.sum_eq_single m]
    · by_cases h : x2 = m
      · subst h; simp [zsmul_eq_mul]
      · simp [zsmul_eq_mul, h, lt_of_le_of_ne hkm h]
        intro h'; exact absurd hkm (not_le.mpr h')
    · intro m' _ hm'
      split_ifs <;> simp_all
    · simp
  · rw [if_neg h1]
    by_cases h2 : x2 = m
    · subst h2
      have : k < x2 := lt_of_le_of_ne hkm (Ne.symm h1)
      rw [Finset.sum_eq_single k]
      · simp [this, not_le.mpr this, zsmul_eq_mul]
      · intro m' _ hm'
        split_ifs <;> simp_all
      · simp
    · rw [if_neg (fun h => h2 h.1), add_zero]
      refine Finset.sum_eq_zero fun m' _ => ?_
      split_ifs <;> simp_all

@[simp] theorem cS2'_XIV (x1 : Fin T.s) (x2 : Fin T.t) (k m : Fin T.t) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XIV h4 hT hy4 x1 x2) = 0 := by
  coord_tac

@[simp] theorem cS2'_XV (x1 x2 x3 : Fin T.s) (k m : Fin T.t) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XV h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

@[simp] theorem cS2'_XVI (x1 x2 x3 : Fin T.s) (k m : Fin T.t) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XVI h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

@[simp] theorem cS2'_XVII (x1 x2 x3 : Fin T.s) (k m : Fin T.t) :
    (TF).cS2' (ℓ2 k) (ℓ2 m) (XVII h4 hT hy4 x1 x2 x3) = 0 := by
  coord_tac

end TFrame

end TaharaProof

end GroupDimension
