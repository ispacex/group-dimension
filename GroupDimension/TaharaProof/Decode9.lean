module

public import GroupDimension.TaharaProof.Decode8

@[expose] public section

/-!
# Coordinates of the combination of the relations

The coordinates of `combx` at Tahara's basis vectors, family by family.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

theorem sum_fst_eq {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (g : α × β → M) (a0 : α) (h : ∀ x : α × β, x.1 ≠ a0 → g x = 0) :
    ∑ x, g x = ∑ b, g (a0, b) := by
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single a0]
  intro a ha
  exact Finset.sum_eq_zero fun b _ => h (a, b) ha

theorem sum_snd_eq {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (g : α × β → M) (b0 : β) (h : ∀ x : α × β, x.2 ≠ b0 → g x = 0) :
    ∑ x, g x = ∑ a, g (a, b0) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single b0]
  intro b hb
  exact h (a, b) hb

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

local notation "TF" => Tframe h4 hT hy4

attribute [-simp] Tframe_o1 Tframe_o2 Tframe_o3 Tframe_o4

variable (p : Fin T.u → ℤ) (U : Fin T.s × Fin T.s → ℤ) (V V' : Fin T.s × Fin T.t → ℤ)
  (W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ)

/-- The seven families of `combx`. -/
noncomputable def sI : (TF).M3 :=
  ∑ l, p l • ((T.f l : ℤ) • (TF).E3' (ℓ3 l) - (TF).A4 (T.x₃ l ^ T.f l))
noncomputable def sII : (TF).M3 :=
  ∑ x, U x • (if x.1 < x.2 then XII h4 hT hy4 x.1 x.2 else 0)
noncomputable def sIII : (TF).M3 := ∑ x, V x • XIII h4 hT hy4 x.1 x.2
noncomputable def sIV : (TF).M3 := ∑ x, V' x • XIV h4 hT hy4 x.1 x.2
noncomputable def sV : (TF).M3 :=
  ∑ x, W5 x • (if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then XV h4 hT hy4 x.1 x.2.1 x.2.2 else 0)
noncomputable def sVI : (TF).M3 :=
  ∑ x, W6 x • (if x.1 < x.2.1 ∧ x.2.1 ≤ x.2.2 then XVI h4 hT hy4 x.1 x.2.1 x.2.2 else 0)
noncomputable def sVII : (TF).M3 :=
  ∑ x, W7 x • (if x.1 ≤ x.2.1 ∧ x.2.1 < x.2.2 then XVII h4 hT hy4 x.1 x.2.1 x.2.2 else 0)

theorem combx_eq : combx h4 hT hy4 p U V V' W5 W6 W7 =
    sI h4 hT hy4 p + sII h4 hT hy4 U + sIII h4 hT hy4 V + sIV h4 hT hy4 V' +
      sV h4 hT hy4 W5 + sVI h4 hT hy4 W6 + sVII h4 hT hy4 W7 := rfl

/-! ## `E3` -/

section E3

variable (a b c : Fin T.s)

@[simp] theorem cE3_sI : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sI h4 hT hy4 p) = 0 := by simp [sI]
@[simp] theorem cE3_sIII : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sIII h4 hT hy4 V) = 0 := by simp [sIII]
@[simp] theorem cE3_sIV : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sIV h4 hT hy4 V') = 0 := by simp [sIV]

theorem cE3_sV : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sV h4 hT hy4 W5) =
    if a ≤ b ∧ b ≤ c then -(W5 (a, b, c) * T.d a) else 0 := by
  rw [sV, map_sum, Fintype.sum_eq_single (a, b, c)]
  · split_ifs <;> simp [cE3_XV, *]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cE3_XV] <;> intros <;> simp_all

theorem cE3_sVI : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sVI h4 hT hy4 W6) =
    if a < b ∧ b ≤ c then -(W6 (a, b, c) * T.d b) else 0 := by
  rw [sVI, map_sum, Fintype.sum_eq_single (a, b, c)]
  · split_ifs <;> simp [cE3_XVI, *]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cE3_XVI] <;> intros <;> simp_all

theorem cE3_sVII : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sVII h4 hT hy4 W7) =
    if a ≤ b ∧ b < c then -(W7 (a, b, c) * T.d c) else 0 := by
  rw [sVII, map_sum, Fintype.sum_eq_single (a, b, c)]
  · split_ifs <;> simp [cE3_XVII, *]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cE3_XVII] <;> intros <;> simp_all

theorem cE3_sII_iij (hac : a < c) : (TF).cE3 (ℓ1 a, ℓ1 a, ℓ1 c) (sII h4 hT hy4 U) =
    U (a, c) * (T.q a c * ((T.d a).choose 2 : ℤ)) := by
  rw [sII, map_sum, Fintype.sum_eq_single (a, c)]
  · simp [cE3_XII, hac, hac.ne]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cE3_XII] <;> split_ifs <;> simp_all

theorem cE3_sII_ijj (hab : a < b) : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 b) (sII h4 hT hy4 U) =
    -(U (a, b) * ((T.d b).choose 2 : ℤ)) := by
  rw [sII, map_sum, Fintype.sum_eq_single (a, b)]
  · simp [cE3_XII, hab, hab.ne']
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cE3_XII] <;> split_ifs <;> simp_all

theorem cE3_sII_iii : (TF).cE3 (ℓ1 a, ℓ1 a, ℓ1 a) (sII h4 hT hy4 U) = 0 := by
  rw [sII, map_sum]
  refine Finset.sum_eq_zero ?_
  rintro ⟨x1, x2⟩ -
  split_ifs with h <;> simp [cE3_XII] <;> split_ifs <;> aesop

theorem cE3_sII_ijk (hab : a < b) (hbc : b < c) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sII h4 hT hy4 U) = 0 := by
  rw [sII, map_sum]
  refine Finset.sum_eq_zero ?_
  rintro ⟨x1, x2⟩ -
  split_ifs with h <;> simp [cE3_XII] <;> split_ifs <;> aesop

end E3

/-! ## `E12` -/

section E12

variable (i : Fin T.s) (k : Fin T.t)

@[simp] theorem cE12_sI : (TF).cE12 (ℓ1 i, ℓ2 k) (sI h4 hT hy4 p) = 0 := by simp [sI]
@[simp] theorem cE12_sV : (TF).cE12 (ℓ1 i, ℓ2 k) (sV h4 hT hy4 W5) = 0 := by
  simp [sV, map_ite0]
@[simp] theorem cE12_sVI : (TF).cE12 (ℓ1 i, ℓ2 k) (sVI h4 hT hy4 W6) = 0 := by
  simp [sVI, map_ite0]
@[simp] theorem cE12_sVII : (TF).cE12 (ℓ1 i, ℓ2 k) (sVII h4 hT hy4 W7) = 0 := by
  simp [sVII, map_ite0]

theorem cE12_sII : (TF).cE12 (ℓ1 i, ℓ2 k) (sII h4 hT hy4 U) =
    (∑ h, if i < h then U (i, h) * T.b h k else 0) -
      ∑ h, if h < i then U (h, i) * (T.q h i * T.b h k) else 0 := by
  rw [sII, map_sum]
  have e : ∀ x : Fin T.s × Fin T.s,
      (TF).cE12 (ℓ1 i, ℓ2 k) (U x • if x.1 < x.2 then XII h4 hT hy4 x.1 x.2 else 0) =
        (if i = x.1 ∧ x.1 < x.2 then U x * T.b x.2 k else 0) -
          (if i = x.2 ∧ x.1 < x.2 then U x * (T.q x.1 x.2 * T.b x.1 k) else 0) := by
    rintro ⟨x1, x2⟩
    simp only [map_zsmul, map_ite0, cE12_XII, smul_eq_mul, map_zero]
    split_ifs <;> (try simp_all) <;> (try ring)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_fst_eq _ i (by rintro ⟨x1, x2⟩ (h : x1 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]
  · rw [sum_snd_eq _ i (by rintro ⟨x1, x2⟩ (h : x2 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]

theorem cE12_sIII : (TF).cE12 (ℓ1 i, ℓ2 k) (sIII h4 hT hy4 V) = -(V (i, k) * T.d i) := by
  rw [sIII, map_sum, Fintype.sum_eq_single (i, k)]
  · simp [cE12_XIII]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    simp [cE12_XIII]; intros; simp_all

theorem cE12_sIV : (TF).cE12 (ℓ1 i, ℓ2 k) (sIV h4 hT hy4 V') = -(V' (i, k) * T.e k) := by
  rw [sIV, map_sum, Fintype.sum_eq_single (i, k)]
  · simp [cE12_XIV]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    simp [cE12_XIV]; intros; simp_all

end E12

/-! ## `S4` -/

section S4

variable (a b c d : Fin T.s)

@[simp] theorem cS4_sI : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sI h4 hT hy4 p) = 0 := by
  simp [sI]
@[simp] theorem cS4_sIII : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sIII h4 hT hy4 V) = 0 := by
  simp [sIII]
@[simp] theorem cS4_sIV : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sIV h4 hT hy4 V') = 0 := by
  simp [sIV]

theorem cS4_sV : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sV h4 hT hy4 W5) =
    if a = b ∧ a ≤ c ∧ c ≤ d then -((W5 (a, c, d) * ((T.d a).choose 2 : ℤ) : ℤ) : ZMod _)
      else 0 := by
  rw [sV, map_sum, Fintype.sum_eq_single (a, c, d)]
  · rcases eq_or_ne a b with rfl | hab
    · by_cases h1 : a ≤ c ∧ c ≤ d
      · simp [h1, cS4_XV, zsmul_eq_mul]
      · simp [h1]
    · split_ifs <;> simp_all [cS4_XV, Ne.symm hab]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS4_XV] <;> intros <;> simp_all

theorem cS4_sVI : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sVI h4 hT hy4 W6) =
    if a < b ∧ b = c ∧ c ≤ d then -((W6 (a, b, d) * ((T.d b).choose 2 : ℤ) : ℤ) : ZMod _)
      else 0 := by
  rw [sVI, map_sum, Fintype.sum_eq_single (a, b, d)]
  · rcases eq_or_ne b c with rfl | hbc
    · by_cases h1 : a < b ∧ b ≤ d
      · simp [h1, cS4_XVI, zsmul_eq_mul]
      · simp [h1]
    · split_ifs <;> simp_all [cS4_XVI, Ne.symm hbc]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS4_XVI] <;> intros <;> simp_all

theorem cS4_sVII : (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sVII h4 hT hy4 W7) =
    if a ≤ b ∧ b < c ∧ c = d then -((W7 (a, b, c) * ((T.d c).choose 2 : ℤ) : ℤ) : ZMod _)
      else 0 := by
  rw [sVII, map_sum, Fintype.sum_eq_single (a, b, c)]
  · rcases eq_or_ne c d with rfl | hcd
    · by_cases h1 : a ≤ b ∧ b < c
      · simp [h1, cS4_XVII, zsmul_eq_mul]
      · simp [h1]
    · split_ifs <;> simp_all [cS4_XVII, Ne.symm hcd]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS4_XVII] <;> intros <;> simp_all

theorem cS4_sII_iiij (hab : a < b) :
    (TF).cS4 (ℓ1 a) (ℓ1 a) (ℓ1 a) (ℓ1 b) (sII h4 hT hy4 U) =
      ((U (a, b) * (T.q a b * ((T.d a).choose 3 : ℤ)) : ℤ) : ZMod _) := by
  rw [sII, map_sum, Fintype.sum_eq_single (a, b)]
  · simp [cS4_XII, hab, hab.ne, zsmul_eq_mul]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS4_XII] <;> split_ifs <;> simp_all

theorem cS4_sII_ijjj (hab : a < b) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 b) (ℓ1 b) (sII h4 hT hy4 U) =
      -((U (a, b) * ((T.d b).choose 3 : ℤ) : ℤ) : ZMod _) := by
  rw [sII, map_sum, Fintype.sum_eq_single (a, b)]
  · simp [cS4_XII, hab, hab.ne', zsmul_eq_mul]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS4_XII] <;> split_ifs <;> simp_all

theorem cS4_sII_zero (h1 : ¬(a = b ∧ b = c ∧ c < d)) (h2 : ¬(a < b ∧ b = c ∧ c = d)) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sII h4 hT hy4 U) = 0 := by
  rw [sII, map_sum]
  refine Finset.sum_eq_zero ?_
  rintro ⟨x1, x2⟩ -
  split_ifs with h <;> simp [cS4_XII] <;> split_ifs <;> aesop

end S4

/-! ## `S22` -/

section S22

variable (a b : Fin T.s) (m : Fin T.t)

@[simp] theorem cS22_sI : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sI h4 hT hy4 p) = 0 := by simp [sI]
@[simp] theorem cS22_sII : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sII h4 hT hy4 U) = 0 := by
  simp [sII, map_ite0]
@[simp] theorem cS22_sIV : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sIV h4 hT hy4 V') = 0 := by
  simp [sIV]

theorem cS22_sIII : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sIII h4 hT hy4 V) =
    if a = b then -((V (a, m) * ((T.d a).choose 2 : ℤ) : ℤ) : ZMod _) else 0 := by
  rw [sIII, map_sum, Fintype.sum_eq_single (a, m)]
  · rcases eq_or_ne a b with rfl | hab
    · simp [cS22_XIII, zsmul_eq_mul]
    · simp [cS22_XIII, hab, Ne.symm hab]
  · rintro ⟨x1, x2⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    simp [cS22_XIII]; intros; simp_all

theorem cS22_sV : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sV h4 hT hy4 W5) =
    ∑ h, if h ≤ a ∧ a ≤ b then ((W5 (h, a, b) * T.b h m : ℤ) : ZMod _) else 0 := by
  rw [sV, map_sum, sum_snd_eq _ (a, b)]
  · refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp_all [cS22_XV, zsmul_eq_mul]
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq, Prod.mk.injEq] at hx
    split_ifs <;> simp [cS22_XV] <;> intros <;> simp_all

theorem cS22_sVI : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sVI h4 hT hy4 W6) =
    ∑ h, if a < h ∧ h ≤ b then ((W6 (a, h, b) * T.b h m : ℤ) : ZMod _) else 0 := by
  rw [sVI, map_sum, sum_fst_eq _ a, sum_snd_eq _ b]
  · refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp_all [cS22_XVI, zsmul_eq_mul]
  · rintro ⟨x2, x3⟩ hx
    simp only [ne_eq] at hx
    split_ifs <;> simp [cS22_XVI] <;> intros <;> simp_all
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq] at hx
    split_ifs <;> simp [cS22_XVI] <;> intros <;> simp_all

theorem cS22_sVII : (TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m) (sVII h4 hT hy4 W7) =
    ∑ h, if a ≤ b ∧ b < h then ((W7 (a, b, h) * T.b h m : ℤ) : ZMod _) else 0 := by
  rw [sVII, map_sum, sum_fst_eq _ a, sum_fst_eq _ b]
  · refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp_all [cS22_XVII, zsmul_eq_mul]
  · rintro ⟨x2, x3⟩ hx
    simp only [ne_eq] at hx
    split_ifs <;> simp [cS22_XVII] <;> intros <;> simp_all
  · rintro ⟨x1, x2, x3⟩ hx
    simp only [ne_eq] at hx
    split_ifs <;> simp [cS22_XVII] <;> intros <;> simp_all

end S22

/-! ## `T13` -/

section T13

variable (i : Fin T.s) (l : Fin T.u)

@[simp] theorem cT13_sI : (TF).cT13 (ℓ1 i) (ℓ3 l) (sI h4 hT hy4 p) = 0 := by simp [sI]
@[simp] theorem cT13_sIII : (TF).cT13 (ℓ1 i) (ℓ3 l) (sIII h4 hT hy4 V) = 0 := by simp [sIII]
@[simp] theorem cT13_sVII : (TF).cT13 (ℓ1 i) (ℓ3 l) (sVII h4 hT hy4 W7) = 0 := by
  simp [sVII, map_ite0]

theorem cT13_sII : (TF).cT13 (ℓ1 i) (ℓ3 l) (sII h4 hT hy4 U) =
    (∑ h, if i < h then ((U (i, h) * T.c h l : ℤ) : ZMod _) else 0) -
      ∑ h, if h < i then ((U (h, i) * (T.q h i * (T.c h l + T.α h i l)) : ℤ) : ZMod _)
        else 0 := by
  rw [sII, map_sum]
  have e : ∀ x : Fin T.s × Fin T.s,
      (TF).cT13 (ℓ1 i) (ℓ3 l) (U x • if x.1 < x.2 then XII h4 hT hy4 x.1 x.2 else 0) =
        (if i = x.1 ∧ x.1 < x.2 then ((U x * T.c x.2 l : ℤ) : ZMod _) else 0) -
          (if i = x.2 ∧ x.1 < x.2 then
            ((U x * (T.q x.1 x.2 * (T.c x.1 l + T.α x.1 x.2 l)) : ℤ) : ZMod _) else 0) := by
    rintro ⟨x1, x2⟩
    simp only [map_zsmul, map_ite0, cT13_XII, zsmul_eq_mul, map_zero]
    split_ifs <;> (try simp_all) <;> (try push_cast) <;> (try ring)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_fst_eq _ i (by rintro ⟨x1, x2⟩ (h : x1 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]
  · rw [sum_snd_eq _ i (by rintro ⟨x1, x2⟩ (h : x2 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]

theorem cT13_sIV : (TF).cT13 (ℓ1 i) (ℓ3 l) (sIV h4 hT hy4 V') =
    ∑ k, ((V' (i, k) * T.dd k l : ℤ) : ZMod _) := by
  rw [sIV, map_sum, sum_fst_eq _ i]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [cT13_XIV, zsmul_eq_mul]
  · rintro ⟨x1, x2⟩ (hx : x1 ≠ i)
    simp [cT13_XIV, Ne.symm hx]

theorem cT13_sV : (TF).cT13 (ℓ1 i) (ℓ3 l) (sV h4 hT hy4 W5) =
    (∑ g, ∑ h, if g ≤ i ∧ i ≤ h then ((W5 (g, i, h) * T.α g h l : ℤ) : ZMod _) else 0) +
      ∑ g, ∑ h, if g ≤ h ∧ h ≤ i then ((W5 (g, h, i) * T.α g h l : ℤ) : ZMod _) else 0 := by
  rw [sV, map_sum]
  have e : ∀ x : Fin T.s × Fin T.s × Fin T.s,
      (TF).cT13 (ℓ1 i) (ℓ3 l) (W5 x • if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then
        XV h4 hT hy4 x.1 x.2.1 x.2.2 else 0) =
        (if i = x.2.1 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then
          ((W5 x * T.α x.1 x.2.2 l : ℤ) : ZMod _) else 0) +
        (if i = x.2.2 ∧ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then
          ((W5 x * T.α x.1 x.2.1 l : ℤ) : ZMod _) else 0) := by
    rintro ⟨x1, x2, x3⟩
    simp only [map_zsmul, map_ite0, cT13_XV, zsmul_eq_mul, map_zero]
    split_ifs <;> (try simp_all) <;> (try push_cast) <;> (try ring)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [sum_fst_eq _ i (by rintro ⟨x2, x3⟩ (h : x2 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [sum_snd_eq _ i (by rintro ⟨x2, x3⟩ (h : x3 ≠ i); exact if_neg fun hh => h hh.1.symm)]
    simp only [true_and]

theorem cT13_sVI : (TF).cT13 (ℓ1 i) (ℓ3 l) (sVI h4 hT hy4 W6) =
    ∑ g, ∑ h, if i < g ∧ g ≤ h then ((W6 (i, g, h) * T.α g h l : ℤ) : ZMod _) else 0 := by
  rw [sVI, map_sum, sum_fst_eq _ i, Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp_all [cT13_XVI, zsmul_eq_mul]
  · rintro ⟨x1, x2, x3⟩ (hx : x1 ≠ i)
    split_ifs <;> simp [cT13_XVI, Ne.symm hx]

end T13

/-! ## `S2'` -/

section S2'

variable (k m : Fin T.t)

@[simp] theorem cS2'_sI : (TF).cS2' (ℓ2 k) (ℓ2 m) (sI h4 hT hy4 p) = 0 := by simp [sI]
@[simp] theorem cS2'_sII : (TF).cS2' (ℓ2 k) (ℓ2 m) (sII h4 hT hy4 U) = 0 := by
  simp [sII, map_ite0]
@[simp] theorem cS2'_sIV : (TF).cS2' (ℓ2 k) (ℓ2 m) (sIV h4 hT hy4 V') = 0 := by simp [sIV]
@[simp] theorem cS2'_sV : (TF).cS2' (ℓ2 k) (ℓ2 m) (sV h4 hT hy4 W5) = 0 := by
  simp [sV, map_ite0]
@[simp] theorem cS2'_sVI : (TF).cS2' (ℓ2 k) (ℓ2 m) (sVI h4 hT hy4 W6) = 0 := by
  simp [sVI, map_ite0]
@[simp] theorem cS2'_sVII : (TF).cS2' (ℓ2 k) (ℓ2 m) (sVII h4 hT hy4 W7) = 0 := by
  simp [sVII, map_ite0]

theorem cS2'_sIII_kk : (TF).cS2' (ℓ2 k) (ℓ2 k) (sIII h4 hT hy4 V) =
    ∑ i, ((V (i, k) * T.b i k : ℤ) : ZMod _) := by
  rw [sIII, map_sum, sum_snd_eq _ k]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [cS2'_XIII h4 hT hy4 _ _ (le_refl k), zsmul_eq_mul]
  · rintro ⟨x1, x2⟩ (hx : x2 ≠ k)
    simp [cS2'_XIII h4 hT hy4 _ _ (le_refl k), hx]

theorem cS2'_sIII_km (hkm : k < m) : (TF).cS2' (ℓ2 k) (ℓ2 m) (sIII h4 hT hy4 V) =
    (∑ i, ((V (i, k) * T.b i m : ℤ) : ZMod _)) + ∑ i, ((V (i, m) * T.b i k : ℤ) : ZMod _) := by
  rw [sIII, map_sum]
  have e : ∀ x : Fin T.s × Fin T.t, (TF).cS2' (ℓ2 k) (ℓ2 m) (V x • XIII h4 hT hy4 x.1 x.2) =
      (if x.2 = k then ((V x * T.b x.1 m : ℤ) : ZMod _) else 0) +
        (if x.2 = m then ((V x * T.b x.1 k : ℤ) : ZMod _) else 0) := by
    rintro ⟨x1, x2⟩
    simp only [map_zsmul, cS2'_XIII h4 hT hy4 _ _ hkm.le, zsmul_eq_mul]
    split_ifs <;> (try simp_all) <;> (try push_cast) <;> (try ring)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib]
  congr 1
  · rw [sum_snd_eq _ k (by rintro ⟨x1, x2⟩ (h : x2 ≠ k); exact if_neg h)]
    simp only [if_true]
  · rw [sum_snd_eq _ m (by rintro ⟨x1, x2⟩ (h : x2 ≠ m); exact if_neg h)]
    simp only [if_true]

end S2'

end TFrame

end TaharaProof

end GroupDimension
