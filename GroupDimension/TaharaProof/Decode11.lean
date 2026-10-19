import GroupDimension.TaharaProof.Decode10

/-!
# The family `τ` satisfies (A)–(F)
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

section TFrame

variable [Fintype G] (h4 : lowerCentralSeries G 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

local notation "TF" => Tframe h4 hT hy4

attribute [-simp] Tframe_o1 Tframe_o2 Tframe_o3 Tframe_o4

variable {p : Fin T.u → ℤ} {U : Fin T.s × Fin T.s → ℤ} {V V' : Fin T.s × Fin T.t → ℤ}
  {W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ} {g : G}

/-- **Tahara's conditions (A)–(F)** for the coefficients of the symbol of `g ∈ D₅`. -/
theorem admissible_tau (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7) :
    T.Admissible (tau U V V' W5 W6 W7) where
  A₁ i := by
    have h := hE3 h4 hT hy4 hS i i i
    rw [cE3_sII_iii] at h
    simp only [le_refl, and_self, if_true, lt_irrefl, false_and, and_false, if_false,
      add_zero, zero_add] at h
    have hd : (T.d i : ℤ) ≠ 0 := by have := hT.basis₁.one_lt i; omega
    have h' : W5 (i, i, i) * (T.d i : ℤ) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_right hd
  A₂ i j hij := by
    have h := hE3 h4 hT hy4 hS i i j
    rw [cE3_sII_iij h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, hij, and_self, if_true, lt_irrefl, false_and, if_false,
      add_zero, true_and] at h
    show -U (i, j) * T.q i j * T.ch i 2 + W5 (i, i, j) * T.d i + W7 (i, i, j) * T.d j = 0
    simp only [Data.ch]
    first | linear_combination h | linear_combination -h
  A₃ i j hij := by
    have h := hE3 h4 hT hy4 hS i j j
    rw [cE3_sII_ijj h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, hij, and_self, if_true, lt_irrefl, and_false, if_false,
      add_zero, true_and] at h
    show -(-U (i, j)) * T.ch j 2 + W5 (i, j, j) * T.d i + W6 (i, j, j) * T.d j = 0
    simp only [Data.ch]
    first | linear_combination h | linear_combination -h
  A₄ i j k hij hjk := by
    have h := hE3 h4 hT hy4 hS i j k
    rw [cE3_sII_ijk h4 hT hy4 U i j k hij hjk] at h
    simp only [hij.le, hjk.le, hij, hjk, and_self, if_true, zero_add] at h
    show W5 (i, j, k) * T.d i + W6 (i, j, k) * T.d j + W7 (i, j, k) * T.d k = 0
    first | linear_combination h | linear_combination -h
  B i k := by
    have h := hE12 h4 hT hy4 hS i k
    show (∑ h, if i < h then -U (i, h) * T.b h k else 0)
      - (∑ h, if h < i then -U (h, i) * T.q h i * T.b h k else 0)
      + V (i, k) * T.d i + V' (i, k) * T.e k = 0
    simp only [neg_mul, mul_assoc, sum_ite_neg]
    first | linear_combination h | linear_combination -h
  C₁ i j hij := by
    have h := hS4 h4 hT hy4 hS i i i j
    rw [cS4_sII_iiij h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, and_self, if_true, lt_irrefl, false_and, and_false, if_false,
      add_zero, true_and] at h
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
    show (((-U (i, j) * T.q i j * T.ch i 3 + W5 (i, i, j) * T.ch i 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
    simp only [Data.ch]
    push_cast at h ⊢
    first | linear_combination h | linear_combination -h
  C₂ i j hij := by
    have h := hS4 h4 hT hy4 hS i i j j
    rw [cS4_sII_zero h4 hT hy4 U i i j j (by simp [hij.ne]) (by simp)] at h
    simp only [le_refl, hij.le, hij, and_self, if_true, lt_irrefl, false_and, if_false,
      zero_add, true_and] at h
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
    show (((W5 (i, j, j) * T.ch i 2 + W7 (i, i, j) * T.ch j 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
    simp only [Data.ch]
    push_cast at h ⊢
    first | linear_combination h | linear_combination -h
  C₃ i j hij := by
    have h := hS4 h4 hT hy4 hS i j j j
    rw [cS4_sII_ijjj h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, hij, hij.ne, and_self, if_true, lt_irrefl, false_and,
      and_false, if_false, add_zero, true_and] at h
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
    show (((-(-U (i, j)) * T.ch j 3 + W6 (i, j, j) * T.ch j 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
    simp only [Data.ch]
    push_cast at h ⊢
    first | linear_combination h | linear_combination -h
  C₄ i j k hij hjk := by
    refine ⟨?_, ?_, ?_⟩
    · have h := hS4 h4 hT hy4 hS i i j k
      rw [cS4_sII_zero h4 hT hy4 U i i j k (by simp [hij.ne]) (by simp)] at h
      simp only [le_refl, hij.le, hjk.le, hjk.ne, hij, and_self, if_true, lt_irrefl, false_and,
        and_false, if_false, zero_add, add_zero, true_and] at h
      refine Int.modEq_zero_iff_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
      show (((W5 (i, j, k) * T.ch i 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
      simp only [Data.ch]
      push_cast at h ⊢
      first | linear_combination h | linear_combination -h
    · have h := hS4 h4 hT hy4 hS i j j k
      rw [cS4_sII_zero h4 hT hy4 U i j j k (by simp [hij.ne]) (by simp [hjk.ne])] at h
      simp only [le_refl, hij.le, hjk.le, hij.ne, hij, and_self, if_true, lt_irrefl,
        false_and, and_false, if_false, zero_add, add_zero, true_and] at h
      refine Int.modEq_zero_iff_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
      show (((W6 (i, j, k) * T.ch j 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
      simp only [Data.ch]
      push_cast at h ⊢
      first | linear_combination h | linear_combination -h
    · have h := hS4 h4 hT hy4 hS i j k k
      rw [cS4_sII_zero h4 hT hy4 U i j k k (by simp [hij.ne]) (by simp [hjk.ne])] at h
      simp only [le_refl, hij.le, hjk.le, hij.ne, hjk.ne, hij, hjk, and_self, if_true,
        lt_irrefl, false_and, and_false, if_false, zero_add, add_zero, true_and] at h
      refine Int.modEq_zero_iff_dvd.mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ1 i))).mp ?_)
      show (((W7 (i, j, k) * T.ch k 2 : ℤ)) : ZMod ((TF).o (ℓ1 i))) = 0
      simp only [Data.ch]
      push_cast at h ⊢
      first | linear_combination h | linear_combination -h
  D₁ i k := by
    have h := hS22 h4 hT hy4 hS i i k
    simp only [le_refl, and_true, true_and, if_true, lt_and_le_false, if_false,
      Finset.sum_const_zero, add_zero] at h
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ2 k)))).mp ?_)
    show (((V (i, k) * T.ch i 2 - (∑ h, if h ≤ i then W5 (h, i, i) * T.b h k else 0)
      - (∑ h, if i < h then W7 (i, i, h) * T.b h k else 0) : ℤ)) : ZMod (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ2 k)))) = 0
    simp only [Data.ch]
    push_cast at h ⊢
    first | linear_combination h | linear_combination -h
  D₂ i j k hij := by
    have h := hS22 h4 hT hy4 hS i j k
    simp only [hij.ne, hij.le, and_true, true_and, if_false, zero_add] at h
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ2 k)))).mp ?_)
    show (((∑ h, if h ≤ i then W5 (h, i, j) * T.b h k else 0)
      + (∑ h, if i < h ∧ h ≤ j then W6 (i, h, j) * T.b h k else 0)
      + (∑ h, if j < h then W7 (i, j, h) * T.b h k else 0) : ℤ) : ZMod (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ2 k)))) = 0
    push_cast at h ⊢
    first | linear_combination h | linear_combination -h
  E i l := by
    have h := hT13 h4 hT hy4 hS i l
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ3 l)))).mp ?_)
    show (((-(∑ h, if h < i then -U (h, i) * T.q h i * T.α h i l else 0)
      + (∑ h, if i < h then -U (i, h) * T.c h l else 0)
      - (∑ h, if h < i then -U (h, i) * T.q h i * T.c h l else 0)
      - (∑ k, V' (i, k) * T.dd k l)
      - (∑ g, ∑ h, if g ≤ i ∧ i ≤ h then W5 (g, i, h) * T.α g h l else 0)
      - (∑ g, ∑ h, if g ≤ h ∧ h ≤ i then W5 (g, h, i) * T.α g h l else 0)
      - (∑ g, ∑ h, if i < g ∧ g ≤ h then W6 (i, g, h) * T.α g h l else 0) : ℤ)) : ZMod (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ3 l)))) = 0
    push_cast at h ⊢
    simp only [mul_add, ite_add0, Finset.sum_add_distrib, mul_assoc] at h
    simp only [neg_mul, mul_assoc, sum_ite_neg, neg_neg]
    first | linear_combination h | linear_combination -h
  F₁ k := by
    have h := hS2'_kk h4 hT hy4 hS k
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ2 k))).mp ?_)
    show (((∑ i, V (i, k) * T.b i k : ℤ)) : ZMod ((TF).o (ℓ2 k))) = 0
    push_cast at h ⊢
    exact h
  F₂ k m hkm := by
    have h := hS2'_km h4 hT hy4 hS hkm
    refine Int.modEq_zero_iff_dvd.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ((TF).o (ℓ2 k))).mp ?_)
    show (((∑ i, V (i, k) * T.b i m) + (∑ i, V (i, m) * T.b i k) : ℤ) : ZMod ((TF).o (ℓ2 k))) = 0
    push_cast at h ⊢
    exact h

end TFrame

end TaharaProof

end GroupDimension
