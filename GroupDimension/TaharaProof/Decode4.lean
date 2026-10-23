module

public import GroupDimension.TaharaProof.Decode3

@[expose] public section

/-!
# The relations (I)–(VII) in Tahara's frame, explicitly

Each generator of `R₅*` written through the basis vectors of `W₃* ⊕ W₄` and Tahara's structure
constants `b, c, d, α` ([Tah81, Theorem 5.1]).
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

section TFrame

variable [Finite G] [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4) (ho4 : ∀ q, 1 < o4 q)

local notation "TF" => Tframe h4 hT hy4
local notation "TC" => Tframe_class4 h4 hT hy4 ho4

/-! ## Symbols of short words -/

theorem Φ3_111 {a b c : Fin T.s} (hab : a ≤ b) (hbc : b ≤ c) :
    (TF).Φ3 (cnt [ℓ1 a, ℓ1 b, ℓ1 c]) = (TF).E3 (ℓ1 a) (ℓ1 b) (ℓ1 c) := by
  rw [(TF).Φ3_cnt (by simp [ℓ1_le_ℓ1.mpr hab, ℓ1_le_ℓ1.mpr hbc, ℓ1_le_ℓ1.mpr (hab.trans hbc)])]
  exact Frame.Φ3w_111 (by simp) (by simp) (by simp)

theorem Φ3_1111 {a b c d : Fin T.s} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (TF).Φ3 (cnt [ℓ1 a, ℓ1 b, ℓ1 c, ℓ1 d]) = (TF).S4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) := by
  rw [(TF).Φ3_cnt (by simp [ℓ1_le_ℓ1.mpr hab, ℓ1_le_ℓ1.mpr hbc, ℓ1_le_ℓ1.mpr hcd,
    ℓ1_le_ℓ1.mpr (hab.trans hbc), ℓ1_le_ℓ1.mpr (hbc.trans hcd),
    ℓ1_le_ℓ1.mpr (hab.trans (hbc.trans hcd))])]
  exact Frame.Φ3w_1111 (by simp) (by simp) (by simp) (by simp)

theorem Φ3_12 (a : Fin T.s) (k : Fin T.t) :
    (TF).Φ3 (cnt [ℓ1 a, ℓ2 k]) = (TF).E12 (ℓ1 a) (ℓ2 k) := by
  rw [(TF).Φ3_cnt (by simp [(ℓ1_lt_ℓ2 a k).le])]
  exact Frame.Φ3w_12 (by simp) (by simp)

theorem Φ3_112 {a b : Fin T.s} (hab : a ≤ b) (k : Fin T.t) :
    (TF).Φ3 (cnt [ℓ1 a, ℓ1 b, ℓ2 k]) = (TF).S22 (ℓ1 a) (ℓ1 b) (ℓ2 k) := by
  rw [(TF).Φ3_cnt (by simp [ℓ1_le_ℓ1.mpr hab, (ℓ1_lt_ℓ2 a k).le, (ℓ1_lt_ℓ2 b k).le])]
  exact Frame.Φ3w_112 (by simp) (by simp) (by simp)

theorem Φ3_3 (l : Fin T.u) : (TF).Φ3 (cnt [ℓ3 l]) = (TF).E3' (ℓ3 l) := by
  rw [(TF).Φ3_cnt (List.pairwise_singleton _ _)]
  exact Frame.Φ3w_single3 (by simp)

/-! ## Membership facts -/

theorem yy1_mem (i : Fin T.s) : (TF).yy (ℓ1 i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
  (IsLayerBasis.layerNF hT.basis₁).pow_mem i

theorem yy2_mem (k : Fin T.t) : (TF).yy (ℓ2 k) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  (IsLayerBasis.layerNF hT.basis₂).pow_mem k

theorem cc_mem2 (g h : Fin T.s) : (TF).cc (ℓ1 g) (ℓ1 h) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  ExpThree.tc_mem (i := 1) (j := 0) (by norm_num) (yy1_mem h4 hT hy4 g) (hT.basis₁.mem h)

/-! ## The generators -/

theorem nsum_yy1_ℓ1 (i j : Fin T.s) :
    (TF).nsum ((TF).yy (ℓ1 i)) (cnt [ℓ1 j]) =
      ∑ k, T.b i k • (TF).E12 (ℓ1 j) (ℓ2 k) + ∑ l, T.c i l • (TF).T13 (ℓ1 j) (ℓ3 l) := by
  rw [nsum_ℓ1 h4 hT hy4 (yy1_mem h4 hT hy4 i)]
  simp only [(nfc_yy1 h4 hT hy4 i).1, (nfc_yy1 h4 hT hy4 i).2]

theorem nsum_cc_ℓ1 {g h : Fin T.s} (hgh : g ≤ h) (j : Fin T.s) :
    (TF).nsum ((TF).cc (ℓ1 g) (ℓ1 h)) (cnt [ℓ1 j]) =
      ∑ l, T.α g h l • (TF).T13 (ℓ1 j) (ℓ3 l) := by
  rw [nsum_ℓ1_of_mem2 h4 hT hy4 (cc_mem2 h4 hT hy4 g h)]
  simp only [nfc_cc h4 hT hy4 hgh]

/-- Tahara's value (3). -/
theorem V3val_T {i j : Fin T.s} (hij : i ≤ j) :
    (TF).V3val (ℓ1 i) (ℓ1 j) =
      ∑ k, T.b i k • (TF).E12 (ℓ1 j) (ℓ2 k) + ∑ l, T.c i l • (TF).T13 (ℓ1 j) (ℓ3 l) +
        (TF).S ((TF).cc (ℓ1 i) (ℓ1 j)) + ∑ l, T.α i j l • (TF).T13 (ℓ1 j) (ℓ3 l) -
        ((T.d i).choose 2 : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 i) (ℓ1 j) -
        ((T.d i).choose 3 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 i) (ℓ1 i) (ℓ1 j) := by
  rw [Frame.V3val, nsum_yy1_ℓ1, nsum_cc_ℓ1 h4 hT hy4 hij, Φ3_111 h4 hT hy4 le_rfl hij,
    Φ3_1111 h4 hT hy4 le_rfl le_rfl hij]
  rfl

include ho4 in
/-- (I). -/
theorem gI_T (l : Fin T.u) :
    (TF).gI (ℓ3 l) = (T.f l : ℤ) • (TF).E3' (ℓ3 l) - (TF).A4 (T.x₃ l ^ T.f l) := by
  rw [Frame.gI_eq TC (by simp : (TF).w (ℓ3 l) = 3), Frame.Φ3_single, if_pos (by simp)]
  rfl

/-- (II), `i < j`. -/
theorem gII_T {i j : Fin T.s} (hij : i < j) :
    (TF).gII (ℓ1 i) (ℓ1 j) =
      ∑ k, T.b j k • (TF).E12 (ℓ1 i) (ℓ2 k) + ∑ l, T.c j l • (TF).T13 (ℓ1 i) (ℓ3 l) -
        T.q i j • (TF).V3val (ℓ1 i) (ℓ1 j) -
        ((T.d j).choose 2 : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 j) -
        ((T.d j).choose 3 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 j) (ℓ1 j) := by
  rw [Frame.gII, nsum_yy1_ℓ1, Φ3_111 h4 hT hy4 hij.le le_rfl,
    Φ3_1111 h4 hT hy4 hij.le le_rfl le_rfl]
  rfl

theorem nsum_yy1_ℓ2 (i : Fin T.s) (k : Fin T.t) :
    (TF).nsum ((TF).yy (ℓ1 i)) (cnt [ℓ2 k]) =
      ∑ m, T.b i m • (if k ≤ m then (TF).S2' (ℓ2 k) (ℓ2 m) else (TF).S2' (ℓ2 m) (ℓ2 k)) := by
  rw [nsum_ℓ2 h4 hT hy4 (yy1_mem h4 hT hy4 i)]
  simp only [(nfc_yy1 h4 hT hy4 i).1]

include ho4 in
theorem commsum_T (i : Fin T.s) (k : Fin T.t) :
    ∑ m, ((TF).nfc ((TF).yy (ℓ1 i)) m : ℤ) •
        (if ℓ2 k < m then (TF).nsum (tc ((TF).x m) ((TF).x (ℓ2 k))) 0 else 0) =
      ∑ m, T.b i m • (if k < m then (TF).A4 (tc (T.x₂ m) (T.x₂ k)) else 0) := by
  rw [TIdx_sum]
  have e1 : ∀ i', ((TF).nfc ((TF).yy (ℓ1 i)) (ℓ1 i') : ℤ) = 0 := fun i' => by
    rw [nfc_ℓ1_zero h4 hT hy4 (yy1_mem h4 hT hy4 i)]; rfl
  have hc4 : ∀ (z : G), z ∈ (⊤ : Subgroup G).lowerCentralSeries 4 → (TF).nsum z 0 = 0 := fun z hz => by
    rw [h4, Subgroup.mem_bot] at hz; rw [hz]; exact Frame.nsum_one 0
  have e3 : ∀ l, (TF).nsum (tc ((TF).x (ℓ3 l)) ((TF).x (ℓ2 k))) 0 = 0 := fun l =>
    hc4 _ (ExpThree.tc_mem (i := 2) (j := 1) (by norm_num) (hT.basis₃.mem l) (hT.basis₂.mem k))
  have e4 : ∀ q, (TF).nsum (tc ((TF).x (ℓ4 q)) ((TF).x (ℓ2 k))) 0 = 0 := fun q =>
    hc4 _ (lcs_mem_of_le (by norm_num)
      (ExpThree.tc_mem (i := 3) (j := 1) (n := 5) (by norm_num) (hy4.mem q) (hT.basis₂.mem k)))
  have e2 : ∀ m, (TF).nsum (tc ((TF).x (ℓ2 m)) ((TF).x (ℓ2 k))) 0 =
      (TF).A4 (tc (T.x₂ m) (T.x₂ k)) := fun m =>
    Frame.nsum_zero_of_mem4 TC (ExpThree.tc_mem (i := 1) (j := 1) (by norm_num)
      (hT.basis₂.mem m) (hT.basis₂.mem k))
  simp only [e1, e2, e3, e4, zero_smul, Finset.sum_const_zero, zero_add, ite_self, smul_zero,
    add_zero, ℓ2_lt_ℓ2, (nfc_yy1 h4 hT hy4 i).1]

include ho4 in
/-- (III). -/
theorem gIII_T (i : Fin T.s) (k : Fin T.t) :
    (TF).gIII (ℓ1 i) (ℓ2 k) =
      ∑ m, T.b i m • (if k ≤ m then (TF).S2' (ℓ2 k) (ℓ2 m) else (TF).S2' (ℓ2 m) (ℓ2 k)) +
        ∑ m, T.b i m • (if k < m then (TF).A4 (tc (T.x₂ m) (T.x₂ k)) else 0) -
        (T.d i : ℤ) • (TF).E12 (ℓ1 i) (ℓ2 k) -
        ((T.d i).choose 2 : ℤ) • (TF).S22 (ℓ1 i) (ℓ1 i) (ℓ2 k) := by
  rw [Frame.gIII, nsum_yy1_ℓ2, commsum_T h4 hT hy4 ho4, Φ3_12, Φ3_112 h4 hT hy4 le_rfl]
  rfl

/-- (IV). -/
theorem gIV_T (i : Fin T.s) (k : Fin T.t) :
    (TF).gIV (ℓ1 i) (ℓ2 k) =
      ∑ l, T.dd k l • (TF).T13 (ℓ1 i) (ℓ3 l) - (T.e k : ℤ) • (TF).E12 (ℓ1 i) (ℓ2 k) := by
  rw [Frame.gIV, nsum_ℓ1_of_mem2 h4 hT hy4 (yy2_mem h4 hT hy4 k), Φ3_12]
  simp only [nfc_yy2 h4 hT hy4]
  rfl

include ho4 in
/-- (V), `i ≤ j ≤ k`. -/
theorem gV_T {i j k : Fin T.s} (hij : i ≤ j) (hjk : j ≤ k) :
    (TF).gV (ℓ1 i) (ℓ1 j) (ℓ1 k) =
      ∑ m, T.b i m • (TF).S22 (ℓ1 j) (ℓ1 k) (ℓ2 m) +
        ∑ l, T.α i k l • (TF).T13 (ℓ1 j) (ℓ3 l) + ∑ l, T.α i j l • (TF).T13 (ℓ1 k) (ℓ3 l) +
        (TF).A4 (tc ((TF).cc (ℓ1 i) (ℓ1 j)) (T.x₁ k)) -
        (T.d i : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
        ((T.d i).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 i) (ℓ1 j) (ℓ1 k) := by
  rw [Frame.gV, nsum_ℓ11 h4 hT hy4 (yy1_mem h4 hT hy4 i) hjk, nsum_cc_ℓ1 h4 hT hy4 (hij.trans hjk),
    nsum_cc_ℓ1 h4 hT hy4 hij, Frame.nsum_zero_of_mem4 TC
      (z := tc ((TF).cc (ℓ1 i) (ℓ1 j)) ((TF).x (ℓ1 k))) (ExpThree.tc_mem (i := 2) (j := 0)
      (by norm_num) (cc_mem2 h4 hT hy4 i j) (hT.basis₁.mem k)),
    Φ3_111 h4 hT hy4 hij hjk, Φ3_1111 h4 hT hy4 le_rfl hij hjk]
  simp only [(nfc_yy1 h4 hT hy4 i).1]
  rfl

/-- (VI), `i ≤ j ≤ k`. -/
theorem gVI_T {i j k : Fin T.s} (hij : i ≤ j) (hjk : j ≤ k) :
    (TF).gVI (ℓ1 i) (ℓ1 j) (ℓ1 k) =
      ∑ m, T.b j m • (TF).S22 (ℓ1 i) (ℓ1 k) (ℓ2 m) + ∑ l, T.α j k l • (TF).T13 (ℓ1 i) (ℓ3 l) -
        (T.d j : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
        ((T.d j).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 j) (ℓ1 k) := by
  rw [Frame.gVI, nsum_ℓ11 h4 hT hy4 (yy1_mem h4 hT hy4 j) (hij.trans hjk),
    nsum_cc_ℓ1 h4 hT hy4 hjk, Φ3_111 h4 hT hy4 hij hjk, Φ3_1111 h4 hT hy4 hij le_rfl hjk]
  simp only [(nfc_yy1 h4 hT hy4 j).1]
  rfl

/-- (VII), `i ≤ j < k`. -/
theorem gVII_T {i j k : Fin T.s} (hij : i ≤ j) (hjk : j < k) :
    (TF).gVII (ℓ1 i) (ℓ1 j) (ℓ1 k) =
      ∑ m, T.b k m • (TF).S22 (ℓ1 i) (ℓ1 j) (ℓ2 m) -
        (T.d k : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
        ((T.d k).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 k) (ℓ1 k) := by
  rw [Frame.gVII, nsum_ℓ11 h4 hT hy4 (yy1_mem h4 hT hy4 k) hij,
    Φ3_111 h4 hT hy4 hij hjk.le, Φ3_1111 h4 hT hy4 hij hjk.le le_rfl]
  simp only [(nfc_yy1 h4 hT hy4 k).1]
  rfl

end TFrame

end TaharaProof

end GroupDimension
