import GroupDimension.TaharaProof.Decode3

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

variable [Finite G] [Fintype G] (h4 : lowerCentralSeries G 4 = ⊥) {T : Data G} (hT : T.Valid)
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

theorem yy1_mem (i : Fin T.s) : (TF).yy (ℓ1 i) ∈ lowerCentralSeries G 1 :=
  (IsLayerBasis.layerNF hT.basis₁).pow_mem i

theorem yy2_mem (k : Fin T.t) : (TF).yy (ℓ2 k) ∈ lowerCentralSeries G 2 :=
  (IsLayerBasis.layerNF hT.basis₂).pow_mem k

theorem cc_mem2 (g h : Fin T.s) : (TF).cc (ℓ1 g) (ℓ1 h) ∈ lowerCentralSeries G 2 :=
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

end TFrame

end TaharaProof

end GroupDimension
