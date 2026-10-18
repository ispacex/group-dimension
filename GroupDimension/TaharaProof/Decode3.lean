import GroupDimension.TaharaProof.Decode2

/-!
# Decoding for Tahara's frame: structure constants and the shape of the relations

In Tahara's frame (`Tframe`), the normal-form coordinates of `x_{1i}^{d(i)}`, `x_{2k}^{e(k)}` and
`[x_{1g}^{d(g)}, x_{1h}]` in the layers 2, 3 are Tahara's structure constants `b, c, d, α`
(`nfc_yy1`, `nfc_yy2`, `nfc_cc`), by the uniqueness of normal forms layer by layer.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

theorem sum_lex {α β : Type*} [LinearOrder α] [Fintype α] [LinearOrder β] [Fintype β]
    {M : Type*} [AddCommMonoid M] (f : α ⊕ₗ β → M) :
    ∑ m, f m = ∑ a, f (toLex (Sum.inl a)) + ∑ b, f (toLex (Sum.inr b)) := by
  rw [← Equiv.sum_comp toLex f, Fintype.sum_sum_type]

section TIdx

variable {s t u v : ℕ}

theorem TIdx_sum {M : Type*} [AddCommMonoid M] (f : TIdx s t u v → M) :
    ∑ m, f m = ∑ i, f (ℓ1 i) + (∑ k, f (ℓ2 k) + (∑ l, f (ℓ3 l) + ∑ q, f (ℓ4 q))) := by
  rw [sum_lex, sum_lex, sum_lex, sum_lex]
  simp [ℓ1, ℓ2, ℓ3, ℓ4]

theorem ℓ1_lt_ℓ2 (i : Fin s) (k : Fin t) : (ℓ1 i : TIdx s t u v) < ℓ2 k := Sum.Lex.inl_lt_inr _ _
theorem ℓ1_lt_ℓ3 (i : Fin s) (l : Fin u) : (ℓ1 i : TIdx s t u v) < ℓ3 l := Sum.Lex.inl_lt_inr _ _
theorem ℓ1_lt_ℓ4 (i : Fin s) (q : Fin v) : (ℓ1 i : TIdx s t u v) < ℓ4 q := Sum.Lex.inl_lt_inr _ _
theorem ℓ2_lt_ℓ3 (k : Fin t) (l : Fin u) : (ℓ2 k : TIdx s t u v) < ℓ3 l := by
  simp only [ℓ2, ℓ3, Sum.Lex.inr_lt_inr_iff]; exact Sum.Lex.inl_lt_inr _ _
theorem ℓ2_lt_ℓ4 (k : Fin t) (q : Fin v) : (ℓ2 k : TIdx s t u v) < ℓ4 q := by
  simp only [ℓ2, ℓ4, Sum.Lex.inr_lt_inr_iff]; exact Sum.Lex.inl_lt_inr _ _

theorem ℓ1_inj {i j : Fin s} : (ℓ1 i : TIdx s t u v) = ℓ1 j ↔ i = j := by
  simp [ℓ1]
theorem ℓ2_inj {i j : Fin t} : (ℓ2 i : TIdx s t u v) = ℓ2 j ↔ i = j := by
  simp [ℓ2]
theorem ℓ3_inj {i j : Fin u} : (ℓ3 i : TIdx s t u v) = ℓ3 j ↔ i = j := by
  simp [ℓ3]
theorem ℓ4_inj {i j : Fin v} : (ℓ4 i : TIdx s t u v) = ℓ4 j ↔ i = j := by
  simp [ℓ4]

end TIdx

section TFrame

variable [Finite G] [Fintype G] (h4 : lowerCentralSeries G 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

/-- The normal form in Tahara's frame, layer by layer. -/
theorem Tframe_nprod (n : TIdx T.s T.t T.u v → ℕ) :
    (Tframe h4 hT hy4).nprod n =
      lprod (ordL (Fin T.s)) T.x₁ (fun i => n (ℓ1 i)) *
        (lprod (ordL (Fin T.t)) T.x₂ (fun k => n (ℓ2 k)) *
          (lprod (ordL (Fin T.u)) T.x₃ (fun l => n (ℓ3 l)) *
            lprod (ordL (Fin v)) y4 (fun q => n (ℓ4 q)))) := by
  rw [Frame.nprod, lprod_split, lprod_split, lprod_split, lprod_split]
  have : lprod (ordL (Fin 0)) ((Tframe h4 hT hy4).x ∘ inrₗ ∘ inrₗ ∘ inrₗ ∘ inrₗ)
      (n ∘ inrₗ ∘ inrₗ ∘ inrₗ ∘ inrₗ) = 1 := by simp [lprod, ordL]
  simp only [Function.comp_def] at this ⊢
  rw [this, mul_one]
  rfl

theorem lprod_eq_oprod_toNat {n : ℕ} (y : Fin n → G) {β : Fin n → ℤ} (hβ : ∀ k, 0 ≤ β k) :
    oprod y β = lprod (ordL (Fin n)) y (fun k => (β k).toNat) := by
  rw [lprod_fin_eq_oprod]; congr 1; funext k; simp [Int.toNat_of_nonneg (hβ k)]

/-- **The coordinates in layers 2, 3** of `z ∈ γ₂` with `z ≡ ∏ x_2^β ∏ x_3^γ (mod γ₄)`. -/
theorem nfc_23 {z : G} (hz : z ∈ lowerCentralSeries G 1) {β : Fin T.t → ℤ} {γ : Fin T.u → ℤ}
    (hβ : ∀ k, 0 ≤ β k ∧ β k < T.e k) (hγ : ∀ l, 0 ≤ γ l ∧ γ l < T.f l)
    (h : (oprod T.x₂ β * oprod T.x₃ γ)⁻¹ * z ∈ lowerCentralSeries G 3) :
    (∀ k, ((Tframe h4 hT hy4).nfc z (ℓ2 k) : ℤ) = β k) ∧
      (∀ l, ((Tframe h4 hT hy4).nfc z (ℓ3 l) : ℤ) = γ l) := by
  set F := Tframe h4 hT hy4
  set n := F.nfc z
  have hz' := F.nprod_nfc z
  rw [Tframe_nprod] at hz'
  -- the first layer is empty
  have h1 : (fun i => n (ℓ1 i)) = 0 := funext fun i => by
    by_contra h0
    have := F.nf_weight (k := 2) (by simpa using hz) (F.nfc_lt z) (F.nprod_nfc z) h0
    simp [F, Tframe_w1] at this
  rw [h1, lprod_zero, one_mul] at hz'
  set L2 := lprod (ordL (Fin T.t)) T.x₂ (fun k => n (ℓ2 k))
  set L3 := lprod (ordL (Fin T.u)) T.x₃ (fun l => n (ℓ3 l))
  set L4 := lprod (ordL (Fin v)) y4 (fun q => n (ℓ4 q))
  have hL2 : L2 ∈ lowerCentralSeries G 1 := (IsLayerBasis.layerNF hT.basis₂).lprod_mem _
  have hL3 : L3 ∈ lowerCentralSeries G 2 := (IsLayerBasis.layerNF hT.basis₃).lprod_mem _
  have hL4 : L4 ∈ lowerCentralSeries G 3 := hy4.lprod_mem _
  set A := lprod (ordL (Fin T.t)) T.x₂ (fun k => (β k).toNat)
  set C := lprod (ordL (Fin T.u)) T.x₃ (fun l => (γ l).toNat)
  rw [lprod_eq_oprod_toNat T.x₂ (fun k => (hβ k).1),
    lprod_eq_oprod_toNat T.x₃ (fun l => (hγ l).1)] at h
  change (A * C)⁻¹ * z ∈ _ at h
  have hC : C ∈ lowerCentralSeries G 2 := (IsLayerBasis.layerNF hT.basis₃).lprod_mem _
  -- layer 2
  have e2 : (fun k => n (ℓ2 k)) = fun k => (β k).toNat := by
    refine (IsLayerBasis.layerNF hT.basis₂).nf_unique (fun k => F.nfc_lt z (ℓ2 k))
      (fun k => by have := hβ k; omega) ?_
    have : L2⁻¹ * A = (C * ((A * C)⁻¹ * z) * (L3 * L4)⁻¹)⁻¹ := by
      rw [← hz']; group
    change L2⁻¹ * A ∈ _
    rw [this]
    refine inv_mem (mul_mem (mul_mem (lcs_mem_of_le (by norm_num) hC)
      (lcs_mem_of_le (by norm_num) h)) (inv_mem (mul_mem (lcs_mem_of_le (by norm_num) hL3)
        (lcs_mem_of_le (by norm_num) hL4))))
  have hLA : L2 = A := by simp only [L2, A]; rw [e2]
  -- layer 3
  have e3 : (fun l => n (ℓ3 l)) = fun l => (γ l).toNat := by
    refine (IsLayerBasis.layerNF hT.basis₃).nf_unique (fun l => F.nfc_lt z (ℓ3 l))
      (fun l => by have := hγ l; omega) ?_
    have : L3⁻¹ * C = (C⁻¹ * L3 * L4 * L4⁻¹)⁻¹ := by group
    have h' : C⁻¹ * L3 * L4 ∈ lowerCentralSeries G 3 := by
      have : C⁻¹ * L3 * L4 = (A * C)⁻¹ * z := by rw [← hz', ← hLA]; group
      rw [this]; exact h
    change L3⁻¹ * C ∈ _
    rw [this]
    exact inv_mem (mul_mem h' (inv_mem hL4))
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have := congrFun e2 k; simp only at this; rw [this, Int.toNat_of_nonneg (hβ k).1]
  · have := congrFun e3 l; simp only at this; rw [this, Int.toNat_of_nonneg (hγ l).1]

/-! ## Tahara's structure constants -/

theorem yy_ℓ1 (i : Fin T.s) : (Tframe h4 hT hy4).yy (ℓ1 i) = T.x₁ i ^ T.d i := rfl
theorem yy_ℓ2 (k : Fin T.t) : (Tframe h4 hT hy4).yy (ℓ2 k) = T.x₂ k ^ T.e k := rfl
theorem cc_ℓ1 (g h : Fin T.s) :
    (Tframe h4 hT hy4).cc (ℓ1 g) (ℓ1 h) = tc (T.x₁ g ^ T.d g) (T.x₁ h) := rfl

/-- `b, c`: the normal form of `x_{1i}^{d(i)}`. -/
theorem nfc_yy1 (i : Fin T.s) :
    (∀ k, ((Tframe h4 hT hy4).nfc ((Tframe h4 hT hy4).yy (ℓ1 i)) (ℓ2 k) : ℤ) = T.b i k) ∧
      ∀ l, ((Tframe h4 hT hy4).nfc ((Tframe h4 hT hy4).yy (ℓ1 i)) (ℓ3 l) : ℤ) = T.c i l := by
  rw [yy_ℓ1]
  exact nfc_23 h4 hT hy4 ((IsLayerBasis.layerNF hT.basis₁).pow_mem i) (hT.b_range i)
    (hT.c_range i) (hT.hb i)

/-- `d`: the normal form of `x_{2k}^{e(k)}`. -/
theorem nfc_yy2 (k : Fin T.t) (l : Fin T.u) :
    ((Tframe h4 hT hy4).nfc ((Tframe h4 hT hy4).yy (ℓ2 k)) (ℓ3 l) : ℤ) = T.dd k l := by
  rw [yy_ℓ2]
  refine (nfc_23 h4 hT hy4 (β := 0) (lcs_mem_of_le (by norm_num)
    ((IsLayerBasis.layerNF hT.basis₂).pow_mem k)) (fun k' => ⟨le_rfl, by
      have := hT.basis₂.one_lt k'; simp only [Pi.zero_apply]; omega⟩) (hT.dd_range k) ?_).2 l
  have h0 : oprod T.x₂ (0 : Fin T.t → ℤ) = 1 := by simp [oprod]
  rw [h0, one_mul]; exact hT.hdd k

/-- `α`: the normal form of `[x_{1g}^{d(g)}, x_{1h}]`, `g ≤ h`. -/
theorem nfc_cc {g h : Fin T.s} (hgh : g ≤ h) (l : Fin T.u) :
    ((Tframe h4 hT hy4).nfc ((Tframe h4 hT hy4).cc (ℓ1 g) (ℓ1 h)) (ℓ3 l) : ℤ) = T.α g h l := by
  rw [cc_ℓ1]
  have hm : tc (T.x₁ g ^ T.d g) (T.x₁ h) ∈ lowerCentralSeries G 2 :=
    ExpThree.tc_mem (i := 1) (j := 0) (by norm_num) ((IsLayerBasis.layerNF hT.basis₁).pow_mem g)
      (hT.basis₁.mem h)
  refine (nfc_23 h4 hT hy4 (β := 0) (lcs_mem_of_le (by norm_num) hm) (fun k' => ⟨le_rfl, by
      have := hT.basis₂.one_lt k'; simp only [Pi.zero_apply]; omega⟩) (fun l =>
        hT.α_range g h l hgh) ?_).2 l
  have h0 : oprod T.x₂ (0 : Fin T.t → ℤ) = 1 := by simp [oprod]
  rw [h0, one_mul]; exact hT.hα g h hgh

/-! ## First-order symbols in Tahara's frame -/

theorem nfc_ℓ1_zero {y : G} (hy : y ∈ lowerCentralSeries G 1) (i : Fin T.s) :
    (Tframe h4 hT hy4).nfc y (ℓ1 i) = 0 := by
  by_contra h0
  have := (Tframe h4 hT hy4).nf_weight (k := 2) (by simpa using hy)
    ((Tframe h4 hT hy4).nfc_lt y) ((Tframe h4 hT hy4).nprod_nfc y) h0
  simp at this

theorem nfc_ℓ2_zero {y : G} (hy : y ∈ lowerCentralSeries G 2) (k : Fin T.t) :
    (Tframe h4 hT hy4).nfc y (ℓ2 k) = 0 := by
  by_contra h0
  have := (Tframe h4 hT hy4).nf_weight (k := 3) (by simpa using hy)
    ((Tframe h4 hT hy4).nfc_lt y) ((Tframe h4 hT hy4).nprod_nfc y) h0
  simp at this

/-- `P(x_{1j} - 1)(y - 1)` to first order, for `y ∈ γ₂`. -/
theorem nsum_ℓ1 {y : G} (hy : y ∈ lowerCentralSeries G 1) (j : Fin T.s) :
    (Tframe h4 hT hy4).nsum y (cnt [ℓ1 j]) =
      ∑ k, ((Tframe h4 hT hy4).nfc y (ℓ2 k) : ℤ) • (Tframe h4 hT hy4).E12 (ℓ1 j) (ℓ2 k) +
        ∑ l, ((Tframe h4 hT hy4).nfc y (ℓ3 l) : ℤ) • (Tframe h4 hT hy4).T13 (ℓ1 j) (ℓ3 l) := by
  set F := Tframe h4 hT hy4
  rw [Frame.nsum, TIdx_sum]
  have e1 : ∑ i, (F.nfc y (ℓ1 i) : ℤ) • F.Φ3 (cnt [ℓ1 j] + Pi.single (ℓ1 i) 1) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [nfc_ℓ1_zero h4 hT hy4 hy]; simp
  have e2 : ∀ k, F.Φ3 (cnt [ℓ1 j] + Pi.single (ℓ2 k) 1) = F.E12 (ℓ1 j) (ℓ2 k) := fun k => by
    rw [← cnt_single, ← cnt_append, F.Φ3_cnt (by simp [(ℓ1_lt_ℓ2 j k).le])]
    exact Frame.Φ3w_12 (by simp [F]) (by simp [F])
  have e3 : ∀ l, F.Φ3 (cnt [ℓ1 j] + Pi.single (ℓ3 l) 1) = F.T13 (ℓ1 j) (ℓ3 l) := fun l => by
    rw [← cnt_single, ← cnt_append, F.Φ3_cnt (by simp [(ℓ1_lt_ℓ3 j l).le])]
    exact Frame.Φ3w_13 (by simp [F]) (by simp [F])
  have e4 : ∀ q, F.Φ3 (cnt [ℓ1 j] + Pi.single (ℓ4 q) 1) = 0 := fun q =>
    F.Φ3_eq_zero_of_five_le (by rw [← cnt_single, ← cnt_append, F.W_cnt]; simp [F])
  simp only [e1, e2, e3, e4, smul_zero, Finset.sum_const_zero, add_zero, zero_add]

/-- `P(x_{1j} - 1)(x_{1j'} - 1)(y - 1)` to first order, for `y ∈ γ₂`, `j ≤ j'`. -/
theorem nsum_ℓ11 {y : G} (hy : y ∈ lowerCentralSeries G 1) {j j' : Fin T.s} (hjj : j ≤ j') :
    (Tframe h4 hT hy4).nsum y (cnt [ℓ1 j, ℓ1 j']) =
      ∑ k, ((Tframe h4 hT hy4).nfc y (ℓ2 k) : ℤ) •
        (Tframe h4 hT hy4).S22 (ℓ1 j) (ℓ1 j') (ℓ2 k) := by
  set F := Tframe h4 hT hy4
  rw [Frame.nsum, TIdx_sum]
  have hle : (ℓ1 j : TIdx T.s T.t T.u v) ≤ ℓ1 j' := ℓ1_le_ℓ1.mpr hjj
  have e1 : ∑ i, (F.nfc y (ℓ1 i) : ℤ) • F.Φ3 (cnt [ℓ1 j, ℓ1 j'] + Pi.single (ℓ1 i) 1) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [nfc_ℓ1_zero h4 hT hy4 hy]; simp
  have e2 : ∀ k, F.Φ3 (cnt [ℓ1 j, ℓ1 j'] + Pi.single (ℓ2 k) 1) = F.S22 (ℓ1 j) (ℓ1 j') (ℓ2 k) :=
    fun k => by
    rw [← cnt_single, ← cnt_append, F.Φ3_cnt (by
      simp [hle, (ℓ1_lt_ℓ2 j k).le, (ℓ1_lt_ℓ2 j' k).le])]
    exact Frame.Φ3w_112 (by simp [F]) (by simp [F]) (by simp [F])
  have e3 : ∀ l, F.Φ3 (cnt [ℓ1 j, ℓ1 j'] + Pi.single (ℓ3 l) 1) = 0 := fun l =>
    F.Φ3_eq_zero_of_five_le (by rw [← cnt_single, ← cnt_append, F.W_cnt]; simp [F])
  have e4 : ∀ q, F.Φ3 (cnt [ℓ1 j, ℓ1 j'] + Pi.single (ℓ4 q) 1) = 0 := fun q =>
    F.Φ3_eq_zero_of_five_le (by rw [← cnt_single, ← cnt_append, F.W_cnt]; simp [F])
  simp only [e1, e2, e3, e4, smul_zero, Finset.sum_const_zero, add_zero, zero_add]

/-- `P(x_{1j} - 1)(y - 1)` to first order, for `y ∈ γ₃`. -/
theorem nsum_ℓ1_of_mem2 {y : G} (hy : y ∈ lowerCentralSeries G 2) (j : Fin T.s) :
    (Tframe h4 hT hy4).nsum y (cnt [ℓ1 j]) =
      ∑ l, ((Tframe h4 hT hy4).nfc y (ℓ3 l) : ℤ) • (Tframe h4 hT hy4).T13 (ℓ1 j) (ℓ3 l) := by
  rw [nsum_ℓ1 h4 hT hy4 (lcs_mem_of_le (by norm_num) hy)]
  simp [nfc_ℓ2_zero h4 hT hy4 hy]

/-- `P(x_{2k} - 1)(y - 1)` to first order, for `y ∈ γ₂`. -/
theorem nsum_ℓ2 {y : G} (hy : y ∈ lowerCentralSeries G 1) (k : Fin T.t) :
    (Tframe h4 hT hy4).nsum y (cnt [ℓ2 k]) =
      ∑ m, ((Tframe h4 hT hy4).nfc y (ℓ2 m) : ℤ) •
        (if k ≤ m then (Tframe h4 hT hy4).S2' (ℓ2 k) (ℓ2 m)
          else (Tframe h4 hT hy4).S2' (ℓ2 m) (ℓ2 k)) := by
  set F := Tframe h4 hT hy4
  rw [Frame.nsum, TIdx_sum]
  have e1 : ∑ i, (F.nfc y (ℓ1 i) : ℤ) • F.Φ3 (cnt [ℓ2 k] + Pi.single (ℓ1 i) 1) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [nfc_ℓ1_zero h4 hT hy4 hy]; simp
  have e2 : ∀ m, F.Φ3 (cnt [ℓ2 k] + Pi.single (ℓ2 m) 1) =
      if k ≤ m then F.S2' (ℓ2 k) (ℓ2 m) else F.S2' (ℓ2 m) (ℓ2 k) := fun m => by
    rw [← cnt_single, ← cnt_append]
    split_ifs with h
    · rw [F.Φ3_cnt (by simp [ℓ2_le_ℓ2.mpr h])]
      exact Frame.Φ3w_22 (by simp [F]) (by simp [F])
    · have e : cnt ([ℓ2 k] ++ [ℓ2 m]) = cnt ([ℓ2 m] ++ [ℓ2 k] : List (TIdx T.s T.t T.u v)) := by
        rw [cnt_append, cnt_append, add_comm]
      rw [e, F.Φ3_cnt (by simp [ℓ2_le_ℓ2.mpr (le_of_not_ge h)])]
      exact Frame.Φ3w_22 (by simp [F]) (by simp [F])
  have e3 : ∀ l, F.Φ3 (cnt [ℓ2 k] + Pi.single (ℓ3 l) 1) = 0 := fun l =>
    F.Φ3_eq_zero_of_five_le (by rw [← cnt_single, ← cnt_append, F.W_cnt]; simp [F])
  have e4 : ∀ q, F.Φ3 (cnt [ℓ2 k] + Pi.single (ℓ4 q) 1) = 0 := fun q =>
    F.Φ3_eq_zero_of_five_le (by rw [← cnt_single, ← cnt_append, F.W_cnt]; simp [F])
  simp only [e1, e2, e3, e4, smul_zero, Finset.sum_const_zero, add_zero, zero_add]

end TFrame

end TaharaProof

end GroupDimension
