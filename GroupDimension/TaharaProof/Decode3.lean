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

variable [Finite G] (h4 : lowerCentralSeries G 4 = ⊥) {T : Data G} (hT : T.Valid)
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

end TFrame

end TaharaProof

end GroupDimension
