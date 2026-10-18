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

end TFrame

end TaharaProof

end GroupDimension
