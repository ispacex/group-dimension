module

public import GroupDimension.TaharaProof.Level3Cases

@[expose] public section

/-!
# The frame of Tahara's data

For a finite group of class `≤ 4` and Tahara's data `T` (uniqueness bases of the first three
layers with their structure constants), we complete `T` by a uniqueness basis of `γ₄` (any finite
abelian group is a direct sum of cyclic groups) and glue the four layers into a frame
`T.frame` with letters `Fin s ⊕ₗ Fin t ⊕ₗ Fin u ⊕ₗ Fin v`. It satisfies `Class4`, and the
normal-form coordinates of `x_{1i}^{d(i)}`, `x_{2k}^{e(k)}`, `[x_{1g}^{d(g)}, x_{1h}]` are Tahara's
structure constants `b, c, d, α`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

/-! ## A uniqueness basis of `γ₄` -/

theorem exists_layer4 [Finite G] :
    ∃ (v : ℕ) (y : Fin v → G) (o : Fin v → ℕ), LayerNF 3 y o ∧ ∀ q, 1 < o q := by
  classical
  haveI : Finite (Additive (Layer G 3)) := by
    unfold Layer; infer_instance
  obtain ⟨κ, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (Additive (Layer G 3))
  let E : Additive (Layer G 3) ≃+ ((i : κ) → ZMod (n i)) :=
    e.trans (DirectSum.linearEquivFunOnFintype ℤ κ fun i => ZMod (n i)).toAddEquiv
  obtain ⟨σ, -⟩ : ∃ σ : Fin (Fintype.card κ) ≃ κ, True := ⟨(Fintype.equivFin κ).symm, trivial⟩
  have hy : ∀ q : Fin (Fintype.card κ), ∃ g ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      cl G 3 g = E.symm (Pi.single (σ q) 1) := fun q => cl_surj 3 _
  choose y hy1 hy2 using hy
  have hcl : ∀ a : Fin (Fintype.card κ) → ℤ,
      E (cl G 3 (oprod y a)) = fun i => ((a (σ.symm i) : ℤ) : ZMod (n i)) := by
    intro a
    rw [cl_oprod hy1, map_sum]
    funext i
    obtain ⟨q0, rfl⟩ := σ.surjective i
    simp only [map_zsmul, hy2, AddEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply,
      Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single q0]
    · simp
    · intro q _ hq
      have : σ q ≠ σ q0 := fun h => hq (σ.injective h)
      simp [Pi.single_eq_of_ne' this]
    · simp
  refine ⟨Fintype.card κ, y, fun q => n (σ q), ⟨hy1, fun q => lt_trans zero_lt_one (hn _), ?_, ?_⟩,
    fun q => hn _⟩
  · intro a
    rw [← cl_eq_zero_iff (ExpThree.oprod_mem hy1 a), ← E.map_eq_zero_iff, hcl]
    constructor
    · intro h q
      have := congrFun h (σ q)
      simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    · intro h
      funext i
      simp only [Pi.zero_apply]
      have := h (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr this
  · intro g hg
    refine ⟨fun q => ((E (cl G 3 g) (σ q)).val : ℤ), ?_⟩
    have hm := ExpThree.oprod_mem hy1 (fun q => ((E (cl G 3 g) (σ q)).val : ℤ))
    rw [← cl_eq_zero_iff (mul_mem (inv_mem hm) hg), cl_mul (inv_mem hm) hg, cl_inv hm,
      neg_add_eq_zero]
    apply E.injective
    rw [hcl]
    funext i
    obtain ⟨q, rfl⟩ := σ.surjective i
    rw [Equiv.symm_apply_apply]
    haveI : NeZero (n (σ q)) := ⟨(lt_trans zero_lt_one (hn _)).ne'⟩
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-! ## The frame -/

/-- The letters of Tahara's frame: the four layers in order. -/
abbrev TIdx (s t u v : ℕ) := Fin s ⊕ₗ (Fin t ⊕ₗ (Fin u ⊕ₗ (Fin v ⊕ₗ Fin 0)))

/-- Decidable equality on `TIdx` taken from its linear order, so that `Pi.single` written here
agrees with the `Pi.single` in the generic statements over `[LinearOrder ι]` (Mathlib also has a
direct `DecidableEq` instance on `Lex` sums, which is not syntactically the same). -/
instance (priority := high) TIdx.decidableEq (s t u v : ℕ) : DecidableEq (TIdx s t u v) :=
  LinearOrder.toDecidableEq

section TFrame

variable {s t u v : ℕ}

/-- A letter of the first layer. -/
def ℓ1 (i : Fin s) : TIdx s t u v := toLex (Sum.inl i)
/-- A letter of the second layer. -/
def ℓ2 (k : Fin t) : TIdx s t u v := toLex (Sum.inr (toLex (Sum.inl k)))
/-- A letter of the third layer. -/
def ℓ3 (l : Fin u) : TIdx s t u v := toLex (Sum.inr (toLex (Sum.inr (toLex (Sum.inl l)))))
/-- A letter of the fourth layer. -/
def ℓ4 (q : Fin v) : TIdx s t u v :=
  toLex (Sum.inr (toLex (Sum.inr (toLex (Sum.inr (toLex (Sum.inl q)))))))

theorem TIdx_cases (p : TIdx s t u v) :
    (∃ i, p = ℓ1 i) ∨ (∃ k, p = ℓ2 k) ∨ (∃ l, p = ℓ3 l) ∨ ∃ q, p = ℓ4 q := by
  rcases p with (i | (k | (l | (q | z))))
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨l, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))
  · exact z.elim0

theorem ℓ1_le_ℓ1 {i j : Fin s} : (ℓ1 i : TIdx s t u v) ≤ ℓ1 j ↔ i ≤ j := Sum.Lex.inl_le_inl_iff
theorem ℓ1_lt_ℓ1 {i j : Fin s} : (ℓ1 i : TIdx s t u v) < ℓ1 j ↔ i < j := Sum.Lex.inl_lt_inl_iff
theorem ℓ2_le_ℓ2 {i j : Fin t} : (ℓ2 i : TIdx s t u v) ≤ ℓ2 j ↔ i ≤ j := by
  simp [ℓ2, Sum.Lex.inr_le_inr_iff, Sum.Lex.inl_le_inl_iff]
theorem ℓ2_lt_ℓ2 {i j : Fin t} : (ℓ2 i : TIdx s t u v) < ℓ2 j ↔ i < j := by
  simp [ℓ2, Sum.Lex.inr_lt_inr_iff, Sum.Lex.inl_lt_inl_iff]

variable [Finite G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

/-- Tahara's frame, glued from the layers `γ₁/γ₂, …, γ₄`. -/
noncomputable def Tframe : Frame G (TIdx T.s T.t T.u v) :=
  (TailFrame.glue (k := 0) (IsLayerBasis.layerNF hT.basis₁) <| TailFrame.glue (k := 1) (IsLayerBasis.layerNF hT.basis₂) <|
    TailFrame.glue (k := 2) (IsLayerBasis.layerNF hT.basis₃) <| TailFrame.glue (k := 3) hy4 <|
      TailFrame.empty 4 h4).toFrame

@[simp] theorem Tframe_x1 (i : Fin T.s) : (Tframe h4 hT hy4).x (ℓ1 i) = T.x₁ i := rfl
@[simp] theorem Tframe_x2 (k : Fin T.t) : (Tframe h4 hT hy4).x (ℓ2 k) = T.x₂ k := rfl
@[simp] theorem Tframe_x3 (l : Fin T.u) : (Tframe h4 hT hy4).x (ℓ3 l) = T.x₃ l := rfl
@[simp] theorem Tframe_x4 (q : Fin v) : (Tframe h4 hT hy4).x (ℓ4 q) = y4 q := rfl
@[simp] theorem Tframe_w1 (i : Fin T.s) : (Tframe h4 hT hy4).w (ℓ1 i) = 1 := rfl
@[simp] theorem Tframe_w2 (k : Fin T.t) : (Tframe h4 hT hy4).w (ℓ2 k) = 2 := rfl
@[simp] theorem Tframe_w3 (l : Fin T.u) : (Tframe h4 hT hy4).w (ℓ3 l) = 3 := rfl
@[simp] theorem Tframe_w4 (q : Fin v) : (Tframe h4 hT hy4).w (ℓ4 q) = 4 := rfl
@[simp] theorem Tframe_o1 (i : Fin T.s) : (Tframe h4 hT hy4).o (ℓ1 i) = T.d i := rfl
@[simp] theorem Tframe_o2 (k : Fin T.t) : (Tframe h4 hT hy4).o (ℓ2 k) = T.e k := rfl
@[simp] theorem Tframe_o3 (l : Fin T.u) : (Tframe h4 hT hy4).o (ℓ3 l) = T.f l := rfl
@[simp] theorem Tframe_o4 (q : Fin v) : (Tframe h4 hT hy4).o (ℓ4 q) = o4 q := rfl

theorem Tframe_class4 (h1 : ∀ q, 1 < o4 q) : (Tframe h4 hT hy4).Class4 where
  top := h4
  w_le p := by
    rcases TIdx_cases p with ⟨i, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩ | ⟨q, rfl⟩ <;> simp
  one_lt p := by
    rcases TIdx_cases p with ⟨i, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩ | ⟨q, rfl⟩
    · exact hT.basis₁.one_lt i
    · exact hT.basis₂.one_lt k
    · exact hT.basis₃.one_lt l
    · exact h1 q
  dvd p p' hw h2 hle := by
    rcases TIdx_cases p with ⟨i, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩ | ⟨q, rfl⟩ <;>
      rcases TIdx_cases p' with ⟨i', rfl⟩ | ⟨k', rfl⟩ | ⟨l', rfl⟩ | ⟨q', rfl⟩ <;>
      simp at hw h2
    · exact hT.basis₁.dvd i i' (ℓ1_le_ℓ1.mp hle)
    · exact hT.basis₂.dvd k k' (ℓ2_le_ℓ2.mp hle)

end TFrame

end TaharaProof

end GroupDimension
