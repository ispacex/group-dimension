module

public import GroupDimension.LowerCentral

@[expose] public section

/-!
# `D₂(G) = γ₂(G)`

The classical statement `G ∩ (1 + Δ²) = [G, G]` (equivalently, `Δ/Δ² ≅ G_ab` via
`g - 1 ↦ g [G,G]`).

Proof. Let `A = G_ab`, written additively, and let `T = ℤ ⊕ A` be the trivial square-zero
extension (`TrivSqZeroExt ℤ A`: `(m, a)(n, b) = (mn, mb + na)`). The map `g ↦ (1, ḡ)` is a
monoid homomorphism `G → T`, so it extends to a ring map `Φ : ℤ[G] → T` whose first coordinate
is the augmentation. Hence `Φ(Δ) ⊆ 0 ⊕ A`, and `(0 ⊕ A)² = 0`, so `Φ(Δ²) = 0`. If `g ∈ D₂(G)`
then `0 = Φ(g - 1) = (0, ḡ)`, i.e. `g ∈ [G, G]`. The reverse inclusion is `γ₂ ⊆ D₂`.
-/

namespace GroupDimension

open MonoidAlgebra

variable {G : Type*} [Group G]

variable (G) in
/-- `G_ab`, written additively. -/
abbrev Gab := Additive (Abelianization G)

/-! `TrivSqZeroExt R M` is a ring once `M` is an `R`–`Rᵐᵒᵖ`-bimodule; for the commutative
ring `ℤ` the right action is the left one. -/

variable (G) in
/-- The right `ℤ`-action on `G_ab` (equal to the left one). -/
@[reducible] noncomputable def gabModuleOp : Module ℤᵐᵒᵖ (Gab G) :=
  Module.compHom _ (RingEquiv.toOpposite ℤ).symm.toRingHom

attribute [local instance] gabModuleOp

instance : IsCentralScalar ℤ (Gab G) := ⟨fun _ _ => rfl⟩

instance : SMulCommClass ℤ ℤᵐᵒᵖ (Gab G) :=
  ⟨fun a b m => by
    change a • ((MulOpposite.unop b) • m) = (MulOpposite.unop b) • (a • m)
    rw [smul_comm]⟩

/-- `g ↦ (1, ḡ) ∈ ℤ ⊕ G_ab`, a monoid homomorphism into the square-zero extension. -/
noncomputable def toSqZero : G →* TrivSqZeroExt ℤ (Gab G) where
  toFun g := (1, Additive.ofMul (Abelianization.of g))
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    · simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · show (1 : ℤ) = 1 * 1
      rfl
    · show Additive.ofMul (Abelianization.of (a * b)) =
        (1 : ℤ) • Additive.ofMul (Abelianization.of b) +
          MulOpposite.op (1 : ℤ) • Additive.ofMul (Abelianization.of a)
      simp [add_comm]

/-- The ring map `Φ : ℤ[G] → ℤ ⊕ G_ab`. -/
noncomputable def sqZeroRep : MonoidAlgebra ℤ G →+* TrivSqZeroExt ℤ (Gab G) :=
  (MonoidAlgebra.lift ℤ (TrivSqZeroExt ℤ (Gab G)) G toSqZero).toRingHom

theorem fst_sqZeroRep (x : MonoidAlgebra ℤ G) :
    (sqZeroRep x).fst = augmentation G x := by
  have : (TrivSqZeroExt.fstHom ℤ ℤ (Gab G)).toRingHom.comp sqZeroRep = augmentation G := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [sqZeroRep, augmentation]
    · intro g
      simp [sqZeroRep, augmentation, toSqZero]
      all_goals rfl
  exact congrArg (fun φ => φ x) this

theorem sqZeroRep_of (g : G) :
    sqZeroRep (of ℤ G g) = toSqZero g := by
  simp only [sqZeroRep, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_of]

theorem augIdeal_sq_le_ker : augIdeal G ^ 2 ≤ RingHom.ker (sqZeroRep : MonoidAlgebra ℤ G →+* _) := by
  rw [Submodule.pow_succ, Submodule.pow_one, Ideal.mul_le]
  intro r hr s hs
  rw [mem_augIdeal, ← fst_sqZeroRep] at hr hs
  rw [RingHom.mem_ker, map_mul]
  apply TrivSqZeroExt.ext
  · simp [hr, hs]
  · simp [TrivSqZeroExt.snd_mul, hr, hs]

/-- `D₂(G) ⊆ [G, G]`. -/
theorem D_two_le_commutator : D 2 G ≤ commutator G := by
  intro g hg
  have h0 : sqZeroRep (of ℤ G g - 1) = 0 := augIdeal_sq_le_ker hg
  rw [_root_.map_sub, _root_.map_one, sqZeroRep_of, sub_eq_zero] at h0
  have h1 := congrArg TrivSqZeroExt.snd h0
  simp only [toSqZero, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_one] at h1
  have h2 : Abelianization.of g = 1 := by
    have h1' : Additive.ofMul (Abelianization.of g) = 0 := h1
    simpa using h1'
  rw [← Abelianization.ker_of]
  exact h2

variable (G) in
/-- **`D₂(G) = γ₂(G)`**: `G ∩ (1 + Δ(G)²) = [G, G]`. In Mathlib's indexing
`γ₂(G) = (⊤ : Subgroup G).lowerCentralSeries 1 = commutator G`. -/
theorem D_two : D 2 G = (⊤ : Subgroup G).lowerCentralSeries 1 := by
  apply le_antisymm
  · rw [Subgroup.top_lowerCentralSeries_one]
    exact D_two_le_commutator
  · exact lowerCentralSeries_le_D G 1

end GroupDimension
