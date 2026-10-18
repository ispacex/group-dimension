import GroupDimension.TaharaProof.Words
import GroupDimension.CentralRoot

/-!
# The basic products form a `ℤ`-basis of `ℤ[G]` ([Tah81, Lemma 3.1], after Losey)

For a frame of a finite group, the proper products `P b` with `b` basic (`0 ≤ b_j < o_j`) form a
`ℤ`-basis of `ℤ[G]`. They span by Lemma 2.1 (`of_nprod_sub_one`), and there are `|G|` of them;
a spanning family of a free `ℤ`-module of rank `|G|` with `|G|` members is a basis (a surjective
endomorphism of a finitely generated module over a Noetherian ring is injective).
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable (F : Frame G ι)

/-- Basic sequences: `0 ≤ b_j < o_j`. -/
abbrev Basic := (j : ι) → Fin (F.o j)

variable {F}

/-- A basic sequence as an `m`-sequence. -/
def Basic.val (b : F.Basic) : ι → ℕ := fun j => b j

theorem Basic.val_lt (b : F.Basic) (j : ι) : b.val j < F.o j := (b j).isLt

/-- The basic sequence of a sequence below `o`. -/
def toBasic (b : ι → ℕ) (hb : ∀ j, b j < F.o j) : F.Basic := fun j => ⟨b j, hb j⟩

@[simp] theorem toBasic_val (b : ι → ℕ) (hb : ∀ j, b j < F.o j) : (F.toBasic b hb).val = b := rfl

variable (F)

/-- The normal form as a bijection `Basic ≃ G`. -/
noncomputable def nfEquiv : F.Basic ≃ G :=
  Equiv.ofBijective (fun b => F.nprod b.val)
    ⟨fun b c h => by
      have := F.nf_unique b.val c.val b.val_lt c.val_lt h
      funext j; exact Fin.ext (congrFun this j),
    fun g => by
      obtain ⟨b, hb, rfl⟩ := F.nf g
      exact ⟨F.toBasic b hb, rfl⟩⟩

theorem P_span : Submodule.span ℤ (Set.range fun b : F.Basic => F.P b.val) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro z -
  induction z using CentralRoot.induction_of with
  | h0 => exact zero_mem _
  | hof g =>
    obtain ⟨b, hb, rfl⟩ := F.nf g
    have h1 := (F.of_nprod_sub_one b).1
    have : of ℤ G (F.nprod b) = (of ℤ G (F.nprod b) - 1) + F.P 0 := by rw [P_zero]; abel
    change of ℤ G (F.nprod b) ∈ _
    rw [this]
    refine add_mem (Submodule.span_le.mpr ?_ h1) (Submodule.subset_span ⟨F.toBasic 0 ?_, rfl⟩)
    · rintro _ ⟨β, hβ, -, rfl⟩
      exact Submodule.subset_span ⟨F.toBasic β fun j => lt_of_le_of_lt (hβ j) (hb j), rfl⟩
    · intro j; exact lt_of_le_of_lt (zero_le _) (hb j)
  | hneg y hy => exact neg_mem hy
  | hadd y z hy hz => exact add_mem hy hz

variable [Fintype G]

theorem P_linearIndependent : LinearIndependent ℤ fun b : F.Basic => F.P b.val := by
  classical
  -- `f : ℤ^Basic → ℤ[G]`, surjective
  set f : (F.Basic → ℤ) →ₗ[ℤ] MonoidAlgebra ℤ G :=
    Fintype.linearCombination ℤ fun b : F.Basic => F.P b.val with hf
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, hf, Fintype.range_linearCombination, F.P_span]
  -- `e : ℤ[G] ≃ ℤ^Basic`
  let e : MonoidAlgebra ℤ G ≃ₗ[ℤ] (F.Basic → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ G).trans (LinearEquiv.funCongrLeft ℤ ℤ (F.nfEquiv))
  have hinj : Function.Injective (e.toLinearMap.comp f) :=
    IsNoetherian.injective_of_surjective_endomorphism _ (e.surjective.comp hsurj)
  have hfi : Function.Injective f := fun u v huv => hinj (by simp [huv])
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have : f g = f 0 := by rw [hf, Fintype.linearCombination_apply, hg, map_zero]
  exact congrFun (hfi this) i

/-- The basis of `ℤ[G]` by basic products. -/
noncomputable def basis : Module.Basis F.Basic ℤ (MonoidAlgebra ℤ G) :=
  Module.Basis.mk F.P_linearIndependent (by rw [F.P_span])

@[simp] theorem basis_apply (b : F.Basic) : F.basis b = F.P b.val := by
  simp [basis]

end Frame

end TaharaProof

end GroupDimension
