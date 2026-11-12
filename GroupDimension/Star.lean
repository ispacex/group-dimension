module

public import GroupDimension.Star.Row
public import GroupDimension.Star.VW

@[expose] public section

/-!
# The exact identity `(⋆)` (Theorem 6.11 of the paper, wiki page 891 §3; MATH-448)

`two_smul_gen_eq`: in a group of class `≤ 4`, for Tahara's data and any family `τ` satisfying
(A)–(F) (only (B), (D₂), (E), (F₂) are used), `2 A(g(τ)) = T₁ + T₂ + T₃ + T₄ + T₅` for every map
`A` additive on `γ₃`. Assembly as in `ExpThree.SetupB.two_smul_gen`: the rows of
`Star.row_exact` summed give `2 A(genA) = T₁ + T₂ + V - ∑ ⟨E^w⟩`, then `Star.v_exact` and
`Star.w_exact`.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- **`(⋆)`**: `2 A(g(τ)) = T₁ + T₂ + T₃ + T₄ + T₅`. -/
theorem two_smul_gen_eq {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (hv : T.Valid) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    (2 : ℤ) • A (T.gen τ) = T1 T τ A + T2 T τ A + T3 T τ A + T4 T τ A + T5 T τ A := by
  sorry

end Star

end GroupDimension
