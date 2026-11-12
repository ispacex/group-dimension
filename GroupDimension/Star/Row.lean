module

public import GroupDimension.Star.Defs

@[expose] public section

/-!
# `(⋆)`, Lemma 1: the exact row identity (MATH-448)

Wiki page 891, §3, Lemma 1, in the form of `ExpThree.SetupB.rowB` (`G4Cube.lean`) but exact:
condition (E) is used with its true modulus `gcd(d(r), f(l))`, which kills `[x_{3l}, x_r]`
(its order divides `f(l)`, since `x_{3l}^{f(l)} ∈ γ₄`, and `d(r)`, since `[x_{3l}, x_r^{d(r)}] = 1`),
so no condition on the exponent of `γ₄` is needed.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- **Lemma 1 (row `r`), exact.** For every map `A` additive on `γ₃`:
`∑_k v_{rk} d(r) A[x_{2k}, x_r] + ∑_h crow_{rh} A[Y_h, x_r]
  = ∑_{h<r} u_{hr} q_{hr} A[Y_h, x_r, x_r] + ∑_l Ew_{rl} A[x_{3l}, x_r]`. -/
theorem row_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) (r : Fin T.s) :
    ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) +
      ∑ h, crow T τ r h • A (tc (T.x₁ h ^ T.d h) (T.x₁ r)) =
    (∑ h, if h < r then
      (τ.u h r * T.q h r) • A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ r)) (T.x₁ r)) else 0) +
      ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r)) := by
  sorry

end Star

end GroupDimension
