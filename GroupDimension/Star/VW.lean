module

public import GroupDimension.Star.Defs

@[expose] public section

/-!
# `(⋆)`, Lemmas 2 and 3: the `v`-part and the `w`-part, exact (MATH-448)

Wiki page 891, §3, Lemmas 2 and 3, with no condition on the exponent of `γ₄`.
* `v_exact`: `d(r)[x_{2k}, x_r] = [x_{2k}, Y_r] - binom(d(r),2) [x_{2k}, x_r, x_r]` (K3), and
  `∑_r ∑_k v_{rk} [x_{2k}, Y_r] + 2 V = 0` by (F₂) (`V = A(genB)`): the coefficient of
  `[x_{2l}, x_{2k}]`, `k < l`, is divisible by `e(k)`, and `[x_{2l}, x_{2k}]^{e(k)} = [x_{2l}, x_{2k}^{e(k)}] = 1`.
* `w_exact`: `2 W - ∑_r ⟨E^w_r, x_r⟩ = T₃ + T₄` by (D₂) with its true modulus and the Jacobi
  identity (K5) `[a, x, y] - [a, y, x] = [a, [x, y]]` for `a ∈ γ₂`.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- **Lemma 2, exact.** -/
theorem v_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) + (2 : ℤ) • A (T.genB τ) =
      T5 T τ A := by
  sorry

/-- **Lemma 3, exact.** -/
theorem w_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    (2 : ℤ) • A (T.genC τ) - ∑ r, ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r)) =
      T3 T τ A + T4 T τ A := by
  sorry

end Star

end GroupDimension
