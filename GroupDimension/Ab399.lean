module

public import GroupDimension.Star

@[expose] public section

/-!
# `D₅ = 1` for `Q_ab ≅ C₃ × C₉ × C₉` (MATH-448)

The case `Q_ab` of type `[3, 9, 9]` of the case `γ₄ ≅ C₉` left open by Theorem 6.11 (remark 6.13
of the paper). The proof (MATH-446, Kimi's note `case_b.md`, Theorem 2 and Corollary 3 with the
corrections of the review, comment 8041, and the conclusion of comment 8035) evaluates the exact
identity `(⋆)` (`Star.two_smul_gen_eq`) term by term in the basis of `G4Cube.lean` (heights flag and
the kernel of the cube map; `act` = the index set `A`):
* `T₅ = 0`: `d(i) ∣ binom(d(i), 2)` and `[a, x_i, x_i]^{d(i)} = 1` (K4);
* every term with the index `i₀` (`d(i₀) = 3`) vanishes: `c̄_{i₀ j}` has order `3` in `L₂`, and each
  coefficient carries a factor `3` by (c1)–(c3), or the class `Ȳ_h` lies in `3 L₂` (inactive `h`);
* the terms with the pair `(i₁, i₂)` (`d = 9, 9`) vanish because `ω(c̄_{i₁ i₂}, ·)` is `3`-torsion:
  `L₂` is spanned by `c̄_{i₀ i₁}`, `c̄_{i₀ i₂}` (of order `3`) and `c̄_{i₁ i₂}`, and
  `ω(c̄, c̄) = 0`; the coefficients are `u_{i₁ i₂} = 3U` (c1), `(n-1)/2 = 4`, `n(n²-1)/12 = 60`.
No condition on `γ₄` is needed (its exponent divides `9` automatically).
-/

namespace GroupDimension

namespace Ab399

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The situation: class `≤ 4`, Tahara's data whose first-layer basis has exactly three elements
`x_{i₀}, x_{i₁}, x_{i₂}` of orders `3, 9, 9`, the active indices `act` of the basis adapted to the
kernel of the cube map (as in `ExpThree.SetupB`, without `γ₄³ = 1`). -/
structure Setup (T : Data G) (act : Fin T.s → Prop) (i₀ i₁ i₂ : Fin T.s) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  htor : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1
  valid : T.Valid
  h01 : i₀ < i₁
  h12 : i₁ < i₂
  hall : ∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂
  hd₀ : T.d i₀ = 3
  hd₁ : T.d i₁ = 9
  hd₂ : T.d i₂ = 9
  he : ∀ k, 3 ∣ T.e k
  hf : ∀ l, 3 ∣ T.f l
  hK : ∀ i, ¬ act i → ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, T.x₁ i ^ T.d i = a ^ 3 * c
  hind : ∀ cf : Fin T.s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * T.b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h

namespace Setup

variable {T : Data G} {act : Fin T.s → Prop} {i₀ i₁ i₂ : Fin T.s} (S : Setup T act i₀ i₁ i₂)
include S

variable {N : Type*} [AddCommGroup N] {A : G → N}
  (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
    A (a * b) = A a + A b)
include hA

/-- `ω(c̄_{i₁ i₂}, ·)` is `3`-torsion on `γ₂`. -/
theorem omega_three (a : G) (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    (3 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) a) = 0 := by
  sorry

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

theorem T1_eq : Star.T1 T τ A = 0 := by
  sorry

theorem T2_eq : Star.T2 T τ A = 0 := by
  sorry

theorem T3_eq : Star.T3 T τ A = 0 := by
  sorry

theorem T4_eq : Star.T4 T τ A = 0 := by
  sorry

theorem T5_eq : Star.T5 T τ A = 0 := by
  sorry

end Setup

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `Setup`. -/
theorem Setup.gen_eq_one {T : Data G} {act : Fin T.s → Prop} {i₀ i₁ i₂ : Fin T.s}
    (S : Setup T act i₀ i₁ i₂) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) : T.gen τ = 1 := by
  sorry

/-- **`D₅(Q) = 1` for `Q_ab ≅ C₃ × C₉ × C₉`, modulo Tahara.** A finite group of class `≤ 4` whose
abelianization is `C₃ × C₉ × C₉` has `D₅(Q) = 1`. -/
theorem D_five_eq_bot_of_class_four_ab399 (hT : TaharaFiveOne) {Q : Type} [Group Q] [Finite Q]
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hab : Nonempty (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 1 ≃*
      Multiplicative (ZMod 3 × ZMod 9 × ZMod 9))) :
    D 5 Q = ⊥ := by
  sorry

end Ab399

end GroupDimension
