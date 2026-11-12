module

public import GroupDimension.G4Cube

@[expose] public section

/-!
# The exact identity `(⋆)`: definitions (Theorem 6.11 of the paper; MATH-448)

For Tahara's data `T` and a family `τ`, the identity `(⋆)` of the proof of Theorem 6.11
(MATH wiki page 891, §3) reads, written additively in `γ₄` (or after any map `A` additive on `γ₃`),
`2 g(τ) = T₁ + T₂ + T₃ + T₄ + T₅` with
* `T₁ = ∑_{i<h} u_{ih} Δ_{ih}`, `Δ_{ih} = [x_i^{d(h)}, x_h] + [x_h^{d(h)}, x_i]`;
* `T₂ = -∑_{h<i} u_{hi} q_{hi} [Y_h, x_i, x_i]`, `Y_h = x_h^{d(h)}`, `q_{hi} = d(i)/d(h)`;
* `T₃ = -∑_{i<g≤h} w'_{igh} [Y_g, x_i, x_h]`;
* `T₄ = -∑_{j<k<h} w''_{jkh} [Y_h, [x_j, x_k]]`;
* `T₅ = -∑_{i,k} v_{ik} binom(d(i), 2) [x_{2k}, x_i, x_i]`.
It holds in every group of class `≤ 4` for every `τ` satisfying (B), (D₂), (E), (F₂); no condition
on the exponent of `γ₄` is needed. Theorem 6.11 itself (`G4Cube.lean`) is proved by a shorter route
that uses `γ₄³ = 1` early; the exact identity is needed when `γ₄` has exponent `9`.

Here the terms are defined after a map `A : G → N` into an additive group; the identity is
`Star.two_smul_gen_eq` (`Star.lean`), for `A` additive on `γ₃`.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- The `w`-part of condition (E) in row `r`, column `l`. -/
def Ew (T : Data G) (τ : Coeffs T.s T.t) (r : Fin T.s) (l : Fin T.u) : ℤ :=
  (∑ g, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0) +
  (∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0) +
  (∑ g, ∑ h, if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0)

/-- `T₁ = ∑_{i<h} u_{ih} Δ_{ih}`, `Δ_{ih} = [x_i^{d(h)}, x_h] [x_h^{d(h)}, x_i]`. -/
def T1 (T : Data G) (τ : Coeffs T.s T.t) (A : G → N) : N :=
  ∑ i, ∑ h, if i < h then
    τ.u i h • A (tc (T.x₁ i ^ T.d h) (T.x₁ h) * tc (T.x₁ h ^ T.d h) (T.x₁ i)) else 0

/-- `T₂ = -∑_{h<i} u_{hi} q_{hi} [Y_h, x_i, x_i]`. -/
def T2 (T : Data G) (τ : Coeffs T.s T.t) (A : G → N) : N :=
  -∑ h, ∑ i, if h < i then
    (τ.u h i * T.q h i) • A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ i)) else 0

/-- `T₃ = -∑_{i<g≤h} w'_{igh} [Y_g, x_i, x_h]`. -/
def T3 (T : Data G) (τ : Coeffs T.s T.t) (A : G → N) : N :=
  -∑ i, ∑ g, ∑ h, if i < g ∧ g ≤ h then
    τ.w' i g h • A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ i)) (T.x₁ h)) else 0

/-- `T₄ = -∑_{j<k<h} w''_{jkh} [Y_h, [x_j, x_k]]`. -/
def T4 (T : Data G) (τ : Coeffs T.s T.t) (A : G → N) : N :=
  -∑ j, ∑ k, ∑ h, if j < k ∧ k < h then
    τ.w'' j k h • A (tc (T.x₁ h ^ T.d h) (tc (T.x₁ j) (T.x₁ k))) else 0

/-- `T₅ = -∑_{i,k} v_{ik} binom(d(i), 2) [x_{2k}, x_i, x_i]`. -/
def T5 (T : Data G) (τ : Coeffs T.s T.t) (A : G → N) : N :=
  -∑ i, ∑ k, (τ.v i k * T.ch i 2) • A (tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i))

end Star

end GroupDimension
