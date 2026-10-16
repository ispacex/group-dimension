import LieRings.Publication.Results
import GroupDimension.DTwo
import GroupDimension.Reduction

/-!
# The group question next to the Lie-ring theorem

This file imports the authors' formalization [IMP26] (package `lie-rings`, commit `ed3d9fb`,
the same commit as the submodule `upstream/lie-algebras`) and puts the two settings side by side.

| | Lie rings (`LieRings`, proved by the authors) | groups (this project) |
|---|---|---|
| filtration ring | `U(L)`, augmentation ideal `ϖ(L)` | `ℤ[G]`, augmentation ideal `Δ(G)` |
| `D_n` | `LieRings.dimensionSubring ℤ L n` | `GroupDimension.D n G` |
| `γ_{k+1}` | `LieRings.lowerCentralSeries ℤ L k` | `lowerCentralSeries G k` |
| `γ_n ⊆ D_n` | `LieRings.lowerCentralSeries_le_dimensionSubring` | `GroupDimension.lowerCentralSeries_le_D` |
| functoriality | `LieRings.map_dimensionSubring_le` | `GroupDimension.map_D_le` |
| `D₂ = γ₂` | `LieRings.dimensionSubring_two_eq_lowerCentralSeries_one` | `GroupDimension.D_two` |
| `D₃ = γ₃` | `LieRings.dimensionSubring_three_eq_lowerCentralSeries_two` | `DThreeEqGammaThree` (stated only) |
| `D₅ ⊆ γ₄` | `LieRings.Publication.corollaryD` (second half) | `DimensionQuestion5` — **open** |

## The authors' statement

```
theorem corollaryD
    (c : ℕ) (L : Type v) [LieRing L] (hc : 2 ≤ c) :
    dimensionSubring ℤ L (2 * c - 1) ≤
        lowerCentralSeries ℤ L c ⊔ LieAlgebra.derivedSeries ℤ L 2 ∧
      dimensionSubring ℤ L 5 ≤ lowerCentralSeries ℤ L 3
```
(`LieRings/Publication/Results.lean`, lines 67–76 at `ed3d9fb`.)

## Which steps of the Lie proof have group analogues

The Lie proof ([IMP26, §§5–6]) runs: Theorem C (metabelian, class `≤ c` ⇒ `D_{2c-1}(L) = 0`)
for finitely generated `L` via a *certificate*, then Lemma 6.13 (reduction to finitely
generated subrings), then Corollary 6.14 (pass to `L/(γ_{c+1}(L) + L'')`).

*Steps that carry over to groups.*
1. **Corollary 6.14, the passage to a quotient.** Functoriality of `D_n` is the same for
   groups, and `D_n(G/N) = 1 ⇒ D_n(G) ⊆ N`. Proved here: `GroupDimension.forall_D_le_iff`,
   `GroupDimension.dimensionQuestion5_iff` — the question is equivalent to `D₅(Q) = 1` for every
   group `Q` of class `≤ 3`. As for Lie rings, such a `Q` is metabelian (`[γ₂, γ₂] ⊆ γ₄`;
   standard, not formalized here).
2. **Lemma 6.13, finite generation.** An identity `g - 1 = Σ ±(x₁ - 1)⋯(x_m - 1)` with
   `m ≥ n` involves finitely many group elements, so it already holds in `ℤ[H]` for a finitely
   generated `H ≤ G`. Not formalized here, but the argument is the same.
3. **Step 1 of §6, the central extension `T = L ×_{L_ab} P`.** The fibre product
   `T = G ×_{G_ab} P` with `P` free abelian onto `G_ab` is again a central extension with
   `γ_i(T) ≅ γ_i(G)` for `i ≥ 2`, and `1 → T' → T → P → 1` splits — but as a semidirect
   product `T ≅ T' ⋊ P`, not as a direct sum: `T` is not abelian, so "additive direct summand"
   (Lemma 6.4 (2)) becomes a normal form `t · p` rather than a decomposition of a module.

*Steps without a direct analogue.*
4. **The ambient additive structure (Theorem 2.3, Corollary 2.4).** For Lie rings `L ⊆ U(L)`
   is an *additive subgroup* (integral PBW), and `U(L)` has the PBW filtration `P_{≤r}U(L)`
   with `gr U(L) ≅ Sym_ℤ(L)` and, for finitely generated `L`, an explicit `ℤ`-basis of ordered
   monomials. For groups the embedding is `g ↦ g - 1`, which is not additive:
   `gh - 1 = (g - 1) + (h - 1) + (g - 1)(h - 1)`. It becomes additive only modulo `Δ²`
   (this is exactly `D₂ = γ₂`, `GroupDimension.D_two`). The natural `ℤ`-basis of `ℤ[G]` is `G`
   itself, and there is no filtration of `ℤ[G]` playing the role of `P_{≤r}U(T)`, i.e. with
   `G` sitting in degree one as an additive direct summand and `gr` a symmetric algebra on it.
   (Over `ℚ` the `Δ`-adic graded ring of `ℚ[G]` is an enveloping algebra — Quillen 1968† —
   but the question is integral, and the torsion in `D_n/γ_n` is precisely what the integral
   structure sees.)
5. **Theorem 5.1 and Lemma 5.3, the certificate.** They recover `x ∈ D_n(L)` from its own
   image by *additive* maps: `x = r(p(x))` with `p : U(T) ↠ P_{≤2}U(T)` an additive retraction and
   `r : P_{≤2}U(T) ↠ T` the retraction of Lemma 5.3 vanishing on `Z(T) · T`. Both use that `T`
   is an abelian group inside `U(T)`. Lemma 5.3 needs a biadditive `H` on `T/Z(T)` with
   `H(x̄, ȳ) - H(ȳ, x̄) = [x, y]`; for groups the commutator is not biadditive outside class 2,
   and there is no subgroup `T ⊆ ℤ[T]` on which an additive retraction could be the identity.
   The closest group-ring analogue of "an additive functional on `ℤ[G]/Δⁿ`" is a polynomial map
   of degree `< n` on `G` in the sense of Passi [Pas79]; a group certificate would have to be
   built in those terms. We do not know of such a construction.
6. **Step 2 of §6, the retraction `p` (Proposition 6.12).** Built monomial by monomial in the
   PBW basis of `U(T)` and checked against `ϖ(T)^{2c-1}`, which is described additively through
   that basis. `Δ(T)^n` has no comparable explicit `ℤ`-basis for a general finitely generated
   nilpotent `T`; describing `Δⁿ` is itself the hard part of the dimension-subgroup problem.

What *is* known for groups in degree 5 constrains the question: [MP09, Theorem 2.28] (quoted
in [IMP26, §3.3]) gives `D₅(G)² ⊆ G'' γ₅(G)`, and `G'' ⊆ γ₄(G)`, so `D₅(G)γ₄(G)/γ₄(G)` has
exponent at most 2: the question is purely 2-primary. (`FifthDimensionSquare` below states it.)
-/

namespace GroupDimension.LieComparison

open GroupDimension

/-- The Lie-ring form of the question, `D₅(L) ⊆ γ₄(L)` for every Lie ring. -/
def LieDimensionQuestion5 : Prop :=
  ∀ (L : Type) [LieRing L], LieRings.dimensionSubring ℤ L 5 ≤ LieRings.lowerCentralSeries ℤ L 3

/-- The Lie-ring form **holds**: this is the second half of the authors' Corollary D. -/
theorem lieDimensionQuestion5 : LieDimensionQuestion5 :=
  fun L _ => (LieRings.Publication.corollaryD 3 L (by norm_num)).2

/-- The group form, for comparison: this is `GroupDimension.DimensionQuestion5`, open. -/
theorem groupQuestion_def :
    DimensionQuestion5 = ∀ (G : Type) [Group G], D 5 G ≤ lowerCentralSeries G 3 := rfl

/-- The group analogue of the general Corollary D,
`D_{2c-1}(G) ⊆ γ_{c+1}(G) G''` (Mathlib: `derivedSeries G 2 = G''`).
For `c = 2` it follows from `D₃ = γ₃`; for `c = 3` it is equivalent to
`DimensionQuestion5`, since `G'' ⊆ γ₄`. Formulation only: we do not know its status for
`c ≥ 4`, and nothing here assumes it. -/
def GroupCorollaryD (c : ℕ) : Prop :=
  ∀ (G : Type) [Group G], D (2 * c - 1) G ≤ lowerCentralSeries G c ⊔ derivedSeries G 2

/-- The group analogue of Theorem C: a metabelian group of class `≤ c` has `D_{2c-1} = 1`.
Formulation only, no claim about its truth. -/
def GroupTheoremC (c : ℕ) : Prop :=
  ∀ (G : Type) [Group G], derivedSeries G 2 = ⊥ → lowerCentralSeries G c = ⊥ →
    D (2 * c - 1) G = ⊥

/-- **The fifth-dimension-subgroup theorem** for groups, `D₅(G)² ⊆ G'' γ₅(G)`
([MP09, Theorem 2.28], as quoted in [IMP26, §3.3]); stated elementwise.
Formulation only, not proved here. -/
def FifthDimensionSquare : Prop :=
  ∀ (G : Type) [Group G], ∀ g ∈ D 5 G, g ^ 2 ∈ derivedSeries G 2 ⊔ lowerCentralSeries G 4

end GroupDimension.LieComparison
