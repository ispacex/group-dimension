import GroupDimension.LowerCentral
import GroupDimension.Statements

/-!
# Reducing the `D₅ ⊆ γ₄` question to nilpotent groups of class ≤ 3

This mirrors the last step of the Lie-ring proof ([IMP26, Corollary 6.14]: pass to
`L / (γ_{c+1}(L) + L'')` and use functoriality). For groups the passage is the same:

* `D_n(G) ⊆ γ_{k+1}(G)` for all `G` **iff** `D_n(Q) = 1` for every `Q` with `γ_{k+1}(Q) = 1`.

In particular `DimensionQuestion5` is equivalent to: *every nilpotent group of class at most 3
has trivial fifth dimension subgroup*. (Such a group is automatically metabelian, since
`[γ₂, γ₂] ⊆ γ₄`; that standard fact is not formalized here.)

Everything in this file is proved.
-/

namespace GroupDimension

variable {G H : Type*} [Group G] [Group H]

/-- For a surjection `f : G → H`, `γ_{k+1}(H) ⊆ f(γ_{k+1}(G))` (the reverse of Mathlib's
`lowerCentralSeries.map`). -/
theorem lowerCentralSeries_le_map_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (k : ℕ) : lowerCentralSeries H k ≤ (lowerCentralSeries G k).map f := by
  induction k with
  | zero => simp [Subgroup.map_top_of_surjective f hf]
  | succ k ih =>
    change ⁅lowerCentralSeries H k, ⊤⁆ ≤ (⁅lowerCentralSeries G k, ⊤⁆ : Subgroup G).map f
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
    exact Subgroup.commutator_mono ih le_rfl

/-- In `G / γ_{k+1}(G)` the term `γ_{k+1}` is trivial. -/
theorem lowerCentralSeries_quotient_eq_bot (k : ℕ) :
    lowerCentralSeries (G ⧸ lowerCentralSeries G k) k = ⊥ := by
  apply le_bot_iff.mp
  calc lowerCentralSeries (G ⧸ lowerCentralSeries G k) k
      ≤ (lowerCentralSeries G k).map (QuotientGroup.mk' (lowerCentralSeries G k)) :=
        lowerCentralSeries_le_map_of_surjective _ (QuotientGroup.mk'_surjective _) k
    _ = ⊥ := QuotientGroup.map_mk'_self _

/-- If `D_n(G/N) = 1` then `D_n(G) ⊆ N` (functoriality of `D_n`). -/
theorem D_le_of_D_quotient_eq_bot (N : Subgroup G) [N.Normal] (n : ℕ)
    (h : D n (G ⧸ N) = ⊥) : D n G ≤ N := by
  intro g hg
  have h1 : QuotientGroup.mk' N g ∈ D n (G ⧸ N) := map_mem_D _ hg
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

/-- **Reduction.** `D_n ⊆ γ_{k+1}` holds for all groups iff `D_n` vanishes on all groups with
`γ_{k+1} = 1` (nilpotent of class `≤ k`). -/
theorem forall_D_le_iff (n k : ℕ) :
    (∀ (G : Type) [Group G], D n G ≤ lowerCentralSeries G k) ↔
      ∀ (Q : Type) [Group Q], lowerCentralSeries Q k = ⊥ → D n Q = ⊥ := by
  constructor
  · intro h Q _ hQ
    exact le_bot_iff.mp (hQ ▸ h Q)
  · intro h G _
    exact D_le_of_D_quotient_eq_bot _ n (h _ (lowerCentralSeries_quotient_eq_bot k))

/-- **`DimensionQuestion5` ⇔ every nilpotent group of class ≤ 3 has `D₅ = 1`.** -/
theorem dimensionQuestion5_iff :
    DimensionQuestion5 ↔
      ∀ (Q : Type) [Group Q], lowerCentralSeries Q 3 = ⊥ → D 5 Q = ⊥ :=
  forall_D_le_iff 5 3

end GroupDimension
