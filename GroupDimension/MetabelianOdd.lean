module

public import GroupDimension.Jennings.Theorem
public import GroupDimension.ClassFourOrder
public import GroupDimension.Descendants
public import GroupDimension.Statements

@[expose] public section

/-!
# `D_{p+2}(Q) ⊆ Q'' ∩ M_{p+2}(Q)` for class `≤ p + 1`, `p` odd (Lemma 6.1)

**Lemma 6.1 of the paper** (`mem_of_mem_D_add_two`): let `p` be an odd prime and `Q` a finite
`p`-group of class `≤ p + 1`. Then `D_{p+2}(Q) ⊆ Q'' ∩ M_{p+2}(Q)`, where
`M_n(Q) = Q ∩ (1 + Δ_{𝔽_p}(Q)^n)`. For `p = 3` and class `≤ 4`, `D₅(Q) ≠ 1` needs `Q'' ≠ 1`, hence
`d(Q) ≥ 3` (`rank_ge_three_of_D_five_ne_bot`).

`D_{p+2} ⊆ Q''` uses Gupta–Tahara ([GT85, Thm. 3.2(c)]: `D_{p+2} = γ_{p+2}` for metabelian
`p`-groups, `p` odd) as the explicit hypothesis `GuptaTaharaMetabelian`, applied to `Q/Q''`
(`D_le_derivedSeries_two`). `D_n ⊆ M_n` is the reduction `ℤ[Q] → 𝔽_p[Q]`
(`sub_one_mem_augIdealP_pow_of_mem_D`). `d(Q) ≥ 3` for `Q'' ≠ 1` is `card_ge_of_not_metabelian`
(Proposition 6.5, via the cyclic case of Lemma 6.3).

Here `M_n` is `Q ∩ (1 + Δ_{𝔽_p}(Q)^n)`; that it equals `∏_{i p^j ≥ n} γ_i^{p^j}` (Jennings) is
formalized only in the inclusion needed for `p = 2`, `n = 5` (`Jennings/`).
-/

namespace GroupDimension

open Subgroup MonoidAlgebra

variable {p : ℕ} [Fact p.Prime] {Q : Type} [Group Q] [Finite Q]

/-- `D_{p+2}(Q) ⊆ Q''` for a finite `p`-group of class `≤ p + 1`, `p` odd, given Gupta–Tahara. -/
theorem D_le_derivedSeries_two (hGT : GuptaTaharaMetabelian) (hp2 : p ≠ 2) (hQ : IsPGroup p Q)
    (hc : (⊤ : Subgroup Q).lowerCentralSeries (p + 1) = ⊥) :
    D (p + 2) Q ≤ derivedSeries Q 2 := by
  set N := derivedSeries Q 2
  set π := QuotientGroup.mk' N
  have hmet : derivedSeries (Q ⧸ N) 2 = ⊥ := by
    rw [← map_derivedSeries_of_surjective (QuotientGroup.mk'_surjective N), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  have hcQ : (⊤ : Subgroup (Q ⧸ N)).lowerCentralSeries (p + 1) = ⊥ := by
    rw [← lcs_map_mk N, hc, Subgroup.map_bot]
  have hD := hGT p Fact.out hp2 (Q ⧸ N) (hQ.to_quotient N) hmet
  rw [hcQ] at hD
  intro g hg
  have hg' : π g ∈ D (p + 2) (Q ⧸ N) := map_D_le π _ (mem_map_of_mem π hg)
  rw [hD, mem_bot] at hg'
  rwa [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]

/-- **Lemma 6.1.** For a finite `p`-group `Q` of class `≤ p + 1`, `p` odd, given Gupta–Tahara:
`D_{p+2}(Q) ⊆ Q'' ∩ M_{p+2}(Q)`. -/
theorem mem_of_mem_D_add_two (hGT : GuptaTaharaMetabelian) (hp2 : p ≠ 2) (hQ : IsPGroup p Q)
    (hc : (⊤ : Subgroup Q).lowerCentralSeries (p + 1) = ⊥) {g : Q} (hg : g ∈ D (p + 2) Q) :
    g ∈ derivedSeries Q 2 ∧ of (ZMod p) Q g - 1 ∈ Jennings.augIdealP p Q ^ (p + 2) :=
  ⟨D_le_derivedSeries_two hGT hp2 hQ hc hg, sub_one_mem_augIdealP_pow_of_mem_D hg⟩

/-- **Lemma 6.1, `p = 3`.** For a finite `3`-group of class `≤ 4`, given Gupta–Tahara:
`D₅(Q) ≠ 1` needs `Q'' ≠ 1`, hence `d(Q) ≥ 3`. -/
theorem rank_ge_three_of_D_five_ne_bot (hGT : GuptaTaharaMetabelian) (hQ : IsPGroup 3 Q)
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) (hD : D 5 Q ≠ ⊥) :
    derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q := by
  have hm : derivedSeries Q 2 ≠ ⊥ := fun h =>
    hD (le_bot_iff.mp (h ▸ D_le_derivedSeries_two (p := 3) hGT (by norm_num) hQ h5))
  exact ⟨hm, (card_ge_of_not_metabelian (by norm_num) hQ h5 hm).1⟩

end GroupDimension
