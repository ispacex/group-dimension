import GroupDimension.Jennings.Main
import GroupDimension.Jennings.ClassThree

/-!
# Jennings' theorem, the hard inclusion (D5-32)

For a finite `p`-group `G`, `G ∩ (1 + Δ_{𝔽_p}(G)^n) ≤ S_n`, where `S` is the Lazard series
(`mem_lazard_of_sub_one_mem`): the Lazard series is a restricted N-series (`lazardSeries`), and
for any restricted N-series the Jennings basis of `𝔽_p[G]` gives the inclusion
(`Jennings.RestrictedSeries.mem_of_sub_one_mem`).

For `p = 2`, `n = 5` and class `≤ 3` this lands in the product `jennings 2 G 5 = G⁸ γ₂⁴ γ₃²` of
`Candidate.lean` (`mem_jennings_of_sub_one_mem`): the mod-`2` dimension subgroup
`M₅ = G ∩ (1 + Δ_{𝔽₂}^5)` of the paper lies in `jennings 2 G 5`. That `S_n` equals the Jennings
product for all `n` (Lazard's theorem) is not formalized.
-/

namespace GroupDimension

open Subgroup

variable (p : ℕ) [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- The Lazard series of a finite `p`-group as a restricted N-series. -/
noncomputable def lazardSeries (hG : IsPGroup p G) : Jennings.RestrictedSeries p G where
  S := lazard p G
  normal := lazard_normal
  one := lazard_one
  antitone := fun h1 h => lazard_antitone h1 h
  comm := fun ha hb _ hx _ hy => lazard_comm ha hb hx hy
  pow := fun ha _ hx => lazard_pow hp.out.two_le ha hx
  eventually := by
    obtain ⟨n, hn⟩ := lazard_eventually_bot (G := G) hG
    refine ⟨n + 1, by omega, eq_bot_iff.mpr ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [lazard_one, ← lazard_of_le_one (p := p) (G := G) (Nat.zero_le 1), hn]
    · exact (lazard_antitone hpos (Nat.le_succ n)).trans hn.le

variable {p}

/-- **Jennings' theorem** (the hard inclusion): `g - 1 ∈ Δ_{𝔽_p}(G)^n ⇒ g ∈ S_n`. -/
theorem mem_lazard_of_sub_one_mem (hG : IsPGroup p G) {g : G} {n : ℕ} (hn : 1 ≤ n)
    (h : MonoidAlgebra.of (ZMod p) G g - 1 ∈ Jennings.augIdealP p G ^ n) : g ∈ lazard p G n :=
  (lazardSeries p hG).mem_of_sub_one_mem hG hn h

/-- For a finite `2`-group of class `≤ 3`: `M₅ = G ∩ (1 + Δ_{𝔽₂}^5) ≤ G⁸ γ₂⁴ γ₃²`. -/
theorem mem_jennings_of_sub_one_mem (hG : IsPGroup 2 G) (h4 : lowerCentralSeries G 3 = ⊥)
    {g : G} (h : MonoidAlgebra.of (ZMod 2) G g - 1 ∈ Jennings.augIdealP 2 G ^ 5) :
    g ∈ jennings 2 G 5 :=
  ClassThree.lazard_five_le_jennings h4 (mem_lazard_of_sub_one_mem hG (by norm_num) h)

end GroupDimension
