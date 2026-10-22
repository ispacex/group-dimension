import GroupDimension.Jennings.Main
import GroupDimension.Jennings.ClassThree
import GroupDimension.Basic

/-!
# Jennings' theorem, the hard inclusion (D5-32)

For a finite `p`-group `G`, `G ∩ (1 + Δ_{𝔽_p}(G)^n) ≤ S_n`, where `S` is the Lazard series
(`mem_lazard_of_sub_one_mem`): the Lazard series is a restricted N-series (`lazardSeries`), and
for any restricted N-series the Jennings basis of `𝔽_p[G]` gives the inclusion
(`Jennings.RestrictedSeries.mem_of_sub_one_mem`).

For `p = 2`, `n = 5` and class `≤ 3` this lands in the product `jennings 2 G 5 = G⁸ γ₂⁴ γ₃²` of
`Candidate.lean` (`mem_jennings_of_sub_one_mem`): the mod-`2` dimension subgroup
`M₅ = G ∩ (1 + Δ_{𝔽₂}^5)` of the paper lies in `jennings 2 G 5`. With the reduction
`ℤ[G] → 𝔽_p[G]` (`modP`, `sub_one_mem_augIdealP_pow_of_mem_D`) this gives `D₅(G) ≤ jennings 2 G 5`
(`D_five_le_jennings`), which is what Lemma 5.2(b) needs. The Lazard series is the smallest
restricted N-series (`lazard_le_of_restrictedSeries`). That `S_n` equals the Jennings
product for all `n` (Lazard's theorem) is not formalized.
-/

namespace GroupDimension

open Subgroup MonoidAlgebra

/-! ## Reduction mod `p` -/

section ModP

variable (p : ℕ) (G : Type*) [Group G]

/-- Reduction mod `p`, `ℤ[G] → 𝔽_p[G]`. -/
noncomputable def modP : MonoidAlgebra ℤ G →+* MonoidAlgebra (ZMod p) G :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra (ZMod p) G) G (of (ZMod p) G)).toRingHom

variable {p G}

theorem modP_of (g : G) : modP p G (of ℤ G g) = of (ZMod p) G g := by
  simp [modP]

theorem augmentationP_modP :
    (Jennings.augmentationP p G).comp (modP p G) = (Int.castRingHom (ZMod p)).comp (augmentation G) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    simp [modP, augmentation, Jennings.augmentationP, Jennings.augAlgHomP]
  · intro g
    simp [modP, augmentation, Jennings.augmentationP, Jennings.augAlgHomP]

theorem modP_mem_augIdealP_pow (n : ℕ) {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ n) :
    modP p G x ∈ Jennings.augIdealP p G ^ n := by
  induction n generalizing x with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ] at hx ⊢
    have key : augIdeal G ^ n * augIdeal G ≤
        Ideal.comap (modP p G) (Jennings.augIdealP p G ^ n * Jennings.augIdealP p G) := by
      rw [Ideal.mul_le]
      intro r hr s hs
      rw [Ideal.mem_comap, map_mul]
      refine Ideal.mul_mem_mul (ih hr) ?_
      rw [Jennings.mem_augIdealP]
      have := congrArg (fun φ => φ s) (augmentationP_modP (p := p) (G := G))
      simp only [RingHom.comp_apply] at this
      rw [this, (mem_augIdeal).mp hs, map_zero]
    exact key hx

/-- `D_n(G)` lies in the mod-`p` dimension subgroup `G ∩ (1 + Δ_{𝔽_p}^n)`. -/
theorem sub_one_mem_augIdealP_pow_of_mem_D {n : ℕ} {g : G} (hg : g ∈ D n G) :
    of (ZMod p) G g - 1 ∈ Jennings.augIdealP p G ^ n := by
  have := modP_mem_augIdealP_pow (p := p) n ((mem_D).mp hg)
  rwa [_root_.map_sub, _root_.map_one, modP_of] at this

end ModP

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

omit hp [Finite G] in
/-- The Lazard series is the smallest restricted N-series. -/
theorem lazard_le_of_restrictedSeries (T : Jennings.RestrictedSeries p G) :
    ∀ n, 1 ≤ n → lazard p G n ≤ T.S n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [show n = 1 by omega, T.one]; exact le_top
    refine lazard_le h (fun a b ha hb han hbn hab => ?_) (fun a ha han hpa => ?_)
    · rw [commutator_le]
      intro x hx y hy
      exact T.antitone (by omega) hab (T.comm ha hb x (ih a han ha hx) y (ih b hbn hb hy))
    · refine (closure_le _).mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact T.antitone (by omega) hpa (T.pow ha x (ih a han ha hx))


/-- **Jennings' theorem** (the hard inclusion): `g - 1 ∈ Δ_{𝔽_p}(G)^n ⇒ g ∈ S_n`. -/
theorem mem_lazard_of_sub_one_mem (hG : IsPGroup p G) {g : G} {n : ℕ} (hn : 1 ≤ n)
    (h : MonoidAlgebra.of (ZMod p) G g - 1 ∈ Jennings.augIdealP p G ^ n) : g ∈ lazard p G n :=
  (lazardSeries p hG).mem_of_sub_one_mem hn h

/-- For a finite `2`-group of class `≤ 3`: `M₅ = G ∩ (1 + Δ_{𝔽₂}^5) ≤ G⁸ γ₂⁴ γ₃²`. -/
theorem mem_jennings_of_sub_one_mem (hG : IsPGroup 2 G) (h4 : lowerCentralSeries G 3 = ⊥)
    {g : G} (h : MonoidAlgebra.of (ZMod 2) G g - 1 ∈ Jennings.augIdealP 2 G ^ 5) :
    g ∈ jennings 2 G 5 :=
  ClassThree.lazard_five_le_jennings h4 (mem_lazard_of_sub_one_mem hG (by norm_num) h)


/-- For a finite `2`-group of class `≤ 3`, `D₅(G) ≤ G⁸ γ₂⁴ γ₃²` (via `M₅`). -/
theorem D_five_le_jennings {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (h4 : lowerCentralSeries G 3 = ⊥) : D 5 G ≤ jennings 2 G 5 := fun _ hg =>
  mem_jennings_of_sub_one_mem hG h4 (sub_one_mem_augIdealP_pow_of_mem_D hg)

end GroupDimension
