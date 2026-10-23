module

public import GroupDimension.MinimalCounterexample
public import GroupDimension.PCover

@[expose] public section

/-!
# Quotients and immediate descendants: Remark 2.2, Lemma 5.2 (d), Lemma 6.9

* **Remark 2.2** (`metabelian_of_class_three`): a group of class `≤ 3` is metabelian, since
  `G'' = [γ₂, γ₂] ⊆ γ₄`.
* **Lemma 5.2 (d)** (`isDescendant_of_isCandidate`, `isDescendant_of_minimal`): for a candidate
  `Q` with involution `n` and `2`-class `c` (so `P_c(Q) = ⟨n⟩`, Lemma 5.2 (a)–(c)), the group
  `R = Q/⟨n⟩` has class `2` or `3`, `2`-class `c - 1 ≥ 3` and `γ₃(R)` cyclic. As `P_c(Q) = ⟨n⟩`
  has order `2`, `Q` is an immediate descendant of `R` of step size `1` in the sense of
  [OBr90]: `Q` has `2`-class `c` and `Q/P_c(Q) = R`.
* **Lemma 6.9** (`filter_on_parents`): let `U ≤ M` be subgroups of a group `E` with `U` normal and
  `M ⊄ U`, and `Q = E/U`. For the paper, `E = P*`, `M` its multiplier, `U` of index `p` in `M`, so
  that `M/U = ⟨z⟩`; the immediate descendants of step size `1` are these `Q` with `N ⊄ U` for the
  nucleus `N = P_{c+1}(P*)`. If `Q` has class `4` and `M/U ≤ Q'' ∩ M₅(Q)` (i.e. `z ∈ Q'' ∩ M₅(Q)`),
  then none of `M ∩ E''`, `M ∩ M₅(E)`, `N` and `γ₄(E)` lies in `γ₅(E)`. The paper states the last
  condition only when `P` has class `3`; it holds in general. Here `M₅` is the product
  `∏_{i p^j ≥ 5} γ_i^{p^j}` (`jennings`), which is how the paper computes it (Jennings' theorem).

The tool for both lemmas: `γ_n`, the derived series, `P_n` (`expCentral`) and `M_n` (`jennings`)
commute with surjective homomorphisms (`map_expCentral`, `map_jennings`).
-/

namespace GroupDimension

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Remark 2.2 -/

/-- **Remark 2.2.** A group of class `≤ 3` is metabelian. -/
theorem metabelian_of_class_three (h4 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) :
    derivedSeries G 2 = ⊥ :=
  le_bot_iff.mp (h4 ▸ derivedSeries_two_le_lcs_three)

/-! ## Images under surjective homomorphisms -/

section Map

variable {H : Type*} [Group H]

theorem le_ker_of_map_eq_bot {f : G →* H} {K : Subgroup G} (h : K.map f = ⊥) : K ≤ f.ker := by
  rwa [Subgroup.map_eq_bot_iff] at h

theorem map_eq_bot_of_le_ker {f : G →* H} {K : Subgroup G} (h : K ≤ f.ker) : K.map f = ⊥ := by
  rwa [Subgroup.map_eq_bot_iff]

variable {p : ℕ}

theorem map_expCentralAux {f : G →* H} (hf : Function.Surjective f) :
    ∀ k, (expCentralAux p G k).map f = expCentralAux p H k
  | 0 => by rw [expCentralAux.eq_1, expCentralAux.eq_1]; exact map_top_of_surjective f hf
  | k + 1 => by
    rw [expCentralAux.eq_2, expCentralAux.eq_2, Subgroup.map_sup, map_commutator, map_powSubgroup,
      map_expCentralAux hf k, map_top_of_surjective f hf]

/-- `P_n(f(G)) = f(P_n(G))` for `f` onto. -/
theorem map_expCentral {f : G →* H} (hf : Function.Surjective f) (n : ℕ) :
    (expCentral p G n).map f = expCentral p H n :=
  map_expCentralAux hf (n - 1)

/-- `M_n(f(G)) = f(M_n(G))` for `f` onto (`M_n` as the product `∏ γ_i^{p^j}`). -/
theorem map_jennings {f : G →* H} (hf : Function.Surjective f) (n : ℕ) :
    (jennings p G n).map f = jennings p H n := by
  simp only [jennings, Subgroup.map_iSup, map_powSubgroup, lcs_map_of_surjective hf]

/-- `G''` of the image is the image of `G''`. -/
theorem map_derivedSeries_of_surjective {f : G →* H} (hf : Function.Surjective f) (n : ℕ) :
    (derivedSeries G n).map f = derivedSeries H n :=
  le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

/-- If `P_{d+1} ≤ P_{d+2}`, then `P_{d+2} ≤ P_{d+3}`. -/
theorem expCentral_succ_le_of_le {d : ℕ} (h : expCentral p G (d + 1) ≤ expCentral p G (d + 2)) :
    expCentral p G (d + 2) ≤ expCentral p G (d + 3) := by
  rw [expCentral_succ (n := d + 1) (by omega), expCentral_succ (n := d + 2) (by omega)]
  exact sup_le_sup (commutator_mono h le_rfl) (powSubgroup_mono h p)

end Map

/-! ## Lemma 5.2 (d) -/

/-- **Lemma 5.2 (d).** Let `Q` be a candidate with involution `n` (Lemma 5.2 (a)–(c)), and
`R = Q/⟨n⟩`. Then for the `2`-class `c ≥ 4` of `Q`: `P_c(Q) = ⟨n⟩` has order `2` (so `Q` is an
immediate descendant of `R` of step size `1`), `R` has class `2` or `3` (`γ₄(R) = 1 ≠ γ₂(R)`),
`2`-class `c - 1 ≥ 3` (`P_c(R) = 1 ≠ P_{c-1}(R)`), and `γ₃(R)` is cyclic. -/
theorem isDescendant_of_isCandidate {Q : Type*} [Group Q] {n : Q} [(zpowers n).Normal]
    (hQ : IsCandidate Q n) :
    ∃ c ≥ 4, expCentral 2 Q (c + 1) = ⊥ ∧ expCentral 2 Q c = zpowers n ∧ Nat.card (zpowers n) = 2 ∧
      (⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 3 = ⊥ ∧
      (⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 1 ≠ ⊥ ∧
      expCentral 2 (Q ⧸ zpowers n) c = ⊥ ∧ expCentral 2 (Q ⧸ zpowers n) (c - 1) ≠ ⊥ ∧
      IsCyclic ((⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 2) := by
  obtain ⟨c, hc4, hc1, hc⟩ := hQ.twoClass
  set π := QuotientGroup.mk' (zpowers n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = zpowers n := QuotientGroup.ker_mk' _
  have hlcs := lcs_map_of_surjective hπ
  have hn1 : n ≠ 1 := fun h => by simpa [h] using hQ.orderOf_eq_two
  have hzne : zpowers n ≠ ⊥ := fun h => hn1 (by
    have : n ∈ zpowers n := mem_zpowers n
    rw [h] at this; exact this)
  refine ⟨c, hc4, hc1, hc, by rw [Nat.card_zpowers, hQ.orderOf_eq_two], ?_, ?_, ?_, ?_, ?_⟩
  · -- class `≤ 3`
    rw [← hlcs 3, hQ.gamma_four_eq_bot, Subgroup.map_bot]
  · -- not abelian: otherwise `γ₂(Q) ≤ ⟨n⟩ ≤ Z(Q)` and `γ₃(Q) = 1`
    intro h
    apply hQ.gamma_three_ne_bot
    have h2 : (⊤ : Subgroup Q).lowerCentralSeries 1 ≤ zpowers n := by
      exact (le_ker_of_map_eq_bot (by rw [hlcs 1]; exact h)).trans hker.le
    rw [eq_bot_iff]
    show ⁅(⊤ : Subgroup Q).lowerCentralSeries 1, ⊤⁆ ≤ ⊥
    rw [commutator_le]
    intro a ha b _
    have hz : a ∈ center Q :=
      (zpowers_le.mpr hQ.mem_center) (h2 ha)
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp hz b).symm
  · -- `P_c(R) = 1`
    rw [← map_expCentral hπ, hc]
    exact map_eq_bot_of_le_ker hker.ge
  · -- `P_{c-1}(R) ≠ 1`: otherwise `P_{c-1}(Q) ≤ P_c(Q)`, hence `P_c(Q) ≤ P_{c+1}(Q) = 1`
    intro h
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
    have hle : expCentral 2 Q (d + 1) ≤ expCentral 2 Q (d + 2) := by
      rw [hc]
      exact (le_ker_of_map_eq_bot (by rw [map_expCentral hπ]; simpa using h)).trans hker.le
    have := expCentral_succ_le_of_le hle
    rw [hc1, hc, le_bot_iff] at this
    exact hzne this
  · -- `γ₃(R)` is the image of `γ₃(Q) ≤ Z(Q)`, a cyclic group
    have h3Z : (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ center Q := fun a ha => by
      rw [mem_center_iff]
      intro b
      have : ⁅b, a⁆ = 1 := by
        have h := commutator_mem_lcs (G := Q) (i := 0) (j := 2) (n := 3) (by norm_num) (mem_lcs_zero b) ha
        rw [hQ.gamma_four_eq_bot] at h
        exact h
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have := hQ.isCyclic_center
    have : IsCyclic ((⊤ : Subgroup Q).lowerCentralSeries 2) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h3Z).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe h3Z).surjective
    have hs := isCyclic_of_surjective (π.subgroupMap ((⊤ : Subgroup Q).lowerCentralSeries 2))
      (π.subgroupMap_surjective _)
    rwa [hlcs 2] at hs

/-- **Lemma 5.2, all parts**: a minimal counterexample `Q` is a candidate with `D₅(Q) = ⟨n⟩`, and
it is an immediate descendant of step size `1` of `R = Q/⟨n⟩` as in `isDescendant_of_isCandidate`. -/
theorem isDescendant_of_minimal (hD3 : DThreeEqGammaThree) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (h4 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) (h3 : (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 2 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) :
    ∃ n, IsCandidate Q n ∧ D 5 Q = zpowers n ∧ ∃ _ : (zpowers n).Normal,
      ∃ c ≥ 4, expCentral 2 Q (c + 1) = ⊥ ∧ expCentral 2 Q c = zpowers n ∧ Nat.card (zpowers n) = 2 ∧
        (⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 3 = ⊥ ∧
        (⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 1 ≠ ⊥ ∧
        expCentral 2 (Q ⧸ zpowers n) c = ⊥ ∧ expCentral 2 (Q ⧸ zpowers n) (c - 1) ≠ ⊥ ∧
        IsCyclic ((⊤ : Subgroup (Q ⧸ zpowers n)).lowerCentralSeries 2) := by
  obtain ⟨n, hn, hD5⟩ := isCandidate_of_minimal hD3 hQ h4 h3 hmin hD
  have hN : (zpowers n).Normal := normal_of_le_center (zpowers_le.mpr hn.mem_center)
  exact ⟨n, hn, hD5, hN, isDescendant_of_isCandidate hn⟩

/-! ## Lemma 6.9 -/

section Filter

variable {E : Type*} [Group E] (U M : Subgroup E) [U.Normal]

/-- `X(E/U) = X(E)U/U`, in the form used below: if the image of `M` lies in `X(E/U)`, where
`X(E/U)` is the image of `X(E)`, and `M ⊄ U`, then `M ∩ X(E) ⊄ U`. -/
theorem not_inf_le_of_map_le {X : Subgroup E} (hUM : U ≤ M) (hMU : ¬ M ≤ U)
    (hX : M.map (QuotientGroup.mk' U) ≤ X.map (QuotientGroup.mk' U)) : ¬ M ⊓ X ≤ U := by
  intro hle
  apply hMU
  intro m hm
  obtain ⟨x, hx, he⟩ := hX (mem_map_of_mem _ hm)
  -- `m = x u` with `u ∈ U ≤ M`, so `x ∈ M ∩ X ≤ U`
  have hu : x⁻¹ * m ∈ U := (QuotientGroup.eq (s := U)).mp he
  have hxM : x ∈ M := by
    have : x = m * (x⁻¹ * m)⁻¹ := by group
    rw [this]; exact mul_mem hm (inv_mem (hUM hu))
  have hxU : x ∈ U := hle ⟨hxM, hx⟩
  have : m = x * (x⁻¹ * m) := by group
  rw [this]; exact mul_mem hxU hu

/-- **Lemma 6.9 (a filter on parents).** Let `U ≤ M` be subgroups of `E`, `U` normal, `M ⊄ U`,
`Q = E/U`, and `N` a subgroup with `N ⊄ U` (the nucleus). If `Q` has class `4` and the image
`M/U` of `M` lies in `Q'' ∩ M₅(Q)`, then none of `M ∩ E''`, `M ∩ M₅(E)`, `N`, `γ₄(E)` lies in
`γ₅(E)`. -/
theorem filter_on_parents {p : ℕ} (N : Subgroup E) (hUM : U ≤ M) (hMU : ¬ M ≤ U) (hNU : ¬ N ≤ U)
    (h5 : (⊤ : Subgroup (E ⧸ U)).lowerCentralSeries 4 = ⊥)
    (h4 : (⊤ : Subgroup (E ⧸ U)).lowerCentralSeries 3 ≠ ⊥)
    (hd : M.map (QuotientGroup.mk' U) ≤ derivedSeries (E ⧸ U) 2)
    (hj : M.map (QuotientGroup.mk' U) ≤ jennings p (E ⧸ U) 5) :
    ¬ M ⊓ derivedSeries E 2 ≤ (⊤ : Subgroup E).lowerCentralSeries 4 ∧
    ¬ M ⊓ jennings p E 5 ≤ (⊤ : Subgroup E).lowerCentralSeries 4 ∧
    ¬ N ≤ (⊤ : Subgroup E).lowerCentralSeries 4 ∧
    ¬ (⊤ : Subgroup E).lowerCentralSeries 3 ≤ (⊤ : Subgroup E).lowerCentralSeries 4 := by
  have hπ : Function.Surjective (QuotientGroup.mk' U) := QuotientGroup.mk'_surjective U
  -- class `4` of `Q` needs `γ₅(E) ≤ U`
  have h5U : (⊤ : Subgroup E).lowerCentralSeries 4 ≤ U := by
    rw [← QuotientGroup.ker_mk' U, ← Subgroup.map_eq_bot_iff, lcs_map_of_surjective hπ 4, h5]
  refine ⟨fun h => ?_, fun h => ?_, fun h => hNU (h.trans h5U), fun h => ?_⟩
  · exact not_inf_le_of_map_le U M hUM hMU (by rwa [map_derivedSeries_of_surjective hπ]) (h.trans h5U)
  · exact not_inf_le_of_map_le U M hUM hMU (by rwa [map_jennings hπ]) (h.trans h5U)
  · -- `γ₄(Q) ≠ 1` needs `γ₄(E) ⊄ U`
    apply h4
    rw [← lcs_map_of_surjective hπ 3, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h.trans h5U

end Filter

end GroupDimension
