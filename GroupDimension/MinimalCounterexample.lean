import GroupDimension.Jennings.Theorem
import GroupDimension.Reduction
import GroupDimension.Statements

/-!
# A minimal counterexample is a candidate (Lemma 5.2)

**Lemma 5.2 of the paper** (`isCandidate_of_minimal`): let `Q` be a finite `2`-group of class `3`
such that `D₅(Q/N) = 1` for every central subgroup `N` of order `2`. If `D₅(Q) ≠ 1`, then
`D₅(Q) = ⟨n⟩` for a candidate `Q` with involution `n` (`IsCandidate`, `Candidate.lean`):
(a) `Z(Q)` is cyclic and `D₅(Q) = Ω₁(Z(Q))`; (b) `n ∈ γ₃ ∩ M₅`; (c) the `2`-class `c` is `≥ 4`
and `P_c = ⟨n⟩`. Part (d) of the lemma (the immediate descendant) is not formalized.

`D₅ ≤ D₃ = γ₃` uses `DThreeEqGammaThree` as a hypothesis (as in `FiniteReduction.lean`).
`n ∈ M₅` uses Jennings' theorem (`mem_jennings_of_sub_one_mem`): `D₅` maps into
`G ∩ (1 + Δ_{𝔽₂}^5)` under `ℤ[Q] → 𝔽₂[Q]` (`modP`).
-/

namespace GroupDimension

open Subgroup MonoidAlgebra

/-! ## Abelian `2`-groups with one involution are cyclic -/

/-- A finite abelian `2`-group with at most one involution is cyclic. -/
theorem isCyclic_of_unique_involution {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A)
    (hcomm : ∀ a b : A, a * b = b * a)
    (huniq : ∀ y z : A, orderOf y = 2 → orderOf z = 2 → y = z) : IsCyclic A := by
  obtain ⟨x, hx⟩ := Finite.exists_max (fun y : A => orderOf y)
  -- every order divides `|x|`
  have hdvd : ∀ y : A, orderOf y ∣ orderOf x := fun y => by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hA) y
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hA) x
    have hab : a ≤ b := by
      by_contra h
      have h1 : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 := hx y
      rw [ha, hb] at h2
      omega
    rw [ha, hb]
    exact Nat.pow_dvd_pow 2 hab
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, eq_top_iff.mpr fun y _ => ?_⟩
  by_contra hy
  -- the first `y^(2^k)` in `⟨x⟩`
  have hex : ∃ k, y ^ 2 ^ k ∈ zpowers x := by
    obtain ⟨k, hk⟩ := hA y
    exact ⟨k, by rw [hk]; exact one_mem _⟩
  classical
  set k := Nat.find hex with hkdef
  have hk0 : k ≠ 0 := fun h => by
    have := Nat.find_spec hex
    rw [← hkdef, h, pow_zero, pow_one] at this
    exact hy this
  set w := y ^ 2 ^ (k - 1) with hw
  have hwx : w ∉ zpowers x := Nat.find_min hex (by omega)
  have hw2 : w ^ 2 ∈ zpowers x := by
    rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    exact Nat.find_spec hex
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hw2
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hA) x
  have hw1 : w ≠ 1 := fun h => hwx (h ▸ one_mem _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hdvd w
    rw [he, pow_zero, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact hw1 this
  -- `j` is even
  have hj2 : (2 : ℤ) ∣ j := by
    have h1 : w ^ 2 ^ e = 1 := by rw [← he]; exact orderOf_dvd_iff_pow_eq_one.mp (hdvd w)
    have h2 : x ^ (j * ((2 ^ (e - 1) : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, hj, zpow_natCast, ← pow_mul, ← pow_succ',
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), h1]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    have h4 : ((2 * 2 ^ (e - 1) : ℕ) : ℤ) ∣ j * ((2 ^ (e - 1) : ℕ) : ℤ) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), ← he]; exact h3
    push_cast at h4
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by norm_num))).mp h4
  obtain ⟨m, rfl⟩ := hj2
  -- `u = w x^{-m}` is an involution outside `⟨x⟩`
  set u := w * x ^ (-m) with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, (show Commute w (x ^ (-m)) from hcomm _ _).mul_pow, ← hj,
      ← zpow_natCast (x ^ (-m)) 2, ← zpow_mul, ← zpow_add,
      show 2 * m + -m * ((2 : ℕ) : ℤ) = 0 by push_cast; ring, zpow_zero]
  have hu1 : u ≠ 1 := by
    intro h
    apply hwx
    rw [hu, mul_eq_one_iff_eq_inv, ← zpow_neg, neg_neg] at h
    rw [h]; exact zpow_mem_zpowers x m
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  -- the involution of `⟨x⟩`
  set v := x ^ 2 ^ (e - 1) with hv
  have hvord : orderOf v = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hv, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), ← he,
        pow_orderOf_eq_one]
    · rw [hv]
      refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ (by norm_num)) ?_
      rw [he]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have : u = v := huniq u v huord hvord
  apply hwx
  have hwu : w = u * x ^ m := by rw [hu, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [hwu, this, hv]
  exact mul_mem (pow_mem (mem_zpowers x) _) (zpow_mem_zpowers x m)

/-! ## Lemma 5.2 -/

theorem eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {n y : G} (hn : orderOf n = 2)
    (hy : y ∈ zpowers n) : y = 1 ∨ y = n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hn]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem normal_of_le_center {G : Type*} [Group G] {N : Subgroup G} (h : N ≤ center G) :
    N.Normal :=
  ⟨fun x hx g => by rw [mem_center_iff.mp (h hx) g, mul_inv_cancel_right]; exact hx⟩

/-- **Lemma 5.2 of the paper**, parts (a)–(c): a minimal counterexample is a candidate, and
`D₅(Q) = ⟨n⟩`. -/
theorem isCandidate_of_minimal (hD3 : DThreeEqGammaThree) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (h4 : lowerCentralSeries Q 3 = ⊥) (h3 : lowerCentralSeries Q 2 ≠ ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 2 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) : ∃ n, IsCandidate Q n ∧ D 5 Q = zpowers n := by
  -- `D₅` lies in every central subgroup of order `2`
  have hDle : ∀ N : Subgroup Q, N ≤ center Q → Nat.card N = 2 → D 5 Q ≤ N := fun N hN h2 => by
    haveI := normal_of_le_center hN
    exact D_le_of_D_quotient_eq_bot N 5 (hmin N inferInstance hN h2)
  -- an involution `n` of the centre; `D₅ = ⟨n⟩`
  haveI : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hD (Subsingleton.elim _ _)
  haveI := hQ.center_nontrivial
  have hZp : IsPGroup 2 (center Q) := hQ.to_subgroup _
  obtain ⟨e, he, hcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2
    (by rw [hcard]; exact dvd_pow_self 2 he.ne')
  set n : Q := (z : Q) with hndef
  have hn2 : orderOf n = 2 := by rw [hndef, Subgroup.orderOf_coe, hz]
  have hnZ : n ∈ center Q := z.2
  have hn1 : n ≠ 1 := fun h => by rw [h, orderOf_one] at hn2; omega
  have hcardn : Nat.card (zpowers n) = 2 := by rw [Nat.card_zpowers, hn2]
  have hcentral : ∀ x ∈ center Q, zpowers x ≤ center Q := fun x hx => zpowers_le.mpr hx
  have hDeq : ∀ N : Subgroup Q, N ≤ center Q → Nat.card N = 2 → D 5 Q = N := fun N hN h2 => by
    refine eq_of_le_of_card_ge (hDle N hN h2) ?_
    rw [h2]
    have hd : Nat.card (D 5 Q) ∣ 2 := h2 ▸ card_dvd_of_le (hDle N hN h2)
    have h1 : Nat.card (D 5 Q) ≠ 1 := fun h => hD (card_eq_one.mp h)
    have hle : Nat.card (D 5 Q) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.card (D 5 Q) := Nat.card_pos
    interval_cases (Nat.card (D 5 Q)) <;> simp_all
  have hDn : D 5 Q = zpowers n := hDeq _ (hcentral n hnZ) hcardn
  -- every central subgroup of order `2` is `⟨n⟩`
  have huniqN : ∀ N : Subgroup Q, N ≤ center Q → Nat.card N = 2 → N = zpowers n :=
    fun N hN h2 => (hDeq N hN h2).symm.trans hDn
  have huniq : ∀ x ∈ center Q, orderOf x = 2 → x = n := fun x hx hx2 => by
    have : zpowers x = zpowers n := huniqN _ (hcentral x hx) (by rw [Nat.card_zpowers, hx2])
    have hxn : x ∈ zpowers n := this ▸ mem_zpowers x
    rcases eq_one_or_eq_of_mem_zpowers_two hn2 hxn with h | h
    · rw [h, orderOf_one] at hx2; omega
    · exact h
  -- (a) the centre is cyclic
  have hcyc : IsCyclic (center Q) := by
    refine isCyclic_of_unique_involution hZp (fun a b => Subtype.ext ?_) (fun y w hy hw => ?_)
    · rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact mem_center_iff.mp b.2 a
    · apply Subtype.ext
      rw [huniq y y.2 (by rw [Subgroup.orderOf_coe, hy]), huniq w w.2
        (by rw [Subgroup.orderOf_coe, hw])]
  -- (b) `n ∈ γ₃ ∩ M₅`
  have hnD : n ∈ D 5 Q := hDn ▸ mem_zpowers n
  have hnγ3 : n ∈ lowerCentralSeries Q 2 := by
    rw [← hD3 Q]; exact D_antitone (by norm_num : 3 ≤ 5) hnD
  have hnM5 : n ∈ jennings 2 Q 5 :=
    mem_jennings_of_sub_one_mem hQ h4 (sub_one_mem_augIdealP_pow_of_mem_D hnD)
  -- (c) `M₅ ≤ P₄`, the `2`-class
  have hM5P4 : jennings 2 Q 5 ≤ expCentral 2 Q 4 := by
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => (closure_le _).mpr ?_
    rintro _ ⟨h, hh, rfl⟩
    have h1 := pow_pow_mem_expCentral (m := i + 1) (by omega)
      (lowerCentralSeries_le_expCentral (p := 2) i hh) j
    refine expCentral_antitone ?_ h1
    rcases j with _ | _ | _ | j
    · simp at hij; omega
    · simp at hij; omega
    · omega
    · omega
  have hnP4 : n ∈ expCentral 2 Q 4 := hM5P4 hnM5
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c0, hc0⟩ := expCentral_eventually_bot (p := 2) hQ
  have hex : ∃ k, expCentral 2 Q (k + 1) = ⊥ :=
    ⟨c0, eq_bot_iff.mpr ((expCentral_antitone (by omega)).trans hc0.le)⟩
  classical
  set c := Nat.find hex with hcdef
  have hc1 : expCentral 2 Q (c + 1) = ⊥ := Nat.find_spec hex
  have hc4 : 4 ≤ c := by
    by_contra h
    have : n ∈ expCentral 2 Q (c + 1) := expCentral_antitone (by omega) hnP4
    rw [hc1, mem_bot] at this
    exact hn1 this
  have hcne : expCentral 2 Q c ≠ ⊥ := by
    have := Nat.find_min hex (show c - 1 < c by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hPc : expCentral 2 Q c ≤ zpowers n := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    have hxZ : x ∈ center Q := by
      rw [mem_center_iff]
      intro g
      have := commutator_mem_expCentral_succ (by omega) hx g
      rw [hc1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    have hx2 : x ^ 2 = 1 := by
      have := pow_mem_expCentral_succ (by omega) hx
      rwa [hc1, mem_bot] at this
    rw [huniq x hxZ (orderOf_eq_prime hx2 hx1)]
    exact mem_zpowers n
  have hPceq : expCentral 2 Q c = zpowers n := by
    refine eq_of_le_of_card_ge hPc ?_
    rw [hcardn]
    have hd := card_dvd_of_le hPc
    rw [hcardn] at hd
    have h1 : Nat.card (expCentral 2 Q c) ≠ 1 := fun h => hcne (card_eq_one.mp h)
    have hle : Nat.card (expCentral 2 Q c) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.card (expCentral 2 Q c) := Nat.card_pos
    omega
  exact ⟨n, IsCandidate.mk inferInstance hQ h4 h3 hcyc hnZ hn2 hnγ3 hnM5 ⟨c, hc4, hc1, hPceq⟩,
    hDn⟩

/-- **Proposition 5.7 of the paper**, the `D₅` form: given `D₃ = γ₃` and Proposition 5.3
(`D₅ = 1` for the `2`-groups of order `2¹⁰` and class `≤ 3`, a computation), `D₅(Q) = 1` for every
`2`-group `Q` of order `2¹¹`, class `≤ 3` and rank `d(Q) ≥ 8`. By Lemma 5.2 a counterexample would
be a candidate, and there is none (`not_isCandidate_of_rank`). The hypothesis `h1024` allows
class `≤ 2` as well, which is immediate from `D₃ = γ₃`, so given `hD3` it is Proposition 5.3.
Neither `hD3` nor `h1024` is proved here. -/
theorem D_five_eq_bot_of_rank (hD3 : DThreeEqGammaThree)
    (h1024 : ∀ (R : Type) [Group R] [Finite R], Nat.card R = 2 ^ 10 →
      lowerCentralSeries R 3 = ⊥ → D 5 R = ⊥)
    {Q : Type} [Group Q] [Finite Q] (hcard : Nat.card Q = 2 ^ 11)
    (h4 : lowerCentralSeries Q 3 = ⊥) (hrank : 8 ≤ Group.rank Q) : D 5 Q = ⊥ := by
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hcard
  by_contra hD
  have h3 : lowerCentralSeries Q 2 ≠ ⊥ := fun h => hD (by
    rw [eq_bot_iff, ← h, ← hD3 Q]; exact D_antitone (by norm_num : 3 ≤ 5))
  have hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 2 →
      D 5 (Q ⧸ N) = ⊥ := by
    intro N _ _ h2
    refine h1024 (Q ⧸ N) ?_ ?_
    · have h := N.card_mul_index
      rw [index_eq_card, hcard, h2] at h
      omega
    · refine eq_bot_iff.mpr ((lowerCentralSeries_le_map_of_surjective
        (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) 3).trans ?_)
      rw [h4, Subgroup.map_bot]
  obtain ⟨n, hn, -⟩ := isCandidate_of_minimal hD3 hQ h4 h3 hmin hD
  exact not_isCandidate_of_rank hcard hrank n hn

end GroupDimension
