module

public import GroupDimension.MinimalCounterexample
public import GroupDimension.MetabelianOdd
public import GroupDimension.Descendants

@[expose] public section

/-!
# The minimal counterexample for `p = 3` (Lemma 6.2)

**Lemma 6.2 of the paper** (`minimal_three`): let `Q` be a `3`-group of least order with
`D₅(Q) ≠ γ₅(Q)`. Then `Q` has class `4`, `Q'' ≠ 1` and `d(Q) ≥ 3`; `Z(Q)` is cyclic and
`D₅(Q) = Ω₁(Z(Q)) = ⟨z⟩` has order `3`, with `z ∈ Q'' ∩ M₅(Q)`; the last nontrivial term `P_c(Q)`
of the lower exponent-`3` central series is `⟨z⟩`, so `Q` is an immediate descendant of step
size `1` of `Q/⟨z⟩` (`P_c(Q/⟨z⟩) = 1 ≠ P_{c-1}(Q/⟨z⟩)`).

Two classical results enter as explicit hypotheses: Passi's `D₄² ⊆ γ₄` (`PassiDFourSquare`),
which for a `3`-group gives `D₄ = γ₄` (`D_four_le_of_isPGroup_three`), and Gupta–Tahara
(`GuptaTaharaMetabelian`), through Lemma 6.1 (`MetabelianOdd.lean`). Passi's theorem is proved
(`passiDFourSquare`, `Passi.lean`); `minimal_three'` (`DThreeCorollaries.lean`) has Gupta–Tahara
as the only hypothesis. Here `M₅(Q)` is
`Q ∩ (1 + Δ_{𝔽₃}(Q)^5)`.

The form with hypotheses on quotients by central subgroups of order `3`, as in Lemma 5.2, is
`minimal_three_of_quotients`. On the way: a finite abelian `p`-group with only one subgroup of
order `p` is cyclic (`isCyclic_of_unique_subgroup_prime`), and a nontrivial subgroup lying in
every central subgroup of order `p` of a finite `p`-group is `Ω₁` of a cyclic centre
(`eq_zpowers_of_le_central_prime`).
-/

namespace GroupDimension

open Subgroup MonoidAlgebra

/-! ## Abelian `p`-groups with one subgroup of order `p` -/

/-- A finite abelian `p`-group in which any two elements of order `p` generate the same subgroup
is cyclic. -/
theorem isCyclic_of_unique_subgroup_prime {p : ℕ} [hp : Fact p.Prime] {A : Type*} [Group A]
    [Finite A] (hA : IsPGroup p A) (hcomm : ∀ a b : A, a * b = b * a)
    (huniq : ∀ y z : A, orderOf y = p → orderOf z = p → y ∈ zpowers z) : IsCyclic A := by
  have hp1 := hp.out.one_lt
  obtain ⟨x, hx⟩ := Finite.exists_max (fun y : A => orderOf y)
  -- every order divides `|x|`
  have hdvd : ∀ y : A, orderOf y ∣ orderOf x := fun y => by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hA) y
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hA) x
    have hab : a ≤ b := by
      by_contra h
      have h1 : p ^ b < p ^ a := Nat.pow_lt_pow_right hp1 (by omega)
      have h2 := hx y
      rw [ha, hb] at h2
      omega
    rw [ha, hb]
    exact Nat.pow_dvd_pow p hab
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, eq_top_iff.mpr fun y _ => ?_⟩
  by_contra hy
  -- the first `y^(p^k)` in `⟨x⟩`
  have hex : ∃ k, y ^ p ^ k ∈ zpowers x := by
    obtain ⟨k, hk⟩ := hA y
    exact ⟨k, by rw [hk]; exact one_mem _⟩
  classical
  set k := Nat.find hex with hkdef
  have hk0 : k ≠ 0 := fun h => by
    have := Nat.find_spec hex
    rw [← hkdef, h, pow_zero, pow_one] at this
    exact hy this
  set w := y ^ p ^ (k - 1) with hw
  have hwx : w ∉ zpowers x := Nat.find_min hex (by omega)
  have hwp : w ^ p ∈ zpowers x := by
    rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    exact Nat.find_spec hex
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hwp
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hA) x
  have hw1 : w ≠ 1 := fun h => hwx (h ▸ one_mem _)
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hdvd w
    rw [he, pow_zero, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact hw1 this
  -- `p ∣ j`
  have hjp : (p : ℤ) ∣ j := by
    have h1 : w ^ p ^ e = 1 := by rw [← he]; exact orderOf_dvd_iff_pow_eq_one.mp (hdvd w)
    have h2 : x ^ (j * ((p ^ (e - 1) : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, hj, zpow_natCast, ← pow_mul, ← pow_succ',
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), h1]
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    have h4 : ((p * p ^ (e - 1) : ℕ) : ℤ) ∣ j * ((p ^ (e - 1) : ℕ) : ℤ) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), ← he]; exact h3
    push_cast at h4
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))).mp h4
  obtain ⟨m, rfl⟩ := hjp
  -- `u = w x^{-m}` has order `p` and lies outside `⟨x⟩`
  set u := w * x ^ (-m) with hu
  have hup : u ^ p = 1 := by
    rw [hu, (show Commute w (x ^ (-m)) from hcomm _ _).mul_pow, ← hj,
      ← zpow_natCast (x ^ (-m)) p, ← zpow_mul, ← zpow_add,
      show (p : ℤ) * m + -m * (p : ℤ) = 0 by ring, zpow_zero]
  have hu1 : u ≠ 1 := by
    intro h
    apply hwx
    rw [hu, mul_eq_one_iff_eq_inv, ← zpow_neg, neg_neg] at h
    rw [h]; exact zpow_mem_zpowers x m
  have huord : orderOf u = p := orderOf_eq_prime hup hu1
  -- the subgroup of order `p` of `⟨x⟩`
  set v := x ^ p ^ (e - 1) with hv
  have hvord : orderOf v = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hv, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0), ← he,
        pow_orderOf_eq_one]
    · rw [hv]
      refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero) ?_
      rw [he]
      exact Nat.pow_lt_pow_right hp1 (by omega)
  have huv : u ∈ zpowers v := huniq u v huord hvord
  apply hwx
  have hwu : w = u * x ^ m := by rw [hu, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [hwu]
  exact mul_mem (zpowers_le.mpr (pow_mem (mem_zpowers x) _) huv) (zpow_mem_zpowers x m)

/-- A nontrivial subgroup `H` of a finite `p`-group lying in every central subgroup of order `p`
is `Ω₁(Z(G)) = ⟨z⟩` for an element `z` of order `p`, and `Z(G)` is cyclic. -/
theorem eq_zpowers_of_le_central_prime {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) {H : Subgroup G} (hH : H ≠ ⊥)
    (hle : ∀ N : Subgroup G, N ≤ center G → Nat.card N = p → H ≤ N) :
    ∃ z ∈ center G, orderOf z = p ∧ H = zpowers z ∧ IsCyclic (center G) ∧
      ∀ x ∈ center G, x ^ p = 1 → x ∈ zpowers z := by
  haveI : Nontrivial G := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hH (Subsingleton.elim _ _)
  haveI := hG.center_nontrivial
  have hZp : IsPGroup p (center G) := hG.to_subgroup _
  obtain ⟨e, he, hcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) p
    (by rw [hcard]; exact dvd_pow_self p he.ne')
  set n : G := (z : G) with hndef
  have hnp : orderOf n = p := by rw [hndef, Subgroup.orderOf_coe, hz]
  have hnZ : n ∈ center G := z.2
  have hcentral : ∀ x ∈ center G, zpowers x ≤ center G := fun x hx => zpowers_le.mpr hx
  -- `H` is every central subgroup of order `p`
  have hHeq : ∀ N : Subgroup G, N ≤ center G → Nat.card N = p → H = N := fun N hN h2 => by
    refine eq_of_le_of_card_ge (hle N hN h2) ?_
    rw [h2]
    have hd : Nat.card H ∣ p := h2 ▸ card_dvd_of_le (hle N hN h2)
    have h1 : Nat.card H ≠ 1 := fun h => hH (card_eq_one.mp h)
    rcases (Nat.dvd_prime hp.out).mp hd with h | h
    · exact absurd h h1
    · exact h.ge
  have hzp : ∀ x ∈ center G, orderOf x = p → zpowers x = H := fun x hx hxp =>
    (hHeq _ (hcentral x hx) (by rw [Nat.card_zpowers, hxp])).symm
  have hHn : H = zpowers n := (hzp n hnZ hnp).symm
  -- (cyclic centre)
  have hcyc : IsCyclic (center G) := by
    refine isCyclic_of_unique_subgroup_prime hZp (fun a b => Subtype.ext ?_) (fun y w hy hw => ?_)
    · rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact mem_center_iff.mp b.2 a
    · have hy' : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hy]
      have hw' : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hw]
      have hmem : (y : G) ∈ zpowers (w : G) := by
        rw [hzp _ w.2 hw', ← hzp _ y.2 hy']; exact mem_zpowers _
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
      exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  refine ⟨n, hnZ, hnp, hHn, hcyc, fun x hx hxp => ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1]; exact one_mem _
  rw [← hHn, ← hzp x hx (orderOf_eq_prime hxp hx1)]
  exact mem_zpowers x

/-! ## Lemma 6.2 -/

variable {Q : Type} [Group Q] [Finite Q]

/-- For a `3`-group, Passi's `D₄² ⊆ γ₄` gives `D₄ ⊆ γ₄`. -/
theorem D_four_le_of_isPGroup_three (hP : PassiDFourSquare) (hQ : IsPGroup 3 Q) :
    D 4 Q ≤ (⊤ : Subgroup Q).lowerCentralSeries 3 := by
  intro g hg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) g
  have hodd : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have hg' : g = (g ^ 2) ^ ((3 ^ k + 1) / 2) := by
    rw [← pow_mul, show 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 by omega, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  rw [hg']
  exact pow_mem (hP Q g hg) _

/-- **Lemma 6.2**, with hypotheses on the quotients: let `Q` be a finite `3`-group of class `≤ 4`
such that `D₅(Q/N) = 1` for every central subgroup `N` of order `3`. If `D₅(Q) ≠ 1`, then
`γ₄(Q) ≠ 1`, `Q'' ≠ 1`, `d(Q) ≥ 3`, `Z(Q)` is cyclic, `D₅(Q) = Ω₁(Z(Q)) = ⟨z⟩` with `z` of
order `3` in `Q'' ∩ M₅(Q)`, and for the `3`-class `c ≥ 4`: `P_c(Q) = ⟨z⟩`,
`P_c(Q/⟨z⟩) = 1 ≠ P_{c-1}(Q/⟨z⟩)`. -/
theorem minimal_three_of_quotients (hP : PassiDFourSquare) (hGT : GuptaTaharaMetabelian)
    (hQ : IsPGroup 3 Q) (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 3 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) :
    (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ ∧ derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q ∧
      IsCyclic (center Q) ∧
      ∃ z ∈ center Q, orderOf z = 3 ∧ D 5 Q = zpowers z ∧
        (∀ x ∈ center Q, x ^ 3 = 1 → x ∈ zpowers z) ∧
        z ∈ derivedSeries Q 2 ∧ of (ZMod 3) Q z - 1 ∈ Jennings.augIdealP 3 Q ^ 5 ∧
        ∃ _ : (zpowers z).Normal, ∃ c ≥ 4, expCentral 3 Q (c + 1) = ⊥ ∧
          expCentral 3 Q c = zpowers z ∧ expCentral 3 (Q ⧸ zpowers z) c = ⊥ ∧
          expCentral 3 (Q ⧸ zpowers z) (c - 1) ≠ ⊥ := by
  have hD5γ4 : D 5 Q ≤ (⊤ : Subgroup Q).lowerCentralSeries 3 :=
    (D_antitone (by norm_num : 4 ≤ 5)).trans (D_four_le_of_isPGroup_three hP hQ)
  have hγ4 : (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ := fun h => hD (le_bot_iff.mp (h ▸ hD5γ4))
  obtain ⟨hm, hrank⟩ := rank_ge_three_of_D_five_ne_bot hGT hQ h5 hD
  -- `D₅` lies in every central subgroup of order `3`
  have hle : ∀ N : Subgroup Q, N ≤ center Q → Nat.card N = 3 → D 5 Q ≤ N := fun N hN h3 => by
    haveI := normal_of_le_center hN
    exact D_le_of_D_quotient_eq_bot N 5 (hmin N inferInstance hN h3)
  obtain ⟨z, hzZ, hz3, hDz, hcyc, hΩ⟩ := eq_zpowers_of_le_central_prime hQ hD hle
  have hzD : z ∈ D 5 Q := hDz ▸ mem_zpowers z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz3; omega
  obtain ⟨hzm, hzM⟩ := mem_of_mem_D_add_two (p := 3) hGT (by norm_num) hQ h5 hzD
  -- the `3`-class
  have hzP4 : z ∈ expCentral 3 Q 4 := lowerCentralSeries_le_expCentral 3 (hD5γ4 hzD)
  obtain ⟨c0, hc0⟩ := expCentral_eventually_bot (p := 3) hQ
  have hex : ∃ k, expCentral 3 Q (k + 1) = ⊥ :=
    ⟨c0, eq_bot_iff.mpr ((expCentral_antitone (by omega)).trans hc0.le)⟩
  classical
  set c := Nat.find hex with hcdef
  have hc1 : expCentral 3 Q (c + 1) = ⊥ := Nat.find_spec hex
  have hc4 : 4 ≤ c := by
    by_contra h
    have : z ∈ expCentral 3 Q (c + 1) := expCentral_antitone (by omega) hzP4
    rw [hc1, mem_bot] at this
    exact hz1 this
  have hcne : expCentral 3 Q c ≠ ⊥ := by
    have := Nat.find_min hex (show c - 1 < c by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  -- `P_c` is central of exponent `3`, so it lies in `Ω₁(Z(Q)) = ⟨z⟩`
  have hPc : expCentral 3 Q c ≤ zpowers z := by
    intro x hx
    have hxZ : x ∈ center Q := by
      rw [mem_center_iff]
      intro g
      have := commutator_mem_expCentral_succ (by omega) hx g
      rw [hc1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    have hx3 : x ^ 3 = 1 := by
      have := pow_mem_expCentral_succ (by omega) hx
      rwa [hc1, mem_bot] at this
    exact hΩ x hxZ hx3
  have hcardz : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have hPceq : expCentral 3 Q c = zpowers z := by
    refine eq_of_le_of_card_ge hPc ?_
    rw [hcardz]
    have hd := card_dvd_of_le hPc
    rw [hcardz] at hd
    have h1 : Nat.card (expCentral 3 Q c) ≠ 1 := fun h => hcne (card_eq_one.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h h1
    · exact h.ge
  -- the quotient `R = Q/⟨z⟩`
  haveI hN : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hzZ)
  set π := QuotientGroup.mk' (zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = zpowers z := QuotientGroup.ker_mk' _
  have hzne : zpowers z ≠ ⊥ := fun h => hz1 (by
    have : z ∈ zpowers z := mem_zpowers z
    rw [h] at this; exact this)
  refine ⟨hγ4, hm, hrank, hcyc, z, hzZ, hz3, hDz, hΩ, hzm, hzM, hN, c, hc4, hc1, hPceq, ?_, ?_⟩
  · -- `P_c(R) = 1`
    rw [← map_expCentral hπ, hPceq]
    exact map_eq_bot_of_le_ker hker.ge
  · -- `P_{c-1}(R) ≠ 1`: otherwise `P_{c-1}(Q) ≤ P_c(Q)`, hence `P_c(Q) ≤ P_{c+1}(Q) = 1`
    intro h
    obtain ⟨d, hd⟩ : ∃ d, c = d + 2 := ⟨c - 2, by omega⟩
    rw [hd] at hc1 hPceq h
    have hle' : expCentral 3 Q (d + 1) ≤ expCentral 3 Q (d + 2) := by
      rw [hPceq]
      exact (le_ker_of_map_eq_bot (by rw [map_expCentral hπ]; simpa using h)).trans hker.le
    have := expCentral_succ_le_of_le hle'
    rw [hc1, hPceq, le_bot_iff] at this
    exact hzne this

/-- **Lemma 6.2** (minimal counterexample, `p = 3`): let `Q` be a finite `3`-group with
`D₅(Q) ≠ γ₅(Q)` such that `D₅(R) = γ₅(R)` for every finite `3`-group `R` of smaller order. Then
`Q` has class `4`, `Q'' ≠ 1`, `d(Q) ≥ 3`, `Z(Q)` is cyclic, `D₅(Q) = Ω₁(Z(Q)) = ⟨z⟩` with `z` of
order `3` in `Q'' ∩ M₅(Q)`, and for the `3`-class `c ≥ 4`: `P_c(Q) = ⟨z⟩` and
`P_c(Q/⟨z⟩) = 1 ≠ P_{c-1}(Q/⟨z⟩)`, i.e. `Q` is an immediate descendant of step size `1` of
`Q/⟨z⟩`. -/
theorem minimal_three (hP : PassiDFourSquare) (hGT : GuptaTaharaMetabelian) (hQ : IsPGroup 3 Q)
    (hmin : ∀ (R : Type) [Group R] [Finite R], IsPGroup 3 R → Nat.card R < Nat.card Q →
      D 5 R = (⊤ : Subgroup R).lowerCentralSeries 4)
    (hD : D 5 Q ≠ (⊤ : Subgroup Q).lowerCentralSeries 4) :
    (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥ ∧ (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ ∧
      derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q ∧ IsCyclic (center Q) ∧
      ∃ z ∈ center Q, orderOf z = 3 ∧ D 5 Q = zpowers z ∧
        (∀ x ∈ center Q, x ^ 3 = 1 → x ∈ zpowers z) ∧
        z ∈ derivedSeries Q 2 ∧ of (ZMod 3) Q z - 1 ∈ Jennings.augIdealP 3 Q ^ 5 ∧
        ∃ _ : (zpowers z).Normal, ∃ c ≥ 4, expCentral 3 Q (c + 1) = ⊥ ∧
          expCentral 3 Q c = zpowers z ∧ expCentral 3 (Q ⧸ zpowers z) c = ⊥ ∧
          expCentral 3 (Q ⧸ zpowers z) (c - 1) ≠ ⊥ := by
  -- class `≤ 4`: otherwise `Q/γ₅` is a smaller counterexample
  have h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥ := by
    by_contra hne
    have hlt : Nat.card (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 4) < Nat.card Q := by
      rw [← Subgroup.card_mul_index ((⊤ : Subgroup Q).lowerCentralSeries 4), Subgroup.index_eq_card]
      have h1 : 1 < Nat.card ((⊤ : Subgroup Q).lowerCentralSeries 4) := by
        rw [Subgroup.one_lt_card_iff_ne_bot]; exact hne
      have h2 : 0 < Nat.card (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 4) := Nat.card_pos
      nlinarith
    have hR := hmin _ (hQ.to_quotient _) hlt
    rw [lowerCentralSeries_quotient_eq_bot 4] at hR
    exact hD (le_antisymm (D_le_of_D_quotient_eq_bot _ 5 hR) (lowerCentralSeries_le_D Q 4))
  rw [h5] at hD
  -- quotients by central subgroups of order `3` are smaller and of class `≤ 4`
  have hq : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 3 →
      D 5 (Q ⧸ N) = ⊥ := fun N _ _ h3 => by
    have hlt : Nat.card (Q ⧸ N) < Nat.card Q := by
      rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card, h3]
      have h2 : 0 < Nat.card (Q ⧸ N) := Nat.card_pos
      omega
    rw [hmin (Q ⧸ N) (hQ.to_quotient N) hlt, ← lcs_map_mk N 4, h5, Subgroup.map_bot]
  exact ⟨h5, minimal_three_of_quotients hP hGT hQ h5 hq hD⟩

end GroupDimension
