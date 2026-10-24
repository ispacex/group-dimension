module

public import GroupDimension.DThree
public import GroupDimension.Descendants
public import GroupDimension.Gruenberg

@[expose] public section

/-!
# The results that assumed `D₃ = γ₃`, without that hypothesis

With `dThreeEqGammaThree` (`DThree.lean`) the hypothesis `hD3 : DThreeEqGammaThree` is discharged:
Proposition 2.1 with class exactly `3` (with Gruenberg's theorem `gruenbergResidualTwo`,
`Gruenberg.lean`, now only with Passi's theorem as a hypothesis) and Remark 2.3 (likewise), Lemma 5.2 (all parts), and the `D₅` form of Proposition 5.7 (now only
with Proposition 5.3 as a hypothesis). The order-`2¹⁰` statement `prop_1024` is in
`Cert1024/Prop1024.lean` (`prop_1024'`).
-/

namespace GroupDimension

/-- Class `≤ 2` has `D₅ = 1`. -/
theorem D_five_eq_bot_of_class_two' (Q : Type) [Group Q]
    (h3 : (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥) : D 5 Q = ⊥ :=
  D_five_eq_bot_of_class_two dThreeEqGammaThree Q h3

/-- **Proposition 2.1, `(1) ⇔ (3)`**, given Passi's theorem: `D₅(G) ⊆ γ₄(G)` for all groups iff
`D₅(Q) = 1` for all finite `2`-groups of class `≤ 3`. -/
theorem dimensionQuestion5_iff_finite_two_groups' (hP : PassiDFourSquare) :
    DimensionQuestion5 ↔
      ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup 2 Q → (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ →
        D 5 Q = ⊥ :=
  dimensionQuestion5_iff_finite_two_groups hP gruenbergResidualTwo

/-- **Proposition 2.1 with class exactly `3`**, given Passi's theorem. -/
theorem dimensionQuestion5_iff_class_three' (hP : PassiDFourSquare) :
    DimensionQuestion5 ↔
      ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup 2 Q → (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ →
        (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥ → D 5 Q = ⊥ :=
  dimensionQuestion5_iff_class_three dThreeEqGammaThree hP gruenbergResidualTwo

/-- **Remark 2.3 with class exactly `3`**, given Passi's theorem. -/
theorem D_five_le_of_bounded_class_three' (hP : PassiDFourSquare) (k : ℕ)
    (h : ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup 2 Q → (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ →
      (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥ → Nat.card Q ≤ 2 ^ k → D 5 Q = ⊥)
    (G : Type) [Group G] [Finite G] (hG : ∀ P : Sylow 2 G, Nat.card P ≤ 2 ^ k) :
    D 5 G ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
  D_five_le_of_bounded_class_three dThreeEqGammaThree hP k h G hG

/-- **Lemma 5.2 (a)–(c)**: a minimal counterexample is a candidate, and `D₅(Q) = ⟨n⟩`. -/
theorem isCandidate_of_minimal' {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (h4 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) (h3 : (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ Subgroup.center Q → Nat.card N = 2 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) : ∃ n, IsCandidate Q n ∧ D 5 Q = Subgroup.zpowers n :=
  isCandidate_of_minimal dThreeEqGammaThree hQ h4 h3 hmin hD

/-- **Lemma 5.2, all parts.** -/
theorem isDescendant_of_minimal' {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (h4 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) (h3 : (⊤ : Subgroup Q).lowerCentralSeries 2 ≠ ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ Subgroup.center Q → Nat.card N = 2 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) :
    ∃ n, IsCandidate Q n ∧ D 5 Q = Subgroup.zpowers n ∧ ∃ _ : (Subgroup.zpowers n).Normal,
      ∃ c ≥ 4, expCentral 2 Q (c + 1) = ⊥ ∧ expCentral 2 Q c = Subgroup.zpowers n ∧
        Nat.card (Subgroup.zpowers n) = 2 ∧
        (⊤ : Subgroup (Q ⧸ Subgroup.zpowers n)).lowerCentralSeries 3 = ⊥ ∧
        (⊤ : Subgroup (Q ⧸ Subgroup.zpowers n)).lowerCentralSeries 1 ≠ ⊥ ∧
        expCentral 2 (Q ⧸ Subgroup.zpowers n) c = ⊥ ∧ expCentral 2 (Q ⧸ Subgroup.zpowers n) (c - 1) ≠ ⊥ ∧
        IsCyclic ((⊤ : Subgroup (Q ⧸ Subgroup.zpowers n)).lowerCentralSeries 2) :=
  isDescendant_of_minimal dThreeEqGammaThree hQ h4 h3 hmin hD

/-- **Proposition 5.7**, the `D₅` form, given Proposition 5.3 (`h1024`). -/
theorem D_five_eq_bot_of_rank'
    (h1024 : ∀ (R : Type) [Group R] [Finite R], Nat.card R = 2 ^ 10 →
      (⊤ : Subgroup R).lowerCentralSeries 3 = ⊥ → D 5 R = ⊥)
    {Q : Type} [Group Q] [Finite Q] (hcard : Nat.card Q = 2 ^ 11)
    (h4 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) (hrank : 8 ≤ Group.rank Q) : D 5 Q = ⊥ :=
  D_five_eq_bot_of_rank dThreeEqGammaThree h1024 hcard h4 hrank

end GroupDimension
