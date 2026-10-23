import GroupDimension.Cert1024.Data.All
import GroupDimension.MinimalCounterexample

/-!
# Proposition 5.3 of the paper from the certificates

`Data/All.lean` checks (by `native_decide`) the certificate of each of the `3400` candidates of
order `2¹⁰`, so `D₅(candidate i) = 1` for every `i` (`D_five_cand`). Here this is combined with
Lemma 5.2 (`isCandidate_of_minimal`) into Proposition 5.3 in the form used by
`D_five_eq_bot_of_rank` (`h1024`). Three statements are hypotheses:

* `hD3`: `D₃ = γ₃` (Passi; as in `MinimalCounterexample.lean`);
* `h512`: Proposition 5.1 at order `2⁹` (`D₅ = 1` for the groups of order `2⁹` and class `≤ 3`),
  a computation;
* `hcomplete`: the completeness of the list — every candidate of order `2¹⁰` is isomorphic to one
  of the `3400` groups `cand i`. This is the ANUPQ search of Prop. 5.3 together with part (d) of
  Lemma 5.2 (a candidate is an immediate descendant of step size `1` of `Q/⟨n⟩`).

The presentations `cand i` are those of the search itself: line `i` of `Data` is
`PqDescendants(SmallGroup(512, parent) : StepSize := 1)[k]` with its ANUPQ pc presentation.
-/

namespace GroupDimension.Cert1024

open Data

/-- The `i`-th candidate group of order `2¹⁰` (its pc presentation). -/
abbrev cand (i : Fin 3400) : Type := candGroup (cands.get (i.cast cands_length.symm))

theorem cand_ok (i : Fin 3400) : checkStr (cands.get (i.cast cands_length.symm)) = true := by
  have h := cands_ok
  rw [List.all_eq_true] at h
  exact h _ (List.get_mem _ _)

/-- **The certificates**: `D₅ = 1` for all `3400` candidates. -/
theorem D_five_cand (i : Fin 3400) : D 5 (cand i) = ⊥ := D_five_candGroup (cand_ok i)

/-- `D₄ = 1` for all `3400` candidates (this is what the certificates prove). -/
theorem D_four_cand (i : Fin 3400) : D 4 (cand i) = ⊥ := D_four_candGroup (cand_ok i)

/-- Each `cand i` has order `2¹⁰` (so a surjection from it onto a group of order `2¹⁰` is an
isomorphism; this is how `verify_lines.g` identifies it with the ANUPQ group). -/
theorem card_cand (i : Fin 3400) : Nat.card (cand i) = 2 ^ 10 := card_candGroup (cand_ok i)

/-- `D_n` is invariant under isomorphism. -/
theorem D_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {n : ℕ}
    (h : D n H = ⊥) : D n G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have := map_mem_D e.toMonoidHom hg
  rw [h, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using this)

/-- **Proposition 5.3**, given `D₃ = γ₃`, Proposition 5.1 at order `2⁹`, and the completeness of
the candidate list: `D₅(R) = 1` for every group of order `2¹⁰` with `γ₄(R) = 1`. -/
theorem prop_1024 (hD3 : DThreeEqGammaThree)
    (h512 : ∀ (R : Type) [Group R] [Finite R], Nat.card R = 2 ^ 9 →
      lowerCentralSeries R 3 = ⊥ → D 5 R = ⊥)
    (hcomplete : ∀ (Q : Type) [Group Q] [Finite Q] (n : Q), Nat.card Q = 2 ^ 10 →
      IsCandidate Q n → ∃ i : Fin 3400, Nonempty (Q ≃* cand i))
    (R : Type) [Group R] [Finite R] (hcard : Nat.card R = 2 ^ 10)
    (h4 : lowerCentralSeries R 3 = ⊥) : D 5 R = ⊥ := by
  have hR : IsPGroup 2 R := IsPGroup.of_card hcard
  by_contra hD
  have h3 : lowerCentralSeries R 2 ≠ ⊥ := fun h => hD (by
    rw [eq_bot_iff, ← h, ← hD3 R]; exact D_antitone (by norm_num : 3 ≤ 5))
  have hmin : ∀ N : Subgroup R, ∀ _ : N.Normal, N ≤ Subgroup.center R → Nat.card N = 2 →
      D 5 (R ⧸ N) = ⊥ := by
    intro N _ _ h2
    refine h512 (R ⧸ N) ?_ ?_
    · have h := N.card_mul_index
      rw [Subgroup.index_eq_card, hcard, h2] at h
      omega
    · refine eq_bot_iff.mpr ((lowerCentralSeries_le_map_of_surjective
        (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) 3).trans ?_)
      rw [h4, Subgroup.map_bot]
  obtain ⟨n, hn, -⟩ := isCandidate_of_minimal hD3 hR h4 h3 hmin hD
  obtain ⟨i, ⟨e⟩⟩ := hcomplete R n hcard hn
  exact hD (D_eq_bot_of_mulEquiv e (D_five_cand i))

/-- **Proposition 5.7** (`D_five_eq_bot_of_rank`) with its hypothesis `h1024` discharged by
`prop_1024`: what remains assumed is `D₃ = γ₃`, Proposition 5.1 at order `2⁹`, and the completeness
of the order-`2¹⁰` candidate list. -/
theorem D_five_eq_bot_of_rank_of_complete (hD3 : DThreeEqGammaThree)
    (h512 : ∀ (R : Type) [Group R] [Finite R], Nat.card R = 2 ^ 9 →
      lowerCentralSeries R 3 = ⊥ → D 5 R = ⊥)
    (hcomplete : ∀ (Q : Type) [Group Q] [Finite Q] (n : Q), Nat.card Q = 2 ^ 10 →
      IsCandidate Q n → ∃ i : Fin 3400, Nonempty (Q ≃* cand i))
    {Q : Type} [Group Q] [Finite Q] (hcard : Nat.card Q = 2 ^ 11)
    (h4 : lowerCentralSeries Q 3 = ⊥) (hrank : 8 ≤ Group.rank Q) : D 5 Q = ⊥ :=
  D_five_eq_bot_of_rank hD3 (fun R _ _ => prop_1024 hD3 h512 hcomplete R) hcard h4 hrank

end GroupDimension.Cert1024
