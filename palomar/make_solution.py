#!/usr/bin/env python3
"""Generate Solution.lean from Challenge.lean.

The Solution must contain the Challenge's definitions *verbatim* (Comparator requires every
declaration reached from a compared statement to be identical on both sides), so it is
generated: the Challenge text is copied, the development is imported, bridge lemmas between
the Challenge's Mathlib-only definitions and the development's are inserted before the first
theorem, and each `sorry` is replaced by a proof from the development.

Run from the repository root: `python3 palomar/make_solution.py` (rewrites Solution.lean).
"""
import re
import sys

CH = open('Challenge.lean').read()

HEADER_OLD = 'public import Mathlib\n'
HEADER_NEW = 'public import Mathlib\npublic import GroupDimension\n'

DOC_OLD = '# Fifth dimension subgroups: the statements submitted to Palomar'
DOC_NEW = ('# Fifth dimension subgroups: proofs of the statements submitted to Palomar\n\n'
           'GENERATED from `Challenge.lean` by `palomar/make_solution.py`; do not edit by hand.\n'
           'The definitions are the Challenge\'s, verbatim; the bridge lemmas identify them with the\n'
           'development\'s (`GroupDimension.D`, `GroupDimension.IsCandidate`, ...), and every theorem is\n'
           'proved from the development.')

BRIDGE = r'''/-! ## Bridges to the development (not compared; used by the proofs below) -/

theorem augIdeal_eq (G : Type*) [Group G] : augIdeal G = GroupDimension.augIdeal G := rfl

theorem DSet_eq (n : ℕ) (G : Type*) [Group G] : DSet n G = (GroupDimension.D n G : Set G) := rfl

theorem DSet_eq_one_iff {n : ℕ} {G : Type*} [Group G] :
    DSet n G = {1} ↔ GroupDimension.D n G = ⊥ := by
  rw [DSet_eq, ← Subgroup.coe_bot, SetLike.coe_set_eq]

theorem powSubgroup_eq {G : Type*} [Group G] (H : Subgroup G) (m : ℕ) :
    powSubgroup H m = GroupDimension.powSubgroup H m := rfl

theorem expCentralAux_eq (p : ℕ) (G : Type*) [Group G] :
    ∀ k, expCentralAux p G k = GroupDimension.expCentralAux p G k
  | 0 => by rw [expCentralAux.eq_1, GroupDimension.expCentralAux.eq_1]
  | k + 1 => by
    rw [expCentralAux.eq_2, GroupDimension.expCentralAux.eq_2, expCentralAux_eq p G k,
      powSubgroup_eq]

theorem expCentral_eq (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    expCentral p G n = GroupDimension.expCentral p G n :=
  expCentralAux_eq p G (n - 1)

theorem jennings_eq (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    jennings p G n = GroupDimension.jennings p G n := rfl

theorem isCandidate_iff {G : Type*} [Group G] {n : G} :
    IsCandidate G n ↔ GroupDimension.IsCandidate G n := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
    · rwa [← jennings_eq]
    · simpa only [expCentral_eq] using h10
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
    · rwa [jennings_eq]
    · simpa only [expCentral_eq] using h10

theorem dimensionQuestion5_iff :
    DimensionQuestion5 ↔ GroupDimension.DimensionQuestion5 := by
  constructor
  · intro h G _
    have := h G
    rwa [DSet_eq, SetLike.coe_subset_coe] at this
  · intro h G _
    rw [DSet_eq, SetLike.coe_subset_coe]
    exact h G

theorem dThreeEqGammaThree_bridge (h : DThreeEqGammaThree) : GroupDimension.DThreeEqGammaThree :=
  fun G _ => SetLike.coe_injective (by rw [← DSet_eq]; exact h G)

theorem passiDFourSquare_bridge (h : PassiDFourSquare) : GroupDimension.PassiDFourSquare :=
  fun G _ g hg => h G g (by rw [DSet_eq]; exact hg)

theorem gruenbergResidualTwo_bridge (h : GruenbergResidualTwo) :
    GroupDimension.GruenbergResidualTwo := h

'''

PROOFS = {
'D_five_eq_gamma_five_of_exp_three': r'''  rw [DSet_eq, GroupDimension.D_five_eq_gamma_five_of_exp_three G hfin h1]''',
'D_five_eq_gamma_five_of_cubes_cyclic': r'''  rw [DSet_eq, GroupDimension.D_five_eq_gamma_five_of_cubes_cyclic G hfin h3grp t ht]''',
'D_five_le_jennings': r'''  rw [DSet_eq, jennings_eq]
  exact fun g hg => GroupDimension.D_five_le_jennings hG h4 hg''',
'not_isCandidate_of_quotient_z4': r'''  intro hQ
  have hker' : f.ker = GroupDimension.expCentral 2 Q 3 := by rw [hker, expCentral_eq]
  have e : Q ⧸ GroupDimension.expCentral 2 Q 3 ≃* GroupDimension.Z4Z2pow7 :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact GroupDimension.not_isCandidate_of_quotient_z4 hcard e n (isCandidate_iff.1 hQ)''',
'false_of_card_expCentral_two_le': r'''  exact GroupDimension.false_of_card_expCentral_two_le (isCandidate_iff.1 hQ)
    (by rw [← expCentral_eq]; exact hP2le)''',
'not_isCandidate_of_rank': r'''  exact fun hQ => GroupDimension.not_isCandidate_of_rank hcard hrank n (isCandidate_iff.1 hQ)''',
'dimensionQuestion5_iff_class_three': r'''  rw [dimensionQuestion5_iff, GroupDimension.dimensionQuestion5_iff_class_three
    (dThreeEqGammaThree_bridge hD3) (passiDFourSquare_bridge hP) (gruenbergResidualTwo_bridge hG)]
  simp only [DSet_eq_one_iff]''',
'isCandidate_of_minimal': r'''  have hmin' : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ Subgroup.center Q → Nat.card N = 2 →
      GroupDimension.D 5 (Q ⧸ N) = ⊥ := fun N _ h1 h2 => DSet_eq_one_iff.1 (hmin N ‹_› h1 h2)
  obtain ⟨n, hn, hD5⟩ := GroupDimension.isCandidate_of_minimal (dThreeEqGammaThree_bridge hD3)
    hQ h4 h3 hmin' (fun h => hD (DSet_eq_one_iff.2 h))
  exact ⟨n, isCandidate_iff.2 hn, by rw [DSet_eq, hD5]⟩''',
'D_five_eq_bot_of_rank': r'''  exact DSet_eq_one_iff.2 (GroupDimension.D_five_eq_bot_of_rank (dThreeEqGammaThree_bridge hD3)
    (fun R _ _ h1 h2 => DSet_eq_one_iff.1 (h1024 R h1 h2)) hcard h4 hrank)''',
}

s = CH
assert s.count(HEADER_OLD) == 1 and s.count(DOC_OLD) == 1
s = s.replace(HEADER_OLD, HEADER_NEW).replace(DOC_OLD, DOC_NEW)
marker = '/-! ## Unconditional results -/'
assert s.count(marker) == 1
s = s.replace(marker, BRIDGE + marker)

out = []
pos = 0
names = []
for m in re.finditer(r':= by\n  sorry\n', s):
    name = re.findall(r'^theorem (\S+)', s[:m.start()], re.M)[-1]
    names.append(name)
    out.append(s[pos:m.start()])
    out.append(':= by\n' + PROOFS[name] + '\n')
    pos = m.end()
out.append(s[pos:])
s = ''.join(out)
assert 'sorry' not in s, 'unreplaced sorry'
assert set(names) == set(PROOFS), (set(names) ^ set(PROOFS))
open('Solution.lean', 'w').write(s)
print('Solution.lean:', len(names), 'theorems')
