import GroupDimension.Cert1024.Check

/-!
# The candidate group of a data line

A line of the data (format: `Cert1024Comp.lean`) defines the pc presentation `presOf s`, and the
group `candGroup s` is the group of that presentation (`PcGroup`). The decoding is part of its
definition; nothing about the certificate in the line is trusted: `checkStr s = true` implies
`D₅(candGroup s) = 1` (`D_five_candGroup`).
-/

namespace GroupDimension.Cert1024

/-- The candidate group of a line: the group of its pc presentation. -/
abbrev candGroup (s : String) : Type := PcGroup M (presOf s)

theorem checkVec_of_checkStr {s : String} (h : checkStr s = true) :
    checkAux M (presOf s) (fun i => (modsOf s)[i]) (fun k => (matsOf s)[k]) = true := by
  simp only [checkStr, Bool.and_eq_true] at h
  exact h.2

theorem D_four_candGroup {s : String} (h : checkStr s = true) : D 4 (candGroup s) = ⊥ :=
  D_four_eq_bot_of_checkAux (checkVec_of_checkStr h)

theorem D_five_candGroup {s : String} (h : checkStr s = true) : D 5 (candGroup s) = ⊥ :=
  D_five_eq_bot_of_checkAux (checkVec_of_checkStr h)

/-- The group of a line that passes the check has order `2¹⁰`. -/
theorem card_candGroup {s : String} (h : checkStr s = true) : Nat.card (candGroup s) = 2 ^ 10 :=
  card_eq_of_checkAux (checkVec_of_checkStr h)

end GroupDimension.Cert1024
