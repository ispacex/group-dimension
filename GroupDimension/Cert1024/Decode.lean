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

theorem D_five_candGroup {s : String} (h : checkStr s = true) : D 5 (candGroup s) = ⊥ :=
  D_five_eq_bot_of_checkAux h

end GroupDimension.Cert1024
