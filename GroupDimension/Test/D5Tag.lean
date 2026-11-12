module

public import GroupDimension.D5Tag

/-! Tests of `@[d5 ...]` and `#d5_tags` (negative controls included). Not imported by the
library; CI builds it (`lake build GroupDimension.Test.D5Tag`). -/

@[d5 "thm:a", d5 000P "part (a)"] theorem t₁ : True := trivial

/-- A docstring. -/
@[d5 0001] theorem t₂ : True := trivial

/-- error: d5: a label is a nonempty string without spaces or quotes, got "bad label" -/
#guard_msgs in @[d5 "bad label"] theorem t₃ : True := trivial

/-- error: d5: write a tag without quotes and without the prefix: @[d5 000P] -/
#guard_msgs in @[d5 "D5:000P"] theorem t₄ : True := trivial

/-- error: d5: D5:000A is already on t₅ -/
#guard_msgs in @[d5 000A, d5 000A] theorem t₅ : True := trivial

/-- error: D5 tags consist of digits and capital letters other than I and O -/
#guard_msgs in @[d5 I001] theorem t₆ : True := trivial

/-- error: D5 tags have exactly 4 characters -/
#guard_msgs in @[d5 000] theorem t₇ : True := trivial

/-- error: D5 tags have exactly 4 characters -/
#guard_msgs in @[d5 00001] theorem t₈ : True := trivial

/-- error: D5 tags consist of digits and capital letters other than I and O -/
#guard_msgs in @[d5 000p] theorem t₉ : True := trivial

/--
info: d5 tags:
{"comment":"","decl":"t₂","key":"D5:0001"}
{"comment":"","decl":"t₅","key":"D5:000A"}
{"comment":"part (a)","decl":"t₁","key":"D5:000P"}
{"comment":"","decl":"t₁","key":"thm:a"}
-/
#guard_msgs in #d5_tags
