module

public import GroupDimension.D5Tag

/-! Tests of `@[d5 ...]` and `#d5_tags` (negative controls included). Not imported by the
library; CI builds it (`lake build GroupDimension.Test.D5Tag`). -/

public section

@[d5 "thm:a", d5 000P "part (a)"] theorem t₁ : True := trivial

/-- A docstring. -/
@[d5 0001] theorem t₂ : True := trivial

/-- error: d5: a label is a nonempty string without spaces or quotes, got "bad label" -/
#guard_msgs in @[d5 "bad label"] theorem t₃ : True := trivial

/-- error: d5: write a tag without quotes and without the prefix: @[d5 000P] -/
#guard_msgs in @[d5 "D5:000P"] theorem t₄ : True := trivial

/-- error: d5: D5:000A is already on t₅ -/
#guard_msgs in @[d5 000A, d5 000A] theorem t₅ : True := trivial

/-! The parser: a tag has exactly four digits or capitals other than `I` and `O` (a parse error
cannot be caught by `#guard_msgs`, so the attribute syntax is parsed here from strings). -/

open Lean Elab Command in
/--
info: d5 000P: ok
d5 0001 "part (a)": ok
d5 "thm:a": ok
d5 I001: error
d5 00O1: error
d5 000: error
d5 00001: error
d5 000p: error
d5 000P0: error
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let mut out := #[]
  for s in ["d5 000P", "d5 0001 \"part (a)\"", "d5 \"thm:a\"", "d5 I001", "d5 00O1", "d5 000",
      "d5 00001", "d5 000p", "d5 000P0"] do
    let r := match Parser.runParserCategory (← getEnv) `attr s with
      | .ok _ => "ok"
      | .error e => e
    out := out.push s!"{s}: {r}"
  logInfo ("\n".intercalate out.toList)

/--
info: d5 tags:
{"comment":"","decl":"t₂","key":"D5:0001"}
{"comment":"","decl":"t₅","key":"D5:000A"}
{"comment":"part (a)","decl":"t₁","key":"D5:000P"}
{"comment":"","decl":"t₁","key":"thm:a"}
-/
#guard_msgs in #d5_tags
