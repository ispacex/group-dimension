module

public meta import Lean.Elab.Command

/-!
# `@[d5 ...]`: the statement of the D₅ paper that a declaration states or proves

The attribute records which statement of the paper (S. Vorobev, *On the inclusion
`D₅(G) ⊆ γ₄(G)`*, https://ispacex.github.io/d5) a declaration states or proves, by the statement's
permanent **tag** `D5:XXXX` (wiki 912, MATH-454, MATH-457), written without the prefix: `@[d5 000P]`.
A tag is four characters, digits and capital letters without `I` and `O` (a subset of the format
of Stacks tags); it is the `tag` of a node of the blueprint (`site/blueprint.toml` of
https://github.com/ispacex/dimension-subrings: the statements of the paper, and the nodes outside
it, `ext:…` for results of the literature and `own:…` for results proved here but not in the
paper), and it stays when the paper is renumbered or a `\label` renamed. An optional comment may
follow: `@[d5 000P "part (a)"]`. A declaration may carry several tags: `@[d5 002V, d5 0031]`.

Labels of the paper (`@[d5 "thm:g4cube"]`) were accepted until MATH-458; they are refused now, with
the hint to write the tag. The key is stored with the prefix, `D5:000P`.

`#d5_tags` lists every `(key, declaration, comment)` of the environment, one JSON object per line
(the order of the fields is not significant), e.g.
`{"comment":"","decl":"GroupDimension.D_five_eq_gamma_five_of_g4_cube","key":"D5:000P"}`.

Modelled on Mathlib's `@[stacks TAG]` (`Mathlib.Tactic.CrossRefAttribute`), whose list of databases
is closed. **This attribute is the source of truth** for which declaration formalizes which
statement (MATH-458): the `lean` fields of the nodes of `site/blueprint.toml` are written from the
output of `#d5_tags` (`site/blueprint.py sync`), and the CI of dimension-subrings fails if they
differ from it. Unlike
Mathlib's attribute this one does not append a link to the docstring: tried on Lean 4.35, a link
appended at `.beforeElaboration` was gone from a declaration with its own docstring (that docstring
is added later, with the definition), so it was dropped.
-/

public meta section

open Lean Elab Parser

namespace GroupDimension.D5Tag

/-- A declaration and the tag `D5:XXXX` of the statement of the paper that it states or proves. -/
structure Entry where
  /-- The tagged declaration. -/
  declName : Name
  /-- The tag with its prefix, e.g. `D5:000P`. -/
  key : String
  /-- An optional comment, e.g. `part (a)`. -/
  comment : String
  deriving BEq, Hashable

/-- The entries of `@[d5 ...]`. -/
initialize d5Ext : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := id
    addEntryFn := fun s _ => s
  }

/-- A character of a permanent tag: a digit or a capital letter other than `I` and `O`. -/
def isTagChar (c : Char) : Bool :=
  c.isDigit || (c.isUpper && c != 'I' && c != 'O')

/-- The node kind of a permanent tag (`000P`). -/
abbrev d5TagKind : SyntaxNodeKind := `d5Tag

/-- A permanent tag: exactly four digits or capital letters other than `I` and `O`. (A plain
identifier or number does not do: `000P` lexes as a number followed by an identifier.) -/
def d5TagFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (fun c => c.isAlphanum) c s
  if s.hasError then
    s
  else if s.pos == i then
    ParserState.mkError s "D5 tag"
  else
    let tag := c.extract i s.pos
    if !tag.all isTagChar then
      ParserState.mkUnexpectedError s
        "D5 tags consist of digits and capital letters other than I and O"
    else if tag.length != 4 then
      ParserState.mkUnexpectedError s "D5 tags have exactly 4 characters"
    else
      mkNodeToken d5TagKind i true c s

@[inherit_doc d5TagFn]
def d5TagNoAntiquot : Parser := {
  fn   := d5TagFn
  info := mkAtomicInfo "d5Tag"
}

@[inherit_doc d5TagFn]
def d5TagParser : Parser :=
  withAntiquot (mkAntiquot "d5Tag" d5TagKind) d5TagNoAntiquot

end GroupDimension.D5Tag

namespace Lean.PrettyPrinter

/-- The formatter of a D5 tag. -/
@[combinator_formatter GroupDimension.D5Tag.d5TagNoAntiquot]
def Formatter.d5TagNoAntiquot.formatter := Formatter.visitAtom GroupDimension.D5Tag.d5TagKind

/-- The parenthesizer of a D5 tag. -/
@[combinator_parenthesizer GroupDimension.D5Tag.d5TagNoAntiquot]
def Parenthesizer.d5TagNoAntiquot.parenthesizer := Parenthesizer.visitToken

end Lean.PrettyPrinter

namespace GroupDimension.D5Tag

/-- All entries of the environment, sorted by key, then declaration. -/
def entries (env : Environment) : Array Entry :=
  let s := PersistentEnvExtension.getState d5Ext env
  (s.2.flatten.appendList s.1).qsort fun a b =>
    a.key < b.key || (a.key == b.key && a.declName.toString < b.declName.toString)

/-- `@[d5 000P]`, with an optional comment: `@[d5 000P "part (a)"]`. The statement of the D₅ paper
that the declaration states or proves, by its permanent tag `D5:XXXX` written without the prefix;
see the module docstring. (A string in place of the tag is parsed only to refuse it with a hint.) -/
syntax (name := d5) "d5" (d5TagParser <|> str) (ppSpace str)? : attr

/-- The key as stored, `D5:000P`. A string is refused: a tag is written without quotes and without
the prefix, and a label of the paper is no longer a key (MATH-458). -/
def keyOf (k : Syntax) : CoreM String := do
  if let some t := Syntax.isLit? d5TagKind k then
    return "D5:" ++ t
  let some l := k.isStrLit? | throwError "d5: malformed key {k}"
  if l.startsWith "D5:" then
    throwError "d5: write a tag without quotes and without the prefix: @[d5 {(l.drop 3).toString}]"
  throwError "d5: write the permanent tag of the statement, not a label: @[d5 XXXX], the tag of \
    node {repr l} in site/blueprint.toml of dimension-subrings"

initialize registerBuiltinAttribute {
  name := `d5
  descr := "The statement of the D₅ paper that a declaration states or proves (its tag D5:XXXX)."
  add := fun decl stx _attrKind => do
    -- `stx` is `d5 key comment?`
    let key ← keyOf stx[1]
    let comment := (stx[2].getOptional?.bind (·.isStrLit?)).getD ""
    if (entries (← getEnv)).any (fun e => e.declName == decl && e.key == key) then
      throwError "d5: {key} is already on {.ofConstName decl}"
    modifyEnv (d5Ext.addEntry · { declName := decl, key, comment })
  applicationTime := .beforeElaboration
}

/-- One entry as a JSON object on one line. -/
def Entry.toJson (e : Entry) : String :=
  (Json.mkObj [("key", e.key), ("decl", e.declName.toString (escape := false)),
    ("comment", e.comment)]).compress

/--
`#d5_tags` lists the entries of `@[d5 ...]`, one JSON object per line (sorted by key), with the
fields `key`, `decl` and `comment`. `site/blueprint.py tags` and `sync` of dimension-subrings read it.
-/
elab (name := d5Tags) "#d5_tags" : command => do
  let es := entries (← getEnv)
  if es.isEmpty then logInfo "No d5 tags found." else
  logInfo <| "\n".intercalate <| "d5 tags:" :: es.toList.map Entry.toJson

end GroupDimension.D5Tag
