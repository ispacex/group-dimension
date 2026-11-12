module

public meta import Lean.Elab.Command

/-!
# `@[d5 ...]`: the statement of the D₅ paper that a declaration states or proves

The attribute records which statement of the paper (S. Vorobev, *On the inclusion
`D₅(G) ⊆ γ₄(G)`*, https://ispacex.github.io/d5) a declaration states or proves. It takes one key
and an optional comment, in either of two forms:

* `@[d5 "thm:g4cube"]` — a **label** of the paper, a key of the nodes of the blueprint
  (`site/blueprint.toml` of https://github.com/ispacex/dimension-subrings);
* `@[d5 000P]` — a permanent **tag** `D5:000P` (wiki 912, MATH-454): four characters, digits and
  capital letters without `I` and `O` (a subset of the format of Stacks tags).

and, in both, an optional comment: `@[d5 000P "part (a)"]`. A declaration may carry several keys:
`@[d5 "thm:gt3", d5 "ext:guptatahara"]`. The key is stored as written (a tag with the prefix
`D5:`), nothing else, so labels and tags can live side by side while the tags are introduced.

`#d5_tags` lists every `(key, declaration, comment)` of the environment, one JSON object per line,
e.g. `{"key": "thm:g4cube", "decl": "GroupDimension.D_five_eq_gamma_five_g4_cube", "comment": ""}`.

Modelled on Mathlib's `@[stacks TAG]` (`Mathlib.Tactic.CrossRefAttribute`), whose list of databases
is closed. `site/blueprint.toml` stays the source of truth: the CI of dimension-subrings compares the
output of `#d5_tags` with the `lean` fields of its nodes and fails on any difference. Unlike
Mathlib's attribute this one does not append a link to the docstring: in Lean 4.35 a declaration's
own docstring is set after `.beforeElaboration` attributes run and would replace it.
-/

public meta section

open Lean Elab Parser

namespace GroupDimension.D5Tag

/-- A declaration and a key of the paper (a label, or a tag `D5:XXXX`) that it states or proves. -/
structure Entry where
  /-- The tagged declaration. -/
  declName : Name
  /-- `thm:g4cube` (a label of the paper) or `D5:000P` (a permanent tag). -/
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

/-- The key of `@[d5 ...]`: a permanent tag (`000P`) or a label of the paper (`"thm:g4cube"`). -/
declare_syntax_cat d5Key
/-- A permanent tag `D5:XXXX`, written without the prefix. -/
syntax d5TagParser : d5Key
/-- A label of the paper, a key of the nodes of `site/blueprint.toml`. -/
syntax str : d5Key

/-- `@[d5 000P]`, `@[d5 "thm:g4cube"]`, with an optional comment: `@[d5 000P "part (a)"]`. The
statement of the D₅ paper that the declaration states or proves; see the module docstring. -/
syntax (name := d5) "d5" d5Key (ppSpace str)? : attr

/-- The key as stored: `D5:000P` for a tag, the label as written for a label. -/
def keyOf (stx : TSyntax `d5Key) : CoreM String := do
  match stx with
  | `(d5Key| $s:str) =>
    let l := s.getString
    if l.isEmpty || l.any (fun c => c.isWhitespace || c == '"') then
      throwError "d5: a label is a nonempty string without spaces or quotes, got {repr l}"
    if l.startsWith "D5:" then
      throwError "d5: write a tag without quotes and without the prefix: @[d5 {(l.drop 3).toString}]"
    return l
  | _ =>
    let some t := Syntax.isLit? d5TagKind stx.raw[0] | throwError "d5: malformed tag"
    return "D5:" ++ t

initialize registerBuiltinAttribute {
  name := `d5
  descr := "The statement of the D₅ paper that a declaration states or proves (a label or a tag)."
  add := fun decl stx _attrKind => do
    let (key, comment) ← match stx with
      | `(attr| d5 $k $[$c]?) => pure (k, c)
      | _ => throwUnsupportedSyntax
    let key ← keyOf key
    if (d5Ext.getEntries (← getEnv)).any (fun e => e.declName == decl && e.key == key) then
      throwError "d5: {key} is already on {.ofConstName decl}"
    modifyEnv (d5Ext.addEntry · { declName := decl, key, comment := (comment.map (·.getString)).getD "" })
  applicationTime := .beforeElaboration
}

/-- All entries of the environment, sorted by key, then declaration. -/
def entries (env : Environment) : Array Entry :=
  let s := PersistentEnvExtension.getState d5Ext env
  (s.2.flatten.appendList s.1).qsort fun a b =>
    a.key < b.key || (a.key == b.key && a.declName.toString < b.declName.toString)

/-- One entry as a JSON object on one line. -/
def Entry.toJson (e : Entry) : String :=
  (Json.mkObj [("key", e.key), ("decl", e.declName.toString (escape := false)),
    ("comment", e.comment)]).compress

/--
`#d5_tags` lists the entries of `@[d5 ...]`, one JSON object per line (sorted by key):
`{"key": ..., "decl": ..., "comment": ...}`. `site/blueprint.py tags` of dimension-subrings reads it.
-/
elab (name := d5Tags) "#d5_tags" : command => do
  let es := entries (← getEnv)
  if es.isEmpty then logInfo "No d5 tags found." else
  logInfo <| "\n".intercalate <| "d5 tags:" :: es.toList.map Entry.toJson

end GroupDimension.D5Tag
