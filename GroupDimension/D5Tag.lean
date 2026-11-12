module

public meta import Lean.Elab.Command
public meta import Lean.DocString

/-!
# `@[d5 "label"]`: the statement of the paper that a declaration states or proves

`@[d5 "thm:g4cube"]` records that the declaration states or proves the statement labelled
`thm:g4cube` in the paper (S. Vorobev, *On the inclusion `D₅(G) ⊆ γ₄(G)`*,
https://ispacex.github.io/d5), and appends a link to that statement's entry on the blueprint page to
the declaration's docstring. A declaration may carry several labels (`@[d5 "a" "b"]`). `#d5_tags`
lists every tagged declaration of the environment, one line `d5 "<label>": <declaration>` each.

Modelled on Mathlib's `@[stacks TAG]` (`Mathlib.Tactic.CrossRefAttribute`), which knows only fixed
databases. The labels are those of the paper and of the nodes of the blueprint,
`site/blueprint.toml` of https://github.com/ispacex/dimension-subrings, which stays the source of
truth: its CI compares the output of `#d5_tags` with the `lean` fields of the nodes and fails on any
difference. A tag is stored as a plain string, so another labelling (e.g. stable tags) can be added
later as further strings or a second attribute without changing this one.
-/

public meta section

open Lean Elab

namespace GroupDimension.D5Tag

/-- A declaration and a label of the paper that it states or proves. -/
structure Entry where
  /-- The tagged declaration. -/
  declName : Name
  /-- The label of the paper (a key of `site/blueprint.toml`), e.g. `thm:g4cube`. -/
  tag : String
  deriving BEq, Hashable

/-- The `(declaration, label)` pairs of `@[d5 ...]`. -/
initialize d5Ext : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := id
    addEntryFn := fun s _ => s
  }

/-- The anchor of a label on the blueprint page: `thm:g4cube ↦ b-thm-g4cube` (as `build_site.py`). -/
def anchor (tag : String) : String :=
  "b-" ++ String.map (fun c => if c == ':' || c == '.' then '-' else c) tag

/-- The link to a label on the blueprint page of the site. -/
def url (tag : String) : String :=
  s!"https://ispacex.github.io/d5/blueprint.html#{anchor tag}"

/-- The attribute `@[d5 "label" ...]`: one or more labels of the paper. -/
syntax (name := d5) "d5" (ppSpace str)+ : attr

initialize registerBuiltinAttribute {
  name := `d5
  descr := "The statement(s) of the D₅ paper that a declaration states or proves (blueprint labels)."
  add := fun decl stx _attrKind => do
    let tags ← match stx with
      | `(attr| d5 $tags*) => pure (tags.map (·.getString))
      | _ => throwUnsupportedSyntax
    for tag in tags do
      if tag.isEmpty || tag.any (fun c => c.isWhitespace || c == '"') then
        throwError "d5: a label is a nonempty string without spaces or quotes, got {repr tag}"
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let links := tags.toList.map fun t => s!"[D5 paper: {t}]({url t})"
    addDocStringCore decl <| "\n\n".intercalate ((oldDoc :: links).filter (· != ""))
    for tag in tags do
      modifyEnv (d5Ext.addEntry · { declName := decl, tag := tag })
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

/-- All `(declaration, label)` pairs of the environment, sorted by label, then declaration. -/
def entries (env : Environment) : Array Entry :=
  let s := PersistentEnvExtension.getState d5Ext env
  (s.2.flatten.appendList s.1).qsort fun a b =>
    a.tag < b.tag || (a.tag == b.tag && a.declName.toString < b.declName.toString)

/--
`#d5_tags` lists the declarations tagged `@[d5 ...]`, one line `d5 "<label>": <declaration>` per
pair (sorted by label), for `site/blueprint.py tags` of dimension-subrings to compare with the
blueprint.
-/
elab (name := d5Tags) "#d5_tags" : command => do
  let es := entries (← getEnv)
  if es.isEmpty then logInfo "No d5 tags found." else
  logInfo <| "\n".intercalate <| es.toList.map fun e =>
    s!"d5 \"{e.tag}\": {e.declName.toString (escape := false)}"

end GroupDimension.D5Tag
