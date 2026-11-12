module

public import GroupDimension
public import GroupDimension.Cert1024.Prop1024

/-! `lake env lean D5Tags.lean` prints every `@[d5 ...]` entry of the package, one JSON
object `{"key", "decl", "comment"}` per line (read by `site/blueprint.py tags` of dimension-subrings). -/

#d5_tags
