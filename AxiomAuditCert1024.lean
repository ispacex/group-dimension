module

public import GroupDimension.Cert1024.Prop1024

@[expose] public section

/-! Axiom audit of the order-`2¹⁰` certificates (D5-34): `lake build GroupDimension.Cert1024.Prop1024`
then `lake env lean AxiomAuditCert1024.lean`. Besides `propext`, `Classical.choice`, `Quot.sound`
these depend on the 34 axioms `Data.cXX_ok._native.native_decide.ax_1_1` that `native_decide`
introduces (Lean 4.29), one per chunk: the checks `Data.c00_ok`, …, `Data.c33_ok` are evaluated by
compiled code, not by the kernel. Nothing else is assumed.
The soundness theorems themselves are in `AxiomAudit.lean` and use no extra axioms. -/

#print axioms GroupDimension.Cert1024.Data.c00_ok
#print axioms GroupDimension.Cert1024.D_five_cand
#print axioms GroupDimension.Cert1024.prop_1024
#print axioms GroupDimension.Cert1024.D_five_eq_bot_of_rank_of_complete
#print axioms GroupDimension.Cert1024.D_four_cand
#print axioms GroupDimension.Cert1024.card_cand
