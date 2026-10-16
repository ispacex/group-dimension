import GroupDimension

/-! Axiom audit: `lake env lean AxiomAudit.lean`. Every proved theorem of the project must
depend only on `propext`, `Classical.choice`, `Quot.sound`. -/

open GroupDimension

#print axioms GroupDimension.D_normal
#print axioms GroupDimension.D_zero
#print axioms GroupDimension.D_one
#print axioms GroupDimension.D_antitone
#print axioms GroupDimension.mul_mem_augIdeal_pow
#print axioms GroupDimension.of_commutator_sub_one
#print axioms GroupDimension.of_inv_mul_inv_mul_mul_sub_one
#print axioms GroupDimension.commutator_mem_D
#print axioms GroupDimension.commutator_D_le
#print axioms GroupDimension.lowerCentralSeries_le_D
#print axioms GroupDimension.gamma_le_D
#print axioms GroupDimension.map_mem_D
#print axioms GroupDimension.map_D_le
#print axioms GroupDimension.D_le_comap
#print axioms GroupDimension.D_two_le_commutator
#print axioms GroupDimension.D_two
#print axioms GroupDimension.lowerCentralSeries_le_map_of_surjective
#print axioms GroupDimension.lowerCentralSeries_quotient_eq_bot
#print axioms GroupDimension.D_le_of_D_quotient_eq_bot
#print axioms GroupDimension.forall_D_le_iff
#print axioms GroupDimension.dimensionQuestion5_iff
#print axioms GroupDimension.LieComparison.lieDimensionQuestion5
#print axioms GroupDimension.LieComparison.groupQuestion_def
