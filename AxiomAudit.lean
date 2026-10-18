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
#print axioms GroupDimension.center_comm
#print axioms GroupDimension.comm_central
#print axioms GroupDimension.CentralRoot.zpow_central
#print axioms GroupDimension.CentralRoot.decomp
#print axioms GroupDimension.CentralRoot.ell_spec
#print axioms GroupDimension.CentralRoot.coe_retr
#print axioms GroupDimension.CentralRoot.retr_spec
#print axioms GroupDimension.CentralRoot.retr_coe
#print axioms GroupDimension.CentralRoot.retr_mul
#print axioms GroupDimension.CentralRoot.q_of
#print axioms GroupDimension.CentralRoot.induction_of
#print axioms GroupDimension.CentralRoot.q_mul_left
#print axioms GroupDimension.CentralRoot.q_mul_of_r
#print axioms GroupDimension.CentralRoot.q_iota
#print axioms GroupDimension.CentralRoot.of_r_mem_center
#print axioms GroupDimension.CentralRoot.of_zpow_mem_center
#print axioms GroupDimension.CentralRoot.of_zpow_sub_one_eq
#print axioms GroupDimension.CentralRoot.gen_mem_W
#print axioms GroupDimension.CentralRoot.sub_one_mem_center
#print axioms GroupDimension.CentralRoot.augIdeal_induction
#print axioms GroupDimension.CentralRoot.W_mul_augIdeal
#print axioms GroupDimension.CentralRoot.augIdeal_pow_le_W
#print axioms GroupDimension.CentralRoot.q_gen
#print axioms GroupDimension.CentralRoot.W_le_T
#print axioms GroupDimension.CentralRoot.iota_mem_augIdeal_pow_iff
#print axioms GroupDimension.CentralRoot.commutator_le
#print axioms GroupDimension.CentralRoot.D_eq
#print axioms GroupDimension.D_n_eq_of_index
