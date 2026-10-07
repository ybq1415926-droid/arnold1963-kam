import KamProject.Arnold1963.W10
import KamProject.Arnold1963.Audit.W10Branches

/-! 实际输出公理依赖，验证脚本核对每条声明名称、唯一性和标准公理集合。 -/
open KamProject.Arnold1963

#print axioms invariant_under_nonresonant_line_constant
#print axioms denseRange_unitTorusLine
#print axioms denseRange_realTorusLine
#print axioms Iteration.InitialData.projected_orbit_closure
#print axioms eq_of_analytic_autonomous_orbits
#print axioms FiniteLocalization.tori_eq_of_intersection
#print axioms FiniteLocalization.tori_pairwise_disjoint
#print axioms FiniteLocalization.goodSet_eq_sUnion_tori
#print axioms FiniteLocalization.torusResult
#print axioms FiniteLocalization.goodSet_volume_gt
#print axioms FiniteLocalization.theorem1Result
#print axioms theorem1
#print axioms theorem1_of_pointwise
#print axioms GlobalHamiltonianData.exists_finiteLocalization
#print axioms HamiltonianPatch.threshold_eq_initial_bound
#print axioms FiniteLocalization.phase_cover
#print axioms FiniteLocalization.exists_global_orbit
#print axioms theorem2
#print axioms localKAM
#print axioms Audit.W9Example.cubic_original_data
#print axioms Audit.W9Example.frequency_not_injective
#print axioms Audit.W9Example.nonconstant_on_initial_phase
#print axioms Audit.W10Example.result
#print axioms Audit.W10Example.original_data_threshold
#print axioms Audit.W10Example.actual_disjoint_tori
#print axioms Audit.W10Example.actual_torus_realization
#print axioms Audit.W10Example.actual_good_nonempty
#print axioms Audit.W10Example.actual_large_measure
#print axioms Audit.W10Example.actual_bad_measure
#print axioms Audit.W10Example.actual_good_meets_both_branches
#print axioms Audit.W10Example.actual_torus_in_one_branch
#print axioms Audit.W10Example.actual_two_branch_tori
