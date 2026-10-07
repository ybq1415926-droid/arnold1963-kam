import KamProject.Arnold1963.W7

set_option linter.style.header false

/-! W7 语义清单的机器可读证据入口：打印实际声明与公理，而非把注释当证明。
原清单要求的 13 项公理仍在 Audit/W7.lean；本文件增加依赖链和新增桥接的核查。
-/
open KamProject.Arnold1963 Iteration

#print InitialData
#print AnalyticFrequencyChart
#print InitialData.volume_pos
#print InitialData.volume_finite
#print InitialData.limit_realSlice_nonempty
#print InitialData.limit_volume_gt
#print iterationExponent
#print lowModes
#print mem_lowModes
#print indexLength
#print latticeLength
#check indexLength_eq_latticeLength
#print cutoff
#print previousCutoff
#print nonresonantDomain
#check InitialParameters.cutoff_numerator_gt_half
#check InitialData.frequencyDomain_succ
#check ResonanceDomainState.nonresonant
#check ResonanceDomainState.compact
#check InitialData.remainder_derivative
#check InitialData.frequency_displacement
#check InitialData.cumulative_identity
#check hamiltonianVectorField_add
#check hamiltonianVectorField_actionOnly
#check norm_hamiltonianVectorField_le
#check analyticAt_qGradient
#check analyticAt_pGradient
#check IterationInput.newChart
#check IterationInput.result_chart_next
#print State.nextInput
#check ContinuousLinearMap.norm_restrictScalars
#check InitialData.cumulative_realPhase_value
#check InitialData.cumulative_real_derivative
#check phaseShift_eq_add
#check complexifyPhase_realPartPhase_of_conj
#check torusProjection_eq_iff
#check torusProjection_representative
#check InitialParameters.frequency_tail_lt
#check InitialData.limitFrequency_tail
#check InitialData.vectorField_limit_error
#check InitialData.width_gt_third
#check InitialData.limitMap_line_analytic
#check InitialData.orbit_eq_real_angle
#check realPhaseLebesgue_physicalCell
#check InitialData.limit_physicalCell_volume_gt
#check measure_image_gt_of_uniform_limit

#print axioms InitialData.remainder_derivative
#print axioms InitialData.frequency_displacement
#print axioms InitialData.cumulative_identity
#print axioms IterationInput.newChart
#print axioms State.nextInput
#print axioms InitialData.limit_realSlice_nonempty
#print axioms InitialData.limit_volume_gt
#print axioms norm_realPhaseDerivative_le
#print axioms InitialData.cumulative_realPhase_value
#print axioms InitialData.cumulative_real_derivative
#print axioms InitialData.limit_physicalCell_volume_gt
#print axioms measure_image_gt_of_uniform_limit
