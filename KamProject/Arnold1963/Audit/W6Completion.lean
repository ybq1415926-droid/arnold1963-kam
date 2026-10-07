import KamProject.Arnold1963.W6
import KamProject.Arnold1963.Audit.W6Example

/-! W6 完整声明、公理依赖和非恒定扰动的实际正测度极限域审计。 -/
noncomputable section
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W6Completion

#check Iteration.threshold1_mono
#check Iteration.InitialParameters.parameters
#check Iteration.InitialParameters.cutoff_gt_one
#check Iteration.InitialParameters.cutoff_strictMono
#check Iteration.InitialParameters.cutoff_budget
#check Iteration.shell_tsum_le_two
#check Iteration.InitialParameters.total_budget
#check Iteration.InitialParameters.lossBudget_tsum_lt
#check Iteration.InitialData.state
#check Iteration.InitialData.transformation
#check Iteration.InitialData.cumulative_maps
#check Iteration.InitialData.cumulative_identity
#check Iteration.InitialData.remainder_coordinate_derivative
#check Iteration.InitialData.limit_volume_gt
#check theorem2
#check result
#check limit_nonempty
#check limit_volume_gt_one

#print axioms Iteration.threshold1_mono
#print axioms Iteration.InitialParameters.parameters
#print axioms Iteration.InitialParameters.cutoff_strictMono
#print axioms Iteration.InitialParameters.cutoff_budget
#print axioms Iteration.shell_tsum_le_two
#print axioms Iteration.InitialParameters.lossBudget_tsum_lt
#print axioms Iteration.InitialData.cumulative_identity
#print axioms Iteration.InitialData.limit_volume_gt
#print axioms theorem2
#print axioms parameters
#print axioms nonconstant
#print axioms result
#print axioms limit_nonempty
#print axioms limit_volume_gt_one

end KamProject.Arnold1963.Audit.W6Completion
