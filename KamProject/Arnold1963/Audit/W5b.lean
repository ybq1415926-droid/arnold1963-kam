import KamProject.Arnold1963.Audit.W5bExample

/-! W5b 的公开声明、端点、实例和核心公理依赖。 -/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W5b

example : result.perturbation.uniformNorm < iterationRemainderBound 1 amplitude delta (delta / 2) :=
  result.bound

example {z} (hz : z ∈ phaseDomain result.domain (1 - 3 * (6 * delta))) :
    ‖fderiv ℂ result.transformation.toFun z‖ < 2 := result.transformation.derivative_bound z hz

example {z} (hz : z ∈ phaseDomain result.domain (1 - 3 * (6 * delta))) :
    ‖fderiv ℂ (fderiv ℂ result.perturbation.toFun) z
      (phaseBasis (.inl 0)) (phaseBasis (.inr 0))‖ <
      2 * iterationRemainderBound 1 amplitude delta (delta / 2) / ((delta / 2 : ℝ≥0) : ℝ) ^ 2 :=
  result.second_derivative z hz _ _

#check @IterationInput.mk
#check @InductiveResult.mk
#check inductive_lemma
#check InductiveResult.nextInput
#check IterationInput.result_chart_next
#check IterationInput.result_measure_budget
#check IterationInput.result_measure_uniform
#check frequency_iteration_measure_budget
#check frequency_measure_to_uniform_action_budget
#check FrequencyChangeInput.iteration_nonempty_of_measure_budget
#print axioms AnalyticPhaseFunction.frequencyShift_derivative_bound
#print axioms IterationParameters.mean_hessian_small
#print axioms IterationInput.frequencyChange
#print axioms IterationInput.fundamental
#print axioms IterationInput.phase_buffer
#print axioms IterationInput.remainder_second_derivative_bound
#print axioms inductive_lemma
#print axioms InductiveResult.nextInput
#print axioms IterationInput.result_chart_next
#print axioms IterationInput.result_measure_budget
#print axioms IterationInput.result_measure_uniform
#print axioms AnalyticFrequencyChart.realVolume_image_le
#print axioms frequency_measure_to_uniform_action_budget
#print axioms FrequencyChangeInput.iteration_nonempty_of_measure_budget
#print axioms budget
#print axioms result
#print axioms nonconstant
#print axioms shift_nonzero
#print axioms result_realSlice_nonempty_of_explicit_point

end KamProject.Arnold1963.Audit.W5b
