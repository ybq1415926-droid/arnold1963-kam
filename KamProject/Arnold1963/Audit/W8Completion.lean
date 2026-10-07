import KamProject.Arnold1963.W8
import KamProject.Arnold1963.Audit.W6Example

/-! W8 审计：复用 W6 的非恒定扰动样例，不另加极限性质或零扰动假设。
本例 n=1、ρ₀=1、κ=1/2 是 W6Completion.parameters 类型中的固定参数，
一般 localKAM 仍量化于任意满足 InitialParameters 的参数及相匹配的 InitialData。
原 26 条实际输出保留在 w8-20261002-axioms-output.txt；
2026-10-03 的 31 条复核输出见 w8-review-20261003-axioms-output.txt。
-/
noncomputable section
open Set MeasureTheory Function Topology
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W8Completion
open Iteration W6Completion
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- parameters 与 initialData 的维数、域和数值参数在类型层面匹配。 -/
theorem result : LocalKAMResult parameters initialData := localKAM parameters initialData

/-- 两个非恒定性见证确实属于原始相域 F₀；成员关系由域定义证明，不能由解析性推出。
作用坐标为单位复圆盘的中心 0；两组角坐标均为实数，虚部为 0≤ρ₀=1。
-/
theorem nonconstant_points_mem :
    (0, 0) ∈ initialData.phase parameters 0 ∧
    (0, fun _ => (Real.pi : ℂ)) ∈ initialData.phase parameters 0 := by
  have hp : (0 : ComplexSpace 1) ∈ initialData.domain := by
    change (0 : ComplexSpace 1) ∈ realCenteredPolydisc 0 (fun _ => 1)
    simp [realCenteredPolydisc]
  simp only [InitialData.phase, InitialData.domain_zero, width_zero]
  constructor
  · exact ⟨hp, complexify_mem_angleStrip 0 1⟩
  · exact ⟨hp, complexify_mem_angleStrip (fun _ => Real.pi) 1⟩

theorem nonconstant_input : initialData.perturbation.toFun (0, 0) ≠
    initialData.perturbation.toFun (0, fun _ => (Real.pi : ℂ)) := W6Completion.nonconstant

/-- 原相域内的非恒定性，不仅是总函数在两个未经检查的环境点取值不同。 -/
theorem nonconstant_on_initial_phase : ∃ z ∈ initialData.phase parameters 0,
    ∃ w ∈ initialData.phase parameters 0,
      initialData.perturbation.toFun z ≠ initialData.perturbation.toFun w :=
  ⟨(0, 0), nonconstant_points_mem.1, (0, fun _ => (Real.pi : ℂ)),
    nonconstant_points_mem.2, nonconstant_input⟩

theorem exists_embedded_torus : ∃ p ∈ realSlice (initialData.limitDomain parameters),
    IsClosedEmbedding (initialData.torusEmbedding parameters p) := by
  obtain ⟨p, hp⟩ := result.nonempty
  exact ⟨p, hp, result.embedding p hp⟩

/-- 此 W6 实例 κ=1/2；一般 localKAM 的补集界仍使用任意满足初始条件的 κ。 -/
theorem small_complement : volume (initialData.localF2 parameters) <
    ENNReal.ofReal (1 / 2 : ℝ) * volume initialData.localPhase := result.small_complement

/-- 此 W6 实例 n=1；一般逆解析性定理保持维数 n 自由（满足初始条件，含 n>0）。
复逆在实目标附近解析，并在该点等于同一个全局实逆的复嵌入。
-/
theorem real_inverse_analytic {p : RealSpace 1}
    (hp : p ∈ realSlice (initialData.limitDomain parameters)) (Q : RealSpace 1) :
    AnalyticAt ℂ (initialData.complexAngleInverse parameters (complexify p)) (complexify Q) ∧
    initialData.complexAngleInverse parameters (complexify p) (complexify Q) =
      complexify (initialData.realAngleInverse parameters p Q) :=
  ⟨result.inverse_analytic p hp Q, initialData.complexAngleInverse_real_value parameters hp Q⟩

end KamProject.Arnold1963.Audit.W8Completion

open KamProject.Arnold1963 KamProject.Arnold1963.Iteration
#print axioms InitialData.limitFrequency_ball_subset
#print axioms InitialData.limitFrequency_injOn
#print axioms InitialData.frequencyLabel_left
#print axioms InitialData.unperturbedCenter_displacement
#print axioms InitialParameters.beta_width_budget
#print axioms InitialData.angleCorrection_derivative
#print axioms InitialData.orbit_eq_of_initial_eq
#print axioms InitialData.frequency_eq_of_orbit_eq
#print axioms InitialData.torusLimitMap_injOn
#print axioms InitialData.invariantTorus_disjoint
#print axioms InitialData.realAngleMap_bijective
#print axioms InitialData.complexAngleInverse_analytic_at_real
#print axioms InitialData.complexAngleInverse_real_value
#print axioms InitialData.torusLift_derivative_injective
#print axioms InitialData.torusEmbedding_isClosedEmbedding
#print axioms InitialData.torusAngleMap_bijective
#print axioms InitialData.torusCorrections_small
#print axioms InitialData.frequencyParameterization_eq
#print axioms InitialData.frequency_orbit
#print axioms InitialData.localF1_eq_frequency_union
#print axioms InitialData.localF2_volume_lt
#print axioms localKAM
#print axioms Audit.W8Completion.result
#print axioms Audit.W8Completion.nonconstant_input
#print axioms Audit.W8Completion.exists_embedded_torus
#print axioms Audit.W8Completion.real_inverse_analytic
#print axioms InitialData.localF1_compact
#print axioms InitialData.torusEmbedding_lift
#print axioms InitialData.local_partition
#print axioms InitialData.torusLimitMap_volume_gt
#print axioms Audit.W8Completion.nonconstant_on_initial_phase
