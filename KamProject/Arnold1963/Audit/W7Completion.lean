import KamProject.Arnold1963.W7
import KamProject.Arnold1963.Audit.W6Example

/-! W7 → W8 交接审计：实际非恒定扰动同时满足联合角解析与周期大测度像。
不以独立假设或零扰动替代任何一个结论。
W6Completion.parameters 的类型固定 n=1、ρ₀=1、κ=1/2；这是具体样例，
一般接口仍为 InitialData.limitMap_angle_analytic 和 InitialData.torusLimitMap_volume_gt。
InitialParameters 的这些值是类型参数，不是 parameters.ρ₀ 等结构字段。
本轮 15 条公理的实际输出见 Audit/w7-volume-review-20261002-completion-output.txt。
-/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W7Completion
open Iteration W6Completion
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- 反馈中的 ENNReal 幂相容性，直接调用 mathlib。 -/
example (n : ℕ) : ENNReal.ofReal ((2 * Real.pi) ^ n) =
    ENNReal.ofReal (2 * Real.pi) ^ n := ENNReal.ofReal_pow (by positivity) n

/-- 使用 AddCircle 的默认 volume，总质量为 2π。 -/
example : volume (univ : Set (AddCircle (2 * Real.pi))) = ENNReal.ofReal (2 * Real.pi) :=
  AddCircle.measure_univ _

/-- 半开角盒要求每个坐标严格大于零；定义是逐坐标 Ioc 的乘积。 -/
example {n : ℕ} (q : RealSpace n) : q ∈ realAngleCell n (2 * Real.pi) ↔
    ∀ j, 0 < q j ∧ q j ≤ 2 * Real.pi := by simp [realAngleCell]

/-- 此样例 ρ₀=1，因此公共开角带的宽度为 1/3。 -/
theorem joint_analytic {p : ComplexSpace 1} (hp : p ∈ initialData.limitDomain parameters) :
    AnalyticOnNhd ℂ (fun q => initialData.limitMap parameters (p, q))
      (InitialData.commonAngleStrip 1 1) :=
  initialData.limitMap_angle_analytic parameters hp

/-- 此样例 κ=1/2；一般大测度定理并没有固定 κ。 -/
theorem actual_large_image :
    ENNReal.ofReal (1 - (1 / 2 : ℝ)) * volume
      (realSlice initialData.domain ×ˢ (univ : Set (RealTorus 1))) <
    volume (initialData.torusLimitMap parameters ''
      (realSlice (initialData.limitDomain parameters) ×ˢ (univ : Set (RealTorus 1)))) :=
  initialData.torusLimitMap_volume_gt parameters

/-- 参数和输入均直接使用 W6Example；s 是论文组合 S_s 的状态编号，S₀=id。 -/
theorem finite_volume (s : ℕ) :
    volume ((torusProjection ∘ initialData.realCumulative parameters s) ''
      initialData.retainedCell parameters) = volume (initialData.retainedCell parameters) :=
  initialData.cumulative_torus_volume parameters s

example : IsCompact (initialData.torusLimitMap parameters ''
    (realSlice (initialData.limitDomain parameters) ×ˢ (univ : Set (RealTorus 1)))) :=
  initialData.torusLimitMap_image_compact parameters

end KamProject.Arnold1963.Audit.W7Completion

open KamProject.Arnold1963 Iteration
#check Audit.W6Completion.parameters
#check ENNReal.ofReal_pow
#check AddCircle.measure_univ
#check realPhaseLebesgue_physicalCell
#check InitialData.limit_physicalCell_volume_gt
#check InitialData.limit_volume_gt
#check InitialData.limitMap_angle_analytic
#check InitialData.cumulative_real_det
#check InitialData.cumulative_real_volume
#check InitialData.cumulative_torus_volume
#check InitialData.torusLimitMap_volume_ge
#check InitialData.torusLimitMap_volume_gt
#print axioms polydisc_cauchy
#print axioms analyticAt_cauchyIntegral
#print axioms analyticOnNhd_uniform_limit
#print axioms InitialData.limitMap_angle_analytic
#print axioms realPhase_det_eq_one
#print axioms InitialData.cumulative_real_det
#print axioms InitialData.cumulative_real_volume
#print axioms torusProjection_volume
#print axioms InitialData.cumulative_torus_volume
#print axioms InitialData.torusLimitMap_image_compact
#print axioms InitialData.torusLimitMap_volume_ge
#print axioms InitialData.torusLimitMap_volume_gt
#print axioms Audit.W7Completion.joint_analytic
#print axioms Audit.W7Completion.actual_large_image
#print axioms Audit.W7Completion.finite_volume
