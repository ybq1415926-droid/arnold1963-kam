import KamProject.Arnold1963.W6
import KamProject.Arnold1963.Geometry.NearIdentity

/-! W6a 声明及公理审计；所有例子均调用已经证明的实际接口。 -/
noncomputable section
open Set Filter
open scoped NNReal ENNReal Topology
namespace KamProject.Arnold1963.Audit.W6

example (n : ℕ) (M δ β : ℝ) :
    fundamentalRemainderBound n (2 * M) δ β = iterationRemainderBound n M δ β :=
  fundamentalRemainderBound_eq_iterationRemainderBound n M δ β

example : fundamentalRemainderBound 1 (2 * 1) 1 1 ≠
    4 * iterationRemainderBound 1 1 1 1 := by
  norm_num [fundamentalRemainderBound, iterationRemainderBound]

/-- 从原有 threshold5 得到 θ 下界，消除每一步额外的 θ₀/2 假设。 -/
theorem lower_bound_from_threshold {n : ℕ} {θ₀ δ₁ : ℝ≥0} {Θ ρ κ D : ℝ}
    (hθ : 0 < θ₀) (hδ : (δ₁ : ℝ) < threshold5 n θ₀ Θ ρ κ D) (s : ℕ) :
    (θ₀ : ℝ) / 2 < (Iteration.lower θ₀ δ₁ s : ℝ) :=
  Iteration.lower_gt_half hθ (Iteration.delta_initial_lt_quarter hδ) s

/-- W9a 关键库能力：一般可逆导数给出复多变量解析局部逆。
完整有限覆盖、紧片划分和统一常数仍属于 W9a。 -/
theorem localization_interface {n : ℕ} {A : ComplexSpace n → ComplexSpace n}
    {p : ComplexSpace n} (hA : AnalyticAt ℂ A p)
    (hD : Function.Bijective (fderiv ℂ A p)) :
    ∃ g : ComplexSpace n → ComplexSpace n, AnalyticAt ℂ g (A p) ∧ g (A p) = p ∧
      (∀ᶠ y in 𝓝 (A p), A (g y) = y) :=
  exists_analytic_local_inverse_of_isUnit hA (ContinuousLinearMap.isUnit_iff_bijective.mpr hD)

#check Iteration.gamma_initial_bounds
#check Iteration.lower_succ
#check Iteration.upper_succ
#check Iteration.width_succ
#check Iteration.result_measure_uniform
#check Iteration.limit_positive_of_budget
#print axioms fundamentalRemainderBound_eq_iterationRemainderBound
#print axioms Iteration.remainder_eq_next_parameter
#print axioms Iteration.decay_tsum_le
#print axioms Iteration.gamma_initial_bounds
#print axioms lower_bound_from_threshold
#print axioms Iteration.upper_lt_twice
#print axioms Iteration.width_gt_two_fifths
#print axioms Iteration.uniform_bounds_of_threshold
#print axioms Iteration.result_measure_uniform
#print axioms Iteration.finite_loss_le
#print axioms Iteration.limit_positive_of_budget
#print axioms InductiveResult.realSlice_nonempty_of_budget
#print axioms localization_interface

end KamProject.Arnold1963.Audit.W6
