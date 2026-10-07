import KamProject.Arnold1963.Iteration.NumericalConditions
import KamProject.Arnold1963.Iteration.StepInterface

/-! 真实归纳状态：包含当前 Hamiltonian、实际逆频率图、AR 历史及其共同作用域。
下一状态由既有 IterationInput.result 构造；不加入待证分析结论的假设。
-/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration

structure State (n : ℕ) (Ω₀ : Set (ComplexSpace n)) (δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0)
    (κ : ℝ) (s : ℕ) where
  domain : Set (ComplexSpace n)
  ar : ResonanceDomainState n (κ * (δ₁ : ℝ)) (previousCutoff n δ₁ s)
  integrable : ComplexSpace n → ℂ
  perturbation : AnalyticPhaseFunction n domain (width n ρ₀ δ₁ s)
  inverseFrequency : ComplexSpace n → ComplexSpace n
  input : IterationInput (Ω := ar.domain Ω₀) integrable perturbation inverseFrequency
    (beta δ₁ s) (delta δ₁ s) (gamma n δ₁ s) (lower θ₀ δ₁ s) (upper Θ₀ δ₁ s)
    (κ * (δ₁ : ℝ)) (Iteration.perturbation n δ₁ s)

namespace State
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ} {s : ℕ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (z : State n Ω₀ δ₁ θ₀ Θ₀ ρ₀ κ s)

def step := z.input.result

def nextPerturbation : AnalyticPhaseFunction n z.step.domain (width n ρ₀ δ₁ (s + 1)) :=
  z.step.perturbation.restrict (Subset.refl _) (by rw [width_succ]) z.step.chart.domain_conj

include b in
theorem nextPerturbation_bound : z.nextPerturbation.uniformNorm <
    Iteration.perturbation n δ₁ (s + 1) := by
  have hh := (z.step.perturbation.uniformNorm_restrict_le (Subset.refl _)
    (show width n ρ₀ δ₁ (s + 1) ≤ width n ρ₀ δ₁ s - 3 * gamma n δ₁ s by rw [width_succ])
    z.step.chart.domain_conj).trans_lt z.step.bound
  exact hh.trans_eq (remainder_eq_next_parameter b.delta_pos n s)

def nextAR : ResonanceDomainState n (κ * (δ₁ : ℝ)) (previousCutoff n δ₁ (s + 1)) :=
  z.ar.next b.divisor_pos (b.cutoff_step_le s) ((5 + 7 * upper Θ₀ δ₁ s) * beta δ₁ s)

theorem nextInput : IterationInput (Ω := (z.nextAR b).domain Ω₀)
    (z.perturbation.averagedHamiltonian z.integrable) z.nextPerturbation z.step.inverseFrequency
    (beta δ₁ (s + 1)) (delta δ₁ (s + 1)) (gamma n δ₁ (s + 1))
    (lower θ₀ δ₁ (s + 1)) (upper Θ₀ δ₁ (s + 1))
    (κ * (δ₁ : ℝ)) (Iteration.perturbation n δ₁ (s + 1)) where
  chart := z.input.result_chart_next z.ar (b.cutoff_step_le s)
  analytic := z.step.analytic
  conj := z.step.conj
  lower := by
    intro p hp v
    rw [lower_succ]
    simpa only [NNReal.coe_mul, NNReal.coe_sub (b.parameters s).delta_lt_one.le,
      NNReal.coe_one] using (z.step.derivative_bounds p hp v).1
  upper := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [upper_succ]
    simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one] using
      (z.step.derivative_bounds p hp v).2
  perturbation := (z.nextPerturbation_bound b).le
  budget := b.parameters (s + 1)

def next : State n Ω₀ δ₁ θ₀ Θ₀ ρ₀ κ (s + 1) where
  domain := z.step.domain
  ar := z.nextAR b
  integrable := z.perturbation.averagedHamiltonian z.integrable
  perturbation := z.nextPerturbation
  inverseFrequency := z.step.inverseFrequency
  input := z.nextInput b

theorem next_domain_subset : (z.next b).domain ⊆ erosion z.domain (beta δ₁ s) :=
  z.step.domain_subset

/-- 真实旧 Hamiltonian 经真实 B 拉回，等于下一状态的真实 Hamiltonian。 -/
theorem next_identity (x : ComplexPhaseSpace n) :
    z.integrable (z.step.transformation.toFun x).1 +
      z.perturbation.toFun (z.step.transformation.toFun x) =
      (z.next b).integrable x.1 + (z.next b).perturbation.toFun x := z.step.identity x

end State
end KamProject.Arnold1963.Iteration
