import KamProject.Arnold1963.Iteration.UniformBounds
import KamProject.Arnold1963.Step.InductiveIteration

/-! W6a 与 W5b 的直接衔接：自动提供统一 θ 下界，并核验下一步扰动参数。
本文件不声称已经对每一步构造出 IterationParameters。
-/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration

theorem remainder_eq_next_parameter {δ₁ : ℝ≥0} (hδ : 0 < δ₁) (n s : ℕ) :
    iterationRemainderBound n (perturbation n δ₁ s) (delta δ₁ s) (beta δ₁ s) =
      perturbation n δ₁ (s + 1) := remainder_eq_next hδ n s

theorem result_measure_uniform {n s : ℕ} {G Ωbase G₀ : Set (ComplexSpace n)}
    {A₀ g₀ : ComplexSpace n → ComplexSpace n} {ρ δ₁ θ₀ Θ₀ : ℝ≥0}
    {K N₀ D : ℝ} {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
    {g : ComplexSpace n → ComplexSpace n} (r : ResonanceDomainState n K N₀)
    (i : IterationInput (Ω := r.domain Ωbase) a f g
      (beta δ₁ s) (delta δ₁ s) (gamma n δ₁ s) (lower θ₀ δ₁ s) (upper Θ₀ δ₁ s)
      K (perturbation n δ₁ s))
    (c₀ : AnalyticFrequencyChart A₀ g₀ G₀ Ωbase)
    (hθ₀ : 0 < θ₀) (hδ₁ : δ₁ < 1 / 4)
    (hupper : ∀ p ∈ G₀, ‖fderiv ℂ A₀ p‖ ≤ (Θ₀ : ℝ))
    (hD : TypeD Ωbase D) (hN₀ : 1 ≤ N₀)
    (hNN : N₀ ≤ fundamentalCutoff (gamma n δ₁ s) (2 * perturbation n δ₁ s)) :
    realVolume (G \ i.result.domain) ≤ ENNReal.ofReal ((2 * (Θ₀ : ℝ) / θ₀) ^ n) *
      (ENNReal.ofReal (resonanceLossConstant n * D *
        (K * newShellBudget N₀ (fundamentalCutoff (gamma n δ₁ s) (2 * perturbation n δ₁ s)) +
          (((6 + 7 * upper Θ₀ δ₁ s) * beta δ₁ s : ℝ≥0) : ℝ) *
            (fundamentalCutoff (gamma n δ₁ s) (2 * perturbation n δ₁ s)) ^ n)) * realVolume G₀) :=
  i.result_measure_uniform r c₀ hθ₀ (lower_gt_half hθ₀ hδ₁ s).le Θ₀.coe_nonneg
    hupper hD hN₀ hNN

end KamProject.Arnold1963.Iteration
