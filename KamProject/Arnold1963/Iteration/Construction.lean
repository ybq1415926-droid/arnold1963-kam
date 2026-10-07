import KamProject.Arnold1963.Iteration.State

/-! 原文初始数据到所有自然数阶段的实际递归。状态 s 的扰动由初始扰动逐次构造。
初始阶段没有预设变换、好集或后续 Hamiltonian。
-/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration

structure InitialData (n : ℕ) (Ω₀ : Set (ComplexSpace n)) (δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0)
    (D : ℝ) where
  domain : Set (ComplexSpace n)
  integrable : ComplexSpace n → ℂ
  perturbation : AnalyticPhaseFunction n domain ρ₀
  inverseFrequency : ComplexSpace n → ComplexSpace n
  chart : AnalyticFrequencyChart (actionFrequency integrable) inverseFrequency domain Ω₀
  analytic : AnalyticOnNhd ℂ integrable domain
  conj : ∀ p ∈ domain, integrable (conjVec p) = star (integrable p)
  lower : ∀ p ∈ domain, ∀ v, (θ₀ : ℝ) * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency integrable) p v‖
  upper : ∀ p ∈ domain, ‖fderiv ℂ (actionFrequency integrable) p‖ ≤ Θ₀
  bound : perturbation.uniformNorm ≤ Iteration.perturbation n δ₁ 0
  typeD : TypeD Ω₀ D

namespace InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- 初始作用体积正性由真实频率图的换元上界和 Ω₀ 的 D 型正体积推出。 -/
theorem volume_pos : 0 < realVolume h.domain := by
  by_contra hn
  have hz : realVolume h.domain = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hh := h.chart.realVolume_image_le Θ₀.coe_nonneg h.upper
  rw [hz, mul_zero] at hh
  exact not_lt_of_ge hh h.typeD.volume_pos

/-- 初始实截面紧，因此 Lebesgue 体积有限；不再要求调用者重复提供证书。 -/
theorem volume_finite : realVolume h.domain ≠ ⊤ := by
  change MeasureTheory.volume (realSlice h.domain) ≠ ⊤
  exact (isCompact_realSlice h.chart.compact).measure_ne_top

def initialState : State n Ω₀ δ₁ θ₀ Θ₀ ρ₀ κ 0 where
  domain := h.domain
  ar := ResonanceDomainState.initial n (κ * (δ₁ : ℝ))
  integrable := h.integrable
  perturbation := h.perturbation.restrict (Subset.refl _) (by simp) h.chart.domain_conj
  inverseFrequency := h.inverseFrequency
  input := {
    chart := by
      dsimp only [previousCutoff]
      rw [ResonanceDomainState.initial_domain]
      exact h.chart
    analytic := h.analytic
    conj := h.conj
    lower := by simpa only [lower_zero] using h.lower
    upper := by simpa only [upper_zero] using h.upper
    perturbation := (h.perturbation.uniformNorm_restrict_le _ _ _).trans h.bound
    budget := b.parameters 0 }

def state : (s : ℕ) → State n Ω₀ δ₁ θ₀ Θ₀ ρ₀ κ s
  | 0 => h.initialState b
  | s + 1 => (state s).next b

@[simp] theorem state_zero : h.state b 0 = h.initialState b := rfl
theorem state_succ (s : ℕ) : h.state b (s + 1) = (h.state b s).next b := rfl

def actionDomain (s : ℕ) : Set (ComplexSpace n) := (h.state b s).domain
def phase (s : ℕ) : Set (ComplexPhaseSpace n) := phaseDomain (h.actionDomain b s) (width n ρ₀ δ₁ s)
def hamiltonian (s : ℕ) (z : ComplexPhaseSpace n) : ℂ :=
  (h.state b s).integrable z.1 + (h.state b s).perturbation.toFun z

/-- B 的索引 s 表示从状态 s+1 到状态 s 的第 s+1 个变换。 -/
def transformation (s : ℕ) : AnalyticCanonicalTransformation
    (h.phase b (s + 1)) (h.phase b s) (beta δ₁ s) :=
  (h.state b s).step.transformation.restrict (by
    simp only [phase, actionDomain, state_succ, State.next, width_succ]
    exact Subset.refl _)

theorem domain_zero : h.actionDomain b 0 = h.domain := rfl

theorem domain_step_subset (s : ℕ) :
    h.actionDomain b (s + 1) ⊆ erosion (h.actionDomain b s) (beta δ₁ s) :=
  (h.state b s).next_domain_subset b

theorem domain_antitone : Antitone (h.actionDomain b) :=
  antitone_nat_of_succ_le (fun s => (h.domain_step_subset b s).trans (erosion_subset _ _))

theorem domain_compact (s : ℕ) : IsCompact (h.actionDomain b s) := (h.state b s).input.chart.compact

theorem perturbation_bound (s : ℕ) :
    (h.state b (s + 1)).perturbation.uniformNorm < Iteration.perturbation n δ₁ (s + 1) :=
  (h.state b s).nextPerturbation_bound b

theorem step_identity (s : ℕ) (z : ComplexPhaseSpace n) :
    h.hamiltonian b s ((h.transformation b s).toFun z) = h.hamiltonian b (s + 1) z := by
  exact (h.state b s).next_identity b z

/-- S_s=B₁∘…∘B_s，次序与原文一致。 -/
def cumulative : ℕ → ComplexPhaseSpace n → ComplexPhaseSpace n
  | 0 => id
  | s + 1 => cumulative s ∘ (h.transformation b s).toFun

theorem cumulative_maps (s : ℕ) : MapsTo (h.cumulative b s) (h.phase b s) (h.phase b 0) := by
  induction s with
  | zero => exact fun _ hx => hx
  | succ s ih => exact ih.comp (h.transformation b s).mapsTo

theorem cumulative_identity (s : ℕ) (z : ComplexPhaseSpace n) :
    h.hamiltonian b 0 (h.cumulative b s z) = h.hamiltonian b s z := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih =>
    change h.hamiltonian b 0 (h.cumulative b s ((h.transformation b s).toFun z)) = _
    rw [ih, h.step_identity]

end InitialData
end KamProject.Arnold1963.Iteration
