import KamProject.Arnold1963.Convergence.Composition
import KamProject.Arnold1963.Geometry.RealCover
import KamProject.Arnold1963.Geometry.RealJacobian

/-! 有限组合 S_s 在实相空间的导数界。
复空间和实覆盖均使用坐标最大范数。`restrictScalars` 保持同一映射的范数；
再限制到实坐标并取实部只需使用不增范数的估计，不假设两种限制的范数相等。
这里只处理有限组合，不断言极限映射在作用变量上可微。
-/
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

def complexifyPhaseCLM (n : ℕ) : RealPhaseCover n →L[ℝ] ComplexPhaseSpace n :=
  (complexifyCLM n).prodMap (complexifyCLM n)

def realPartPhaseCLM (n : ℕ) : ComplexPhaseSpace n →L[ℝ] RealPhaseCover n :=
  (realPartCLM n).prodMap (realPartCLM n)

@[simp] theorem complexifyPhaseCLM_apply {n} (x : RealPhaseCover n) :
    complexifyPhaseCLM n x = complexifyPhase x := rfl

@[simp] theorem realPartPhaseCLM_apply {n} (z : ComplexPhaseSpace n) :
    realPartPhaseCLM n z = realPartPhase z := rfl

@[simp] theorem norm_complexifyPhase {n} (x : RealPhaseCover n) :
    ‖complexifyPhase x‖ = ‖x‖ := by
  simp [complexifyPhase, Prod.norm_def]

theorem norm_realPartPhase_le {n} (z : ComplexPhaseSpace n) :
    ‖realPartPhase z‖ ≤ ‖z‖ :=
  max_le_max (norm_realPart_le z.1) (norm_realPart_le z.2)

def realPhaseRestriction {n} (f : ComplexPhaseSpace n → ComplexPhaseSpace n) :
    RealPhaseCover n → RealPhaseCover n := realPartPhase ∘ f ∘ complexifyPhase

def realPhaseDerivative {n} (L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n) :
    RealPhaseCover n →L[ℝ] RealPhaseCover n :=
  (realPartPhaseCLM n).comp ((L.restrictScalars ℝ).comp (complexifyPhaseCLM n))

theorem hasFDerivAt_realPhaseRestriction {n}
    {f : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : RealPhaseCover n}
    (hf : DifferentiableAt ℂ f (complexifyPhase x)) :
    HasFDerivAt (realPhaseRestriction f)
      (realPhaseDerivative (fderiv ℂ f (complexifyPhase x))) x :=
  (realPartPhaseCLM n).hasFDerivAt.comp x
    ((hf.hasFDerivAt.restrictScalars ℝ).comp x (complexifyPhaseCLM n).hasFDerivAt)

theorem norm_realPhaseDerivative_le {n}
    (L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n) :
    ‖realPhaseDerivative L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  exact (norm_realPartPhase_le _).trans (by simpa using L.le_opNorm (complexifyPhase x))

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- 实输入处取实部没有改变 S_s 的值：由每一步的共轭等变性保证。 -/
theorem cumulative_realPhase_value (s : ℕ) {x : RealPhaseCover n}
    (hx : complexifyPhase x ∈ h.phase b s) :
    complexifyPhase (realPhaseRestriction (h.cumulative b s) x) =
      h.cumulative b s (complexifyPhase x) := by
  apply complexifyPhase_realPartPhase_of_conj
  have hr := h.cumulative_real b s _ hx
  rw [conjPhase_complexifyPhase] at hr
  exact hr.symm

/-- 与复导数界相同的 2^s 实算子上界；没有欧氏范数换算常数。 -/
theorem cumulative_real_derivative (s : ℕ) {x : RealPhaseCover n}
    (hx : complexifyPhase x ∈ h.phase b s) :
    ‖fderiv ℝ (realPhaseRestriction (h.cumulative b s)) x‖ ≤ (2 : ℝ) ^ s := by
  rw [(hasFDerivAt_realPhaseRestriction
    (h.cumulative_analytic b s _ hx).differentiableAt).fderiv]
  exact (norm_realPhaseDerivative_le _).trans (h.cumulative_derivative b s _ hx)

end Iteration.InitialData
end KamProject.Arnold1963
