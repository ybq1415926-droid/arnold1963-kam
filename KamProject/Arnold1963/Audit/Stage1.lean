import KamProject.Arnold1963.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FinCases

/-!
# 阶段 1 的语义校准与衔接验证

实际计算 H=p₀²/2 与 H=q₀ 的向量场，并检查非恒等的辛旋转。
这些实例同时固定 (p,q) 坐标顺序、Hamilton 方程符号、矩阵 J 的符号。
另用上一阶段的 AnalyticPhaseFunction 直接调用新的解析／正则变换接口。
-/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963.Audit

theorem quadratic_action_field (x : ComplexPhaseSpace 1) :
    hamiltonianVectorField (fun z : ComplexPhaseSpace 1 => z.1 0 * z.1 0 / 2) x =
      (0, x.1) := by
  have hp := (hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 1) x.1).comp x
    (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
  have hd := (hp.mul hp).mul_const (2 : ℂ)⁻¹
  change HasFDerivAt (fun z : ComplexPhaseSpace 1 => z.1 0 * z.1 0 / 2) _ x at hd
  ext j <;> fin_cases j <;>
    simp [hamiltonianVectorField, pGradient, qGradient, hd.fderiv,
      pDirection, qDirection]
  ring

theorem angle_coordinate_field (x : ComplexPhaseSpace 1) :
    hamiltonianVectorField (fun z : ComplexPhaseSpace 1 => z.2 0) x =
      (-Pi.single 0 1, 0) := by
  have hd := (hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 1) x.2).comp x
    (hasFDerivAt_snd (𝕜 := ℂ) (p := x))
  change HasFDerivAt (fun z : ComplexPhaseSpace 1 => z.2 0) _ x at hd
  ext j <;> fin_cases j <;>
    simp [hamiltonianVectorField, pGradient, qGradient, hd.fderiv,
      pDirection, qDirection]

/-- 覆盖空间上的辛旋转；不声称它下降为周期角空间上的映射。 -/
theorem canonical_rotation {n : ℕ} (x : ComplexPhaseSpace n) :
    CanonicalAt (fun z : ComplexPhaseSpace n => (z.2, -z.1)) x := by
  have hd := (hasFDerivAt_snd (𝕜 := ℂ) (p := x)).prodMk
    (hasFDerivAt_fst (𝕜 := ℂ) (p := x)).neg
  change HasFDerivAt (fun z : ComplexPhaseSpace n => (z.2, -z.1)) _ x at hd
  refine ⟨hd.differentiableAt, ?_⟩
  intro v w
  rw [hd.fderiv]
  change symplecticForm (v.2, -v.1) (w.2, -w.1) = symplecticForm v w
  unfold symplecticForm
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.neg_apply]
  ring

example : symplecticMatrix 1 (.inl 0) (.inr 0) = 1 := by simp
example : symplecticMatrix 1 (.inr 0) (.inl 0) = -1 := by simp

/-- 旧定义的解析性在闭域边界处也能提供环境导数。 -/
example {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (H : AnalyticPhaseFunction n G ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain G ρ) (v : ComplexPhaseSpace n) :
    symplecticForm v (hamiltonianVectorField H.toFun x) = fderiv ℂ H.toFun x v :=
  H.symplectic_identity hx v

/-- 泛型集成检查：带原定义域的函数直接接入正则拉回公式。 -/
example {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (H : AnalyticPhaseFunction n G ρ) {B : ComplexPhaseSpace n → ComplexPhaseSpace n}
    {S : Set (ComplexPhaseSpace n)} (hB : CanonicalOn B S)
    (hmap : Set.MapsTo B S (phaseDomain G ρ)) {x : ComplexPhaseSpace n} (hx : x ∈ S) :
    fderiv ℂ B x (hamiltonianVectorField (H.toFun ∘ B) x) =
      hamiltonianVectorField H.toFun (B x) :=
  H.canonical_pullback hB hmap hx

#print axioms symplecticForm_ext_right
#print axioms symplecticForm_sharp
#print axioms IsSymplecticLinear.map_sharp_comp
#print axioms norm_hamiltonianVectorField_le
#print axioms hamiltonianVectorField_actionOnly
#print axioms hamiltonianVectorField_add
#print axioms CanonicalAt.derivative_bijective
#print axioms CanonicalAt.matrix_identity
#print axioms CanonicalOn.comp
#print axioms AnalyticPhaseFunction.canonical_pullback
#print axioms quadratic_action_field
#print axioms angle_coordinate_field
#print axioms canonical_rotation

end KamProject.Arnold1963.Audit
