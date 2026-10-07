import KamProject.Arnold1963.Basic.Functions
import KamProject.Arnold1963.Basic.SymplecticMatrix
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Hamiltonian 向量场与正则变换（校订版 §2.1、§4.5）

使用复 Fréchet 导数，无复共轭梯度，坐标为 (p,q)，X_H=(-H_q,H_p)。
`fderiv` 是全函数：不可微点处有库约定的取值；任何微分／链式法则定理都
显式要求可微性，或由已有 AnalyticPhaseFunction 的解析性取得可微性。
`CanonicalOn` 只表明每一点的导数保持辛形式，不宣称 B 在整个域上单射。
本文件证明向量场的推前恒等式；ODE 存在性、环面下降和体积换元另行处理。
-/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

/-- 坐标导数候选值，不隐含可微性。不可微时 fderiv 按库约定为零；
数学上的偏导解释须使用 pGradient_eq_of_hasFDerivAt 或解析性证书。 -/
def pGradient {n : ℕ} (H : ComplexPhaseSpace n → ℂ) (x : ComplexPhaseSpace n) :
    ComplexSpace n := fun j => fderiv ℂ H x (pDirection j)

/-- 与 pGradient 相同的全函数约定；不会从定义自动获得可微性。 -/
def qGradient {n : ℕ} (H : ComplexPhaseSpace n → ℂ) (x : ComplexPhaseSpace n) :
    ComplexSpace n := fun j => fderiv ℂ H x (qDirection j)

/-- 可微性证书将候选值识别为真实导数在各坐标方向的取值。 -/
theorem pGradient_eq_of_hasFDerivAt {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) : pGradient H x = fun j => L (pDirection j) := by
  unfold pGradient
  rw [hH.fderiv]

theorem qGradient_eq_of_hasFDerivAt {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) : qGradient H x = fun j => L (qDirection j) := by
  unfold qGradient
  rw [hH.fderiv]

/-- 库约定的退化情况，仅用于揭示全函数语义，不能解释为偏导存在且为零。 -/
theorem pGradient_eq_zero_of_not_differentiableAt {n : ℕ}
    {H : ComplexPhaseSpace n → ℂ} {x : ComplexPhaseSpace n}
    (hH : ¬ DifferentiableAt ℂ H x) : pGradient H x = 0 := by
  ext j
  simp [pGradient, fderiv_zero_of_not_differentiableAt hH]

theorem qGradient_eq_zero_of_not_differentiableAt {n : ℕ}
    {H : ComplexPhaseSpace n → ℂ} {x : ComplexPhaseSpace n}
    (hH : ¬ DifferentiableAt ℂ H x) : qGradient H x = 0 := by
  ext j
  simp [qGradient, fderiv_zero_of_not_differentiableAt hH]

def hamiltonianVectorField {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ComplexPhaseSpace n :=
  (-qGradient H x, pGradient H x)

/-- Hamilton 方程使用 mathlib.J 作用于梯度；它与辛形式的矩阵相差负号。 -/
theorem hamiltonianVectorField_mathlibJ {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) :
    phaseCoordinate (hamiltonianVectorField H x) =
      (Matrix.J (Fin n) ℂ).mulVec (phaseCoordinate (pGradient H x, qGradient H x)) := by
  ext i
  cases i <;> simp [phaseCoordinate, hamiltonianVectorField, Matrix.J,
    Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem hamiltonianVectorField_eq_sharp {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) :
    hamiltonianVectorField H x = symplecticSharp (fderiv ℂ H x).toLinearMap := rfl

/-- 与上一阶段最大范数一致；右端是同一范数诱导的导数算子范数。 -/
theorem norm_hamiltonianVectorField_le {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ‖hamiltonianVectorField H x‖ ≤ ‖fderiv ℂ H x‖ := by
  rw [hamiltonianVectorField, phase_norm_eq, norm_neg, max_le_iff]
  constructor
  · apply (complex_norm_le_iff _ (norm_nonneg _)).2
    intro j
    change ‖fderiv ℂ H x (qDirection j)‖ ≤ ‖fderiv ℂ H x‖
    exact (fderiv ℂ H x).unit_le_opNorm (qDirection j) (by simp)
  · apply (complex_norm_le_iff _ (norm_nonneg _)).2
    intro j
    change ‖fderiv ℂ H x (pDirection j)‖ ≤ ‖fderiv ℂ H x‖
    exact (fderiv ℂ H x).unit_le_opNorm (pDirection j) (by simp)

/-- 仅依赖作用变量的可积 Hamiltonian：p 不动，q 以 ∂h/∂p 运动。 -/
theorem hamiltonianVectorField_actionOnly {n : ℕ} {h : ComplexSpace n → ℂ}
    (x : ComplexPhaseSpace n) (hh : DifferentiableAt ℂ h x.1) :
    hamiltonianVectorField (h ∘ Prod.fst) x =
      (0, fun j => fderiv ℂ h x.1 (Pi.single j 1)) := by
  have hd := hh.hasFDerivAt.comp x (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
  ext j <;> simp [hamiltonianVectorField, pGradient, qGradient, hd.fderiv,
    pDirection, qDirection]

/-- 后续分解 H=N+P 时使用；可微性明确列为假设。 -/
theorem hamiltonianVectorField_add {n : ℕ} {H K : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hH : DifferentiableAt ℂ H x)
    (hK : DifferentiableAt ℂ K x) :
    hamiltonianVectorField (H + K) x =
      hamiltonianVectorField H x + hamiltonianVectorField K x := by
  ext j <;> simp [hamiltonianVectorField, pGradient, qGradient,
    (hH.hasFDerivAt.add hK.hasFDerivAt).fderiv, add_comm]

/-- 给定真实导数证书后，向量场与该导数的辛对偶关系成立。 -/
theorem HasFDerivAt.symplectic_identity {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) (v : ComplexPhaseSpace n) :
    symplecticForm v (hamiltonianVectorField H x) = L v := by
  rw [hamiltonianVectorField_eq_sharp, hH.fderiv]
  exact symplecticForm_sharp L.toLinearMap v

theorem AnalyticPhaseFunction.hasFDerivAt {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain G ρ) : HasFDerivAt H.toFun (fderiv ℂ H.toFun x) x :=
  (H.analytic x hx).differentiableAt.hasFDerivAt

theorem AnalyticPhaseFunction.symplectic_identity {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain G ρ) (v : ComplexPhaseSpace n) :
    symplecticForm v (hamiltonianVectorField H.toFun x) = fderiv ℂ H.toFun x v :=
  HasFDerivAt.symplectic_identity (H.hasFDerivAt hx) v

/-- 环境空间导数保持辛形式；不使用仅相对于闭域的导数。 -/
def CanonicalAt {n : ℕ} (B : ComplexPhaseSpace n → ComplexPhaseSpace n)
    (x : ComplexPhaseSpace n) : Prop :=
  DifferentiableAt ℂ B x ∧ IsSymplecticLinear (fderiv ℂ B x).toLinearMap

def CanonicalOn {n : ℕ} (B : ComplexPhaseSpace n → ComplexPhaseSpace n)
    (S : Set (ComplexPhaseSpace n)) : Prop := ∀ x ∈ S, CanonicalAt B x

theorem canonicalAt_id {n : ℕ} (x : ComplexPhaseSpace n) : CanonicalAt id x := by
  refine ⟨differentiableAt_id, ?_⟩
  intro v w
  simp [fderiv_id]

theorem CanonicalAt.derivative_bijective {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) : Function.Bijective (fderiv ℂ B x) :=
  ⟨hB.2.injective, hB.2.surjective⟩

theorem CanonicalAt.matrix_identity {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) :
    (phaseLinearMatrix (fderiv ℂ B x).toLinearMap).transpose * symplecticMatrix n *
        phaseLinearMatrix (fderiv ℂ B x).toLinearMap = symplecticMatrix n :=
  hB.2.matrix_identity

theorem CanonicalAt.comp {n : ℕ}
    {B C : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B (C x)) (hC : CanonicalAt C x) : CanonicalAt (B ∘ C) x := by
  refine ⟨hB.1.comp x hC.1, ?_⟩
  rw [fderiv_comp x hB.1 hC.1]
  exact hB.2.comp hC.2

theorem CanonicalOn.comp {n : ℕ}
    {B C : ComplexPhaseSpace n → ComplexPhaseSpace n}
    {S T : Set (ComplexPhaseSpace n)} (hB : CanonicalOn B T)
    (hC : CanonicalOn C S) (hmap : Set.MapsTo C S T) : CanonicalOn (B ∘ C) S := by
  intro x hx
  exact (hB (C x) (hmap hx)).comp (hC x hx)

/-- 正确方向：DB(x) X_(H∘B)(x) = X_H(Bx)。 -/
theorem CanonicalAt.map_hamiltonianVectorField {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) {H : ComplexPhaseSpace n → ℂ}
    (hH : DifferentiableAt ℂ H (B x)) :
    fderiv ℂ B x (hamiltonianVectorField (H ∘ B) x) =
      hamiltonianVectorField H (B x) := by
  rw [hamiltonianVectorField_eq_sharp, hamiltonianVectorField_eq_sharp,
    fderiv_comp x hH hB.1]
  exact hB.2.map_sharp_comp (fderiv ℂ H (B x)).toLinearMap

/-- 与上一阶段函数对象及定义域直接对接，不额外假设输出存在性。 -/
theorem AnalyticPhaseFunction.canonical_pullback {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ)
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {S : Set (ComplexPhaseSpace n)}
    (hB : CanonicalOn B S) (hmap : Set.MapsTo B S (phaseDomain G ρ))
    {x : ComplexPhaseSpace n} (hx : x ∈ S) :
    fderiv ℂ B x (hamiltonianVectorField (H.toFun ∘ B) x) =
      hamiltonianVectorField H.toFun (B x) :=
  (hB x hx).map_hamiltonianVectorField (H.analytic (B x) (hmap hx)).differentiableAt

end KamProject.Arnold1963
