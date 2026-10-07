import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Isometry

/-!
# 公共空间与两种范数（校订版 §4.5）

`RealSpace n`、`ComplexSpace n` 使用 mathlib 有限乘积的最大范数。
`ComplexPhaseSpace n` 的坐标顺序固定为 `(p, q)`，乘积范数仍为最大范数。
`FourierIndex n` 的默认范数不能用作论文的指标长度；必须使用 `indexLength`。
这些基础定义允许 n = 0；KAM 定理本身将另外要求 0 < n。
不新增或替换任何全局范数实例，不使用 EuclideanSpace。
复数标量使用复模；函数使用域上一致范数；连续线性映射使用上述最大范数诱导的
算子范数。普通 Matrix 的逐项最大范数不能当成该算子范数，换算须另证维数因子。
-/

noncomputable section

namespace KamProject.Arnold1963

abbrev RealSpace (n : ℕ) := Fin n → ℝ
abbrev ComplexSpace (n : ℕ) := Fin n → ℂ
abbrev FourierIndex (n : ℕ) := Fin n → ℤ
abbrev ComplexPhaseSpace (n : ℕ) := ComplexSpace n × ComplexSpace n

/-- 实向量逐坐标嵌入复空间。 -/
def complexify {n : ℕ} (x : RealSpace n) : ComplexSpace n := fun j => (x j : ℂ)

@[simp] theorem complexify_zero {n : ℕ} : complexify (0 : RealSpace n) = 0 := by
  ext j
  simp [complexify]

theorem isometry_complexify (n : ℕ) : Isometry (complexify (n := n)) :=
  Isometry.piMap (fun _ : Fin n => ((↑) : ℝ → ℂ)) (fun _ => Complex.isometry_ofReal)

theorem continuous_complexify (n : ℕ) : Continuous (complexify (n := n)) :=
  (isometry_complexify n).continuous

/-- 逐坐标复共轭。 -/
def conjVec {n : ℕ} (z : ComplexSpace n) : ComplexSpace n := fun j => star (z j)

def realPart {n : ℕ} (z : ComplexSpace n) : RealSpace n := fun j => (z j).re
def imagPart {n : ℕ} (z : ComplexSpace n) : RealSpace n := fun j => (z j).im

def conjPhase {n : ℕ} (z : ComplexPhaseSpace n) : ComplexPhaseSpace n :=
  (conjVec z.1, conjVec z.2)

/-- Fourier 指标的 ℓ¹ 长度，值域取 ℝ 以便后续实指数估计。 -/
def indexLength {n : ℕ} (k : FourierIndex n) : ℝ := ∑ j, |(k j : ℝ)|

/-- 双线性配对 Σ kⱼzⱼ；这里没有 Hermitian 内积中的复共轭。 -/
def indexPairing {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) : ℂ :=
  ∑ j, (k j : ℂ) * z j

theorem complex_norm_le_iff {n : ℕ} (z : ComplexSpace n) {r : ℝ} (hr : 0 ≤ r) :
    ‖z‖ ≤ r ↔ ∀ j, ‖z j‖ ≤ r :=
  pi_norm_le_iff_of_nonneg hr

theorem real_norm_le_iff {n : ℕ} (x : RealSpace n) {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ ∀ j, |x j| ≤ r := by
  simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hr (x := x))

/-- 实复嵌入保持原最大范数，不发生 ℓ² 范数替换。 -/
@[simp] theorem norm_complexify {n : ℕ} (x : RealSpace n) : ‖complexify x‖ = ‖x‖ := by
  simpa only [complexify_zero, dist_zero_right] using (isometry_complexify n).dist_eq x 0

theorem complex_coordinate_norm_le {n : ℕ} (z : ComplexSpace n) (j : Fin n) :
    ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j

theorem phase_norm_eq {n : ℕ} (z : ComplexPhaseSpace n) :
    ‖z‖ = max ‖z.1‖ ‖z.2‖ := rfl

@[simp] theorem realPart_complexify {n : ℕ} (x : RealSpace n) :
    realPart (complexify x) = x := by
  funext j
  simp [realPart, complexify]

@[simp] theorem imagPart_complexify {n : ℕ} (x : RealSpace n) :
    imagPart (complexify x) = 0 := by
  funext j
  simp [imagPart, complexify]

@[simp] theorem conjVec_complexify {n : ℕ} (x : RealSpace n) :
    conjVec (complexify x) = complexify x := by
  funext j
  simp [conjVec, complexify]

@[simp] theorem conjVec_conjVec {n : ℕ} (z : ComplexSpace n) :
    conjVec (conjVec z) = z := by
  funext j
  simp [conjVec]

theorem indexLength_nonneg {n : ℕ} (k : FourierIndex n) : 0 ≤ indexLength k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- 连接空间最大范数与 Fourier 指标 ℓ¹ 长度的关键估计。 -/
theorem norm_indexPairing_le {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) :
    ‖indexPairing k z‖ ≤ indexLength k * ‖z‖ := by
  calc
    ‖indexPairing k z‖ ≤ ∑ j, ‖(k j : ℂ) * z j‖ := norm_sum_le _ _
    _ = ∑ j, |(k j : ℝ)| * ‖z j‖ := by simp [Complex.norm_intCast]
    _ ≤ ∑ j, |(k j : ℝ)| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (complex_coordinate_norm_le z j) (abs_nonneg _)
    _ = indexLength k * ‖z‖ := by rw [indexLength, Finset.sum_mul]

end KamProject.Arnold1963
