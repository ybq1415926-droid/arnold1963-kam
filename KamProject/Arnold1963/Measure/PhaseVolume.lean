import KamProject.Arnold1963.Iteration.LimitDomain

/-! W6 保留作用域的物理相体积。这里的角基本区域长度为 2π，
不是 Fourier 平均使用的单位周期坐标。本文件估计源域，不断言 S_s 或 S∞ 的像保体积。
半开基本区域可计算体积，但不能直接用于需要紧集的 C4。
-/
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- 严格保留比例 (1−κ)，两侧相空间体积都包括相同的 (2π)^n 因子。 -/
theorem limit_physicalCell_volume_gt :
    ENNReal.ofReal (1 - κ) *
        realPhaseLebesgue n (realSlice h.domain ×ˢ realAngleCell n (2 * Real.pi)) <
      realPhaseLebesgue n (realSlice (h.limitDomain b) ×ˢ
        realAngleCell n (2 * Real.pi)) := by
  rw [realPhaseLebesgue_physicalCell, realPhaseLebesgue_physicalCell, ← mul_assoc]
  exact ENNReal.mul_lt_mul_left (by positivity) (by finiteness) (h.limit_volume_gt b)

end KamProject.Arnold1963.Iteration.InitialData
