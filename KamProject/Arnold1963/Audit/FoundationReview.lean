import KamProject.Arnold1963.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.DenselyOrdered

/-! 六项基础审查的边界实例与公理审计（2026-09-20）。 -/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963.Audit

-- 向量最大范数与 Fourier 指标的 ℓ¹ 长度不能互换。
example : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp
example : indexLength (fun _ : Fin 2 => (1 : ℤ)) = 2 := by simp [indexLength]
example (x : RealSpace 2) : ‖complexify x‖ = ‖x‖ := norm_complexify x

-- 同一全 1 矩阵：逐项最大范数为 1，作用于最大范数空间的算子范数至少为 2。
example : ‖(fun _ : Fin 2 => fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp

def duplicateSum : ComplexSpace 2 →L[ℂ] ComplexSpace 2 :=
  ContinuousLinearMap.pi (fun _ : Fin 2 =>
    (ContinuousLinearMap.proj 0 : ComplexSpace 2 →L[ℂ] ℂ) + ContinuousLinearMap.proj 1)

theorem two_le_duplicateSum_norm : (2 : ℝ) ≤ ‖duplicateSum‖ := by
  have h := duplicateSum.le_opNorm (fun _ => (1 : ℂ))
  have hv : ‖duplicateSum (fun _ => (1 : ℂ))‖ = 2 := by norm_num [duplicateSum]
  have hu : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp
  simpa only [hv, hu, mul_one] using h

-- 空域上的负上界被定义本身排除，零上界仍合法。
example : ¬ NormBoundOn (fun _ : ℝ => (0 : ℂ)) ∅ (-1) := by simp
example : NormBoundOn (fun _ : ℝ => (0 : ℂ)) ∅ 0 := by simp
example {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (H : AnalyticPhaseFunction n G ρ) :
    H.uniformNorm ≤ -1 ↔ NormBoundOn H.toFun (phaseDomain G ρ) (-1) := H.norm_le_iff

-- 论文所用有限维复空间确实满足紧邻域定理的实例要求。
example {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsCompact G) (r : ℝ≥0) :
    IsCompact (closedBallNeighborhood G r) := isCompact_closedBallNeighborhood hG r
example {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsCompact G) :
    IsCompact (realSlice G) := isCompact_realSlice hG
example {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsCompact G) :
    MeasurableSet (realSlice G) := measurableSet_realSlice_of_isCompact hG

/-- 正半径也不能让任意集合的闭球并自动成为闭集。 -/
theorem neighborhood_open_halfLine :
    closedBallNeighborhood (Set.Iio (0 : ℝ)) 1 = Set.Iio 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxy' : x - y ≤ 1 := (abs_le.mp (show |x - y| ≤ 1 from hxy)).2
    change y < 0 at hy
    change x < 1
    linarith
  · intro hx
    refine ⟨x - 1, ?_, ?_⟩
    · change x - 1 < 0
      change x < 1 at hx
      linarith
    · simp

theorem neighborhood_open_halfLine_not_closed :
    ¬ IsClosed (closedBallNeighborhood (Set.Iio (0 : ℝ)) 1) := by
  rw [neighborhood_open_halfLine]
  intro h
  have heq := h.closure_eq
  rw [closure_Iio] at heq
  have hmem : (1 : ℝ) ∈ Set.Iio (1 : ℝ) := heq ▸ (show (1 : ℝ) ∈ Set.Iic 1 by simp)
  exact (lt_irrefl (1 : ℝ)) hmem

-- 每个域中点的邻域解析性是库定义本身；不是后来增添的假设。
example {n : ℕ} (H : ComplexPhaseSpace n → ℂ) (S : Set (ComplexPhaseSpace n)) :
    AnalyticOnNhd ℂ H S ↔ ∀ x ∈ S, AnalyticAt ℂ H x := Iff.rfl

-- 真实偏导解释必须带导数证书。
example {n : ℕ} {H : ComplexPhaseSpace n → ℂ} {x : ComplexPhaseSpace n}
    {L : ComplexPhaseSpace n →L[ℂ] ℂ} (hH : HasFDerivAt H L x) (j : Fin n) :
    pGradient H x j = L (pDirection j) := by rw [pGradient_eq_of_hasFDerivAt hH]

#print axioms norm_complexify
#print axioms two_le_duplicateSum_norm
#print axioms isOpen_realSlice
#print axioms isClosed_realSlice
#print axioms isCompact_realSlice
#print axioms isClosed_closedBallNeighborhood
#print axioms isCompact_closedBallNeighborhood
#print axioms measurableSet_realSlice_of_isCompact
#print axioms normBoundOn_empty
#print axioms AnalyticPhaseFunction.norm_le_iff
#print axioms analyticOnNhd_iff_forall_analyticAt
#print axioms pGradient_eq_of_hasFDerivAt
#print axioms pGradient_eq_zero_of_not_differentiableAt
#print axioms neighborhood_open_halfLine_not_closed

end KamProject.Arnold1963.Audit
