import KamProject.Arnold1963.Geometry.HamiltonianLocalization
import Mathlib.MeasureTheory.Measure.Regular

/-! 原始非退化资料的有限局部覆盖。损失按初始作用体积计量。
所得有限覆盖可能重叠；这里不把它误写成不交分解。
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace KamProject.Arnold1963

/-- 原文有界作用域的闭域实现。实截面由非空开集取闭包，边界零测，
实内点处有复邻域。没有频率全局单射、局部逆、好集或体积正性字段。
`nondegenerate` 只在将被覆盖的实开集上要求 Hessian 非退化。
-/
structure GlobalHamiltonianData (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) : Type where
  dimension_pos : 0 < n
  compact : IsCompact ambient
  domain_conj : ConjInvariant ambient
  analytic : AnalyticOnNhd ℂ H₀ ambient
  conj : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p)
  realOpen : Set (RealSpace n)
  isOpen_realOpen : IsOpen realOpen
  nonempty_realOpen : realOpen.Nonempty
  closure_realOpen : closure realOpen = realSlice ambient
  boundary_null : volume (frontier realOpen) = 0
  complex_interior : ∀ p ∈ realOpen, complexify p ∈ interior ambient
  nondegenerate : ∀ p ∈ realOpen, hessianDet H₀ (complexify p) ≠ 0

namespace GlobalHamiltonianData
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  (h : GlobalHamiltonianData n H₀ ambient)
include h

theorem realOpen_subset : h.realOpen ⊆ realSlice ambient :=
  h.closure_realOpen ▸ subset_closure

theorem volume_finite : volume (realSlice ambient) ≠ ⊤ :=
  (isCompact_realSlice h.compact).measure_ne_top

theorem volume_pos : 0 < volume (realSlice ambient) :=
  (h.isOpen_realOpen.measure_pos volume h.nonempty_realOpen).trans_le
    (measure_mono h.realOpen_subset)

theorem real_boundary_null : volume (realSlice ambient \ h.realOpen) = 0 := by
  simpa only [frontier, h.isOpen_realOpen.interior_eq, h.closure_realOpen] using h.boundary_null

/-- 覆盖和误差预算均从原始资料构造；ε 是真实相对误差，不是绝对体积。 -/
theorem exists_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (HamiltonianPatch n H₀ ambient),
      volume (realSlice ambient \ ⋃ c ∈ s, realSlice c.domain) <
        ENNReal.ofReal ε * volume (realSlice ambient) := by
  have hεV : ENNReal.ofReal ε * volume (realSlice ambient) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hε).ne' h.volume_pos.ne'
  obtain ⟨K, hKU, hK, hVK⟩ := h.isOpen_realOpen.measurableSet.exists_isCompact_sdiff_lt
    (ne_top_of_le_ne_top h.volume_finite (measure_mono h.realOpen_subset)) hεV
  obtain ⟨s, hs⟩ := HamiltonianPatch.exists_finite_cover hK
    (fun p hp => h.complex_interior p (hKU hp)) h.analytic h.conj
    (fun p hp => h.nondegenerate p (hKU hp))
  refine ⟨s, lt_of_le_of_lt ?_ hVK⟩
  calc
    volume (realSlice ambient \ ⋃ c ∈ s, realSlice c.domain) ≤
        volume ((realSlice ambient \ h.realOpen) ∪ (h.realOpen \ K)) := measure_mono (by
      intro p hp
      by_cases hpU : p ∈ h.realOpen
      · refine Or.inr ⟨hpU, ?_⟩
        intro hpK
        obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hs hpK)
        exact hp.2 (mem_iUnion₂.mpr ⟨c, hc,
          (show complexify p ∈ c.domain from interior_subset hpc)⟩)
      · exact Or.inl ⟨hp.1, hpU⟩)
    _ ≤ volume (realSlice ambient \ h.realOpen) + volume (h.realOpen \ K) := measure_union_le _ _
    _ = volume (h.realOpen \ K) := by rw [h.real_boundary_null, zero_add]

end GlobalHamiltonianData
end KamProject.Arnold1963
