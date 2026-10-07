import KamProject.Arnold1963.Basic.Spaces
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# 闭球邻域、侵蚀、复角带与实截面（校订版 §4.5）

半径使用 ℝ≥0，排除负半径导致的空球／真空假设。
`closedBallNeighborhood U r` 是实际闭球的并，不是先取 U 的闭包。
因此在任意集合上半径为零时仍等于 U；不声称任意 U 的这种邻域都闭。
论文所用 U 是紧集：下面给出此时与 Metric.cthickening 的等价及闭性，
在 ProperSpace（包括本项目有限维实／复空间）中还证明紧性。
复空间中的球使用最大模范数；实截面是拉回到 ℝⁿ 的集合。
角带在复覆盖空间上定义，其实部无界，不能把它当作紧集。
-/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

section MetricDomains

variable {E : Type*} [MetricSpace E]

/-- U + r：存在 U 内的中心，点到中心的距离不超过 r。 -/
def closedBallNeighborhood (U : Set E) (r : ℝ≥0) : Set E :=
  {x | ∃ y ∈ U, dist x y ≤ (r : ℝ)}

/-- U − r：以该点为中心的整个闭 r 球仍包含在 U 中。 -/
def erosion (U : Set E) (r : ℝ≥0) : Set E :=
  {x | Metric.closedBall x (r : ℝ) ⊆ U}

@[simp] theorem erosion_zero (U : Set E) : erosion U 0 = U := by
  ext x
  simp [erosion]

@[simp] theorem closedBallNeighborhood_zero (U : Set E) :
    closedBallNeighborhood U 0 = U := by
  ext x
  simp [closedBallNeighborhood]

theorem erosion_subset (U : Set E) (r : ℝ≥0) : erosion U r ⊆ U := by
  intro x hx
  exact hx (Metric.mem_closedBall_self r.coe_nonneg)

theorem subset_closedBallNeighborhood (U : Set E) (r : ℝ≥0) :
    U ⊆ closedBallNeighborhood U r := by
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem erosion_mono {U V : Set E} (hUV : U ⊆ V) (r : ℝ≥0) :
    erosion U r ⊆ erosion V r := by
  intro x hx y hy
  exact hUV (hx hy)

theorem erosion_antitone_radius (U : Set E) {r s : ℝ≥0} (hrs : r ≤ s) :
    erosion U s ⊆ erosion U r := by
  intro x hx y hy
  apply hx
  exact le_trans hy (show (r : ℝ) ≤ (s : ℝ) from hrs)

theorem erosion_inter (U V : Set E) (r : ℝ≥0) :
    erosion (U ∩ V) r = erosion U r ∩ erosion V r := by
  ext x
  simp only [erosion, Set.mem_ofPred_eq, Set.subset_inter_iff, Set.mem_inter_iff]

/-- 侵蚀点周围的闭球确实位于原域，供后续 Cauchy／线段估计使用。 -/
theorem mem_of_mem_erosion {U : Set E} {r : ℝ≥0} {x y : E}
    (hx : x ∈ erosion U r) (hxy : dist y x ≤ (r : ℝ)) : y ∈ U :=
  hx hxy

end MetricDomains

section CompactDomains

variable {E : Type*} [MetricSpace E] {U : Set E}

/-- 紧集上，闭球并就是 mathlib 的闭增厚；不对任意集合强加闭包。 -/
theorem closedBallNeighborhood_eq_cthickening_of_isCompact (hU : IsCompact U)
    (r : ℝ≥0) : closedBallNeighborhood U r = Metric.cthickening (r : ℝ) U := by
  rw [hU.cthickening_eq_biUnion_closedBall r.coe_nonneg]
  ext x
  simp [closedBallNeighborhood, Metric.mem_closedBall]

theorem isClosed_closedBallNeighborhood_of_isCompact (hU : IsCompact U) (r : ℝ≥0) :
    IsClosed (closedBallNeighborhood U r) := by
  rw [closedBallNeighborhood_eq_cthickening_of_isCompact hU]
  exact Metric.isClosed_cthickening

theorem isCompact_closedBallNeighborhood [ProperSpace E] (hU : IsCompact U)
    (r : ℝ≥0) : IsCompact (closedBallNeighborhood U r) := by
  rw [closedBallNeighborhood_eq_cthickening_of_isCompact hU]
  exact hU.cthickening

/-- 有限维空间中甚至只需 U 闭；一般度量空间不能省略 ProperSpace 前提。 -/
theorem isClosed_closedBallNeighborhood [ProperSpace E] (hU : IsClosed U) (r : ℝ≥0) :
    IsClosed (closedBallNeighborhood U r) := by
  have heq : closedBallNeighborhood U r = Metric.cthickening (r : ℝ) U := by
    rw [hU.cthickening_eq_biUnion_closedBall r.coe_nonneg]
    ext x
    simp [closedBallNeighborhood, Metric.mem_closedBall]
  rw [heq]
  exact Metric.isClosed_cthickening

end CompactDomains

/-- 复角带：每个角坐标的虚部绝对值 ≤ ρ。 -/
def angleStrip (n : ℕ) (ρ : ℝ≥0) : Set (ComplexSpace n) :=
  {q | ‖imagPart q‖ ≤ (ρ : ℝ)}

/-- 复相空间的覆盖域；q 尚未取周期商。 -/
def phaseDomain {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0) :
    Set (ComplexPhaseSpace n) := G ×ˢ angleStrip n ρ

/-- 复作用域的实截面，类型为 Set ℝⁿ。开闭性相对于 ℝⁿ，按下列定理传递。 -/
def realSlice {n : ℕ} (G : Set (ComplexSpace n)) : Set (RealSpace n) :=
  complexify ⁻¹' G

theorem isOpen_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsOpen G) :
    IsOpen (realSlice G) := hG.preimage (continuous_complexify n)

theorem isClosed_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsClosed G) :
    IsClosed (realSlice G) := hG.preimage (continuous_complexify n)

/-- 紧性的逆像结论使用闭嵌入，不能仅凭连续性。 -/
theorem isCompact_realSlice {n : ℕ} {G : Set (ComplexSpace n)} (hG : IsCompact G) :
    IsCompact (realSlice G) :=
  (isometry_complexify n).isClosedEmbedding.isCompact_preimage hG

/-- 域关于逐坐标复共轭封闭。紧性与初始域规则性须另给证明。 -/
def ConjInvariant {n : ℕ} (G : Set (ComplexSpace n)) : Prop :=
  ∀ p ∈ G, conjVec p ∈ G

theorem mem_angleStrip_iff {n : ℕ} (q : ComplexSpace n) (ρ : ℝ≥0) :
    q ∈ angleStrip n ρ ↔ ∀ j, |(q j).im| ≤ (ρ : ℝ) := by
  simp only [angleStrip, Set.mem_ofPred_eq, pi_norm_le_iff_of_nonneg ρ.coe_nonneg,
    imagPart, Real.norm_eq_abs]

theorem complexify_mem_angleStrip {n : ℕ} (q : RealSpace n) (ρ : ℝ≥0) :
    complexify q ∈ angleStrip n ρ := by
  simp [angleStrip]

theorem angleStrip_mono {n : ℕ} {ρ σ : ℝ≥0} (h : ρ ≤ σ) :
    angleStrip n ρ ⊆ angleStrip n σ := by
  intro q hq
  exact le_trans hq (show (ρ : ℝ) ≤ (σ : ℝ) from h)

end KamProject.Arnold1963
