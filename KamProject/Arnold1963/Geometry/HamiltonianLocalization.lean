import KamProject.Arnold1963.Geometry.Localization
import KamProject.Arnold1963.Step.Integrable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Operator.Banach

/-! H₀ 的 Hessian 非退化性到实际局部资料。所有对象先于扰动 H₁ 构造。
`HamiltonianPatch` 是构造的输出格式；下面证明其存在，不能将存在性留给最终定理输入。
-/
noncomputable section
open Set Filter Function Metric
open scoped Topology NNReal
namespace KamProject.Arnold1963

/-- Hessian 作为频率映射的微分；行列式不依赖选用哪个基。 -/
def hessianDet {n : ℕ} (H₀ : ComplexSpace n → ℂ) (p : ComplexSpace n) : ℂ :=
  LinearMap.det (fderiv ℂ (actionFrequency H₀) p).toLinearMap

/-- D(∇H₀) 的坐标就是实际二阶 Fréchet 导数，没有独立给定一个 Hessian。 -/
theorem frequency_derivative_apply {n : ℕ} {H₀ : ComplexSpace n → ℂ}
    {p : ComplexSpace n} (ha : AnalyticAt ℂ H₀ p) (v : ComplexSpace n) (j : Fin n) :
    fderiv ℂ (actionFrequency H₀) p v j =
      fderiv ℂ (fderiv ℂ H₀) p v (Pi.single j 1) := by
  let L : (ComplexSpace n →L[ℂ] ℂ) →L[ℂ] ComplexSpace n :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1))
  exact congrArg (fun D : ComplexSpace n →L[ℂ] ComplexSpace n => D v j)
    ((L.hasFDerivAt.comp p ha.fderiv.differentiableAt.hasFDerivAt).fderiv)

/-- 与原文坐标 Hessian 行列式的连接：列 j 表示沿第 j 个作用坐标求导。 -/
theorem hessianDet_eq_matrix {n : ℕ} {H₀ : ComplexSpace n → ℂ}
    {p : ComplexSpace n} (ha : AnalyticAt ℂ H₀ p) :
    hessianDet H₀ p = Matrix.det (fun i j : Fin n =>
      fderiv ℂ (fderiv ℂ H₀) p (Pi.single j 1) (Pi.single i 1)) := by
  rw [hessianDet, ← LinearMap.det_toMatrix']
  congr 1
  ext i j
  exact frequency_derivative_apply ha (Pi.single j 1) i

theorem isUnit_frequency_derivative_iff {n : ℕ} (H₀ : ComplexSpace n → ℂ)
    (p : ComplexSpace n) :
    IsUnit (fderiv ℂ (actionFrequency H₀) p) ↔ hessianDet H₀ p ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  rfl

/-- 一个局部频率多圆盘及其实际逆像，连同供迭代使用的定量上下界。 -/
structure HamiltonianPatch (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) where
  domain : Set (ComplexSpace n)
  subset : domain ⊆ ambient
  center : RealSpace n
  radius : ℝ
  radius_pos : 0 < radius
  inverse : ComplexSpace n → ComplexSpace n
  chart : AnalyticFrequencyChart (actionFrequency H₀) inverse domain
    (realCenteredPolydisc center (fun _ => radius))
  analytic : AnalyticOnNhd ℂ H₀ domain
  conj : ∀ p ∈ domain, H₀ (conjVec p) = star (H₀ p)
  lower : ℝ≥0
  upper : ℝ≥0
  lower_pos : 0 < lower
  lower_lt_one : lower < 1
  upper_gt_one : 1 < upper
  derivative_lower : ∀ p ∈ domain, ∀ v,
    (lower : ℝ) * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency H₀) p v‖
  derivative_upper : ∀ p ∈ domain, ‖fderiv ℂ (actionFrequency H₀) p‖ ≤ upper

namespace HamiltonianPatch
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}

def frequencyDomain (c : HamiltonianPatch n H₀ ambient) : Set (ComplexSpace n) :=
  realCenteredPolydisc c.center (fun _ => c.radius)

def typeConstant (c : HamiltonianPatch n H₀ ambient) : ℝ :=
  polydiscTypeConstant (fun _ : Fin n => c.radius)

theorem typeD (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n) :
    TypeD c.frequencyDomain c.typeConstant :=
  realCenteredPolydisc_typeD hn c.center _ (fun _ => c.radius_pos)

/-- 原始非退化实点附近存在可调用的局部块，且可置于任意指定邻域 V 内。
H₀ 的共轭条件只在 ambient 上假设；对频率求导时先取包含于 ambient 的对称开球。
-/
theorem exists_at {x : RealSpace n} {V : Set (ComplexSpace n)}
    (hV : V ∈ 𝓝 (complexify x)) (hVG : V ⊆ ambient)
    (ha : AnalyticOnNhd ℂ H₀ ambient)
    (hc : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p))
    (hnd : hessianDet H₀ (complexify x) ≠ 0) :
    ∃ c : HamiltonianPatch n H₀ ambient,
      c.domain ⊆ V ∧ complexify x ∈ interior c.domain := by
  obtain ⟨a, ha0, hab⟩ := Metric.mem_nhds_iff.mp hV
  have hball : ball (complexify x) a ⊆ ambient := hab.trans hVG
  have hfc : ∀ p ∈ ball (complexify x) a,
      actionFrequency H₀ (conjVec p) = conjVec (actionFrequency H₀ p) := by
    intro p hp
    have hcp : conjVec p ∈ ball (complexify x) a := by
      change dist (star p) (complexify x) < a
      have hxstar : star (complexify x) = complexify x := conjVec_complexify x
      rw [← hxstar, dist_star_star]
      exact hp
    exact actionFrequency_conj_of_mem_nhds (ha _ (hball hp)) hc
      (mem_of_superset (isOpen_ball.mem_nhds hcp) hball)
  obtain ⟨g, G, r, hr, hG, hxG, hchart⟩ := exists_polydisc_frequency_chart x
    (ball_mem_nhds _ ha0) (analyticOnNhd_actionFrequency ha _ (hVG (mem_of_mem_nhds hV)))
    ((isUnit_frequency_derivative_iff H₀ _).mpr hnd) hfc
  obtain ⟨θ, Θ, hθ, hθ1, hΘ, hlo, hup⟩ := hchart.exists_derivative_bounds
  exact ⟨{
    domain := G
    subset := hG.trans hball
    center := realPart (actionFrequency H₀ (complexify x))
    radius := r
    radius_pos := hr
    inverse := g
    chart := hchart
    analytic := ha.mono (hG.trans hball)
    conj := fun p hp => hc p (hball (hG hp))
    lower := θ
    upper := Θ
    lower_pos := hθ
    lower_lt_one := hθ1
    upper_gt_one := hΘ
    derivative_lower := hlo
    derivative_upper := hup }, hG.trans hab, hxG⟩

/-- 任意紧实核心可由实际构造的有限个频率图覆盖。
这里只断言覆盖：这些块可能重叠，不据此断言跨分支环面互不相交。
-/
theorem exists_finite_cover {K : Set (RealSpace n)} (hK : IsCompact K)
    (hKG : ∀ x ∈ K, complexify x ∈ interior ambient)
    (ha : AnalyticOnNhd ℂ H₀ ambient)
    (hc : ∀ p ∈ ambient, H₀ (conjVec p) = star (H₀ p))
    (hnd : ∀ x ∈ K, hessianDet H₀ (complexify x) ≠ 0) :
    ∃ s : Finset (HamiltonianPatch n H₀ ambient),
      K ⊆ ⋃ c ∈ s, realSlice (interior c.domain) := by
  classical
  have hex : ∀ x : K, ∃ c : HamiltonianPatch n H₀ ambient,
      complexify x.val ∈ interior c.domain := by
    intro x
    obtain ⟨c, _, hx⟩ := exists_at (mem_interior_iff_mem_nhds.mp (hKG x x.property))
      (Subset.refl ambient) ha hc (hnd x x.property)
    exact ⟨c, hx⟩
  choose c hcx using hex
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => realSlice (interior (c x).domain))
    (fun _ => isOpen_realSlice isOpen_interior) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcx ⟨x, hx⟩⟩)
  refine ⟨s.image c, ?_⟩
  intro x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion₂.mpr ⟨c j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hxj⟩

end HamiltonianPatch
end KamProject.Arnold1963
