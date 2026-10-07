import KamProject.Arnold1963.Measure.CumulativeVolume
import KamProject.Arnold1963.Measure.LimitImage
import KamProject.Arnold1963.Measure.PhaseVolume
import KamProject.Arnold1963.Dynamics.RealOrbits

/-! C4 应用于实际 KAM 极限像。
半开胞腔用于有限组合的无重叠体积；闭胞腔用于紧性与一致极限。
目标是 2π 周期商相空间，保留完整源体积后再使用严格预算。
-/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
namespace KamProject.Arnold1963
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- `AddCircle.measure_univ` 给出每个角圆的物理质量 2π。
右侧幂作用于 `ENNReal.ofReal (2 * Real.pi)`；由 `ENNReal.ofReal_pow` 和 2π ≥ 0，
它恰好等于 `ENNReal.ofReal ((2 * Real.pi) ^ n)`。不使用概率归一化。 -/
theorem torus_phase_volume {n : ℕ} (G : Set (ComplexSpace n)) :
    volume (realSlice G ×ˢ (univ : Set (RealTorus n))) =
      realVolume G * ENNReal.ofReal (2 * Real.pi) ^ n := by
  change (volume.prod volume) _ = _
  rw [Measure.prod_prod]
  congr 1
  change (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle (2 * Real.pi)))) univ = _
  simp [Measure.pi_univ, AddCircle.measure_univ]

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- 闭胞腔 Re G∞ × [0,2π]^n。这里的 Icc 是点态序下的闭盒；
半开胞腔 retainedCell 则使用逐坐标 Ioc 的乘积。 -/
def retainedClosedCell : Set (RealPhaseCover n) :=
  realSlice (h.limitDomain b) ×ˢ Icc 0 (fun _ => 2 * Real.pi)

/-- limit_compact 来自 G₀ 中的闭交集；实截面紧性使用 complexify 的闭嵌入。 -/
theorem retainedClosedCell_compact : IsCompact (h.retainedClosedCell b) :=
  (isCompact_realSlice (h.limit_compact b)).prod isCompact_Icc

theorem retainedCell_subset_closed : h.retainedCell b ⊆ h.retainedClosedCell b := by
  intro x hx
  exact ⟨hx.1, (fun j => (hx.2 j (mem_univ j)).1.le), fun j => (hx.2 j (mem_univ j)).2⟩

/-- 所有实角虚部为零，故 complexifyPhase 映入公共角带 ‖Im q‖ ≤ ρ₀/3。 -/
theorem realLimitMap_continuous : ContinuousOn (h.realLimitMap b)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n))) := by
  change ContinuousOn ((realPartPhaseCLM n) ∘ h.limitMap b ∘ (complexifyPhaseCLM n)) _
  apply (realPartPhaseCLM n).continuous.comp_continuousOn
  exact (h.limitMap_continuous b).comp (complexifyPhaseCLM n).continuous.continuousOn
    (fun _ hx => h.commonPhase_subset b ⟨hx.1, complexify_mem_angleStrip _ _⟩)

/-- 一致收敛先预合成 complexifyPhase，再后合成连续线性实部映射和 1-Lipschitz 商投影。
预合成只需要域映入，两个后合成使用各自的一致连续性。 -/
theorem projected_cumulative_uniform :
    TendstoUniformlyOn (fun s => torusProjection ∘ h.realCumulative b s)
      (torusProjection ∘ h.realLimitMap b) atTop (h.retainedClosedCell b) := by
  have hc := ((h.cumulative_uniform b).comp (@complexifyPhase n)).mono
    (show h.retainedClosedCell b ⊆ complexifyPhase ⁻¹' h.limitPhase b from
      fun _ hx => h.commonPhase_subset b ⟨hx.1, complexify_mem_angleStrip _ _⟩)
  exact torusProjection_lipschitz.uniformContinuous.comp_tendstoUniformlyOn
    ((realPartPhaseCLM n).uniformContinuous.comp_tendstoUniformlyOn hc)

theorem projected_limit_continuous :
    ContinuousOn (torusProjection ∘ h.realLimitMap b) (h.retainedClosedCell b) :=
  continuous_torusProjection.comp_continuousOn ((h.realLimitMap_continuous b).mono
    (fun _ hx => ⟨hx.1, mem_univ _⟩))

/-- 闭胞腔投影的像恰为同一 torusLimitMap 的整个保留周期相空间像。 -/
theorem projected_limit_image :
    (torusProjection ∘ h.realLimitMap b) '' h.retainedClosedCell b =
      h.torusLimitMap b '' (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨torusProjection x, ⟨hx.1, mem_univ _⟩, h.torusLimitMap_projection b hx.1⟩
  · rintro ⟨x, hx, rfl⟩
    have hr := torusRepresentative_mem_cell x
    refine ⟨torusRepresentative x, ?_, rfl⟩
    exact h.retainedCell_subset_closed b ⟨hx.1, hr.2⟩

theorem torusLimitMap_image_compact : IsCompact
    (h.torusLimitMap b '' (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  rw [← h.projected_limit_image b]
  exact (h.retainedClosedCell_compact b).image_of_continuousOn (h.projected_limit_continuous b)

/-- 此处左侧是源域 G∞ 的完整物理体积；下一定理才与初始域 G₀ 的体积比较。
C4 的紧源为 retainedClosedCell，下界来自 retainedCell 的有限步像体积及其包含关系。
不要求极限单射，也不要求极限域有内点。 -/
theorem torusLimitMap_volume_ge :
    realVolume (h.limitDomain b) * ENNReal.ofReal (2 * Real.pi) ^ n ≤
      volume (h.torusLimitMap b ''
        (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  let : (volume : Measure (RealPhaseSpace n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [← h.projected_limit_image b]
  have ha : realVolume (h.limitDomain b) * ENNReal.ofReal (2 * Real.pi) ^ n =
      volume (h.retainedCell b) :=
    (realPhaseLebesgue_physicalCell (h.limitDomain b)).symm
  rw [ha]
  apply measure_image_ge_of_uniform_limit (h.retainedClosedCell_compact b)
    (h.projected_limit_continuous b) (h.projected_cumulative_uniform b)
  exact Eventually.of_forall fun s => (h.cumulative_torus_volume b s).symm.le.trans
    (measure_mono (image_mono (h.retainedCell_subset_closed b)))

/-- W7 的实际大测度结论：体积取于 2π 周期相空间，参照域是原始 G₀。
W6 的严格源预算与前一定理的弱像下界相接：初始目标 < 保留源体积 ≤ 极限像体积。 -/
theorem torusLimitMap_volume_gt :
    ENNReal.ofReal (1 - κ) * volume (realSlice h.domain ×ˢ (univ : Set (RealTorus n))) <
      volume (h.torusLimitMap b ''
        (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  have ht := h.limit_physicalCell_volume_gt b
  rw [realPhaseLebesgue_physicalCell, realPhaseLebesgue_physicalCell] at ht
  rw [torus_phase_volume]
  exact ht.trans_le (h.torusLimitMap_volume_ge b)

end Iteration.InitialData
end KamProject.Arnold1963
