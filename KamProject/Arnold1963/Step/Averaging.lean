import KamProject.Arnold1963.Analysis.FourierParameter
import KamProject.Arnold1963.Analysis.SecondCauchy
import KamProject.Arnold1963.Analysis.MeanValue
import KamProject.Arnold1963.Step.IntegrableBounds
import KamProject.Arnold1963.Geometry.GlobalInverse

/-! W5b 平均化：从真实角积分取得移频及其最大范数算子界。
二阶坐标界转成频率导数的算子界时，显式计入 n。 -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963

theorem actionFrequency_add {n : ℕ} {a b : ComplexSpace n → ℂ} {p}
    (ha : DifferentiableAt ℂ a p) (hb : DifferentiableAt ℂ b p) :
    actionFrequency (fun x => a x + b x) p = actionFrequency a p + actionFrequency b p := by
  ext j
  have hd : fderiv ℂ (fun x => a x + b x) p = fderiv ℂ a p + fderiv ℂ b p :=
    (ha.hasFDerivAt.add hb.hasFDerivAt).fderiv
  change fderiv ℂ (fun x => a x + b x) p (Pi.single j 1) = _
  rw [hd]
  rfl

/-- 在环境邻域的恒等式足以继续求导和搬运解析坐标，避免在闭集上错误求导。 -/
theorem actionFrequency_add_eventually {n : ℕ} {a b : ComplexSpace n → ℂ} {p}
    (ha : AnalyticAt ℂ a p) (hb : AnalyticAt ℂ b p) :
    actionFrequency (fun x => a x + b x) =ᶠ[𝓝 p]
      (fun x => actionFrequency a x + actionFrequency b x) := by
  filter_upwards [ha.eventually_analyticAt, hb.eventually_analyticAt] with x hx hy
  exact actionFrequency_add hx.differentiableAt hy.differentiableAt

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
  (f : AnalyticPhaseFunction n G ρ)

def averagedHamiltonian (a : ComplexSpace n → ℂ) : ComplexSpace n → ℂ :=
  fun p => a p + f.angleAverage p

def frequencyShift : ComplexSpace n → ComplexSpace n := actionFrequency f.angleAverage

theorem frequencyShift_analytic : AnalyticOnNhd ℂ f.frequencyShift G :=
  analyticOnNhd_actionFrequency f.analyticOnNhd_angleAverage

theorem frequencyShift_bound {β : ℝ≥0} (hβ : 0 < β) {M : ℝ}
    (hf : f.uniformNorm ≤ M) : NormBoundOn f.frequencyShift (erosion G β) (M / β) := by
  have hM := (f.norm_le_iff.mp hf).nonneg
  refine ⟨div_nonneg hM β.coe_nonneg, fun p hp => ?_⟩
  apply (complex_norm_le_iff _ (div_nonneg hM β.coe_nonneg)).mpr
  intro j
  exact norm_fderiv_apply_le_div_of_mem_erosion hβ f.analyticOnNhd_angleAverage
    ⟨hM, fun p hp => (f.norm_angleAverage_le hp).trans hf⟩ hp (by simp [Pi.norm_single])

theorem frequencyShift_derivative_bound {β : ℝ≥0} (hβ : 0 < β) {M : ℝ}
    (hf : f.uniformNorm ≤ M) {p} (hp : p ∈ erosion G β) :
    ‖fderiv ℂ f.frequencyShift p‖ ≤ 2 * n * M / (β : ℝ) ^ 2 := by
  have hM := (f.norm_le_iff.mp hf).nonneg
  have h := norm_linearMap_le_of_coordinate_bound (fderiv ℂ f.frequencyShift p)
    (by positivity : 0 ≤ 2 * M / (β : ℝ) ^ 2) (fun i => ?_)
  · convert h using 1; ring
  · apply (complex_norm_le_iff _ (by positivity)).mpr
    intro j
    rw [frequencyShift, fderiv_actionFrequency_apply
      (f.analyticOnNhd_angleAverage p (erosion_subset _ _ hp))]
    exact norm_second_coordinate_le hβ f.analyticOnNhd_angleAverage
      ⟨hM, fun p hp => (f.norm_angleAverage_le hp).trans hf⟩ hp i j

theorem frequencyShift_conj {β : ℝ≥0} (hβ : 0 < β) {p}
    (hp : p ∈ erosion G β) : f.frequencyShift (conjVec p) = conjVec (f.frequencyShift p) := by
  apply actionFrequency_conj_of_mem_nhds
    (f.analyticOnNhd_angleAverage p (erosion_subset _ _ hp))
    (fun _ hx => f.angleAverage_conj hx)
  have hh := erosion_mem_nhds (r := 0) hβ
    (show conjVec p ∈ erosion G (0 + β) by
      simpa using star_mem_erosion f.domain_conj hp)
  simpa only [erosion_zero] using hh

theorem averagedHamiltonian_frequency {a : ComplexSpace n → ℂ}
    (ha : AnalyticOnNhd ℂ a G) {p} (hp : p ∈ G) :
    actionFrequency (f.averagedHamiltonian a) p = actionFrequency a p + f.frequencyShift p :=
  actionFrequency_add (ha p hp).differentiableAt
    (f.analyticOnNhd_angleAverage p hp).differentiableAt

end AnalyticPhaseFunction
end KamProject.Arnold1963
