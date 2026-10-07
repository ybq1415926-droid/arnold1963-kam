import KamProject.Arnold1963.Step.GeneratingFunction
import KamProject.Arnold1963.Analysis.Taylor

/-! 可积部分的频率及基本引理所需的输入。
频率是实际 Fréchet 导数的坐标，不另行指定一个无关的向量场。
在任意闭集上，仅函数值保实不足以推出导数保实，故显式保留频率的共轭条件。
-/
noncomputable section
open Set
open Filter
open scoped Topology
namespace KamProject.Arnold1963

def actionFrequency {n : ℕ} (h : ComplexSpace n → ℂ) (p : ComplexSpace n) :
    ComplexSpace n := fun j => fderiv ℂ h p (Pi.single j 1)

theorem fderiv_eq_actionFrequency {n : ℕ} (h : ComplexSpace n → ℂ)
    (p v : ComplexSpace n) :
    fderiv ℂ h p v = ∑ j, actionFrequency h p j * v j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [actionFrequency, mul_comm]

theorem analyticOnNhd_actionFrequency {n : ℕ} {G : Set (ComplexSpace n)}
    {h : ComplexSpace n → ℂ} (hh : AnalyticOnNhd ℂ h G) :
    AnalyticOnNhd ℂ (actionFrequency h) G := by
  intro p hp
  apply AnalyticAt.pi
  intro j
  exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single j 1)).analyticAt _).comp (hh.fderiv p hp)

/-- 若保实恒等式在共轭点的环境邻域成立，频率保实可由求导推出。 -/
theorem actionFrequency_conj_of_mem_nhds {n : ℕ} {h : ComplexSpace n → ℂ}
    {V : Set (ComplexSpace n)} {p : ComplexSpace n}
    (ha : AnalyticAt ℂ h p) (hc : ∀ x ∈ V, h (conjVec x) = star (h x))
    (hp : V ∈ 𝓝 (conjVec p)) :
    actionFrequency h (conjVec p) = conjVec (actionFrequency h p) := by
  have he : h =ᶠ[𝓝 (star p)] (star ∘ h ∘ star) := by
    filter_upwards [hp] with z hz
    simpa [Function.comp_def, ← hc z hz] using (star_star (h z)).symm
  have hd := ha.differentiableAt.hasFDerivAt.star_star
  ext j
  dsimp [actionFrequency, conjVec]
  rw [he.fderiv_eq, hd.fderiv]
  simp

/-- 原文可积部分的局部输入。下界 θ 和频率的全局可逆性属于后续移频/测度步骤；
本引理只使用解析性、实结构及坐标 Hessian 上界。 -/
structure IntegrableData {n : ℕ} (h : ComplexSpace n → ℂ)
    (G : Set (ComplexSpace n)) (Θ : ℝ) : Prop where
  analytic : AnalyticOnNhd ℂ h G
  conj_compatible : ∀ p ∈ G, h (conjVec p) = star (h p)
  frequency_conj : ∀ p ∈ G,
    actionFrequency h (conjVec p) = conjVec (actionFrequency h p)
  hessian_bound : ∀ p ∈ G, ∀ i j,
    ‖fderiv ℂ (fderiv ℂ h) p (Pi.single i 1) (Pi.single j 1)‖ ≤ Θ

end KamProject.Arnold1963
