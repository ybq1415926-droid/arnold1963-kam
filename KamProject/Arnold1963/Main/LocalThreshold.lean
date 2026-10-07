import KamProject.Arnold1963.Geometry.HamiltonianLocalization
import KamProject.Arnold1963.Main.LocalKAM

/-! 从先于 H₁ 构造的几何块，选择正阈值并接入 W8 的真实迭代。
复用既有 threshold5 与 initialPerturbationThreshold，不另设小量尺度。
-/
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963
open Iteration
namespace HamiltonianPatch
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}

def seed (c : HamiltonianPatch n H₀ ambient) (ρ : ℝ≥0) (κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (threshold5 n c.lower c.upper ρ κ c.typeConstant / 2)

def threshold (c : HamiltonianPatch n H₀ ambient) (ρ : ℝ≥0) (κ : ℝ) : ℝ :=
  initialPerturbationThreshold n c.lower c.upper ρ κ c.typeConstant

theorem threshold_pos (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) : 0 < c.threshold ρ κ :=
  initialPerturbationThreshold_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos

theorem seed_coe (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    (c.seed ρ κ : ℝ) = threshold5 n c.lower c.upper ρ κ c.typeConstant / 2 := by
  apply Real.coe_toNNReal _ (le_of_lt (half_pos ?_))
  exact threshold5_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos

theorem parameters (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1) :
    InitialParameters n (c.seed ρ κ) c.lower c.upper ρ κ c.typeConstant := by
  have ht := threshold5_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos
  refine ⟨hn, ?_, c.lower_pos, c.lower_lt_one, c.upper_gt_one, hρ, hρ1,
    hκ, hκ1, (c.typeD hn).constant_pos, ?_⟩
  · change (0 : ℝ) < c.seed ρ κ
    rw [c.seed_coe hn hρ hκ]
    exact half_pos ht
  · rw [c.seed_coe hn hρ hκ]
    exact half_lt_self ht

/-- 精确衔接：threshold = (threshold5 / 2)^(8*n+24) = (seed : ℝ)^(8*n+24)。
`seed_coe` 先用正性排除 `Real.toNNReal` 的截零分支；`delta seed 0 = seed`。
这里代码索引 0 对应论文第 1 步的扰动界 M₁。
-/
theorem threshold_eq_initial_bound (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    c.threshold ρ κ = Iteration.perturbation n (c.seed ρ κ) 0 := by
  simp only [Iteration.perturbation, delta, decay_zero, c.seed_coe hn hρ hκ,
    threshold, initialPerturbationThreshold]

/-- 限制到局部域不改变全函数，也不会增加一致范数。
因此没有 H₁ 的导数、Fourier 频谱等参与阈值选择。
-/
def initialData (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ σ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (f : AnalyticPhaseFunction n ambient σ) (hρσ : ρ ≤ σ)
    (hf : f.uniformNorm ≤ c.threshold ρ κ) :
    InitialData n c.frequencyDomain (c.seed ρ κ) c.lower c.upper ρ c.typeConstant where
  domain := c.domain
  integrable := H₀
  perturbation := f.restrict c.subset hρσ c.chart.domain_conj
  inverseFrequency := c.inverse
  chart := c.chart
  analytic := c.analytic
  conj := c.conj
  lower := c.derivative_lower
  upper := c.derivative_upper
  bound := by
    rw [← c.threshold_eq_initial_bound hn hρ hκ]
    exact (f.uniformNorm_restrict_le _ _ _).trans hf
  typeD := c.typeD hn

/-- 一般局部块上的 W8 定理；并非只验证一维二次例子。 -/
theorem local_result (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ σ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (f : AnalyticPhaseFunction n ambient σ) (hρσ : ρ ≤ σ)
    (hf : f.uniformNorm ≤ c.threshold ρ κ) :
    LocalKAMResult (c.parameters hn hρ hρ1 hκ hκ1) (c.initialData hn hρ hκ f hρσ hf) :=
  localKAM _ _

/-- 有限个几何块的统一正阈值；量词中尚未出现扰动 f。
空族也有正阈值，覆盖的正测度与非空性另由几何预算保证。
-/
theorem exists_common_threshold (s : Finset (HamiltonianPatch n H₀ ambient))
    (hn : 0 < n) {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ c ∈ s, M ≤ c.threshold ρ κ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert c s _ ih =>
    obtain ⟨M, hM, hs⟩ := ih
    refine ⟨min M (c.threshold ρ κ), lt_min hM (c.threshold_pos hn hρ hκ), ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs d hd)

end HamiltonianPatch
end KamProject.Arnold1963
