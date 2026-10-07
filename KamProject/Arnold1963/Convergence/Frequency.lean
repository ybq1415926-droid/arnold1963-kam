import KamProject.Arnold1963.Convergence.Limit

/-! 实际频率列在同一个 G∞ 上一致收敛，保留 β 尺度的严格尾差。
frequency s = 论文 A_s；frequency_displacement b s 控制 A_{s+1}-A_s，
使用 beta δ₁ s * delta δ₁ s = 论文 β_{s+1} δ_{s+1}。
-/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

def frequency (s : ℕ) : ComplexSpace n → ComplexSpace n :=
  actionFrequency (h.state b s).integrable

def limitFrequency : ComplexSpace n → ComplexSpace n := Convergence.sequenceLimit (h.frequency b)

theorem frequency_uniform : TendstoUniformlyOn (h.frequency b) (h.limitFrequency b) atTop
    (h.limitDomain b) :=
  Convergence.sequenceLimit_tendstoUniformlyOn b.frequency_budget_summable
    (fun s _ hp => (h.frequency_displacement b s (h.limit_subset b (s + 1) hp)).le)

/-- 论文 |A∞-A_s| < β_{s+1}/2。状态 s 不偏移，步参数 beta 的下标加一。 -/
theorem limitFrequency_tail {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) (s : ℕ) :
    ‖h.limitFrequency b p - h.frequency b s p‖ < (beta δ₁ s : ℝ) / 2 :=
  (Convergence.sequenceLimit_tail_le b.frequency_budget_summable
    (fun j => (h.frequency_displacement b j (h.limit_subset b (j + 1) hp)).le) s).trans_lt
      (b.frequency_tail_lt s)

theorem limitFrequency_continuous : ContinuousOn (h.limitFrequency b) (h.limitDomain b) :=
  (h.frequency_uniform b).continuousOn (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun s =>
      (h.state b s).input.chart.analytic.continuousOn.mono (h.limit_subset b s)))

theorem limitFrequency_real {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    h.limitFrequency b (conjVec p) = conjVec (h.limitFrequency b p) := by
  have hc : conjVec p ∈ h.limitDomain b := by
    apply mem_iInter.mpr
    intro s
    exact (h.state b s).input.chart.domain_conj p (h.limit_subset b s hp)
  have hs := (h.frequency_uniform b).tendsto_at hc
  have ht := ((h.frequency_uniform b).tendsto_at hp).star
  apply tendsto_nhds_unique hs
  convert ht using 1
  · funext s
    exact (h.state b s).input.chart.map_conj p (h.limit_subset b s hp)
  · rw [conjVec_eq_star]

theorem limitFrequency_real_value {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    complexify (realPart (h.limitFrequency b (complexify p))) =
      h.limitFrequency b (complexify p) := by
  apply complexify_realPart_of_conj
  simpa only [conjVec_complexify] using (h.limitFrequency_real b hp).symm

end KamProject.Arnold1963.Iteration.InitialData
