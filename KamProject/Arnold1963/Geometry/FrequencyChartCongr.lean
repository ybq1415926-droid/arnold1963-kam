import KamProject.Arnold1963.Geometry.FrequencyChart

/-! 在每个域点附近相同的频率函数给出同一解析图，保留真实环境逆性质。 -/
noncomputable section
open Set Filter
open scoped Topology
namespace KamProject.Arnold1963

theorem AnalyticFrequencyChart.congr {n : ℕ} {A A' g : ComplexSpace n → ComplexSpace n}
    {G Ω : Set (ComplexSpace n)} (c : AnalyticFrequencyChart A g G Ω)
    (he : ∀ p ∈ G, A' =ᶠ[𝓝 p] A) : AnalyticFrequencyChart A' g G Ω where
  compact := c.compact
  analytic := fun p hp => (c.analytic p hp).congr (he p hp).symm
  inverse_analytic := c.inverse_analytic
  maps := fun p hp => (he p hp).self_of_nhds ▸ c.maps hp
  inverse_maps := c.inverse_maps
  left_local := by
    intro p hp
    filter_upwards [he p hp, c.left_local p hp] with x hx hi
    rwa [hx]
  right_local := by
    intro y hy
    have hh := (c.inverse_analytic y hy).continuousAt.eventually (he _ (c.inverse_maps hy))
    filter_upwards [hh, c.right_local y hy] with x hx hi
    exact hx.trans hi
  domain_conj := c.domain_conj
  map_conj := by
    intro p hp
    rw [(he _ (c.domain_conj _ hp)).self_of_nhds, (he _ hp).self_of_nhds, c.map_conj _ hp]

end KamProject.Arnold1963
