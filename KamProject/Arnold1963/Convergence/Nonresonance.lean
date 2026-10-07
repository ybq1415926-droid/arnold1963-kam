import KamProject.Arnold1963.Convergence.Frequency

/-! N 趋于无穷后，实际极限频率满足全部非零整数模的同一个小分母下界。 -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)

theorem indexLength_pos_of_ne_zero (k : FourierIndex n) (hk : k ≠ 0) :
    0 < indexLength k := by
  rw [indexLength_eq_latticeLength]
  exact_mod_cast Nat.pos_of_ne_zero (mt (latticeLength_eq_zero k).mp hk)

include b in
theorem InitialParameters.cutoff_tendsto_atTop : Tendsto (cutoff n δ₁) atTop atTop := by
  have hγ : Summable (fun s => (gamma n δ₁ s : ℝ)) := by
    apply decay_summable
    have hh := (gamma_initial_bounds b.dimension_pos (threshold5_bounds b.small).2.1).2.le
    simp only [gamma, decay_zero] at hh
    exact_mod_cast hh
  apply tendsto_atTop.mpr
  intro R
  have hr : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he : 0 < (1 / 2 : ℝ) / max R 1 := div_pos (by norm_num) hr
  filter_upwards [hγ.tendsto_atTop_zero.eventually (gt_mem_nhds he)] with s hs
  have hg : (0 : ℝ) < gamma n δ₁ s := b.gamma_step_pos s
  have hh := (lt_div_iff₀ hr).mp hs
  have hl := b.cutoff_numerator_gt_half s
  apply le_of_lt
  calc
    R ≤ max R 1 := le_max_left _ _
    _ < cutoff n δ₁ s := (lt_div_iff₀ hg).mpr (by nlinarith)

namespace InitialData
variable (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

def frequencyDomain (s : ℕ) : Set (ComplexSpace n) := (h.state b s).ar.domain Ω₀

theorem frequencyDomain_succ (s : ℕ) : h.frequencyDomain b (s + 1) =
    erosion (nonresonantDomain (h.frequencyDomain b s) id (κ * (δ₁ : ℝ)) (cutoff n δ₁ s))
      ((5 + 7 * Iteration.upper Θ₀ δ₁ s) * beta δ₁ s) :=
  (h.state b s).ar.next_domain b.divisor_pos (b.cutoff_step_le s) _ Ω₀

theorem frequencyDomain_antitone : Antitone (h.frequencyDomain b) := by
  apply antitone_nat_of_succ_le
  intro s
  rw [h.frequencyDomain_succ b]
  exact (erosion_subset _ _).trans (fun _ hx => hx.1)

theorem limitFrequency_mem {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) (s : ℕ) :
    h.limitFrequency b p ∈ h.frequencyDomain b s := by
  apply ((h.state b s).ar.compact h.typeD.compact).isClosed.mem_of_tendsto
    ((h.frequency_uniform b).tendsto_at hp)
  filter_upwards [eventually_ge_atTop s] with t ht
  exact h.frequencyDomain_antitone b ht ((h.state b t).input.chart.maps (h.limit_subset b t hp))

/-- 严格截断 0<|k|₁<N_{s+1}，由状态 s+1 的 AR 域给出该步非共振性。
只使用整数模的 ℓ¹ 长度；不把它换成复向量的最大范数。 -/
theorem limitFrequency_nonresonant {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (k : FourierIndex n) (hk : k ≠ 0) :
    κ * (δ₁ : ℝ) / indexLength k ^ (n + 1) ≤ ‖indexPairing k (h.limitFrequency b p)‖ := by
  obtain ⟨s, hs⟩ := (b.cutoff_tendsto_atTop.eventually (eventually_gt_atTop (indexLength k))).exists
  exact (h.state b (s + 1)).ar.nonresonant (h.limitFrequency_mem b hp (s + 1)) k
    (mem_lowModes.mpr ⟨indexLength_pos_of_ne_zero k hk, hs⟩)

theorem limitFrequency_no_integer_relation {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (k : FourierIndex n) (hk : k ≠ 0) : indexPairing k (h.limitFrequency b p) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (div_pos b.divisor_pos (pow_pos (indexLength_pos_of_ne_zero k hk) _)).trans_le
    (h.limitFrequency_nonresonant b hp k hk)

end InitialData
end KamProject.Arnold1963.Iteration
