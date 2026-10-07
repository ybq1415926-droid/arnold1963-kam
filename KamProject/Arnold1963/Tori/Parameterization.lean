import KamProject.Arnold1963.Tori.FrequencyInjectivity
import KamProject.Arnold1963.Tori.AngleBounds
import KamProject.Arnold1963.Dynamics.RealOrbits

/-! 论文的频率重标记及 p=p_ω+f_ω(Q), q=Q+g_ω(Q)。
所有修正仍取自 W7 的同一个 S∞；中心取 A₀⁻¹ω，而不是悄悄换成实际作用标签。
-/
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963.Iteration

namespace InitialParameters
variable {n : ℕ} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
include b
theorem torus_displacement_budget :
    (beta δ₁ 0 : ℝ) * (2 + (θ₀ : ℝ)⁻¹) < κ := by
  have ht := (threshold5_bounds b.small).2.2.2
  change (δ₁ : ℝ) < κ / (2 + (θ₀ : ℝ)⁻¹) at ht
  have hc : 0 < 2 + (θ₀ : ℝ)⁻¹ := by positivity
  have hm := (lt_div_iff₀ hc).mp ht
  have hb : (beta δ₁ 0 : ℝ) ≤ δ₁ := by
    simp only [beta, delta, decay_zero, NNReal.coe_pow]
    exact pow_le_of_le_one δ₁.coe_nonneg (show (δ₁ : ℝ) ≤ 1 from b.delta_one.le)
      (by norm_num : 3 ≠ 0)
  exact (mul_le_mul_of_nonneg_right hb hc.le).trans_lt hm
end InitialParameters

namespace InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

def actionCorrection (p q : ComplexSpace n) : ComplexSpace n :=
  (h.limitMap b (p, q)).1 - h.unperturbedCenter (h.limitFrequency b p)

theorem parameterization_eq (p q : ComplexSpace n) :
    h.limitMap b (p, q) =
      (h.unperturbedCenter (h.limitFrequency b p) + h.actionCorrection b p q,
        q + h.angleCorrection b p q) := by
  simp [actionCorrection, angleCorrection, angleMap]

theorem actionCorrection_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    AnalyticOnNhd ℂ (h.actionCorrection b p) (commonAngleStrip n ρ₀) := by
  intro q hq
  exact (analyticAt_fst.comp (h.limitMap_angle_analytic b hp q hq)).sub analyticAt_const

theorem torusCorrections_small {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ commonAngleStrip n ρ₀) :
    ‖h.actionCorrection b p q‖ < κ ∧ ‖h.angleCorrection b p q‖ < κ := by
  have hd := h.limitMap_displacement b (h.angle_mem_limitPhase b hp hq)
  have hf := (norm_fst_le (h.limitMap b (p, q) - (p, q))).trans_lt hd
  change ‖(h.limitMap b (p, q)).1 - p‖ < 2 * (beta δ₁ 0 : ℝ) at hf
  have hc := h.unperturbedCenter_displacement b hp
  have ht := norm_sub_le_norm_sub_add_norm_sub (h.limitMap b (p, q)).1 p
    (h.unperturbedCenter (h.limitFrequency b p))
  rw [norm_sub_rev p (h.unperturbedCenter (h.limitFrequency b p))] at ht
  have hi : 0 ≤ (θ₀ : ℝ)⁻¹ := inv_nonneg.mpr θ₀.coe_nonneg
  have hb := (beta δ₁ 0).coe_nonneg
  have hbudget := b.torus_displacement_budget
  constructor
  · change ‖(h.limitMap b (p, q)).1 - h.unperturbedCenter (h.limitFrequency b p)‖ < κ
    nlinarith
  · have hqB := h.angleCorrection_bound b hp hq
    nlinarith

theorem torusCorrections_periodic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ commonAngleStrip n ρ₀) (k : FourierIndex n) :
    h.actionCorrection b p (q + angleShift k) = h.actionCorrection b p q ∧
    h.angleCorrection b p (q + angleShift k) = h.angleCorrection b p q := by
  have he := h.limitMap_periodic b (h.angle_mem_limitPhase b hp hq) k
  change h.limitMap b (p, q + angleShift k) = phaseShift k (h.limitMap b (p, q)) at he
  constructor
  · simp only [actionCorrection, he, phaseShift]
  · simp only [angleCorrection, angleMap, he, phaseShift]
    abel

def retainedRealFrequencies : Set (ComplexSpace n) :=
  h.limitFrequency b '' (complexify '' realSlice (h.limitDomain b))

def realFrequencyLabel (ω : ComplexSpace n) : RealSpace n := realPart (h.frequencyLabel b ω)

theorem realFrequencyLabel_spec {ω : ComplexSpace n} (hω : ω ∈ h.retainedRealFrequencies b) :
    h.realFrequencyLabel b ω ∈ realSlice (h.limitDomain b) ∧
      h.limitFrequency b (complexify (h.realFrequencyLabel b ω)) = ω ∧
      complexify (h.realFrequencyLabel b ω) = h.frequencyLabel b ω := by
  rcases hω with ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have he : h.realFrequencyLabel b (h.limitFrequency b (complexify p)) = p := by
    simp only [realFrequencyLabel, h.frequencyLabel_left b hp, realPart_complexify]
  rw [he]
  exact ⟨hp, rfl, (h.frequencyLabel_left b hp).symm⟩

theorem retainedRealFrequency_real {ω : ComplexSpace n}
    (hω : ω ∈ h.retainedRealFrequencies b) : complexify (realPart ω) = ω := by
  have hs := h.realFrequencyLabel_spec b hω
  simpa only [hs.2.1] using h.limitFrequency_real_value b hs.1

theorem retainedRealFrequencies_nonempty : (h.retainedRealFrequencies b).Nonempty := by
  obtain ⟨p, hp⟩ := h.limit_realSlice_nonempty b
  exact ⟨h.limitFrequency b (complexify p), complexify p, ⟨p, hp, rfl⟩, rfl⟩

theorem unperturbedCenter_real {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    complexify (realPart (h.unperturbedCenter (h.limitFrequency b (complexify p)))) =
      h.unperturbedCenter (h.limitFrequency b (complexify p)) := by
  apply complexify_realPart_of_conj
  have hc := h.chart.inverse_conj (by simpa using h.limitFrequency_mem b hp 0)
  have hf : conjVec (h.limitFrequency b (complexify p)) =
      h.limitFrequency b (complexify p) := by
    simpa only [conjVec_complexify] using (h.limitFrequency_real b hp).symm
  rw [hf] at hc
  exact hc.symm

/-- 在频率像上定义的参数提升。实标签的真实性由 realFrequencyLabel_spec 推出。 -/
def frequencyParameterization (ω q : ComplexSpace n) : ComplexPhaseSpace n :=
  h.limitMap b (h.frequencyLabel b ω, q)

theorem frequencyParameterization_eq {ω : ComplexSpace n}
    (hω : ω ∈ h.retainedRealFrequencies b) (q : ComplexSpace n) :
    h.frequencyParameterization b ω q =
      (h.unperturbedCenter ω + h.actionCorrection b (h.frequencyLabel b ω) q,
        q + h.angleCorrection b (h.frequencyLabel b ω) q) := by
  have hs := h.realFrequencyLabel_spec b hω
  have hω' : h.limitFrequency b (h.frequencyLabel b ω) = ω := hs.2.2 ▸ hs.2.1
  simpa only [frequencyParameterization, hω'] using h.parameterization_eq b (h.frequencyLabel b ω) q

end InitialData
end KamProject.Arnold1963.Iteration
