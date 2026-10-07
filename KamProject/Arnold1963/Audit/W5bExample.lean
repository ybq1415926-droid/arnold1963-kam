import KamProject.Arnold1963.Audit.W5bParameters
import KamProject.Arnold1963.Audit.FundamentalExample

/-! 非退化二次 Hamiltonian + 非零线性平均 + 非常数角扰动。
实际调用整个 W5b，并证明构造的新实截面非空。 -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963.Audit.W5b

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem chart : AnalyticFrequencyChart (actionFrequency quadraticAction) id
    exampleActionDomain exampleActionDomain := by
  have he : actionFrequency quadraticAction = id := funext quadraticAction_frequency
  rw [he]
  exact ⟨isCompact_closedBall _ _, fun _ _ => analyticAt_id, fun _ _ => analyticAt_id,
    fun _ hp => hp, fun _ hp => hp, fun _ _ => Filter.Eventually.of_forall (fun _ => rfl),
    fun _ _ => Filter.Eventually.of_forall (fun _ => rfl), exampleActionDomain_conj,
    fun _ _ => rfl⟩

theorem norm_action_le_four {p : ComplexSpace 1} (hp : p ∈ exampleActionDomain) : ‖p 0‖ ≤ 4 := by
  have hh : ‖p 0 - 1‖ ≤ (1 / 4 : ℝ) :=
    (norm_le_pi_norm (p - (fun _ => 1)) 0).trans (by
      simpa only [exampleActionDomain, mem_closedBall, dist_eq_norm] using hp)
  have ht := norm_le_norm_sub_add (p 0) 1
  norm_num at ht
  linarith

def linearMean (c : ℝ) : AnalyticPhaseFunction 1 exampleActionDomain 1 where
  toFun z := (c : ℂ) * z.1 0
  domain_conj := exampleActionDomain_conj
  analytic := by
    intro z _
    exact analyticAt_const.mul (((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 1 => ℂ) 0).analyticAt z.1).comp (f := Prod.fst) analyticAt_fst)
  periodic := by intro p hp q hq k; rfl
  conj_compatible := by intro z _; simp [conjPhase]
  bounded := ⟨|c| * 4, by positivity, fun z hz => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_action_le_four hz.1) (abs_nonneg _)⟩

def anglePart := (examplePerturbation 1 (amplitude / 2)).restrict
  (subset_univ exampleActionDomain) le_rfl exampleActionDomain_conj

def perturbation := (linearMean (amplitude / 16)).add anglePart

theorem perturbation_bound : perturbation.uniformNorm ≤ amplitude := by
  have hM := amplitude_pos
  have hm : (linearMean (amplitude / 16)).uniformNorm ≤ amplitude / 4 := by
    apply (AnalyticPhaseFunction.norm_le_iff _).mpr
    refine ⟨by positivity, fun z hz => ?_⟩
    change ‖((amplitude / 16 : ℝ) : ℂ) * z.1 0‖ ≤ _
    have hh := mul_le_mul_of_nonneg_left (norm_action_le_four hz.1)
      (show 0 ≤ amplitude / 16 by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < amplitude / 16 by positivity)]
    linarith
  have hc : anglePart.uniformNorm ≤ amplitude / 2 :=
    (AnalyticPhaseFunction.uniformNorm_restrict_le _ _ _ _).trans
      (examplePerturbation_bound 1 (by positivity))
  exact ((AnalyticPhaseFunction.uniformNorm_add_le _ _).trans
    (add_le_add hm hc)).trans (by linarith)

theorem perturbation_average (p : ComplexSpace 1) :
    perturbation.angleAverage p = ((amplitude / 16 : ℝ) : ℂ) * p 0 := by
  rw [AnalyticPhaseFunction.angleAverage_eq_integral]
  change (∫ t : UnitAddTorus (Fin 1), ((amplitude / 16 : ℝ) : ℂ) * p 0 +
    (examplePerturbation 1 (amplitude / 2)).torusValue p t) = _
  rw [integral_add (integrable_const _)
    (((examplePerturbation 1 (amplitude / 2)).continuous_torusValue
    (mem_univ p)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    ← AnalyticPhaseFunction.angleAverage_eq_integral]
  have hz := (scaledCosine 1 (exampleAmplitude 1 (amplitude / 2))).angleAverage_centered_eq_zero
    (mem_univ p)
  change (examplePerturbation 1 (amplitude / 2)).angleAverage p = 0 at hz
  simp [hz]

theorem shift_nonzero (p : ComplexSpace 1) : perturbation.frequencyShift p ≠ 0 := by
  have he : perturbation.angleAverage = fun p => ((amplitude / 16 : ℝ) : ℂ) * p 0 :=
    funext perturbation_average
  intro hh
  have hv := congrFun hh 0
  change fderiv ℂ perturbation.angleAverage p (Pi.single 0 1) = 0 at hv
  rw [he] at hv
  have hd := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt
    (x := p)).const_mul ((amplitude / 16 : ℝ) : ℂ)
  change HasFDerivAt (fun y : ComplexSpace 1 => ((amplitude / 16 : ℝ) : ℂ) * y 0) _ p at hd
  rw [hd.fderiv] at hv
  have heq : ((amplitude / 16 : ℝ) : ℂ) = 0 := by simpa using hv
  have hr : amplitude / 16 = 0 := by exact_mod_cast heq
  linarith [amplitude_pos]

theorem input : IterationInput (Ω := exampleActionDomain) quadraticAction perturbation id
    (delta / 2) delta (6 * delta) (1 / 2) 2 (1 / 2) amplitude where
  chart := chart
  analytic := fun p _ => quadraticAction_analytic p
  conj := fun p _ => quadraticData.conj_compatible p (mem_univ p)
  lower := by
    intro p _ v
    rw [quadraticAction_nondegenerate]
    simp only [ContinuousLinearMap.id_apply, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    nlinarith [norm_nonneg v]
  upper := by
    intro p _
    rw [quadraticAction_nondegenerate]
    exact (ContinuousLinearMap.norm_id_le).trans (by norm_num)
  perturbation := perturbation_bound
  budget := budget

def result := input.result

theorem nonconstant : perturbation.toFun ((fun _ => 1), 0) ≠
    perturbation.toFun ((fun _ => 1), fun _ => (Real.pi : ℂ)) := by
  change ((amplitude / 16 : ℝ) : ℂ) * 1 +
    (examplePerturbation 1 (amplitude / 2)).toFun ((fun _ => 1), 0) ≠
    ((amplitude / 16 : ℝ) : ℂ) * 1 + (examplePerturbation 1 (amplitude / 2)).toFun
      ((fun _ => 1), fun _ => (Real.pi : ℂ))
  exact fun hh => examplePerturbation_nonconstant 1
    (by linarith [amplitude_pos]) _ (add_left_cancel hh)

theorem one_in_frequency_domain : (fun _ : Fin 1 => (1 : ℂ)) ∈
    erosion (nonresonantDomain exampleActionDomain id (1 / 2)
      (fundamentalCutoff (6 * delta) (2 * amplitude))) ((5 + 7 * 2) * (delta / 2)) := by
  intro z hz
  have hd : dist z (fun _ => (1 : ℂ)) ≤ (19 : ℝ) * (delta : ℝ) / 2 := by
    norm_num only [mem_closedBall, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_ofNat] at hz
    linarith
  have hg : z ∈ exampleActionDomain := by
    change dist z (fun _ => (1 : ℂ)) ≤ (1 / 4 : ℝ)
    linarith [delta_small.2]
  refine ⟨hg, ?_⟩
  simpa only [quadraticAction_frequency, id_eq] using example_nonresonance hg
    (fundamentalCutoff (6 * delta) (2 * amplitude))

/-- 此回归例子从显式频率点及逆图构造实点；不声称使用了严格测度预算。 -/
theorem result_realSlice_nonempty_of_explicit_point : (realSlice result.domain).Nonempty := by
  let y : RealSpace 1 := fun _ => 1
  have hy : complexify y ∈ erosion (nonresonantDomain exampleActionDomain id (1 / 2)
      (fundamentalCutoff (6 * delta) (2 * amplitude))) ((5 + 7 * 2) * (delta / 2)) :=
    one_in_frequency_domain
  refine ⟨realPart (result.inverseFrequency (complexify y)), ?_⟩
  change complexify (realPart (result.inverseFrequency (complexify y))) ∈ result.domain
  rw [result.chart.inverse_real hy]
  exact result.chart.inverse_maps hy

end KamProject.Arnold1963.Audit.W5b

