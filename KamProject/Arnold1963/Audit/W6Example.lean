import KamProject.Arnold1963.Main.Theorem2
import KamProject.Arnold1963.Audit.FundamentalExample
import KamProject.Arnold1963.Geometry.SlabMeasure

/-! 非退化二次 Hamiltonian + 非恒定余弦扰动的完整无限迭代回归。
本例的极限非空来自已证明的 AR 总预算，不提供任何新域内点假设。
-/
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W6Completion
open Iteration

theorem threshold_pos : 0 < threshold5 1 (1 / 2) 2 1 (1 / 2) 1 :=
  threshold5_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def initialDelta : ℝ≥0 :=
  ⟨threshold5 1 (1 / 2) 2 1 (1 / 2) 1 / 2, (half_pos threshold_pos).le⟩

theorem parameters : InitialParameters 1 initialDelta (1 / 2) 2 1 (1 / 2) 1 where
  dimension_pos := by norm_num
  delta_pos := half_pos threshold_pos
  lower_pos := by norm_num
  lower_lt_one := by norm_num
  upper_gt_one := by norm_num
  width_pos := by norm_num
  width_le_one := le_rfl
  fraction_pos := by norm_num
  fraction_lt_one := by norm_num
  type_constant_pos := by norm_num
  small := by
    change threshold5 1 (1 / 2) 2 1 (1 / 2) 1 / 2 < threshold5 1 (1 / 2) 2 1 (1 / 2) 1
    linarith [threshold_pos]

def domain : Set (ComplexSpace 1) := realCenteredPolydisc 0 (fun _ => 1)

theorem domain_typeD : TypeD domain 1 := by
  simpa [domain, polydiscTypeConstant] using
    realCenteredPolydisc_typeD (n := 1) (by norm_num) 0 (fun _ => 1) (fun _ => by norm_num)

theorem domain_conj : ConjInvariant domain := by
  intro z hz
  simpa [domain, realCenteredPolydisc, conjVec] using hz

theorem domain_volume : realVolume domain = 2 := by
  rw [domain, realVolume_realCenteredPolydisc]
  norm_num

theorem chart : AnalyticFrequencyChart (actionFrequency quadraticAction) id domain domain := by
  rw [show actionFrequency quadraticAction = id from funext quadraticAction_frequency]
  exact ⟨domain_typeD.compact, fun _ _ => analyticAt_id, fun _ _ => analyticAt_id,
    fun _ hx => hx, fun _ hx => hx, fun _ _ => Filter.Eventually.of_forall (fun _ => rfl),
    fun _ _ => Filter.Eventually.of_forall (fun _ => rfl), domain_conj, fun _ _ => rfl⟩

def perturbation : AnalyticPhaseFunction 1 domain 1 :=
  (examplePerturbation 1 (Iteration.perturbation 1 initialDelta 0)).restrict
    (subset_univ _) le_rfl domain_conj

def initialData : InitialData 1 domain initialDelta (1 / 2) 2 1 1 where
  domain := domain
  integrable := quadraticAction
  perturbation := perturbation
  inverseFrequency := id
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
    exact ContinuousLinearMap.norm_id_le.trans (by norm_num)
  bound :=
    ((examplePerturbation 1 (Iteration.perturbation 1 initialDelta 0)).uniformNorm_restrict_le
      _ _ _).trans (examplePerturbation_bound 1 (parameters.perturbation_step_pos 0))
  typeD := domain_typeD

theorem nonconstant : perturbation.toFun (0, 0) ≠
    perturbation.toFun (0, fun _ => (Real.pi : ℂ)) :=
  examplePerturbation_nonconstant 1 (parameters.perturbation_step_pos 0) 0

theorem result : Theorem2Result parameters initialData := theorem2 parameters initialData

theorem limit_nonempty : (realSlice (initialData.limitDomain parameters)).Nonempty :=
  result.limit_nonempty

theorem limit_volume_gt_one : 1 < realVolume (initialData.limitDomain parameters) := by
  have hh := result.limit_volume
  change ENNReal.ofReal (1 - (1 / 2 : ℝ)) * realVolume domain < _ at hh
  rw [domain_volume, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)] at hh
  norm_num at hh
  exact hh

end KamProject.Arnold1963.Audit.W6Completion
