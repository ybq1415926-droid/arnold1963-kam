import KamProject.Arnold1963.Audit.W5a
import KamProject.Arnold1963.Step.FrequencyPreparation

/-! W5a 闭合审计：非零移频、非空新域、真实管道排除及两次域更新。 -/
noncomputable section
open Set Metric
open scoped NNReal ENNReal Topology
namespace KamProject.Arnold1963.Audit.Completion

def box : Set (ComplexSpace 1) := closedBall 0 4

theorem identityChart : AnalyticFrequencyChart id id box box := by
  refine ⟨isCompact_closedBall _ _, fun _ _ => analyticAt_id, fun _ _ => analyticAt_id,
    fun _ hx => hx, fun _ hx => hx, fun _ _ => Filter.Eventually.of_forall (fun _ => rfl),
    fun _ _ => Filter.Eventually.of_forall (fun _ => rfl), ?_, fun _ _ => rfl⟩
  intro p hp
  simpa only [box, mem_closedBall, dist_zero_right, conjVec_eq_star, norm_star] using hp

theorem translationInput : FrequencyChangeInput id id smallTranslation box box (1 / 10) 0 1 1 := by
  refine ⟨identityChart, by norm_num, by norm_num, by norm_num, le_rfl, ?_, ?_,
    fun _ _ => analyticAt_const, ?_, ?_, ?_⟩
  · intro p _ v
    simp only [fderiv_id, ContinuousLinearMap.id_apply, NNReal.coe_one, one_mul, le_refl]
  · intro p _
    simpa only [fderiv_id, NNReal.coe_one] using
      (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (ComplexSpace 1)‖ ≤ 1)
  · refine ⟨by norm_num, fun _ _ => ?_⟩
    norm_num [smallTranslation, Pi.norm_def]
  · intro p _
    rw [show fderiv ℂ smallTranslation p = 0 from
      (hasFDerivAt_const (fun _ : Fin 1 => (1 / 20 : ℂ)) p).fderiv]
    norm_num
  · intro p _
    ext j
    simp [smallTranslation, conjVec]

theorem scalar_nonresonant {z : ComplexSpace 1} (hz : (1 / 4 : ℝ) ≤ ‖z 0‖) :
    FiniteNonresonant z (1 / 4) 2 := by
  intro k hk
  have hh := mem_lowModes.mp hk
  rw [indexLength_eq_latticeLength] at hh
  have hlen : latticeLength k = 1 := by
    have hpos : 0 < latticeLength k := by exact_mod_cast hh.1
    have hlt : latticeLength k < 2 := by exact_mod_cast hh.2
    omega
  have hkabs : (k 0).natAbs = 1 := by simpa [latticeLength] using hlen
  have hkm : k 0 = 1 ∨ k 0 = -1 := by omega
  rcases hkm with he | he <;>
    simpa [indexLength, indexPairing, he] using hz

theorem two_in_new_frequency : (fun _ : Fin 1 => (2 : ℂ)) ∈
    erosion (nonresonantDomain box id (1 / 4) 2) ((5 + 7 * (1 : ℝ≥0)) * (1 / 10)) := by
  intro z hz
  have hd : ‖z - (fun _ : Fin 1 => (2 : ℂ))‖ ≤ (6 / 5 : ℝ) := by
    norm_num only [mem_closedBall, dist_eq_norm, NNReal.coe_mul, NNReal.coe_add,
      NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_one] at hz
    exact hz
  have hv : ‖(fun _ : Fin 1 => (2 : ℂ))‖ = 2 := by norm_num [Pi.norm_def]
  have hdz : ‖z‖ ≤ (16 / 5 : ℝ) := by
    have hh := norm_le_norm_sub_add z (fun _ : Fin 1 => (2 : ℂ))
    rw [hv] at hh
    linarith
  constructor
  · change dist z 0 ≤ (4 : ℝ)
    rw [dist_zero_right]
    linarith
  · apply scalar_nonresonant
    change (1 / 4 : ℝ) ≤ ‖z 0‖
    have hd0 : ‖z 0 - 2‖ ≤ (6 / 5 : ℝ) := (norm_le_pi_norm (z - (fun _ => 2)) 0).trans hd
    have hh := norm_le_norm_sub_add (2 : ℂ) (z 0)
    rw [norm_sub_rev] at hh
    norm_num at hh
    linarith

/-- 完整 G5 产生非空域，不是通过空集满足输出。 -/
theorem translated_domain_nonempty : (translationInput.iterationDomain (1 / 4) 2).Nonempty := by
  exact ⟨translationInput.newInverse (fun _ => 2),
    (translationInput.iterationChart (1 / 4) 2).inverse_maps two_in_new_frequency⟩

theorem translated_inverse_value : translationInput.newInverse (fun _ => 2) =
    (fun _ : Fin 1 => (39 / 20 : ℂ)) := by
  have hh := (translationInput.iterationChart (1 / 4) 2).right two_in_new_frequency
  change translationInput.newInverse (fun _ => 2) + (fun _ => 1 / 20) = (fun _ => 2) at hh
  rw [eq_sub_of_add_eq hh]
  ext j
  norm_num

example : closedBallNeighborhood (translationInput.iterationDomain (1 / 4) 2) (1 / 10) ⊆
    erosion (translationInput.iterationE (1 / 4) 2) (1 / 10 + 1 / 10) :=
  translationInput.iteration_target_buffer _ _

example {p} (hp : p ∈ translationInput.iterationE (1 / 4) 2) :
    FiniteNonresonant (p + smallTranslation p) (1 / 4) 2 :=
  translationInput.iterationE_nonresonant _ _ hp

def initialState := ResonanceDomainState.initial 2 (1 / 64)
def firstState := initialState.next (by norm_num) (show (1 : ℝ) ≤ 2 by norm_num) (1 / 100)
def secondState := firstState.next (by norm_num) (show (2 : ℝ) ≤ 4 by norm_num) (1 / 100)

/-- 非坐标方向 (1,1) 的对偶长度是 2，而不是其默认最大范数 1。 -/
example : erosion {z : ComplexSpace 2 | 1 ≤ ‖z 0 + z 1‖} (1 / 10) =
    {z : ComplexSpace 2 | (6 / 5 : ℝ) ≤ ‖z 0 + z 1‖} := by
  have hh := erosion_tube_complement (![1, 1] : RealSpace 2)
    (by norm_num [covectorLength, Fin.sum_univ_two]) 0 1 (by norm_num) (1 / 10)
  norm_num [realCovectorPairing, covectorLength, Fin.sum_univ_two] at hh
  exact hh

theorem firstState_contains_resonantPoint : resonantPoint ∈ firstState.domain frequencyBox := by
  apply firstState.mem_domain.mpr
  constructor
  · have hr : firstState.radius = (1 / 100 : ℝ≥0) := by
      norm_num [firstState, initialState, ResonanceDomainState.next,
        ResonanceDomainState.erode, ResonanceDomainState.cut, ResonanceDomainState.initial]
    have he : resonantPoint = complexify (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
      ext j
      norm_num [resonantPoint, complexify]
    rw [hr, he]
    change (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ realSlice (erosion frequencyBox (1 / 100))
    rw [frequencyBox, mem_realSlice_erosion_polydisc]
    intro j
    norm_num
  · intro k hk
    have hh := mem_lowModes.mp hk
    rw [indexLength_eq_latticeLength] at hh
    have hlen : latticeLength k = 1 := by
      have hpos : 0 < latticeLength k := by exact_mod_cast hh.1
      have hlt : latticeLength k < 2 := by exact_mod_cast hh.2
      omega
    have hklen : (k 0).natAbs + (k 1).natAbs = 1 := by
      simpa [latticeLength, Fin.sum_univ_two] using hlen
    have hc : (k 0 = 1 ∧ k 1 = 0) ∨ (k 0 = -1 ∧ k 1 = 0) ∨
        (k 0 = 0 ∧ k 1 = 1) ∨ (k 0 = 0 ∧ k 1 = -1) := by omega
    rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      norm_num [firstState, initialState, ResonanceDomainState.next,
        ResonanceDomainState.erode, ResonanceDomainState.cut, ResonanceDomainState.initial,
        lowModes, nonzeroLatticeBall, indexLength, indexPairing, resonantPoint,
        Fin.sum_univ_two, h0, h1]

theorem two_step_loss_nonempty :
    (firstState.domain frequencyBox \ secondState.domain frequencyBox).Nonempty := by
  refine ⟨resonantPoint, firstState_contains_resonantPoint, ?_⟩
  intro hp
  have hnr := secondState.nonresonant hp
  let k : FourierIndex 2 := ![1, -1]
  have hk : k ∈ lowModes 2 4 := by norm_num [mem_lowModes, indexLength, k, Fin.sum_univ_two]
  have hh := hnr k hk
  norm_num [indexLength, indexPairing, k, resonantPoint, Fin.sum_univ_two] at hh

example : secondState.domain frequencyBox = erosion
    (nonresonantDomain (firstState.domain frequencyBox) id (1 / 64) 4) (1 / 100) :=
  firstState.next_domain _ _ _ _

example : realVolume (firstState.domain frequencyBox \ secondState.domain frequencyBox) ≤
    ENNReal.ofReal (resonanceLossConstant 2 * 2 *
      ((1 / 64) * newShellBudget 2 4 + (1 / 100) * (4 : ℝ) ^ 2)) * realVolume frequencyBox := by
  rw [show secondState.domain frequencyBox = _ from firstState.next_domain _ _ _ _]
  exact frequencyBox_typeD.ar_loss_le firstState (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _

#check FrequencyChangeInput.fundamentalInput
#check frequency_iteration_measure_budget
#print axioms mem_erosion_of_image_buffer
#print axioms AnalyticFrequencyChart.inverse_maps_erosion
#print axioms abs_det_le_pow_of_opNorm_le
#print axioms AnalyticFrequencyChart.realVolume_loss_le
#print axioms correctedFrequency_chart
#print axioms FrequencyChangeInput.neighborhood_maps
#print axioms FrequencyChangeInput.measure_loss
#print axioms TypeD.finiteTube_erosion_layer
#print axioms ResonanceDomainState.next_domain
#print axioms TypeD.ar_loss_le
#print axioms FrequencyChangeInput.fundamentalInput
#print axioms frequency_iteration_measure_budget
#print axioms frequency_iteration_next_chart
#print axioms translated_domain_nonempty
#print axioms translated_inverse_value
#print axioms two_step_loss_nonempty

end KamProject.Arnold1963.Audit.Completion
