import KamProject

/-! W5a 的语义与公理审计；包含新共振真正删除点的二维例子，以及非零频率平移。 -/
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit

def frequencyBox : Set (ComplexSpace 2) := realCenteredPolydisc 0 1

theorem frequencyBox_typeD : TypeD frequencyBox 2 := by
  have h := realCenteredPolydisc_typeD (by norm_num : 0 < 2)
    (0 : RealSpace 2) 1 (by intro j; norm_num)
  simpa [frequencyBox, polydiscTypeConstant] using h

theorem frequencyBox_volume : realVolume frequencyBox = 4 := by
  rw [frequencyBox, realVolume_realCenteredPolydisc]
  norm_num

example : realVolume (erosion frequencyBox 1) = 0 := by
  rw [frequencyBox, realVolume_erosion_polydisc]
  norm_num

example : (0 : RealSpace 2) ∈ realSlice (erosion frequencyBox 1) := by
  rw [frequencyBox, mem_realSlice_erosion_polydisc]
  intro j
  norm_num

example : realVolume (erosion frequencyBox 2) = 0 := by
  rw [frequencyBox, realVolume_erosion_polydisc]
  norm_num

example : 2 ∈ newShells 2 4 := mem_newShells.mpr (by norm_num)
example : 4 ∉ newShells 2 4 := by rw [mem_newShells]; norm_num
example : 3 ∈ newShells (5 / 2) (7 / 2) := mem_newShells.mpr (by norm_num)

theorem newShellBudget_two_four : newShellBudget 2 4 = 13 / 36 := by
  norm_num [newShellBudget, newShells, Finset.sum_Ico_succ_top]

def oldFrequencySet : Set (ComplexSpace 2) := nonresonantDomain frequencyBox id (1 / 64) 2

def resonantPoint : ComplexSpace 2 := fun _ => 1 / 2

theorem resonantPoint_old : resonantPoint ∈ oldFrequencySet := by
  refine ⟨?_, ?_⟩
  · intro j
    norm_num [frequencyBox, resonantPoint]
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
      norm_num [indexLength, indexPairing, resonantPoint, Fin.sum_univ_two, h0, h1]

theorem resonance_removal_nonempty :
    (oldFrequencySet \ nonresonantDomain oldFrequencySet id (1 / 64) 4).Nonempty := by
  refine ⟨resonantPoint, resonantPoint_old, ?_⟩
  intro h
  let k : FourierIndex 2 := ![1, -1]
  have hk : k ∈ lowModes 2 4 := by norm_num [mem_lowModes, indexLength, k, Fin.sum_univ_two]
  have hh := h.2 k hk
  norm_num [indexLength, indexPairing, k, resonantPoint, Fin.sum_univ_two] at hh

theorem actual_new_resonance_bound :
    realVolume (oldFrequencySet \ nonresonantDomain oldFrequencySet id (1 / 64) 4) ≤
      ENNReal.ofReal (13 / 18) := by
  have h := frequencyBox_typeD.new_resonance_loss_le (E := oldFrequencySet)
    (N₀ := 2) (N₁ := 4) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 64)
    (by norm_num) (fun _ hx => hx.1) (fun _ hx => hx.2)
  rw [newShellBudget_two_four, frequencyBox_volume] at h
  norm_num at h ⊢
  calc
    _ ≤ ENNReal.ofReal (13 / 72) * 4 := h
    _ = ENNReal.ofReal (13 / 18) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 13 / 72)]
      norm_num

def smallTranslation : ComplexSpace 1 → ComplexSpace 1 := fun _ _ => 1 / 20

theorem smallTranslation_data : FrequencyShiftData smallTranslation (closedBall 0 1)
    (1 / 10) 0 := by
  refine ⟨by norm_num, by norm_num, fun _ _ => analyticAt_const, ?_, ?_⟩
  · refine ⟨by norm_num, fun _ _ => ?_⟩
    norm_num [smallTranslation, Pi.norm_def]
  · intro x _
    rw [show fderiv ℂ smallTranslation x = 0 from
      (hasFDerivAt_const (fun _ : Fin 1 => (1 / 20 : ℂ)) x).fderiv]
    simp

theorem zero_mem_frequencyTarget : (0 : ComplexSpace 1) ∈
    frequencyInverseTarget (closedBall 0 1) (1 / 10) := by
  intro z hz
  exact closedBall_subset_closedBall (by norm_num) hz

theorem inverse_translation_at_zero :
    frequencyInverse smallTranslation (closedBall 0 1) (1 / 10) 0 = fun _ => -(1 / 20) := by
  have h := (smallTranslation_data.inverse_spec zero_mem_frequencyTarget).2.1
  change frequencyInverse smallTranslation (closedBall 0 1) (1 / 10) 0 + (fun _ => 1 / 20) = 0 at h
  exact eq_neg_of_add_eq_zero_left h

example : AnalyticAt ℂ (frequencyInverse smallTranslation (closedBall 0 1) (1 / 10)) 0 :=
  (smallTranslation_data.inverse_analytic_right zero_mem_frequencyTarget).1

example : fundamentalRemainderBound 2 (2 * (1 / 100)) (1 / 10) (1 / 100) =
    (1 / 100 : ℝ) ^ 2 / ((1 / 10 : ℝ) ^ (2 * stepExponent 2) * (1 / 100 : ℝ) ^ 2) :=
  fundamentalRemainderBound_twice 2 _ _ _

#check TypeD
#check TypeD.new_resonance_loss_le
#check frequencyShiftData_of_old_inverse
#check correctedFrequency_image_domain
#print axioms FundamentalParameters.action_buffer_loss_lt
#print axioms fundamentalRemainderBound_twice
#print axioms erosion_add
#print axioms realVolume_erosion_polydisc
#print axioms realCenteredPolydisc_typeD
#print axioms TypeD.new_resonance_loss_le
#print axioms FrequencyShiftData.inverse_analytic_right
#print axioms FrequencyShiftData.inverse_real
#print axioms frequencyChange_derivative_bounds
#print axioms correctedFrequency_image_domain
#print axioms resonance_removal_nonempty
#print axioms actual_new_resonance_bound
#print axioms inverse_translation_at_zero

end KamProject.Arnold1963.Audit
