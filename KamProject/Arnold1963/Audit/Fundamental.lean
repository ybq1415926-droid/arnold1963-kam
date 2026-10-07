import KamProject.Arnold1963.Audit.FundamentalExample

/-! 基本引理交付审计：全部输入有实例，定义域非空，扰动不是常函数。 -/
noncomputable section
open Set Metric
open scoped NNReal
namespace KamProject.Arnold1963.Audit

def auditDelta : ℝ≥0 :=
  ⟨min (threshold0 1 1) (1 / 100) / 2,
    (div_pos (lt_min (threshold0_pos (by norm_num) (by norm_num)) (by norm_num))
      (by norm_num)).le⟩

theorem auditDelta_pos : 0 < auditDelta := by
  change 0 < min (threshold0 1 1) (1 / 100) / 2
  exact div_pos (lt_min (threshold0_pos (by norm_num) (by norm_num)) (by norm_num)) (by norm_num)

theorem auditDelta_small : (auditDelta : ℝ) < threshold0 1 1 ∧ (auditDelta : ℝ) < 1 / 100 := by
  have hh : 0 < min (threshold0 1 1) (1 / 100) :=
    lt_min (threshold0_pos (by norm_num) (by norm_num)) (by norm_num)
  have ha := min_le_left (threshold0 1 1) (1 / 100)
  have hb := min_le_right (threshold0 1 1) (1 / 100)
  change min (threshold0 1 1) (1 / 100) / 2 < _ ∧
    min (threshold0 1 1) (1 / 100) / 2 < _
  constructor <;> linarith

def auditM : ℝ := min ((auditDelta : ℝ) ^ 5 * ((auditDelta : ℝ) / 2) ^ 2)
  (Real.exp (-(6 * (auditDelta : ℝ) + 1))) / 2

theorem auditM_pos : 0 < auditM := by
  have hd : (0 : ℝ) < auditDelta := auditDelta_pos
  unfold auditM
  positivity

theorem auditBudget : FundamentalParameters 1 1 (auditDelta / 2) auditDelta
    (6 * auditDelta) (1 / 2) auditM 1 where
  dimension_pos := by norm_num
  beta_pos := div_pos auditDelta_pos (by norm_num)
  delta_pos := auditDelta_pos
  theta_pos := by norm_num
  delta_small := auditDelta_small.1
  angle_loss := by
    have hd : (0 : ℝ) < auditDelta := auditDelta_pos
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  angle_width := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
    linarith [auditDelta_small.2]
  width_le_one := le_rfl
  action_loss := by
    have hd : (0 : ℝ) < auditDelta := auditDelta_pos
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  divisor_margin := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith [auditDelta_small.2]
  perturbation_pos := auditM_pos
  perturbation_small := by
    have hd : (0 : ℝ) < auditDelta := auditDelta_pos
    have ha := min_le_left ((auditDelta : ℝ) ^ 5 * ((auditDelta : ℝ) / 2) ^ 2)
      (Real.exp (-(6 * (auditDelta : ℝ) + 1)))
    have hp : 0 < (auditDelta : ℝ) ^ 5 * ((auditDelta : ℝ) / 2) ^ 2 := by positivity
    dsimp [auditM, stepExponent]
    nlinarith
  cutoff_gt_one := by
    have hd : (0 : ℝ) < auditDelta := auditDelta_pos
    have hmexp : auditM < Real.exp (-(6 * (auditDelta : ℝ))) := by
      have hm := min_le_right ((auditDelta : ℝ) ^ 5 * ((auditDelta : ℝ) / 2) ^ 2)
        (Real.exp (-(6 * (auditDelta : ℝ) + 1)))
      have hexp := Real.exp_pos (-(6 * (auditDelta : ℝ) + 1))
      have he := Real.exp_lt_exp.mpr
        (show -(6 * (auditDelta : ℝ) + 1) < -(6 * (auditDelta : ℝ)) by linarith)
      dsimp [auditM]
      linarith
    have hlog := (Real.log_lt_iff_lt_exp auditM_pos).mpr hmexp
    unfold fundamentalCutoff
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    apply (lt_div_iff₀ (by positivity : 0 < 6 * (auditDelta : ℝ))).mpr
    rw [one_div, Real.log_inv]
    linarith

def auditedResult : FundamentalResult quadraticAction (examplePerturbation 1 auditM)
    exampleActionDomain (auditDelta / 2) auditDelta (6 * auditDelta) (1 / 2) auditM :=
  (exampleInput auditBudget).result

theorem audit_domain_nonempty :
    ((fun _ => (1 : ℂ)), (0 : ComplexSpace 1)) ∈
      phaseDomain (erosion exampleActionDomain (auditDelta / 2 + auditDelta / 2))
        (1 - (6 * auditDelta + 6 * auditDelta)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    change dist p (fun _ => (1 : ℂ)) ≤ (1 / 4 : ℝ)
    change dist p (fun _ => (1 : ℂ)) ≤ (↑(auditDelta / 2 + auditDelta / 2) : ℝ) at hp
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat] at hp
    linarith [auditDelta_small.2]
  · simpa using complexify_mem_angleStrip (0 : RealSpace 1) _

example : (examplePerturbation 1 auditM).toFun ((fun _ => 1), 0) ≠
    (examplePerturbation 1 auditM).toFun ((fun _ => 1), fun _ => (Real.pi : ℂ)) :=
  examplePerturbation_nonconstant 1 auditM_pos _

example : auditedResult.perturbation.uniformNorm <
    fundamentalRemainderBound 1 auditM auditDelta (auditDelta / 2) := auditedResult.bound

example : CanonicalOn auditedResult.transformation.toFun
    (phaseDomain (erosion exampleActionDomain (auditDelta / 2 + auditDelta / 2))
      (1 - (6 * auditDelta + 6 * auditDelta))) := auditedResult.transformation.canonical

#check fundamental_lemma
#check FundamentalInput.result
#check @FundamentalInput.mk
#check @FundamentalResult.mk
#print axioms homological_equation
#print axioms norm_homologicalGenerator_le
#print axioms FundamentalParameters.remainder_budget
#print axioms FundamentalInput.remainder_norm_bound
#print axioms FundamentalInput.newPerturbation_bound
#print axioms fundamental_lemma
#print axioms FundamentalInput.onNonresonantDomain
#print axioms auditedResult
#print axioms audit_domain_nonempty
#print axioms example_has_nonzero_mode
#print axioms IntegrableData.of_frequency_bound

end KamProject.Arnold1963.Audit
