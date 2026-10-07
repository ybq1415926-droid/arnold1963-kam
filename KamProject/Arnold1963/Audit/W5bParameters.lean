import KamProject.Arnold1963.W5b

/-! 具体可满足的单步参数，避免只在抽象数值假设下检验接口。 -/
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Audit.W5b

def delta : ℝ≥0 :=
  ⟨min (threshold1 1 (1 / 2) 2) (1 / 100) / 2,
    (div_pos (lt_min (threshold1_pos (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)) (by norm_num)).le⟩

theorem delta_pos : 0 < delta := by
  change 0 < min (threshold1 1 (1 / 2) 2) (1 / 100) / 2
  exact div_pos (lt_min (threshold1_pos (by norm_num) (by norm_num) (by norm_num))
    (by norm_num)) (by norm_num)

theorem delta_small : (delta : ℝ) < threshold1 1 (1 / 2) 2 ∧ (delta : ℝ) < 1 / 100 := by
  have hh : 0 < min (threshold1 1 (1 / 2) 2) (1 / 100) :=
    lt_min (threshold1_pos (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have ha := min_le_left (threshold1 1 (1 / 2) 2) (1 / 100)
  have hb := min_le_right (threshold1 1 (1 / 2) 2) (1 / 100)
  change min (threshold1 1 (1 / 2) 2) (1 / 100) / 2 < _ ∧
    min (threshold1 1 (1 / 2) 2) (1 / 100) / 2 < _
  constructor <;> linarith

def amplitude : ℝ := min ((delta : ℝ) ^ 5 * ((delta : ℝ) / 2) ^ 2)
  (Real.exp (-(6 * (delta : ℝ) + 1))) / 4

theorem amplitude_pos : 0 < amplitude := by
  have hd : (0 : ℝ) < delta := delta_pos
  unfold amplitude
  positivity

theorem budget : IterationParameters 1 1 (delta / 2) delta (6 * delta) (1 / 2) 2
    (1 / 2) amplitude where
  dimension_pos := by norm_num
  beta_pos := div_pos delta_pos (by norm_num)
  delta_pos := delta_pos
  lower_pos := by norm_num
  lower_lt_one := by norm_num
  upper_gt_one := by norm_num
  delta_small := by simpa using delta_small.1
  angle_loss := by
    have hd : (0 : ℝ) < delta := delta_pos
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  angle_width := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
    linarith [delta_small.2]
  width_le_one := le_rfl
  action_loss := by
    have hd : (0 : ℝ) < delta := delta_pos
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith
  divisor_margin := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith [delta_small.2]
  divisor_le_one := by norm_num
  perturbation_pos := amplitude_pos
  perturbation_small := by
    have hd : (0 : ℝ) < delta := delta_pos
    have ha := min_le_left ((delta : ℝ) ^ 5 * ((delta : ℝ) / 2) ^ 2)
      (Real.exp (-(6 * (delta : ℝ) + 1)))
    have hp : 0 < (delta : ℝ) ^ 5 * ((delta : ℝ) / 2) ^ 2 := by positivity
    dsimp [amplitude, stepExponent]
    nlinarith
  cutoff_gt_one := by
    have hd : (0 : ℝ) < delta := delta_pos
    have hmexp : 2 * amplitude < Real.exp (-(6 * (delta : ℝ))) := by
      have hm := min_le_right ((delta : ℝ) ^ 5 * ((delta : ℝ) / 2) ^ 2)
        (Real.exp (-(6 * (delta : ℝ) + 1)))
      have hexp := Real.exp_pos (-(6 * (delta : ℝ) + 1))
      have he := Real.exp_lt_exp.mpr
        (show -(6 * (delta : ℝ) + 1) < -(6 * (delta : ℝ)) by linarith)
      dsimp [amplitude]
      linarith
    have hlog := (Real.log_lt_iff_lt_exp
      (by linarith [amplitude_pos] : 0 < 2 * amplitude)).mpr hmexp
    unfold fundamentalCutoff
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    apply (lt_div_iff₀ (by positivity : 0 < 6 * (delta : ℝ))).mpr
    rw [one_div, Real.log_inv]
    linarith

end KamProject.Arnold1963.Audit.W5b
