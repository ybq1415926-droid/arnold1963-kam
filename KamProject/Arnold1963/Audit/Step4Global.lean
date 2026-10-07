import KamProject.Arnold1963.Audit.Step4
import KamProject.Arnold1963.Geometry.GeneratingTorus

/-! 第四步全域交付审计：非零混合生成函数、旧函数类型拉回、原文预算和真实环面。 -/
noncomputable section
open KamProject.Arnold1963 Set Metric
open scoped NNReal
namespace KamProject.Arnold1963.Audit

def smallMixed (z : ComplexPhaseSpace 1) : ℂ := mixedQuadratic z / 4

theorem smallMixed_analytic (z : ComplexPhaseSpace 1) : AnalyticAt ℂ smallMixed z :=
  (mixedQuadratic_analytic z).div analyticAt_const (by norm_num)

theorem smallMixed_deriv (z v : ComplexPhaseSpace 1) :
    fderiv ℂ smallMixed z v = (v.1 0 * z.2 0 + z.1 0 * v.2 0) / 512 := by
  have hd := (mixedQuadratic_analytic z).differentiableAt.hasFDerivAt.mul_const (4 : ℂ)⁻¹
  change HasFDerivAt smallMixed _ z at hd
  rw [hd.fderiv]
  change (4 : ℂ)⁻¹ * fderiv ℂ mixedQuadratic z v = _
  rw [mixedQuadratic_deriv]
  ring

theorem smallMixed_bound : NormBoundOn smallMixed
    ((closedBall (0 : ComplexSpace 1) 4) ×ˢ closedBall 0 4) (1 / 32) := by
  refine ⟨by norm_num, fun z hz => ?_⟩
  have hh := mixedQuadratic_bound.norm_le hz
  change ‖mixedQuadratic z / 4‖ ≤ _
  rw [norm_div]
  norm_num
  linarith

theorem smallMixed_data : GeneratingData smallMixed (closedBall 0 4) (closedBall 0 4) 1 (1 / 32) :=
  ⟨by norm_num, fun z _ => smallMixed_analytic z, smallMixed_bound, by norm_num⟩

theorem one_mem_generatingTarget : ((fun _ => (1 : ℂ)), (fun _ => (1 : ℂ))) ∈
    generatingTarget (closedBall (0 : ComplexSpace 1) 4) (closedBall 0 4) 1 := by
  constructor <;> intro t ht
  · have hb : dist t (fun _ : Fin 1 => (1 : ℂ)) ≤ 2 := by norm_num at ht; exact ht
    have hh := dist_triangle t (fun _ : Fin 1 => (1 : ℂ)) 0
    have hc : dist (fun _ : Fin 1 => (1 : ℂ)) 0 = 1 := by simp [dist_eq_norm]
    rw [hc] at hh
    exact hh.trans (by linarith)
  · have hb : dist t (fun _ : Fin 1 => (1 : ℂ)) ≤ 3 := by norm_num at ht; exact ht
    have hh := dist_triangle t (fun _ : Fin 1 => (1 : ℂ)) 0
    have hc : dist (fun _ : Fin 1 => (1 : ℂ)) 0 = 1 := by simp [dist_eq_norm]
    rw [hc] at hh
    exact hh.trans (by linarith)

-- 输入两组坐标均非零，输出两组坐标均真正发生变化。
theorem smallMixed_transform_one :
    generatingTransform smallMixed (closedBall 0 4) (closedBall 0 4) 1
      ((fun _ => 1), (fun _ => 1)) = ((fun _ => (513 / 512 : ℂ)), (fun _ => (512 / 513 : ℂ))) := by
  let x : ComplexPhaseSpace 1 := ((fun _ => 1), (fun _ => 512 / 513))
  have hq : x.2 ∈ closedBall (fun _ => (1 : ℂ)) (1 : ℝ≥0) := by
    simp [x, mem_closedBall, dist_eq_norm, Pi.sub_def]
    norm_num
  have hx := generating_ball_buffer one_mem_generatingTarget.1 one_mem_generatingTarget.2 hq
  have hD : x ∈ generatingSource (closedBall 0 4) (closedBall 0 4) 1 :=
    erosion_antitone_radius _ (show (1 : ℝ≥0) ≤ 1 + 1 by norm_num) hx
  have hF : generatingInput smallMixed x = ((fun _ => 1), (fun _ => 1)) := by
    apply Prod.ext
    · rfl
    · ext j
      simp [generatingInput, pGradient, smallMixed_deriv, pDirection, x, Fin.eq_zero j]
      norm_num
  have hg : generatingInverse smallMixed (closedBall 0 4) (closedBall 0 4) 1
      ((fun _ => 1), (fun _ => 1)) = x := by
    rw [← hF]
    exact smallMixed_data.input_injOn.leftInvOn_invFunOn hD
  unfold generatingTransform
  rw [Function.comp_apply, hg]
  apply Prod.ext
  · ext j
    simp [generatingOutput, qGradient, smallMixed_deriv, qDirection, x, Fin.eq_zero j]
    norm_num
  · rfl

example : Function.Bijective (fderiv ℂ
    (generatingTransform smallMixed (closedBall 0 4) (closedBall 0 4) 1)
    ((fun _ => 1), (fun _ => 1))) :=
  (smallMixed_data.transform_canonical _ one_mem_generatingTarget).derivative_bijective

example {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0}
    (S : AnalyticPhaseFunction n G ρ) (hn : 0 < n) (hr : 0 < r)
    (hM : S.uniformNorm < (r : ℝ) ^ 2 / (16 * n)) :
    AnalyticCanonicalTransformation (generatingTarget G (angleStrip n ρ) r)
      (phaseDomain G ρ) (S.uniformNorm / r) := (S.generatingData hn hr hM).transformation

example {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0}
    (H S : AnalyticPhaseFunction n G ρ) (hn : 0 < n) (hr : 0 < r)
    (hM : S.uniformNorm < (r : ℝ) ^ 2 / (16 * n)) (hρ : r + r + r ≤ ρ) :
    (H.pullbackGenerating S (S.generatingData hn hr hM) hρ).uniformNorm ≤ H.uniformNorm :=
  H.uniformNorm_pullbackGenerating_le S _ hρ

example {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0}
    (H S : AnalyticPhaseFunction n G ρ)
    (d : GeneratingData S.toFun G (angleStrip n ρ) r S.uniformNorm)
    {z : ComplexPhaseSpace n} (hz : z ∈ generatingTarget G (angleStrip n ρ) r) :
    fderiv ℂ (generatingTransform S.toFun G (angleStrip n ρ) r) z
      (hamiltonianVectorField (H.toFun ∘ generatingTransform S.toFun G (angleStrip n ρ) r) z) =
      hamiltonianVectorField H.toFun (generatingTransform S.toFun G (angleStrip n ρ) r z) :=
  H.canonical_pullback d.transform_canonical d.transform_mapsTo hz

#print axioms generating_injOn
#print axioms GeneratingData.inverse_analytic_right
#print axioms GeneratingData.transformation
#print axioms AnalyticPhaseFunction.pullbackGenerating
#print axioms AnalyticPhaseFunction.generatingTransform_real
#print axioms AnalyticPhaseFunction.generatingTorusTransform_projection
#print axioms AnalyticPhaseFunction.generatingTorusTransform_injOn
#print axioms smallMixed_transform_one

end KamProject.Arnold1963.Audit
