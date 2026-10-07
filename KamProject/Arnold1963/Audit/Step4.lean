import KamProject.Arnold1963.Audit.Steps123
import KamProject.Arnold1963.Analysis.FourierParameter
import KamProject.Arnold1963.Geometry.GeneratingLocal

/-! 参数积分与生成函数的语义衔接检查，含非零混合生成函数。 -/
noncomputable section
open KamProject.Arnold1963 Set Metric
open scoped NNReal
namespace KamProject.Arnold1963.Audit

example (ρ : ℝ≥0) (k : FourierIndex 1) :
    AnalyticOnNhd ℂ (fun p => (cosineExample ρ).fourierCoeff p k) univ :=
  (cosineExample ρ).analyticOnNhd_fourierCoeff k

example (ρ : ℝ≥0) : (cosineExample ρ).centered.angleAverage 0 = 0 :=
  (cosineExample ρ).angleAverage_centered_eq_zero (mem_univ _)

example (ρ : ℝ≥0) (N : ℝ) : AnalyticOnNhd ℂ
    (fun z : ComplexPhaseSpace 1 =>
      fourierTruncation ((cosineExample ρ).fourierCoeff z.1) N z.2)
    (phaseDomain univ ρ) := (cosineExample ρ).analyticOnNhd_fourierTruncation N

def mixedQuadratic (z : ComplexPhaseSpace 1) : ℂ := z.1 0 * z.2 0 / 128

theorem mixedQuadratic_analytic (z : ComplexPhaseSpace 1) : AnalyticAt ℂ mixedQuadratic z := by
  let Lp : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℂ _ _)
  let Lq : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ _ _)
  exact ((Lp.analyticAt z).mul (Lq.analyticAt z)).div analyticAt_const (by norm_num)

theorem mixedQuadratic_deriv (z v : ComplexPhaseSpace 1) :
    fderiv ℂ mixedQuadratic z v = (v.1 0 * z.2 0 + z.1 0 * v.2 0) / 128 := by
  let Lp : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℂ _ _)
  let Lq : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ _ _)
  have hd := ((Lp.hasFDerivAt (x := z)).mul Lq.hasFDerivAt).mul_const (128 : ℂ)⁻¹
  change HasFDerivAt mixedQuadratic _ z at hd
  rw [hd.fderiv]
  simp [Lp, Lq, div_eq_mul_inv, mul_comm]
  ring

example : (fun _ : Fin 1 => (128 / 129 : ℂ)) +
    pGradient mixedQuadratic (0, fun _ => (128 / 129 : ℂ)) = (fun _ => 1) := by
  ext j
  simp [pGradient, mixedQuadratic_deriv, pDirection, Fin.eq_zero j]
  norm_num

theorem mixedQuadratic_bound : NormBoundOn mixedQuadratic
    ((closedBall (0 : ComplexSpace 1) 4) ×ˢ closedBall 0 4) (1 / 8) := by
  refine ⟨by norm_num, fun z hz => ?_⟩
  have hp : ‖z.1 0‖ ≤ 4 := (norm_le_pi_norm z.1 0).trans (by simpa using hz.1)
  have hq : ‖z.2 0‖ ≤ 4 := (norm_le_pi_norm z.2 0).trans (by simpa using hz.2)
  have hm := mul_le_mul hp hq (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
  simp only [mixedQuadratic, norm_div, norm_mul]
  norm_num
  nlinarith

-- q 的目标是 1，实际解是非零根；混合生成函数的 S_P、S_q 都不恒等于零。
example : Nonempty (GeneratingLocalBranch mixedQuadratic
    (closedBall 0 4) (closedBall 0 4) 1 (1 / 8) (0, fun _ => 1)) := by
  apply exists_generatingLocalBranch (by norm_num)
    (fun z _ => mixedQuadratic_analytic z) mixedQuadratic_bound (by norm_num)
  · intro t ht
    change dist t 0 ≤ 4
    have ht' : dist t 0 ≤ 2 := by norm_num at ht; simpa using ht
    exact ht'.trans (by norm_num)
  · intro t ht
    have h := dist_triangle t (fun _ : Fin 1 => (1 : ℂ)) 0
    have hb : dist t (fun _ : Fin 1 => (1 : ℂ)) ≤ 3 := by norm_num at ht; exact ht
    have hc : dist (fun _ : Fin 1 => (1 : ℂ)) 0 = 1 := by simp [dist_eq_norm]
    rw [hc] at h
    exact h.trans (by linarith)

example {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G U : Set (ComplexSpace n)}
    {r : ℝ≥0} {M : ℝ} {y : ComplexPhaseSpace n}
    (b : GeneratingLocalBranch S G U r M y) {z : ComplexPhaseSpace n}
    (hz : z ∈ b.neighborhood) : Function.Bijective (fderiv ℂ b.transform z) :=
  (b.canonical z hz).derivative_bijective

-- 几何输出直接满足旧 Hamiltonian 拉回定理的域和辛性前提。
example {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G : Set (ComplexSpace n)}
    {ρ r : ℝ≥0} {M : ℝ} {y z : ComplexPhaseSpace n}
    (b : GeneratingLocalBranch S G (angleStrip n ρ) r M y)
    (H : AnalyticPhaseFunction n G ρ) (hz : z ∈ b.neighborhood) :
    fderiv ℂ b.transform z (hamiltonianVectorField (H.toFun ∘ b.transform) z) =
      hamiltonianVectorField H.toFun (b.transform z) :=
  H.canonical_pullback b.canonical b.mapsTo hz

-- 非零维及原文小量预算的数值连接。
example : (1 / 128 : ℝ) / (1 : ℝ≥0) / (1 : ℝ≥0) < 1 / 4 :=
  generating_small_of_arnold (n := 1) (by norm_num) (by norm_num) (by norm_num)

#print axioms analyticAt_integral_compact
#print axioms AnalyticPhaseFunction.analyticOnNhd_fourierCoeff
#print axioms existsUnique_generating_root
#print axioms generating_symplectic_identity
#print axioms exists_generatingLocalBranch
#print axioms generatingLocalBranch_center_unique

end KamProject.Arnold1963.Audit
