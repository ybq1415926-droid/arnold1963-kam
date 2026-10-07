import KamProject
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! 新流程第 1–3 步的衔接审计；不把条件性 Fourier 定理误报为完整 W2。 -/
noncomputable section
open KamProject.Arnold1963 MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963.Audit

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

-- 用正交性检查真实积分的符号和归一化：非零模式自己的系数为 1。
example (k : FourierIndex 2) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) k = (1 : ℂ) := by
  have h := (orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier) k k
  simpa only [ite_true, eq_self, ContinuousMap.inner_toLp, ← UnitAddTorus.mFourier_neg,
    UnitAddTorus.mFourierCoeff, smul_eq_mul, mul_comm] using h

example : indexLength (![1, 1] : FourierIndex 2) = 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∉ fourierModes 2 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∈ fourierModes 2 (5 / 2) := by
  norm_num [indexLength]
example : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp
example (M : ℝ) : NormBoundOn (fun _ : ℝ => (0 : ℂ)) ∅ M ↔ 0 ≤ M := by simp

-- 一个有真实非零角依赖的旧类型实例，不以零扰动替代接口检查。
private theorem norm_cos_le_exp_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  rw [Complex.norm_exp, Complex.norm_exp] at h
  have ha : (z * Complex.I).re ≤ |z.im| := by simpa using neg_le_abs z.im
  have hb : (-z * Complex.I).re ≤ |z.im| := by simpa using le_abs_self z.im
  exact h.trans (by nlinarith [Real.exp_le_exp.mpr ha, Real.exp_le_exp.mpr hb])

def cosineExample (ρ : ℝ≥0) : AnalyticPhaseFunction 1 Set.univ ρ where
  toFun z := Complex.cos (z.2 0)
  domain_conj := by intro z hz; trivial
  analytic := by
    intro z hz
    let L : ComplexPhaseSpace 1 →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (0 : Fin 1)).comp (ContinuousLinearMap.snd ℂ _ _)
    exact Complex.analyticAt_cos.comp (f := L) (L.analyticAt z)
  periodic := by
    intro p hp q hq k
    simpa [angleShift, complexify, mul_comm, mul_assoc] using
      Complex.cos_add_int_mul_two_pi (q 0) (k 0)
  conj_compatible := by
    intro z hz
    simpa only [conjPhase, conjVec, starRingEnd_apply] using Complex.cos_conj (z.2 0)
  bounded := ⟨Real.exp ρ, (Real.exp_pos _).le, fun z hz =>
    (norm_cos_le_exp_im _).trans (Real.exp_le_exp.mpr ((mem_angleStrip_iff _ _).mp hz.2 0))⟩

example (ρ : ℝ≥0) : (cosineExample ρ).toFun (0, 0) = 1 := by
  simp [cosineExample]
example (ρ : ℝ≥0) :
    (cosineExample ρ).toFun (0, fun _ => (Real.pi : ℂ)) = -1 := by
  simp [cosineExample]

-- 真实系数与平均接口确实接受此前定义的解析函数对象。
example (ρ : ℝ≥0) (k : FourierIndex 1) :
    ‖(cosineExample ρ).fourierCoeff 0 k‖ ≤ (cosineExample ρ).uniformNorm :=
  (cosineExample ρ).norm_fourierCoeff_le (Set.mem_univ _) k
example (ρ : ℝ≥0) :
    ‖(cosineExample ρ).toFun (0, 0) - (cosineExample ρ).angleAverage 0‖ ≤
      2 * (cosineExample ρ).uniformNorm :=
  (cosineExample ρ).norm_sub_angleAverage_le (Set.mem_univ _)
    (by simpa using complexify_mem_angleStrip (0 : RealSpace 1) ρ)

example {δ : ℝ} (hδ : 0 < δ) :
    HasSum (fun k : FourierIndex 0 => Real.exp (-δ * indexLength k)) 1 := by
  simpa using hasSum_exp_indexLength 0 hδ

example {n : ℕ} (hn : 0 < n) {θ Θ ρ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < initialPerturbationThreshold n θ Θ ρ κ D :=
  initialPerturbationThreshold_pos hn hθ hΘ hρ hκ hD

#print axioms AnalyticPhaseFunction.uniformNorm_restrict_le
#print axioms cosineExample
#print axioms AnalyticPhaseFunction.uniformNorm_sub_le
#print axioms AnalyticPhaseFunction.norm_pGradient_le_rectangular
#print axioms AnalyticPhaseFunction.norm_qGradient_le_rectangular
#print axioms norm_le_dim_mul_linearEntries
#print axioms norm_bilinear_le_of_entries
#print axioms threshold5_pos
#print axioms threshold0_budget_conditions
#print axioms budget_step_eq
#print axioms AnalyticPhaseFunction.continuous_torusValue
#print axioms AnalyticPhaseFunction.fourierCoeff_eq_cubeIntegral
#print axioms AnalyticPhaseFunction.fourierCoeff_conj
#print axioms AnalyticPhaseFunction.integral_centered_eq_zero
#print axioms norm_normalized_fourierIntegral_le
#print axioms hasSum_exp_indexLength
#print axioms summable_fourierTerms_of_decay
#print axioms AnalyticPhaseFunction.hasSum_fourier_real_of_summable
#print axioms norm_fourierSeries_tail_le_of_decay

end KamProject.Arnold1963.Audit
