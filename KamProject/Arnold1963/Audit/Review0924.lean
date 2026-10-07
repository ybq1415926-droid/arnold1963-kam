import KamProject.Arnold1963.Audit.Steps123
import KamProject.Arnold1963.Analysis.FourierReconstruction

/-! 2026-09-24：交域、测度、辛符号、多变量衰减及复角重构的调用检查。 -/
noncomputable section
open KamProject.Arnold1963
open scoped NNReal
namespace KamProject.Arnold1963.Audit

example {n : ℕ} {G H : Set (ComplexSpace n)} {ρ τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    AnalyticPhaseFunction n (G ∩ H) (min ρ τ) := f.subOnInter g

example {n : ℕ} {G H : Set (ComplexSpace n)} {ρ τ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (g : AnalyticPhaseFunction n H τ) :
    (f.addOnInter g).uniformNorm ≤ f.uniformNorm + g.uniformNorm :=
  f.uniformNorm_addOnInter_le g

example (G : Set (ComplexSpace 2)) :
    realPhaseLebesgue 2 (realSlice G ×ˢ realAngleCell 2 (2 * Real.pi)) =
      realVolume G * ENNReal.ofReal (2 * Real.pi) ^ 2 := realPhaseLebesgue_physicalCell G

example : symplecticMatrix 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [symplecticMatrix, Matrix.J]
example : Matrix.J (Fin 1) ℂ (Sum.inl 0) (Sum.inr 0) = -1 := by
  simp [Matrix.J]

-- 对旧余弦实例调用真实系数衰减，未添加任何衰减假设。
example (ρ : ℝ≥0) (k : FourierIndex 1) :
    ‖(cosineExample ρ).fourierCoeff 0 k‖ ≤
      (cosineExample ρ).uniformNorm * Real.exp (-(indexLength k * ρ)) :=
  (cosineExample ρ).norm_fourierCoeff_le_exp (Set.mem_univ _) k

-- 纯虚角 I/2，确实检验复角重构而非只检查实角截面。
example :
    HasSum (fun k => (cosineExample 1).fourierCoeff 0 k *
      fourierMonomial k (fun _ : Fin 1 => Complex.I / 2))
        (Complex.cos (Complex.I / 2)) := by
  have hq : (fun _ : Fin 1 => Complex.I / 2) ∈ angleStrip 1 (1 / 2 : ℝ≥0) := by
    apply (mem_angleStrip_iff _ _).mpr
    intro j
    norm_num
  exact (cosineExample 1).hasSum_fourier_on_strip (Set.mem_univ _)
    (by norm_num : (1 / 2 : ℝ≥0) < 1) hq

-- N 为实数；接回原文常数的真实余项可直接作用于同一余弦实例。
example (N : ℝ) {q : ComplexSpace 1} (hq : q ∈ angleStrip 1 (3 / 4 : ℝ≥0)) :
    ‖(cosineExample 1).toFun (0, q) -
      fourierTruncation ((cosineExample 1).fourierCoeff 0) N q‖ ≤
        ((2 / Real.exp 1) * (cosineExample 1).uniformNorm / (1 / 24 : ℝ) ^ 2) *
          Real.exp (-N * (1 / 8)) := by
  simpa using (cosineExample 1).norm_sub_fourierTruncation_le
    (Set.mem_univ _) (by decide) (δ := 1 / 24) (γ := 1 / 8) (N := N)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq

example {δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ 1 / 12) :
    (4 / δ) ^ 2 ≤ (4 / Real.exp 1) ^ 2 / δ ^ 3 := by
  convert kernel_constant_le_arnold (n := 2) (by decide) hδ hs using 1
  norm_num

#print axioms AnalyticPhaseFunction.uniformNorm_addOnInter_le
#print axioms AnalyticPhaseFunction.uniformNorm_subOnInter_le
#print axioms realPhaseLebesgue_physicalCell
#print axioms symplectic_matrix_identity_iff_mathlib
#print axioms hamiltonianVectorField_mathlibJ
#print axioms unitCubeIntegral_shift_eq
#print axioms AnalyticPhaseFunction.norm_fourierCoeff_le_exp
#print axioms AnalyticPhaseFunction.shiftedCoeff_eq
#print axioms AnalyticPhaseFunction.hasSum_fourier_on_strip
#print axioms AnalyticPhaseFunction.tsum_fourierTerms_apply
#print axioms kernel_constant_le_arnold
#print axioms AnalyticPhaseFunction.norm_sub_fourierTruncation_le
#print axioms AnalyticPhaseFunction.normBoundOn_fourierRemainder

end KamProject.Arnold1963.Audit
