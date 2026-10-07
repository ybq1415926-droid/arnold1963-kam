import KamProject.Arnold1963.Basic
import KamProject.Arnold1963.Arithmetic

/-! 阶段 2 的零点、严格截断端点、ℓ¹ 长度、辛矩阵符号及公理审计。 -/

open KamProject.Arnold1963

namespace KamProject.Arnold1963.Audit

example (n : ℕ) : (latticeShell n 0).card = 1 := by simp
example : (![2, 1] : FourierIndex 2) ∈ latticeShell 2 3 := by
  norm_num [latticeLength]
example : (![2, 1] : FourierIndex 2) ∉ latticeShell 2 2 := by
  norm_num [latticeLength]
example (n : ℕ) (N : ℝ) : (0 : FourierIndex n) ∉ lowModes n N := by
  simp [indexLength]
example : (![1, 0] : FourierIndex 2) ∉ lowModes 2 1 := by
  norm_num [indexLength]
example : (![1, 0] : FourierIndex 2) ∈ lowModes 2 (3 / 2) := by
  norm_num [indexLength]
example : (![2, 0] : FourierIndex 2) ∉ lowModes 2 2 := by
  norm_num [indexLength]
example : ((lowModes 2 3).card : ℝ) ≤ 36 := by
  have h := card_lowModes_le (n := 2) (N := 3) (by omega) (by norm_num)
  norm_num at h ⊢
  exact h

example (n : ℕ) : symplecticMatrix n = -Matrix.J (Fin n) ℂ := rfl
example : symplecticMatrix 1 (.inl 0) (.inr 0) = 1 := by simp
example : symplecticMatrix 1 (.inr 0) (.inl 0) = -1 := by simp

-- 数值引理在 δ=1 的边界仍可用；不把正性假设藏进默认值。
example : (1 : ℝ) / 2 ≤ 1 - Real.exp (-1) :=
  half_le_one_sub_exp_neg (by norm_num) le_rfl

#print axioms indexLength_eq_latticeLength
#print axioms card_latticeShell_le
#print axioms card_nonzeroLatticeBall_le
#print axioms mem_lowModes
#print axioms card_lowModes_le
#print axioms rpow_mul_exp_neg_le
#print axioms rpow_mul_exp_neg_mul_le
#print axioms log_inv_le_rpow
#print axioms half_le_one_sub_exp_neg
#print axioms symplecticMatrix_apply
#print axioms CanonicalAt.matrix_identity
#print axioms AnalyticPhaseFunction.canonical_pullback

end KamProject.Arnold1963.Audit
