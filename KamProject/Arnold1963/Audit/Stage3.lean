import KamProject.Arnold1963.Analysis

/-! 截断端点、零模、ℓ¹/最大范数区别、解析域衔接及公理依赖审计。 -/

open KamProject.Arnold1963
open scoped NNReal

namespace KamProject.Arnold1963.Audit

-- 同一个 (1,1) 的 Pi 范数是 1，Fourier 指标长度是 2，必须落在不同端点。
example : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp
example : indexLength (![1, 1] : FourierIndex 2) = 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∉ fourierModes 2 2 := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∈ fourierModes 2 (5 / 2) := by norm_num [indexLength]
example : (![1, 1] : FourierIndex 2) ∈ nonzeroLatticeBall 2 2 := by norm_num [latticeLength]

example (n : ℕ) : (0 : FourierIndex n) ∈ fourierModes n 1 := by simp [indexLength]
example (n : ℕ) : (0 : FourierIndex n) ∉ lowModes n 1 := by simp [indexLength]
example (n : ℕ) : fourierModes n 0 = ∅ := by
  ext k
  simp [not_lt.mpr (indexLength_nonneg k)]
example : (![2, 0] : FourierIndex 2) ∉ fourierModes 2 2 := by norm_num [indexLength]
example (n : ℕ) {N : ℝ} {k : FourierIndex n} (hk : indexLength k = N) :
    k ∉ fourierModes n N := by simp [hk]

-- 常数函数的截断仍保留平均项，不能使用 lowModes 代替完整截断。
example {n : ℕ} (c : ℂ) {N : ℝ} (hN : 0 < N) (q : ComplexSpace n) :
    fourierTruncation (Pi.single (0 : FourierIndex n) c) N q = c := by
  classical
  simp [fourierTruncation, Pi.single_apply, hN, indexLength]

-- 角带可以缩到零宽度，但用于 Cauchy 的缓冲半径仍须严格为正。
example {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0) :
    phaseDomain (erosion G ρ) 0 ⊆ erosion (phaseDomain G ρ) ρ := by
  simpa using phaseDomain_shrink_subset_erosion G (ρ := ρ) le_rfl

-- 二阶一变量估计中的 factorial 2 确实是 2。
example : iteratedDeriv 2 (fun z : ℂ => z ^ 2) 0 = 2 := by
  simp

#print axioms mem_fourierModes
#print axioms not_mem_fourierModes
#print axioms norm_fderiv_le_div_of_mem_erosion
#print axioms AnalyticPhaseFunction.norm_vectorField_le_on_shrink
#print axioms iteratedDeriv_two_line_eq
#print axioms norm_second_fderiv_mixed_le
#print axioms norm_second_coordinate_le
#print axioms norm_sub_le_of_coordinate_bound
#print axioms norm_taylor_remainder_le
#print axioms norm_taylor_remainder_le_of_coordinate_bound
#print axioms fourierTruncation_eq_zero_add
#print axioms norm_fourierTerm_le
#print axioms norm_fourierTruncation_le

end KamProject.Arnold1963.Audit
