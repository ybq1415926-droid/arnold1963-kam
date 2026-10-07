import KamProject.Arnold1963.Analysis.MeanValue

/-! 逐项最大范数与最大范数诱导算子范数。没有更换任何矩阵范数实例。 -/
noncomputable section
namespace KamProject.Arnold1963

def linearEntries {n m : ℕ} (A : ComplexSpace n →L[ℂ] ComplexSpace m) :
    Fin m → Fin n → ℂ := fun i j => A (Pi.single j 1) i

theorem norm_linearEntries_le {n m : ℕ} (A : ComplexSpace n →L[ℂ] ComplexSpace m) :
    ‖linearEntries A‖ ≤ ‖A‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
  intro j
  calc
    ‖linearEntries A i j‖ ≤ ‖A (Pi.single j 1)‖ := norm_le_pi_norm _ i
    _ ≤ ‖A‖ * ‖(Pi.single j (1 : ℂ) : ComplexSpace n)‖ := A.le_opNorm _
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
      ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro l; by_cases h : l = j <;> simp [h]))
      (norm_nonneg _)
    _ = ‖A‖ := mul_one _

theorem norm_le_dim_mul_linearEntries {n m : ℕ}
    (A : ComplexSpace n →L[ℂ] ComplexSpace m) :
    ‖A‖ ≤ n * ‖linearEntries A‖ := by
  apply norm_linearMap_le_of_coordinate_bound A (norm_nonneg _)
  intro j
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (linearEntries A))).mpr
  intro i
  exact (norm_le_pi_norm (linearEntries A i) j).trans (norm_le_pi_norm (linearEntries A) i)

theorem norm_bilinear_le_of_entries {n : ℕ}
    (B : ComplexSpace n →L[ℂ] ComplexSpace n →L[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, ‖B (Pi.single i 1) (Pi.single j 1)‖ ≤ C) :
    ‖B‖ ≤ (n : ℝ) ^ 2 * C := by
  have hb : ‖B‖ ≤ (n : ℝ) * ((n : ℝ) * C) :=
    norm_linearMap_le_of_coordinate_bound B (mul_nonneg (Nat.cast_nonneg _) hC)
      (fun i => norm_linearMap_le_of_coordinate_bound _ hC (h i))
  convert hb using 1; ring

end KamProject.Arnold1963
