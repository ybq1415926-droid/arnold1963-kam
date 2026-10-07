import KamProject.Arnold1963.Basic.Symplectic
import Mathlib.Data.Matrix.Mul

/-!
# 具体坐标矩阵与辛条件

将公共相空间中的线性映射写成 (p,q) 顺序的矩阵。
转置是普通转置，不是共轭转置；辛条件是 Mᵀ J M = J。
-/

noncomputable section

namespace KamProject.Arnold1963

/-- 固定 (p,q) 顺序：论文 Σ dp∧dq 的矩阵是 mathlib.J 的负矩阵。 -/
theorem symplecticMatrix_eq_neg_mathlibJ (n : ℕ) :
    symplecticMatrix n = -Matrix.J (Fin n) ℂ := rfl

/-- 同时改变辛形式两边的符号不改变保持辛形式的条件。 -/
theorem symplectic_matrix_identity_iff_mathlib {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :
    M.transpose * symplecticMatrix n * M = symplecticMatrix n ↔
      M.transpose * Matrix.J (Fin n) ℂ * M = Matrix.J (Fin n) ℂ := by
  simp only [symplecticMatrix, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def phaseCoordinate {n : ℕ} (v : ComplexPhaseSpace n) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim v.1 v.2

def phaseLinearMatrix {n : ℕ} (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fun i j => phaseCoordinate (A (phaseDirection j)) i

theorem phaseLinearMatrix_symplectic_apply {n : ℕ}
    (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) (i j : Fin n ⊕ Fin n) :
    ((phaseLinearMatrix A).transpose * symplecticMatrix n * phaseLinearMatrix A) i j =
      symplecticForm (A (phaseDirection i)) (A (phaseDirection j)) := by
  simp [Matrix.mul_apply, Matrix.transpose_apply,
    phaseLinearMatrix, phaseCoordinate, Finset.sum_add_distrib, symplecticForm,
    neg_mul, sub_eq_add_neg, add_comm]

theorem IsSymplecticLinear.matrix_identity {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    (phaseLinearMatrix A).transpose * symplecticMatrix n * phaseLinearMatrix A =
      symplecticMatrix n := by
  ext i j
  rw [phaseLinearMatrix_symplectic_apply, hA]
  exact (symplecticMatrix_apply i j).symm

end KamProject.Arnold1963
