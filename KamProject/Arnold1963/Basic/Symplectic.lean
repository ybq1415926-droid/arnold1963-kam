import KamProject.Arnold1963.Basic.Spaces
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.Ring

/-!
# 有限维标准辛形式（校订版 §4.5）

坐标顺序仍为 (p,q)，ω = Σ dpⱼ ∧ dqⱼ，不改变最大范数。
`IsSymplecticLinear` 是保持具体双线性形式的等式，不是可任意填充的占位条件。
以下在线性层证明非退化性、保持辛形式的映射可逆以及协向量到向量的变换规律。
-/

noncomputable section

namespace KamProject.Arnold1963

def pDirection {n : ℕ} (j : Fin n) : ComplexPhaseSpace n := (Pi.single j 1, 0)
def qDirection {n : ℕ} (j : Fin n) : ComplexPhaseSpace n := (0, Pi.single j 1)

@[simp] theorem norm_pDirection {n : ℕ} (j : Fin n) : ‖pDirection j‖ = 1 := by
  simp [pDirection, Pi.norm_single]

@[simp] theorem norm_qDirection {n : ℕ} (j : Fin n) : ‖qDirection j‖ = 1 := by
  simp [qDirection, Pi.norm_single]

/-- 标准复双线性辛形式；不使用 Hermitian 共轭。 -/
def symplecticForm {n : ℕ} (v w : ComplexPhaseSpace n) : ℂ :=
  ∑ j, (v.1 j * w.2 j - v.2 j * w.1 j)

theorem phase_decomposition {n : ℕ} (v : ComplexPhaseSpace n) :
    v = (∑ j, v.1 j • pDirection j) + ∑ j, v.2 j • qDirection j := by
  simp only [pDirection, qDirection, Prod.smul_mk, smul_zero, ← prod_mk_sum]
  simp only [Finset.sum_const_zero, Prod.mk_add_mk, add_zero, zero_add]
  exact Prod.ext (pi_eq_sum_univ' v.1) (pi_eq_sum_univ' v.2)

@[simp] theorem symplecticForm_pDirection {n : ℕ} (j : Fin n)
    (w : ComplexPhaseSpace n) : symplecticForm (pDirection j) w = w.2 j := by
  simp [symplecticForm, pDirection, Pi.single_apply]

@[simp] theorem symplecticForm_qDirection {n : ℕ} (j : Fin n)
    (w : ComplexPhaseSpace n) : symplecticForm (qDirection j) w = -w.1 j := by
  simp [symplecticForm, qDirection, Pi.single_apply]

theorem symplecticForm_skew {n : ℕ} (v w : ComplexPhaseSpace n) :
    symplecticForm v w = -symplecticForm w v := by
  rw [symplecticForm, symplecticForm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem symplecticForm_self {n : ℕ} (v : ComplexPhaseSpace n) :
    symplecticForm v v = 0 := by simp [symplecticForm, mul_comm]

theorem symplecticForm_add_left {n : ℕ} (u v w : ComplexPhaseSpace n) :
    symplecticForm (u + v) w = symplecticForm u w + symplecticForm v w := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem symplecticForm_smul_left {n : ℕ} (c : ℂ) (v w : ComplexPhaseSpace n) :
    symplecticForm (c • v) w = c * symplecticForm v w := by
  simp only [symplecticForm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- 右变量的非退化性；等式可通过全部测试向量辨认。 -/
theorem symplecticForm_ext_right {n : ℕ} {u w : ComplexPhaseSpace n}
    (h : ∀ v, symplecticForm v u = symplecticForm v w) : u = w := by
  apply Prod.ext
  · funext j
    have hj := h (qDirection j)
    simpa using hj
  · funext j
    simpa using h (pDirection j)

/-- 协向量 L 对应的向量 (-L(e_q), L(e_p))。 -/
def symplecticSharp {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ) :
    ComplexPhaseSpace n := (fun j => -L (qDirection j), fun j => L (pDirection j))

theorem linearForm_decomposition {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ)
    (v : ComplexPhaseSpace n) :
    L v = (∑ j, v.1 j * L (pDirection j)) + ∑ j, v.2 j * L (qDirection j) := by
  conv_lhs => rw [phase_decomposition v]
  simp

/-- 符号校准：ω(v,sharp L)=L(v)，因而 ω(sharp L,v)=-L(v)。 -/
theorem symplecticForm_sharp {n : ℕ} (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ)
    (v : ComplexPhaseSpace n) : symplecticForm v (symplecticSharp L) = L v := by
  rw [linearForm_decomposition L v]
  simp [symplecticForm, symplecticSharp, Finset.sum_add_distrib]

def IsSymplecticLinear {n : ℕ} (A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n) :
    Prop := ∀ v w, symplecticForm (A v) (A w) = symplecticForm v w

theorem IsSymplecticLinear.injective {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    Function.Injective A := by
  intro x y hxy
  apply symplecticForm_ext_right
  intro v
  rw [← hA v x, ← hA v y, hxy]

theorem IsSymplecticLinear.surjective {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A) :
    Function.Surjective A := LinearMap.surjective_of_injective hA.injective

theorem IsSymplecticLinear.comp {n : ℕ}
    {A B : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n}
    (hA : IsSymplecticLinear A) (hB : IsSymplecticLinear B) :
    IsSymplecticLinear (A.comp B) := by
  intro v w
  exact (hA (B v) (B w)).trans (hB v w)

/-- 线性辛变换将拉回协向量对应的 Hamiltonian 向量送到原向量。 -/
theorem IsSymplecticLinear.map_sharp_comp {n : ℕ}
    {A : ComplexPhaseSpace n →ₗ[ℂ] ComplexPhaseSpace n} (hA : IsSymplecticLinear A)
    (L : ComplexPhaseSpace n →ₗ[ℂ] ℂ) :
    A (symplecticSharp (L.comp A)) = symplecticSharp L := by
  apply symplecticForm_ext_right
  intro v
  obtain ⟨w, rfl⟩ := hA.surjective v
  rw [hA, symplecticForm_sharp, symplecticForm_sharp]
  rfl

/-- 辛矩阵的实际系数，索引的左／右部分分别表示 p／q。 -/
def phaseDirection {n : ℕ} : Fin n ⊕ Fin n → ComplexPhaseSpace n
  | .inl j => pDirection j
  | .inr j => qDirection j

def symplecticMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  -Matrix.J (Fin n) ℂ

@[simp] theorem symplecticMatrix_pp {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inl i) (.inl j) = 0 := by
  simp [symplecticMatrix, Matrix.J]

@[simp] theorem symplecticMatrix_pq {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inl i) (.inr j) = if i = j then 1 else 0 := by
  simp [symplecticMatrix, Matrix.J, Matrix.one_apply]

@[simp] theorem symplecticMatrix_qp {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inr i) (.inl j) = -(if i = j then 1 else 0) := by
  simp [symplecticMatrix, Matrix.J, Matrix.one_apply]

@[simp] theorem symplecticMatrix_qq {n : ℕ} (i j : Fin n) :
    symplecticMatrix n (.inr i) (.inr j) = 0 := by
  simp [symplecticMatrix, Matrix.J]

/-- mathlib 的 J 采用相反符号；取负后仍对应本项目 Σ dp∧dq。 -/
theorem symplecticMatrix_apply {n : ℕ} (i j : Fin n ⊕ Fin n) :
    symplecticMatrix n i j = symplecticForm (phaseDirection i) (phaseDirection j) := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [phaseDirection, pDirection, qDirection, symplecticForm, Pi.single_apply, eq_comm]

end KamProject.Arnold1963
