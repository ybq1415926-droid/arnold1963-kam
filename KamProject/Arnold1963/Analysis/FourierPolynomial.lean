import KamProject.Arnold1963.Arithmetic.Lattice
import KamProject.Arnold1963.Basic.Domains
import Mathlib.Analysis.Complex.Trigonometric

/-!
# 有限 Fourier 截断及单项范数界

系数是输入 aₖ；本文件不将任意系数族冒充已证明的 Fourier 积分系数。
完整截断使用 fourierModes（含零模），非零求和使用 lowModes。
指标长度始终为 indexLength 的 ℓ¹ 长度，角带使用虚部的最大范数。
-/

noncomputable section
namespace KamProject.Arnold1963

def fourierMonomial {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) : ℂ :=
  Complex.exp (Complex.I * indexPairing k q)

def fourierTruncation {n : ℕ} (a : FourierIndex n → ℂ) (N : ℝ)
    (q : ComplexSpace n) : ℂ :=
  ∑ k ∈ fourierModes n N, a k * fourierMonomial k q

@[simp] theorem fourierMonomial_zero {n : ℕ} (q : ComplexSpace n) :
    fourierMonomial 0 q = 1 := by
  simp [fourierMonomial, indexPairing]

/-- N>0 时完整截断等于平均项加非零低频项。 -/
theorem fourierTruncation_eq_zero_add {n : ℕ} (a : FourierIndex n → ℂ)
    {N : ℝ} (hN : 0 < N) (q : ComplexSpace n) :
    fourierTruncation a N q = a 0 + ∑ k ∈ lowModes n N, a k * fourierMonomial k q := by
  classical
  rw [fourierTruncation, fourierModes_eq_insert_lowModes n hN,
    Finset.sum_insert (by simp [indexLength])]
  simp

theorem norm_fourierMonomial_le {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    ‖fourierMonomial k q‖ ≤ Real.exp (indexLength k * ‖imagPart q‖) := by
  rw [fourierMonomial, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have him : (Complex.I * indexPairing k q).re =
      -(∑ j, (k j : ℝ) * (q j).im) := by
    simp [indexPairing, Complex.mul_re, Complex.mul_im]
  rw [him]
  calc
    _ ≤ |∑ j, (k j : ℝ) * (q j).im| := neg_le_abs _
    _ ≤ ∑ j, |(k j : ℝ) * (q j).im| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(k j : ℝ)| * ‖imagPart q‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [imagPart, Real.norm_eq_abs] using norm_le_pi_norm (imagPart q) j
    _ = indexLength k * ‖imagPart q‖ := by rw [indexLength, Finset.sum_mul]

/-- 缩窄角带后，系数衰减与单项增长抵消为 exp(-δ|k|₁)。 -/
theorem norm_fourierTerm_le {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ : ℝ} (hM : 0 ≤ M)
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ)))
    {q : ComplexSpace n} (hq : ‖imagPart q‖ ≤ ρ - δ) (k : FourierIndex n) :
    ‖a k * fourierMonomial k q‖ ≤ M * Real.exp (-(indexLength k * δ)) := by
  rw [norm_mul]
  calc
    _ ≤ (M * Real.exp (-(indexLength k * ρ))) *
        Real.exp (indexLength k * ‖imagPart q‖) :=
      mul_le_mul (ha k) (norm_fourierMonomial_le k q) (norm_nonneg _)
        (mul_nonneg hM (Real.exp_pos _).le)
    _ = M * Real.exp (-(indexLength k * ρ) + indexLength k * ‖imagPart q‖) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ M * Real.exp (-(indexLength k * δ)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hq (indexLength_nonneg k)]

theorem norm_fourierTruncation_le {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ : ℝ} (hM : 0 ≤ M)
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ)))
    {q : ComplexSpace n} (hq : ‖imagPart q‖ ≤ ρ - δ) (N : ℝ) :
    ‖fourierTruncation a N q‖ ≤
      M * ∑ k ∈ fourierModes n N, Real.exp (-(indexLength k * δ)) := by
  calc
    _ ≤ ∑ k ∈ fourierModes n N, ‖a k * fourierMonomial k q‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ fourierModes n N, M * Real.exp (-(indexLength k * δ)) :=
      Finset.sum_le_sum fun k _ => norm_fourierTerm_le hM ha hq k
    _ = _ := (Finset.mul_sum _ _ _).symm

end KamProject.Arnold1963
