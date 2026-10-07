import KamProject.Arnold1963.Analysis.FourierTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases

/-! 在 KAM 已有 δ≤1/12 的范围内，把已证的尾界接回原文常数；不改变参数账本。 -/
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

theorem kernel_constant_le_arnold {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 12) :
    (4 / δ) ^ n ≤ ((2 * n : ℝ) / Real.exp 1) ^ n / δ ^ (n + 1) := by
  have hc : δ * (4 : ℝ) ^ n ≤ ((2 * n : ℝ) / 3) ^ n := by
    by_cases hlarge : 6 ≤ n
    · have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hlarge
      calc
        _ ≤ (4 : ℝ) ^ n := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n]
        _ ≤ ((2 * n : ℝ) / 3) ^ n := pow_le_pow_left₀ (by norm_num) (by linarith) n
    · interval_cases n <;> norm_num at hn ⊢ <;> nlinarith
  have hb : ((2 * n : ℝ) / 3) ^ n ≤ ((2 * n : ℝ) / Real.exp 1) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1) Real.exp_one_lt_three.le
  have h := hc.trans hb
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < δ ^ (n + 1))).mpr
  have he : (4 / δ) ^ n * δ ^ (n + 1) = δ * 4 ^ n := by
    rw [div_pow, pow_succ]
    field_simp
  rwa [he]

/-- 原文尾界常数的 KAM 适用版本：额外小量条件来自 δ⁽⁰⁾≤1/12。
仍是系数衰减下的级数尾界；识别为原函数的尾项必须调用重构定理。 -/
theorem norm_fourierSeries_tail_le_arnoldConstant {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ γ N : ℝ} {σ : ℝ≥0} (hn : 0 < n) (hM : 0 ≤ M)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 12) (hγ : 0 ≤ γ)
    (hσ : (σ : ℝ) ≤ ρ - (δ + γ))
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ))) :
    ‖(∑' k, fourierTermOnStrip a σ k) -
        ∑ k ∈ fourierModes n N, fourierTermOnStrip a σ k‖ ≤
      (((2 * n : ℝ) / Real.exp 1) ^ n * M / δ ^ (n + 1)) * Real.exp (-N * γ) := by
  have h := norm_fourierSeries_tail_le_of_decay (N := N) hM hδ (by linarith) hγ hσ ha
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (kernel_constant_le_arnold hn hδ hsmall)
    (show 0 ≤ M * Real.exp (-N * γ) by positivity)
  convert hb using 1
  ring

end KamProject.Arnold1963
