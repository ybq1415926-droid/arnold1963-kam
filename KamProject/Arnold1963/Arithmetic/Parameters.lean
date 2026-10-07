import KamProject.Arnold1963.Arithmetic.Estimates
import Mathlib.Tactic.Positivity

/-! 2026-09-15 校订版本的常数和阈值。指数依用途分别命名。
T=8n+24 及 threshold5 的四项最小值均见原文 §2.2（印刷页 16）；
原文 §3.3 式 (9) 的指数平衡由 budget_exponent_identity / budget_step_eq 核验。
校订版的加强基本引理预算确保代入 m=2M 后精确衔接此原有数列。
-/
noncomputable section
namespace KamProject.Arnold1963

def arithmeticExponent (n : ℕ) : ℕ := n + 1
def homologicalExponent (n : ℕ) : ℕ := 2 * n + 1
def stepExponent (n : ℕ) : ℕ := 2 * n + 3
def iterationExponent (n : ℕ) : ℕ := 8 * n + 24

def constantL0 (n : ℕ) : ℝ := ((n + 1 : ℝ) / Real.exp 1) ^ (n + 1)
def constantL5 (n : ℕ) : ℝ := 4 ^ n * constantL0 n
def constantL2 (n : ℕ) : ℝ := 16 * n * constantL5 n
def constantL3 (n : ℕ) : ℝ := (1 / 2 : ℝ) * n ^ 2 * constantL5 n ^ 2
def constantL4 (n : ℕ) : ℝ := 2 * ((2 * n : ℝ) / Real.exp 1) ^ n

def threshold0 (n : ℕ) (Θ : ℝ) : ℝ :=
  min (1 / 12) (min (constantL2 n)⁻¹ (min ((constantL3 n)⁻¹ * Θ⁻¹) (constantL4 n)⁻¹))
def threshold1 (n : ℕ) (θ Θ : ℝ) : ℝ := min (threshold0 n (2 * Θ)) (θ / (2 * n))
def threshold2 (n : ℕ) (κ ρ : ℝ) : ℝ :=
  min (((10 : ℝ) ^ (4 * n))⁻¹ * ρ ^ (4 * n)) (min ((4 : ℝ) ^ (4 * n))⁻¹ κ)
def threshold3 (n : ℕ) (θ Θ κ D : ℝ) : ℝ :=
  min (Real.exp (2 * n) / (32 * n ^ 2 + 100 * n) ^ (2 * n))
    (min (1 / (6 + 14 * Θ)) (((4 : ℝ) ^ (n + 2))⁻¹ * κ * θ ^ n / (Θ ^ n * D * n)))
def threshold4 (κ θ : ℝ) : ℝ := κ / (2 + θ⁻¹)
def threshold5 (n : ℕ) (θ Θ ρ κ D : ℝ) : ℝ :=
  min (threshold1 n (θ / 2) (2 * Θ))
    (min (threshold2 n κ ρ) (min (threshold3 n θ Θ κ D) (threshold4 κ θ)))

theorem constants_pos {n : ℕ} (hn : 0 < n) :
    0 < constantL0 n ∧ 0 < constantL5 n ∧ 0 < constantL2 n ∧
      0 < constantL3 n ∧ 0 < constantL4 n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [constantL0, constantL5, constantL2, constantL3, constantL4]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem threshold0_pos {n : ℕ} (hn : 0 < n) {Θ : ℝ} (hΘ : 0 < Θ) :
    0 < threshold0 n Θ := by
  obtain ⟨_, _, h2, h3, h4⟩ := constants_pos hn
  unfold threshold0
  positivity

theorem threshold1_pos {n : ℕ} (hn : 0 < n) {θ Θ : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) : 0 < threshold1 n θ Θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_min (threshold0_pos hn (by positivity)) (by positivity)

theorem threshold0_bounds {n : ℕ} {Θ δ : ℝ} (h : δ < threshold0 n Θ) :
    δ < 1 / 12 ∧ δ < (constantL2 n)⁻¹ ∧
      δ < (constantL3 n)⁻¹ * Θ⁻¹ ∧ δ < (constantL4 n)⁻¹ := by
  simpa only [threshold0, lt_min_iff] using h

/-- 阈值确实提供基本引理三个预算因子的严格小量条件。 -/
theorem threshold0_budget_conditions {n : ℕ} (hn : 0 < n) {Θ δ : ℝ}
    (hΘ : 0 < Θ) (hδ : δ < threshold0 n Θ) :
    δ < 1 / 12 ∧ δ * constantL2 n < 1 ∧
      δ * (constantL3 n * Θ) < 1 ∧ δ * constantL4 n < 1 := by
  obtain ⟨hsmall, h2, h3, h4⟩ := threshold0_bounds hδ
  obtain ⟨_, _, hL2, hL3, hL4⟩ := constants_pos hn
  refine ⟨hsmall, ?_, ?_, ?_⟩
  · exact (lt_div_iff₀ hL2).mp (by simpa only [one_div] using h2)
  · exact (lt_div_iff₀ (mul_pos hL3 hΘ)).mp (by
      simpa only [one_div, mul_inv] using h3)
  · exact (lt_div_iff₀ hL4).mp (by simpa only [one_div] using h4)

theorem threshold1_bounds {n : ℕ} {θ Θ δ : ℝ} (h : δ < threshold1 n θ Θ) :
    δ < threshold0 n (2 * Θ) ∧ δ < θ / (2 * n) := lt_min_iff.mp h

theorem threshold5_bounds {n : ℕ} {θ Θ ρ κ D δ : ℝ}
    (h : δ < threshold5 n θ Θ ρ κ D) :
    δ < threshold1 n (θ / 2) (2 * Θ) ∧ δ < threshold2 n κ ρ ∧
      δ < threshold3 n θ Θ κ D ∧ δ < threshold4 κ θ := by
  simpa only [threshold5, lt_min_iff] using h

theorem threshold2_pos (n : ℕ) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    0 < threshold2 n κ ρ := by
  unfold threshold2
  positivity

theorem threshold3_pos {n : ℕ} (hn : 0 < n) {θ Θ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < threshold3 n θ Θ κ D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold threshold3
  positivity

theorem threshold4_pos {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    0 < threshold4 κ θ := by unfold threshold4; positivity

theorem threshold5_pos {n : ℕ} (hn : 0 < n) {θ Θ ρ κ D : ℝ}
    (hθ : 0 < θ) (hΘ : 0 < Θ) (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < threshold5 n θ Θ ρ κ D := by
  exact lt_min (threshold1_pos hn (by positivity) (by positivity))
    (lt_min (threshold2_pos n hκ hρ)
      (lt_min (threshold3_pos hn hθ hΘ hκ hD) (threshold4_pos hκ hθ)))

/-- 阈值只依赖固定数据；这里没有扰动函数参数。 -/
def initialPerturbationThreshold (n : ℕ) (θ Θ ρ κ D : ℝ) : ℝ :=
  (threshold5 n θ Θ ρ κ D / 2) ^ iterationExponent n

theorem initialPerturbationThreshold_pos {n : ℕ} (hn : 0 < n)
    {θ Θ ρ κ D : ℝ} (hθ : 0 < θ) (hΘ : 0 < Θ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (hD : 0 < D) :
    0 < initialPerturbationThreshold n θ Θ ρ κ D := by
  have := threshold5_pos hn hθ hΘ hρ hκ hD
  unfold initialPerturbationThreshold
  positivity

theorem strengthened_budget_two_mul (M δ β : ℝ) (n : ℕ) :
    (1 / 4 : ℝ) * (2 * M) ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2) =
      M ^ 2 / (δ ^ (2 * stepExponent n) * β ^ 2) := by ring

theorem budget_exponent_identity (n : ℕ) :
    2 * iterationExponent n = 2 * stepExponent n + 6 + (12 * n + 36) := by
  unfold iterationExponent stepExponent
  omega

/-- 先用自然数幂核验二次余项预算，不依赖任何 KAM 分析结论。 -/
theorem budget_step_eq {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (δ ^ iterationExponent n) ^ 2 / (δ ^ (2 * stepExponent n) * (δ ^ 3) ^ 2) =
      δ ^ (12 * n + 36) := by
  apply (div_eq_iff (by positivity : δ ^ (2 * stepExponent n) * (δ ^ 3) ^ 2 ≠ 0)).mpr
  simp only [← pow_mul, ← pow_add]
  congr 1
  unfold iterationExponent stepExponent
  omega

end KamProject.Arnold1963
