import KamProject.Arnold1963.Geometry.LocalizationCover
import KamProject.Arnold1963.Main.LocalThreshold

/-! 原文 §3.4 1°–2° 的有限覆盖及扰动无关阈值。
每块允许不同 θ、Θ、D；统一角宽取 min ρ 1，扰动界取有限族的共同正下界。
局部测度损失先按块数分配，不能将重叠覆盖的体积直接相加当作并集体积。
-/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- 全部字段由 `exists_finiteLocalization` 构造。它是中间输出，不是原始定理假设。 -/
structure FiniteLocalization (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (ambient : Set (ComplexSpace n)) (ρ : ℝ≥0) (κ : ℝ) where
  dimension_pos : 0 < n
  patches : Finset (HamiltonianPatch n H₀ ambient)
  width : ℝ≥0
  width_pos : 0 < width
  width_le_one : width ≤ 1
  width_le : width ≤ ρ
  fraction : ℝ
  fraction_pos : 0 < fraction
  fraction_lt_one : fraction < 1
  fraction_le : fraction ≤ κ
  coverError : ℝ
  coverError_pos : 0 < coverError
  coverError_lt_one : coverError < 1
  cover : volume (realSlice ambient \ ⋃ c ∈ patches, realSlice c.domain) <
    ENNReal.ofReal coverError * volume (realSlice ambient)
  budget : coverError + (patches.card : ℝ) * fraction ≤ κ
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_le : ∀ c ∈ patches, threshold ≤ c.threshold width fraction

/-- 先固定 n,G,H₀,ρ,κ，才构造所有块和正阈值；量词中没有 H₁。 -/
theorem GlobalHamiltonianData.exists_finiteLocalization {n : ℕ}
    {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ ambient) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) : Nonempty (FiniteLocalization n H₀ ambient ρ κ) := by
  let τ := min κ 1
  have hτ : 0 < τ := lt_min hκ zero_lt_one
  have hτκ : τ ≤ κ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  obtain ⟨s, hs⟩ := h.exists_cover (τ / 4) (by positivity)
  let η := τ / (4 * ((s.card : ℝ) + 1))
  have hm : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hd : 0 < 4 * ((s.card : ℝ) + 1) := by positivity
  have hη : 0 < η := div_pos hτ hd
  have heq : η * (4 * ((s.card : ℝ) + 1)) = τ := div_mul_cancel₀ _ hd.ne'
  have hη1 : η < 1 := by nlinarith
  have hητ : η ≤ τ := by nlinarith
  have hb : τ / 4 + (s.card : ℝ) * η ≤ κ := by nlinarith
  have hw : (0 : ℝ≥0) < min ρ 1 := lt_min hρ zero_lt_one
  obtain ⟨M, hM, hMs⟩ := HamiltonianPatch.exists_common_threshold s h.dimension_pos hw hη
  exact ⟨{
    dimension_pos := h.dimension_pos
    patches := s
    width := min ρ 1
    width_pos := hw
    width_le_one := min_le_right _ _
    width_le := min_le_left _ _
    fraction := η
    fraction_pos := hη
    fraction_lt_one := hη1
    fraction_le := hητ.trans hτκ
    coverError := τ / 4
    coverError_pos := by positivity
    coverError_lt_one := by linarith
    cover := hs
    budget := hb
    threshold := M
    threshold_pos := hM
    threshold_le := hMs }⟩

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)

theorem parameters (c : L.patches) :
    Iteration.InitialParameters n (c.val.seed L.width L.fraction)
      c.val.lower c.val.upper L.width L.fraction c.val.typeConstant :=
  c.val.parameters L.dimension_pos L.width_pos L.width_le_one L.fraction_pos L.fraction_lt_one

def data (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) :=
  c.val.initialData L.dimension_pos L.width_pos L.fraction_pos f L.width_le
    (hf.trans (L.threshold_le c c.property))

/-- 完整 W8 局部输出来自同一个初始 H₀+H₁ 的限制。 -/
theorem local_result (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) : LocalKAMResult (L.parameters c) (L.data f hf c) := localKAM _ _

/-- 重叠块间也是同一个原始 Hamiltonian；限制操作保留全函数值。 -/
theorem hamiltonian_zero (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)
    (c : L.patches) (z : ComplexPhaseSpace n) :
    (L.data f hf c).hamiltonian (L.parameters c) 0 z = H₀ z.1 + f.toFun z := rfl

/-- 非空性由实际覆盖的严格测度预算推出，不预设某个分支存在。 -/
theorem patches_nonempty : L.patches.Nonempty := by
  classical
  by_contra he
  have hempty : L.patches = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hh := L.cover
  simp only [hempty, Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty] at hh
  have hle : ENNReal.ofReal L.coverError * volume (realSlice ambient) ≤
      volume (realSlice ambient) := by
    calc
      _ ≤ 1 * volume (realSlice ambient) :=
        mul_le_mul' (ENNReal.ofReal_le_one.mpr L.coverError_lt_one.le) le_rfl
      _ = _ := one_mul _
  exact (not_lt_of_ge hle) hh

end FiniteLocalization
end KamProject.Arnold1963
