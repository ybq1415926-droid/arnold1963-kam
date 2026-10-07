import KamProject.Arnold1963.Basic.Domains
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# 实截面的体积

明确使用 Fin n → ℝ 上各坐标 Lebesgue 测度的乘积。
复域的 `realVolume` 测量的是其实截面，绝非 ℂⁿ 上的 2n 维体积。
保留 ℝ≥0∞ 值域；以后只有在证明有限性后才使用 toReal。
本文件区分作用体积、物理角基本区域体积与单位周期坐标体积。
未在此证明任意初始作用域的正性、有限性或一般周期集合的商测度换元。
-/

noncomputable section

open scoped ENNReal

namespace KamProject.Arnold1963

def realLebesgue (n : ℕ) : MeasureTheory.Measure (RealSpace n) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ))

instance realLebesgue_sigmaFinite (n : ℕ) : MeasureTheory.SigmaFinite (realLebesgue n) :=
  inferInstanceAs (MeasureTheory.SigmaFinite
    (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ))))

def realVolume {n : ℕ} (G : Set (ComplexSpace n)) : ℝ≥0∞ :=
  realLebesgue n (realSlice G)

/-- 论文中的紧作用域给出实空间中的 Borel 可测实截面。 -/
theorem measurableSet_realSlice_of_isCompact {n : ℕ} {G : Set (ComplexSpace n)}
    (hG : IsCompact G) : MeasurableSet (realSlice G) :=
  (isCompact_realSlice hG).isClosed.measurableSet

theorem realVolume_mono {n : ℕ} {G H : Set (ComplexSpace n)} (hGH : G ⊆ H) :
    realVolume G ≤ realVolume H :=
  MeasureTheory.measure_mono (Set.preimage_mono hGH)

/-- 半开角基本区域；L=2π 是物理角坐标，L=1 是归一化积分坐标。 -/
def realAngleCell (n : ℕ) (L : ℝ) : Set (RealSpace n) :=
  Set.pi Set.univ (fun _ => Set.Ioc 0 L)

def realPhaseLebesgue (n : ℕ) : MeasureTheory.Measure (RealSpace n × RealSpace n) :=
  (realLebesgue n).prod (realLebesgue n)

theorem realLebesgue_angleCell (n : ℕ) (L : ℝ) :
    realLebesgue n (realAngleCell n L) = ENNReal.ofReal L ^ n := by
  simp [realLebesgue, realAngleCell, MeasureTheory.Measure.pi_pi, Real.volume_Ioc]

/-- 相空间的基本区域体积 = 作用截面体积 × 每个角坐标的长度的 n 次幂。 -/
theorem realPhaseLebesgue_cell {n : ℕ} (G : Set (ComplexSpace n)) (L : ℝ) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n L) =
      realVolume G * ENNReal.ofReal L ^ n := by
  rw [realPhaseLebesgue, MeasureTheory.Measure.prod_prod, realLebesgue_angleCell]
  rfl

theorem realPhaseLebesgue_physicalCell {n : ℕ} (G : Set (ComplexSpace n)) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n (2 * Real.pi)) =
      realVolume G * ENNReal.ofReal (2 * Real.pi) ^ n := realPhaseLebesgue_cell G _

theorem realPhaseLebesgue_unitCell {n : ℕ} (G : Set (ComplexSpace n)) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n 1) = realVolume G := by
  simpa using realPhaseLebesgue_cell G 1

end KamProject.Arnold1963
