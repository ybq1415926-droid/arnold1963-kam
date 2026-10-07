import KamProject.Arnold1963.Geometry.Erosion
import KamProject.Arnold1963.Basic.Measure
import Mathlib.Tactic

/-! 实中心闭复多圆盘及其侵蚀的实截面。空间范数始终为坐标最大模范数。 -/
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- 允许一般实半径以精确表达侵蚀；负半径使相应坐标条件为空。 -/
def realCenteredPolydisc {n : ℕ} (c r : RealSpace n) : Set (ComplexSpace n) :=
  {z | ∀ j, ‖z j - (c j : ℂ)‖ ≤ r j}

theorem realSlice_realCenteredPolydisc {n : ℕ} (c r : RealSpace n) :
    realSlice (realCenteredPolydisc c r) =
      pi univ (fun j => Icc (c j - r j) (c j + r j)) := by
  ext x
  simp only [realSlice, mem_preimage, realCenteredPolydisc, mem_ofPred_eq,
    complexify, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    mem_univ_pi, mem_Icc, abs_le]
  exact forall_congr' fun j => by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem isClosed_realCenteredPolydisc {n : ℕ} (c r : RealSpace n) :
    IsClosed (realCenteredPolydisc c r) := by
  have he : realCenteredPolydisc c r =
      ⋂ j, {z : ComplexSpace n | ‖z j - (c j : ℂ)‖ ≤ r j} := by
    ext z
    simp [realCenteredPolydisc]
  rw [he]
  exact isClosed_iInter fun j => isClosed_le
    (((continuous_apply j).sub continuous_const).norm) continuous_const

theorem isCompact_realCenteredPolydisc {n : ℕ} (c r : RealSpace n) :
    IsCompact (realCenteredPolydisc c r) := by
  have he : realCenteredPolydisc c r = pi univ (fun j => closedBall (c j : ℂ) (r j)) := by
    ext z
    simp [realCenteredPolydisc, mem_closedBall, dist_eq_norm]
  rw [he]
  exact isCompact_univ_pi fun j => isCompact_closedBall _ _

theorem realVolume_realCenteredPolydisc {n : ℕ} (c r : RealSpace n) :
    realVolume (realCenteredPolydisc c r) = ∏ j, ENNReal.ofReal (2 * r j) := by
  rw [realVolume, realSlice_realCenteredPolydisc]
  simp only [realLebesgue, Measure.pi_pi, Real.volume_Icc]
  congr 1
  funext j
  congr 1
  ring

/-- 只限制到实截面之后使用 ±实半径端点；不把实球误作整个复球。 -/
theorem mem_realSlice_erosion_polydisc {n : ℕ} (c r : RealSpace n)
    (t : ℝ≥0) (x : RealSpace n) :
    x ∈ realSlice (erosion (realCenteredPolydisc c r) t) ↔
      ∀ j, |x j - c j| + (t : ℝ) ≤ r j := by
  change complexify x ∈ erosion (realCenteredPolydisc c r) t ↔ _
  constructor
  · intro hx j
    have hp : complexify x + Pi.single j (t : ℂ) ∈
        closedBall (complexify x) (t : ℝ) := by
      simp [mem_closedBall, dist_eq_norm, Pi.norm_single]
    have hm : complexify x - Pi.single j (t : ℂ) ∈
        closedBall (complexify x) (t : ℝ) := by
      simp [mem_closedBall, Pi.norm_single]
    have hplus := hx hp j
    have hminus := hx hm j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, complexify,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hplus hminus
    have hp' := (abs_le.mp hplus).2
    have hm' := (abs_le.mp hminus).1
    have habs : |x j - c j| ≤ r j - t := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · intro hx y hy j
    have hd : ‖y j - (x j : ℂ)‖ ≤ (t : ℝ) :=
      (norm_le_pi_norm (y - complexify x) j).trans
        (by simpa only [mem_closedBall, dist_eq_norm] using hy)
    calc
      ‖y j - (c j : ℂ)‖ ≤ ‖y j - (x j : ℂ)‖ + ‖(x j : ℂ) - (c j : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ t + |x j - c j| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        linarith
      _ ≤ r j := by linarith [hx j]

theorem realSlice_erosion_polydisc {n : ℕ} (c r : RealSpace n) (t : ℝ≥0) :
    realSlice (erosion (realCenteredPolydisc c r) t) =
      realSlice (realCenteredPolydisc c (fun j => r j - t)) := by
  ext x
  rw [mem_realSlice_erosion_polydisc]
  change _ ↔ ∀ j, ‖(x j : ℂ) - (c j : ℂ)‖ ≤ r j - t
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact forall_congr' fun j => by constructor <;> intro h <;> linarith

/-- 适用于全部 t≥0；ofReal 自动给出 (rⱼ−t)₊，不假设侵蚀仍有内点。 -/
theorem realVolume_erosion_polydisc {n : ℕ} (c r : RealSpace n) (t : ℝ≥0) :
    realVolume (erosion (realCenteredPolydisc c r) t) =
      ∏ j, ENNReal.ofReal (2 * (r j - t)) := by
  rw [realVolume, realSlice_erosion_polydisc]
  exact realVolume_realCenteredPolydisc c _

end KamProject.Arnold1963
