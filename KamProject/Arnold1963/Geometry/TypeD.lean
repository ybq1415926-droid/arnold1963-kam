import KamProject.Arnold1963.Geometry.Polydisc

/-! 校订版 §4.1.1 的 D 型条件。这里是域的性质，不是频率变化结论的假设包。 -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- 实系数线性形式的复延拓；对偶大小为 ℓ¹，不使用系数的默认最大范数。 -/
def realCovectorPairing {n : ℕ} (ℓ : RealSpace n) (z : ComplexSpace n) : ℂ :=
  ∑ j, (ℓ j : ℂ) * z j

def covectorLength {n : ℕ} (ℓ : RealSpace n) : ℝ := ∑ j, |ℓ j|

/-- 复管道在实截面上是开条带。a 是线性形式的阈值，几何全宽为 2a/|ℓ|₁。 -/
def complexSlab {n : ℕ} (ℓ : RealSpace n) (c a : ℝ) : Set (ComplexSpace n) :=
  {z | ‖realCovectorPairing ℓ z - (c : ℂ)‖ < a}

structure TypeD {n : ℕ} (Ω : Set (ComplexSpace n)) (D : ℝ) : Prop where
  constant_pos : 0 < D
  compact : IsCompact Ω
  volume_pos : 0 < realVolume Ω
  boundary : ∀ d₁ d₂ : ℝ≥0, d₁ ≤ d₂ →
    realVolume (erosion Ω d₁ \ erosion Ω d₂) ≤
      ENNReal.ofReal (D * ((d₂ : ℝ) - d₁)) * realVolume Ω
  slab : ∀ (ℓ : RealSpace n) (c a : ℝ), 0 < covectorLength ℓ → 0 ≤ a →
    realVolume (Ω ∩ complexSlab ℓ c a) ≤
      ENNReal.ofReal (D * n * (2 * a / covectorLength ℓ)) * realVolume Ω

theorem realVolume_biUnion_finset_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Set (ComplexSpace n)) :
    realVolume (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, realVolume (f i) := by
  unfold realVolume realSlice
  simp only [preimage_iUnion]
  exact measure_biUnion_finset_le s _

end KamProject.Arnold1963
