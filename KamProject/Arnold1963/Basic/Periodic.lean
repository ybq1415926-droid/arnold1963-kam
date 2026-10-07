import KamProject.Arnold1963.Basic.Domains
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# 2π 周期与实角环面

解析估计在复覆盖空间进行；`RealTorus` 仅用于实角变量。
`AnglePeriodicOn` 只约束所指定域上的函数值，不对域外任意延拓作要求。
本文件尚不实现函数下降、环面测度或 Fourier 积分；不能将这些视为已证。
-/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

abbrev RealTorus (n : ℕ) := Fin n → AddCircle (2 * Real.pi)
abbrev RealPhaseSpace (n : ℕ) := RealSpace n × RealTorus n

/-- 覆盖空间中的角平移 2πk；每个分量是实数嵌入 ℂ。 -/
def angleShift {n : ℕ} (k : FourierIndex n) : ComplexSpace n :=
  complexify (fun j => 2 * Real.pi * (k j : ℝ))

def AnglePeriodicOn {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0)
    (f : ComplexPhaseSpace n → ℂ) : Prop :=
  ∀ p ∈ G, ∀ q ∈ angleStrip n ρ, ∀ k : FourierIndex n,
    f (p, q + angleShift k) = f (p, q)

@[simp] theorem imagPart_add_angleShift {n : ℕ} (q : ComplexSpace n)
    (k : FourierIndex n) : imagPart (q + angleShift k) = imagPart q := by
  funext j
  simp [imagPart, angleShift, complexify]

/-- 周期平移保持复角带，因此周期条件两端均在同一解析域内。 -/
theorem add_angleShift_mem_iff {n : ℕ} (q : ComplexSpace n) (k : FourierIndex n)
    (ρ : ℝ≥0) : q + angleShift k ∈ angleStrip n ρ ↔ q ∈ angleStrip n ρ := by
  simp [angleStrip]

end KamProject.Arnold1963
