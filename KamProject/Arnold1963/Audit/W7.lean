import KamProject.Arnold1963.W7
import KamProject.Arnold1963.Audit.W6Example

set_option linter.style.header false

/-! 真实非恒定扰动的贯通检查；新结论不由零扰动例子替代。 -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace KamProject.Arnold1963.Audit.W7
open Iteration W6Completion

/-- 最终轨道方程使用原输入 Hamiltonian，并非另造的极限 Hamiltonian。 -/
example {n : ℕ} {Ω : Set (ComplexSpace n)} {δ θ Θ ρ : ℝ≥0} {κ D : ℝ}
    (b : InitialParameters n δ θ Θ ρ κ D) (h : InitialData n Ω δ θ Θ ρ D)
    (z : ComplexPhaseSpace n) : h.vectorField b 0 z =
      hamiltonianVectorField (fun w => h.integrable w.1 + h.perturbation.toFun w) z := rfl

/-- 原文的参数编号相对 Lean 步参数有 +1，而初始状态仍为 0。 -/
example (δ : ℝ≥0) : delta δ 0 = δ := decay_zero δ
example : iterationExponent 1 = 32 := rfl
example : initialData.cumulative parameters 0 = id := rfl

/-- 正体积、有限体积均从 InitialData 推出；不再是结构构造时提供的字段。 -/
example : 0 < realVolume initialData.domain := initialData.volume_pos
example : realVolume initialData.domain ≠ ⊤ := initialData.volume_finite

example : TendstoUniformlyOn (initialData.cumulative parameters)
    (initialData.limitMap parameters) atTop (initialData.limitPhase parameters) :=
  initialData.cumulative_uniform parameters

theorem nonconstant_input : perturbation.toFun (0, 0) ≠
    perturbation.toFun (0, fun _ => (Real.pi : ℂ)) := nonconstant

/-- 非空标签来自 W6 的严格总预算。对每个角和每个实时间均得到原方程的解。 -/
theorem exists_real_global_orbit : ∃ p ∈ realSlice (initialData.limitDomain parameters),
    ∀ q : RealSpace 1, ∀ t : ℝ,
      HasDerivAt (initialData.orbit parameters p q)
        (initialData.vectorField parameters 0 (initialData.orbit parameters p q t)) t ∧
      complexifyPhase (realPartPhase (initialData.orbit parameters p q t)) =
        initialData.orbit parameters p q t := by
  obtain ⟨p, hp⟩ := limit_nonempty
  exact ⟨p, hp, fun q t => ⟨initialData.orbit_hasDerivAt parameters hp q t,
    initialData.orbit_real_value parameters hp q t⟩⟩

example {p : ComplexSpace 1} (hp : p ∈ initialData.limitDomain parameters)
    (k : FourierIndex 1) (hk : k ≠ 0) :
    indexPairing k (initialData.limitFrequency parameters p) ≠ 0 :=
  initialData.limitFrequency_no_integer_relation parameters hp k hk

end KamProject.Arnold1963.Audit.W7

open KamProject.Arnold1963 Iteration
#print InitialData
#check InitialData.cumulative_uniform
#check InitialData.limitFrequency_nonresonant
#check InitialData.limitMap_line_analytic
#check InitialData.orbit_hasDerivAt
#check InitialData.orbit_mem_torus_image
#print axioms InitialData.volume_pos
#print axioms InitialData.volume_finite
#print axioms theorem2
#print axioms InitialData.cumulative_uniform
#print axioms InitialData.limitMap_maps
#print axioms InitialData.limitMap_periodic
#print axioms InitialData.limitMap_real_value
#print axioms InitialData.limitFrequency_nonresonant
#print axioms InitialData.limitMap_line_analytic
#print axioms InitialData.orbit_hasDerivAt
#print axioms InitialData.orbit_mem_torus_image
#print axioms limsup_measure_image_le
#print axioms Audit.W7.exists_real_global_orbit
