import KamProject.Arnold1963.W8

/-! 只导入 W8 的调用验证；没有绕过入口另导入 Main/LocalKAM 或样例模块。
维数和 κ 保持一般，只通过原有初始参数假设约束。
-/
open Set
open scoped NNReal
namespace KamProject.Arnold1963.Audit.W8Entry

example {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
    (b : Iteration.InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
    (h : Iteration.InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D) : LocalKAMResult b h := localKAM b h

#check KamProject.Arnold1963.Iteration.InitialData.frequencyParameterization_eq
#check KamProject.Arnold1963.Iteration.InitialData.frequency_orbit
#check KamProject.Arnold1963.Iteration.InitialData.torusEmbedding_isClosedEmbedding
#check KamProject.Arnold1963.Iteration.InitialData.torusEmbedding_lift
#check KamProject.Arnold1963.Iteration.InitialData.torusAngleHomeomorph
#check KamProject.Arnold1963.Iteration.InitialData.localF1_compact
#check KamProject.Arnold1963.Iteration.InitialData.local_partition
#check KamProject.Arnold1963.Iteration.InitialData.localF2_volume_lt
#check KamProject.Arnold1963.Iteration.InitialData.torusLimitMap_volume_gt

end KamProject.Arnold1963.Audit.W8Entry
