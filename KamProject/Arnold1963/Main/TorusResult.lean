import KamProject.Arnold1963.Main.GlobalCover

/-! 主定理中单个解析不变环面的直接语义规格。
中心、频率、提升、商嵌入及角逆都是输出，并由同一个局部 KAM 极限实现。
-/
noncomputable section
open Set Function Topology
open scoped NNReal
namespace KamProject.Arnold1963

/-- `T` 是物理 2π 相空间中的实际集合；解析性由同一嵌入的复提升表达。
`center` 满足原始 H₀ 的频率方程，不能用极限作用标签替代。
-/
structure KAMTorus (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (H₁ : ComplexPhaseSpace n → ℂ) (ambient : Set (ComplexSpace n))
    (r : ℝ≥0) (κ : ℝ) (T : Set (RealPhaseSpace n)) where
  center : RealSpace n
  frequency : RealSpace n
  lift : ComplexSpace n → ComplexPhaseSpace n
  embedding : RealTorus n → RealPhaseSpace n
  angleInverse : ComplexSpace n → ComplexSpace n
  center_mem : center ∈ realSlice ambient
  frequency_eq : actionFrequency H₀ (complexify center) = complexify frequency
  nonresonance : ∀ k : FourierIndex n, k ≠ 0 → indexPairing k (complexify frequency) ≠ 0
  analytic : AnalyticOnNhd ℂ lift (angleStrip n r)
  periodic : ∀ q ∈ angleStrip n r, ∀ k : FourierIndex n,
    lift (q + angleShift k) = phaseShift k (lift q)
  real_value : ∀ q : RealSpace n,
    complexifyPhase (realPartPhase (lift (complexify q))) = lift (complexify q)
  embedding_lift : ∀ q : RealSpace n,
    embedding (fun j => (q j : AddCircle (2 * Real.pi))) =
      torusProjection (realPartPhase (lift (complexify q)))
  embedding_range : range embedding = T
  closedEmbedding : IsClosedEmbedding embedding
  immersion : ∀ q ∈ angleStrip n r, Injective (fderiv ℂ lift q)
  angle_homeomorph : ∃ e : RealTorus n ≃ₜ RealTorus n, ∀ Q, e Q = (embedding Q).2
  inverse_analytic : ∀ Q : RealSpace n, AnalyticAt ℂ angleInverse (complexify Q)
  inverse_left : ∀ q : RealSpace n, angleInverse (lift (complexify q)).2 = complexify q
  inverse_right : ∀ Q : RealSpace n, (lift (angleInverse (complexify Q))).2 = complexify Q
  displacement : ∀ q ∈ angleStrip n r,
    ‖(lift q).1 - complexify center‖ < κ ∧ ‖(lift q).2 - q‖ < κ
  orbit_equation : ∀ q : RealSpace n, ∀ t : ℝ,
    HasDerivAt (fun u : ℝ => lift (complexify (q + u • frequency)))
      (hamiltonianVectorField (fun z => H₀ z.1 + H₁ z)
        (lift (complexify (q + t • frequency)))) t
  orbit_mem : ∀ q : RealSpace n, ∀ t : ℝ,
    torusProjection (realPartPhase (lift (complexify (q + t • frequency)))) ∈ T

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)
  (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)

/-- W8 的实际输出装配为独立于迭代内部符号的主定理规格。
`L.parameters c` 与 `L.data f hf c` 的局部初始角宽 ρ₀ 定义性地就是 `L.width`，
并非原始输入 ρ；一般只知 `L.width ≤ ρ`。本输出的解析性和浸入性共用 `L.width/6`。
-/
def torusResult (c : L.patches) {p : RealSpace n}
    (hp : p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c))) :
    KAMTorus n H₀ f.toFun ambient (L.width / 6) κ
      ((L.data f hf c).invariantTorus (L.parameters c) p) := by
  let h := L.data f hf c
  let b := L.parameters c
  let ω := h.limitFrequency b (complexify p)
  let pc := h.unperturbedCenter ω
  have hstrip : angleStrip n (L.width / 6) ⊆
      Iteration.InitialData.commonAngleStrip n L.width :=
    Iteration.InitialData.thinAngleStrip_subset b
  have hpc : complexify (realPart pc) = pc := h.unperturbedCenter_real b hp
  have hω : complexify (realPart ω) = ω := h.limitFrequency_real_value b hp
  have ho (q : RealSpace n) : h.orbit b p q =
      fun t : ℝ => h.limitMap b (complexify p, complexify (q + t • realPart ω)) :=
    funext (h.orbit_eq_real_angle b hp q)
  refine {
    center := realPart pc
    frequency := realPart ω
    lift := fun q => h.limitMap b (complexify p, q)
    embedding := h.torusEmbedding b p
    angleInverse := h.complexAngleInverse b (complexify p)
    center_mem := ?_
    frequency_eq := ?_
    nonresonance := ?_
    analytic := (h.limitMap_angle_analytic b hp).mono hstrip
    periodic := ?_
    real_value := fun q => h.limitMap_real_value b (x := (p, q)) hp
    embedding_lift := h.torusEmbedding_lift b hp
    embedding_range := h.torusEmbedding_range b p
    closedEmbedding := h.torusEmbedding_isClosedEmbedding b hp
    immersion := fun _ hq => h.torusLift_derivative_injective b hp hq
    angle_homeomorph := ⟨h.torusAngleHomeomorph b hp, fun _ => rfl⟩
    inverse_analytic := h.complexAngleInverse_analytic_at_real b hp
    inverse_left := fun q => (h.complexAngleInverse_analytic b hp q).2.1
    inverse_right := ?_
    displacement := ?_
    orbit_equation := ?_
    orbit_mem := ?_ }
  · change complexify (realPart pc) ∈ ambient
    rw [hpc]
    -- 此处 h.domain 定义性等于 c.val.domain，即该图的 G₀，不是全局 ambient。
    have hlocal : pc ∈ c.val.domain := h.unperturbedCenter_mem b hp
    exact c.val.subset hlocal
  · rw [hpc, hω]
    exact h.chart.right (by simpa using h.limitFrequency_mem b hp 0)
  · intro k hk
    rw [hω]
    exact h.limitFrequency_no_integer_relation b hp k hk
  · intro q hq k
    exact h.limitMap_periodic b
      (h.angle_mem_limitPhase b hp (hstrip hq)) k
  · intro Q
    rw [h.complexAngleInverse_real_value b hp]
    change h.angleMap b (complexify p) (complexify (h.realAngleInverse b p Q)) = complexify Q
    rw [← h.angleMap_real_value b hp, h.realAngleInverse_right b hp]
  · intro q hq
    rw [hpc]
    exact L.corrections_small f hf c hp (hstrip hq)
  · intro q t
    have hh := L.orbit_original f hf c hp q t
    change HasDerivAt (h.orbit b p q)
      (hamiltonianVectorField (fun z => H₀ z.1 + f.toFun z) (h.orbit b p q t)) t at hh
    simpa only [ho q] using hh
  · intro q t
    have hh := h.orbit_mem_torus_image b hp q t
    simpa only [ho q, Iteration.InitialData.invariantTorus] using hh

end FiniteLocalization
end KamProject.Arnold1963
