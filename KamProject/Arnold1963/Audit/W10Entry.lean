import KamProject.Arnold1963.W10

/-! 仅导入 W10 的公开接口审计；一般维数和一般原始资料不依赖审计样例。 -/
open KamProject.Arnold1963
open scoped NNReal

#check theorem1
#check theorem1_of_pointwise
#check Theorem1Result
#check KAMTorus
#check Theorem1Result.pairwise_disjoint
#check Theorem1Result.realization
#check Theorem1Result.good_large
#check Theorem1Result.bad_small
#check Theorem1Result.global_orbits
#check FiniteLocalization.tori_eq_of_intersection
#check FiniteLocalization.goodSet_eq_sUnion_tori
#check Iteration.InitialData.projected_orbit_closure
#check denseRange_realTorusLine

example {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result n H₀ G ρ κ f) := theorem1 h hρ hκ

example {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      (∀ z ∈ phaseDomain G ρ, ‖f.toFun z‖ < M) → Nonempty (Theorem1Result n H₀ G ρ κ f) :=
  theorem1_of_pointwise h hρ hκ

/-- 闭包与实开集的体积确实相同；此事实不代替域正则性输入本身。 -/
example {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) :
    MeasureTheory.volume (realSlice G) = MeasureTheory.volume h.realOpen := by
  apply MeasureTheory.measure_congr
  apply MeasureTheory.ae_eq_set.mpr
  exact ⟨h.real_boundary_null, by
    rw [Set.sdiff_eq_empty.mpr h.realOpen_subset, MeasureTheory.measure_empty]⟩
