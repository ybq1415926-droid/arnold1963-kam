import KamProject.Arnold1963.W9

/-! 仅导入 W9 的可调用性审计；不依赖审计样例导入数学实现。 -/
open KamProject.Arnold1963
open scoped NNReal

#check GlobalHamiltonianData
#check HamiltonianPatch.exists_at
#check HamiltonianPatch.exists_finite_cover
#check GlobalHamiltonianData.exists_finiteLocalization
#check HamiltonianPatch.initialData
#check HamiltonianPatch.local_result
#check FiniteLocalization.phase_cover
#check FiniteLocalization.badSet_volume_lt
#check FiniteLocalization.goodSet_eq_tori
#check FiniteLocalization.exists_global_orbit
#check global_kam_cover
#check localKAM

example {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) : Nonempty (FiniteLocalization n H₀ G ρ κ) :=
  h.exists_finiteLocalization hρ hκ
