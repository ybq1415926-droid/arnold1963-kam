import KamProject.Arnold1963.Analysis.SecondCauchy
import KamProject.Arnold1963.Analysis.DomainBuffer

/-! 相空间 (p,q) 的 2n 个坐标及二阶 Cauchy 界。坐标顺序不改变，
二阶坐标界为 2M/r²；这不是二阶算子范数的无维数界。 -/
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

def phaseBasis {n : ℕ} : Fin n ⊕ Fin n → ComplexPhaseSpace n
  | .inl j => (Pi.single j 1, 0)
  | .inr j => (0, Pi.single j 1)

theorem norm_phaseBasis {n : ℕ} (j : Fin n ⊕ Fin n) : ‖phaseBasis j‖ = 1 := by
  cases j <;> simp [phaseBasis, Pi.norm_single]

private theorem norm_single_add_le {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ‖(Pi.single i 1 : ComplexSpace n) + Pi.single j 1‖ ≤ 1 := by
  apply (complex_norm_le_iff _ zero_le_one).mpr
  intro k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

private theorem norm_single_sub_le {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ‖(Pi.single i 1 : ComplexSpace n) - Pi.single j 1‖ ≤ 1 := by
  apply (complex_norm_le_iff _ zero_le_one).mpr
  intro k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

theorem norm_phaseBasis_add_le {n : ℕ} {i j : Fin n ⊕ Fin n} (h : i ≠ j) :
    ‖phaseBasis i + phaseBasis j‖ ≤ 1 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [phaseBasis, phase_norm_eq] using norm_single_add_le (by simpa using h)
    | inr j => simp [phaseBasis, Pi.norm_single]
  | inr i =>
    cases j with
    | inl j => simp [phaseBasis, Pi.norm_single]
    | inr j => simpa [phaseBasis, phase_norm_eq] using norm_single_add_le (by simpa using h)

theorem norm_phaseBasis_sub_le {n : ℕ} {i j : Fin n ⊕ Fin n} (h : i ≠ j) :
    ‖phaseBasis i - phaseBasis j‖ ≤ 1 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [phaseBasis, phase_norm_eq] using norm_single_sub_le (by simpa using h)
    | inr j => simp [phaseBasis, Pi.norm_single]
  | inr i =>
    cases j with
    | inl j => simp [phaseBasis, Pi.norm_single]
    | inr j => simpa [phaseBasis, phase_norm_eq] using norm_single_sub_le (by simpa using h)

theorem norm_second_phaseCoordinate_le {n : ℕ} {f : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f U) (hM : NormBoundOn f U M)
    (hx : x ∈ erosion U r) (i j : Fin n ⊕ Fin n) :
    ‖fderiv ℂ (fderiv ℂ f) x (phaseBasis i) (phaseBasis j)‖ ≤ 2 * M / (r : ℝ) ^ 2 := by
  by_cases hij : i = j
  · subst j
    exact norm_second_fderiv_diag_le hr hf hM hx (norm_phaseBasis i).le
  · apply (norm_second_fderiv_mixed_le hr hf hM hx
      (norm_phaseBasis_add_le hij) (norm_phaseBasis_sub_le hij)).trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith [hM.nonneg]

/-- 邻域包含提供整个相空间的闭球缓冲，允许作用半径与角宽损失不同。 -/
theorem phaseDomain_buffer_of_neighborhood {n : ℕ} {S T : Set (ComplexSpace n)}
    {r σ τ : ℝ≥0} (hrσ : r ≤ σ) (hτσ : τ ≤ σ - r)
    (hST : closedBallNeighborhood S r ⊆ T) :
    phaseDomain S τ ⊆ erosion (phaseDomain T σ) r := by
  apply Subset.trans _ (phaseDomain_shrink_subset_erosion T hrσ)
  apply Set.prod_mono _ (angleStrip_mono hτσ)
  intro x hx y hy
  exact hST ⟨x, hx, hy⟩

end KamProject.Arnold1963
