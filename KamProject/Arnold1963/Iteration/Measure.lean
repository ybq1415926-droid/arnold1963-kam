import KamProject.Arnold1963.Step.MeasureBudget

/-! W6a 的累计测度层：所有损失均以固定的初始作用域 G 0 为参照。
这里只累加调用者已经证明的单步损失；具体 AR 系数的无穷和留给数值闭合层。
不把有限域或极限域非空作为假设。
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KamProject.Arnold1963.Iteration

theorem finite_loss_le {n : ℕ} (G : ℕ → Set (ComplexSpace n)) (b : ℕ → ℝ≥0∞)
    (hstep : ∀ s, realVolume (G s \ G (s + 1)) ≤ b s * realVolume (G 0)) (s : ℕ) :
    realVolume (G 0 \ G s) ≤ (∑ j ∈ Finset.range s, b j) * realVolume (G 0) := by
  induction s with
  | zero => simp [realVolume, realSlice]
  | succ s ih =>
    have hc : realSlice (G 0 \ G (s + 1)) ⊆
        realSlice (G 0 \ G s) ∪ realSlice (G s \ G (s + 1)) := by
      intro x hx
      by_cases hs : complexify x ∈ G s
      · exact Or.inr ⟨hs, hx.2⟩
      · exact Or.inl ⟨hx.1, hs⟩
    have hh := (measure_mono (μ := realLebesgue n) hc).trans (measure_union_le _ _)
    change realVolume (G 0 \ G (s + 1)) ≤
      realVolume (G 0 \ G s) + realVolume (G s \ G (s + 1)) at hh
    rw [Finset.sum_range_succ, add_mul]
    exact hh.trans (add_le_add ih (hstep s))

/-- 可数次损失覆盖极限损失；外测度的次可加性已经足够，无隐含可测性假设。 -/
theorem limit_loss_le {n : ℕ} (G : ℕ → Set (ComplexSpace n)) (b : ℕ → ℝ≥0∞)
    (hstep : ∀ s, realVolume (G s \ G (s + 1)) ≤ b s * realVolume (G 0)) :
    realVolume (G 0 \ ⋂ s, G s) ≤ (∑' s, b s) * realVolume (G 0) := by
  have hc : realSlice (G 0 \ ⋂ s, G s) ⊆ ⋃ s, realSlice (G s \ G (s + 1)) := by
    intro x hx
    by_contra h
    have hs : ∀ s, complexify x ∈ G s := by
      intro s
      induction s with
      | zero => exact hx.1
      | succ s ih =>
        by_contra hn
        exact h (mem_iUnion_of_mem s ⟨ih, hn⟩)
    exact hx.2 (mem_iInter.mpr hs)
  calc
    _ ≤ ∑' s, realVolume (G s \ G (s + 1)) :=
      (measure_mono (μ := realLebesgue n) hc).trans (measure_iUnion_le _)
    _ ≤ ∑' s, b s * realVolume (G 0) := ENNReal.tsum_le_tsum hstep
    _ = _ := ENNReal.tsum_mul_right

/-- 严格总预算推出极限正体积及非空。初始正体积、有限性必须明确提供。 -/
theorem limit_positive_of_budget {n : ℕ} (G : ℕ → Set (ComplexSpace n))
    (b : ℕ → ℝ≥0∞) {κ : ℝ≥0∞}
    (hstep : ∀ s, realVolume (G s \ G (s + 1)) ≤ b s * realVolume (G 0))
    (hsum : (∑' s, b s) < κ) (hκ : κ < 1)
    (hpos : 0 < realVolume (G 0)) (hfinite : realVolume (G 0) ≠ ⊤) :
    realVolume (G 0 \ ⋂ s, G s) < κ * realVolume (G 0) ∧
      0 < realVolume (⋂ s, G s) ∧ (realSlice (⋂ s, G s)).Nonempty := by
  have hl := (limit_loss_le G b hstep).trans_lt
    (ENNReal.mul_lt_mul_left hpos.ne' hfinite hsum)
  have hκG : κ * realVolume (G 0) < realVolume (G 0) := by
    simpa only [one_mul] using ENNReal.mul_lt_mul_left hpos.ne' hfinite hκ
  have hp := realVolume_pos_of_loss_lt (hl.trans hκG)
  exact ⟨hl, hp, realSlice_nonempty_of_realVolume_pos hp⟩

end KamProject.Arnold1963.Iteration
