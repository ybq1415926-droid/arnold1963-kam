import KamProject.Arnold1963.Main.TorusResult
import KamProject.Arnold1963.Tori.CrossChart

/-! Arnold 1963 §§2–4 的非退化解析 KAM 主定理。
原始资料先构造统一正阈值；任意足够小的真实扰动得到两两不交的解析环面族。
所有输出从 W0–W9 的证明与跨图轨道闭包定理构造，没有把环面不交或存在性作为输入。
-/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
local instance theorem1PeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- 直接使用原始 H₀、H₁、G、ρ、κ 的输出规格，不要求用户提供任何局部频率图。
`tori` 按实际集合标记；不同频率分支中相同的集合只保留一次。
-/
structure Theorem1Result (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (G : Set (ComplexSpace n)) (ρ : ℝ≥0) (κ : ℝ)
    (f : AnalyticPhaseFunction n G ρ) where
  width : ℝ≥0
  width_pos : 0 < width
  width_le : width ≤ ρ
  goodSet : Set (RealPhaseSpace n)
  badSet : Set (RealPhaseSpace n)
  tori : Set (Set (RealPhaseSpace n))
  good_compact : IsCompact goodSet
  good_measurable : MeasurableSet goodSet
  bad_measurable : MeasurableSet badSet
  partition : goodSet ∪ badSet = realSlice G ×ˢ (univ : Set (RealTorus n))
  disjoint_partition : Disjoint goodSet badSet
  good_volume_pos : 0 < volume goodSet
  good_nonempty : goodSet.Nonempty
  good_large : ENNReal.ofReal (1 - κ) *
    volume (realSlice G ×ˢ (univ : Set (RealTorus n))) < volume goodSet
  bad_small : volume badSet < ENNReal.ofReal κ *
    volume (realSlice G ×ˢ (univ : Set (RealTorus n)))
  union_eq : goodSet = ⋃₀ tori
  pairwise_disjoint : tori.Pairwise Disjoint
  realization : ∀ T ∈ tori, Nonempty (KAMTorus n H₀ f.toFun G width κ T)
  global_orbits : ∀ z ∈ goodSet, ∃ γ : ℝ → ComplexPhaseSpace n,
    torusProjection (realPartPhase (γ 0)) = z ∧
    (∀ t, HasDerivAt γ (hamiltonianVectorField (fun w => H₀ w.1 + f.toFun w) (γ t)) t) ∧
    (∀ t, complexifyPhase (realPartPhase (γ t)) = γ t) ∧
    (∀ t, torusProjection (realPartPhase (γ t)) ∈ goodSet)

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ G ρ κ)

theorem goodSet_volume_gt (hG : IsCompact G) (f : AnalyticPhaseFunction n G ρ)
    (hf : f.uniformNorm ≤ L.threshold) :
    ENNReal.ofReal (1 - κ) * volume L.phase < volume (L.goodSet f hf) := by
  by_cases hκ : κ < 1
  · have hκ0 : 0 ≤ κ := (L.fraction_pos.trans_le L.fraction_le).le
    have hV := L.phase_volume_finite hG
    have hK := ne_top_of_le_ne_top hV (measure_mono (L.goodSet_subset f hf))
    have hκV : ENNReal.ofReal κ * volume L.phase ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV
    have he : ENNReal.ofReal (1 - κ) * volume L.phase +
        ENNReal.ofReal κ * volume L.phase = volume L.phase := by
      rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.mpr hκ.le) hκ0,
        sub_add_cancel, ENNReal.ofReal_one, one_mul]
    have hm := measure_union (μ := volume) (L.partition f hf).2 (L.badSet_measurable hG f hf)
    rw [(L.partition f hf).1] at hm
    apply (ENNReal.add_lt_add_iff_right hκV).mp
    rw [he]
    calc
      volume L.phase = volume (L.goodSet f hf) + volume (L.badSet f hf) := hm
      _ < volume (L.goodSet f hf) + ENNReal.ofReal κ * volume L.phase :=
        ENNReal.add_lt_add_left hK (L.badSet_volume_lt hG f hf)
  · rw [ENNReal.ofReal_of_nonpos (by linarith : 1 - κ ≤ 0), zero_mul]
    exact L.goodSet_volume_pos f hf

/-- 将实际有限局部化输出交给完整主定理规格，去重不改变好集或测度预算。 -/
def theorem1Result (hG : IsCompact G) (f : AnalyticPhaseFunction n G ρ)
    (hf : f.uniformNorm ≤ L.threshold) : Theorem1Result n H₀ G ρ κ f where
  width := L.width / 6
  width_pos := div_pos L.width_pos (by norm_num)
  width_le := (div_le_self (zero_le : 0 ≤ L.width) (by norm_num : (1 : ℝ≥0) ≤ 6)).trans
    L.width_le
  goodSet := L.goodSet f hf
  badSet := L.badSet f hf
  tori := L.tori f hf
  good_compact := L.goodSet_compact f hf
  good_measurable := (L.goodSet_compact f hf).isClosed.measurableSet
  bad_measurable := L.badSet_measurable hG f hf
  partition := (L.partition f hf).1
  disjoint_partition := (L.partition f hf).2
  good_volume_pos := L.goodSet_volume_pos f hf
  good_nonempty := nonempty_of_measure_ne_zero (L.goodSet_volume_pos f hf).ne'
  good_large := L.goodSet_volume_gt hG f hf
  bad_small := L.badSet_volume_lt hG f hf
  union_eq := L.goodSet_eq_sUnion_tori f hf
  pairwise_disjoint := L.tori_pairwise_disjoint f hf
  realization := by
    rintro T ⟨c, p, hp, rfl⟩
    exact ⟨L.torusResult f hf c hp⟩
  global_orbits := fun _ hz => L.exists_global_orbit f hf hz

end FiniteLocalization

/-- 主体非退化解析 KAM 定理：M 在 H₁ 之前选择，依赖固定的原始资料。
M 是各局部阈值的共同正下界；结论不要求它是最大的下界。
假设为 GlobalHamiltonianData 中的闭域实现：实截面是非空开集的闭包，边界零测，
实内点有复邻域，H₀ 解析保实且 Hessian 在这些实内点非退化。
原文 §4.5 本身约定 G 为紧复区域；实截面的明确正则性条件采用校订稿 §2.1。
此接口不声称任意开域或任意紧集都能自动转换成 GlobalHamiltonianData。
-/
theorem theorem1 {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result n H₀ G ρ κ f) := by
  obtain ⟨L⟩ := h.exists_finiteLocalization hρ hκ
  exact ⟨L.threshold, L.threshold_pos, fun f hf => ⟨L.theorem1Result h.compact f hf⟩⟩

/-- 原文的逐点严格小性版本；只推出一致范数 ≤ M，不错误地提升为一致范数 < M。 -/
theorem theorem1_of_pointwise {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      (∀ z ∈ phaseDomain G ρ, ‖f.toFun z‖ < M) → Nonempty (Theorem1Result n H₀ G ρ κ f) := by
  obtain ⟨M, hM, hmain⟩ := theorem1 h hρ hκ
  refine ⟨M, hM, fun f hf => hmain f ?_⟩
  exact f.norm_le_iff.mpr ⟨hM.le, fun z hz => (hf z hz).le⟩

end KamProject.Arnold1963
