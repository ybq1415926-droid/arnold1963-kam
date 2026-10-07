import KamProject.Arnold1963.W10
import KamProject.Arnold1963.Audit.W9Example

/-! 沿用全域频率不单射的双分支 H₀=p³/3 与域内非恒定小扰动。
本轮将该真实输入送入完整主定理，检查输出而非另设一个有利的零扰动样例。
-/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W10Example
open W9Example
local instance w10ExamplePeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def result : Theorem1Result 1 cubic ambient 1 (1 / 2) perturbation :=
  localization.theorem1Result cubic_original_data.compact perturbation perturbation_bound

theorem original_data_threshold :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction 1 ambient 1,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result 1 cubic ambient 1 (1 / 2) f) :=
  theorem1 cubic_original_data (by norm_num) (by norm_num)

theorem actual_disjoint_tori : result.tori.Pairwise Disjoint := result.pairwise_disjoint

theorem actual_torus_realization (T : Set (RealPhaseSpace 1)) (hT : T ∈ result.tori) :
    Nonempty (KAMTorus 1 cubic perturbation.toFun ambient result.width (1 / 2) T) :=
  result.realization T hT

theorem actual_good_nonempty : result.goodSet.Nonempty := result.good_nonempty

theorem actual_large_measure : ENNReal.ofReal (1 / 2 : ℝ) *
    volume (realSlice ambient ×ˢ (univ : Set (RealTorus 1))) < volume result.goodSet := by
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using result.good_large

theorem actual_bad_measure : volume result.badSet < ENNReal.ofReal (1 / 2 : ℝ) *
    volume (realSlice ambient ×ˢ (univ : Set (RealTorus 1))) := result.bad_small

end KamProject.Arnold1963.Audit.W10Example
