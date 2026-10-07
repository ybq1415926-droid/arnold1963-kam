import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! 将 mathlib 的一致收敛级数用于实际映射的逐次差；保留可调用的尾差估计。 -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace KamProject.Arnold1963.Convergence

variable {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

def sequenceLimit (f : ℕ → α → E) (x : α) : E :=
  f 0 x + ∑' s, (f (s + 1) x - f s x)

theorem sequenceLimit_tendstoUniformlyOn {f : ℕ → α → E} {U : Set α} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ s x, x ∈ U → ‖f (s + 1) x - f s x‖ ≤ u s) :
    TendstoUniformlyOn f (sequenceLimit f) atTop U := by
  have hs := tendstoUniformlyOn_tsum_nat hu hf
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hs ε hε] with s hs x hx
  have he : f s x = f 0 x + ∑ j ∈ Finset.range s, (f (j + 1) x - f j x) := by
    rw [Finset.sum_range_sub (fun j => f j x)]
    abel
  rw [sequenceLimit, he, dist_add_left]
  exact hs x hx

theorem sequenceLimit_sub_eq_tsum {f : ℕ → α → E} {x : α} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ s, ‖f (s + 1) x - f s x‖ ≤ u s) (s : ℕ) :
    sequenceLimit f x - f s x = ∑' j, (f (j + s + 1) x - f (j + s) x) := by
  have hi := hu.of_norm_bounded hf
  have he := hi.sum_add_tsum_nat_add s
  rw [Finset.sum_range_sub (fun j => f j x)] at he
  unfold sequenceLimit
  rw [← he]
  abel

/-- 尾和从代码差分 s 开始。KAM 中取 u s = 2^s β_{s+1}，
换元 m = j+s+1 后正是论文从 m>s 开始的尾和；此引理不推出 U 非空。 -/
theorem sequenceLimit_tail_le {f : ℕ → α → E} {x : α} {u : ℕ → ℝ}
    (hu : Summable u) (hf : ∀ s, ‖f (s + 1) x - f s x‖ ≤ u s) (s : ℕ) :
    ‖sequenceLimit f x - f s x‖ ≤ ∑' j, u (j + s) := by
  rw [sequenceLimit_sub_eq_tsum hu hf s]
  exact tsum_of_norm_bounded ((summable_nat_add_iff s).mpr hu).hasSum (fun j => hf (j + s))

end KamProject.Arnold1963.Convergence
