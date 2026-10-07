import KamProject.Arnold1963.W8
import KamProject.Arnold1963.Main.GlobalCover

set_option linter.style.header false

/-!
W9 当前入口：原始非退化资料 → 实际局部频率图 → 有限近满测度覆盖 →
扰动无关共同正阈值 → 同一 Hamilton 系统的解析不变环面覆盖与全局坏集严格测度界。

主要公共声明（均位于 `KamProject.Arnold1963` 命名空间）：
- `KamProject.Arnold1963.GlobalHamiltonianData.exists_finiteLocalization`：先于扰动的有限局部化。
- `KamProject.Arnold1963.HamiltonianPatch.threshold_eq_initial_bound`：与 W8 初始扰动界精确衔接。
- `KamProject.Arnold1963.FiniteLocalization.phase_cover`：保留 (2π)^n 的物理相空间覆盖预算。
- `KamProject.Arnold1963.FiniteLocalization.badSet_volume_lt`：实际全局坏集严格测度界。
- `KamProject.Arnold1963.FiniteLocalization.goodSet_eq_tori`：按 (c,ω) 标记的环面并集。
- `KamProject.Arnold1963.FiniteLocalization.exists_global_orbit`：原始 Hamilton 系统的全时间轨道。
- `KamProject.Arnold1963.global_kam_cover`：量词为 ∃ L, ∀ f 的全局覆盖结论。

`Disjoint goodSet badSet` 只表示好集与其补集不交，不是不同环面之间的不交性。
范数、2π 周期和物理测度继承公共基础；每个局部块的迭代编号仍为代码 0 ↔ 论文第 1 步。

尚未交付完整 Theorem1Result：本轮有限覆盖可以重叠，跨图环面仍需匹配/去重并证明
互不相交。`LocalKAMResult.disjoint` 只在同一个局部图内有效，不得跨图套用。
因此没有将一个未经证明的全局不交分解命名为 theorem1。
-/
