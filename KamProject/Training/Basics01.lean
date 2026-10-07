import Mathlib.Data.Real.Basic

/-!
# 第 1 课：读懂目标，使用已有引理

配合 Mathematics in Lean 第 2 章。学习路线及自测题见同目录 README.md。
把光标放在每条 tactic 后，观察 Lean Infoview 中的目标变化。
这些 example 是完整示范；读完后可遮住证明，在同一文件末尾重写。
-/

namespace KamProject.Training.Basics01

-- 1. a、b、c 是实数；h₁、h₂ 是假设的名字；冒号后的 a < c 是目标。
-- exact 接受一个类型与当前目标匹配的证明。
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  exact lt_of_le_of_lt h₁ h₂

-- 2. apply 从结论倒推前提。这里显式指定中间点 b。
-- 两个 · 分别处理 a ≤ b 和 b < c；缩进决定各分支的范围。
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  apply lt_of_le_of_lt (b := b)
  · exact h₁
  · exact h₂

-- 3. calc 从已知关系向前串联。第二行的 _ 接续上一行右端的 b。
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  calc
    a ≤ b := h₁
    _ < c := h₂

-- 4. rw 使用等式改写。第一步将目标里的 x 替换为 y。
-- 第二步使用 add_zero，完成 y + 0 = y。
example (x y : ℝ) (h : x = y) : x + 0 = y := by
  rw [h]
  rw [add_zero]

-- 5. ← 反向使用等式：把目标里的 y 替换为 x。
example (x y : ℝ) (h : x = y) : y + 0 = x := by
  rw [← h]
  rw [add_zero]

-- 6. 为将来的误差估计练习“传递界”。这只是基础不等式，不是 KAM 定理。
example (err bound ε : ℝ) (hbound : err ≤ bound) (hsmall : bound < ε) :
    err < ε := by
  exact lt_of_le_of_lt hbound hsmall

-- 可以取消下面某一行的注释，查看引理类型；看完后再注释回去。
-- #check lt_of_le_of_lt
-- #check lt_of_lt_of_le
-- #check add_zero

end KamProject.Training.Basics01
