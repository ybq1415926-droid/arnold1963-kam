import Mathlib

namespace KamProject

example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  exact lt_of_le_of_lt h₁ h₂

end KamProject
