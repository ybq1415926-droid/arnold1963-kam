import KamProject.Arnold1963.Basic

/-!
# 公共对象层的集成与公理检查

检查最大范数与 ℓ¹ 长度的区别，并在非空域上构造非零解析函数、验证其范数。
这些是对象约定的校准，不是 KAM 主定理或非退化性实例。
通过 `lake env lean KamProject/Arnold1963/Audit/Basic.lean` 查看实际输出。
-/

open scoped NNReal

namespace KamProject.Arnold1963.Audit

example : indexLength (fun _ : Fin 2 => (1 : ℤ)) = 2 := by
  simp [indexLength]

example : ‖(fun _ : Fin 2 => (1 : ℂ))‖ = 1 := by simp

example :
    (AnalyticPhaseFunction.constReal (Set.univ : Set (ComplexSpace 1)) 1
      (fun _ _ => Set.mem_univ _) 1).uniformNorm = 1 := by
  simpa using AnalyticPhaseFunction.uniformNorm_constReal
    (Set.univ : Set (ComplexSpace 1)) 1 (fun _ _ => Set.mem_univ _)
    ⟨0, Set.mem_univ _⟩ 1

#check ComplexSpace
#check erosion
#check AnalyticPhaseFunction
#check AnalyticPhaseFunction.norm_le_iff
#print axioms norm_indexPairing_le
#print axioms erosion_inter
#print axioms analyticOnNhd_iff_exists_open
#print axioms supNorm_lt_iff
#print axioms AnalyticPhaseFunction.norm_le_iff
#print axioms AnalyticPhaseFunction.real_value
#print axioms AnalyticPhaseFunction.uniformNorm_constReal
#print axioms realVolume_mono

end KamProject.Arnold1963.Audit
