import KamProject.Arnold1963.Analysis
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Matrix.Normed

/-!
2026-09-22：在锁定版本上核查后续库接口。
只验证这些声明可用，不宣称项目已经完成周期、测度、范数或解析域的转换。
不打开任何 Matrix.Norms 范数作用域，不修改公共范数实例。
-/

#check UnitAddTorus.mFourierCoeff
#check UnitAddTorus.mFourierCoeff_eq_integral
#check UnitAddTorus.hasSum_mFourier_series_L2
#check UnitAddTorus.hasSum_mFourier_series_of_summable
#check UnitAddTorus.hasSum_mFourier_series_apply_of_summable
#check Matrix.linfty_opNorm_def
#check Matrix.norm_entry_le_entrywise_sup_norm

#print axioms UnitAddTorus.hasSum_mFourier_series_of_summable
#print axioms UnitAddTorus.hasSum_mFourier_series_apply_of_summable
