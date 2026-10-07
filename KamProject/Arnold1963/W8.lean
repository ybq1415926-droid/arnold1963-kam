import KamProject.Arnold1963.W7
import KamProject.Arnold1963.Main.LocalKAM

set_option linter.style.header false

/-! W8 交付入口：从同一个 W6 初始数据构造的局部解析不变环面族。
localKAM 汇总频率单射、解析覆盖提升、浸入、周期拓扑嵌入、角投影全局可逆、
不同标签不交、重标记后 κ 小性、实际全时间 Hamilton 轨道和严格物理测度分解。
Main/LocalKAM 另提供显式频率参数化及 q+tω 公式。

范数仍是复坐标最大模、乘积最大范数及其诱导算子范数；Fourier 长度保持 ℓ¹。
周期仍为 2π，商上 volume 未归一化。代码 beta δ₁ 0 是论文 β₁。
本入口只完成一个初始解析频率图内的局部定理，W9 的局部覆盖与完整定理 1 仍待证明。
这里指一对数值参数相匹配的 Iteration.InitialParameters 与 Iteration.InitialData：
前者给出小量等数值条件，后者提供实际 Hamiltonian、解析频率图和初始域。
解析嵌入以周期复解析提升、单射微分及商上的 IsClosedEmbedding 表达；
不另引入或声称已建立 mathlib 流形解析性实例。

仅 import KamProject.Arnold1963.W8 即可通过传递导入使用下列声明，
无需另行导入其定义文件；本入口不重复定义或另建别名。
- KamProject.Arnold1963.localKAM
- KamProject.Arnold1963.LocalKAMResult
- KamProject.Arnold1963.Iteration.InitialData.frequencyParameterization_eq
- KamProject.Arnold1963.Iteration.InitialData.frequency_orbit
- KamProject.Arnold1963.Iteration.InitialData.torusEmbedding_isClosedEmbedding
- KamProject.Arnold1963.Iteration.InitialData.torusEmbedding_lift
- KamProject.Arnold1963.Iteration.InitialData.torusAngleHomeomorph
- KamProject.Arnold1963.Iteration.InitialData.localF1_compact
- KamProject.Arnold1963.Iteration.InitialData.local_partition
- KamProject.Arnold1963.Iteration.InitialData.localF2_volume_lt
- KamProject.Arnold1963.Iteration.InitialData.torusLimitMap_volume_gt

审计文件：KamProject/Arnold1963/Audit/W8Completion.lean，含非恒定扰动实例及
31 条公理输出；原 26 条、复核补充的 4 个结论和域内非恒定性见证各自有实际记录。
最新输出：Audit/w8-review-20261003-axioms-output.txt；复核说明：W8SemanticReview.md。
本入口不导入审计文件，以免其反向导入 W8 造成循环依赖。
-/
