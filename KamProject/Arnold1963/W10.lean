import KamProject.Arnold1963.W9
import KamProject.Arnold1963.Main.Theorem1

set_option linter.style.header false

/-!
W10 完整主定理入口（固定的闭域实现与原始非退化假设见 `GlobalHamiltonianData`）。

- `KamProject.Arnold1963.theorem1`：统一正阈值先于扰动；输出 `Theorem1Result`。
- `KamProject.Arnold1963.theorem1_of_pointwise`：原文逐点严格小性的直接版本。
- `KamProject.Arnold1963.KAMTorus`：同一解析提升、周期嵌入、角解析逆、原始频率中心、
  非共振频率、两块 κ 小位移和全实时间原 Hamilton 方程。
- `KamProject.Arnold1963.FiniteLocalization.tori_eq_of_intersection`：跨图相交必重合。

好集按实际环面集合去重，保留并集和原物理测度，所得不同环面两两不交。
原有 W9 覆盖结论继续保留；这里补齐其跨图缺口，不假设全局频率单射。
范数、严格 Fourier 截断和代码 0 ↔ 论文第 1 步的约定沿用既有公共基础。
范围是 §§2–4 的基本非退化解析 KAM 定理，不包含等能推广、退化情形及重刚体应用。
原文 §2.1 脚注的等能非退化推广也未包含。G 为紧复区域遵循原文 §4.5；
实截面闭包、边界零测和复内点条件采用校订稿明确的正则性假设。
-/
