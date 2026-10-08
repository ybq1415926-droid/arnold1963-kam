# Arnold 1963 KAM 的 Lean 4 形式化

本项目正在准备发布 v1.0.0。作者已按照明确的自然语言定理完成主体语义自查及审计实例核对。项目已有 Lean 构建与公理审计通过记录；作者自查不等同于独立人工复核或正式同行评审。

**上一存档版本：**[v0.1.0，DOI：10.5281/zenodo.23201478](https://doi.org/10.5281/zenodo.23201478)，发布于 2026 年 10 月 7 日。
[项目整体 DOI](https://doi.org/10.5281/zenodo.23201477) 标识整个版本系列。v1.0.0 的版本 DOI 将在存档后补充。

作者：**Bingqi Yu，Jilin University**。
[ORCID](https://orcid.org/0009-0000-4646-1791) · [GitHub](https://github.com/ybq1415926-droid)。
开发使用了 AI 辅助，具体分工见 [Provenance](docs/PROVENANCE.md)。

## 数学范围

本项目参考 Arnold 1963 年经典论文，在当前明确列出的假设下，形式化一个基本非退化解析 Hamiltonian KAM 定理。采用明确的域正则性条件及相应估计，不声明与原文全部假设、结论范围或证明步骤完全一致。内容包括实际迭代、解析不变环面、原始 Hamiltonian 系统的全时间轨道、跨局部图的环面不交性与全局测度结论。等能推广、退化情形和重刚体应用不在本次范围内。

完整自然语言陈述见[英文定理 PDF](docs/Arnold1963_Main_Theorem_Code_Aligned_EN.pdf)及其[LaTeX 源码](docs/Arnold1963_Main_Theorem_Code_Aligned_EN.tex)。扰动阈值可以依赖预先给定的未扰动系统、几何域、复角带宽度 `ρ` 和测度误差比例 `κ`，但不依赖扰动本身。最终环面接口要求频率不存在非零整数关系；本次不额外要求定量丢番图条件，也不包含 Lagrangian 性质的声明。

据作者目前所知，尚未发现更早公开完成的、包含不变环面与大测度结论的一般基本非退化解析 Hamiltonian KAM 定理的 Lean 形式化。这是基于目前检索的限定性首创判断，并非已经确认的全球优先权结论；欢迎提供可比较的先行工作。检索范围见[审核状态与证据](docs/REVIEW_STATUS.md)。

主定理为 `KamProject.Arnold1963.theorem1`，见
[Main/Theorem1.lean](KamProject/Arnold1963/Main/Theorem1.lean)。
阅读时应同时核查 `GlobalHamiltonianData`、`AnalyticPhaseFunction`、`KAMTorus` 和 `Theorem1Result`，不能只凭定理名称判断已经形式化的内容。

[英文首页](README.md) 收录入口与定理签名；[Scope](docs/SCOPE.md) 列出精确假设、范数、周期、索引及工作包对应关系。

## 编译和审计

版本固定为 Lean 4.33.1、mathlib v4.33.1；不需要升级依赖。环境具备后，在仓库根目录运行：

```text
lake build
lake env lean KamProject/Arnold1963/Audit/W10.lean
lake env lean KamProject/Arnold1963/Audit/W10Entry.lean
```

完整逐模块检查使用 `python scripts/verify.py --all`。详见
[Reproducibility](docs/REPRODUCIBILITY.md)。

公开候选包保留 191 个 Lean 文件与 3 个版本配置文件，均与 2026-10-04 的验证基线逐字节一致。该日已有全部 191 模块构建成功记录；32 条主要声明的递归公理审计仅使用 `propext`、`Classical.choice`、`Quot.sound`。源码扫描没有发现 `sorry`、`admit`、`native_decide` 或显式 `axiom` 标记。

初始公开源码提交 `0e1151b` 已通过 GitHub Actions 的构建和公理审计。2026-10-08 的本地复查再次通过实例相关构建，并重新运行 W10 审计，核对全部 32 条预期声明。W9Example 的直接检查在一次工具链文件读取失败后单独重试通过。

作者已按当前明确陈述的定理完成语义自查及审计实例核对。实例使用一自由度、全局频率不单射的双分支模型和非恒定扰动，证明两侧各有非空不交环面；它不替代一般维数定理的证明，也不是多自由度小除数现象的实例展示。详见[审核状态与证据](docs/REVIEW_STATUS.md)。准备发布的 v1.0.0 提交仍应通过其对应的 CI 检查。

## 引用和许可

代码与仓库说明采用 [Apache-2.0](LICENSE)。引用信息见 [CITATION.cff](CITATION.cff)。旧版本 v0.1.0 的引用为：

Bingqi Yu. (2026). *Arnold 1963 KAM in Lean 4* (v0.1.0) [Computer software]. Zenodo. https://doi.org/10.5281/zenodo.23201478

数学原文：V. I. Arnol'd, Russian Mathematical Surveys **18**(5), 9–36 (1963)，
[DOI](https://doi.org/10.1070/RM1963v018n05ABEH004130)。
原论文与未公开的工作参考稿未包含在此代码包中。
