# Arnold 1963 KAM 的 Lean 4 形式化

本项目公开的是供审阅的研究代码版本。Lean 机器检验已有通过记录，最终人工语义复核仍在进行，尚不声称完成同行评审或确立世界首次形式化。

**已存档版本：**[v0.1.0，DOI：10.5281/zenodo.23201478](https://doi.org/10.5281/zenodo.23201478)，发布于 2026 年 10 月 7 日。
引用这一版本时使用此 DOI；[项目整体 DOI](https://doi.org/10.5281/zenodo.23201477) 指向最新存档版本。

作者：**Bingqi Yu，Jilin University**。
[ORCID](https://orcid.org/0009-0000-4646-1791) · [GitHub](https://github.com/ybq1415926-droid)。
开发使用了 AI 辅助，具体分工见 [Provenance](docs/PROVENANCE.md)。

## 数学范围

目标是 Arnold 1963 年论文 §§2–4 的基本非退化解析 Hamiltonian KAM 定理，采用明确的闭域及实截面正则性假设。包含实际迭代、解析不变环面、原 Hamiltonian 的真实轨道、跨局部图的环面不交性与全局测度结论。等能推广、退化情形和 §5 重刚体应用不在本次范围内。

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

机器检查证明的是 Lean 中的精确陈述。域条件是否与原文对应、估计是否表达预期含义等，仍属于人工语义复核的职责。

## 引用和许可

代码与仓库说明采用 [Apache-2.0](LICENSE)。引用信息见 [CITATION.cff](CITATION.cff)。本次版本可引用为：

Bingqi Yu. (2026). *Arnold 1963 KAM in Lean 4* (v0.1.0) [Computer software]. Zenodo. https://doi.org/10.5281/zenodo.23201478

数学原文：V. I. Arnol'd, Russian Mathematical Surveys **18**(5), 9–36 (1963)，
[DOI](https://doi.org/10.1070/RM1963v018n05ABEH004130)。
原论文与未公开的工作参考稿未包含在此代码包中。
