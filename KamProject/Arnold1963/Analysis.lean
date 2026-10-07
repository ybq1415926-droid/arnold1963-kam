import KamProject.Arnold1963.Analysis.Cauchy
import KamProject.Arnold1963.Analysis.DomainBuffer
import KamProject.Arnold1963.Analysis.SecondCauchy
import KamProject.Arnold1963.Analysis.MeanValue
import KamProject.Arnold1963.Analysis.Taylor
import KamProject.Arnold1963.Analysis.FourierPolynomial
import KamProject.Arnold1963.Analysis.NormComparison
import KamProject.Arnold1963.Analysis.FourierCoefficients
import KamProject.Arnold1963.Analysis.FourierKernel
import KamProject.Arnold1963.Analysis.ContourShift
import KamProject.Arnold1963.Analysis.FourierSeries
import KamProject.Arnold1963.Analysis.FourierTail
import KamProject.Arnold1963.Analysis.FourierReconstruction
import KamProject.Arnold1963.Analysis.FourierParameter
import KamProject.Arnold1963.Analysis.AnalyticUniformLimit

set_option linter.style.header false

/-! 分析工具公共入口。多变量衰减、复带重构、真实尾项和参数积分解析性已接入。
多变量 Cauchy 公式及一致解析极限见 AnalyticUniformLimit，供 W7 联合角解析性使用。
本轮参数解析性及生成变换的精确范围见 Step4ModificationReport.md。 -/
