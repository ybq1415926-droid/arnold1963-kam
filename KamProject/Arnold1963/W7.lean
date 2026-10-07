import KamProject.Arnold1963.W6
import KamProject.Arnold1963.Convergence.Nonresonance
import KamProject.Arnold1963.Convergence.RealDerivative
import KamProject.Arnold1963.Convergence.JointAnalyticity
import KamProject.Arnold1963.Dynamics.RealOrbits
import KamProject.Arnold1963.Measure.LimitImage
import KamProject.Arnold1963.Measure.PhaseVolume
import KamProject.Arnold1963.Measure.LimitTorusVolume

set_option linter.style.header false

/-! W7 交付入口：实际极限映射和频率、全部整数模非共振、
固定作用标签下的多变量联合角解析性、全部实时间的实际 Hamilton 轨道，
以及同一个 2π 商极限映射的严格大测度像。
有限组合的实辛 Jacobian、周期商体积换元和紧闭胞腔上的 C4 应用均已证明。
W8 继续证明频率单射、角投影解析可逆、环面嵌入及两两不交；此入口不宣称完整定理 1。

编号契约：state/phase/actionDomain/frequency/cumulative 的代码 s 就是论文状态 s。
delta/beta/gamma/perturbation/cutoff 的代码 s 是论文步参数 s+1；
transformation b s = B_{s+1} : F_{s+1} → F_s，cumulative b 0 = id。
特别是代码状态 s+1 仍是论文状态 s+1，不能再减一。
有限组合的实导数界见 cumulative_real_derivative；其结论不涉及极限的作用可微性。
-/
