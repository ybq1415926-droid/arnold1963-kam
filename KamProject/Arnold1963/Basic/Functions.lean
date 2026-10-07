import KamProject.Arnold1963.Basic.Periodic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# 域上的解析函数、实性及一致范数

`AnalyticOnNhd ℂ f S` 要求每个 x ∈ S 在整个环境空间的邻域上有收敛幂级数，
不是只要求相对于 S 解析。`analyticOnNhd_iff_exists_open` 显示它对应一个开邻域。
全函数 f 的域外值仅作为形式化载体；不要求在整个空间上解析或有界。

一致范数使用 mathlib 的有界连续函数空间 `↥S →ᵇ F`，包括空域的范数为零。
绝不对未经有界性证明的函数直接取实数 sSup；也不把逐点严格小于 M 与
一致范数严格小于 M 混同。`supNorm_lt_iff` 明确要求存在统一的较小上界。
-/

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

section UniformNorm

variable {E F : Type*} [NormedAddCommGroup F]

/-- 非负的逐点一致上界；即使 S 为空，也要求 0 ≤ M。 -/
def NormBoundOn (f : E → F) (S : Set E) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ x ∈ S, ‖f x‖ ≤ M

theorem NormBoundOn.nonneg {f : E → F} {S : Set E} {M : ℝ}
    (h : NormBoundOn f S M) : 0 ≤ M := h.1

theorem NormBoundOn.norm_le {f : E → F} {S : Set E} {M : ℝ}
    (h : NormBoundOn f S M) {x : E} (hx : x ∈ S) : ‖f x‖ ≤ M := h.2 x hx

@[simp] theorem normBoundOn_empty (f : E → F) (M : ℝ) :
    NormBoundOn f ∅ M ↔ 0 ≤ M := by simp [NormBoundOn]

variable [TopologicalSpace E]

/-- 连续且有界的域上函数；范数继承 mathlib 的一致范数。 -/
abbrev BoundedOnDomain (S : Set E) := BoundedContinuousFunction ↥S F

def supNorm {S : Set E} (f : BoundedOnDomain (F := F) S) : ℝ := ‖f‖

/-- 从环境函数、在 S 上的连续性及真实上界构造域上函数。 -/
def boundedRestriction (f : E → F) (S : Set E) (hf : ContinuousOn f S)
    (M : ℝ) (hM : NormBoundOn f S M) : BoundedOnDomain (F := F) S :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : S => f x)
    hf.domRestrict M (fun x => hM.norm_le x.property)

@[simp] theorem boundedRestriction_apply (f : E → F) (S : Set E)
    (hf : ContinuousOn f S) (M : ℝ) (hM : NormBoundOn f S M) (x : S) :
    boundedRestriction f S hf M hM x = f x := rfl

theorem norm_apply_le_supNorm {S : Set E} (f : BoundedOnDomain (F := F) S) (x : S) :
    ‖f x‖ ≤ supNorm f := f.norm_coe_le_norm x

theorem supNorm_le_iff {S : Set E} (f : BoundedOnDomain (F := F) S)
    {M : ℝ} (hM : 0 ≤ M) : supNorm f ≤ M ↔ ∀ x : S, ‖f x‖ ≤ M :=
  BoundedContinuousFunction.norm_le hM

/-- 严格一致界意味着存在同一个 C < M 支配所有点，包括非紧域。 -/
theorem supNorm_lt_iff {S : Set E} (f : BoundedOnDomain (F := F) S) (M : ℝ) :
    supNorm f < M ↔ ∃ C : ℝ, 0 ≤ C ∧ C < M ∧ ∀ x : S, ‖f x‖ ≤ C := by
  constructor
  · intro h
    exact ⟨supNorm f, norm_nonneg f, h, fun x => norm_apply_le_supNorm f x⟩
  · rintro ⟨C, hC, hCM, hf⟩
    exact lt_of_le_of_lt ((supNorm_le_iff f hC).2 hf) hCM

theorem supNorm_boundedRestriction_le (f : E → F) (S : Set E)
    (hf : ContinuousOn f S) {M : ℝ} (hM : NormBoundOn f S M) :
    supNorm (boundedRestriction f S hf M hM) ≤ M :=
  (supNorm_le_iff _ hM.nonneg).2 fun x => hM.norm_le x.property

end UniformNorm

/-- mathlib 原定义的展开，来自 Mathlib/Analysis/Analytic/Basic.lean；不是本项目公理。 -/
theorem analyticOnNhd_iff_forall_analyticAt {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) :
    AnalyticOnNhd ℂ f S ↔ ∀ x ∈ S, AnalyticAt ℂ f x := Iff.rfl

/-- 闭域上使用 AnalyticOnNhd，等价于在某个包含该域的开集上处处解析。 -/
theorem analyticOnNhd_iff_exists_open {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) :
    AnalyticOnNhd ℂ f S ↔
      ∃ U : Set (ComplexPhaseSpace n), IsOpen U ∧ S ⊆ U ∧ AnalyticOnNhd ℂ f U := by
  constructor
  · intro h
    exact ⟨{x | AnalyticAt ℂ f x}, isOpen_analyticAt ℂ f, h, fun _ hx => hx⟩
  · rintro ⟨U, _, hSU, hU⟩
    exact hU.mono hSU

/-- 与复共轭相容；使用时还须确保所用域共轭不变。 -/
def ConjCompatibleOn {n : ℕ} (f : ComplexPhaseSpace n → ℂ)
    (S : Set (ComplexPhaseSpace n)) : Prop :=
  ∀ z ∈ S, f (conjPhase z) = star (f z)

/--
指定作用域和角带上的解析、实性、周期性、有界性证书。
字段都是输入性质，不包含 KAM 存在性、逆映射或输出余项。
不要求 G 非空或规则：初始域条件与删共振后的域必须分别处理。
-/
structure AnalyticPhaseFunction (n : ℕ) (G : Set (ComplexSpace n)) (ρ : ℝ≥0) where
  toFun : ComplexPhaseSpace n → ℂ
  domain_conj : ConjInvariant G
  analytic : AnalyticOnNhd ℂ toFun (phaseDomain G ρ)
  periodic : AnglePeriodicOn G ρ toFun
  conj_compatible : ConjCompatibleOn toFun (phaseDomain G ρ)
  bounded : ∃ M : ℝ, NormBoundOn toFun (phaseDomain G ρ) M

/-- 在真实解析域上构造可取一致范数的函数，不使用域外取值。 -/
def AnalyticPhaseFunction.toBounded {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) :
    BoundedOnDomain (F := ℂ) (phaseDomain G ρ) :=
  boundedRestriction f.toFun (phaseDomain G ρ) f.analytic.continuousOn
    f.bounded.choose f.bounded.choose_spec

/-- 该实数才是解析函数在指定域上的一致范数。 -/
def AnalyticPhaseFunction.uniformNorm {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) : ℝ := supNorm f.toBounded

theorem AnalyticPhaseFunction.norm_le_iff {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (f : AnalyticPhaseFunction n G ρ) {M : ℝ} :
    f.uniformNorm ≤ M ↔ NormBoundOn f.toFun (phaseDomain G ρ) M := by
  constructor
  · intro h
    refine ⟨(norm_nonneg f.toBounded).trans h, ?_⟩
    intro x hx
    exact (norm_apply_le_supNorm f.toBounded ⟨x, hx⟩).trans h
  · intro h
    exact (supNorm_le_iff _ h.nonneg).2 fun x => h.norm_le x.property

/-- 复共轭相容性确实推出实点处的函数值为实数。 -/
theorem AnalyticPhaseFunction.real_value {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (f : AnalyticPhaseFunction n G ρ) (p q : RealSpace n)
    (hp : complexify p ∈ G) : (f.toFun (complexify p, complexify q)).im = 0 := by
  have h := f.conj_compatible (complexify p, complexify q)
    (show (complexify p, complexify q) ∈ phaseDomain G ρ from
      ⟨hp, complexify_mem_angleStrip q ρ⟩)
  apply Complex.conj_eq_iff_im.mp
  simpa [conjPhase] using h.symm

/-- 任意实常函数给出这一证书的实际实例，不以输出存在性作为输入。 -/
def AnalyticPhaseFunction.constReal {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0)
    (hG : ConjInvariant G) (c : ℝ) : AnalyticPhaseFunction n G ρ where
  toFun := fun _ => (c : ℂ)
  domain_conj := hG
  analytic := analyticOnNhd_const
  periodic := by intro p hp q hq k; rfl
  conj_compatible := by intro z hz; simp
  bounded := ⟨‖(c : ℂ)‖, norm_nonneg _, fun _ _ => le_rfl⟩

/-- 非空域上的实常函数一致范数为 |c|，验证范数不是任意选取的预算 M。 -/
theorem AnalyticPhaseFunction.uniformNorm_constReal {n : ℕ}
    (G : Set (ComplexSpace n)) (ρ : ℝ≥0) (hG : ConjInvariant G)
    (hne : G.Nonempty) (c : ℝ) :
    (AnalyticPhaseFunction.constReal G ρ hG c).uniformNorm = |c| := by
  apply le_antisymm
  · apply (AnalyticPhaseFunction.norm_le_iff _).2
    refine ⟨abs_nonneg c, ?_⟩
    intro x hx
    simp [AnalyticPhaseFunction.constReal, Complex.norm_real, Real.norm_eq_abs]
  · obtain ⟨p, hp⟩ := hne
    let x : phaseDomain G ρ := ⟨(p, complexify (0 : RealSpace n)),
      hp, complexify_mem_angleStrip 0 ρ⟩
    have h := norm_apply_le_supNorm
      (AnalyticPhaseFunction.constReal G ρ hG c).toBounded x
    simpa [AnalyticPhaseFunction.toBounded, boundedRestriction,
      AnalyticPhaseFunction.constReal, AnalyticPhaseFunction.uniformNorm,
      Complex.norm_real, Real.norm_eq_abs] using h

end KamProject.Arnold1963
