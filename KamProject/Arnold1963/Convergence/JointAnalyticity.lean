import KamProject.Arnold1963.Convergence.ComplexLines
import KamProject.Arnold1963.Analysis.AnalyticUniformLimit

/-! 固定最终作用标签后的多变量联合角解析性。
结论在统一复角开带成立；不声称极限映射对 Cantor 作用标签的环境邻域解析。
-/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

def commonAngleStrip (n : ℕ) (ρ : ℝ≥0) : Set (ComplexSpace n) :=
  {q | ‖imagPart q‖ < (ρ : ℝ) / 3}

theorem commonAngleStrip_open : IsOpen (commonAngleStrip n ρ₀) := by
  apply isOpen_lt _ continuous_const
  unfold imagPart
  fun_prop

theorem angle_mem_limitPhase {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ commonAngleStrip n ρ₀) : (p, q) ∈ h.limitPhase b := by
  apply h.commonPhase_subset b
  exact ⟨hp, (show ‖imagPart q‖ < (ρ₀ : ℝ) / 3 from hq).le⟩

theorem angle_uniform {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    TendstoUniformlyOn (fun s q => h.cumulative b s (p, q))
      (fun q => h.limitMap b (p, q)) atTop (commonAngleStrip n ρ₀) :=
  ((h.cumulative_uniform b).comp (fun q => (p, q))).mono
    (fun _ hq => h.angle_mem_limitPhase b hp hq)

theorem cumulative_angle_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (s : ℕ) : AnalyticOnNhd ℂ (fun q => h.cumulative b s (p, q)) (commonAngleStrip n ρ₀) := by
  intro q hq
  exact (h.cumulative_analytic b s _
    (h.limitPhase_subset b s (h.angle_mem_limitPhase b hp hq))).comp
      (f := fun q : ComplexSpace n => (p, q)) (analyticAt_const.prod analyticAt_id)

theorem limitMap_angle_scalar_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (L : ComplexPhaseSpace n →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun q => L (h.limitMap b (p, q))) (commonAngleStrip n ρ₀) :=
  analyticOnNhd_uniform_limit commonAngleStrip_open
    (fun s q hq => (L.analyticAt _).comp (h.cumulative_angle_analytic b hp s q hq))
    (L.uniformContinuous.comp_tendstoUniformlyOn (h.angle_uniform b hp))

/-- W8 使用的联合角解析接口：值域包含作用与角两部分。 -/
theorem limitMap_angle_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) :
    AnalyticOnNhd ℂ (fun q => h.limitMap b (p, q)) (commonAngleStrip n ρ₀) := by
  intro q hq
  have hpA : AnalyticAt ℂ (fun q => (h.limitMap b (p, q)).1) q := by
    apply AnalyticAt.pi
    intro j
    exact h.limitMap_angle_scalar_analytic b hp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
        (ContinuousLinearMap.fst ℂ (ComplexSpace n) (ComplexSpace n))) q hq
  have hqA : AnalyticAt ℂ (fun q => (h.limitMap b (p, q)).2) q := by
    apply AnalyticAt.pi
    intro j
    exact h.limitMap_angle_scalar_analytic b hp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
        (ContinuousLinearMap.snd ℂ (ComplexSpace n) (ComplexSpace n))) q hq
  exact hpA.prod hqA

end KamProject.Arnold1963.Iteration.InitialData
