import KamProject.Arnold1963.Basic.Functions
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! 将局部幂级数提升到有界连续函数空间；为紧参数积分提供真正的解析证书。 -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace KamProject.Arnold1963

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem lift_bound {m : ℕ} (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (v : Fin m → X →ᵇ E) (x : X) :
    ‖p (fun j => v j x)‖ ≤ ‖p‖ * ∏ j, ‖v j‖ := by
  exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => (v j).norm_coe_le_norm x))
    (norm_nonneg _))

omit [NormedSpace ℂ E] in
private theorem eval_update {m : ℕ} [DecidableEq (Fin m)] (v : Fin m → X →ᵇ E) (i : Fin m)
    (a : X →ᵇ E) (x : X) :
    (fun j => Function.update v i a j x) = Function.update (fun j => v j x) i (a x) := by
  ext j
  by_cases h : j = i <;> simp [h]

def boundedMultilinearLift {m : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => X →ᵇ E) (X →ᵇ ℂ) :=
  MultilinearMap.mkContinuous
    { toFun := fun v => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => p (fun j => v j x))
        (p.cont.comp (continuous_pi (fun j => (v j).continuous)))
        (‖p‖ * ∏ j, ‖v j‖) (lift_bound p v)
      map_update_add' := by
        intro _ v i a b
        ext x
        change p (fun j => Function.update v i (a + b) j x) =
          p (fun j => Function.update v i a j x) + p (fun j => Function.update v i b j x)
        simp only [eval_update, BoundedContinuousFunction.add_apply, p.map_update_add]
      map_update_smul' := by
        intro _ v i c a
        ext x
        change p (fun j => Function.update v i (c • a) j x) =
          c • p (fun j => Function.update v i a j x)
        simp only [eval_update, BoundedContinuousFunction.smul_apply, p.map_update_smul]
        }
    ‖p‖ (fun v => (BoundedContinuousFunction.norm_le (by positivity)).mpr (lift_bound p v))

@[simp] theorem boundedMultilinearLift_apply {m : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (v : Fin m → X →ᵇ E) (x : X) : boundedMultilinearLift p v x = p (fun j => v j x) := rfl

theorem norm_boundedMultilinearLift_le {m : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ) :
    ‖boundedMultilinearLift (X := X) p‖ ≤ ‖p‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  exact (BoundedContinuousFunction.norm_le (by positivity)).mpr (lift_bound p v)

def boundedSeriesLift (p : FormalMultilinearSeries ℂ E ℂ) :
    FormalMultilinearSeries ℂ (X →ᵇ E) (X →ᵇ ℂ) := fun m => boundedMultilinearLift (p m)

theorem radius_boundedSeriesLift_le (p : FormalMultilinearSeries ℂ E ℂ) :
    p.radius ≤ (boundedSeriesLift (X := X) p).radius :=
  FormalMultilinearSeries.radius_le_of_le (fun m => norm_boundedMultilinearLift_le (p m))

theorem boundedSeriesLift_sum_apply (p : FormalMultilinearSeries ℂ E ℂ)
    {v : X →ᵇ E} (hv : v ∈ Metric.eball 0 p.radius) (x : X) :
    (boundedSeriesLift p).sum v x = p.sum (v x) := by
  have hl : v ∈ Metric.eball 0 (boundedSeriesLift (X := X) p).radius :=
    lt_of_lt_of_le hv (radius_boundedSeriesLift_le p)
  have hs := (BoundedContinuousFunction.evalCLM ℂ x).hasSum
    ((boundedSeriesLift p).summable hl).hasSum
  have hx : v x ∈ Metric.eball 0 p.radius := by
    have hv' : ENNReal.ofReal ‖v‖ < p.radius := by
      simpa [Metric.mem_eball, edist_dist, dist_zero_right] using hv
    simpa [Metric.mem_eball, edist_dist, dist_zero_right] using
      (ENNReal.ofReal_le_ofReal (v.norm_coe_le_norm x)).trans_lt hv'
  exact hs.unique (p.summable hx).hasSum

/-- 常值函数嵌入保持线性且算子范数不超过 1。 -/
def boundedConstCLM : E →L[ℂ] (X →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := BoundedContinuousFunction.const X
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (fun v => by simpa using BoundedContinuousFunction.norm_const_le (α := X) v)

@[simp] theorem boundedConstCLM_apply (v : E) (x : X) : boundedConstCLM v x = v := rfl

/-- 对有限测度的真实积分是有界连续函数空间上的连续复线性泛函。 -/
def boundedIntegralCLM [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := by intro c f; exact integral_smul c f }
    (μ.real univ) (fun f => f.norm_integral_le_mul_norm μ)

end KamProject.Arnold1963
