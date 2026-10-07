import KamProject.Arnold1963.Geometry.NearIdentity
import KamProject.Arnold1963.Geometry.GeneratingMaps

/-! §4.3.3 的隐式方程：由 S 的解析性和一致界实际构造唯一的小位移根。 -/
noncomputable section
open Set Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963

variable {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G U : Set (ComplexSpace n)}
  {r : ℝ≥0} {M : ℝ} {P Q : ComplexSpace n}

theorem generating_ball_buffer
    (hP : P ∈ erosion G (r + r)) (hQ : Q ∈ erosion U ((r + r) + r))
    {q : ComplexSpace n} (hq : q ∈ closedBall Q r) :
    (P, q) ∈ erosion (G ×ˢ U) (r + r) :=
  prod_mem_erosion hP (mem_erosion_of_dist_le hQ hq)

/-- 这里只需 M/r²<1；对原文的 M<r²/(16n) 后续另给显式数值连接。 -/
theorem existsUnique_generating_root (hr : 0 < r)
    (hS : AnalyticOnNhd ℂ S (G ×ˢ U)) (hM : NormBoundOn S (G ×ˢ U) M)
    (hsmall : M / r / r < 1)
    (hP : P ∈ erosion G (r + r)) (hQ : Q ∈ erosion U ((r + r) + r)) :
    ∃! q, q ∈ closedBall Q r ∧ q + pGradient S (P, q) = Q := by
  let a : ComplexSpace n → ComplexSpace n := fun q => pGradient S (P, q)
  let κ : ℝ≥0 := ⟨M / r / r, div_nonneg (div_nonneg hM.nonneg r.coe_nonneg) r.coe_nonneg⟩
  have hp (q : ComplexSpace n) (hq : q ∈ closedBall Q r) := generating_ball_buffer hP hQ hq
  have hA (q : ComplexSpace n) (hq : q ∈ closedBall Q r) : AnalyticAt ℂ a q :=
    (analyticAt_pGradient (hS _ (erosion_subset _ _ (hp q hq)))).comp
      (f := fun t => (P, t)) (analyticAt_const.prod analyticAt_id)
  have hd (q : ComplexSpace n) (hq : q ∈ closedBall Q r) :
      ‖fderiv ℂ a q‖ ≤ M / r / r := by
    have hc := ((analyticAt_pGradient
      (hS _ (erosion_subset _ _ (hp q hq)))).differentiableAt.hasFDerivAt).comp q
      ((hasFDerivAt_const P q).prodMk (hasFDerivAt_id (𝕜 := ℂ) q))
    apply le_trans (b := ‖fderiv ℂ (pGradient S) (P, q)‖)
    · refine (fderiv ℂ a q).opNorm_le_bound (norm_nonneg _) ?_
      intro v
      change ‖fderiv ℂ (pGradient S ∘ Prod.mk P) q v‖ ≤ _
      rw [hc.fderiv]
      simpa using (fderiv ℂ (pGradient S) (P, q)).le_opNorm (0, v)
    · exact norm_fderiv_pGradient_le hr hS hM (hp q hq)
  have hLip : LipschitzOnWith κ a (closedBall Q r) :=
    (convex_closedBall Q (r : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq => (hA q hq).differentiableAt) (fun q hq => hd q hq)
  have hb : NormBoundOn a (closedBall Q r) (M / r) := by
    refine ⟨div_nonneg hM.nonneg r.coe_nonneg, ?_⟩
    intro q hq
    exact norm_pGradient_le_div hr hS hM
      (erosion_antitone_radius _ (le_add_self) (hp q hq))
  exact existsUnique_add_eq_on_closedBall hb
    (le_of_lt (by simpa using (div_lt_iff₀ (show (0 : ℝ) < r from hr)).mp hsmall))
    hsmall hLip

/-- 任一闭球内根的定量位移、原域映入和输出坐标公式。 -/
theorem generating_root_bounds (hr : 0 < r)
    (hS : AnalyticOnNhd ℂ S (G ×ˢ U)) (hM : NormBoundOn S (G ×ˢ U) M)
    (hsmall : M / r / r ≤ 1)
    (hP : P ∈ erosion G (r + r)) (hQ : Q ∈ erosion U ((r + r) + r))
    {q : ComplexSpace n} (hq : q ∈ closedBall Q r) (he : q + pGradient S (P, q) = Q) :
    ‖generatingOutput S (P, q) - (P, Q)‖ ≤ M / r ∧
      generatingOutput S (P, q) ∈ G ×ˢ U := by
  have hx := generating_ball_buffer hP hQ hq
  have hx' := erosion_antitone_radius (G ×ˢ U) (show r ≤ r + r from le_add_self) hx
  have hbP := norm_pGradient_le_div hr hS hM hx'
  have hbQ := norm_qGradient_le_div hr hS hM hx'
  have hε : M / r ≤ (r : ℝ) := by
    simpa using (div_le_iff₀ (show (0 : ℝ) < r from hr)).mp hsmall
  constructor
  · simpa [generatingOutput, Prod.sub_def, Prod.norm_def] using
      max_le hbQ (norm_sub_le_of_add_eq (a := fun t => pGradient S (P, t)) he hbP)
  · constructor
    · apply (erosion_antitone_radius G (show r ≤ r + r from le_add_self) hP)
      simpa [generatingOutput, Metric.mem_closedBall, dist_eq_norm] using hbQ.trans hε
    · exact (erosion_subset _ _ hx).2

/-- 原文额外角缓冲 δ 所给出的改进作用位移 M/δ；δ 与 r 分别使用。 -/
theorem generating_action_displacement_le {δ : ℝ≥0} (hδ : 0 < δ)
    (hS : AnalyticOnNhd ℂ S (G ×ˢ U)) (hM : NormBoundOn S (G ×ˢ U) M)
    (hP : P ∈ G) (hQ : Q ∈ erosion U (((r + r) + r) + δ))
    {q : ComplexSpace n} (hq : q ∈ closedBall Q r) :
    ‖(generatingOutput S (P, q)).1 - P‖ ≤ M / δ := by
  have hQr : Q ∈ erosion U (δ + r) :=
    erosion_antitone_radius U (by
      simpa only [add_assoc, add_comm, add_left_comm] using
        (show δ + r ≤ (δ + r) + (r + r) from le_self_add)) hQ
  have hqδ := mem_erosion_of_dist_le hQr hq
  simpa [generatingOutput] using norm_qGradient_le_on_product hδ hS hM hP hqδ

end KamProject.Arnold1963
