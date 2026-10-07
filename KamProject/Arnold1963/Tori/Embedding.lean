import KamProject.Arnold1963.Tori.Disjointness
import KamProject.Arnold1963.Measure.LimitTorusVolume
import KamProject.Arnold1963.Geometry.GlobalInverse

/-! 角投影的全局实逆与局部复解析逆，以及真正的周期环面拓扑嵌入。
解析性由同一嵌入的复覆盖提升给出；不声称对 Cantor 作用标签环境解析。
-/
noncomputable section
open Set Function Filter Metric Topology
open scoped NNReal
namespace KamProject.Arnold1963.Iteration.InitialData
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

def realAngleMap (p q : RealSpace n) : RealSpace n := (h.realLimitMap b (p, q)).2
def realAngleCorrection (p : RealSpace n) : RealSpace n → RealSpace n :=
  realRestriction (h.angleCorrection b (complexify p))

theorem realAngleMap_eq (p q : RealSpace n) :
    h.realAngleMap b p q = q + h.realAngleCorrection b p q := by
  ext j
  simp [realAngleMap, realAngleCorrection, realRestriction, angleCorrection, angleMap,
    realLimitMap, realPartPhase, complexifyPhase, realPart, complexify]

theorem realAngleCorrection_lipschitz {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    LipschitzWith (1 / 2) (h.realAngleCorrection b p) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  have hh := (h.angleCorrection_lipschitz b hp).dist_le_mul
    (complexify q) (complexify_mem_angleStrip _ _) (complexify r) (complexify_mem_angleStrip _ _)
  rw [(isometry_complexify n).dist_eq] at hh
  rw [dist_eq_norm] at hh ⊢
  have he : h.realAngleCorrection b p q - h.realAngleCorrection b p r =
      realPart (h.angleCorrection b (complexify p) (complexify q) -
        h.angleCorrection b (complexify p) (complexify r)) := by
    ext j; simp [realAngleCorrection, realRestriction, realPart]
  rw [he]
  exact (norm_realPart_le _).trans hh

theorem realAngleCorrection_bound {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) : ‖h.realAngleCorrection b p q‖ < 2 * (beta δ₁ 0 : ℝ) :=
  (norm_realPart_le _).trans_lt (h.angleCorrection_bound b hp
    (thinAngleStrip_subset b (complexify_mem_angleStrip _ _)))

theorem realAngleMap_bijective {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    Bijective (h.realAngleMap b p) := by
  constructor
  · intro q r he
    have hh := (h.realAngleCorrection_lipschitz b hp).dist_le_mul q r
    rw [h.realAngleMap_eq b, h.realAngleMap_eq b] at he
    have hd : q - r = h.realAngleCorrection b p r - h.realAngleCorrection b p q := by
      linear_combination he
    rw [dist_eq_norm, norm_sub_rev (h.realAngleCorrection b p q)
      (h.realAngleCorrection b p r), ← hd, ← dist_eq_norm] at hh
    apply dist_eq_zero.mp
    norm_num at hh
    linarith [dist_nonneg (x := q) (y := r)]
  · intro Q
    obtain ⟨q, hq, _⟩ := existsUnique_add_eq_on_closedBall
      (a := h.realAngleCorrection b p) (Q := Q) (r := 2 * beta δ₁ 0) (κ := 1 / 2)
      ⟨by positivity, fun q _ => (h.realAngleCorrection_bound b hp q).le⟩
      (by simp) (by norm_num) ((h.realAngleCorrection_lipschitz b hp).lipschitzOnWith)
    exact ⟨q, (h.realAngleMap_eq b p q).trans hq.2⟩

def realAngleInverse (p : RealSpace n) : RealSpace n → RealSpace n :=
  invFun (h.realAngleMap b p)

theorem realAngleInverse_left {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) : h.realAngleInverse b p (h.realAngleMap b p q) = q :=
  Function.leftInverse_invFun (h.realAngleMap_bijective b hp).1 q

theorem realAngleInverse_right {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (Q : RealSpace n) : h.realAngleMap b p (h.realAngleInverse b p Q) = Q :=
  Function.rightInverse_invFun (h.realAngleMap_bijective b hp).2 Q

/-- 固定复薄角带上的统一逆选择，后证其在每个实像点附近解析。 -/
def complexAngleInverse (p : ComplexSpace n) : ComplexSpace n → ComplexSpace n :=
  invFunOn (h.angleMap b p) (angleStrip n (ρ₀ / 6))

theorem angleMap_derivative_near_id {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ angleStrip n (ρ₀ / 6)) :
    ‖fderiv ℂ (h.angleMap b p) q - ContinuousLinearMap.id ℂ _‖ < 1 / 2 := by
  have ha := analyticAt_snd.comp
    (h.limitMap_angle_analytic b hp q (thinAngleStrip_subset b hq))
  have he : fderiv ℂ (h.angleCorrection b p) q =
      fderiv ℂ (h.angleMap b p) q - ContinuousLinearMap.id ℂ _ := by
    exact (ha.differentiableAt.hasFDerivAt.sub (hasFDerivAt_id q)).fderiv
  rw [← he]
  exact h.angleCorrection_derivative b hp hq

theorem complexAngleInverse_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (q : RealSpace n) :
    AnalyticAt ℂ (h.complexAngleInverse b p) (h.angleMap b p (complexify q)) ∧
    h.complexAngleInverse b p (h.angleMap b p (complexify q)) = complexify q ∧
    (∀ᶠ Q in 𝓝 (h.angleMap b p (complexify q)),
      h.angleMap b p (h.complexAngleInverse b p Q) = Q) := by
  have hD : angleStrip n (ρ₀ / 6) ∈ 𝓝 (complexify q) := by
    have hc : Continuous (fun z : ComplexSpace n => ‖imagPart z‖) := by
      unfold imagPart; fun_prop
    have hh : ‖imagPart (complexify q)‖ < ((ρ₀ / 6 : ℝ≥0) : ℝ) := by
      simp only [imagPart_complexify, norm_zero, NNReal.coe_div, NNReal.coe_ofNat]
      exact div_pos b.width_pos (by norm_num)
    exact mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds hh)
      (fun z (hz : ‖imagPart z‖ < ((ρ₀ / 6 : ℝ≥0) : ℝ)) => hz.le)
  exact analytic_invFunOn (h.angleMap_injOn b hp) hD
    (analyticAt_snd.comp (h.limitMap_angle_analytic b hp _
      (thinAngleStrip_subset b (complexify_mem_angleStrip _ _))))
    ((h.angleMap_derivative_near_id b hp (complexify_mem_angleStrip _ _)).trans (by norm_num))

/-- 复提升的角微分可逆，故完整相空间提升是浸入。 -/
theorem angleMap_derivative_injective {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ angleStrip n (ρ₀ / 6)) :
    Injective (fderiv ℂ (h.angleMap b p) q) := by
  have hn := h.angleMap_derivative_near_id b hp hq
  have hu := isUnit_one_sub_of_norm_lt_one
    (show ‖-(fderiv ℂ (h.angleMap b p) q - ContinuousLinearMap.id ℂ _)‖ < 1 by
      simpa only [norm_neg] using hn.trans (by norm_num : (1 / 2 : ℝ) < 1))
  have he : (1 : ComplexSpace n →L[ℂ] ComplexSpace n) -
      -(fderiv ℂ (h.angleMap b p) q - 1) = fderiv ℂ (h.angleMap b p) q := by abel
  change IsUnit (1 - -(fderiv ℂ (h.angleMap b p) q - 1)) at hu
  rw [he] at hu
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  exact (ContinuousLinearEquiv.ofUnit u).injective

def torusEmbedding (p : RealSpace n) (Q : RealTorus n) : RealPhaseSpace n :=
  h.torusLimitMap b (p, Q)

/-- 拓扑嵌入与已证解析的 S∞ 覆盖提升是同一个映射。 -/
theorem torusEmbedding_lift {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) :
    h.torusEmbedding b p (fun j => (q j : AddCircle (2 * Real.pi))) =
      torusProjection (realPartPhase (h.limitMap b (complexify p, complexify q))) :=
  h.torusLimitMap_projection b (x := (p, q)) hp

theorem torusEmbedding_range (p : RealSpace n) :
    range (h.torusEmbedding b p) = h.invariantTorus b p := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(p, q), ⟨rfl, mem_univ _⟩, rfl⟩
  · rintro ⟨⟨p', q⟩, ⟨hp, _⟩, rfl⟩
    change p' = p at hp
    subst p'
    exact ⟨q, rfl⟩

theorem torusEmbedding_continuous {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    Continuous (h.torusEmbedding b p) := by
  let π : RealSpace n → RealTorus n := fun q j => (q j : AddCircle (2 * Real.pi))
  have hπ : IsQuotientMap π :=
    (IsOpenQuotientMap.piMap fun _ : Fin n =>
      (QuotientAddGroup.isOpenQuotientMap_mk : IsOpenQuotientMap
        (fun t : ℝ => (t : AddCircle (2 * Real.pi))))).isQuotientMap
  apply hπ.continuous_iff.mpr
  have he : h.torusEmbedding b p ∘ π =
      fun q => torusProjection (h.realLimitMap b (p, q)) := by
    funext q
    exact h.torusLimitMap_projection b (x := (p, q)) hp
  rw [he]
  exact continuous_torusProjection.comp
    ((h.realLimitMap_continuous b).comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hp, mem_univ _⟩))

theorem torusEmbedding_isClosedEmbedding {p : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) : IsClosedEmbedding (h.torusEmbedding b p) := by
  apply (h.torusEmbedding_continuous b hp).isClosedEmbedding
  intro Q R he
  exact congrArg Prod.snd (h.torusLimitMap_injOn b ⟨hp, mem_univ Q⟩ ⟨hp, mem_univ R⟩ he)

theorem angleMap_real_value {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) : complexify (h.realAngleMap b p q) =
      h.angleMap b (complexify p) (complexify q) :=
  congrArg Prod.snd (h.limitMap_real_value b (x := (p, q)) hp)

/-- 复逆在全部实角目标上确实限制为所构造的同一个全局实逆。 -/
theorem complexAngleInverse_real_value {p : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (Q : RealSpace n) :
    h.complexAngleInverse b (complexify p) (complexify Q) =
      complexify (h.realAngleInverse b p Q) := by
  have he := h.angleMap_real_value b hp (h.realAngleInverse b p Q)
  rw [h.realAngleInverse_right b hp] at he
  rw [he]
  exact (h.complexAngleInverse_analytic b hp _).2.1

theorem complexAngleInverse_analytic_at_real {p : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (Q : RealSpace n) :
    AnalyticAt ℂ (h.complexAngleInverse b (complexify p)) (complexify Q) := by
  have he := h.angleMap_real_value b hp (h.realAngleInverse b p Q)
  rw [h.realAngleInverse_right b hp] at he
  rw [he]
  exact (h.complexAngleInverse_analytic b hp _).1

theorem torusLift_derivative_injective {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} (hq : q ∈ angleStrip n (ρ₀ / 6)) :
    Injective (fderiv ℂ (fun q => h.limitMap b (p, q)) q) := by
  have ha := (h.limitMap_angle_analytic b hp q (thinAngleStrip_subset b hq)).differentiableAt
  have hd := ((ContinuousLinearMap.snd ℂ (ComplexSpace n) (ComplexSpace n)).hasFDerivAt.comp q
    ha.hasFDerivAt).fderiv
  intro v w he
  apply h.angleMap_derivative_injective b hp hq
  change fderiv ℂ (h.angleMap b p) q = _ at hd
  rw [hd]
  exact congrArg Prod.snd he

def torusAngleMap (p : RealSpace n) (Q : RealTorus n) : RealTorus n :=
  (h.torusEmbedding b p Q).2

theorem torusAngleMap_projection {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) :
    h.torusAngleMap b p (fun j => (q j : AddCircle (2 * Real.pi))) =
      fun j => (h.realAngleMap b p q j : AddCircle (2 * Real.pi)) :=
  congrArg Prod.snd (h.torusLimitMap_projection b (x := (p, q)) hp)

theorem torusAngleMap_bijective {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    Bijective (h.torusAngleMap b p) := by
  constructor
  · intro Q R he
    let q := (torusRepresentative (p, Q)).2
    let r := (torusRepresentative (p, R)).2
    have hq : (fun j => (q j : AddCircle (2 * Real.pi))) = Q :=
      congrArg Prod.snd (torusProjection_representative (p, Q))
    have hr : (fun j => (r j : AddCircle (2 * Real.pi))) = R :=
      congrArg Prod.snd (torusProjection_representative (p, R))
    have ht : torusProjection ((0 : RealSpace n), h.realAngleMap b p q) =
        torusProjection (0, h.realAngleMap b p r) := by
      apply Prod.ext
      · rfl
      change (fun j => (h.realAngleMap b p q j : AddCircle (2 * Real.pi))) =
        fun j => (h.realAngleMap b p r j : AddCircle (2 * Real.pi))
      rw [← h.torusAngleMap_projection b hp q, ← h.torusAngleMap_projection b hp r, hq, hr]
      exact he
    obtain ⟨k, hk⟩ := (torusProjection_eq_iff _ _).mp ht
    have hs := congrArg Prod.snd (h.realLimitMap_shift b (x := (p, r)) hp k)
    have hqr : q = r + realAngleShift k := (h.realAngleMap_bijective b hp).1
      ((congrArg Prod.snd hk).trans hs.symm)
    rw [← hq, ← hr, hqr]
    exact congrArg Prod.snd (torusProjection_shift k (p, r))
  · intro Q
    let q := (torusRepresentative (p, Q)).2
    obtain ⟨r, hr⟩ := (h.realAngleMap_bijective b hp).2 q
    refine ⟨fun j => (r j : AddCircle (2 * Real.pi)), ?_⟩
    rw [h.torusAngleMap_projection b hp r, hr]
    exact congrArg Prod.snd (torusProjection_representative (p, Q))

/-- 角投影在 2π 商上为同胚；解析正逆提升由上述定理单独提供。 -/
def torusAngleHomeomorph {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b)) :
    RealTorus n ≃ₜ RealTorus n :=
  (Equiv.ofBijective _ (h.torusAngleMap_bijective b hp)).toHomeomorphOfContinuousClosed
    (h.torusEmbedding_continuous b hp).snd
    (h.torusEmbedding_continuous b hp).snd.isClosedMap

/-- 商上逆同胚由同一个有复解析延拓的实逆提升，排除“两套逆”的语义缺口。 -/
theorem torusAngleHomeomorph_inverse_lift {p : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (Q : RealSpace n) :
    (h.torusAngleHomeomorph b hp).symm (fun j => (Q j : AddCircle (2 * Real.pi))) =
      fun j => (h.realAngleInverse b p Q j : AddCircle (2 * Real.pi)) := by
  apply (h.torusAngleHomeomorph b hp).injective
  rw [Homeomorph.apply_symm_apply]
  change (fun j => (Q j : AddCircle (2 * Real.pi))) =
    h.torusAngleMap b p (fun j => (h.realAngleInverse b p Q j : AddCircle (2 * Real.pi)))
  rw [h.torusAngleMap_projection b hp, h.realAngleInverse_right b hp]

end KamProject.Arnold1963.Iteration.InitialData
