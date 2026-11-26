import BlowupFormalization.H1Sobolev

/-! # The radial exterior estimate on the plane -/

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Blowup

private noncomputable def radialMeasureFactor : ℝ :=
  2 * volume.real (Metric.ball (0 : ℝ²) 1)

private lemma radialMeasureFactor_pos : 0 < radialMeasureFactor := by
  unfold radialMeasureFactor
  exact mul_pos two_pos (ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne)

private lemma integrable_radial_profile {f : ℝ → ℝ} :
    Integrable (fun x : ℝ² ↦ f ‖x‖) ↔ IntegrableOn (fun r ↦ r * f r) (Ioi 0) := by
  simpa [smul_eq_mul] using
    (integrable_fun_norm_addHaar (volume : Measure ℝ²) (f := f))

private lemma integral_radial_profile (f : ℝ → ℝ) :
    (∫ x : ℝ², f ‖x‖) = radialMeasureFactor * (∫ r in Ioi (0 : ℝ), r * f r) := by
  simpa [radialMeasureFactor, smul_eq_mul, nsmul_eq_mul, mul_assoc] using
    integral_fun_norm_addHaar (volume : Measure ℝ²) f

private noncomputable def firstDirection : ℝ² := EuclideanSpace.single 0 1

private lemma norm_firstDirection : ‖firstDirection‖ = 1 := by
  simp [firstDirection]

private lemma hasDerivAt_ray {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u) (v : ℝ²) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ u (s • v)) (fderiv ℝ u (r • v) v) r := by
  have hLine := (hasDerivAt_id' r).smul_const v
  simpa only [one_smul, Function.comp_def] using
    ((hu.differentiable one_ne_zero (r • v)).hasFDerivAt.comp_hasDerivAt r hLine)

private lemma norm_fderiv_apply_le_coordinates (u : ℝ² → ℂ) (x v : ℝ²) (hv : ‖v‖ = 1) :
    ‖fderiv ℝ u x v‖ ≤ ‖partialDeriv 0 u x‖ + ‖partialDeriv 1 u x‖ := by
  let L := fderiv ℝ u x
  have hBasis : v = v 0 • EuclideanSpace.single 0 1 + v 1 • EuclideanSpace.single 1 1 := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]
  change ‖L v‖ ≤ _
  conv_lhs => rw [hBasis]
  rw [map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul]
  have hCoord (j : Fin 2) : ‖v j‖ ≤ 1 := (PiLp.norm_apply_le v j).trans_eq hv
  exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hCoord 0))
    (mul_le_of_le_one_left (norm_nonneg _) (hCoord 1))

private lemma radial_profile_deriv_sq_le {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u)
    (hur : IsRadial u) (x : ℝ²) :
    ‖deriv (fun r : ℝ ↦ u (r • firstDirection)) ‖x‖‖ ^ 2 ≤
      2 * (‖partialDeriv 0 u x‖ ^ 2 + ‖partialDeriv 1 u x‖ ^ 2) := by
  obtain ⟨v, hv, hPoint⟩ : ∃ v : ℝ², ‖v‖ = 1 ∧ ‖x‖ • v = x := by
    by_cases hx : x = 0
    · exact ⟨firstDirection, norm_firstDirection, by simp [hx]⟩
    · have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hx'.le),
          inv_mul_cancel₀ hx'.ne']
      · rw [smul_smul, mul_inv_cancel₀ hx'.ne', one_smul]
  have hFun : (fun r : ℝ ↦ u (r • firstDirection)) = fun r ↦ u (r • v) := by
    funext r
    exact hur _ _ (by rw [norm_smul, norm_smul, norm_firstDirection, hv])
  rw [hFun, (hasDerivAt_ray hu v ‖x‖).deriv, hPoint]
  calc
    _ ≤ (‖partialDeriv 0 u x‖ + ‖partialDeriv 1 u x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_apply_le_coordinates u x v hv) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖partialDeriv 0 u x‖ - ‖partialDeriv 1 u x‖)]

private lemma exists_small_on_Ioi {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) : ∃ s > r, f s < ε := by
  by_contra! h
  have hI : IntegrableOn f (Ioi r) := hf.mono_set (Ioi_subset_Ioi hr.le)
  have hCI : IntegrableOn (fun _ : ℝ ↦ ε) (Ioi r) := by
    refine hI.mono' aestronglyMeasurable_const ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact .of_forall fun x hx ↦ by simpa only [Real.norm_of_nonneg hε.le] using h x hx
  simp [integrableOn_const_iff, Real.volume_Ioi, hε.ne'] at hCI

private lemma radial_profile_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hmono : Monotone w)
    (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    (hMass : IntegrableOn (fun r ↦ r * ‖f r‖ ^ 2) (Ioi 0))
    (hGrad : IntegrableOn (fun r ↦ r * (w r ^ 2 * ‖deriv f r‖ ^ 2)) (Ioi 0))
    {r : ℝ} (hr : 0 < r) :
    r * w r * ‖f r‖ ^ 2 ≤
      2 * Real.sqrt (∫ s in Ioi (0 : ℝ), s * ‖f s‖ ^ 2) *
        Real.sqrt (∫ s in Ioi (0 : ℝ), s * (w s ^ 2 * ‖deriv f s‖ ^ 2)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (s : ℝ) := Real.sqrt s * ‖f s‖
  let G (s : ℝ) := Real.sqrt s * (w s * ‖deriv f s‖)
  have hFcont : Continuous F := Real.continuous_sqrt.mul hf.continuous.norm
  have hDcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hGcont : Continuous G := Real.continuous_sqrt.mul (hw.continuous.mul hDcont.norm)
  have hFSq : (fun s ↦ F s ^ 2) =ᵐ[μ] (fun s ↦ s * ‖f s‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (mul_pow _ _ _).trans (by rw [Real.sq_sqrt (le_of_lt hs)])
  have hGSq : (fun s ↦ G s ^ 2) =ᵐ[μ] (fun s ↦ s * (w s ^ 2 * ‖deriv f s‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change (Real.sqrt s * (w s * ‖deriv f s‖)) ^ 2 = _
    rw [mul_pow, mul_pow (w s), Real.sq_sqrt (le_of_lt hs)]
  have hF : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq hFcont.aestronglyMeasurable).mpr (hMass.congr hFSq.symm)
  have hG : MemLp G 2 μ :=
    (memLp_two_iff_integrable_sq hGcont.aestronglyMeasurable).mpr (hGrad.congr hGSq.symm)
  have hProduct : Integrable (fun s ↦ F s * G s) μ := hF.integrable_mul hG
  have hHolder : (∫ s, F s * G s ∂μ) ≤
      Real.sqrt (∫ s in Ioi (0 : ℝ), s * ‖f s‖ ^ 2) *
        Real.sqrt (∫ s in Ioi (0 : ℝ), s * (w s ^ 2 * ‖deriv f s‖ ^ 2)) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (μ := μ) (Eventually.of_forall fun s ↦ by positivity : 0 ≤ᵐ[μ] F)
      (Eventually.of_forall fun s ↦ mul_nonneg (Real.sqrt_nonneg s)
        (mul_nonneg (hw₀ s) (norm_nonneg _)) : 0 ≤ᵐ[μ] G)
      (by simpa using hF) (by simpa using hG)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, integral_congr_ae hFSq,
      integral_congr_ae hGSq] using h
  let W (s : ℝ) := s * w s * ‖f s‖ ^ 2
  let dW (s : ℝ) := (w s + s * deriv w s) * ‖f s‖ ^ 2 +
    (s * w s) * (2 * (deriv f s * starRingEnd ℂ (f s)).re)
  have hDeriv (s : ℝ) : HasDerivAt W (dW s) s := by
    have hNorm := ((hf.differentiable one_ne_zero s).hasDerivAt).norm_sq
    have hWeight := (hw.differentiable one_ne_zero s).hasDerivAt
    change HasDerivAt (((fun z : ℝ ↦ z) * w) * fun z ↦ ‖f z‖ ^ 2) (dW s) s
    simpa only [Complex.inner, dW, one_mul, Pi.mul_apply] using
      ((hasDerivAt_id' s).mul hWeight).mul hNorm
  have hdW : Continuous dW := by
    dsimp [dW]
    have hC := hf.continuous
    have hWC := hw.continuous
    have hDW := hw.continuous_deriv le_rfl
    fun_prop
  have hLower (s : ℝ) (hs : 0 ≤ s) : -(2 * (F s * G s)) ≤ dW s := by
    have hRe : -(‖deriv f s‖ * ‖f s‖) ≤ (deriv f s * starRingEnd ℂ (f s)).re := by
      have h := Complex.abs_re_le_norm (deriv f s * starRingEnd ℂ (f s))
      rw [norm_mul, Complex.norm_conj] at h
      exact (neg_le_neg h).trans (neg_abs_le _)
    have hFG : F s * G s = (s * w s) * (‖f s‖ * ‖deriv f s‖) := by
      calc
        _ = (Real.sqrt s * Real.sqrt s * w s) * (‖f s‖ * ‖deriv f s‖) := by
          dsimp [F, G]
          ring
        _ = _ := by rw [Real.mul_self_sqrt hs]
    rw [hFG]
    dsimp [dW]
    have hws := hw₀ s
    have hdws : 0 ≤ deriv w s := hmono.deriv_nonneg
    have hl := mul_le_mul_of_nonneg_left hRe (show 0 ≤ 2 * (s * w s) by positivity)
    have he : 0 ≤ (w s + s * deriv w s) * ‖f s‖ ^ 2 := by positivity
    linarith
  have hMain : W r ≤ 2 * (∫ s, F s * G s ∂μ) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hbε⟩ := exists_small_on_Ioi hMass hr hε
    have hbW : W b < ε := by
      have hmul := mul_le_mul_of_nonneg_left (hw₁ b) (hr.trans hb).le
      exact (mul_le_mul_of_nonneg_right (hmul.trans_eq (mul_one b)) (sq_nonneg _)).trans_lt hbε
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hDeriv s) (hdW.intervalIntegrable r b)
    rw [intervalIntegral.integral_of_le hb.le] at hFTC
    have hCoeff : Continuous (fun s ↦ -(2 * (F s * G s))) :=
      ((hFcont.mul hGcont).const_mul 2).neg
    have hI1 : IntegrableOn (fun s ↦ -(2 * (F s * G s))) (Ioc r b) :=
      hCoeff.integrableOn_Ioc
    have hI2 : IntegrableOn dW (Ioc r b) := hdW.integrableOn_Ioc
    have hl := setIntegral_mono_on hI1 hI2 measurableSet_Ioc
      (fun s hs ↦ hLower s (hr.trans hs.1).le)
    rw [integral_neg, integral_const_mul, hFTC] at hl
    have hDom : (∫ s in Ioc r b, F s * G s) ≤ ∫ s, F s * G s ∂μ :=
      setIntegral_mono_set hProduct
        (.of_forall fun s ↦ by
          have := hw₀ s
          dsimp [F, G]
          positivity)
        (.of_forall fun s hs ↦ hr.trans hs.1)
    linarith
  exact hMain.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hHolder two_pos.le)

/-- A universal constant in the radial pointwise estimate on the plane. -/
noncomputable def radialTailConstant : ℝ :=
  2 * Real.sqrt (1 / radialMeasureFactor) * Real.sqrt (2 / radialMeasureFactor)

theorem radialTailConstant_nonneg : 0 ≤ radialTailConstant := by
  unfold radialTailConstant
  positivity

/-- The kinetic integral with squared radial weight. -/
noncomputable def weightedGradNormSq (w : ℝ → ℝ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  ∫ x, w ‖x‖ ^ 2 * (‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2)

theorem weightedGradNormSq_nonneg (w : ℝ → ℝ) (Du : Fin 2 → ℝ² → ℂ) :
    0 ≤ weightedGradNormSq w Du :=
  integral_nonneg fun _ ↦ by positivity

@[simp] theorem weightedGradNormSq_one (Du : Fin 2 → ℝ² → ℂ) :
    weightedGradNormSq (fun _ ↦ 1) Du = gradNormSq Du := by
  simp [weightedGradNormSq, gradNormSq]

private lemma norm_radial_weight_smul_le {w : ℝ → ℝ}
    (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1) {x : ℝ²} (z : ℂ) :
    ‖w ‖x‖ • z‖ ≤ ‖z‖ := by
  rw [norm_smul, Real.norm_of_nonneg (hw₀ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw₁ _)

private lemma eLpNorm_radial_weight_smul_le {w : ℝ → ℝ}
    (hw : Continuous w) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {f : ℝ² → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x ↦ w ‖x‖ • f x) 2 volume ≤ eLpNorm f 2 volume :=
  eLpNorm_mono_ae ((hw.comp continuous_norm).aestronglyMeasurable.smul hf)
    (.of_forall fun _ ↦ norm_radial_weight_smul_le hw₀ hw₁ _)

private lemma memLp_radial_weight_smul {w : ℝ → ℝ}
    (hw : Continuous w) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {f : ℝ² → ℂ} (hf : MemLp f 2) : MemLp (fun x ↦ w ‖x‖ • f x) 2 :=
  (eLpNorm_radial_weight_smul_le hw hw₀ hw₁ hf.aestronglyMeasurable).trans_lt hf.eLpNorm_lt_top

private lemma norm_radial_weight_smul_sq {w : ℝ → ℝ} (hw₀ : ∀ r, 0 ≤ w r)
    (x : ℝ²) (z : ℂ) : ‖w ‖x‖ • z‖ ^ 2 = w ‖x‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (hw₀ _), mul_pow]

/-- The weighted kinetic density is integrable for an L² gradient and a continuous weight
with values between zero and one. -/
theorem integrable_weightedGradNormSq_density {w : ℝ → ℝ}
    (hw : Continuous w) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {Du : Fin 2 → ℝ² → ℂ} (hD : ∀ j, MemLp (Du j) 2) :
    Integrable (fun x ↦ w ‖x‖ ^ 2 * (‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2)) := by
  have h (j : Fin 2) := (memLp_radial_weight_smul hw hw₀ hw₁ (hD j)).norm.integrable_sq
  have hSum : Integrable (fun x ↦ ‖w ‖x‖ • Du 0 x‖ ^ 2 + ‖w ‖x‖ • Du 1 x‖ ^ 2) :=
    (h 0).add (h 1)
  simpa only [norm_radial_weight_smul_sq hw₀, ← mul_add] using hSum

/-- The weighted radial pointwise bound for C¹ functions and their classical derivatives. -/
theorem weighted_radial_tail_bound_of_contDiff {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u)
    (hur : IsRadial u) (hU : MemLp u 2) (hD : ∀ j, MemLp (partialDeriv j u) 2)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hmono : Monotone w)
    (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1) (x : ℝ²) :
    ‖x‖ * w ‖x‖ * ‖u x‖ ^ 2 ≤
      radialTailConstant * Real.sqrt (mass u) *
        Real.sqrt (weightedGradNormSq w (fun j ↦ partialDeriv j u)) := by
  let f (r : ℝ) := u (r • firstDirection)
  let M := ∫ r in Ioi (0 : ℝ), r * ‖f r‖ ^ 2
  let K := ∫ r in Ioi (0 : ℝ), r * (w r ^ 2 * ‖deriv f r‖ ^ 2)
  have hf : ContDiff ℝ 1 f := hu.comp (contDiff_id.smul contDiff_const)
  have hEq (y : ℝ²) : f ‖y‖ = u y := by
    apply hur
    simp [norm_smul, norm_firstDirection]
  have hMass : IntegrableOn (fun r ↦ r * ‖f r‖ ^ 2) (Ioi 0) :=
    (integrable_radial_profile (f := fun r ↦ ‖f r‖ ^ 2)).mp
      (by simpa only [hEq] using hU.norm.integrable_sq)
  have hGradientDirect := integrable_weightedGradNormSq_density hw.continuous hw₀ hw₁ hD
  have hGradLe (y : ℝ²) : w ‖y‖ ^ 2 * ‖deriv f ‖y‖‖ ^ 2 ≤
      2 * (w ‖y‖ ^ 2 * (‖partialDeriv 0 u y‖ ^ 2 + ‖partialDeriv 1 u y‖ ^ 2)) := by
    calc
      _ ≤ w ‖y‖ ^ 2 * (2 * (‖partialDeriv 0 u y‖ ^ 2 + ‖partialDeriv 1 u y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (radial_profile_deriv_sq_le hu hur y) (sq_nonneg _)
      _ = _ := by ring
  have hGradCont : Continuous (fun y : ℝ² ↦ w ‖y‖ ^ 2 * ‖deriv f ‖y‖‖ ^ 2) :=
    ((hw.continuous.comp continuous_norm).pow 2).mul
      (((hf.continuous_deriv le_rfl).comp continuous_norm).norm.pow 2)
  have hGrad : Integrable (fun y : ℝ² ↦ w ‖y‖ ^ 2 * ‖deriv f ‖y‖‖ ^ 2) :=
    (hGradientDirect.const_mul 2).mono_nonneg hGradCont.aestronglyMeasurable
      (.of_forall fun _ ↦ by positivity) (.of_forall hGradLe)
  have hK : IntegrableOn (fun r ↦ r * (w r ^ 2 * ‖deriv f r‖ ^ 2)) (Ioi 0) :=
    (integrable_radial_profile (f := fun r ↦ w r ^ 2 * ‖deriv f r‖ ^ 2)).mp hGrad
  have hMassEq : mass u = radialMeasureFactor * M := by
    simpa only [mass, hEq, M] using integral_radial_profile (fun r ↦ ‖f r‖ ^ 2)
  have hKBound : radialMeasureFactor * K ≤
      2 * weightedGradNormSq w (fun j ↦ partialDeriv j u) := by
    dsimp only [K]
    rw [← integral_radial_profile (fun r ↦ w r ^ 2 * ‖deriv f r‖ ^ 2)]
    have hLe := integral_mono hGrad (hGradientDirect.const_mul 2) hGradLe
    simpa only [weightedGradNormSq, integral_const_mul] using hLe
  have hMscaled : M ≤ (1 / radialMeasureFactor) * mass u := by
    have hc := radialMeasureFactor_pos
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc, mul_comm M]
    exact hMassEq.symm.le
  have hKscaled : K ≤ (2 / radialMeasureFactor) *
      weightedGradNormSq w (fun j ↦ partialDeriv j u) := by
    have hc := radialMeasureFactor_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm K]
    exact hKBound
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · rw [← hx, zero_mul, zero_mul]
    exact mul_nonneg (mul_nonneg radialTailConstant_nonneg (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  calc
    _ = ‖x‖ * w ‖x‖ * ‖f ‖x‖‖ ^ 2 := by rw [hEq]
    _ ≤ 2 * Real.sqrt M * Real.sqrt K :=
      radial_profile_decay hf hw hmono hw₀ hw₁ hMass hK hx
    _ ≤ (2 * Real.sqrt ((1 / radialMeasureFactor) * mass u)) *
        Real.sqrt ((2 / radialMeasureFactor) *
          weightedGradNormSq w (fun j ↦ partialDeriv j u)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (div_nonneg zero_le_one radialMeasureFactor_pos.le),
        Real.sqrt_mul (div_nonneg zero_le_two radialMeasureFactor_pos.le)]
      unfold radialTailConstant
      ring

/-- Strauss' radial bound for C¹ functions and their classical spatial derivatives. -/
theorem radial_tail_bound_of_contDiff {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u)
    (hur : IsRadial u) (hU : MemLp u 2) (hD : ∀ j, MemLp (partialDeriv j u) 2) (x : ℝ²) :
    ‖x‖ * ‖u x‖ ^ 2 ≤
      radialTailConstant * Real.sqrt (mass u) *
        Real.sqrt (gradNormSq (fun j ↦ partialDeriv j u)) := by
  simpa only [mul_one, weightedGradNormSq_one] using
    weighted_radial_tail_bound_of_contDiff hu hur hU hD
      (w := fun _ ↦ 1) contDiff_const (fun _ _ _ ↦ le_rfl)
      (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) x

private noncomputable def radialMollifierBase (n : ℕ) (x : ℝ²) : ℝ :=
  Real.smoothTransition (1 - ‖x‖ ^ 2 / mollifierRadius n ^ 2)

private lemma mollifierRadius_pos (n : ℕ) : 0 < mollifierRadius n := by
  unfold mollifierRadius
  positivity

private lemma radialMollifierBase_isTestFunction (n : ℕ) :
    IsTestFunction (radialMollifierBase n) := by
  refine ⟨Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _)), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ²) (mollifierRadius n)) ?_
  intro x hx
  have h : mollifierRadius n < ‖x‖ := by simpa [Metric.mem_closedBall, not_le] using hx
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, le_div_iff₀ (sq_pos_of_pos (mollifierRadius_pos n)), one_mul]
  exact pow_le_pow_left₀ (mollifierRadius_pos n).le h.le 2

private lemma radialMollifierBase_integral_pos (n : ℕ) :
    0 < ∫ x, radialMollifierBase n x := by
  have hB := radialMollifierBase_isTestFunction n
  have hInt := hB.1.continuous.integrable_of_hasCompactSupport (μ := volume) hB.2
  refine (integral_pos_iff_support_of_nonneg
    (fun x ↦ Real.smoothTransition.nonneg _) hInt).mpr ?_
  have hSupp : Metric.ball (0 : ℝ²) (mollifierRadius n) ⊆
      Function.support (radialMollifierBase n) := by
    intro x hx
    have h : ‖x‖ < mollifierRadius n := by simpa [Metric.mem_ball] using hx
    rw [Function.mem_support, radialMollifierBase, Ne, Real.smoothTransition.zero_iff_nonpos,
      not_le, sub_pos, div_lt_iff₀ (sq_pos_of_pos (mollifierRadius_pos n)), one_mul]
    exact pow_lt_pow_left₀ h (norm_nonneg _) (by norm_num)
  exact (Metric.measure_ball_pos volume _ (mollifierRadius_pos n)).trans_le (measure_mono hSupp)

private noncomputable def radialMollifier (n : ℕ) (x : ℝ²) : ℝ :=
  radialMollifierBase n x / ∫ y, radialMollifierBase n y

private lemma radialMollifier_isTestFunction (n : ℕ) : IsTestFunction (radialMollifier n) := by
  have hB := radialMollifierBase_isTestFunction n
  refine ⟨hB.1.div_const _, ?_⟩
  exact hB.2.comp_left (g := fun q : ℝ ↦ q / ∫ y, radialMollifierBase n y) (zero_div _)

private lemma radialMollifier_nonneg (n : ℕ) (x : ℝ²) : 0 ≤ radialMollifier n x :=
  div_nonneg (Real.smoothTransition.nonneg _) (radialMollifierBase_integral_pos n).le

private lemma radialMollifier_integral (n : ℕ) : ∫ x, radialMollifier n x = 1 := by
  simp only [radialMollifier, integral_div]
  exact div_self (radialMollifierBase_integral_pos n).ne'

private lemma radialMollifier_support (n : ℕ) :
    Function.support (radialMollifier n) ⊆ Metric.closedBall 0 (mollifierRadius n) := by
  intro x hx
  by_contra hx'
  have h : mollifierRadius n < ‖x‖ := by simpa [Metric.mem_closedBall, not_le] using hx'
  have hBase : radialMollifierBase n x = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rw [sub_nonpos, le_div_iff₀ (sq_pos_of_pos (mollifierRadius_pos n)), one_mul]
    exact pow_le_pow_left₀ (mollifierRadius_pos n).le h.le 2
  exact hx (by simp [radialMollifier, hBase])

private lemma radialMollifier_radial (n : ℕ) (x y : ℝ²) (h : ‖x‖ = ‖y‖) :
    radialMollifier n x = radialMollifier n y := by
  simp only [radialMollifier, radialMollifierBase, h]

private lemma isRadial_mollify_of_isRadialAE {ρ : ℝ² → ℝ}
    (hρ : ∀ x y, ‖x‖ = ‖y‖ → ρ x = ρ y) {u : ℝ² → ℂ} (hu : IsRadialAE u) :
    IsRadial (mollify ρ u) := by
  obtain ⟨w, hw, hue⟩ := hu
  have hEq : mollify ρ u = mollify ρ w := by
    funext x
    simp only [mollify_apply]
    exact integral_congr_ae (hue.mono fun y hy ↦ by
      change (ρ (x - y) : ℂ) * u y = (ρ (x - y) : ℂ) * w y
      rw [hy])
  rw [hEq]
  change Function.IsRadial (mollify ρ w)
  apply (Function.isRadial_iff_comp_linearIsometryEquiv _).mpr
  intro e
  funext x
  simp only [Function.comp_apply, mollify_apply]
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ (ρ (e x - y) : ℂ) * w y)
  rw [← h]
  apply integral_congr_ae
  refine .of_forall fun y ↦ ?_
  change (ρ (e x - e y) : ℂ) * w (e y) = (ρ (x - y) : ℂ) * w y
  rw [← map_sub e, hρ (e (x - y)) (x - y) (e.norm_map _), hw (e y) y (e.norm_map _)]

private lemma weightedGradNormSq_eq_sum_mass {w : ℝ → ℝ}
    (hw : Continuous w) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {Du : Fin 2 → ℝ² → ℂ} (hD : ∀ j, MemLp (Du j) 2) :
    weightedGradNormSq w Du =
      mass (fun x ↦ w ‖x‖ • Du 0 x) + mass (fun x ↦ w ‖x‖ • Du 1 x) := by
  have h (j : Fin 2) : Integrable (fun x ↦ w ‖x‖ ^ 2 * ‖Du j x‖ ^ 2) := by
    simpa only [norm_radial_weight_smul_sq hw₀] using
      (memLp_radial_weight_smul hw hw₀ hw₁ (hD j)).norm.integrable_sq
  simp_rw [weightedGradNormSq, mass, norm_radial_weight_smul_sq hw₀, mul_add]
  exact integral_add (h 0) (h 1)

private lemma tendsto_eLpNorm_two_sub_of_mass_sub {f : ℕ → ℝ² → ℂ} {g : ℝ² → ℂ}
    (hf : ∀ n, MemLp (f n) 2) (hg : MemLp g 2)
    (h : Tendsto (fun n ↦ mass (f n - g)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n - g) 2 volume) atTop (𝓝 0) := by
  simp_rw [eLpNorm_two_eq_ofReal_sqrt_mass ((hf _).sub hg)]
  simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h.sqrt

private lemma tendsto_mass_of_eLpNorm_two_sub {f : ℕ → ℝ² → ℂ} {g : ℝ² → ℂ}
    (hf : ∀ n, MemLp (f n) 2) (hg : MemLp g 2)
    (h : Tendsto (fun n ↦ eLpNorm (f n - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ mass (f n)) atTop (𝓝 (mass g)) := by
  have hLp : Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) :=
    tendsto_iff_eNorm_sub_tendsto_zero.2 (by simpa only [← MemLp.toLp_sub, Lp.eNorm_toLp])
  have hMass (v : ℝ² → ℂ) (hv : MemLp v 2) : ‖hv.toLp v‖ ^ 2 = mass v := by
    rw [Lp.norm_toLp, eLpNorm_two_eq_ofReal_sqrt_mass hv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  simpa only [hMass] using hLp.norm.pow 2

private lemma tendsto_weighted_mass_of_mass_sub {w : ℝ → ℝ}
    (hw : Continuous w) (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {f : ℕ → ℝ² → ℂ} {g : ℝ² → ℂ} (hf : ∀ n, MemLp (f n) 2) (hg : MemLp g 2)
    (h : Tendsto (fun n ↦ mass (f n - g)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ mass (fun x ↦ w ‖x‖ • f n x)) atTop
      (𝓝 (mass (fun x ↦ w ‖x‖ • g x))) := by
  let F (n : ℕ) (x : ℝ²) := w ‖x‖ • f n x
  let G (x : ℝ²) := w ‖x‖ • g x
  refine tendsto_mass_of_eLpNorm_two_sub
    (fun n ↦ memLp_radial_weight_smul hw hw₀ hw₁ (hf n))
    (memLp_radial_weight_smul hw hw₀ hw₁ hg) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_two_sub_of_mass_sub hf hg h) (fun _ ↦ zero_le) (fun n ↦ ?_)
  have hEq : F n - G = fun x ↦ w ‖x‖ • (f n - g) x := by
    funext x
    exact (smul_sub _ _ _).symm
  rw [hEq]
  exact eLpNorm_radial_weight_smul_le hw hw₀ hw₁ ((hf n).sub hg).aestronglyMeasurable

/-- Weighted Strauss estimate for the almost-everywhere class of weak radial H¹ data. -/
theorem IsH1.weighted_radial_tail_bound {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hur : IsRadialAE u)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hmono : Monotone w)
    (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1) :
    ∀ᵐ x ∂volume, ‖x‖ * w ‖x‖ * ‖u x‖ ^ 2 ≤
      radialTailConstant * Real.sqrt (mass u) * Real.sqrt (weightedGradNormSq w Du) := by
  let v (n : ℕ) := mollify (radialMollifier n) u
  let Dv (n : ℕ) (j : Fin 2) := partialDeriv j (v n)
  have hv (n : ℕ) : MemLp (v n) 2 := memLp_mollify (radialMollifier_isTestFunction n) hu.memL2
  have hD (n : ℕ) (j : Fin 2) : MemLp (Dv n j) 2 := by
    change MemLp (partialDeriv j (mollify (radialMollifier n) u)) 2
    rw [hu.partialDeriv_mollify (radialMollifier_isTestFunction n) j]
    exact memLp_mollify (radialMollifier_isTestFunction n) (hu.memL2_partial j)
  have hContract (n : ℕ) : mass (v n) ≤ mass u := by
    simpa only [v, Real.norm_of_nonneg (radialMollifier_nonneg n _),
      radialMollifier_integral n, one_pow, one_mul] using
      mass_mollify_le (radialMollifier_isTestFunction n) hu.memL2
  have hK (j : Fin 2) :
      Tendsto (fun n ↦ mass (fun x ↦ w ‖x‖ • Dv n j x)) atTop
        (𝓝 (mass (fun x ↦ w ‖x‖ • Du j x))) :=
    tendsto_weighted_mass_of_mass_sub hw.continuous hw₀ hw₁
      (fun n ↦ hD n j) (hu.memL2_partial j)
      (hu.tendsto_mass_partialDeriv_mollify_sub radialMollifier_isTestFunction
        radialMollifier_nonneg radialMollifier_integral radialMollifier_support
        tendsto_mollifierRadius j)
  have hKSq : Tendsto (fun n ↦ weightedGradNormSq w (Dv n)) atTop
      (𝓝 (weightedGradNormSq w Du)) := by
    simp_rw [weightedGradNormSq_eq_sum_mass hw.continuous hw₀ hw₁ (hD _),
      weightedGradNormSq_eq_sum_mass hw.continuous hw₀ hw₁ hu.memL2_partial]
    exact (hK 0).add (hK 1)
  have hBound (n : ℕ) (x : ℝ²) : ‖x‖ * w ‖x‖ * ‖v n x‖ ^ 2 ≤
      radialTailConstant * Real.sqrt (mass u) * Real.sqrt (weightedGradNormSq w (Dv n)) := by
    have hC : ContDiff ℝ 1 (v n) :=
      (contDiff_mollify (radialMollifier_isTestFunction n) hu.memL2).of_le (by simp)
    have hR : IsRadial (v n) := isRadial_mollify_of_isRadialAE (radialMollifier_radial n) hur
    refine (weighted_radial_tail_bound_of_contDiff hC hR (hv n) (hD n)
      hw hmono hw₀ hw₁ x).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hContract n)) radialTailConstant_nonneg)
      (Real.sqrt_nonneg _)
  have hConv := tendsto_eLpNorm_two_sub_of_mass_sub hv hu.memL2
    (tendsto_mass_mollify_sub radialMollifier_isTestFunction radialMollifier_nonneg
      radialMollifier_integral radialMollifier_support tendsto_mollifierRadius hu.memL2)
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hConv
  obtain ⟨s, hs, hAE⟩ := hMeasure.exists_seq_tendsto_ae
  filter_upwards [hAE] with x hx
  have hlim := (hKSq.comp hs.tendsto_atTop).sqrt.const_mul
    (radialTailConstant * Real.sqrt (mass u))
  exact le_of_tendsto_of_tendsto' ((hx.norm.pow 2).const_mul (‖x‖ * w ‖x‖)) hlim
    (fun n ↦ hBound (s n) x)

/-- Strauss' radial pointwise bound for the almost-everywhere class of weak H¹ data. -/
theorem IsH1.radial_tail_bound {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (hu : IsH1 u Du)
    (hur : IsRadialAE u) : ∀ᵐ x ∂volume, ‖x‖ * ‖u x‖ ^ 2 ≤
      radialTailConstant * Real.sqrt (mass u) * Real.sqrt (gradNormSq Du) := by
  simpa only [mul_one, weightedGradNormSq_one] using
    hu.weighted_radial_tail_bound hur (w := fun _ ↦ 1) contDiff_const
      (fun _ _ _ ↦ le_rfl) (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)

/-- A nonnegative monotone weight vanishing through radius R gives the weighted cubic
exterior estimate. -/
theorem IsH1.weighted_quartic_integral_le {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hur : IsRadialAE u)
    {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hmono : Monotone w)
    (hw₀ : ∀ r, 0 ≤ w r) (hw₁ : ∀ r, w r ≤ 1)
    {R : ℝ} (hR : 0 < R) (hzero : ∀ r ≤ R, w r = 0) :
    (∫ x, w ‖x‖ * ‖u x‖ ^ 4) ≤
      (radialTailConstant / R) * mass u * Real.sqrt (mass u) *
        Real.sqrt (weightedGradNormSq w Du) := by
  let B := radialTailConstant * Real.sqrt (mass u) * Real.sqrt (weightedGradNormSq w Du)
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg radialTailConstant_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hUpper : ∀ᵐ x ∂volume, w ‖x‖ * ‖u x‖ ^ 4 ≤ (B / R) * ‖u x‖ ^ 2 := by
    filter_upwards [hu.weighted_radial_tail_bound hur hw hmono hw₀ hw₁] with x hx
    have hW : w ‖x‖ * ‖u x‖ ^ 2 ≤ B / R := by
      by_cases h : ‖x‖ ≤ R
      · rw [hzero ‖x‖ h, zero_mul]
        exact div_nonneg hB hR.le
      · apply (le_div_iff₀ hR).2
        calc
          _ = R * (w ‖x‖ * ‖u x‖ ^ 2) := mul_comm _ _
          _ ≤ ‖x‖ * (w ‖x‖ * ‖u x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_of_not_ge h) (mul_nonneg (hw₀ _) (sq_nonneg _))
          _ ≤ B := by simpa only [B, mul_assoc] using hx
    calc
      _ = (w ‖x‖ * ‖u x‖ ^ 2) * ‖u x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  have hDom := hu.memL2.norm.integrable_sq.const_mul (B / R)
  have hMeas : AEStronglyMeasurable (fun x ↦ w ‖x‖ * ‖u x‖ ^ 4) volume :=
    (hw.continuous.comp continuous_norm).aestronglyMeasurable.mul
      (hu.memL2.aestronglyMeasurable.norm.pow 4)
  have hIntegrable := hDom.mono_nonneg hMeas
    (.of_forall fun x ↦ mul_nonneg (hw₀ _) (by positivity)) hUpper
  calc
    _ ≤ ∫ x, (B / R) * ‖u x‖ ^ 2 := integral_mono_ae hIntegrable hDom hUpper
    _ = _ := by
      rw [integral_const_mul]
      change (B / R) * mass u = _
      dsimp [B]
      ring

/-- The radial pointwise bound implies an exterior L^{p+1} estimate at every positive radius. -/
theorem IsH1.radial_exterior_integral_le {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hur : IsRadialAE u) {p Q : ℝ} (hp : 3 ≤ p) (hQ : 0 < Q) :
    (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u x‖ ^ (p + 1)) ≤
      mass u * ((radialTailConstant * Real.sqrt (mass u) * Real.sqrt (gradNormSq Du)) / Q)
        ^ ((p - 1) / 2) := by
  let K := radialTailConstant * Real.sqrt (mass u) * Real.sqrt (gradNormSq Du)
  let E := {x : ℝ² | Q < ‖x‖}
  let c := (K / Q) ^ ((p - 1) / 2)
  have hE : MeasurableSet E := measurableSet_lt measurable_const continuous_norm.measurable
  have hInt := hu.integrable_nonlinear_density hp
  have hSq := hu.memL2.norm.integrable_sq
  have hPoint : ∀ᵐ x ∂volume.restrict E, ‖u x‖ ^ (p + 1) ≤ ‖u x‖ ^ 2 * c := by
    filter_upwards [ae_restrict_of_ae (hu.radial_tail_bound hur), ae_restrict_mem hE] with x hx hxE
    have hN : ‖u x‖ ^ 2 ≤ K / Q := by
      apply (le_div_iff₀ hQ).2
      calc
        _ = Q * ‖u x‖ ^ 2 := mul_comm _ _
        _ ≤ ‖x‖ * ‖u x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (show Q ≤ ‖x‖ from hxE.le) (sq_nonneg _)
        _ ≤ K := hx
    have hPow : ‖u x‖ ^ (p + 1) = ‖u x‖ ^ 2 * (‖u x‖ ^ 2) ^ ((p - 1) / 2) := by
      simp only [← Real.rpow_natCast]
      rw [← Real.rpow_mul (norm_nonneg _),
        ← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by linarith)]
      congr 1
      norm_num
      ring
    rw [hPow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (sq_nonneg _) hN (by linarith)) (sq_nonneg _)
  calc
    _ ≤ ∫ x in E, ‖u x‖ ^ 2 * c :=
      integral_mono_ae hInt.integrableOn (hSq.mul_const c).integrableOn hPoint
    _ = (∫ x in E, ‖u x‖ ^ 2) * c := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (setIntegral_le_integral hSq
      (.of_forall fun _ ↦ sq_nonneg _)) (Real.rpow_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg radialTailConstant_nonneg (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)) hQ.le) _)

end Blowup
