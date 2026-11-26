import BlowupFormalization.WeightProperties

/-! # A localized virial weight for the critical cubic exponent -/

open Filter MeasureTheory Set Topology
open scoped ContDiff BigOperators

namespace Blowup

private noncomputable def cubicStep (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

private noncomputable def cubicSlope (s : ℝ) : ℝ := 1 - cubicStep s ^ 2

private noncomputable def cubicProfile (s : ℝ) : ℝ := ∫ t in (2 : ℝ)..s, cubicSlope t

private noncomputable def scaledRadiusSq (R : ℝ) (x : ℝ²) : ℝ := ‖x‖ ^ 2 / R ^ 2

/-- The radial cutoff used to measure the Hessian deficit at the cubic exponent.
Truncating the negative radii makes the cutoff nondecreasing on all of ℝ. -/
noncomputable def cubicVirialCutoff (R r : ℝ) : ℝ :=
  cubicStep ((max r 0) ^ 2 / R ^ 2)

/-- The weight whose radial slope in the squared radius is the deficit factor. -/
noncomputable def cubicVirialWeight (R : ℝ) (x : ℝ²) : ℝ :=
  R ^ 2 * cubicProfile (scaledRadiusSq R x)

theorem cubicVirialCutoff_norm (R : ℝ) (x : ℝ²) :
    cubicVirialCutoff R ‖x‖ = Real.smoothTransition (‖x‖ ^ 2 / R ^ 2 - 1) := by
  simp only [cubicVirialCutoff, cubicStep, max_eq_left (norm_nonneg _)]

theorem cubicVirialCutoff_nonneg (R r : ℝ) : 0 ≤ cubicVirialCutoff R r :=
  Real.smoothTransition.nonneg _

theorem cubicVirialCutoff_le_one (R r : ℝ) : cubicVirialCutoff R r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cubicVirialCutoff_monotone (R : ℝ) : Monotone (cubicVirialCutoff R) := by
  intro r t hrt
  apply Real.smoothTransition.monotone
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ hrt) 2) (sq_nonneg _)) _

theorem cubicVirialCutoff_eq_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) :
    cubicVirialCutoff R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one (sq_pos_of_pos hR)).mpr
    (pow_le_pow_left₀ (le_max_right _ _) (max_le hr hR.le) 2))

theorem cubicVirialCutoff_contDiff {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (cubicVirialCutoff R) := by
  apply contDiff_iff_contDiffAt.2
  intro r
  by_cases hr : r < R
  · have hConst : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) r := contDiffAt_const
    apply hConst.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with t ht
    exact cubicVirialCutoff_eq_zero hR ht.le
  · have hr' : 0 < r := hR.trans_le (le_of_not_gt hr)
    have hSmooth : ContDiff ℝ ∞
        (fun t : ℝ ↦ Real.smoothTransition (t ^ 2 / R ^ 2 - 1)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    apply hSmooth.contDiffAt.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr'] with t ht
    simp only [cubicVirialCutoff, cubicStep, max_eq_left ht.le]

private lemma cubicStep_contDiff : ContDiff ℝ ∞ cubicStep :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private lemma cubicSlope_contDiff : ContDiff ℝ ∞ cubicSlope :=
  contDiff_const.sub (cubicStep_contDiff.pow 2)

private lemma cubicProfile_hasDerivAt (s : ℝ) : HasDerivAt cubicProfile (cubicSlope s) s :=
  intervalIntegral.integral_hasDerivAt_right (cubicSlope_contDiff.continuous.intervalIntegrable 2 s)
    (cubicSlope_contDiff.continuous.stronglyMeasurableAtFilter _ _)
    cubicSlope_contDiff.continuous.continuousAt

private lemma cubicProfile_contDiff : ContDiff ℝ ∞ cubicProfile := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun s ↦ (cubicProfile_hasDerivAt s).differentiableAt, ?_⟩
  rw [show deriv cubicProfile = cubicSlope from funext fun s ↦ (cubicProfile_hasDerivAt s).deriv]
  exact cubicSlope_contDiff

private lemma cubicProfile_eq_zero {s : ℝ} (hs : 2 ≤ s) : cubicProfile s = 0 := by
  calc
    _ = ∫ _ in (2 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs] at ht
      have hw : cubicStep t = 1 := Real.smoothTransition.one_of_one_le (by linarith [ht.1])
      simp only [cubicSlope, hw, one_pow, sub_self]
    _ = 0 := intervalIntegral.integral_zero

private lemma scaledRadiusSq_contDiff (R : ℝ) : ContDiff ℝ ∞ (scaledRadiusSq R) :=
  (contDiff_norm_sq ℝ).div_const _

/-- The cubic weight vanishes when the squared radius reaches twice the squared scale. -/
theorem cubicVirialWeight_eq_zero {R : ℝ} {x : ℝ²} (hx : 2 ≤ ‖x‖ ^ 2 / R ^ 2) :
    cubicVirialWeight R x = 0 := by
  have h := cubicProfile_eq_zero (show 2 ≤ scaledRadiusSq R x from hx)
  simp only [cubicVirialWeight, h, mul_zero]

private lemma cubicProfile_eq_add_of_le_one {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    cubicProfile s = cubicProfile 0 + s := by
  have hI : (∫ t in (0 : ℝ)..s, cubicSlope t) = s := by
    calc
      _ = ∫ _ in (0 : ℝ)..s, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs₀] at ht
        have hw : cubicStep t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith [ht.2])
        simp [cubicSlope, hw]
      _ = s := by simp
  have hc := cubicSlope_contDiff.continuous
  calc
    _ = cubicProfile 0 + ∫ t in (0 : ℝ)..s, cubicSlope t := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 2 0) (hc.intervalIntegrable 0 s)).symm
    _ = _ := by rw [hI]

/-- Inside the localization radius, the weight differs from the squared norm by a constant. -/
theorem cubicVirialWeight_eq_add_norm_sq {R : ℝ} (hR : 0 < R) {x : ℝ²} (hx : ‖x‖ ≤ R) :
    cubicVirialWeight R x = cubicVirialWeight R 0 + ‖x‖ ^ 2 := by
  have h₀ : 0 ≤ ‖x‖ ^ 2 / R ^ 2 := by positivity
  have h₁ : ‖x‖ ^ 2 / R ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hR)).mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2)
  unfold cubicVirialWeight scaledRadiusSq
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
  rw [cubicProfile_eq_add_of_le_one h₀ h₁, mul_add, mul_comm (R ^ 2) (‖x‖ ^ 2 / R ^ 2),
    div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')]

/-- The weight vanishes outside a ball and is smooth at the origin by construction. -/
theorem cubicVirialWeight_isTestFunction {R : ℝ} (hR : 0 < R) :
    IsTestFunction (cubicVirialWeight R) := by
  refine ⟨contDiff_const.mul (cubicProfile_contDiff.comp (scaledRadiusSq_contDiff R)), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ²) (2 * R)) fun x hx ↦ ?_
  have hx' : 2 * R < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hs : 2 ≤ scaledRadiusSq R x := by
    apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
    nlinarith [pow_le_pow_left₀ (show 0 ≤ 2 * R by positivity) hx'.le 2, sq_nonneg R]
  exact cubicVirialWeight_eq_zero hs

theorem cubicVirialWeight_bddBelow {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, ∀ x, L ≤ cubicVirialWeight R x := by
  have h := cubicVirialWeight_isTestFunction hR
  obtain ⟨L, hL⟩ := (h.2.isCompact_range h.1.continuous).bddBelow
  exact ⟨L, fun x ↦ hL ⟨x, rfl⟩⟩

private lemma partialDeriv_scaledRadiusSq (R : ℝ) (j : Fin 2) (x : ℝ²) :
    partialDeriv j (scaledRadiusSq R) x = 2 * x j / R ^ 2 := by
  have hd : DifferentiableAt ℝ (fun y : ℝ² ↦ ‖y‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero) x
  unfold partialDeriv scaledRadiusSq
  simp_rw [div_eq_inv_mul]
  rw [fderiv_const_mul hd]
  simp [fderiv_norm_sq_apply, EuclideanSpace.inner_single_right, two_smul, two_mul, mul_add]

private lemma partialDeriv_coord (j k : Fin 2) (x : ℝ²) :
    partialDeriv j (fun y : ℝ² ↦ y k) x = if j = k then 1 else 0 := by
  let p := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) k
  change fderiv ℝ p x (EuclideanSpace.single j 1) = _
  rw [(p.hasFDerivAt (x := x)).fderiv]
  simp [p, EuclideanSpace.single, PiLp.single_apply, eq_comm]

private lemma partialDeriv_cubicVirialWeight {R : ℝ} (hR : 0 < R) (k : Fin 2) :
    partialDeriv k (cubicVirialWeight R) = fun x ↦
      2 * (x k * cubicSlope (scaledRadiusSq R x)) := by
  funext x
  have h := ((cubicProfile_hasDerivAt (scaledRadiusSq R x)).comp_hasFDerivAt x
    (((scaledRadiusSq_contDiff R).differentiable (by simp) x).hasFDerivAt)).const_mul (R ^ 2)
  change HasFDerivAt (cubicVirialWeight R) _ x at h
  unfold partialDeriv
  rw [h.fderiv]
  change R ^ 2 * (cubicSlope (scaledRadiusSq R x) * partialDeriv k (scaledRadiusSq R) x) = _
  rw [partialDeriv_scaledRadiusSq]
  field_simp

private lemma hessian_cubicVirialWeight {R : ℝ} (hR : 0 < R) (j k : Fin 2) (x : ℝ²) :
    partialDeriv j (partialDeriv k (cubicVirialWeight R)) x =
      (if j = k then 2 * cubicSlope (scaledRadiusSq R x) else 0) +
      (4 / R ^ 2) * deriv cubicSlope (scaledRadiusSq R x) * (x j * x k) := by
  let X (y : ℝ²) := y k
  let Y (y : ℝ²) := cubicSlope (scaledRadiusSq R y)
  have hX : DifferentiableAt ℝ X x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) k).differentiableAt
  have hSlope := (cubicSlope_contDiff.differentiable (by simp) (scaledRadiusSq R x)).hasDerivAt
  have hY := hSlope.comp_hasFDerivAt x
    (((scaledRadiusSq_contDiff R).differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt Y _ x at hY
  rw [partialDeriv_cubicVirialWeight hR]
  change fderiv ℝ (fun y ↦ 2 * (X y * Y y)) x (EuclideanSpace.single j 1) = _
  have hProd := (hX.hasFDerivAt.mul hY).const_mul (2 : ℝ)
  change HasFDerivAt (fun y ↦ 2 * (X y * Y y)) _ x at hProd
  rw [hProd.fderiv]
  change 2 * (X x * (deriv cubicSlope (scaledRadiusSq R x) *
    partialDeriv j (scaledRadiusSq R) x) + Y x * partialDeriv j (fun y : ℝ² ↦ y k) x) = _
  rw [partialDeriv_scaledRadiusSq, partialDeriv_coord]
  dsimp only [X, Y]
  split <;> ring

private lemma cubicStep_monotone : Monotone cubicStep := by
  intro s t hst
  exact Real.smoothTransition.monotone (sub_le_sub_right hst _)

private lemma cubicStep_nonneg (s : ℝ) : 0 ≤ cubicStep s := Real.smoothTransition.nonneg _

private lemma cubicStep_le_one (s : ℝ) : cubicStep s ≤ 1 := Real.smoothTransition.le_one _

private lemma deriv_cubicSlope (s : ℝ) :
    deriv cubicSlope s = -2 * cubicStep s * deriv cubicStep s := by
  have h := (hasDerivAt_const s (1 : ℝ)).sub
    ((cubicStep_contDiff.differentiable (by simp) s).hasDerivAt.pow 2)
  change HasDerivAt cubicSlope _ s at h
  rw [h.deriv]
  ring

private lemma deriv_cubicSlope_nonpos (s : ℝ) : deriv cubicSlope s ≤ 0 := by
  rw [deriv_cubicSlope]
  have h := cubicStep_monotone.deriv_nonneg (x := s)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (cubicStep_nonneg s)) h

/-- The drop in the Hessian quadratic form controls the square of the radial cutoff. -/
theorem hessian_cubicVirialWeight_le {R : ℝ} (hR : 0 < R) (x : ℝ²) (z : Fin 2 → ℂ) :
    ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k (cubicVirialWeight R)) x *
      (z j * starRingEnd ℂ (z k)).re ≤
      2 * (1 - (cubicVirialCutoff R ‖x‖) ^ 2) * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) := by
  let s := scaledRadiusSq R x
  have hCut : cubicVirialCutoff R ‖x‖ = cubicStep s := cubicVirialCutoff_norm R x
  rw [hCut]
  have hForm :
      (∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k (cubicVirialWeight R)) x *
        (z j * starRingEnd ℂ (z k)).re) =
      2 * cubicSlope s * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) +
      (4 / R ^ 2) * deriv cubicSlope s *
        ((x 0 * (z 0).re + x 1 * (z 1).re) ^ 2 +
          (x 0 * (z 0).im + x 1 * (z 1).im) ^ 2) := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Fin.sum_univ_two, hessian_cubicVirialWeight hR, Fin.zero_ne_one, h10,
      ite_true, ite_false, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply, s]
    ring
  rw [hForm]
  change 2 * cubicSlope s * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) + _ ≤
    2 * cubicSlope s * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2)
  exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (deriv_cubicSlope_nonpos s)) (by positivity))

private lemma laplacian_cubicVirialWeight_formula {R : ℝ} (hR : 0 < R) (x : ℝ²) :
    laplacian (cubicVirialWeight R) x =
      4 * cubicSlope (scaledRadiusSq R x) +
        4 * scaledRadiusSq R x * deriv cubicSlope (scaledRadiusSq R x) := by
  unfold laplacian
  rw [hessian_cubicVirialWeight hR 0 0, hessian_cubicVirialWeight hR 1 1]
  simp only [ite_true]
  unfold scaledRadiusSq
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  ring

private lemma deriv_cubicStep_hasCompactSupport : HasCompactSupport (deriv cubicStep) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
  intro s hs
  simp only [mem_Icc, not_and_or, not_le] at hs
  rcases hs with hs | hs
  · have he : cubicStep =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hs] with t ht
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [he.deriv_eq, deriv_const]
  · have he : cubicStep =ᶠ[𝓝 s] fun _ ↦ (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      exact Real.smoothTransition.one_of_one_le (by linarith)
    rw [he.deriv_eq, deriv_const]

/-- The cubic Laplacian deficit is bounded by a scale-independent multiple of the cutoff. -/
theorem laplacian_cubicVirialWeight_deficit_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R > 0, ∀ x : ℝ²,
      4 - laplacian (cubicVirialWeight R) x ≤ B * cubicVirialCutoff R ‖x‖ := by
  have hc : Continuous (fun s ↦ s * deriv cubicStep s) :=
    continuous_id.mul (cubicStep_contDiff.continuous_deriv (by simp))
  have hs : HasCompactSupport (fun s ↦ s * deriv cubicStep s) :=
    deriv_cubicStep_hasCompactSupport.mul_left
  obtain ⟨B, hB⟩ := (hs.isCompact_range hc).bddAbove
  have hB₀ : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨4 + 8 * max B 0, by positivity, fun R hR x ↦ ?_⟩
  let s := scaledRadiusSq R x
  let w := cubicStep s
  have hCut : cubicVirialCutoff R ‖x‖ = w := cubicVirialCutoff_norm R x
  rw [hCut, laplacian_cubicVirialWeight_formula hR, deriv_cubicSlope]
  change 4 - (4 * (1 - w ^ 2) + 4 * s * (-2 * w * deriv cubicStep s)) ≤
    (4 + 8 * max B 0) * w
  have hw : 0 ≤ w := cubicStep_nonneg s
  have hwSq : w ^ 2 ≤ w := by
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr (cubicStep_le_one s))]
  have hBd : s * deriv cubicStep s ≤ B := hB ⟨s, rfl⟩
  have hProd : (s * deriv cubicStep s) * w ≤ max B 0 * w :=
    mul_le_mul_of_nonneg_right (hBd.trans (le_max_left _ _)) hw
  nlinarith only [hwSq, hProd]

private lemma partialDeriv_dilate_real {f : ℝ² → ℝ} (hf : Differentiable ℝ f)
    (a b : ℝ) (j : Fin 2) :
    partialDeriv j (fun x ↦ a * f (b • x)) = fun x ↦ (a * b) * partialDeriv j f (b • x) := by
  funext x
  have hd := ((hf (b • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul b)).const_mul a
  unfold partialDeriv
  simp only [Function.comp_apply] at hd
  rw [hd.fderiv]
  simp [mul_assoc]

private lemma laplacian_dilate_real {f : ℝ² → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    laplacian (fun x ↦ a * f (b • x)) = fun x ↦ (a * b ^ 2) * laplacian f (b • x) := by
  have hD (j : Fin 2) : ContDiff ℝ ∞ (partialDeriv j f) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  funext x
  unfold laplacian
  simp only [partialDeriv_dilate_real (hf.differentiable (by simp)),
    partialDeriv_dilate_real ((hD _).differentiable (by simp))]
  ring

private lemma cubicVirialWeight_dilate {R : ℝ} (hR : 0 < R) :
    cubicVirialWeight R = fun x ↦ R ^ 2 * cubicVirialWeight 1 (R⁻¹ • x) := by
  funext x
  have hSq : ‖R⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / R ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), mul_pow, inv_pow, div_eq_inv_mul]
  simp only [cubicVirialWeight, scaledRadiusSq, hSq, one_pow, div_one, one_mul]

private lemma laplacian_cubicVirialWeight_dilate {R : ℝ} (hR : 0 < R) :
    laplacian (cubicVirialWeight R) = fun x ↦ laplacian (cubicVirialWeight 1) (R⁻¹ • x) := by
  rw [cubicVirialWeight_dilate hR,
    laplacian_dilate_real (cubicVirialWeight_isTestFunction one_pos).1]
  simp [hR.ne']

/-- The biharmonic weight is bounded by a scale-independent constant times the inverse square
of the localization radius. -/
theorem bilaplacian_cubicVirialWeight_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R > 0, ∀ x : ℝ²,
      |laplacian (laplacian (cubicVirialWeight R)) x| ≤ D / R ^ 2 := by
  have hΔ := (cubicVirialWeight_isTestFunction one_pos).laplacian
  have hΔΔ := hΔ.laplacian
  obtain ⟨D, hD⟩ := ((hΔΔ.2.isCompact_range hΔΔ.1.continuous).image continuous_abs).bddAbove
  have hDabs (x : ℝ²) : |laplacian (laplacian (cubicVirialWeight 1)) x| ≤ D :=
    hD ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨D, (abs_nonneg _).trans (hDabs 0), fun R hR x ↦ ?_⟩
  rw [laplacian_cubicVirialWeight_dilate hR]
  have scale := laplacian_dilate_real hΔ.1 1 R⁻¹
  simp only [one_mul] at scale
  rw [scale, abs_mul, abs_of_nonneg (sq_nonneg _), inv_pow, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hDabs _) (by positivity)

end Blowup
