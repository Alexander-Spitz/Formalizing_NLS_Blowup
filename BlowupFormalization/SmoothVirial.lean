import BlowupFormalization.LocalizedVirial

/-! # First localized virial identity for smooth solutions -/

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace Blowup

private lemma hasDerivAt_time_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ² → E} (hf : ContDiff ℝ 1 (Function.uncurry f)) (t : ℝ) (x : ℝ²) :
    HasDerivAt (fun s ↦ f s x) (fderiv ℝ (Function.uncurry f) (t, x) (1, 0)) t := by
  have hs := (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact ((hf.differentiable (by simp) (t, x)).hasFDerivAt).comp_hasDerivAt t hs

/-- A jointly continuously differentiable integrand can be differentiated in time against a
fixed continuous, compactly supported spatial weight. -/
theorem hasDerivAt_integral_mul_of_contDiff {A : ℝ² → ℝ} (hA : Continuous A)
    (hAc : HasCompactSupport A) {f : ℝ → ℝ² → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, A x * f s x) (∫ x, A x * deriv (fun s ↦ f s x) t) t := by
  let F (s : ℝ) (x : ℝ²) := A x * f s x
  let F' (s : ℝ) (x : ℝ²) := A x * fderiv ℝ (Function.uncurry f) (s, x) (1, 0)
  have hF (s : ℝ) : Continuous (F s) :=
    hA.mul (hf.continuous.comp (continuous_const.prodMk continuous_id))
  have hF' : Continuous (Function.uncurry F') :=
    (hA.comp continuous_snd).mul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hFI : Integrable (F t) := (hF t).integrable_of_hasCompactSupport hAc.mul_right
  have hF'M : AEStronglyMeasurable (F' t) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  let J := Icc (t - 1) (t + 1)
  have hJ : J ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hAc).exists_bound_of_continuousOn
    (f := Function.uncurry F') hF'.continuousOn
  have hBound : ∀ᵐ x ∂volume, ∀ s ∈ J, ‖F' s x‖ ≤ (tsupport A).indicator (fun _ ↦ C) x :=
    ae_of_all _ fun x s hs ↦ by
      by_cases hx : x ∈ tsupport A
      · rw [indicator_of_mem hx]
        exact hC (s, x) ⟨hs, hx⟩
      · have hAx : A x = 0 := by
          by_contra h
          exact hx (subset_tsupport A h)
        rw [indicator_of_notMem hx]
        simp [F', hAx]
  have hCI : Integrable ((tsupport A).indicator (fun _ ↦ C)) :=
    (integrable_indicator_iff (isClosed_tsupport A).measurableSet).2
      (integrableOn_const hAc.measure_lt_top.ne)
  have hDiff (s : ℝ) (x : ℝ²) : HasDerivAt (fun r ↦ F r x) (F' s x) s :=
    (hasDerivAt_time_slice hf s x).const_mul (A x)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ
    (Eventually.of_forall fun s ↦ (hF s).aestronglyMeasurable) hFI hF'M hBound hCI
    (ae_of_all _ fun x s _ ↦ hDiff s x)).2
  simpa only [F, F', ← (hasDerivAt_time_slice hf t _).deriv] using h

private lemma contDiff_partialDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ² → E} {m n : ℕ∞ω} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (j : Fin 2) :
    ContDiff ℝ m (partialDeriv j f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

private lemma integral_im_mul_partialDeriv_eq_neg {f g : ℝ² → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) (j : Fin 2) :
    ∫ x, (f x * partialDeriv j g x).im = -∫ x, (partialDeriv j f x * g x).im := by
  let e := EuclideanSpace.single j (1 : ℝ)
  have hf' : Continuous (partialDeriv j f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (partialDeriv j g) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hLeft : Integrable (fun x ↦ f x * partialDeriv j g x) :=
    (hf.continuous.mul hg').integrable_of_hasCompactSupport hfc.mul_right
  have hRight : Integrable (fun x ↦ partialDeriv j f x * g x) :=
    (hf'.mul hg.continuous).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ e).mul_right
  have hParts : ∫ x, f x * partialDeriv j g x = -∫ x, partialDeriv j f x * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hRight hLeft
      ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right)
      (fun x _ ↦ hf.differentiable (by simp) x)
      (fun x _ ↦ hg.differentiable (by simp) x)
  have hIm := congrArg (RCLike.im : ℂ →+ ℝ) hParts
  simpa only [map_neg, ← integral_im hLeft, ← integral_im hRight, RCLike.im_eq_complex_im]
    using hIm

private lemma integral_im_weighted_partialDeriv_eq_neg {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {u : ℝ² → ℂ} (hu : ContDiff ℝ 2 u) (j : Fin 2) :
    ∫ x, ((A x : ℂ) * starRingEnd ℂ (u x) * partialDeriv j (partialDeriv j u) x).im =
      -∫ x, (starRingEnd ℂ (u x) * ((partialDeriv j A x : ℝ) : ℂ) * partialDeriv j u x).im := by
  let B (x : ℝ²) : ℂ := A x
  let v (x : ℝ²) : ℂ := starRingEnd ℂ (u x)
  let f (x : ℝ²) : ℂ := B x * v x
  let g := partialDeriv j u
  have hB : ContDiff ℝ 1 B := Complex.ofRealCLM.contDiff.comp (hA.1.of_le (by simp))
  have hv : ContDiff ℝ 1 v :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp (hu.of_le (by simp))
  have hf : ContDiff ℝ 1 f := hB.mul hv
  have hg : ContDiff ℝ 1 g := contDiff_partialDeriv hu (by norm_num) j
  have hfc : HasCompactSupport f :=
    (hA.2.comp_left Complex.ofReal_zero : HasCompactSupport B).mul_right
  have hProd (x : ℝ²) :
      (partialDeriv j f x * g x).im =
        (starRingEnd ℂ (u x) * ((partialDeriv j A x : ℝ) : ℂ) * partialDeriv j u x).im := by
    have hA' := (hA.1.differentiable (by simp) x).hasFDerivAt
    have hu' := (hu.differentiable (by simp) x).hasFDerivAt
    have hB' := (Complex.ofRealCLM.hasFDerivAt.comp x hA').fderiv
    have hv' := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hu').fderiv
    change fderiv ℝ B x = _ at hB'
    change fderiv ℝ v x = _ at hv'
    change (fderiv ℝ (B * v) x (EuclideanSpace.single j 1) * g x).im = _
    rw [fderiv_mul (hB.differentiable (by simp) x) (hv.differentiable (by simp) x), hB', hv']
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, Complex.ofRealCLM_apply]
    change (((A x : ℂ) * starRingEnd ℂ (g x) +
      starRingEnd ℂ (u x) * ((partialDeriv j A x : ℝ) : ℂ)) * g x).im = _
    rw [add_mul, Complex.add_im, mul_assoc, mul_comm (starRingEnd ℂ (g x)) (g x),
      Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im, zero_add]
  have hIm := integral_im_mul_partialDeriv_eq_neg hf hg hfc j
  rw [show (fun x ↦ (partialDeriv j f x * g x).im) = _ from funext hProd] at hIm
  exact hIm

/-- Spatial integration by parts converts the imaginary part of the weighted Laplacian
term to the negative gradient term in the first virial identity. -/
theorem integral_im_weighted_laplacian_eq_neg {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {u : ℝ² → ℂ} (hu : ContDiff ℝ 2 u) :
    ∫ x, ((A x : ℂ) * starRingEnd ℂ (u x) * laplacian u x).im =
      -∫ x, (starRingEnd ℂ (u x) *
        (((partialDeriv 0 A x : ℝ) : ℂ) * partialDeriv 0 u x +
          ((partialDeriv 1 A x : ℝ) : ℂ) * partialDeriv 1 u x)).im := by
  have hA' : ContDiff ℝ 2 A := hA.1.of_le (by simp)
  have hcA : HasCompactSupport (fun x ↦ (A x : ℂ)) := hA.2.comp_left Complex.ofReal_zero
  have hcA' (j : Fin 2) : HasCompactSupport (fun x ↦ ((partialDeriv j A x : ℝ) : ℂ)) :=
    (hA.2.fderiv_apply ℝ (EuclideanSpace.single j 1)).comp_left Complex.ofReal_zero
  have hV : Continuous (fun x ↦ starRingEnd ℂ (u x)) :=
    Complex.continuous_conj.comp hu.continuous
  have hD (j : Fin 2) : ContDiff ℝ 1 (partialDeriv j u) :=
    contDiff_partialDeriv hu (by norm_num) j
  have hD' (j : Fin 2) : Continuous (partialDeriv j (partialDeriv j u)) :=
    ((hD j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hL (j : Fin 2) :
      Integrable (fun x ↦ ((A x : ℂ) * starRingEnd ℂ (u x) *
        partialDeriv j (partialDeriv j u) x).im) :=
    (((Complex.continuous_ofReal.comp hA.1.continuous).mul hV).mul (hD' j)
      |>.integrable_of_hasCompactSupport hcA.mul_right.mul_right).im
  have hR (j : Fin 2) :
      Integrable (fun x ↦ (starRingEnd ℂ (u x) * ((partialDeriv j A x : ℝ) : ℂ) *
        partialDeriv j u x).im) :=
    ((hV.mul (Complex.continuous_ofReal.comp
      (contDiff_partialDeriv (m := 1) hA' (by norm_num) j).continuous)).mul (hD j).continuous
        |>.integrable_of_hasCompactSupport (hcA' j).mul_left.mul_right).im
  simp only [laplacian, mul_add, Complex.add_im, ← mul_assoc]
  rw [integral_add (hL 0) (hL 1), integral_add (hR 0) (hR 1),
    integral_im_weighted_partialDeriv_eq_neg hA hu 0,
    integral_im_weighted_partialDeriv_eq_neg hA hu 1, neg_add]

/-- The first derivative of the localized variance (4.2) is the expression (4.4)
for a jointly C² solution of the strong NLS equation at the time under consideration. -/
theorem hasDerivAt_localizedVariance_of_smooth_nls
    {u : ℝ → ℝ² → ℂ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {A : ℝ² → ℝ} (hA : IsTestFunction A) {p t : ℝ}
    (hNLS : ∀ x, Complex.I * deriv (fun s ↦ u s x) t +
      laplacian (u t) x + nonlinearity p (u t x) = 0) :
    HasDerivAt (fun s ↦ ∫ x, A x * ‖u s x‖ ^ 2)
      (virialFirstDeriv A (u t) (fun j ↦ partialDeriv j (u t))) t := by
  have hu1 : ContDiff ℝ 1 (Function.uncurry u) := hu.of_le (by norm_num)
  have hSpace : ContDiff ℝ 2 (u t) := hu.comp (contDiff_const.prodMk contDiff_id)
  have hNorm : ContDiff ℝ 1 (Function.uncurry (fun s x ↦ ‖u s x‖ ^ 2)) := hu1.norm_sq ℂ
  have hVar := hasDerivAt_integral_mul_of_contDiff hA.1.continuous hA.2 hNorm t
  have hDensity (x : ℝ²) : A x * deriv (fun s ↦ ‖u s x‖ ^ 2) t =
      (-2) * ((A x : ℂ) * starRingEnd ℂ (u t x) * laplacian (u t) x).im := by
    have hd := hasDerivAt_time_slice hu1 t x
    have hNormDeriv : deriv (fun s ↦ ‖u s x‖ ^ 2) t =
        2 * (deriv (fun s ↦ u s x) t * starRingEnd ℂ (u t x)).re := by
      simpa only [Complex.inner, ← hd.deriv] using hd.norm_sq.deriv
    have hTime : deriv (fun s ↦ u s x) t =
        Complex.I * (laplacian (u t) x + nonlinearity p (u t x)) := by
      have h := congrArg (fun z : ℂ ↦ Complex.I * z) (hNLS x)
      simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, mul_zero] at h
      linear_combination -h
    have hNonlinear : (nonlinearity p (u t x) * starRingEnd ℂ (u t x)).im = 0 := by
      rw [nonlinearity, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [hNormDeriv, hTime, mul_assoc, Complex.I_mul_re, add_mul, Complex.add_im, hNonlinear,
      add_zero]
    rw [mul_comm (laplacian (u t) x), mul_assoc]
    simp only [Complex.mul_im (A x : ℂ), Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  have hValue : (∫ x, A x * deriv (fun s ↦ ‖u s x‖ ^ 2) t) =
      virialFirstDeriv A (u t) (fun j ↦ partialDeriv j (u t)) := by
    simp_rw [hDensity]
    rw [integral_const_mul, integral_im_weighted_laplacian_eq_neg hA hSpace, mul_neg, ← neg_mul]
    simp [virialFirstDeriv]
  exact hValue ▸ hVar

end Blowup
