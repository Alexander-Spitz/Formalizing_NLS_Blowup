import BlowupFormalization.SmoothVirial

/-! # Differentiation of the first virial current -/

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Blowup

/-- The contribution to the time derivative of the virial current when the field evolves
by `vₜ = i B`. -/
noncomputable def virialSource (A : ℝ² → ℝ) (u : ℝ² → ℂ)
    (Du : Fin 2 → ℝ² → ℂ) (B : ℝ² → ℂ) : ℝ :=
  -4 * (∑ j : Fin 2, ∫ x, (starRingEnd ℂ (Du j x) *
    (((partialDeriv j A x : ℝ) : ℂ) * B x)).re) -
  2 * (∫ x, (starRingEnd ℂ (u x) * (((laplacian A x : ℝ) : ℂ) * B x)).re)

private lemma integrable_weighted_pair {a : ℝ² → ℝ} (ha : IsTestFunction a)
    {f g : ℝ² → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x ↦ starRingEnd ℂ (f x) * ((a x : ℂ) * g x)) :=
  ((Complex.continuous_conj.comp hf).mul ((Complex.continuous_ofReal.comp ha.1.continuous).mul hg))
    |>.integrable_of_hasCompactSupport (ha.2.comp_left Complex.ofReal_zero).mul_right.mul_left

private lemma integral_re_weighted_add {a : ℝ² → ℝ} (ha : IsTestFunction a)
    {f B₁ B₂ : ℝ² → ℂ} (hf : Continuous f) (hB₁ : Continuous B₁) (hB₂ : Continuous B₂) :
    (∫ x, (starRingEnd ℂ (f x) * ((a x : ℂ) * (B₁ + B₂) x)).re) =
      (∫ x, (starRingEnd ℂ (f x) * ((a x : ℂ) * B₁ x)).re) +
      (∫ x, (starRingEnd ℂ (f x) * ((a x : ℂ) * B₂ x)).re) := by
  simp only [Pi.add_apply, mul_add, Complex.add_re]
  exact integral_add (integrable_weighted_pair ha hf hB₁).re
    (integrable_weighted_pair ha hf hB₂).re

/-- The virial source is additive in the field `B` for continuous spatial inputs. -/
theorem virialSource_add {A : ℝ² → ℝ} (hA : IsTestFunction A) {u : ℝ² → ℂ}
    {Du : Fin 2 → ℝ² → ℂ} (hu : Continuous u) (hDu : ∀ j, Continuous (Du j))
    {B₁ B₂ : ℝ² → ℂ} (hB₁ : Continuous B₁) (hB₂ : Continuous B₂) :
    virialSource A u Du (B₁ + B₂) = virialSource A u Du B₁ + virialSource A u Du B₂ := by
  simp only [virialSource, integral_re_weighted_add (hA.partialDeriv _) (hDu _) hB₁ hB₂,
    integral_re_weighted_add hA.laplacian hu hB₁ hB₂, Finset.sum_add_distrib]
  ring

private lemma im_weighted_pair (a : ℝ) (z w : ℂ) :
    (starRingEnd ℂ z * ((a : ℂ) * w)).im = a * (starRingEnd ℂ z * w).im := by
  rw [mul_left_comm, Complex.im_ofReal_mul]

private lemma im_conj_time_mul (a : ℝ) (d b : ℂ) :
    a * (starRingEnd ℂ (Complex.I * b) * d).im = -(starRingEnd ℂ d * ((a : ℂ) * b)).re := by
  rw [map_mul, Complex.conj_I]
  rw [show -Complex.I * starRingEnd ℂ b * d = -((starRingEnd ℂ b * d) * Complex.I) by ring,
    Complex.neg_im, Complex.mul_I_im, mul_left_comm (starRingEnd ℂ d), Complex.re_ofReal_mul]
  have hre : (starRingEnd ℂ b * d).re = (starRingEnd ℂ d * b).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre, mul_neg]

private lemma im_pair_mul_time (a : ℝ) (u b : ℂ) :
    ((starRingEnd ℂ u * (a : ℂ)) * (Complex.I * b)).im =
      (starRingEnd ℂ u * ((a : ℂ) * b)).re := by
  rw [show (starRingEnd ℂ u * (a : ℂ)) * (Complex.I * b) =
    (starRingEnd ℂ u * ((a : ℂ) * b)) * Complex.I by ring, Complex.mul_I_im]

private lemma partialDeriv_weighted_conj {a : ℝ² → ℝ} (ha : IsTestFunction a)
    {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u) (j : Fin 2) (x : ℝ²) :
    partialDeriv j (fun y ↦ (a y : ℂ) * starRingEnd ℂ (u y)) x =
      starRingEnd ℂ (partialDeriv j u x) * (a x : ℂ) +
        starRingEnd ℂ (u x) * ((partialDeriv j a x : ℝ) : ℂ) := by
  let aC (y : ℝ²) : ℂ := a y
  let uC (y : ℝ²) : ℂ := starRingEnd ℂ (u y)
  have ha' := Complex.ofRealCLM.hasFDerivAt.comp x
    ((ha.1.differentiable (by simp) x).hasFDerivAt)
  have hu' := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x
    ((hu.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt aC _ x at ha'
  change HasFDerivAt uC _ x at hu'
  change fderiv ℝ (aC * uC) x (EuclideanSpace.single j 1) = _
  rw [(ha'.mul hu').fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    Complex.ofRealCLM_apply, partialDeriv]
  change (a x : ℂ) * starRingEnd ℂ (fderiv ℝ u x (EuclideanSpace.single j 1)) +
    starRingEnd ℂ (u x) * ((fderiv ℝ a x (EuclideanSpace.single j 1) : ℝ) : ℂ) = _
  rw [mul_comm (a x : ℂ)]

private lemma integral_current_component_derivative {a : ℝ² → ℝ} (ha : IsTestFunction a)
    {u w B : ℝ² → ℂ} (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 1 w) (hB : Continuous B)
    (hEq : ∀ x, w x = Complex.I * B x) (j : Fin 2) :
    (∫ x, a x * (starRingEnd ℂ (w x) * partialDeriv j u x +
      starRingEnd ℂ (u x) * partialDeriv j w x).im) =
      -2 * (∫ x, (starRingEnd ℂ (partialDeriv j u x) * ((a x : ℂ) * B x)).re) -
      (∫ x, (starRingEnd ℂ (u x) * (((partialDeriv j a x : ℝ) : ℂ) * B x)).re) := by
  let q (x : ℝ²) : ℂ := (a x : ℂ) * starRingEnd ℂ (u x)
  let R (x : ℝ²) := (starRingEnd ℂ (partialDeriv j u x) * ((a x : ℂ) * B x)).re
  let S (x : ℝ²) := (starRingEnd ℂ (u x) * (((partialDeriv j a x : ℝ) : ℂ) * B x)).re
  have hDu : Continuous (partialDeriv j u) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hR : Integrable R := (integrable_weighted_pair ha hDu hB).re
  have hS : Integrable S := (integrable_weighted_pair (ha.partialDeriv j) hu.continuous hB).re
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hq : ContDiff ℝ 1 q :=
    (Complex.ofRealCLM.contDiff.comp (ha.1.of_le (by simp))).mul
      (Complex.conjCLE.toContinuousLinearMap.contDiff.comp hu₁)
  have hqC : HasCompactSupport q := (ha.2.comp_left Complex.ofReal_zero).mul_right
  have hDw : Continuous (partialDeriv j w) :=
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  have hQInt : Integrable (fun x ↦ (q x * partialDeriv j w x).im) :=
    ((hq.continuous.mul hDw).integrable_of_hasCompactSupport hqC.mul_right).im
  have hParts := integral_im_mul_partialDeriv_eq_neg hq hw hqC j
  have hSplit (x : ℝ²) :
      a x * (starRingEnd ℂ (w x) * partialDeriv j u x +
        starRingEnd ℂ (u x) * partialDeriv j w x).im =
        -R x + (q x * partialDeriv j w x).im := by
    rw [Complex.add_im, mul_add, hEq, im_conj_time_mul]
    simp only [q, R, mul_assoc, Complex.im_ofReal_mul]
  have hIntegratedByParts (x : ℝ²) : (partialDeriv j q x * w x).im = R x + S x := by
    change (partialDeriv j (fun y ↦ (a y : ℂ) * starRingEnd ℂ (u y)) x * w x).im = _
    rw [partialDeriv_weighted_conj ha hu₁, hEq, add_mul, Complex.add_im,
      im_pair_mul_time, im_pair_mul_time]
  simp_rw [hSplit]
  have hRneg : Integrable (fun x ↦ -R x) := hR.neg
  rw [integral_add hRneg hQInt, integral_neg, hParts]
  simp_rw [hIntegratedByParts]
  rw [integral_add hR hS]
  change -(∫ x, R x) + -((∫ x, R x) + (∫ x, S x)) =
    -2 * (∫ x, R x) - (∫ x, S x)
  ring

private lemma hasDerivAt_current_component {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    {a : ℝ² → ℝ} (ha : IsTestFunction a) {v vt z zt : ℝ → ℝ² → ℂ}
    (hv : ContinuousOn (Function.uncurry v) (J ×ˢ univ))
    (hvt : ContinuousOn (Function.uncurry vt) (J ×ˢ univ))
    (hz : ContinuousOn (Function.uncurry z) (J ×ˢ univ))
    (hzt : ContinuousOn (Function.uncurry zt) (J ×ˢ univ))
    (hTime : ∀ s ∈ J, ∀ x, HasDerivAt (fun r ↦ v r x) (vt s x) s)
    (hTimePartial : ∀ s ∈ J, ∀ x, HasDerivAt (fun r ↦ z r x) (zt s x) s) :
    HasDerivAt (fun s ↦ ∫ x, a x * (starRingEnd ℂ (v s x) * z s x).im)
      (∫ x, a x * (starRingEnd ℂ (vt t x) * z t x + starRingEnd ℂ (v t x) * zt t x).im) t := by
  let f (s : ℝ) (x : ℝ²) := (starRingEnd ℂ (v s x) * z s x).im
  let f' (s : ℝ) (x : ℝ²) :=
    (starRingEnd ℂ (vt s x) * z s x + starRingEnd ℂ (v s x) * zt s x).im
  have hvC := Complex.continuous_conj.comp_continuousOn hv
  have hvtC := Complex.continuous_conj.comp_continuousOn hvt
  have hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ) :=
    Complex.continuous_im.comp_continuousOn (hvC.mul hz)
  have hf' : ContinuousOn (Function.uncurry f') (J ×ˢ univ) :=
    Complex.continuous_im.comp_continuousOn ((hvtC.mul hz).add (hvC.mul hzt))
  have hDiff (s : ℝ) (hs : s ∈ J) (x : ℝ²) : HasDerivAt (fun r ↦ f r x) (f' s x) s := by
    have hConj := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hTime s hs x)
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hConj.mul (hTimePartial s hs x))
  exact (integrable_hasDerivAt_integral_mul hJ ht ha.1.continuous ha.2 hf hf' hDiff).2

private lemma virialSource_split_coordinates {A : ℝ² → ℝ} (hA : IsTestFunction A) {u B : ℝ² → ℂ}
    (hu : Continuous u) (hB : Continuous B) (Du : Fin 2 → ℝ² → ℂ) :
    virialSource A u Du B =
      2 * ((-2 * (∫ x, (starRingEnd ℂ (Du 0 x) *
          (((partialDeriv 0 A x : ℝ) : ℂ) * B x)).re) -
        (∫ x, (starRingEnd ℂ (u x) *
          (((partialDeriv 0 (partialDeriv 0 A) x : ℝ) : ℂ) * B x)).re)) +
        (-2 * (∫ x, (starRingEnd ℂ (Du 1 x) *
          (((partialDeriv 1 A x : ℝ) : ℂ) * B x)).re) -
        (∫ x, (starRingEnd ℂ (u x) *
          (((partialDeriv 1 (partialDeriv 1 A) x : ℝ) : ℂ) * B x)).re))) := by
  have hInt (j : Fin 2) : Integrable (fun x ↦ (starRingEnd ℂ (u x) *
      (((partialDeriv j (partialDeriv j A) x : ℝ) : ℂ) * B x)).re) :=
    (integrable_weighted_pair ((hA.partialDeriv j).partialDeriv j) hu hB).re
  simp only [virialSource, Fin.sum_univ_two, laplacian, Complex.ofReal_add,
    add_mul, mul_add, Complex.add_re]
  rw [integral_add (hInt 0) (hInt 1)]
  ring

/-- The first virial current has the stated time derivative when $v_t = iB$.
The hypotheses only require the time derivatives used in the differentiated current. -/
theorem hasDerivAt_virialFirstDeriv
    {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J) {v vt : ℝ → ℝ² → ℂ}
    (hv : ContinuousOn (Function.uncurry v) (J ×ˢ univ))
    (hvt : ContinuousOn (Function.uncurry vt) (J ×ˢ univ))
    (hDv : ∀ j : Fin 2,
      ContinuousOn (Function.uncurry (fun s ↦ partialDeriv j (v s))) (J ×ˢ univ))
    (hDvt : ∀ j : Fin 2,
      ContinuousOn (Function.uncurry (fun s ↦ partialDeriv j (vt s))) (J ×ˢ univ))
    (hTime : ∀ s ∈ J, ∀ x, HasDerivAt (fun r ↦ v r x) (vt s x) s)
    (hTimePartial : ∀ j : Fin 2, ∀ s ∈ J, ∀ x,
      HasDerivAt (fun r ↦ partialDeriv j (v r) x) (partialDeriv j (vt s) x) s)
    (hSpace : ContDiff ℝ 2 (v t)) (hSpaceTime : ContDiff ℝ 1 (vt t))
    {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {B : ℝ² → ℂ} (hEq : ∀ x, vt t x = Complex.I * B x) :
    HasDerivAt (fun s ↦ virialFirstDeriv A (v s) (fun j ↦ partialDeriv j (v s)))
      (virialSource A (v t) (fun j ↦ partialDeriv j (v t)) B) t := by
  let C (j : Fin 2) (s : ℝ) := ∫ x, partialDeriv j A x *
    (starRingEnd ℂ (v s x) * partialDeriv j (v s) x).im
  have hComponent (j : Fin 2) := hasDerivAt_current_component hJ ht (hA.partialDeriv j)
    hv hvt (hDv j) (hDvt j) hTime (hTimePartial j)
  have hB : Continuous B := ((continuous_const_mul (-Complex.I)).comp hSpaceTime.continuous).congr
    (fun x ↦ by
      change -Complex.I * vt t x = B x
      rw [hEq, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul])
  have hValue (j : Fin 2) :=
    integral_current_component_derivative (hA.partialDeriv j) hSpace hSpaceTime hB hEq j
  have hDeriv := ((hComponent 0).add (hComponent 1)).const_mul (2 : ℝ)
  rw [hValue 0, hValue 1,
    ← virialSource_split_coordinates hA hSpace.continuous hB (fun j ↦ partialDeriv j (v t))]
    at hDeriv
  change HasDerivAt (fun s ↦ 2 * (C 0 s + C 1 s)) _ t at hDeriv
  apply hDeriv.congr_of_eventuallyEq
  filter_upwards [hJ.mem_nhds ht] with s hs
  have hV : Continuous (v s) :=
    hv.comp_continuous (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨hs, mem_univ _⟩)
  have hD (j : Fin 2) : Continuous (partialDeriv j (v s)) :=
    (hDv j).comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hs, mem_univ _⟩)
  have hInt (j : Fin 2) : Integrable (fun x ↦ partialDeriv j A x *
      (starRingEnd ℂ (v s x) * partialDeriv j (v s) x).im) := by
    simpa only [RCLike.im_eq_complex_im, im_weighted_pair] using
      (integrable_weighted_pair (hA.partialDeriv j) hV (hD j)).im
  change virialFirstDeriv A (v s) (fun j ↦ partialDeriv j (v s)) = 2 * (C 0 s + C 1 s)
  unfold virialFirstDeriv
  congr 1
  simp only [mul_add, Complex.add_im, im_weighted_pair, C]
  rw [integral_add (hInt 0) (hInt 1)]

end Blowup
