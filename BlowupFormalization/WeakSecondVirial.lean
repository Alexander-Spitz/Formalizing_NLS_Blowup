import BlowupFormalization.LinearVirialAcceleration
import BlowupFormalization.LocalizedVirialBound
import BlowupFormalization.NonlinearVirial
import BlowupFormalization.VirialCurrentDerivative
import BlowupFormalization.WeakFirstVirial

/-! # Second localized virial identity for weak solutions -/

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal

namespace Blowup

private lemma tendstoLocallyUniformlyOn_real_weightedPairing_mollify
    {J : Set ℝ} (hJ : IsOpen J) {a : ℝ² → ℝ} (ha : IsTestFunction a)
    {f g : ℝ → ℝ² → ℂ} (hf : ∀ t : J, MemLp (f t) 2) (hg : ∀ t : J, MemLp (g t) 2)
    (hfc : Continuous (fun t : J ↦ (hf t).toLp (f t)))
    (hgc : Continuous (fun t : J ↦ (hg t).toLp (g t))) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ ∫ x, (starRingEnd ℂ (mollify (normalizedMollifier n) (f t) x) *
        ((a x : ℂ) * mollify (normalizedMollifier n) (g t) x)).re)
      (fun t ↦ ∫ x, (starRingEnd ℂ (f t x) * ((a x : ℂ) * g t x)).re) atTop J := by
  have ha' := testFunction_memLp_top_complex ha
  have hPair := tendstoLocallyUniformlyOn_weightedPairing_mollify
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius hJ ha' hf hg hfc hgc
  have hRe := Complex.uniformContinuous_re.comp_tendstoLocallyUniformlyOn hPair
  refine (hRe.congr (fun n t ht ↦ ?_)).congr_right (fun t ht ↦ ?_)
  · exact (integral_re (integrable_weighted_pairing ha'
      (memLp_mollify (normalizedMollifier_isTestFunction n) (hf ⟨t, ht⟩))
      (memLp_mollify (normalizedMollifier_isTestFunction n) (hg ⟨t, ht⟩)))).symm
  · exact (integral_re (integrable_weighted_pairing ha' (hf ⟨t, ht⟩) (hg ⟨t, ht⟩))).symm

private lemma integral_hessian_pairings {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {D : Fin 2 → ℝ² → ℂ} (hD : ∀ j, MemLp (D j) 2) :
    (∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
      (D j x * starRingEnd ℂ (D k x)).re) =
    ∑ j : Fin 2, ∑ k : Fin 2, ∫ x, (starRingEnd ℂ (D k x) *
      (((partialDeriv j (partialDeriv k A) x : ℝ) : ℂ) * D j x)).re := by
  let T (j k : Fin 2) (x : ℝ²) :=
    (starRingEnd ℂ (D k x) * (((partialDeriv j (partialDeriv k A) x : ℝ) : ℂ) * D j x)).re
  have hPoint (j k : Fin 2) (x : ℝ²) :
      partialDeriv j (partialDeriv k A) x * (D j x * starRingEnd ℂ (D k x)).re = T j k x := by
    simp only [T, mul_left_comm (starRingEnd ℂ (D k x)),
      Complex.re_ofReal_mul, mul_comm (D j x)]
  have hIntegrable (j k : Fin 2) : Integrable (T j k) :=
    (integrable_weighted_pairing
      (testFunction_memLp_top_complex ((hA.partialDeriv k).partialDeriv j))
      (hD k) (hD j)).re
  simp_rw [hPoint]
  rw [integral_finsetSum Finset.univ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hIntegrable j k))]
  exact Finset.sum_congr rfl fun j _ ↦ integral_finsetSum _ (fun k _ ↦ hIntegrable j k)

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

private noncomputable def virialLinear (A : ℝ² → ℝ) (f : ℝ² → ℂ)
    (D : Fin 2 → ℝ² → ℂ) : ℝ :=
  4 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
    (D j x * starRingEnd ℂ (D k x)).re) - ∫ x, laplacian (laplacian A) x * ‖f x‖ ^ 2

set_option maxHeartbeats 700000 in
-- Elaborating the four weighted pairings and the integral rewrites exceeds the default budget.
private lemma tendstoLocallyUniformlyOn_hessian_mollify
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ ∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
        (mollify (normalizedMollifier n) (Du t j) x *
          starRingEnd ℂ (mollify (normalizedMollifier n) (Du t k) x)).re)
      (fun t ↦ ∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
        (Du t j x * starRingEnd ℂ (Du t k x)).re) atTop J := by
  have hMem (j : Fin 2) (t : J) := (h.h1 t t.property).memL2_partial j
  have hPair (j k : Fin 2) := tendstoLocallyUniformlyOn_real_weightedPairing_mollify hJ
    ((hA.partialDeriv k).partialDeriv j) (f := fun t ↦ Du t k) (g := fun t ↦ Du t j)
    (hMem k) (hMem j) (h.continuous_grad_toLp k) (h.continuous_grad_toLp j)
  have hSum := ((hPair 0 0).add (hPair 0 1)).add ((hPair 1 0).add (hPair 1 1))
  refine (hSum.congr (fun n t ht ↦ ?_)).congr_right (fun t ht ↦ ?_)
  · rw [integral_hessian_pairings hA
      (fun j ↦ memLp_mollify (normalizedMollifier_isTestFunction n) (hMem j ⟨t, ht⟩))]
    simp only [Fin.sum_univ_two, Pi.add_apply]
  · rw [integral_hessian_pairings hA (fun j ↦ hMem j ⟨t, ht⟩)]
    simp only [Fin.sum_univ_two, Pi.add_apply]

private lemma tendstoLocallyUniformlyOn_linear_virial_mollify
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ virialLinear A (mollify (normalizedMollifier n) (u t))
        (fun j ↦ mollify (normalizedMollifier n) (Du t j)))
      (fun t ↦ virialLinear A (u t) (Du t)) atTop J := by
  have hHess := (Real.uniformContinuous_const_mul (x := 4)).comp_tendstoLocallyUniformlyOn
    (tendstoLocallyUniformlyOn_hessian_mollify h hJ hA)
  have hBilap := h.tendstoLocallyUniformlyOn_localizedVariance_mollify hJ hA.laplacian.laplacian
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius
  exact hHess.sub hBilap

private lemma tendstoLocallyUniformlyOn_nonlinear_source_mollify
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x)))) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ virialSource A (mollify (normalizedMollifier n) (u t))
        (fun j ↦ mollify (normalizedMollifier n) (Du t j))
        (mollify (normalizedMollifier n) (fun x ↦ nonlinearity p (u t x))))
      (fun t ↦ virialSource A (u t) (Du t) (fun x ↦ nonlinearity p (u t x))) atTop J := by
  have hPair (j : Fin 2) := tendstoLocallyUniformlyOn_real_weightedPairing_mollify hJ
    (hA.partialDeriv j) (f := fun t ↦ Du t j) (g := fun t x ↦ nonlinearity p (u t x))
    (fun t ↦ (h.h1 t t.property).memL2_partial j) hN (h.continuous_grad_toLp j) hNc
  have hLap := tendstoLocallyUniformlyOn_real_weightedPairing_mollify hJ
    hA.laplacian (f := u) (g := fun t x ↦ nonlinearity p (u t x))
    (fun t ↦ (h.h1 t t.property).memL2) hN h.continuous_toLp hNc
  have hFirst := (Real.uniformContinuous_const_mul (x := -4)).comp_tendstoLocallyUniformlyOn
    ((hPair 0).add (hPair 1))
  have hSecond := (Real.uniformContinuous_const_mul (x := 2)).comp_tendstoLocallyUniformlyOn hLap
  unfold virialSource
  simp only [Fin.sum_univ_two]
  exact hFirst.sub hSecond

private lemma hasDerivAt_mollified_current
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x))))
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s ↦ virialFirstDeriv A (mollify ρ (u s)) (fun j ↦ mollify ρ (Du s j)))
      (virialLinear A (mollify ρ (u t)) (fun j ↦ mollify ρ (Du t j)) +
        virialSource A (mollify ρ (u t)) (fun j ↦ mollify ρ (Du t j))
          (mollify ρ (fun x ↦ nonlinearity p (u t x)))) t := by
  let v (s : ℝ) := mollify ρ (u s)
  let N (s : ℝ) := mollify ρ (fun x ↦ nonlinearity p (u s x))
  let vt (s : ℝ) (x : ℝ²) := Complex.I * (laplacian (v s) x + N s x)
  have hSmooth : ContDiff ℝ 3 (v t) := (contDiff_mollify hρ (h.h1 t ht).memL2).of_le (by simp)
  have hSpace : ContDiff ℝ 2 (v t) := hSmooth.of_le (by norm_num)
  have hLap : ContDiff ℝ 1 (laplacian (v t)) := by
    rw [show v t = mollify ρ (u t) from rfl, laplacian_mollify_kernel hρ (h.h1 t ht).memL2]
    exact (contDiff_mollify hρ.laplacian (h.h1 t ht).memL2).of_le (by simp)
  have hNonlinear : ContDiff ℝ 1 (N t) :=
    (contDiff_mollify hρ (hN ⟨t, ht⟩)).of_le (by simp)
  have hSpaceTime : ContDiff ℝ 1 (vt t) := contDiff_const.mul (hLap.add hNonlinear)
  have hCurrent := hasDerivAt_virialFirstDeriv (v := v) (vt := vt) hJ ht
    (h.continuousOn_mollify hρ) (h.continuousOn_mollified_rhs hρ hN hNc)
    (fun j ↦ h.continuousOn_partialDeriv_mollify hρ j)
    (fun j ↦ h.continuousOn_partialDeriv_mollified_rhs hρ hN hNc j)
    (fun s hs x ↦ h.hasDerivAt_mollify hJ hρ hN hNc hs x)
    (fun j s hs x ↦ h.hasDerivAt_partialDeriv_mollify hJ hρ hN hNc hs j x)
    hSpace hSpaceTime hA (B := laplacian (v t) + N t) (fun _ ↦ rfl)
  have hDv (j : Fin 2) : Continuous (partialDeriv j (v t)) :=
    ((hSpace.continuous_fderiv (by simp)).clm_apply continuous_const)
  rw [virialSource_add hA hSpace.continuous hDv hLap.continuous hNonlinear.continuous] at hCurrent
  have hPartial (s : ℝ) (hs : s ∈ J) :
      (fun j ↦ partialDeriv j (v s)) = fun j ↦ mollify ρ (Du s j) :=
    funext (fun j ↦ (h.h1 s hs).partialDeriv_mollify hρ j)
  have hNear : (fun s ↦ virialFirstDeriv A (v s) (fun j ↦ mollify ρ (Du s j))) =ᶠ[𝓝 t]
      (fun s ↦ virialFirstDeriv A (v s) (fun j ↦ partialDeriv j (v s))) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    rw [hPartial s hs]
  have hSource : virialSource A (v t) (fun j ↦ partialDeriv j (v t)) (N t) =
      virialSource A (v t) (fun j ↦ mollify ρ (Du t j)) (N t) := by
    rw [hPartial t ht]
  have hLinear : virialSource A (v t) (fun j ↦ partialDeriv j (v t)) (laplacian (v t)) =
      virialLinear A (v t) (fun j ↦ mollify ρ (Du t j)) := by
    rw [← hPartial t ht]
    exact linear_virial_acceleration hA hSmooth
  rw [hLinear, hSource] at hCurrent
  exact hCurrent.congr_of_eventuallyEq hNear

private lemma virialLinear_add_nonlinear_eq_second {f : ℝ² → ℂ} {D : Fin 2 → ℝ² → ℂ}
    (hf : IsH1 f D) (hp : 3 ≤ p) {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    virialLinear A f D + virialSource A f D (fun x ↦ nonlinearity p (f x)) =
      virialSecondDeriv p A f D := by
  have hEq : virialSource A f D (fun x ↦ nonlinearity p (f x)) =
      -(2 * (p - 1) / (p + 1) * (∫ x, laplacian A x * ‖f x‖ ^ (p + 1))) :=
    hf.second_virial_nonlinearity hp hA
  rw [hEq]
  unfold virialLinear virialSecondDeriv
  ring

private lemma hasDerivAt_virialFirstDeriv_on
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) (hJ : IsOpen J)
    {A : ℝ² → ℝ} (hA : IsTestFunction A) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s ↦ virialFirstDeriv A (u s) (Du s))
      (virialSecondDeriv p A (u t) (Du t)) t := by
  have hCurrent := h.tendstoLocallyUniformlyOn_virialFirstDeriv_mollify hJ hA
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius
  have hN (s : J) := (h.h1 s s.property).memLp_nonlinearity hp
  have hNc := h.continuous_nonlinearity_toLp hp
  have hLinear := tendstoLocallyUniformlyOn_linear_virial_mollify h hJ hA
  have hNonlinear := tendstoLocallyUniformlyOn_nonlinear_source_mollify h hJ hA hN hNc
  have hLimit := (hLinear.add hNonlinear).congr_right
    (fun s hs ↦ virialLinear_add_nonlinear_eq_second (h.h1 s hs) hp hA)
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hJ hLimit ?_
    (fun s hs ↦ hCurrent.tendsto_at hs) ht
  exact Filter.Eventually.of_forall fun n s hs ↦
    hasDerivAt_mollified_current h hJ hA (normalizedMollifier_isTestFunction n) hN hNc hs

/-- The current on the right of (4.4) has derivative (4.5) at every interior
time of a weak H¹ NLS solution for every real p ≥ 3. -/
theorem IsNLSSolution.hasDerivAt_virialFirstDeriv
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s ↦ virialFirstDeriv A (u s) (Du s))
      (virialSecondDeriv p A (u t) (Du t)) t :=
  hasDerivAt_virialFirstDeriv_on (h.mono interior_subset) hp isOpen_interior hA ht

/-- The second derivative of the localized variance of a weak H¹ solution is (4.5). -/
theorem IsNLSSolution.hasDerivAt_deriv_localizedVariance
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (deriv (fun s ↦ ∫ x, A x * ‖u s x‖ ^ 2))
      (virialSecondDeriv p A (u t) (Du t)) t := by
  apply (h.hasDerivAt_virialFirstDeriv hp hA ht).congr_of_eventuallyEq
  filter_upwards [isOpen_interior.mem_nhds ht] with s hs
  exact (h.hasDerivAt_localizedVariance hp hA hs).deriv

/-- The estimate underlying (4.6) bounds the second derivative of the localized variance,
with the energy and mass evaluated at the differentiation time. -/
theorem localizedVariance_acceleration_le :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {p Q : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ},
        IsNLSSolution p J u Du → 3 ≤ p → 0 < Q → ∀ {t : ℝ}, t ∈ interior J →
        deriv (deriv (fun s ↦ ∫ x, virialWeight Q x * ‖u s x‖ ^ 2)) t ≤
          8 * (p - 1) * energy p (u t) (Du t) - 4 * (p - 3) * gradNormSq (Du t) +
          (2 * (p - 1) / (p + 1)) * C * (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1)) +
          D * mass (u t) / Q ^ 2 := by
  obtain ⟨C, D, hC, hD, hBound⟩ := virialSecondDeriv_virialWeight_le
  refine ⟨C, D, hC, hD, fun h hp hQ t ht ↦ ?_⟩
  have hData := h.h1 t (interior_subset ht)
  rw [(h.hasDerivAt_deriv_localizedVariance hp (virialWeight_isTestFunction hQ) ht).deriv]
  exact hBound hp hQ hData.memL2 hData.memL2_partial (hData.integrable_nonlinear_density hp)

end Blowup
