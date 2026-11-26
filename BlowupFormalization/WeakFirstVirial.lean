import BlowupFormalization.H1Sobolev
import BlowupFormalization.MollifiedTimeRegularity
import BlowupFormalization.SmoothVirial
import BlowupFormalization.VirialApproximation

/-! # First localized virial identity for weak solutions -/

open Filter MeasureTheory Set Topology
open scoped ContDiff

namespace Blowup

private lemma hasDerivAt_mollified_variance
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x))))
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s ↦ ∫ x, A x * ‖mollify ρ (u s) x‖ ^ 2)
      (virialFirstDeriv A (mollify ρ (u t)) (fun j ↦ mollify ρ (Du t j)) -
        2 * (∫ x, ((A x : ℂ) * starRingEnd ℂ (mollify ρ (u t) x) *
          mollify ρ (fun y ↦ nonlinearity p (u t y)) x).im)) t := by
  let v (s : ℝ) := mollify ρ (u s)
  let N (s : ℝ) := mollify ρ (fun y ↦ nonlinearity p (u s y))
  let vt (s : ℝ) (x : ℝ²) := Complex.I * (laplacian (v s) x + N s x)
  have hEq (x : ℝ²) : Complex.I * vt t x + laplacian (v t) x = -N t x := by
    dsimp only [vt]
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    abel
  have hSpace : ContDiff ℝ 2 (v t) :=
    (contDiff_mollify hρ (h.h1 t ht).memL2).of_le (by simp)
  have hVariance := hasDerivAt_localizedVariance_of_linear_forced (u := v) (ut := vt) hJ ht
    (h.continuousOn_mollify hρ) (h.continuousOn_mollified_rhs hρ hN hNc)
    (fun s hs x ↦ h.hasDerivAt_mollify hJ hρ hN hNc hs x) hSpace hA hEq
  have hPartial : (fun j ↦ partialDeriv j (v t)) = fun j ↦ mollify ρ (Du t j) :=
    funext (fun j ↦ (h.h1 t ht).partialDeriv_mollify hρ j)
  rw [hPartial] at hVariance
  simpa only [v, N, mul_neg, Complex.neg_im, integral_neg, sub_eq_add_neg]
    using hVariance

/-- The first localized virial identity (4.4) on the open time domain of a weak solution
whose nonlinearity is continuous into L². -/
theorem IsNLSSolution.hasDerivAt_localizedVariance_of_nonlinearity_toLp
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x))))
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun s ↦ ∫ x, A x * ‖u s x‖ ^ 2)
      (virialFirstDeriv A (u t) (Du t)) t := by
  have hVariance := h.tendstoLocallyUniformlyOn_localizedVariance_mollify hJ hA
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius
  have hCurrent := h.tendstoLocallyUniformlyOn_virialFirstDeriv_mollify hJ hA
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius
  have hError := h.tendstoLocallyUniformlyOn_mollified_nonlinear_virial hJ hA hN hNc
    normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
    normalizedMollifier_support tendsto_mollifierRadius
  refine hasDerivAt_of_virial_approximation hJ (fun s hs ↦ hVariance.tendsto_at hs) ?_
    hCurrent hError ht
  exact Filter.Eventually.of_forall fun n s hs ↦ by
    simpa only [neg_mul, sub_eq_add_neg] using
      hasDerivAt_mollified_variance h hJ hA (normalizedMollifier_isTestFunction n) hN hNc hs

/-- The first localized virial identity (4.4) holds at every interior time of a weak
H¹ NLS solution on the plane for every real exponent p ≥ 3. -/
theorem IsNLSSolution.hasDerivAt_localizedVariance
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s ↦ ∫ x, A x * ‖u s x‖ ^ 2)
      (virialFirstDeriv A (u t) (Du t)) t := by
  have hInterior := h.mono (J' := interior J) interior_subset
  exact hInterior.hasDerivAt_localizedVariance_of_nonlinearity_toLp
    isOpen_interior hA (fun s ↦ (hInterior.h1 s s.property).memLp_nonlinearity hp)
    (hInterior.continuous_nonlinearity_toLp hp) ht

end Blowup
