import BlowupFormalization.SolutionFacts
import BlowupFormalization.WeightProperties

/-! # Localized virial expressions and the initial bounds -/

open MeasureTheory

namespace Blowup

/-- Right-hand side of (4.4): `2 Im ∫ ū ∇A·∇u`. -/
noncomputable def virialFirstDeriv (A : ℝ² → ℝ) (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  2 * ∫ x, (starRingEnd ℂ (u x) *
    (((partialDeriv 0 A x : ℝ) : ℂ) * Du 0 x + ((partialDeriv 1 A x : ℝ) : ℂ) * Du 1 x)).im

/-- The nonlinearity paired with the conjugate field and a real weight is real. -/
theorem im_weighted_nonlinearity_eq_zero (a p : ℝ) (z : ℂ) :
    ((a : ℂ) * starRingEnd ℂ z * nonlinearity p z).im = 0 := by
  unfold nonlinearity
  have h : (a : ℂ) * starRingEnd ℂ z * (((‖z‖ ^ (p - 1) : ℝ) : ℂ) * z) =
      ((a : ℂ) * ((‖z‖ ^ (p - 1) : ℝ) : ℂ)) * (starRingEnd ℂ z * z) := by ring
  rw [h, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Complex.ofReal_im]

/-- Right-hand side of (4.5), written for a general (not necessarily radial) weight:
`4 Re ∫ Σⱼₖ ∂ⱼ∂ₖA ∂ⱼu ∂ₖū − 2(p−1)/(p+1) ∫ ΔA |u|^{p+1} − ∫ Δ²A |u|²`.
For radial `A` and `u` the first term is the paper's `4 ∫ A'' |u_r|²`. -/
noncomputable def virialSecondDeriv (p : ℝ) (A : ℝ² → ℝ) (u : ℝ² → ℂ)
    (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  4 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k A) x * (Du j x * starRingEnd ℂ (Du k x)).re)
  - 2 * (p - 1) / (p + 1) * (∫ x, laplacian A x * ‖u x‖ ^ (p + 1))
  - ∫ x, laplacian (laplacian A) x * ‖u x‖ ^ 2

private lemma integrable_testFunction_mul_norm_sq {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {u : ℝ² → ℂ} (hu : MemLp u 2) : Integrable (fun x ↦ A x * ‖u x‖ ^ 2) :=
  hu.norm.integrable_sq.mul_of_top_right (hA.1.continuous.memLp_of_hasCompactSupport hA.2)

/-- The first bound in (4.7): `V_{2S}(0) ≤ H(S)`. -/
theorem eq_4_7_value {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) {S : ℝ} (hS : 0 < S) :
    ∫ x, virialWeight (2 * S) x * ‖u₀ x‖ ^ 2 ≤ compactMoment u₀ S := by
  let ball := Metric.closedBall (0 : ℝ²) (10 * S)
  have hQ : 0 < 2 * S := by positivity
  have hball : MeasurableSet ball := measurableSet_closedBall
  have hDensity : IntegrableOn (fun x ↦ ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2) ball :=
    variance_integrableOn_closedBall hu₀ (10 * S)
  have hLe (x : ℝ²) : virialWeight (2 * S) x * ‖u₀ x‖ ^ 2 ≤
      ball.indicator (fun y ↦ ‖y‖ ^ 2 * ‖u₀ y‖ ^ 2) x := by
    by_cases hx : x ∈ ball
    · rw [Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (virialWeight_le_sq hQ x) (sq_nonneg _)
    · have hx' : 10 * S < ‖x‖ := by simpa [ball, not_le] using hx
      rw [Set.indicator_of_notMem hx, virialWeight_eq_zero hQ (by linarith), zero_mul]
  have hCompact := hDensity.integrable_indicator hball
  have hWeight := integrable_testFunction_mul_norm_sq (virialWeight_isTestFunction hQ) hu₀
  calc
    _ ≤ ∫ x, ball.indicator (fun y ↦ ‖y‖ ^ 2 * ‖u₀ y‖ ^ 2) x :=
      integral_mono hWeight hCompact hLe
    _ = compactMoment u₀ S := integral_indicator hball

/-- The two-coordinate Cauchy–Schwarz bound for real coefficients and complex coordinates. -/
private lemma norm_add_real_mul_le (a b : ℝ) (z w : ℂ) :
    ‖(a : ℂ) * z + (b : ℂ) * w‖ ≤
      Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  calc
    _ ≤ |a| * ‖z‖ + |b| * ‖w‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_add_le ((a : ℂ) * z) ((b : ℂ) * w)
    _ ≤ _ := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 2)) ![|a|, |b|] ![‖z‖, ‖w‖]

/-- The second bound in (4.7), for the first virial expression at any positive scale. -/
theorem eq_4_7_deriv {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (hu : IsH1 u Du)
    {Q : ℝ} (hQ : 0 < Q) :
    |virialFirstDeriv (virialWeight Q) u Du| ≤
      4 * Real.sqrt (gradNormSq Du) * Real.sqrt (∫ x, virialWeight Q x * ‖u x‖ ^ 2) := by
  let A := virialWeight Q
  let F (x : ℝ²) := Real.sqrt (A x) * ‖u x‖
  let G (x : ℝ²) := Real.sqrt (‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2)
  let gradDot (x : ℝ²) := ((partialDeriv 0 A x : ℝ) : ℂ) * Du 0 x +
    ((partialDeriv 1 A x : ℝ) : ℂ) * Du 1 x
  let I (x : ℝ²) := (starRingEnd ℂ (u x) * gradDot x).im
  have hA : IsTestFunction A := virialWeight_isTestFunction hQ
  have hD (j : Fin 2) := (hu.memL2_partial j).norm.integrable_sq
  have hKinetic : Integrable (fun x ↦ ‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2) :=
    (hD 0).add (hD 1)
  have hF_sq (x : ℝ²) : F x ^ 2 = A x * ‖u x‖ ^ 2 := by
    change (Real.sqrt (A x) * ‖u x‖) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ A x from virialWeight_nonneg Q x)]
  have hG_sq (x : ℝ²) : G x ^ 2 = ‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hF_meas : AEStronglyMeasurable F :=
    (Real.continuous_sqrt.comp hA.1.continuous).aestronglyMeasurable.mul
      hu.memL2.aestronglyMeasurable.norm
  have hG_meas : AEStronglyMeasurable G :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hKinetic.1
  have hF : MemLp F 2 := (memLp_two_iff_integrable_sq hF_meas).2 (by
    simpa only [hF_sq] using integrable_testFunction_mul_norm_sq hA hu.memL2)
  have hG : MemLp G 2 := (memLp_two_iff_integrable_sq hG_meas).2 (by
    simpa only [hG_sq] using hKinetic)
  have hPartial (j : Fin 2) : Continuous (fun x ↦ ((partialDeriv j A x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hA.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDot_meas : AEStronglyMeasurable gradDot :=
    ((hPartial 0).aestronglyMeasurable.mul (hu.memL2_partial 0).aestronglyMeasurable).add
      ((hPartial 1).aestronglyMeasurable.mul (hu.memL2_partial 1).aestronglyMeasurable)
  have hI_meas : AEStronglyMeasurable I :=
    Complex.continuous_im.comp_aestronglyMeasurable
      ((Complex.continuous_conj.comp_aestronglyMeasurable hu.memL2.aestronglyMeasurable).mul
        hDot_meas)
  have hI_le (x : ℝ²) : ‖I x‖ ≤ 2 * (F x * G x) := by
    have hGradient : Real.sqrt (partialDeriv 0 A x ^ 2 + partialDeriv 1 A x ^ 2) ≤
        2 * Real.sqrt (A x) := by
      calc
        _ ≤ Real.sqrt (4 * A x) := Real.sqrt_le_sqrt (grad_virialWeight_sq_le hQ x)
        _ = _ := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt (4 : ℝ) = 2 by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    calc
      ‖I x‖ ≤ ‖starRingEnd ℂ (u x) * gradDot x‖ := by
        simpa only [I, Real.norm_eq_abs] using Complex.abs_im_le_norm
          (starRingEnd ℂ (u x) * gradDot x)
      _ = ‖u x‖ * ‖gradDot x‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖u x‖ * (Real.sqrt (partialDeriv 0 A x ^ 2 + partialDeriv 1 A x ^ 2) * G x) :=
        mul_le_mul_of_nonneg_left (norm_add_real_mul_le _ _ _ _) (norm_nonneg _)
      _ ≤ ‖u x‖ * ((2 * Real.sqrt (A x)) * G x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hGradient (Real.sqrt_nonneg _))
          (norm_nonneg _)
      _ = 2 * (F x * G x) := by dsimp [F]; ring
  have hProduct : Integrable (F * G) := hF.integrable_mul hG
  have hDom := hProduct.const_mul (2 : ℝ)
  have hI_int : Integrable I := hDom.mono' hI_meas (Filter.Eventually.of_forall hI_le)
  have hHolder : (∫ x, F x * G x) ≤
      Real.sqrt (∫ x, A x * ‖u x‖ ^ 2) * Real.sqrt (gradNormSq Du) := by
    have hF_nonneg : 0 ≤ᵐ[volume] F := Filter.Eventually.of_forall fun x ↦ by dsimp [F]; positivity
    have hG_nonneg : 0 ≤ᵐ[volume] G := Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg _
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two, hF_sq, hG_sq, gradNormSq] using
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hF_nonneg hG_nonneg
        (by simpa using hF) (by simpa using hG)
  calc
    |virialFirstDeriv (virialWeight Q) u Du| = 2 * ‖∫ x, I x‖ := by
      change |2 * ∫ x, I x| = _
      rw [abs_mul, abs_of_pos two_pos, Real.norm_eq_abs]
    _ ≤ 2 * (∫ x, ‖I x‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm I) two_pos.le
    _ ≤ 2 * (∫ x, 2 * (F x * G x)) :=
      mul_le_mul_of_nonneg_left (integral_mono hI_int.norm hDom hI_le) two_pos.le
    _ = 4 * (∫ x, F x * G x) := by rw [integral_const_mul]; ring
    _ ≤ _ := by
      simpa only [A, mul_left_comm, mul_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hHolder (by norm_num : (0 : ℝ) ≤ 4)

end Blowup
