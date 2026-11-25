import BlowupFormalization.SolutionFacts
import BlowupFormalization.WeightProperties

/-! # Localized virial expressions and the initial value bound -/

open MeasureTheory

namespace Blowup

/-- Right-hand side of (4.4): `2 Im ∫ ū ∇A·∇u`. -/
noncomputable def virialFirstDeriv (A : ℝ² → ℝ) (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  2 * ∫ x, (starRingEnd ℂ (u x) *
    (((partialDeriv 0 A x : ℝ) : ℂ) * Du 0 x + ((partialDeriv 1 A x : ℝ) : ℂ) * Du 1 x)).im

/-- Right-hand side of (4.5), written for a general (not necessarily radial) weight:
`4 Re ∫ Σⱼₖ ∂ⱼ∂ₖA ∂ⱼu ∂ₖū − 2(p−1)/(p+1) ∫ ΔA |u|^{p+1} − ∫ Δ²A |u|²`.
For radial `A` and `u` the first term is the paper's `4 ∫ A'' |u_r|²`. -/
noncomputable def virialSecondDeriv (p : ℝ) (A : ℝ² → ℝ) (u : ℝ² → ℂ)
    (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  4 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k A) x * (Du j x * starRingEnd ℂ (Du k x)).re)
  - 2 * (p - 1) / (p + 1) * (∫ x, laplacian A x * ‖u x‖ ^ (p + 1))
  - ∫ x, laplacian (laplacian A) x * ‖u x‖ ^ 2

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
  have hWeight : Integrable (fun x ↦ virialWeight (2 * S) x * ‖u₀ x‖ ^ 2) := by
    refine hCompact.mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact (virialWeight_isTestFunction hQ).1.continuous.aestronglyMeasurable.mul
        hu₀.norm.integrable_sq.1
    · rw [Real.norm_of_nonneg (mul_nonneg (virialWeight_nonneg _ _) (sq_nonneg _))]
      exact hLe x
  calc
    _ ≤ ∫ x, ball.indicator (fun y ↦ ‖y‖ ^ 2 * ‖u₀ y‖ ^ 2) x :=
      integral_mono hWeight hCompact hLe
    _ = compactMoment u₀ S := integral_indicator hball

end Blowup
