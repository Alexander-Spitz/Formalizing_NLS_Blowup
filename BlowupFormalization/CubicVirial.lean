import BlowupFormalization.CubicVirialWeight
import BlowupFormalization.LocalizedVirialBound
import BlowupFormalization.RadialTail

/-! # The critical cubic localized virial estimate -/

open MeasureTheory
open scoped ContDiff

namespace Blowup

private theorem sqrt_error_le {K b : ℝ} (hK : 0 ≤ K) :
    b * Real.sqrt K ≤ 4 * K + b ^ 2 / 16 := by
  nlinarith only [sq_nonneg (2 * Real.sqrt K - b / 4), Real.sq_sqrt hK]

/-- For radial weak H¹ data at p = 3, the negative weighted kinetic term absorbs
the quartic cutoff error. The remaining error depends only on the mass and the scale. -/
theorem virialSecondDeriv_cubicVirialWeight_le :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {R : ℝ} {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ},
        0 < R → IsH1 u Du → IsRadialAE u →
        virialSecondDeriv 3 (cubicVirialWeight R) u Du ≤
          16 * energy 3 u Du + (C * mass u ^ 3 + D * mass u) / R ^ 2 := by
  obtain ⟨B, hB, hLap⟩ := laplacian_cubicVirialWeight_deficit_bound
  obtain ⟨D, hD, hBilap⟩ := bilaplacian_cubicVirialWeight_bound
  let C := (B * radialTailConstant) ^ 2 / 16
  refine ⟨C, D, by positivity, hD, fun {R u Du} hR hu hur ↦ ?_⟩
  let w := cubicVirialCutoff R
  let K := weightedGradNormSq w Du
  let M := mass u
  let b := B * radialTailConstant * M * Real.sqrt M / R
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hK : 0 ≤ K := weightedGradNormSq_nonneg w Du
  have hw : ContDiff ℝ 1 w := (cubicVirialCutoff_contDiff hR).of_le (by simp)
  have hCutoff₀ := cubicVirialCutoff_nonneg R
  have hCutoff₁ := cubicVirialCutoff_le_one R
  have hQuartic := hu.weighted_quartic_integral_le hur hw (cubicVirialCutoff_monotone R)
    hCutoff₀ hCutoff₁ hR (fun _ hr ↦ cubicVirialCutoff_eq_zero hR hr)
  have hF : Integrable (fun x ↦ ‖u x‖ ^ (4 : ℝ)) := by
    simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using
      hu.integrable_nonlinear_density (p := 3) le_rfl
  have hEstimate := virialSecondDeriv_cubic_le_of_cutoff (cubicVirialWeight_isTestFunction hR)
    (hw.continuous.comp continuous_norm) (fun x ↦ hCutoff₀ ‖x‖) (fun x ↦ hCutoff₁ ‖x‖)
    (hessian_cubicVirialWeight_le hR) (hLap R hR) (hBilap R hR) hu hF
  change virialSecondDeriv 3 (cubicVirialWeight R) u Du ≤
    16 * energy 3 u Du - 8 * K + B * (∫ x, w ‖x‖ * ‖u x‖ ^ (4 : ℝ)) + D / R ^ 2 * M
    at hEstimate
  have hWeighted : B * (∫ x, w ‖x‖ * ‖u x‖ ^ (4 : ℝ)) ≤ b * Real.sqrt K := by
    calc
      _ ≤ B * ((radialTailConstant / R) * M * Real.sqrt M * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.rpow_ofNat] using hQuartic) hB
      _ = _ := by dsimp only [b]; ring
  have hb : b ^ 2 / 16 = C * M ^ 3 / R ^ 2 := by
    dsimp only [b, C]
    simp only [div_pow, mul_pow, Real.sq_sqrt hM]
    ring
  calc
    _ ≤ 16 * energy 3 u Du - 8 * K + (4 * K + b ^ 2 / 16) + D / R ^ 2 * M := by
      exact hEstimate.trans
        (add_le_add (add_le_add le_rfl (hWeighted.trans (sqrt_error_le hK))) le_rfl)
    _ ≤ 16 * energy 3 u Du + b ^ 2 / 16 + D / R ^ 2 * M := by linarith only [hK]
    _ = _ := by rw [hb]; change _ = 16 * energy 3 u Du + (C * M ^ 3 + D * M) / R ^ 2; ring

end Blowup
