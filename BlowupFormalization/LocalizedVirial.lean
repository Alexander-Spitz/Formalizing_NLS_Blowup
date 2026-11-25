import BlowupFormalization.WeightProperties
import BlowupFormalization.SolutionFacts

/-!
# Section 4: the localized virial estimate

From the assumed localized virial identity (4.5) and the properties (4.3) of the
weight `A_Q`, we derive
* (4.6) `V_Q'' ≤ −8(p−1)e − 4(p−3)‖∇u‖₂² + C ∫_{|x|>Q} |u|^{p+1} + C M / Q²`;
* (4.7) `V_{2S}(0) ≤ H(S)` and `|V_{2S}'(0)|² ≤ 16 ‖∇u₀‖₂² V_{2S}(0)`.

Here `e = −E_p(u₀)`, so `−8(p−1)e = 8(p−1)E_p(u₀)`.
-/

open MeasureTheory

namespace Blowup

/-- **(4.6).** For every `H¹` solution on `[0, T]`, every `Q > 0` and `t ∈ [0, T]`:
`V_Q''(t) ≤ 8(p−1)E_p(u₀) − 4(p−3)‖∇u(t)‖₂² + C ∫_{|x|>Q} |u(t)|^{p+1} + C M/Q²`. -/
theorem eq_4_6 {p : ℝ} (hp : 5 < p) :
    ∃ C > 0, ∀ (T : ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ),
      IsNLSSolution p (Set.Icc 0 T) u Du → ∀ Q > 0, ∀ t ∈ Set.Icc 0 T,
        virialSecondDeriv p (virialWeight Q) (u t) (Du t) ≤
          8 * (p - 1) * energy p (u 0) (Du 0) - 4 * (p - 3) * gradNormSq (Du t)
          + C * (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1))
          + C * mass (u 0) / Q ^ 2 := by
  sorry

/-- **(4.7)**, first half: `V_{2S}(0) ≤ ∫_{|x| ≤ 10S} |x|² |u₀|² = H(S)`. -/
theorem eq_4_7_value {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) {S : ℝ} (hS : 0 < S) :
    ∫ x, virialWeight (2 * S) x * ‖u₀ x‖ ^ 2 ≤ compactMoment u₀ S := by
  sorry

/-- **(4.7)**, second half, squared: `|V_{2S}'(0)|² ≤ 16 ‖∇u₀‖₂² V_{2S}(0)`
(from `|∇A_Q|² ≤ 4 A_Q` and Cauchy–Schwarz). -/
theorem eq_4_7_deriv {u₀ : ℝ² → ℂ} {Du₀ : Fin 2 → ℝ² → ℂ} (h : IsH1 u₀ Du₀) {Q : ℝ}
    (hQ : 0 < Q) :
    virialFirstDeriv (virialWeight Q) u₀ Du₀ ^ 2 ≤
      16 * gradNormSq Du₀ * ∫ x, virialWeight Q x * ‖u₀ x‖ ^ 2 := by
  sorry

end Blowup
