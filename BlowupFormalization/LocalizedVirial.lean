import BlowupFormalization.Defs

/-! # Expressions for the localized virial identities (4.4)–(4.5) -/

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

end Blowup
