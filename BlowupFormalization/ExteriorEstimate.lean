import BlowupFormalization.Defs

/-! # Quantities used in the exterior estimate, Proposition 3.2 -/

open MeasureTheory

namespace Blowup

/-- `‖u₀‖_{H¹} = (‖u₀‖₂² + ‖∇u₀‖₂²)^{1/2}`. -/
noncomputable def h1Norm (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  Real.sqrt (mass u + gradNormSq Du)

/-- The smallness parameter (3.5):
`ε = S^{-1/2} ‖u₀‖_{H¹} + T^{1/(p-1)} (F(T)/S² + M T/S⁴)^{1/2}` with `F(T) = ∫₀ᵀ ‖∇u‖₂²`,
`M = ‖u₀‖₂²`. -/
noncomputable def exteriorEps (p T S : ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ) : ℝ :=
  S ^ (-(1 : ℝ) / 2) * h1Norm (u 0) (Du 0) +
    T ^ (1 / (p - 1)) * Real.sqrt ((∫ t in (0)..T, gradNormSq (Du t)) / S ^ 2
      + mass (u 0) * T / S ^ 4)

end Blowup
