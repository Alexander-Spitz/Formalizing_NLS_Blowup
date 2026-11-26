import BlowupFormalization.Specification

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

/-- The estimate required from Proposition 3.2 on time segments in the interior of
a weak solution's domain. The constants depend only on p, and one radius works throughout
each segment satisfying the smallness conditions. -/
def SuperquinticExteriorEstimate : Prop :=
  ∀ p : ℝ, 5 < p →
    ∃ c₀ ε₀ C : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧ 0 < C ∧
      ∀ {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ} {T S : ℝ},
        IsNLSSolution p J u Du → 0 < T → Set.Icc 0 T ⊆ interior J →
        (∀ t ∈ Set.Icc 0 T, IsRadialAE (u t)) →
        1 ≤ S → T / S ^ 2 ≤ c₀ → exteriorEps p T S u Du ≤ ε₀ →
        ∃ R ∈ Set.Icc S (2 * S), ∀ t ∈ Set.Icc 0 T,
          (∫ x in {x : ℝ² | R < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤
            C * exteriorEps p T S u Du ^ (p - 1) *
              ((∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2) +
                mass (u 0) / S ^ 2)

end Blowup
