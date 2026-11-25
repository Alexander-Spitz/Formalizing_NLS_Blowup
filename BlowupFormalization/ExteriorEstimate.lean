import BlowupFormalization.Assumptions

/-!
# Section 3: an estimate for the exterior evolution

The exterior estimate, Proposition 3.2.

**Status:** the statement is final. The proof (Lemma 3.1 and the reflected
one-dimensional equation (3.7)–(3.16)) is still `sorry`; see `PROGRESS.md`.
-/

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

/-- **Proposition 3.2 (Exterior estimate).** Let `p > 5` and let `u ∈ C([0,T]; H¹_rad(ℝ²))`
solve (1.1). Write `M = ‖u₀‖₂²` and `F(T) = ∫₀ᵀ ‖∇u(t)‖₂² dt`. For `S ≥ 1` put
`ε = exteriorEps p T S u Du` (3.5).
There are `c₀, ε₀, C > 0` depending only on `p` such that, if `T/S² ≤ c₀` and `ε ≤ ε₀`,
some `R ∈ [S, 2S]` satisfies, for all `0 ≤ t ≤ T`, (3.6):
`∫_{|x|>R} |u(t)|^{p+1} ≤ C ε^{p-1} (∫_{|x|>R} |∇u(t)|² + M/S²)`. -/
theorem proposition_3_2 {p : ℝ} (hp : 5 < p) :
    ∃ c₀ ε₀ C : ℝ, 0 < c₀ ∧ 0 < ε₀ ∧ 0 < C ∧
    ∀ (T : ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ),
      0 < T → IsNLSSolution p (Set.Icc 0 T) u Du → IsRadial (u 0) →
      ∀ S : ℝ, 1 ≤ S → T / S ^ 2 ≤ c₀ →
      exteriorEps p T S u Du ≤ ε₀ →
      ∃ R ∈ Set.Icc S (2 * S), ∀ t ∈ Set.Icc 0 T,
        ∫ x in {x : ℝ² | R < ‖x‖}, ‖u t x‖ ^ (p + 1) ≤
          C * exteriorEps p T S u Du ^ (p - 1) *
          ((∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2) + mass (u 0) / S ^ 2) := by
  sorry

end Blowup
