import BlowupFormalization.Defs

/-! # Finite-time blow-up for radial two-dimensional focusing NLS -/

open Filter MeasureTheory Topology

namespace Blowup

/-- An `H¹` function is radial when its almost-everywhere class has a radial representative. -/
def IsRadialAE (u : ℝ² → ℂ) : Prop :=
  ∃ v : ℝ² → ℂ, IsRadial v ∧ u =ᵐ[volume] v

/-- Equality of the represented `H¹` data, including both weak partial derivatives. -/
def SameH1Data (u v : ℝ² → ℂ) (Du Dv : Fin 2 → ℝ² → ℂ) : Prop :=
  u =ᵐ[volume] v ∧ ∀ j, Du j =ᵐ[volume] Dv j

/-- The unique maximal solution through time zero. Every solution with the same data on an open
interval containing zero is its restriction, with equality in `H¹` at each time. -/
structure IsMaximalNLSSolution (p : ℝ) (J : Set ℝ) (u : ℝ → ℝ² → ℂ)
    (Du : ℝ → Fin 2 → ℝ² → ℂ) : Prop where
  isOpen : IsOpen J
  ordConnected : J.OrdConnected
  zero_mem : 0 ∈ J
  isSolution : IsNLSSolution p J u Du
  restrict_of_same_data : ∀ (K : Set ℝ) (v : ℝ → ℝ² → ℂ) (Dv : ℝ → Fin 2 → ℝ² → ℂ),
    IsOpen K → K.OrdConnected → 0 ∈ K → IsNLSSolution p K v Dv →
    SameH1Data (v 0) (u 0) (Dv 0) (Du 0) →
    K ⊆ J ∧ ∀ t ∈ K, SameH1Data (v t) (u t) (Dv t) (Du t)

/-- The full target for every real `p ≥ 3`. Radial `H¹(ℝ²)` data of negative energy have a
unique maximal focusing NLS solution on `(-Tminus, Tplus)`, with both lifespan parameters positive
and finite. The `L²` norm of its gradient tends to infinity at both endpoints from within the
lifespan. The lower range, the quintic endpoint, and the superquintic range all belong to
this specification. -/
def RadialNLSFiniteTimeBlowup : Prop :=
  ∀ (p : ℝ) (u₀ : ℝ² → ℂ) (Du₀ : Fin 2 → ℝ² → ℂ),
    3 ≤ p → IsH1 u₀ Du₀ → IsRadialAE u₀ → energy p u₀ Du₀ < 0 →
    ∃ (Tminus Tplus : ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ),
      0 < Tminus ∧ 0 < Tplus ∧
      let J := Set.Ioo (-Tminus) Tplus
      SameH1Data (u 0) u₀ (Du 0) Du₀ ∧
        IsMaximalNLSSolution p J u Du ∧
        Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] (-Tminus)) atTop ∧
        Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] Tplus) atTop

end Blowup
