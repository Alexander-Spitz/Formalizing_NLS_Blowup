import BlowupFormalization.MaximalLifespan
import BlowupFormalization.VirialBlowupCriteria

/-! # Reduction of the full blow-up theorem to solution theory and the exterior estimate -/

open Set

namespace Blowup

/-- Proposition 3.2 supplies the remaining forward virial input for the superquintic range. -/
theorem forwardRadialBlowupCriterion_of_exterior_estimate
    (hExterior : SuperquinticExteriorEstimate) (p : ℝ) (hp : 3 ≤ p) :
    ForwardRadialBlowupCriterion p := by
  intro J u Du h hTime e he hEnergy hRadial
  by_cases hp₅ : p ≤ 5
  · exact h.false_of_radial_forward_of_le_five hp hp₅ hTime he hEnergy hRadial
  · have hp₅' : 5 < p := lt_of_not_ge hp₅
    obtain ⟨c₀, ε₀, C, hc₀, hε₀, hC, hEst⟩ := hExterior p hp₅'
    refine h.false_of_superquintic_exterior_estimate hp₅' hTime he hc₀ hε₀ hC.le hEnergy ?_
    intro T S hT hS hSmall hEps
    exact hEst h hT (fun _ ht ↦ hTime ht.1) (fun t ht ↦ hRadial t ht.1) hS hSmall hEps

/-- The exact frozen theorem follows from the H¹ solution theory and the
superquintic exterior estimate. -/
theorem radialNLSFiniteTimeBlowup_of_solution_theory_and_exterior_estimate
    (hTheory : MaximalH1SolutionTheory) (hExterior : SuperquinticExteriorEstimate) :
    RadialNLSFiniteTimeBlowup :=
  radialNLSFiniteTimeBlowup_of_solution_theory hTheory
    (forwardRadialBlowupCriterion_of_exterior_estimate hExterior)

end Blowup
