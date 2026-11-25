import BlowupFormalization.Specification

/-! # Invariance under changes of H¹ representative -/

open MeasureTheory

namespace Blowup.SameH1Data

variable {u v : ℝ² → ℂ} {Du Dv : Fin 2 → ℝ² → ℂ}

private theorem isH1_of_eq (h : SameH1Data u v Du Dv) (hu : IsH1 u Du) : IsH1 v Dv where
  memL2 := (memLp_congr_ae h.1).mp hu.memL2
  memL2_partial j := (memLp_congr_ae (h.2 j)).mp (hu.memL2_partial j)
  integration_by_parts φ hφ j := by
    have huv :
        (∫ x, u x * ((partialDeriv j φ x : ℝ) : ℂ)) =
          ∫ x, v x * ((partialDeriv j φ x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [h.1] with x hx
      rw [hx]
    have hDuDv : (∫ x, Du j x * (φ x : ℂ)) = ∫ x, Dv j x * (φ x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [h.2 j] with x hx
      rw [hx]
    rw [← huv, ← hDuDv]
    exact hu.integration_by_parts φ hφ j

/-- Almost-everywhere equality of the function and its gradient preserves
the H¹ conditions, including the weak integration-by-parts identity. -/
theorem isH1_iff (h : SameH1Data u v Du Dv) : IsH1 u Du ↔ IsH1 v Dv :=
  ⟨isH1_of_eq h, isH1_of_eq ⟨h.1.symm, fun j ↦ (h.2 j).symm⟩⟩

/-- The mass in (1.2) is independent of the representative. -/
theorem mass_eq (h : SameH1Data u v Du Dv) : mass u = mass v :=
  integral_congr_ae (h.1.fun_comp (fun z ↦ ‖z‖ ^ (2 : ℕ)))

/-- The kinetic integral is independent of the weak gradient representative. -/
theorem gradNormSq_eq (h : SameH1Data u v Du Dv) : gradNormSq Du = gradNormSq Dv := by
  apply integral_congr_ae
  filter_upwards [h.2 0, h.2 1] with x hx₀ hx₁
  rw [hx₀, hx₁]

/-- The energy in (1.2) is independent of both representatives for every real exponent. -/
theorem energy_eq (h : SameH1Data u v Du Dv) (p : ℝ) : energy p u Du = energy p v Dv := by
  have hp : potentialTerm p u = potentialTerm p v :=
    integral_congr_ae (h.1.fun_comp (fun z ↦ ‖z‖ ^ (p + 1)))
  simp only [energy, h.gradNormSq_eq, hp]

end Blowup.SameH1Data

namespace Blowup

/-- The difference of two weak H¹ functions has the difference of their weak gradients. -/
theorem IsH1.sub {u v : ℝ² → ℂ} {Du Dv : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hv : IsH1 v Dv) : IsH1 (u - v) (Du - Dv) where
  memL2 := hu.memL2.sub hv.memL2
  memL2_partial j := (hu.memL2_partial j).sub (hv.memL2_partial j)
  integration_by_parts φ hφ j := by
    let e := EuclideanSpace.single j (1 : ℝ)
    have hTest : MemLp (fun x ↦ (φ x : ℂ)) 2 :=
      (Complex.continuous_ofReal.comp hφ.1.continuous).memLp_of_hasCompactSupport
        (hφ.2.comp_left Complex.ofReal_zero)
    have hPartial : MemLp (fun x ↦ ((partialDeriv j φ x : ℝ) : ℂ)) 2 :=
      (Complex.continuous_ofReal.comp
        ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
          ((hφ.2.fderiv_apply ℝ e).comp_left Complex.ofReal_zero)
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub
      (f := fun x ↦ u x * ((partialDeriv j φ x : ℝ) : ℂ))
      (g := fun x ↦ v x * ((partialDeriv j φ x : ℝ) : ℂ))
      (hu.memL2.integrable_mul hPartial) (hv.memL2.integrable_mul hPartial)]
    rw [integral_sub
      (f := fun x ↦ Du j x * (φ x : ℂ)) (g := fun x ↦ Dv j x * (φ x : ℂ))
      ((hu.memL2_partial j).integrable_mul hTest) ((hv.memL2_partial j).integrable_mul hTest),
      hu.integration_by_parts φ hφ j, hv.integration_by_parts φ hφ j]
    abel

end Blowup
