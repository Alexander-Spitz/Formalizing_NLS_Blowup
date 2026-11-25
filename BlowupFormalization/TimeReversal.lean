import BlowupFormalization.Specification

/-! # Conjugate time reversal for NLS solutions -/

open Filter MeasureTheory Topology
open scoped ComplexConjugate ContDiff

namespace Blowup

private theorem integral_conj_mul_real (f : ℝ² → ℂ) (g : ℝ² → ℝ) :
    (∫ x, conj (f x) * (g x : ℂ)) = conj (∫ x, f x * (g x : ℂ)) := by
  simpa only [map_mul, Complex.conj_ofReal] using
    (integral_conj (μ := volume) (f := fun x ↦ f x * (g x : ℂ)))

/-- Complex conjugation preserves the weak spatial gradient. -/
theorem IsH1.conj {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (h : IsH1 u Du) :
    IsH1 (fun x ↦ conj (u x)) (fun j x ↦ conj (Du j x)) where
  memL2 := h.memL2.star
  memL2_partial j := (h.memL2_partial j).star
  integration_by_parts φ hφ j := by
    simp only [integral_conj_mul_real, h.integration_by_parts φ hφ j, map_neg]

private theorem tendsto_conj_time_reversal {J : Set ℝ} (f : ℝ → ℝ² → ℂ) (t : ℝ)
    (h : Tendsto (fun s ↦ ∫ x, ‖f s x - f (-t) x‖ ^ 2) (𝓝[J] (-t)) (𝓝 (0 : ℝ))) :
    Tendsto (fun s ↦ ∫ x, ‖conj (f (-s) x) - conj (f (-t) x)‖ ^ 2)
      (𝓝[Neg.neg ⁻¹' J] t) (𝓝 0) := by
  have hn : Tendsto (Neg.neg : ℝ → ℝ) (𝓝[Neg.neg ⁻¹' J] t) (𝓝[J] (-t)) :=
    continuous_neg.continuousWithinAt.tendsto_nhdsWithin (fun _ hx ↦ hx)
  simpa only [Function.comp_def, ← map_sub, Complex.norm_conj] using h.comp hn

private def reflectTest (φ : ℝ → ℝ² → ℝ) (t : ℝ) (x : ℝ²) : ℝ := φ (-t) x

private theorem reflectTest_admissible {J : Set ℝ} {φ : ℝ → ℝ² → ℝ}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hc : HasCompactSupport (Function.uncurry φ))
    (hs : tsupport (Function.uncurry φ) ⊆ interior (Neg.neg ⁻¹' J) ×ˢ Set.univ) :
    ContDiff ℝ ∞ (Function.uncurry (reflectTest φ)) ∧
      HasCompactSupport (Function.uncurry (reflectTest φ)) ∧
      tsupport (Function.uncurry (reflectTest φ)) ⊆ interior J ×ˢ Set.univ := by
  let R := (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ²)
  have hR : ContDiff ℝ ∞ (R : ℝ × ℝ² → ℝ × ℝ²) := by
    change ContDiff ℝ ∞ (fun z : ℝ × ℝ² ↦ (-z.1, z.2))
    fun_prop
  change ContDiff ℝ ∞ (Function.uncurry φ ∘ R) ∧
    HasCompactSupport (Function.uncurry φ ∘ R) ∧
    tsupport (Function.uncurry φ ∘ R) ⊆ interior J ×ˢ Set.univ
  refine ⟨hφ.comp hR, ?_, ?_⟩
  · change IsCompact (tsupport (Function.uncurry φ ∘ R))
    rw [tsupport_comp_eq_preimage]
    exact R.isCompact_preimage.2 hc
  · rw [tsupport_comp_eq_preimage]
    intro z hz
    have hz' := (hs hz).1
    change -z.1 ∈ interior (Neg.neg ⁻¹' J) at hz'
    have hInterior : (Neg.neg : ℝ → ℝ) ⁻¹' interior J = interior (Neg.neg ⁻¹' J) :=
      (Homeomorph.neg ℝ).preimage_interior J
    rw [← hInterior] at hz'
    exact ⟨by simpa only [Set.mem_preimage, neg_neg] using hz',
      Set.mem_univ _⟩

private theorem nonlinearity_conj (p : ℝ) (z : ℂ) :
    nonlinearity p (conj z) = conj (nonlinearity p z) := by
  simp only [nonlinearity, Complex.norm_conj, map_mul, Complex.conj_ofReal]

private theorem nlsTestIntegrand_conj_time_reversal (p : ℝ) (u : ℝ → ℝ² → ℂ)
    (φ : ℝ → ℝ² → ℝ) (t : ℝ) (x : ℝ²) :
    nlsTestIntegrand p (fun s y ↦ conj (u (-s) y)) φ t x =
      conj (nlsTestIntegrand p u (reflectTest φ) (-t) x) := by
  have ht : deriv (fun s ↦ φ (-s) x) (-t) = -deriv (fun s ↦ φ s x) t := by
    simpa only [neg_neg] using deriv_comp_neg (fun s ↦ φ s x) (-t)
  unfold nlsTestIntegrand reflectTest
  rw [ht]
  simp only [map_add, map_mul, map_neg, Complex.conj_I, neg_neg, Complex.ofReal_neg,
    Complex.conj_ofReal, ← nonlinearity_conj]
  ring

/-- If `u` solves (1.1), then `(t,x) ↦ conj (u (-t) x)` solves (1.1) on the reflected time
set. The weak equation follows by testing the original solution with the time-reflected test. -/
theorem IsNLSSolution.conj_time_reversal {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (h : IsNLSSolution p J u Du) :
    IsNLSSolution p (Neg.neg ⁻¹' J) (fun t x ↦ conj (u (-t) x))
      (fun t j x ↦ conj (Du (-t) j x)) where
  h1 t ht := (h.h1 (-t) ht).conj
  continuous_L2 t ht := tendsto_conj_time_reversal u t (h.continuous_L2 (-t) ht)
  continuous_grad_L2 t ht j :=
    tendsto_conj_time_reversal (fun s ↦ Du s j) t (h.continuous_grad_L2 (-t) ht j)
  weak_equation φ hφ hc hs := by
    obtain ⟨hψ, hψc, hψs⟩ := reflectTest_admissible hφ hc hs
    obtain ⟨hSpace, hTime, hZero⟩ := h.weak_equation (reflectTest φ) hψ hψc hψs
    let F (s : ℝ) : ℂ := ∫ x, nlsTestIntegrand p u (reflectTest φ) s x
    have hInner (t : ℝ) :
        (∫ x, nlsTestIntegrand p (fun s y ↦ conj (u (-s) y)) φ t x) = conj (F (-t)) := by
      simp only [nlsTestIntegrand_conj_time_reversal, integral_conj, F]
    have hNeg := Measure.measurePreserving_neg (volume : Measure ℝ)
    refine ⟨?_, ?_, ?_⟩
    · intro t
      have hConj : Integrable (fun x ↦ conj (nlsTestIntegrand p u (reflectTest φ) (-t) x)) :=
        Complex.conjLIE.integrable_comp_iff.2 (hSpace (-t))
      exact hConj.congr (.of_forall fun x ↦ (nlsTestIntegrand_conj_time_reversal p u φ t x).symm)
    · have hConj : Integrable (fun t ↦ conj (F t)) :=
        Complex.conjLIE.integrable_comp_iff.2 (show Integrable F from hTime)
      exact (hNeg.integrable_comp_of_integrable hConj).congr (.of_forall fun t ↦ (hInner t).symm)
    · simp only [hInner]
      calc
        (∫ t, conj (F (-t))) = ∫ t, conj (F t) :=
          hNeg.integral_comp (Homeomorph.neg ℝ).measurableEmbedding (fun t ↦ conj (F t))
        _ = conj (∫ t, F t) := integral_conj
        _ = 0 := by rw [show (∫ t, F t) = 0 from hZero, map_zero]

/-- Almost-everywhere equality of a function and its gradient is preserved by
complex conjugation. -/
theorem SameH1Data.conj {u v : ℝ² → ℂ} {Du Dv : Fin 2 → ℝ² → ℂ}
    (h : SameH1Data u v Du Dv) :
    SameH1Data (fun x ↦ conj (u x)) (fun x ↦ conj (v x))
      (fun j x ↦ conj (Du j x)) (fun j x ↦ conj (Dv j x)) :=
  ⟨h.1.fun_comp (starRingEnd ℂ), fun j ↦ (h.2 j).fun_comp (starRingEnd ℂ)⟩

/-- A maximal solution remains maximal after conjugate time reversal.
Reflect any competing solution back to the original time direction to apply maximality. -/
theorem IsMaximalNLSSolution.conj_time_reversal {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (h : IsMaximalNLSSolution p J u Du) :
    IsMaximalNLSSolution p (Neg.neg ⁻¹' J) (fun t x ↦ conj (u (-t) x))
      (fun t j x ↦ conj (Du (-t) j x)) where
  isOpen := h.isOpen.preimage continuous_neg
  ordConnected := h.ordConnected.preimage_anti (fun _ _ hle ↦ neg_le_neg hle)
  zero_mem := by simpa only [Set.mem_preimage, neg_zero] using h.zero_mem
  isSolution := h.isSolution.conj_time_reversal
  restrict_of_same_data K v Dv hOpen hOrd hZero hv hData := by
    have hData' :
        SameH1Data (fun x ↦ conj (v (-0) x)) (u 0)
          (fun j x ↦ conj (Dv (-0) j x)) (Du 0) := by
      simpa only [neg_zero, starRingEnd_apply, star_star] using hData.conj
    obtain ⟨hSub, hAgree⟩ := h.restrict_of_same_data (Neg.neg ⁻¹' K)
      (fun s x ↦ conj (v (-s) x)) (fun s j x ↦ conj (Dv (-s) j x))
      (hOpen.preimage continuous_neg) (hOrd.preimage_anti (fun _ _ hle ↦ neg_le_neg hle))
      (by simpa only [Set.mem_preimage, neg_zero] using hZero) hv.conj_time_reversal hData'
    have hMem (s : ℝ) (hs : s ∈ K) : -s ∈ Neg.neg ⁻¹' K := by
      simpa only [Set.mem_preimage, neg_neg] using hs
    refine ⟨fun s hs ↦ hSub (hMem s hs), ?_⟩
    intro s hs
    simpa only [neg_neg, starRingEnd_apply, star_star] using (hAgree (-s) (hMem s hs)).conj

/-- Conjugation preserves the squared gradient norm. -/
@[simp] theorem gradNormSq_conj (Du : Fin 2 → ℝ² → ℂ) :
    gradNormSq (fun j x ↦ conj (Du j x)) = gradNormSq Du := by
  simp only [gradNormSq, Complex.norm_conj]

/-- The gradient norm tends to infinity at the reflected time from within the reflected
lifespan exactly when the original gradient norm does so at the original time. -/
theorem tendsto_gradNorm_conj_time_reversal_iff
    (Du : ℝ → Fin 2 → ℝ² → ℂ) (J : Set ℝ) (t : ℝ) :
    Tendsto (fun s ↦ Real.sqrt (gradNormSq (fun j x ↦ conj (Du (-s) j x))))
      (𝓝[Neg.neg ⁻¹' J] (-t)) atTop ↔
    Tendsto (fun s ↦ Real.sqrt (gradNormSq (Du s))) (𝓝[J] t) atTop := by
  have hMap := (Homeomorph.neg ℝ).isEmbedding.map_nhdsWithin_eq
    ((Neg.neg : ℝ → ℝ) ⁻¹' J) (-t)
  change Filter.map Neg.neg (𝓝[Neg.neg ⁻¹' J] (-t)) =
    𝓝[(Neg.neg : ℝ → ℝ) '' (Neg.neg ⁻¹' J)] (-(-t)) at hMap
  rw [Set.image_preimage_eq (f := (Neg.neg : ℝ → ℝ)) J (Homeomorph.neg ℝ).surjective,
    neg_neg] at hMap
  simp only [gradNormSq_conj, ← hMap, tendsto_map'_iff, Function.comp_def]

/-- Conjugate initial data have the same mass. -/
@[simp] theorem mass_conj (u : ℝ² → ℂ) : mass (fun x ↦ conj (u x)) = mass u := by
  simp only [mass, Complex.norm_conj]

/-- Conjugate initial data have the same energy for every real exponent. -/
@[simp] theorem energy_conj (p : ℝ) (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) :
    energy p (fun x ↦ conj (u x)) (fun j x ↦ conj (Du j x)) = energy p u Du := by
  simp only [energy, gradNormSq_conj, potentialTerm, Complex.norm_conj]

/-- Conjugate data retain radiality up to almost-everywhere equality. -/
theorem IsRadialAE.conj {u : ℝ² → ℂ} (h : IsRadialAE u) :
    IsRadialAE (fun x ↦ conj (u x)) := by
  obtain ⟨v, hv, huv⟩ := h
  exact ⟨fun x ↦ conj (v x), fun x y hxy ↦ congrArg (starRingEnd ℂ) (hv x y hxy),
    huv.fun_comp (starRingEnd ℂ)⟩

end Blowup
