import BlowupFormalization.Mollification
import BlowupFormalization.WeightProperties

/-! # The spatially mollified weak NLS equation -/

open MeasureTheory Set
open scoped ContDiff

namespace Blowup

private lemma integrable_kernel_mul {A : ℝ² → ℝ} {f : ℝ² → ℂ}
    (hA : IsTestFunction A) (hf : MemLp f 2) (x : ℝ²) :
    Integrable (fun y ↦ (A (x - y) : ℂ) * f y) :=
  hA.2.convolutionExists_right ((ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (hf.locallyIntegrable (by norm_num)) hA.1.continuous x

/-- The spatial Laplacian of the convolution acts on the smooth kernel. -/
theorem laplacian_mollify_kernel {ρ : ℝ² → ℝ} {f : ℝ² → ℂ}
    (hρ : IsTestFunction ρ) (hf : MemLp f 2) :
    laplacian (mollify ρ f) = mollify (laplacian ρ) f := by
  funext x
  have hTerm (j : Fin 2) := integrable_kernel_mul ((hρ.partialDeriv j).partialDeriv j) hf x
  simp only [laplacian, partialDeriv_mollify_kernel hρ hf 0, partialDeriv_mollify_kernel hρ hf 1,
    partialDeriv_mollify_kernel (hρ.partialDeriv 0) hf 0,
    partialDeriv_mollify_kernel (hρ.partialDeriv 1) hf 1, mollify_apply]
  rw [← integral_add (hTerm 0) (hTerm 1)]
  simp only [← add_mul, ← Complex.ofReal_add]

private lemma partialDeriv_neg_real (f : ℝ² → ℝ) (j : Fin 2) :
    partialDeriv j (-f) = -partialDeriv j f := by
  funext y
  simp only [partialDeriv, fderiv_neg, neg_apply, Pi.neg_apply]

private lemma laplacian_reflected_kernel {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) (x y : ℝ²) :
    laplacian (fun z ↦ ρ (x - z)) y = laplacian ρ (x - y) := by
  have hPart (j : Fin 2) :
      partialDeriv j (fun z ↦ ρ (x - z)) = -(fun z ↦ partialDeriv j ρ (x - z)) :=
    funext (fun z ↦ partialDeriv_reflected_kernel hρ.1 x z j)
  have hDiag (j : Fin 2) :
      partialDeriv j (partialDeriv j (fun z ↦ ρ (x - z))) y =
        partialDeriv j (partialDeriv j ρ) (x - y) := by
    rw [hPart j, partialDeriv_neg_real, Pi.neg_apply,
      partialDeriv_reflected_kernel (hρ.partialDeriv j).1, neg_neg]
  simp only [laplacian, hDiag]

private lemma partialDeriv_const_mul_real {A : ℝ² → ℝ} (hA : IsTestFunction A) (c : ℝ)
    (j : Fin 2) : partialDeriv j (fun y ↦ c * A y) = fun y ↦ c * partialDeriv j A y := by
  funext y
  simp only [partialDeriv, fderiv_const_mul (hA.1.differentiable (by simp) y) c,
    smul_apply, smul_eq_mul]

private lemma laplacian_const_mul_real {A : ℝ² → ℝ} (hA : IsTestFunction A) (c : ℝ) (y : ℝ²) :
    laplacian (fun z ↦ c * A z) y = c * laplacian A y := by
  simp only [laplacian, partialDeriv_const_mul_real hA,
    partialDeriv_const_mul_real (hA.partialDeriv 0),
    partialDeriv_const_mul_real (hA.partialDeriv 1), mul_add]

/-- At each spatial point, the spatially mollified equation holds against every temporal
test function supported in the interior of the solution's time domain. -/
theorem IsNLSSolution.weak_equation_mollify
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) (x : ℝ²)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηJ : tsupport η ⊆ interior J) :
    Integrable (fun t ↦ mollify ρ (u t) x * (-Complex.I * ((deriv η t : ℝ) : ℂ)) +
      (laplacian (mollify ρ (u t)) x + mollify ρ (fun y ↦ nonlinearity p (u t y)) x) *
        (η t : ℂ)) ∧
    (∫ t, mollify ρ (u t) x * (-Complex.I * ((deriv η t : ℝ) : ℂ)) +
      (laplacian (mollify ρ (u t)) x + mollify ρ (fun y ↦ nonlinearity p (u t y)) x) *
        (η t : ℂ)) = 0 := by
  let A : ℝ² → ℝ := fun y ↦ ρ (x - y)
  let φ : ℝ → ℝ² → ℝ := fun t y ↦ η t * A y
  have hA : IsTestFunction A := reflected_kernel_isTestFunction hρ x
  have hSmooth : ContDiff ℝ ∞ (Function.uncurry φ) :=
    (hη.comp contDiff_fst).mul (hA.1.comp contDiff_snd)
  have hSupp : tsupport (Function.uncurry φ) ⊆ tsupport η ×ˢ tsupport A := by
    refine closure_minimal (fun z hz ↦ ?_) (isClosed_closure.prod isClosed_closure)
    change η z.1 * A z.2 ≠ 0 at hz
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hz),
      subset_tsupport _ (right_ne_zero_of_mul hz)⟩
  obtain ⟨hSpatial, hTemporal, hZero⟩ :=
    h.weak_equation φ hSmooth ((hηc.prod hA.2).of_isClosed_subset isClosed_closure hSupp)
      (hSupp.trans (prod_mono hηJ (subset_univ _)))
  let U (t : ℝ) (y : ℝ²) : ℂ := (ρ (x - y) : ℂ) * u t y
  let L (t : ℝ) (y : ℝ²) : ℂ := ((laplacian ρ (x - y) : ℝ) : ℂ) * u t y
  let N (t : ℝ) (y : ℝ²) : ℂ := (ρ (x - y) : ℂ) * nonlinearity p (u t y)
  let c (t : ℝ) : ℂ := -Complex.I * ((deriv η t : ℝ) : ℂ)
  let d (t : ℝ) : ℂ := η t
  have hTest (t : ℝ) (y : ℝ²) :
      nlsTestIntegrand p u φ t y = U t y * c t + L t y * d t + N t y * d t := by
    have hDeriv : deriv (fun s ↦ φ s y) t = deriv η t * A y :=
      deriv_mul_const (hη.differentiable (by simp) t) (A y)
    have hLap : laplacian (φ t) y = η t * laplacian ρ (x - y) := by
      rw [laplacian_const_mul_real hA (η t) y, laplacian_reflected_kernel hρ x y]
    simp only [nlsTestIntegrand, hDeriv, hLap, φ, U, L, N, c, d, A, Complex.ofReal_mul]
    ring
  have hIntegral (t : ℝ) : (∫ y, nlsTestIntegrand p u φ t y) =
      mollify ρ (u t) x * c t +
        (laplacian (mollify ρ (u t)) x + mollify ρ (fun y ↦ nonlinearity p (u t y)) x) * d t := by
    by_cases ht : t ∈ J
    · have hu := (h.h1 t ht).memL2
      have hU : Integrable (fun y ↦ U t y * c t) := (integrable_kernel_mul hρ hu x).mul_const _
      have hL : Integrable (fun y ↦ L t y * d t) :=
        (integrable_kernel_mul hρ.laplacian hu x).mul_const _
      have hLinear : Integrable (fun y ↦ U t y * c t + L t y * d t) := hU.add hL
      -- Integrability is needed for the tested nonlinear term, which includes the factor η(t).
      have hN : Integrable (fun y ↦ N t y * d t) := by
        refine ((hSpatial t).sub hLinear).congr (.of_forall fun y ↦ ?_)
        change nlsTestIntegrand p u φ t y - (U t y * c t + L t y * d t) = N t y * d t
        rw [hTest, add_sub_cancel_left]
      simp only [hTest]
      rw [integral_add hLinear hN, integral_add hU hL]
      simp only [integral_mul_const, laplacian_mollify_kernel hρ hu, mollify_apply,
        add_mul, add_assoc, U, L, N]
    · have hηt : t ∉ tsupport η := fun hmem ↦ ht (interior_subset (hηJ hmem))
      have hc : c t = 0 := by simp [c, deriv_of_notMem_tsupport hηt]
      have hd : d t = 0 := by simp [d, image_eq_zero_of_notMem_tsupport hηt]
      simp only [hTest, hc, hd, mul_zero, add_zero, integral_zero]
  exact ⟨hTemporal.congr (.of_forall hIntegral),
    (integral_congr_ae (.of_forall hIntegral)).symm.trans hZero⟩

end Blowup
