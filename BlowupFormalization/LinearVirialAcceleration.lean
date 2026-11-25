import BlowupFormalization.WeightProperties

/-! # Spatial integration by parts for the linear terms in the virial acceleration -/

open MeasureTheory
open scoped ContDiff BigOperators

namespace Blowup

private lemma contDiff_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ² → E} {m n : ℕ∞ω} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (j : Fin 2) :
    ContDiff ℝ m (partialDeriv j f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

private lemma integrable_weighted_inner {W : ℝ² → ℝ} (hW : IsTestFunction W)
    {f g : ℝ² → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x ↦ W x * inner ℝ (f x) (g x)) :=
  (hW.1.continuous.mul (hf.inner hg)).integrable_of_hasCompactSupport hW.2.mul_right

private lemma integral_weighted_inner_partial {W : ℝ² → ℝ} (hW : IsTestFunction W)
    {f g : ℝ² → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (j : Fin 2) :
    (∫ x, W x * inner ℝ (f x) (partialDeriv j g x)) =
      -(∫ x, partialDeriv j W x * inner ℝ (f x) (g x)) -
        ∫ x, W x * inner ℝ (partialDeriv j f x) (g x) := by
  let F (x : ℝ²) := W x • f x
  let e := EuclideanSpace.single j (1 : ℝ)
  have hW₁ : ContDiff ℝ 1 W := hW.1.of_le (by simp)
  have hF : ContDiff ℝ 1 F := hW₁.smul hf
  have hf' : Continuous (partialDeriv j f) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : Continuous (partialDeriv j g) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hProd (x : ℝ²) : partialDeriv j F x =
      partialDeriv j W x • f x + W x • partialDeriv j f x := by
    change fderiv ℝ (fun y ↦ W y • f y) x e = _
    rw [fderiv_fun_smul (hW₁.differentiable one_ne_zero x) (hf.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, partialDeriv, e]
    exact add_comm _ _
  have hEval (x : ℝ²) : inner ℝ (partialDeriv j F x) (g x) =
      partialDeriv j W x * inner ℝ (f x) (g x) +
        W x * inner ℝ (partialDeriv j f x) (g x) := by
    rw [hProd, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hI₁ := integrable_weighted_inner (hW.partialDeriv j) hf.continuous hg.continuous
  have hI₂ := integrable_weighted_inner hW hf' hg.continuous
  have hLeft : Integrable (fun x ↦ inner ℝ (partialDeriv j F x) (g x)) := by
    simp_rw [hEval]
    exact hI₁.add hI₂
  have hRight : Integrable (fun x ↦ inner ℝ (F x) (partialDeriv j g x)) := by
    simpa only [F, real_inner_smul_left] using integrable_weighted_inner hW hf.continuous hg'
  have hBase : Integrable (fun x ↦ inner ℝ (F x) (g x)) := by
    simpa only [F, real_inner_smul_left] using
      integrable_weighted_inner hW hf.continuous hg.continuous
  have hParts := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure ℝ²)) (B := innerSL ℝ (E := ℂ)) (v := e)
    hLeft hRight hBase
    (fun x _ ↦ hF.differentiable one_ne_zero x) (fun x _ ↦ hg.differentiable one_ne_zero x)
  change (∫ x, inner ℝ (F x) (partialDeriv j g x)) =
    -(∫ x, inner ℝ (partialDeriv j F x) (g x)) at hParts
  simp_rw [hEval, F, real_inner_smul_left] at hParts
  rw [integral_add hI₁ hI₂] at hParts
  linarith only [hParts]

private lemma integral_weighted_inner_self_partial {W : ℝ² → ℝ} (hW : IsTestFunction W)
    {f : ℝ² → ℂ} (hf : ContDiff ℝ 1 f) (j : Fin 2) :
    (∫ x, W x * inner ℝ (partialDeriv j f x) (f x)) =
      -(∫ x, partialDeriv j W x * ‖f x‖ ^ 2) / 2 := by
  have h := integral_weighted_inner_partial hW hf hf j
  simp_rw [real_inner_comm (partialDeriv j f _) (f _), real_inner_self_eq_norm_sq] at h
  linarith only [h]

private lemma integral_weighted_inner_laplacian_split {W : ℝ² → ℝ} (hW : IsTestFunction W)
    {f g : ℝ² → ℂ} (hf : Continuous f) (hg : ContDiff ℝ 2 g) :
    (∫ x, W x * inner ℝ (f x) (laplacian g x)) =
      (∫ x, W x * inner ℝ (f x) (partialDeriv 0 (partialDeriv 0 g) x)) +
      (∫ x, W x * inner ℝ (f x) (partialDeriv 1 (partialDeriv 1 g) x)) := by
  have hD (k : Fin 2) : ContDiff ℝ 1 (partialDeriv k g) :=
    contDiff_partial hg (by norm_num) k
  have hInt (k : Fin 2) : Integrable (fun x ↦ W x *
      inner ℝ (f x) (partialDeriv k (partialDeriv k g) x)) :=
    integrable_weighted_inner hW hf
      (((hD k).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  simp only [laplacian, inner_add_right, mul_add]
  exact integral_add (hInt 0) (hInt 1)

private lemma integral_laplacian_mul_norm_sq_split {B : ℝ² → ℝ} (hB : IsTestFunction B)
    {f : ℝ² → ℂ} (hf : Continuous f) :
    (∫ x, laplacian B x * ‖f x‖ ^ 2) =
      (∫ x, partialDeriv 0 (partialDeriv 0 B) x * ‖f x‖ ^ 2) +
      (∫ x, partialDeriv 1 (partialDeriv 1 B) x * ‖f x‖ ^ 2) := by
  have hInt (k : Fin 2) : Integrable
      (fun x ↦ partialDeriv k (partialDeriv k B) x * ‖f x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using
      integrable_weighted_inner ((hB.partialDeriv k).partialDeriv k) hf hf
  simp only [laplacian, add_mul]
  exact integral_add (hInt 0) (hInt 1)

private lemma weighted_conj_mul_re (a : ℝ) (z w : ℂ) :
    (starRingEnd ℂ z * ((a : ℂ) * w)).re = a * inner ℝ z w := by
  rw [mul_left_comm, Complex.re_ofReal_mul, Complex.inner, mul_comm (starRingEnd ℂ z) w]

private lemma mul_conj_re_inner (z w : ℂ) :
    (z * starRingEnd ℂ w).re = inner ℝ z w :=
  (Complex.inner w z).symm.trans (real_inner_comm z w)

/-- The spatial integrations by parts for the linear terms of the second virial identity (4.5). -/
theorem linear_virial_acceleration {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {u : ℝ² → ℂ} (hu : ContDiff ℝ 3 u) :
    -4 * (∑ j : Fin 2, ∫ x, (starRingEnd ℂ (partialDeriv j u x) *
      (((partialDeriv j A x : ℝ) : ℂ) * laplacian u x)).re) -
    2 * (∫ x, (starRingEnd ℂ (u x) * (((laplacian A x : ℝ) : ℂ) * laplacian u x)).re) =
    4 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
      (partialDeriv j u x * starRingEnd ℂ (partialDeriv k u x)).re) -
    ∫ x, laplacian (laplacian A) x * ‖u x‖ ^ 2 := by
  have hA₂ : ContDiff ℝ 2 A := hA.1.of_le (by simp)
  have hu₂ : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hDu (j : Fin 2) : ContDiff ℝ 1 (partialDeriv j u) :=
    contDiff_partial hu₂ (by norm_num) j
  -- When the Laplacian is paired with a first derivative, moving its first derivative yields
  -- a Hessian term and a derivative of the kinetic density.
  have hGradient (j k : Fin 2) :
      (∫ x, partialDeriv j A x *
        inner ℝ (partialDeriv j u x) (partialDeriv k (partialDeriv k u) x)) =
      -(∫ x, partialDeriv j (partialDeriv k A) x *
        inner ℝ (partialDeriv j u x) (partialDeriv k u x)) +
      (∫ x, partialDeriv j (partialDeriv j A) x * ‖partialDeriv k u x‖ ^ 2) / 2 := by
    have hParts := integral_weighted_inner_partial (hA.partialDeriv j) (hDu j) (hDu k) k
    rw [partialDeriv_comm hA₂ k j, partialDeriv_comm hu₂ k j,
      integral_weighted_inner_self_partial (hA.partialDeriv j) (hDu k) j] at hParts
    linarith only [hParts]
  -- The other Laplacian pairing supplies the same kinetic density with the opposite coefficient.
  have hDensity (k : Fin 2) :
      (∫ x, laplacian A x * inner ℝ (u x) (partialDeriv k (partialDeriv k u) x)) =
      -(∫ x, laplacian A x * ‖partialDeriv k u x‖ ^ 2) +
      (∫ x, partialDeriv k (partialDeriv k (laplacian A)) x * ‖u x‖ ^ 2) / 2 := by
    have hParts := integral_weighted_inner_partial hA.laplacian hu₁ (hDu k) k
    simp_rw [real_inner_comm (partialDeriv k u _) (u _), real_inner_self_eq_norm_sq] at hParts
    rw [integral_weighted_inner_self_partial (hA.laplacian.partialDeriv k) hu₁ k] at hParts
    linarith only [hParts]
  have hH (j k : Fin 2) : Integrable (fun x ↦
      partialDeriv j (partialDeriv k A) x * inner ℝ (partialDeriv j u x) (partialDeriv k u x)) :=
    integrable_weighted_inner ((hA.partialDeriv k).partialDeriv j)
      (hDu j).continuous (hDu k).continuous
  have hHessian :
      (∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
        inner ℝ (partialDeriv j u x) (partialDeriv k u x)) =
      ∑ j : Fin 2, ∑ k : Fin 2, ∫ x, partialDeriv j (partialDeriv k A) x *
        inner ℝ (partialDeriv j u x) (partialDeriv k u x) := by
    let H (j k : Fin 2) (x : ℝ²) :=
      partialDeriv j (partialDeriv k A) x * inner ℝ (partialDeriv j u x) (partialDeriv k u x)
    have hRow (j : Fin 2) : Integrable (fun x ↦ H j 0 x + H j 1 x) :=
      (hH j 0).add (hH j 1)
    simp only [Fin.sum_univ_two]
    change (∫ x, (H 0 0 x + H 0 1 x) + (H 1 0 x + H 1 1 x)) = _
    rw [integral_add (hRow 0) (hRow 1)]
    exact congrArg₂ (· + ·) (integral_add (hH 0 0) (hH 0 1)) (integral_add (hH 1 0) (hH 1 1))
  simp_rw [weighted_conj_mul_re, mul_conj_re_inner]
  rw [hHessian, integral_laplacian_mul_norm_sq_split hA.laplacian hu.continuous]
  simp only [Fin.sum_univ_two]
  rw [integral_weighted_inner_laplacian_split (hA.partialDeriv 0) (hDu 0).continuous hu₂,
    integral_weighted_inner_laplacian_split (hA.partialDeriv 1) (hDu 1).continuous hu₂,
    integral_weighted_inner_laplacian_split hA.laplacian hu.continuous hu₂]
  have hDensity₀ := hDensity 0
  have hDensity₁ := hDensity 1
  rw [integral_laplacian_mul_norm_sq_split hA (hDu 0).continuous] at hDensity₀
  rw [integral_laplacian_mul_norm_sq_split hA (hDu 1).continuous] at hDensity₁
  linarith only [hGradient 0 0, hGradient 0 1, hGradient 1 0, hGradient 1 1, hDensity₀, hDensity₁]

end Blowup
