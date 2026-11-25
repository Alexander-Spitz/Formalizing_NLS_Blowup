import BlowupFormalization.Defs

/-! # Spatial convolution of weak H¹ data -/

open MeasureTheory
open scoped ContDiff Convolution

namespace Blowup

/-- Convolution with the real-valued spatial kernel `ρ`, using real scalar multiplication. -/
noncomputable def mollify (ρ : ℝ² → ℝ) (f : ℝ² → ℂ) : ℝ² → ℂ :=
  f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip] ρ

/-- The convolution written with the kernel evaluated at `x - y`. -/
theorem mollify_apply (ρ : ℝ² → ℝ) (f : ℝ² → ℂ) (x : ℝ²) :
    mollify ρ f x = ∫ y, (ρ (x - y) : ℂ) * f y := rfl

/-- Convolving an L² function with a smooth compactly supported kernel yields a smooth function. -/
theorem contDiff_mollify {ρ : ℝ² → ℝ} {f : ℝ² → ℂ} (hρ : IsTestFunction ρ)
    (hf : MemLp f 2) : ContDiff ℝ ∞ (mollify ρ f) :=
  hρ.2.contDiff_convolution_right _ (hf.locallyIntegrable (by norm_num)) hρ.1

private theorem mollify_memLp_and_mass_bound {ρ : ℝ² → ℝ} {f : ℝ² → ℂ}
    (hρ : IsTestFunction ρ) (hf : MemLp f 2) :
    MemLp (mollify ρ f) 2 ∧
      mass (mollify ρ f) ≤ (∫ y, ‖ρ y‖) ^ 2 * mass f := by
  let w : ℝ² → ℝ := fun y ↦ ‖ρ y‖
  let g : ℝ² → ℝ := fun y ↦ ‖f y‖ ^ 2
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hwCont : Continuous w := hρ.1.continuous.norm
  have hwSupp : HasCompactSupport w := hρ.2.norm
  have hw : Integrable w := hwCont.integrable_of_hasCompactSupport hwSupp
  have hg : Integrable g := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hPointwise (x : ℝ²) :
      ‖mollify ρ f x‖ ^ 2 ≤ (∫ y, w y) * (w ⋆[L] g) x := by
    have hwg : Integrable (fun y ↦ w y * g (x - y)) :=
      hwSupp.convolutionExists_left L hwCont hg.locallyIntegrable x
    let a : ℝ² → ℝ := fun y ↦ Real.sqrt (w y)
    let b : ℝ² → ℝ := fun y ↦ a y * ‖f (x - y)‖
    have haNonneg (y) : 0 ≤ a y := Real.sqrt_nonneg _
    have hbNonneg (y) : 0 ≤ b y := mul_nonneg (haNonneg y) (norm_nonneg _)
    have haSq (y) : a y ^ 2 = w y := Real.sq_sqrt (norm_nonneg _)
    have hbSq (y) : b y ^ 2 = w y * g (x - y) := by
      simp only [b, g, mul_pow, haSq]
    have haMeas : AEStronglyMeasurable a volume := (hwCont.sqrt).aestronglyMeasurable
    have hbMeas : AEStronglyMeasurable b volume := by
      have h : (fun y ↦ Real.sqrt (w y * g (x - y))) = b := by
        funext y
        rw [← hbSq y, Real.sqrt_sq (hbNonneg y)]
      exact h ▸ hwg.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    have ha : MemLp a 2 := (memLp_two_iff_integrable_sq haMeas).mpr (by simpa only [haSq])
    have hb : MemLp b 2 := (memLp_two_iff_integrable_sq hbMeas).mpr (by simpa only [hbSq])
    have hHolder : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hHolder
      (.of_forall haNonneg) (.of_forall hbNonneg) (by simpa using ha) (by simpa using hb)
    have hNorm : ‖mollify ρ f x‖ ≤ ∫ y, a y * b y := by
      unfold mollify
      rw [convolution_flip]
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      apply integral_congr_ae (.of_forall fun y ↦ ?_)
      change ‖(ρ y : ℂ) * f (x - y)‖ = a y * b y
      rw [norm_mul, Complex.norm_real, show b y = a y * ‖f (x - y)‖ from rfl,
        ← mul_assoc, ← pow_two, haSq]
    change ‖mollify ρ f x‖ ^ 2 ≤ (∫ y, w y) * (∫ y, w y * g (x - y))
    have hCS' : (∫ y, a y * b y) ≤
        Real.sqrt (∫ y, w y) * Real.sqrt (∫ y, w y * g (x - y)) := by
      simpa only [Real.rpow_two, haSq, hbSq, ← Real.sqrt_eq_rpow] using hCS
    calc
      _ ≤ (Real.sqrt (∫ y, w y) * Real.sqrt (∫ y, w y * g (x - y))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hNorm.trans hCS') 2
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (integral_nonneg fun y ↦ norm_nonneg _),
          Real.sq_sqrt (integral_nonneg fun y ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _))]
  have hBound : Integrable (fun x ↦ (∫ y, w y) * (w ⋆[L] g) x) :=
    (hw.integrable_convolution L hg).const_mul _
  have hContinuous := (contDiff_mollify hρ hf).continuous
  have hSq : Integrable (fun x ↦ ‖mollify ρ f x‖ ^ 2) :=
    hBound.mono_nonneg (hContinuous.norm.pow 2).aestronglyMeasurable
      (.of_forall fun _ ↦ sq_nonneg _) (.of_forall hPointwise)
  refine ⟨(memLp_two_iff_integrable_sq_norm hContinuous.aestronglyMeasurable).mpr hSq, ?_⟩
  calc
    mass (mollify ρ f) ≤ ∫ x, (∫ y, w y) * (w ⋆[L] g) x :=
      integral_mono hSq hBound hPointwise
    _ = (∫ y, ‖ρ y‖) ^ 2 * mass f := by
      rw [integral_const_mul, integral_convolution L hw hg]
      change (∫ y, w y) * ((∫ y, w y) * (∫ y, g y)) = (∫ y, w y) ^ 2 * (∫ y, g y)
      rw [pow_two, mul_assoc]

/-- Convolution with a smooth compactly supported kernel preserves L². -/
theorem memLp_mollify {ρ : ℝ² → ℝ} {f : ℝ² → ℂ} (hρ : IsTestFunction ρ)
    (hf : MemLp f 2) : MemLp (mollify ρ f) 2 :=
  (mollify_memLp_and_mass_bound hρ hf).1

/-- Convolution bounds the mass by the original mass times the squared L¹ norm of the kernel. -/
theorem mass_mollify_le {ρ : ℝ² → ℝ} {f : ℝ² → ℂ} (hρ : IsTestFunction ρ)
    (hf : MemLp f 2) : mass (mollify ρ f) ≤ (∫ y, ‖ρ y‖) ^ 2 * mass f :=
  (mollify_memLp_and_mass_bound hρ hf).2

/-- For L² data, a classical spatial derivative of the convolution can act on the kernel. -/
theorem partialDeriv_mollify_kernel {ρ : ℝ² → ℝ} {f : ℝ² → ℂ} (hρ : IsTestFunction ρ)
    (hf : MemLp f 2) (j : Fin 2) :
    partialDeriv j (mollify ρ f) = mollify (partialDeriv j ρ) f := by
  funext x
  have hfLoc := hf.locallyIntegrable (by norm_num)
  have hρ₁ : ContDiff ℝ 1 ρ := hρ.1.of_le (by simp)
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  change fderiv ℝ (f ⋆[L] ρ) x (EuclideanSpace.single j 1) = _
  rw [(hρ.2.hasFDerivAt_convolution_right L hfLoc hρ₁ x).fderiv]
  exact convolution_precompR_apply L hfLoc (hρ.2.fderiv ℝ)
    (hρ₁.continuous_fderiv one_ne_zero) x _

private theorem reflected_kernel_isTestFunction {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (x : ℝ²) : IsTestFunction (fun y ↦ ρ (x - y)) := by
  refine ⟨hρ.1.comp (by fun_prop), ?_⟩
  let R := (Homeomorph.neg ℝ²).trans (Homeomorph.addLeft x)
  simp only [sub_eq_add_neg]
  change HasCompactSupport (ρ ∘ R)
  exact hρ.2.comp_homeomorph R

private theorem partialDeriv_reflected_kernel {ρ : ℝ² → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x y : ℝ²) (j : Fin 2) :
    partialDeriv j (fun z ↦ ρ (x - z)) y = -partialDeriv j ρ (x - y) := by
  have hReflect := (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id y)
  have hComp : HasFDerivAt (fun z ↦ ρ (x - z))
      ((fderiv ℝ ρ (x - y)).comp (0 - ContinuousLinearMap.id ℝ ℝ²)) y :=
    ((hρ.differentiable (by simp) (x - y)).hasFDerivAt).comp y hReflect
  simp only [partialDeriv, hComp.fderiv, ContinuousLinearMap.comp_apply,
    zero_sub, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

/-- A classical derivative of the mollified function is the mollified weak derivative.
Apply weak integration by parts with `y ↦ ρ (x - y)`. -/
theorem IsH1.partialDeriv_mollify {ρ : ℝ² → ℝ} {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hρ : IsTestFunction ρ) (j : Fin 2) :
    partialDeriv j (mollify ρ u) = mollify ρ (Du j) := by
  rw [partialDeriv_mollify_kernel hρ hu.memL2 j]
  funext x
  have hParts := hu.integration_by_parts (fun y ↦ ρ (x - y))
    (reflected_kernel_isTestFunction hρ x) j
  simp_rw [partialDeriv_reflected_kernel hρ.1, Complex.ofReal_neg, mul_neg,
    integral_neg, neg_inj] at hParts
  simpa only [mollify_apply, mul_comm] using hParts

end Blowup
