import BlowupFormalization.H1Sobolev
import BlowupFormalization.VirialContinuity

/-! # The nonlinear term in the second localized virial identity -/

open Filter MeasureTheory Topology
open scoped ContDiff ENNReal

namespace Blowup

private lemma continuous_partialDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ² → E} (hf : ContDiff ℝ 1 f) (j : Fin 2) : Continuous (partialDeriv j f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

private lemma integral_partialDeriv_mul_eq_neg_mul_partialDeriv
    {𝕜 : Type*} [RCLike 𝕜] {f g : ℝ² → 𝕜}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) (j : Fin 2) :
    ∫ x, partialDeriv j f x * g x = -∫ x, f x * partialDeriv j g x := by
  let e := EuclideanSpace.single j (1 : ℝ)
  have hLeft : Integrable (fun x ↦ partialDeriv j f x * g x) :=
    ((continuous_partialDeriv hf j).mul hg.continuous).integrable_of_hasCompactSupport
      (hfc.fderiv_apply ℝ e).mul_right
  have hRight : Integrable (fun x ↦ f x * partialDeriv j g x) :=
    (hf.continuous.mul (continuous_partialDeriv hg j)).integrable_of_hasCompactSupport
      hfc.mul_right
  have hBoth := (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
    (μ := volume) hfc.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e) hLeft hRight hBoth
    (fun x _ ↦ hf.differentiable one_ne_zero x) (fun x _ ↦ hg.differentiable one_ne_zero x)
  simpa only [neg_neg, partialDeriv, e] using (congrArg Neg.neg h).symm

private lemma isH1_of_contDiff {v : ℝ² → ℂ} (hv : ContDiff ℝ 1 v)
    (hV : MemLp v 2) (hD : ∀ j, MemLp (partialDeriv j v) 2) :
    IsH1 v (fun j ↦ partialDeriv j v) where
  memL2 := hV
  memL2_partial := hD
  integration_by_parts φ hφ j := by
    let ψ (x : ℝ²) : ℂ := φ x
    have hψ : ContDiff ℝ 1 ψ := Complex.ofRealCLM.contDiff.comp (hφ.1.of_le (by simp))
    have hψc : HasCompactSupport ψ := hφ.2.comp_left Complex.ofReal_zero
    have hCast (x : ℝ²) : partialDeriv j ψ x = (partialDeriv j φ x : ℝ) := by
      have h := (Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφ.1.differentiable (by simp) x).hasFDerivAt)).fderiv
      change fderiv ℝ ψ x = _ at h
      simp only [partialDeriv, h, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    simpa only [hCast, mul_comm, ψ] using
      integral_partialDeriv_mul_eq_neg_mul_partialDeriv hψ hv hψc j

private lemma re_weighted_nonlinearity {p : ℝ} (hp : 3 ≤ p) (a : ℝ) (z : ℂ) :
    (starRingEnd ℂ z * ((a : ℂ) * nonlinearity p z)).re = a * ‖z‖ ^ (p + 1) := by
  calc
    _ = ((a : ℂ) * ((‖z‖ ^ (p - 1) : ℝ) * (z * starRingEnd ℂ z))).re := by
      unfold nonlinearity
      congr 1
      ring
    _ = _ := by
      rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.mul_conj',
        ← Complex.ofReal_pow, Complex.ofReal_re,
        ← Real.rpow_natCast, ← Real.rpow_add_of_nonneg (norm_nonneg _) (by linarith) (by norm_num)]
      congr 2
      ring

private lemma partialDeriv_nonlinear_density {p : ℝ} (hp : 3 ≤ p) {v : ℝ² → ℂ}
    (hv : ContDiff ℝ 1 v) (j : Fin 2) (x : ℝ²) :
    partialDeriv j (fun y ↦ ‖v y‖ ^ (p + 1)) x =
      (p + 1) * (starRingEnd ℂ (partialDeriv j v x) * nonlinearity p (v x)).re := by
  have hPow : 1 < p + 1 := by linarith
  have hm : p + 1 - 2 = p - 1 := by ring
  rw [partialDeriv, (hv.differentiable one_ne_zero).fderiv_norm_rpow hPow]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.inner,
    hm, smul_eq_mul]
  change (p + 1) * ‖v x‖ ^ (p - 1) * (partialDeriv j v x * starRingEnd ℂ (v x)).re =
    (p + 1) * (starRingEnd ℂ (partialDeriv j v x) * nonlinearity p (v x)).re
  rw [nonlinearity, mul_left_comm, Complex.re_ofReal_mul]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma smooth_nonlinear_density_ibp {p : ℝ} (hp : 3 ≤ p) {v : ℝ² → ℂ}
    (hv : ContDiff ℝ 1 v) {φ : ℝ² → ℝ} (hφ : IsTestFunction φ) (j : Fin 2) :
    ∫ x, partialDeriv j φ x * ‖v x‖ ^ (p + 1) =
      -(p + 1) * (∫ x, (starRingEnd ℂ (partialDeriv j v x) *
        ((φ x : ℂ) * nonlinearity p (v x))).re) := by
  have hW : ContDiff ℝ 1 (fun x ↦ ‖v x‖ ^ (p + 1)) := hv.norm_rpow (by linarith)
  have hPoint (x : ℝ²) : φ x * partialDeriv j (fun y ↦ ‖v y‖ ^ (p + 1)) x =
      (p + 1) * (starRingEnd ℂ (partialDeriv j v x) *
        ((φ x : ℂ) * nonlinearity p (v x))).re := by
    rw [partialDeriv_nonlinear_density hp hv, mul_left_comm (starRingEnd ℂ _),
      Complex.re_ofReal_mul]
    ring
  rw [integral_partialDeriv_mul_eq_neg_mul_partialDeriv (hφ.1.of_le (by simp)) hW hφ.2 j]
  simp_rw [hPoint, integral_const_mul, neg_mul]

private lemma tendsto_toLp_two_of_mass_sub {f : ℕ → ℝ² → ℂ} {g : ℝ² → ℂ}
    (hf : ∀ n, MemLp (f n) 2) (hg : MemLp g 2)
    (hMass : Tendsto (fun n ↦ mass (f n - g)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hNorm (n : ℕ) :
      ‖(hf n).toLp (f n) - hg.toLp g‖ = Real.sqrt (mass (f n - g)) := by
    rw [← MemLp.toLp_sub, Lp.norm_toLp,
      ((hf n).sub hg).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hInt : 0 ≤ ∫ x, ‖f n x - g x‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
    simp [Real.sqrt_eq_rpow, mass, one_div, Real.rpow_nonneg hInt]
  simpa only [hNorm, Real.sqrt_zero] using hMass.sqrt

set_option maxHeartbeats 600000 in
-- Comparing the nonlinear maps on Lp representatives needs a larger elaboration budget.
private lemma tendsto_toLp_nonlinearity {p : ℝ} (hp : 2 < p)
    [Fact (1 ≤ ENNReal.ofReal (2 * p))] {f : ℕ → ℝ² → ℂ} {g : ℝ² → ℂ}
    (hf : ∀ n, MemLp (f n) (ENNReal.ofReal (2 * p))) (hg : MemLp g (ENNReal.ofReal (2 * p)))
    (h : Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n ↦ (memLp_nonlinearity hp (hf n)).toLp (fun x ↦ nonlinearity p (f n x))) atTop
      (𝓝 ((memLp_nonlinearity hp hg).toLp (fun x ↦ nonlinearity p (g x)))) := by
  let N (v : Lp ℂ (ENNReal.ofReal (2 * p)) (volume : Measure ℝ²)) :
      Lp ℂ 2 (volume : Measure ℝ²) :=
    (memLp_nonlinearity hp (Lp.memLp v)).toLp (fun x ↦ nonlinearity p (v x))
  have hN : Continuous N := continuous_toLp_nonlinearity
    (T := Lp ℂ (ENNReal.ofReal (2 * p)) (volume : Measure ℝ²)) (f := fun v ↦ (v : ℝ² → ℂ))
    hp Lp.memLp (by
      simp only [Lp.toLp_coeFn]
      exact continuous_id)
  have hEq (v : ℝ² → ℂ) (hv : MemLp v (ENNReal.ofReal (2 * p))) :
      N (hv.toLp v) = (memLp_nonlinearity hp hv).toLp (fun x ↦ nonlinearity p (v x)) := by
    have hAE : (fun x ↦ nonlinearity p ((hv.toLp v) x)) =ᵐ[volume]
        (fun x ↦ nonlinearity p (v x)) := hv.coeFn_toLp.fun_comp (nonlinearity p)
    unfold N
    exact MemLp.toLp_congr (memLp_nonlinearity hp (Lp.memLp (hv.toLp v)))
      (memLp_nonlinearity hp hv) hAE
  simpa only [Function.comp_def, hEq] using (hN.tendsto (hg.toLp g)).comp h

private lemma tendsto_integral_re_weighted_pairing {a : ℝ² → ℂ} (ha : MemLp a ∞)
    {f g : ℕ → ℝ² → ℂ} {F G : ℝ² → ℂ} (hf : ∀ n, MemLp (f n) 2)
    (hg : ∀ n, MemLp (g n) 2) (hF : MemLp F 2) (hG : MemLp G 2)
    (hfl : Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hF.toLp F)))
    (hgl : Tendsto (fun n ↦ (hg n).toLp (g n)) atTop (𝓝 (hG.toLp G))) :
    Tendsto (fun n ↦ ∫ x, (starRingEnd ℂ (f n x) * (a x * g n x)).re) atTop
      (𝓝 (∫ x, (starRingEnd ℂ (F x) * (a x * G x)).re)) := by
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure ℝ²) ∞ 2 2 (ha.toLp a)
  have hPair := hfl.inner (𝕜 := ℂ) ((M.continuous.tendsto (hG.toLp G)).comp hgl)
  have hRe := Complex.continuous_re.tendsto _ |>.comp hPair
  have hEq {v w : ℝ² → ℂ} (hv : MemLp v 2) (hw : MemLp w 2) :
      (inner ℂ (hv.toLp v) (M (hw.toLp w))).re =
        ∫ x, (starRingEnd ℂ (v x) * (a x * w x)).re := by
    exact (congrArg Complex.re (weighted_pairing_eq_inner ha hv hw)).trans
      (integral_re (integrable_weighted_pairing ha hv hw)).symm
  simpa only [Function.comp_def, hEq] using hRe

/-- The weak chain rule for the nonlinear density tested against a real test function. -/
theorem IsH1.nonlinear_density_ibp {p : ℝ} (hp : 3 ≤ p) {u : ℝ² → ℂ}
    {Du : Fin 2 → ℝ² → ℂ} (hu : IsH1 u Du) {φ : ℝ² → ℝ} (hφ : IsTestFunction φ)
    (j : Fin 2) :
    ∫ x, partialDeriv j φ x * ‖u x‖ ^ (p + 1) =
      -(p + 1) * (∫ x, (starRingEnd ℂ (Du j x) *
        ((φ x : ℂ) * nonlinearity p (u x))).re) := by
  let v (n : ℕ) := mollify (normalizedMollifier n) u
  let Dv (n : ℕ) (k : Fin 2) := partialDeriv k (v n)
  have hvc (n : ℕ) : ContDiff ℝ 1 (v n) :=
    (contDiff_mollify (normalizedMollifier_isTestFunction n) hu.memL2).of_le (by simp)
  have hv (n : ℕ) : MemLp (v n) 2 :=
    memLp_mollify (normalizedMollifier_isTestFunction n) hu.memL2
  have hDv (n : ℕ) (k : Fin 2) : MemLp (Dv n k) 2 := by
    change MemLp (partialDeriv k (mollify (normalizedMollifier n) u)) 2
    rw [hu.partialDeriv_mollify (normalizedMollifier_isTestFunction n) k]
    exact memLp_mollify (normalizedMollifier_isTestFunction n) (hu.memL2_partial k)
  have hvH (n : ℕ) : IsH1 (v n) (Dv n) := isH1_of_contDiff (hvc n) (hv n) (hDv n)
  have hvlim := tendsto_toLp_two_of_mass_sub hv hu.memL2
    (tendsto_mass_mollify_sub normalizedMollifier_isTestFunction normalizedMollifier_nonneg
      normalizedMollifier_integral normalizedMollifier_support tendsto_mollifierRadius hu.memL2)
  have hDvlim (k : Fin 2) := tendsto_toLp_two_of_mass_sub (fun n ↦ hDv n k)
    (hu.memL2_partial k) (hu.tendsto_mass_partialDeriv_mollify_sub
      normalizedMollifier_isTestFunction normalizedMollifier_nonneg normalizedMollifier_integral
      normalizedMollifier_support tendsto_mollifierRadius k)
  have hq : 2 ≤ 2 * p := by linarith
  let _ : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hvLp (n : ℕ) := (hvH n).memLp_of_two_le hq
  have huLp := hu.memLp_of_two_le hq
  have hLp : Tendsto (fun n ↦ (hvLp n).toLp (v n)) atTop (𝓝 (huLp.toLp u)) :=
    hu.tendsto_toLp_of_two_le hvH hq hvlim hDvlim
  have hp' : 2 < p := by linarith
  have hNlim := tendsto_toLp_nonlinearity hp' hvLp huLp hLp
  have hNv (n : ℕ) := (hvH n).memLp_nonlinearity hp
  have hNu := hu.memLp_nonlinearity hp
  have hLeft := tendsto_integral_re_weighted_pairing
    (testFunction_memLp_top_complex (hφ.partialDeriv j)) hv hNv hu.memL2 hNu hvlim hNlim
  have hRight := tendsto_integral_re_weighted_pairing
    (testFunction_memLp_top_complex hφ) (fun n ↦ hDv n j) hNv
    (hu.memL2_partial j) hNu (hDvlim j) hNlim
  simp_rw [re_weighted_nonlinearity hp] at hLeft
  have hBoth : Tendsto (fun n ↦ ∫ x, partialDeriv j φ x * ‖v n x‖ ^ (p + 1)) atTop
      (𝓝 (-(p + 1) * (∫ x, (starRingEnd ℂ (Du j x) *
        ((φ x : ℂ) * nonlinearity p (u x))).re))) :=
    (hRight.const_mul (-(p + 1))).congr fun n ↦ (smooth_nonlinear_density_ibp hp (hvc n) hφ j).symm
  exact tendsto_nhds_unique hLeft hBoth

/-- The two nonlinear pairings in the second virial derivative combine into the
weighted potential term in (4.5), for weak H¹ data and every real p ≥ 3. -/
theorem IsH1.second_virial_nonlinearity {p : ℝ} (hp : 3 ≤ p)
    {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (hu : IsH1 u Du)
    {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    -4 * (∑ j : Fin 2, ∫ x, (starRingEnd ℂ (Du j x) *
        ((↑(partialDeriv j A x) : ℂ) * nonlinearity p (u x))).re) -
      2 * (∫ x, (starRingEnd ℂ (u x) * (((laplacian A x : ℝ) : ℂ) * nonlinearity p (u x))).re) =
      -(2 * (p - 1) / (p + 1) * (∫ x, laplacian A x * ‖u x‖ ^ (p + 1))) := by
  let F (j : Fin 2) := ∫ x, (starRingEnd ℂ (Du j x) *
    ((↑(partialDeriv j A x) : ℂ) * nonlinearity p (u x))).re
  have hN := hu.memLp_nonlinearity hp
  have hInt (j : Fin 2) : Integrable (fun x ↦
      partialDeriv j (partialDeriv j A) x * ‖u x‖ ^ (p + 1)) := by
    have h := integrable_weighted_pairing
      (testFunction_memLp_top_complex ((hA.partialDeriv j).partialDeriv j)) hu.memL2 hN
    simpa only [RCLike.re_eq_complex_re, re_weighted_nonlinearity hp] using h.re
  have hLap :
      (∫ x, laplacian A x * ‖u x‖ ^ (p + 1)) = -(p + 1) * (F 0 + F 1) := by
    simp only [laplacian, add_mul, integral_add (hInt 0) (hInt 1)]
    rw [hu.nonlinear_density_ibp hp (hA.partialDeriv 0) 0,
      hu.nonlinear_density_ibp hp (hA.partialDeriv 1) 1]
    change -(p + 1) * F 0 + -(p + 1) * F 1 = _
    ring
  simp_rw [re_weighted_nonlinearity hp]
  change -4 * (∑ j : Fin 2, F j) - 2 * (∫ x, laplacian A x * ‖u x‖ ^ (p + 1)) = _
  rw [Fin.sum_univ_two, hLap]
  field_simp [show p + 1 ≠ 0 by linarith]
  ring

end Blowup
