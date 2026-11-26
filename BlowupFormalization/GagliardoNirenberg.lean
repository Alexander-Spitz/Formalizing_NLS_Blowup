import BlowupFormalization.H1Sobolev

/-! # Homogeneous Gagliardo–Nirenberg inequality on the plane -/

open Filter MeasureTheory Topology
open scoped ContDiff ENNReal

namespace Blowup

private lemma integral_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ² → E) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, f (a • x)) = (a ^ 2)⁻¹ • (∫ x, f x) := by
  have hd : Module.finrank ℝ ℝ² = 2 := by simp
  simpa only [hd] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure ℝ²) f a (hR := ha)

private lemma memLp_two_dilate {f : ℝ² → ℂ} (hf : MemLp f 2) {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x ↦ f (a • x)) 2 := by
  have hMeas : AEStronglyMeasurable (fun x ↦ f (a • x)) :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ²) ha)
  exact (memLp_two_iff_integrable_sq_norm hMeas).mpr
    (((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).comp_smul ha)

private lemma partialDeriv_dilate_real {φ : ℝ² → ℝ} (hφ : Differentiable ℝ φ)
    (b : ℝ) (j : Fin 2) (y : ℝ²) :
    partialDeriv j (fun x ↦ φ (b • x)) y = b * partialDeriv j φ (b • y) := by
  have h := (hφ (b • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul b)
  change HasFDerivAt (fun x ↦ φ (b • x)) _ y at h
  unfold partialDeriv
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul]

/-- A positive spatial dilation preserves weak H¹, scaling each gradient coordinate once. -/
theorem IsH1.dilate {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (hu : IsH1 u Du) {a : ℝ}
    (ha : 0 < a) :
    IsH1 (fun x ↦ u (a • x)) (fun j x ↦ a • Du j (a • x)) where
  memL2 := memLp_two_dilate hu.memL2 ha.ne'
  memL2_partial j := (memLp_two_dilate (hu.memL2_partial j) ha.ne').const_smul a
  integration_by_parts φ hφ j := by
    let ψ (y : ℝ²) := φ (a⁻¹ • y)
    have hψ : IsTestFunction ψ := by
      refine ⟨hφ.1.comp (contDiff_id.const_smul _), ?_⟩
      exact hφ.2.comp_homeomorph (Homeomorph.smul (Units.mk0 _ (inv_ne_zero ha.ne')))
    have hψx (x : ℝ²) : ψ (a • x) = φ x := by
      simp only [ψ, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    have hψd (x : ℝ²) : partialDeriv j ψ (a • x) = a⁻¹ * partialDeriv j φ x := by
      rw [show partialDeriv j ψ (a • x) = a⁻¹ * partialDeriv j φ (a⁻¹ • (a • x)) from
        partialDeriv_dilate_real (hφ.1.differentiable (by simp)) _ _ _]
      simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    let F (y : ℝ²) := u y * ((partialDeriv j ψ y : ℝ) : ℂ)
    let G (y : ℝ²) := Du j y * (ψ y : ℂ)
    have hParts : (∫ y, F y) = -(∫ y, G y) := hu.integration_by_parts ψ hψ j
    have hChange : (∫ x, F (a • x)) = -(∫ x, G (a • x)) := by
      rw [integral_dilate F ha.le, integral_dilate G ha.le, hParts, smul_neg]
    have hChain (x : ℝ²) : F (a • x) =
        a⁻¹ • (u (a • x) * ((partialDeriv j φ x : ℝ) : ℂ)) := by
      simp only [F, hψd, Complex.ofReal_mul, Complex.real_smul]
      ring
    calc
      (∫ x, u (a • x) * ((partialDeriv j φ x : ℝ) : ℂ)) = ∫ x, a • F (a • x) := by
        simp only [hChain, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      _ = -(∫ x, a • G (a • x)) := by
        rw [integral_smul, integral_smul, hChange, smul_neg]
      _ = -(∫ x, (a • Du j (a • x)) * (φ x : ℂ)) := by
        simp only [G, hψx, Complex.real_smul, mul_assoc]

private lemma mass_dilate (f : ℝ² → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    mass (fun x ↦ f (a • x)) = (a ^ 2)⁻¹ * mass f :=
  integral_dilate (fun x ↦ ‖f x‖ ^ 2) ha

private lemma potentialTerm_dilate (p : ℝ) (f : ℝ² → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    potentialTerm p (fun x ↦ f (a • x)) = (a ^ 2)⁻¹ * potentialTerm p f :=
  integral_dilate (fun x ↦ ‖f x‖ ^ (p + 1)) ha

private lemma gradNormSq_dilate (Df : Fin 2 → ℝ² → ℂ) {a : ℝ} (ha : 0 < a) :
    gradNormSq (fun j x ↦ a • Df j (a • x)) = gradNormSq Df := by
  unfold gradNormSq
  simp only [norm_smul, Real.norm_of_nonneg ha.le, mul_pow, ← mul_add]
  rw [integral_const_mul, integral_dilate (fun x ↦ ‖Df 0 x‖ ^ 2 + ‖Df 1 x‖ ^ 2) ha.le,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul]

private lemma eLpNorm_two_eq_sqrt_mass {f : ℝ² → ℂ} (hf : MemLp f 2) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (mass f)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp [mass, Real.sqrt_eq_rpow, one_div]

private lemma mass_nonnegative (f : ℝ² → ℂ) : 0 ≤ mass f :=
  integral_nonneg fun _ ↦ sq_nonneg _

private lemma gradNormSq_nonnegative (Df : Fin 2 → ℝ² → ℂ) : 0 ≤ gradNormSq Df :=
  integral_nonneg fun _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma potentialTerm_nonnegative (p : ℝ) (f : ℝ² → ℂ) : 0 ≤ potentialTerm p f :=
  integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _

private lemma exists_potentialTerm_root_bound {p : ℝ} (hp : 3 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ), IsH1 u Du →
      potentialTerm p u ^ (1 / (p + 1)) ≤
        C * (Real.sqrt (mass u) + 2 * Real.sqrt (gradNormSq Du)) := by
  have hq : 2 ≤ p + 1 := by linarith
  have hq₀ : 0 < p + 1 := by linarith
  obtain ⟨C, hC, hSob⟩ := exists_eLpNorm_h1_bound (p + 1) hq
  refine ⟨C.toReal + 1, by positivity, fun u Du hu ↦ ?_⟩
  have hP : eLpNorm u (ENNReal.ofReal (p + 1)) volume =
      ENNReal.ofReal (potentialTerm p u ^ (1 / (p + 1))) := by
    rw [(hu.memLp_of_two_le hq).eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_pos.mpr hq₀).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq₀.le, potentialTerm]
    simp only [one_div]
  have hB := hSob u Du hu
  rw [hP, eLpNorm_two_eq_sqrt_mass hu.memL2,
    eLpNorm_two_eq_sqrt_mass (hu.memL2_partial 0),
    eLpNorm_two_eq_sqrt_mass (hu.memL2_partial 1)] at hB
  have hR : potentialTerm p u ^ (1 / (p + 1)) ≤ C.toReal *
      (Real.sqrt (mass u) + Real.sqrt (mass (Du 0)) + Real.sqrt (mass (Du 1))) := by
    have hFinite : C * (ENNReal.ofReal (Real.sqrt (mass u)) +
        ENNReal.ofReal (Real.sqrt (mass (Du 0))) + ENNReal.ofReal (Real.sqrt (mass (Du 1)))) ≠ ⊤ :=
      ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr ⟨by finiteness, by finiteness⟩)
    simpa (disch := finiteness) only
      [ENNReal.toReal_ofReal (Real.rpow_nonneg (potentialTerm_nonnegative p u) _),
      ENNReal.toReal_mul, ENNReal.toReal_add,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using ENNReal.toReal_mono hFinite hB
  have hInt (j : Fin 2) := ((memLp_two_iff_integrable_sq_norm
    (hu.memL2_partial j).aestronglyMeasurable).mp (hu.memL2_partial j))
  have hG : gradNormSq Du = mass (Du 0) + mass (Du 1) := integral_add (hInt 0) (hInt 1)
  have h0 : Real.sqrt (mass (Du 0)) ≤ Real.sqrt (gradNormSq Du) :=
    Real.sqrt_le_sqrt (hG ▸ le_add_of_nonneg_right (mass_nonnegative _))
  have h1 : Real.sqrt (mass (Du 1)) ≤ Real.sqrt (gradNormSq Du) :=
    Real.sqrt_le_sqrt (hG ▸ le_add_of_nonneg_left (mass_nonnegative _))
  refine hR.trans ((mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)))
  linarith only [h0, h1]

/-- The homogeneous two-dimensional Gagliardo–Nirenberg bound on the potential term for
every real exponent in the target range. -/
theorem exists_potentialTerm_le_mass_mul_gradNormSq_rpow {p : ℝ} (hp : 3 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ), IsH1 u Du →
      potentialTerm p u ≤ C * mass u * gradNormSq Du ^ ((p - 1) / 2) := by
  obtain ⟨C, hC, hSob⟩ := exists_potentialTerm_root_bound hp
  let q := p + 1
  let s := (p - 1) / 2
  let K := (3 * C) ^ q
  have hq : 0 < q := by dsimp [q]; linarith
  have hs : 0 < s := by dsimp [s]; linarith
  have hK : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨K, hK, fun u Du hu ↦ ?_⟩
  let M := mass u
  let D := gradNormSq Du
  let P := potentialTerm p u
  have hM : 0 ≤ M := mass_nonnegative _
  have hD : 0 ≤ D := gradNormSq_nonnegative _
  have hP : 0 ≤ P := potentialTerm_nonnegative _ _
  -- The regularized balancing scale handles both zero mass and zero gradient.
  have hAux (ε : ℝ) (hε : 0 < ε) : P ≤ K * (M + ε) * (D + ε) ^ s := by
    have hMε : 0 < M + ε := by positivity
    have hDε : 0 < D + ε := by positivity
    let a := Real.sqrt ((M + ε) / (D + ε))
    have ha : 0 < a := Real.sqrt_pos_of_pos (div_pos hMε hDε)
    have haSq : a ^ 2 = (M + ε) / (D + ε) :=
      Real.sq_sqrt (div_nonneg hMε.le hDε.le)
    have hScaledM : (a ^ 2)⁻¹ * M ≤ D + ε := by
      rw [haSq, inv_div]
      calc
        _ ≤ ((D + ε) / (M + ε)) * (M + ε) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) (by positivity)
        _ = _ := div_mul_cancel₀ _ hMε.ne'
    have hScaled := hSob (fun x ↦ u (a • x)) (fun j x ↦ a • Du j (a • x)) (hu.dilate ha)
    rw [potentialTerm_dilate _ _ ha.le, mass_dilate _ ha.le, gradNormSq_dilate _ ha] at hScaled
    have hRoot : ((a ^ 2)⁻¹ * P) ^ (1 / q) ≤ 3 * C * Real.sqrt (D + ε) :=
      hScaled.trans (calc
        _ ≤ C * (Real.sqrt (D + ε) + 2 * Real.sqrt (D + ε)) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          exact add_le_add (Real.sqrt_le_sqrt hScaledM)
            (mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (le_add_of_nonneg_right hε.le : D ≤ D + ε)) (by norm_num))
        _ = _ := by ring)
    have hBase : 0 ≤ (a ^ 2)⁻¹ * P := by positivity
    have hPow := Real.rpow_le_rpow (Real.rpow_nonneg hBase _) hRoot hq.le
    rw [← Real.rpow_mul hBase, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one,
      Real.mul_rpow (by positivity : 0 ≤ 3 * C) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hDε.le, show (1 / (2 : ℝ)) * q = q / 2 by ring] at hPow
    calc
      P = a ^ 2 * ((a ^ 2)⁻¹ * P) := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'), one_mul]
      _ ≤ a ^ 2 * (K * (D + ε) ^ (q / 2)) := mul_le_mul_of_nonneg_left hPow (sq_nonneg _)
      _ = K * (M + ε) * (D + ε) ^ s := by
        rw [haSq, show q / 2 = s + 1 by dsimp [q, s]; ring, Real.rpow_add_one hDε.ne']
        field_simp
  have hCont : Continuous (fun ε : ℝ ↦ K * (M + ε) * (D + ε) ^ s) :=
    (continuous_const.mul (continuous_const.add continuous_id)).mul
      ((continuous_const.add continuous_id).rpow_const (fun _ ↦ Or.inr hs.le))
  have hLim : Tendsto (fun ε : ℝ ↦ K * (M + ε) * (D + ε) ^ s) (𝓝[>] 0) (𝓝 (K * M * D ^ s)) := by
    simpa only [add_zero] using
      (hCont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hLim (eventually_mem_nhdsWithin.mono (fun ε hε ↦ hAux ε hε))

/-- A positive mass bound and strictly negative energy give a uniform positive lower bound on
the squared gradient norm, as used in (5.2). -/
theorem exists_pos_le_gradNormSq_of_energy_le_neg {p : ℝ} (hp : 3 ≤ p)
    {M e : ℝ} (hM : 0 < M) (he : 0 < e) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ), IsH1 u Du →
      mass u ≤ M → energy p u Du ≤ -e → γ ≤ gradNormSq Du := by
  obtain ⟨C, hC, hGN⟩ := exists_potentialTerm_le_mass_mul_gradNormSq_rpow hp
  let s := (p - 1) / 2
  let k := (p + 1) * e / (C * M)
  have hs : 0 < s := by dsimp [s]; linarith
  have hp₁ : 0 < p + 1 := by linarith
  have hk : 0 < k := by dsimp [k]; positivity
  let γ := k ^ s⁻¹
  have hγ : 0 < γ := Real.rpow_pos_of_pos hk _
  refine ⟨γ, hγ, fun u Du hu hm hE ↦ ?_⟩
  have hG := gradNormSq_nonnegative Du
  have hLower : (p + 1) * e ≤ potentialTerm p u := by
    rw [mul_comm, ← le_div_iff₀ hp₁]
    unfold energy at hE
    linarith only [hE, hG]
  have hUpper : potentialTerm p u ≤ (C * M) * gradNormSq Du ^ s := by
    refine (hGN u Du hu).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC.le)
      (Real.rpow_nonneg hG _)
  have hPower : k ≤ gradNormSq Du ^ s := by
    apply (div_le_iff₀ (mul_pos hC hM)).mpr
    exact (hLower.trans hUpper).trans_eq (mul_comm _ _)
  apply (Real.rpow_le_rpow_iff hγ.le hG hs).mp
  change (k ^ s⁻¹) ^ s ≤ _
  rwa [← Real.rpow_mul hk.le, inv_mul_cancel₀ hs.ne', Real.rpow_one]

end Blowup
