import BlowupFormalization.WeakFirstVirial

/-! # Mass conservation for weak H¹ solutions -/

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Blowup

private def massBump : ContDiffBump (0 : ℝ²) :=
  ⟨1, 2, zero_lt_one, by norm_num⟩

private noncomputable def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private lemma cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  unfold cutoffScale
  positivity

private noncomputable def massCutoff (n : ℕ) (x : ℝ²) : ℝ :=
  massBump (cutoffScale n • x)

private lemma massCutoff_isTestFunction (n : ℕ) : IsTestFunction (massCutoff n) :=
  ⟨massBump.contDiff.comp (contDiff_id.const_smul (cutoffScale n)),
    massBump.hasCompactSupport.comp_smul (cutoffScale_pos n).ne'⟩

private lemma cutoffRadius_tendsto :
    Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private lemma eventually_massCutoff_eq_one (x : ℝ²) :
    ∀ᶠ n in atTop, massCutoff n x = 1 := by
  filter_upwards [cutoffRadius_tendsto.eventually (eventually_ge_atTop ‖x‖)] with n hn
  apply massBump.one_of_mem_closedBall
  change dist (cutoffScale n • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n),
    cutoffScale, ← div_eq_inv_mul, div_le_one (by positivity)]
  exact hn

private lemma exists_cutoff_gradient_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n j x, |partialDeriv j (massCutoff n) x| ≤ C * cutoffScale n := by
  have hBump : ContDiff ℝ ∞ (massBump : ℝ² → ℝ) := massBump.contDiff
  obtain ⟨C, hC⟩ := (hBump.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (massBump.hasCompactSupport.fderiv ℝ)
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun n j x ↦ ?_⟩
  have hDeriv :
      partialDeriv j (massCutoff n) x = cutoffScale n *
        partialDeriv j (massBump : ℝ² → ℝ) (cutoffScale n • x) := by
    have h := ((hBump.differentiable (by simp) (cutoffScale n • x)).hasFDerivAt).comp x
      ((hasFDerivAt_id x).const_smul (cutoffScale n))
    change HasFDerivAt (massCutoff n) _ x at h
    unfold partialDeriv
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul]
  have hGrad : |partialDeriv j (massBump : ℝ² → ℝ) (cutoffScale n • x)| ≤ C := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (massBump : ℝ² → ℝ) (cutoffScale n • x)‖ *
          ‖EuclideanSpace.single j (1 : ℝ)‖ :=
        (fderiv ℝ (massBump : ℝ² → ℝ) (cutoffScale n • x)).le_opNorm _
      _ ≤ C := by simpa [EuclideanSpace.single] using hC (cutoffScale n • x)
  rw [hDeriv, abs_mul, abs_of_pos (cutoffScale_pos n), mul_comm C]
  exact mul_le_mul_of_nonneg_left hGrad (cutoffScale_pos n).le

private lemma tendsto_cutoff_mass {u : ℝ² → ℂ} (hu : MemLp u 2) :
    Tendsto (fun n ↦ ∫ x, massCutoff n x * ‖u x‖ ^ 2) atTop (𝓝 (mass u)) := by
  have hd := hu.norm.integrable_sq
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x‖ ^ 2)
    (fun n ↦ (massCutoff_isTestFunction n).1.continuous.aestronglyMeasurable.mul hd.1)
    hd (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
  · have hn : 0 ≤ massCutoff n x := massBump.nonneg
    have hle : massCutoff n x ≤ 1 := massBump.le_one
    rw [Real.norm_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) hle
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_massCutoff_eq_one x] with n hn
    rw [hn, one_mul]

private lemma exists_bound_sqrt_mass {J : Set ℝ} {a b : ℝ} (hSub : Icc a b ⊆ J)
    {f : ℝ → ℝ² → ℂ} (hf : ∀ t : J, MemLp (f t) 2)
    (hfc : Continuous (fun t : J ↦ (hf t).toLp (f t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, Real.sqrt (mass (f t)) ≤ C := by
  let i (t : Icc a b) : J := ⟨t, hSub t.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨C, hC⟩ := (isCompact_range (hfc.comp hi).norm).bddAbove
  refine ⟨max 0 C, le_max_left _ _, fun t ht ↦ ?_⟩
  have hNorm : ‖(hf (i ⟨t, ht⟩)).toLp (f t)‖ = Real.sqrt (mass (f t)) :=
    norm_toLp_two (hf (i ⟨t, ht⟩))
  rw [← hNorm]
  exact (hC (mem_range_self (⟨t, ht⟩ : Icc a b))).trans (le_max_right _ _)

private lemma abs_virialFirstDeriv_le_gradient_bound {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {C : ℝ} (hC : ∀ j x, |partialDeriv j A x| ≤ C)
    {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ} (hu : MemLp u 2) (hDu : ∀ j, MemLp (Du j) 2) :
    |virialFirstDeriv A u Du| ≤ 2 * C * Real.sqrt (mass u) *
      (Real.sqrt (mass (Du 0)) + Real.sqrt (mass (Du 1))) := by
  let f (j : Fin 2) (x : ℝ²) :=
    (((partialDeriv j A x : ℝ) : ℂ) * starRingEnd ℂ (u x) * Du j x).im
  have hInt (j : Fin 2) : Integrable (f j) := by
    have hAj := hA.partialDeriv j
    have hCoeff : MemLp (fun x ↦ ((partialDeriv j A x : ℝ) : ℂ)) ⊤ :=
      (Complex.continuous_ofReal.comp hAj.1.continuous).memLp_of_hasCompactSupport
        (hAj.2.comp_left Complex.ofReal_zero)
    have hProduct : Integrable (fun x ↦ ((partialDeriv j A x : ℝ) : ℂ) *
        (starRingEnd ℂ (u x) * Du j x)) :=
      (hu.star.integrable_mul (hDu j)).mul_of_top_right hCoeff
    simpa only [f, mul_assoc, RCLike.im_eq_complex_im] using hProduct.im
  have hSplit : virialFirstDeriv A u Du = 2 * (∫ x, f 0 x) + 2 * (∫ x, f 1 x) := by
    unfold virialFirstDeriv
    simp only [mul_add, Complex.add_im]
    have hTerm (j : Fin 2) (x : ℝ²) :
        (starRingEnd ℂ (u x) * (((partialDeriv j A x : ℝ) : ℂ) * Du j x)).im = f j x := by
      simp only [f, mul_assoc, mul_left_comm (starRingEnd ℂ (u x))]
    simp only [hTerm]
    rw [integral_add (hInt 0) (hInt 1), mul_add]
  have hTerm (j : Fin 2) :=
    abs_virialResidual_le (hA.partialDeriv j).1.continuous (hC j) hu (hDu j)
  rw [hSplit]
  calc
    _ ≤ |2 * (∫ x, f 0 x)| + |2 * (∫ x, f 1 x)| := abs_add_le _ _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (hTerm 0) (hTerm 1)

/-- A weak H¹ NLS solution conserves mass across every closed time segment contained in
the interior of its time domain. -/
theorem IsNLSSolution.mass_eq {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (h : IsNLSSolution p J u Du) (hp : 3 ≤ p)
    {a b : ℝ} (hab : a ≤ b) (hSeg : Icc a b ⊆ interior J) :
    mass (u b) = mass (u a) := by
  have hSub : Icc a b ⊆ J := hSeg.trans interior_subset
  obtain ⟨G, hG, hGrad⟩ := exists_cutoff_gradient_bound
  obtain ⟨U, hU, hUb⟩ := exists_bound_sqrt_mass (f := u) hSub
    (fun t ↦ (h.h1 t t.2).memL2) h.continuous_toLp
  obtain ⟨D₀, hD₀, hD₀b⟩ := exists_bound_sqrt_mass (f := fun t ↦ Du t 0) hSub
    (fun t ↦ (h.h1 t t.2).memL2_partial 0) (h.continuous_grad_toLp 0)
  obtain ⟨D₁, hD₁, hD₁b⟩ := exists_bound_sqrt_mass (f := fun t ↦ Du t 1) hSub
    (fun t ↦ (h.h1 t t.2).memL2_partial 1) (h.continuous_grad_toLp 1)
  let C := 2 * G * U * (D₀ + D₁)
  let V (n : ℕ) (t : ℝ) := ∫ x, massCutoff n x * ‖u t x‖ ^ 2
  have hCurrent (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖virialFirstDeriv (massCutoff n) (u t) (Du t)‖ ≤ C * cutoffScale n := by
    have hl := h.h1 t (hSub ht)
    have hr := (cutoffScale_pos n).le
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2 * (G * cutoffScale n) * Real.sqrt (mass (u t)) *
          (Real.sqrt (mass (Du t 0)) + Real.sqrt (mass (Du t 1))) :=
        abs_virialFirstDeriv_le_gradient_bound (massCutoff_isTestFunction n) (hGrad n)
          hl.memL2 hl.memL2_partial
      _ ≤ 2 * (G * cutoffScale n) * U * (D₀ + D₁) := by
        gcongr
        · exact hUb t ht
        · exact hD₀b t ht
        · exact hD₁b t ht
      _ = C * cutoffScale n := by unfold C; ring
  have hVar (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (V n) (virialFirstDeriv (massCutoff n) (u t) (Du t)) (Icc a b) t :=
    (h.hasDerivAt_localizedVariance hp (massCutoff_isTestFunction n) (hSeg ht)).hasDerivWithinAt
  have hDiff (n : ℕ) : ‖V n b - V n a‖ ≤ (C * cutoffScale n) * (b - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (hVar n)
      (fun t ht ↦ hCurrent n t (Ico_subset_Icc_self ht)) b ⟨hab, le_rfl⟩
  have ha := tendsto_cutoff_mass (h.h1 a (hSub ⟨le_rfl, hab⟩)).memL2
  have hb := tendsto_cutoff_mass (h.h1 b (hSub ⟨hab, le_rfl⟩)).memL2
  have hInv : Tendsto cutoffScale atTop (𝓝 0) := tendsto_inv_atTop_zero.comp cutoffRadius_tendsto
  have hBound : Tendsto (fun n ↦ (C * cutoffScale n) * (b - a)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hInv.const_mul C).mul_const (b - a)
  have hLimit : ‖mass (u b) - mass (u a)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto (hb.sub ha).norm hBound (.of_forall hDiff)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hLimit)

end Blowup
