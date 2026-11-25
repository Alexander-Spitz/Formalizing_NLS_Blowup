import BlowupFormalization.MollifierConvergence
import BlowupFormalization.VirialContinuity

/-! # Locally uniform spatial approximation of the virial expressions -/

open Filter MeasureTheory Topology
open scoped ENNReal Uniformity

namespace Blowup

local notation "SpatialL2" => Lp ℂ 2 (volume : Measure ℝ²)

private lemma norm_toLp_eq_sqrt_mass {f : ℝ² → ℂ} (hf : MemLp f 2) :
    ‖hf.toLp f‖ = Real.sqrt (mass f) := by
  rw [mass, Lp.norm_toLp, toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow, one_div]

private lemma mollify_congr_ae {ρ : ℝ² → ℝ} {f g : ℝ² → ℂ}
    (h : f =ᵐ[volume] g) : mollify ρ f = mollify ρ g := by
  funext x
  simp only [mollify_apply]
  exact integral_congr_ae (h.mono fun _ hy ↦ congrArg _ hy)

/-- Mollification acting on the space of L² equivalence classes. -/
noncomputable def mollifyL2 (ρ : ℝ² → ℝ) (hρ : IsTestFunction ρ) (f : SpatialL2) :
    SpatialL2 :=
  (memLp_mollify hρ (Lp.memLp f)).toLp (mollify ρ f)

/-- Mollification on L² agrees with mollification of any representative. -/
theorem mollifyL2_toLp {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) {f : ℝ² → ℂ} (hf : MemLp f 2) :
    mollifyL2 ρ hρ (hf.toLp f) = (memLp_mollify hρ hf).toLp (mollify ρ f) :=
  MemLp.toLp_congr _ _ (.of_forall (congrFun (mollify_congr_ae hf.coeFn_toLp)))

private lemma mollifyL2_sub {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) (f g : SpatialL2) :
    mollifyL2 ρ hρ (f - g) = mollifyL2 ρ hρ f - mollifyL2 ρ hρ g := by
  have hf := Lp.memLp f
  have hg := Lp.memLp g
  have hSub : (hf.sub hg).toLp ((f : ℝ² → ℂ) - (g : ℝ² → ℂ)) = f - g := by
    rw [MemLp.toLp_sub hf hg, Lp.toLp_coeFn f hf, Lp.toLp_coeFn g hg]
  calc
    _ = (memLp_mollify hρ (hf.sub hg)).toLp (mollify ρ ((f : ℝ² → ℂ) - (g : ℝ² → ℂ))) := by
      rw [← hSub, mollifyL2_toLp]
    _ = _ := by
      unfold mollifyL2
      rw [← MemLp.toLp_sub (memLp_mollify hρ hf) (memLp_mollify hρ hg)]
      exact MemLp.toLp_congr _ _ (.of_forall (congrFun (mollify_sub hρ hf hg)))

/-- A nonnegative normalized kernel is a contraction for the L² distance. -/
theorem dist_mollifyL2_le {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hNonneg : ∀ x, 0 ≤ ρ x) (hIntegral : ∫ x, ρ x = 1) (f g : SpatialL2) :
    dist (mollifyL2 ρ hρ f) (mollifyL2 ρ hρ g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← mollifyL2_sub, mollifyL2, norm_toLp_eq_sqrt_mass,
    ← Lp.toLp_coeFn (f - g) (Lp.memLp (f - g)), norm_toLp_eq_sqrt_mass]
  apply Real.sqrt_le_sqrt
  simpa only [Lp.toLp_coeFn, Real.norm_of_nonneg (hNonneg _), hIntegral, one_pow, one_mul]
    using mass_mollify_le hρ (Lp.memLp (f - g))

variable {ρ : ℕ → ℝ² → ℝ} {r : ℕ → ℝ}

private lemma tendsto_mollifyL2 (hρ : ∀ n, IsTestFunction (ρ n))
    (hNonneg : ∀ n x, 0 ≤ ρ n x) (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) (f : SpatialL2) :
    Tendsto (fun n ↦ mollifyL2 (ρ n) (hρ n) f) atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hNorm (n : ℕ) :
      ‖mollifyL2 (ρ n) (hρ n) f - f‖ = Real.sqrt (mass (mollify (ρ n) f - (f : ℝ² → ℂ))) := by
    have hM := memLp_mollify (hρ n) (Lp.memLp f)
    have hDiff : (hM.sub (Lp.memLp f)).toLp (mollify (ρ n) f - (f : ℝ² → ℂ)) =
        mollifyL2 (ρ n) (hρ n) f - f := by
      rw [MemLp.toLp_sub hM (Lp.memLp f), Lp.toLp_coeFn f (Lp.memLp f)]
      rfl
    rw [← hDiff, norm_toLp_eq_sqrt_mass]
  have hMass := tendsto_mass_mollify_sub hρ hNonneg hIntegral hSupport hr (Lp.memLp f)
  simpa only [hNorm, Real.sqrt_zero] using hMass.sqrt

/-- A sequence of normalized nonnegative kernels with shrinking supports converges uniformly to
the identity on every compact family in L². -/
theorem tendstoUniformlyOn_mollifyL2 (hρ : ∀ n, IsTestFunction (ρ n))
    (hNonneg : ∀ n x, 0 ≤ ρ n x) (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) {K : Set SpatialL2} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n ↦ mollifyL2 (ρ n) (hρ n)) id atTop K := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  have hThird : 0 < ε / 3 := by positivity
  obtain ⟨S, -, hS, hCover⟩ := hK.finite_cover_balls hThird
  have hCenters (v : SpatialL2) :
      ∀ᶠ n in atTop, dist (v) (mollifyL2 (ρ n) (hρ n) v) < ε / 3 := by
    have h := Metric.tendsto_nhds.mp (tendsto_mollifyL2 hρ hNonneg hIntegral hSupport hr v) _ hThird
    simpa only [dist_comm] using h
  filter_upwards [hS.eventually_all.mpr (fun v _ ↦ hCenters v)] with n hn f hf
  obtain ⟨v, hv, hfv⟩ := Set.mem_iUnion₂.mp (hCover hf)
  have hfv' : dist f v < ε / 3 := hfv
  have hContract := dist_mollifyL2_le (hρ n) (hNonneg n) (hIntegral n) v f
  change dist f (mollifyL2 (ρ n) (hρ n) f) < ε
  refine (dist_triangle _ v _).trans_lt ?_
  grw [dist_triangle v (mollifyL2 (ρ n) (hρ n) v), hContract, dist_comm v f]
  linarith [hn v hv]

private lemma tendstoUniformlyOn_comp_continuous {ι X Y Z : Type*}
    [UniformSpace Y] [UniformSpace Z] {l : Filter ι} {F : ι → X → Y} {f : X → Y}
    {K : Set X} {C : Set Y} {g : Y → Z}
    (h : TendstoUniformlyOn F f l K) (hC : IsCompact C) (hf : Set.MapsTo f K C)
    (hg : Continuous g) :
    TendstoUniformlyOn (fun n x ↦ g (F n x)) (fun x ↦ g (f x)) l K := by
  intro U hU
  have hV := hC.uniformContinuousAt_of_continuousAt g (fun _ _ ↦ hg.continuousAt) hU
  filter_upwards [h _ hV] with n hn x hx
  exact hn x hx (hf hx)

/-- The weighted integral of two spatially mollified L² trajectories converges to their weighted
pairing uniformly on compact subsets of the open time domain. -/
theorem tendstoLocallyUniformlyOn_weightedPairing_mollify
    (hρ : ∀ n, IsTestFunction (ρ n)) (hNonneg : ∀ n x, 0 ≤ ρ n x)
    (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) {J : Set ℝ} (hJ : IsOpen J)
    {a : ℝ² → ℂ} (ha : MemLp a ∞) {f g : ℝ → ℝ² → ℂ}
    (hf : ∀ t : J, MemLp (f t) 2) (hg : ∀ t : J, MemLp (g t) 2)
    (hf_cont : Continuous (fun t : J ↦ (hf t).toLp (f t)))
    (hg_cont : Continuous (fun t : J ↦ (hg t).toLp (g t))) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ ∫ x, starRingEnd ℂ (mollify (ρ n) (f t) x) *
        (a x * mollify (ρ n) (g t) x))
      (fun t ↦ ∫ x, starRingEnd ℂ (f t x) * (a x * g t x)) atTop J := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hJ).mpr
  intro K hKJ hK
  let K' : Set J := Subtype.val ⁻¹' K
  have hK' : IsCompact K' :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
      (fun t ht ↦ ⟨⟨t, hKJ ht⟩, rfl⟩)
  let F (t : J) := (hf t).toLp (f t)
  let G (t : J) := (hg t).toLp (g t)
  have hF : TendstoUniformlyOn (fun n t ↦ mollifyL2 (ρ n) (hρ n) (F t)) F atTop K' :=
    ((tendstoUniformlyOn_mollifyL2 hρ hNonneg hIntegral hSupport hr
      (hK'.image hf_cont)).comp F).mono (fun t ht ↦ ⟨t, ht, rfl⟩)
  have hG : TendstoUniformlyOn (fun n t ↦ mollifyL2 (ρ n) (hρ n) (G t)) G atTop K' :=
    ((tendstoUniformlyOn_mollifyL2 hρ hNonneg hIntegral hSupport hr
      (hK'.image hg_cont)).comp G).mono (fun t ht ↦ ⟨t, ht, rfl⟩)
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure ℝ²) ∞ 2 2 (ha.toLp a)
  let P (v : SpatialL2 × SpatialL2) := inner ℂ v.1 (M v.2)
  have hP : Continuous P := continuous_fst.inner (M.continuous.comp continuous_snd)
  have hFG : TendstoUniformlyOn
      (fun n t ↦ (mollifyL2 (ρ n) (hρ n) (F t), mollifyL2 (ρ n) (hρ n) (G t)))
      (fun t ↦ (F t, G t)) atTop K' := fun U hU ↦ ((hF.prodMk hG) U hU).diag_of_prod
  have hPaired := tendstoUniformlyOn_comp_continuous hFG
    (hK'.image (hf_cont.prodMk hg_cont)) (fun t ht ↦ ⟨t, ht, rfl⟩) hP
  have hPaired' : TendstoUniformlyOn
      (fun n (t : J) ↦ ∫ x, starRingEnd ℂ (mollify (ρ n) (f t) x) *
        (a x * mollify (ρ n) (g t) x))
      (fun (t : J) ↦ ∫ x, starRingEnd ℂ (f t x) * (a x * g t x)) atTop K' := by
    refine (hPaired.congr (.of_forall fun n t _ ↦ ?_)).congr_right (fun t _ ↦ ?_)
    · simp only [P, M, F, G, mollifyL2_toLp]
      exact weighted_pairing_eq_inner ha (memLp_mollify (hρ n) (hf t))
        (memLp_mollify (hρ n) (hg t))
    · exact weighted_pairing_eq_inner ha (hf t) (hg t)
  intro U hU
  filter_upwards [hPaired' U hU] with n hn t ht
  exact hn ⟨t, hKJ ht⟩ ht

private lemma real_weighted_self_pairing {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {f : ℝ² → ℂ} (hf : MemLp f 2) :
    (∫ x, starRingEnd ℂ (f x) * ((A x : ℂ) * f x)).re = ∫ x, A x * ‖f x‖ ^ 2 := by
  have hInt := integrable_weighted_pairing (testFunction_memLp_top_complex hA) hf hf
  refine (integral_re hInt).symm.trans (integral_congr_ae (.of_forall fun x ↦ ?_))
  change (starRingEnd ℂ (f x) * ((A x : ℂ) * f x)).re = A x * ‖f x‖ ^ 2
  rw [mul_left_comm, mul_comm (starRingEnd ℂ (f x)), Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.ofReal_re]

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- The localized variance of the mollified solution converges locally uniformly to (4.2). -/
theorem IsNLSSolution.tendstoLocallyUniformlyOn_localizedVariance_mollify
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    (hρ : ∀ n, IsTestFunction (ρ n)) (hNonneg : ∀ n x, 0 ≤ ρ n x)
    (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n t ↦ ∫ x, A x * ‖mollify (ρ n) (u t) x‖ ^ 2)
      (fun t ↦ ∫ x, A x * ‖u t x‖ ^ 2) atTop J := by
  have hu (t : J) := (h.h1 t t.property).memL2
  have hPair := tendstoLocallyUniformlyOn_weightedPairing_mollify
    hρ hNonneg hIntegral hSupport hr hJ (testFunction_memLp_top_complex hA)
    (f := u) (g := u) hu hu h.continuous_toLp h.continuous_toLp
  have hRe := Complex.uniformContinuous_re.comp_tendstoLocallyUniformlyOn hPair
  exact (hRe.congr (fun n t ht ↦ real_weighted_self_pairing hA
    (memLp_mollify (hρ n) (hu ⟨t, ht⟩)))).congr_right
      (fun t ht ↦ real_weighted_self_pairing hA (hu ⟨t, ht⟩))

private lemma virialFirstDeriv_eq_weighted_pairings {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {f : ℝ² → ℂ} {Df : Fin 2 → ℝ² → ℂ} (hf : MemLp f 2)
    (hDf : ∀ j, MemLp (Df j) 2) :
    2 * ((∫ x, starRingEnd ℂ (f x) * (((partialDeriv 0 A x : ℝ) : ℂ) * Df 0 x)) +
      (∫ x, starRingEnd ℂ (f x) * (((partialDeriv 1 A x : ℝ) : ℂ) * Df 1 x))).im =
      virialFirstDeriv A f Df := by
  let F (j : Fin 2) (x : ℝ²) := starRingEnd ℂ (f x) * (((partialDeriv j A x : ℝ) : ℂ) * Df j x)
  have hInt (j : Fin 2) : Integrable (F j) :=
    integrable_weighted_pairing (testFunction_memLp_top_complex (hA.partialDeriv j)) hf (hDf j)
  change 2 * ((∫ x, F 0 x) + (∫ x, F 1 x)).im = virialFirstDeriv A f Df
  have hIm : (∫ x, F 0 x + F 1 x).im = ∫ x, (F 0 x + F 1 x).im :=
    (integral_im ((hInt 0).add (hInt 1))).symm
  rw [← integral_add (hInt 0) (hInt 1), hIm]
  simp only [F, virialFirstDeriv, mul_add]

/-- The right side of (4.4) converges locally uniformly under spatial mollification of the
solution and its weak derivatives. -/
theorem IsNLSSolution.tendstoLocallyUniformlyOn_virialFirstDeriv_mollify
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    (hρ : ∀ n, IsTestFunction (ρ n)) (hNonneg : ∀ n x, 0 ≤ ρ n x)
    (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun n t ↦ virialFirstDeriv A (mollify (ρ n) (u t)) (fun j ↦ mollify (ρ n) (Du t j)))
      (fun t ↦ virialFirstDeriv A (u t) (Du t)) atTop J := by
  let P (j : Fin 2) (f g : ℝ² → ℂ) :=
    ∫ x, starRingEnd ℂ (f x) * (((partialDeriv j A x : ℝ) : ℂ) * g x)
  let M (n : ℕ) (t : ℝ) := mollify (ρ n) (u t)
  let D (n : ℕ) (t : ℝ) (j : Fin 2) := mollify (ρ n) (Du t j)
  let V (f : ℝ² → ℂ) (Df : Fin 2 → ℝ² → ℂ) := 2 * (P 0 f (Df 0) + P 1 f (Df 1)).im
  have hu (t : J) := (h.h1 t t.property).memL2
  have hDu (j : Fin 2) (t : J) := (h.h1 t t.property).memL2_partial j
  have hPair (j : Fin 2) : TendstoLocallyUniformlyOn
      (fun n t ↦ P j (M n t) (D n t j)) (fun t ↦ P j (u t) (Du t j)) atTop J :=
    tendstoLocallyUniformlyOn_weightedPairing_mollify
      hρ hNonneg hIntegral hSupport hr hJ (testFunction_memLp_top_complex (hA.partialDeriv j))
      (f := u) (g := fun t ↦ Du t j) hu (hDu j) h.continuous_toLp (h.continuous_grad_toLp j)
  have hIm := Complex.uniformContinuous_im.comp_tendstoLocallyUniformlyOn
    ((hPair 0).add (hPair 1))
  have hV : TendstoLocallyUniformlyOn (fun n t ↦ V (M n t) (D n t))
      (fun t ↦ V (u t) (Du t)) atTop J :=
    (Real.uniformContinuous_const_mul (x := 2)).comp_tendstoLocallyUniformlyOn hIm
  refine (hV.congr (fun n t ht ↦ ?_)).congr_right (fun t ht ↦ ?_)
  · exact virialFirstDeriv_eq_weighted_pairings (f := M n t) (Df := D n t) hA
      (memLp_mollify (hρ n) (hu ⟨t, ht⟩)) (fun j ↦ memLp_mollify (hρ n) (hDu j ⟨t, ht⟩))
  · exact virialFirstDeriv_eq_weighted_pairings hA (hu ⟨t, ht⟩) (fun j ↦ hDu j ⟨t, ht⟩)

/-- The forcing contribution to the mollified localized variance derivative converges locally
uniformly to zero. The unmollified nonlinear pairing is real pointwise. -/
theorem IsNLSSolution.tendstoLocallyUniformlyOn_mollified_nonlinear_virial
    (h : IsNLSSolution p J u Du) (hJ : IsOpen J) {A : ℝ² → ℝ} (hA : IsTestFunction A)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x))))
    (hρ : ∀ n, IsTestFunction (ρ n)) (hNonneg : ∀ n x, 0 ≤ ρ n x)
    (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun n t ↦ -2 * ∫ x, ((A x : ℂ) *
      starRingEnd ℂ (mollify (ρ n) (u t) x) *
      mollify (ρ n) (fun y ↦ nonlinearity p (u t y)) x).im) (fun _ ↦ 0) atTop J := by
  have hu (t : J) := (h.h1 t t.property).memL2
  have ha := testFunction_memLp_top_complex hA
  have hPair := tendstoLocallyUniformlyOn_weightedPairing_mollify
    hρ hNonneg hIntegral hSupport hr hJ ha
    (f := u) (g := fun t x ↦ nonlinearity p (u t x)) hu hN h.continuous_toLp hNc
  have hIm := Complex.uniformContinuous_im.comp_tendstoLocallyUniformlyOn hPair
  have hTwice := (Real.uniformContinuous_const_mul (x := -2)).comp_tendstoLocallyUniformlyOn hIm
  refine (hTwice.congr (fun n t ht ↦ ?_)).congr_right (fun t ht ↦ ?_)
  · let f := mollify (ρ n) (u t)
    let g := mollify (ρ n) (fun y ↦ nonlinearity p (u t y))
    let q (x : ℝ²) := starRingEnd ℂ (f x) * ((A x : ℂ) * g x)
    have hInt : Integrable q :=
      integrable_weighted_pairing ha (memLp_mollify (hρ n) (hu ⟨t, ht⟩))
        (memLp_mollify (hρ n) (hN ⟨t, ht⟩))
    have hImEq : (∫ x, q x).im = ∫ x, (q x).im := (integral_im hInt).symm
    change -2 * (∫ x, q x).im = -2 * ∫ x, ((A x : ℂ) * starRingEnd ℂ (f x) * g x).im
    rw [hImEq]
    congr 1
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    change (starRingEnd ℂ (f x) * ((A x : ℂ) * g x)).im =
      ((A x : ℂ) * starRingEnd ℂ (f x) * g x).im
    rw [mul_left_comm, ← mul_assoc]
  · let q (x : ℝ²) := starRingEnd ℂ (u t x) * ((A x : ℂ) * nonlinearity p (u t x))
    have hInt : Integrable q := integrable_weighted_pairing ha (hu ⟨t, ht⟩) (hN ⟨t, ht⟩)
    have hImEq : (∫ x, q x).im = ∫ x, (q x).im := (integral_im hInt).symm
    change -2 * (∫ x, q x).im = 0
    rw [hImEq]
    have hReal (x : ℝ²) : (q x).im = 0 := by
      unfold q
      rw [mul_left_comm, ← mul_assoc]
      exact im_weighted_nonlinearity_eq_zero (A x) p (u t x)
    simp only [hReal, integral_zero, mul_zero]

end Blowup
