import BlowupFormalization.MollifiedEquation
import BlowupFormalization.SolutionFacts

/-! # Time regularity of the spatially mollified NLS equation -/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

namespace Blowup

/-- Convolution evaluation is jointly continuous in time and space for an L²-continuous
family and a fixed compactly supported smooth kernel. -/
theorem continuousOn_mollify_of_continuous_toLp {J : Set ℝ} {f : ℝ → ℝ² → ℂ}
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) (hf : ∀ t : J, MemLp (f t) 2)
    (hfc : Continuous (fun t : J ↦ (hf t).toLp (f t))) :
    ContinuousOn (fun z : ℝ × ℝ² ↦ mollify ρ (f z.1) z.2) (J ×ˢ univ) := by
  let ρC (x : ℝ²) : ℂ := ρ x
  have hρC : MemLp ρC 2 :=
    (Complex.continuous_ofReal.comp hρ.1.continuous).memLp_of_hasCompactSupport
      (hρ.2.comp_left Complex.ofReal_zero)
  let translate (x : ℝ²) : C(ℝ², ℝ²) := ⟨fun y ↦ x - y, continuous_const.sub continuous_id⟩
  have hTranslate : Continuous translate :=
    ContinuousMap.continuous_of_continuous_uncurry translate (continuous_fst.sub continuous_snd)
  have hm (x : ℝ²) : MeasurePreserving (translate x) volume volume :=
    volume.measurePreserving_sub_left x
  let K (x : ℝ²) := Lp.compMeasurePreserving (translate x) (hm x) (hρC.toLp ρC)
  have hK : Continuous K := continuous_const.compMeasurePreservingLp hTranslate hm (by norm_num)
  rw [continuousOn_iff_continuous_domRestrict]
  let time (z : (J ×ˢ (univ : Set ℝ²))) : J := ⟨z.1.1, z.2.1⟩
  have hTime : Continuous time := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hSpace : Continuous (fun z : (J ×ˢ (univ : Set ℝ²)) ↦ z.1.2) :=
    continuous_snd.comp continuous_subtype_val
  apply ((hK.comp hSpace).inner (𝕜 := ℂ) (hfc.comp hTime)).congr
  intro z
  change _ = mollify ρ (f z.1.1) z.1.2
  rw [L2.inner_def, mollify_apply]
  apply integral_congr_ae
  let x := z.1.2
  let t := time z
  have hKernel : K x =ᵐ[volume] fun y ↦ (ρ (x - y) : ℂ) := by
    dsimp only [K]
    rw [Lp.toLp_compMeasurePreserving]
    exact MemLp.coeFn_toLp _
  filter_upwards [hKernel, (hf t).coeFn_toLp] with y hKy hfy
  change inner ℂ (K x y) ((hf t).toLp (f t) y) = (ρ (x - y) : ℂ) * f t y
  rw [RCLike.inner_apply', hKy, hfy, Complex.conj_ofReal]

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- The spatially mollified solution is jointly continuous on its time domain. -/
theorem IsNLSSolution.continuousOn_mollify (h : IsNLSSolution p J u Du)
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ) :
    ContinuousOn (fun z : ℝ × ℝ² ↦ mollify ρ (u z.1) z.2) (J ×ˢ univ) :=
  continuousOn_mollify_of_continuous_toLp (f := u) hρ (fun t ↦ (h.h1 t t.2).memL2)
    h.continuous_toLp

/-- The right-hand side of the spatially mollified equation is jointly continuous when the
nonlinearity is L²-continuous. -/
theorem IsNLSSolution.continuousOn_mollified_rhs (h : IsNLSSolution p J u Du)
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x)))) :
    ContinuousOn (fun z : ℝ × ℝ² ↦ Complex.I *
      (laplacian (mollify ρ (u z.1)) z.2 +
        mollify ρ (fun y ↦ nonlinearity p (u z.1 y)) z.2)) (J ×ˢ univ) := by
  have hLinear := h.continuousOn_mollify hρ.laplacian
  have hNonlinear := continuousOn_mollify_of_continuous_toLp
    (f := fun t x ↦ nonlinearity p (u t x)) hρ hN hNc
  have hI : ContinuousOn (fun _ : ℝ × ℝ² ↦ Complex.I) (J ×ˢ univ) := continuousOn_const
  apply (hI.mul (hLinear.add hNonlinear)).congr
  intro z hz
  change Complex.I * (laplacian (mollify ρ (u z.1)) z.2 + _) = _
  rw [laplacian_mollify_kernel hρ (h.h1 _ hz.1).memL2]
  rfl

private lemma hasDerivAt_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : Continuous g) (a t : ℝ) :
    HasDerivAt (fun s ↦ ∫ r in a..s, g r) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a t)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

-- A zero-mean test has a primitive supported in the same open interval.
private lemma exists_test_primitive {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo a b)
    (hf0 : ∫ s, f s = 0) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ deriv η = f := by
  let S := insert ((a + b) / 2) (tsupport f)
  have hS : IsCompact S := hfc.insert _
  have hSN : S.Nonempty := ⟨_, mem_insert _ _⟩
  have hSO : S ⊆ Ioo a b := insert_subset (by constructor <;> linarith) hfs
  obtain ⟨c, hc⟩ := hS.exists_isLeast hSN
  obtain ⟨d, hd⟩ := hS.exists_isGreatest hSN
  have hcd : c ≤ d := hd.2 hc.1
  have hac : a < c := (hSO hc.1).1
  have hdb : d < b := (hSO hd.1).2
  have hSupport : tsupport f ⊆ Icc c d :=
    fun s hs ↦ ⟨hc.2 (mem_insert_of_mem _ hs), hd.2 (mem_insert_of_mem _ hs)⟩
  let η (s : ℝ) := ∫ r in a..s, f r
  have hηD (s : ℝ) : HasDerivAt η (f s) s := hasDerivAt_primitive hf.continuous a s
  have hηderiv : deriv η = f := funext (fun s ↦ (hηD s).deriv)
  have hη0 (s : ℝ) (hs : s ∉ Icc c d) : η s = 0 := by
    by_cases hsc : s < c
    · calc
        η s = ∫ r in a..s, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro r hr
          have hrc : r < c := hr.2.trans_lt (max_lt hac hsc)
          exact image_eq_zero_of_notMem_tsupport (fun hmem ↦ hrc.not_ge (hSupport hmem).1)
        _ = 0 := by simp
    · have hds : d < s := lt_of_not_ge (fun hsd ↦ hs ⟨le_of_not_gt hsc, hsd⟩)
      have has : a ≤ s := hac.le.trans (hcd.trans hds.le)
      unfold η
      rw [intervalIntegral.integral_of_le has, setIntegral_eq_integral_of_forall_compl_eq_zero,
        hf0]
      intro r hr
      exact image_eq_zero_of_notMem_tsupport fun hmem ↦
        hr ⟨hac.trans_le (hSupport hmem).1, (hSupport hmem).2.trans hds.le⟩
  have hηS : tsupport η ⊆ Icc c d :=
    closure_minimal (fun s hs ↦ by
      by_contra h
      exact hs (hη0 s h)) isClosed_Icc
  refine ⟨η, contDiff_infty_iff_deriv.mpr ⟨fun s ↦ (hηD s).differentiableAt, ?_⟩,
    isCompact_Icc.of_isClosed_subset isClosed_closure hηS, ?_, hηderiv⟩
  · rw [hηderiv]
    exact hf
  · exact hηS.trans (fun s hs ↦ ⟨hac.trans_le hs.1, hs.2.trans_lt hdb⟩)

private lemma eqOn_const_of_weak_deriv_zero {a b : ℝ} (hab : a < b) {w : ℝ → ℂ}
    (hw : Continuous w)
    (hWeak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo a b →
      (∫ s, deriv η s • w s) = 0) :
    ∃ C : ℂ, EqOn w (fun _ ↦ C) (Ioo a b) := by
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := by constructor <;> dsimp [m] <;> linarith
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp isOpen_Ioo m hm
  let B : ContDiffBump m :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χ := B.normed (volume : Measure ℝ)
  have hχs : ContDiff ℝ ∞ χ := B.contDiff_normed
  have hχc : HasCompactSupport χ := B.hasCompactSupport_normed
  have hχSupp : tsupport χ ⊆ Ioo a b := by
    change tsupport (B.normed volume) ⊆ _
    rw [B.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [B]; linarith)).trans hBall
  let C := ∫ s, χ s • w s
  refine ⟨C, ?_⟩
  have hTests (ψ : ℝ → ℝ) (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψSupp : tsupport ψ ⊆ Ioo a b) :
      (∫ s, ψ s • (w s - C)) = 0 := by
    let k := ∫ s, ψ s
    let f (s : ℝ) := ψ s - k * χ s
    have hf : ContDiff ℝ ∞ f := hψs.sub (contDiff_const.mul hχs)
    have hfc : HasCompactSupport f := hψc.sub hχc.mul_left
    have hfs : tsupport f ⊆ Ioo a b := by
      refine (closure_minimal (t := tsupport ψ ∪ tsupport χ) ?_
        ((isClosed_tsupport _).union (isClosed_tsupport _))).trans (union_subset hψSupp hχSupp)
      intro s hs
      by_contra h
      have hψ0 := image_eq_zero_of_notMem_tsupport (fun hmem ↦ h (Or.inl hmem))
      have hχ0 := image_eq_zero_of_notMem_tsupport (fun hmem ↦ h (Or.inr hmem))
      exact hs (by simp only [f, hψ0, hχ0, mul_zero, sub_self])
    have hMean : (∫ s, f s) = 0 := by
      change (∫ s, ψ s - k * χ s) = 0
      rw [integral_sub (hψs.continuous.integrable_of_hasCompactSupport hψc)
        (B.integrable_normed.const_mul k), integral_const_mul]
      change k - k * (∫ s, B.normed volume s) = 0
      rw [B.integral_normed, mul_one, sub_self]
    obtain ⟨η, hηs, hηc, hηSupp, hηD⟩ := exists_test_primitive hab hf hfc hfs hMean
    have hψw : Integrable (fun s ↦ ψ s • w s) :=
      (hψs.continuous.smul hw).integrable_of_hasCompactSupport hψc.smul_right
    have hχw : Integrable (fun s ↦ χ s • w s) :=
      (hχs.continuous.smul hw).integrable_of_hasCompactSupport hχc.smul_right
    have hScaled : Integrable (fun s ↦ k • (χ s • w s)) := hχw.smul k
    have hψC : Integrable (fun s ↦ ψ s • C) :=
      (hψs.continuous.smul continuous_const).integrable_of_hasCompactSupport hψc.smul_right
    have hEq := hWeak η hηs hηc hηSupp
    rw [hηD] at hEq
    simp only [f, sub_smul, mul_smul, integral_sub hψw hScaled, integral_smul] at hEq
    simpa only [smul_sub, integral_sub hψw hψC, integral_smul_const, C, k] using hEq
  have hAE := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hw.sub continuous_const).locallyIntegrable.locallyIntegrableOn (s := Ioo a b)) hTests
  have hAE' : w =ᵐ[(volume : Measure ℝ).restrict (Ioo a b)] fun _ ↦ C :=
    (ae_restrict_iff' measurableSet_Ioo).2 (hAE.mono fun s hs hmem ↦ sub_eq_zero.mp (hs hmem))
  exact Measure.eqOn_open_of_ae_eq hAE' isOpen_Ioo hw.continuousOn continuousOn_const

-- Subtract a primitive of the prescribed derivative and apply the zero-derivative lemma.
private lemma hasDerivAt_of_weak_equation {J : Set ℝ} (hJ : IsOpen J) {f g : ℝ → ℂ}
    (hf : ContinuousOn f J) (hg : ContinuousOn g J)
    (hWeak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ J →
      (∫ s, deriv η s • f s + η s • g s) = 0)
    {t : ℝ} (ht : t ∈ J) : HasDerivAt f (g t) t := by
  obtain ⟨a, b, htcc, hNhd, hSub⟩ := exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds ht)
  have htoo : t ∈ Ioo a b := by
    rw [← interior_Icc]
    exact mem_interior_iff_mem_nhds.mpr hNhd
  let clip (s : ℝ) := min b (max a s)
  have hClipCont : Continuous clip := continuous_const.min (continuous_const.max continuous_id')
  have hClipMem (s : ℝ) : clip s ∈ Icc a b :=
    ⟨le_min (htcc.1.trans htcc.2) (le_max_left _ _), min_le_left _ _⟩
  have hClipEq (s : ℝ) (hs : s ∈ Icc a b) : clip s = s := by
    simp only [clip, max_eq_right hs.1, min_eq_right hs.2]
  let F := f ∘ clip
  let G := g ∘ clip
  have hF : Continuous F := (hf.mono hSub).comp_continuous hClipCont hClipMem
  have hG : Continuous G := (hg.mono hSub).comp_continuous hClipCont hClipMem
  have hFeq (s : ℝ) (hs : s ∈ Icc a b) : F s = f s := congrArg f (hClipEq s hs)
  have hGeq (s : ℝ) (hs : s ∈ Icc a b) : G s = g s := congrArg g (hClipEq s hs)
  let P (s : ℝ) := ∫ r in a..s, G r
  have hP (s : ℝ) : HasDerivAt P (G s) s := hasDerivAt_primitive hG a s
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun s ↦ (hP s).continuousAt
  have hPderiv : deriv P = G := funext fun s ↦ (hP s).deriv
  let W := F - P
  have hStep (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηSupp : tsupport η ⊆ Ioo a b) : (∫ s, deriv η s • W s) = 0 := by
    have hEq : (∫ s, deriv η s • F s + η s • G s) = 0 := by
      refine (integral_congr_ae (.of_forall fun s ↦ ?_)).trans
        (hWeak η hηs hηc (hηSupp.trans (Ioo_subset_Icc_self.trans hSub)))
      by_cases hs : s ∈ Icc a b
      · rw [hFeq s hs, hGeq s hs]
      · have hns : s ∉ tsupport η := fun hmem ↦ hs (Ioo_subset_Icc_self (hηSupp hmem))
        simp only [deriv_of_notMem_tsupport hns, image_eq_zero_of_notMem_tsupport hns, zero_smul,
          add_zero]
    have hη' := hηs.continuous_deriv (by simp)
    have hDF : Integrable (fun s ↦ deriv η s • F s) :=
      (hη'.smul hF).integrable_of_hasCompactSupport hηc.deriv.smul_right
    have hDP : Integrable (fun s ↦ deriv η s • P s) :=
      (hη'.smul hPc).integrable_of_hasCompactSupport hηc.deriv.smul_right
    have hηG : Integrable (fun s ↦ η s • G s) :=
      (hηs.continuous.smul hG).integrable_of_hasCompactSupport hηc.smul_right
    have hηP : Integrable (fun s ↦ η s • P s) :=
      (hηs.continuous.smul hPc).integrable_of_hasCompactSupport hηc.smul_right
    have hParts : (∫ s, η s • G s) = -(∫ s, deriv η s • P s) := by
      simpa only [fderiv_apply_one_eq_deriv, hPderiv] using
        integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (v := (1 : ℝ))
          (by simpa only [fderiv_apply_one_eq_deriv] using hDP)
          (by simpa only [fderiv_apply_one_eq_deriv, hPderiv] using hηG) hηP
          (fun s _ ↦ hηs.differentiable (by simp) s) (fun s _ ↦ (hP s).differentiableAt)
    rw [integral_add hDF hηG, hParts] at hEq
    change (∫ s, deriv η s • (F s - P s)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hDF hDP, sub_eq_add_neg]
    exact hEq
  obtain ⟨C, hC⟩ := eqOn_const_of_weak_deriv_zero (htoo.1.trans htoo.2) (hF.sub hPc) hStep
  have hNear : f =ᶠ[𝓝 t] fun s ↦ P s + C := by
    filter_upwards [isOpen_Ioo.mem_nhds htoo] with s hs
    have heq := hC hs
    change F s - P s = C at heq
    rw [hFeq s (Ioo_subset_Icc_self hs)] at heq
    exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
  rw [← hGeq t htcc]
  exact ((hP t).add_const C).congr_of_eventuallyEq hNear

private lemma weak_equation_mul_I {F A : ℝ → ℂ} {η : ℝ → ℝ}
    (hZero : (∫ s, F s * (-Complex.I * ((deriv η s : ℝ) : ℂ)) + A s * (η s : ℂ)) = 0) :
    (∫ s, deriv η s • F s + η s • (Complex.I * A s)) = 0 := by
  have hI : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  calc
    (∫ s, deriv η s • F s + η s • (Complex.I * A s)) =
        ∫ s, Complex.I * (F s * (-Complex.I * ((deriv η s : ℝ) : ℂ)) + A s * (η s : ℂ)) := by
      apply integral_congr_ae (.of_forall fun s ↦ ?_)
      rw [show Complex.I * (F s * (-Complex.I * ((deriv η s : ℝ) : ℂ)) + A s * (η s : ℂ)) =
        (Complex.I * -Complex.I) * (((deriv η s : ℝ) : ℂ) * F s) +
          (η s : ℂ) * (Complex.I * A s) by ring]
      simp only [hI, one_mul, Complex.real_smul]
    _ = 0 := by rw [integral_const_mul, hZero, mul_zero]

private lemma continuousOn_time_slice {J : Set ℝ} {F : ℝ × ℝ² → ℂ}
    (hF : ContinuousOn F (J ×ˢ univ)) (x : ℝ²) :
    ContinuousOn (fun s : ℝ ↦ F (s, x)) J := by
  let slice (s : ℝ) := (s, x)
  have hSlice : Continuous slice := continuous_id.prodMk continuous_const
  have hMaps : MapsTo slice J (J ×ˢ univ) := fun _ hs ↦ ⟨hs, mem_univ _⟩
  exact hF.comp hSlice.continuousOn hMaps

/-- The mollified weak equation yields a classical time derivative at each interior point
when the nonlinearity is L²-continuous. -/
theorem IsNLSSolution.hasDerivAt_mollify (h : IsNLSSolution p J u Du) (hJ : IsOpen J)
    {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hN : ∀ t : J, MemLp (fun x ↦ nonlinearity p (u t x)) 2)
    (hNc : Continuous (fun t : J ↦ (hN t).toLp (fun x ↦ nonlinearity p (u t x))))
    {t : ℝ} (ht : t ∈ J) (x : ℝ²) :
    HasDerivAt (fun s ↦ mollify ρ (u s) x) (Complex.I *
      (laplacian (mollify ρ (u t)) x + mollify ρ (fun y ↦ nonlinearity p (u t y)) x)) t := by
  let F (s : ℝ) := mollify ρ (u s) x
  let A (s : ℝ) := laplacian (mollify ρ (u s)) x + mollify ρ (fun y ↦ nonlinearity p (u s y)) x
  let G (s : ℝ) := Complex.I * A s
  have hF := continuousOn_time_slice (h.continuousOn_mollify hρ) x
  have hG := continuousOn_time_slice (h.continuousOn_mollified_rhs hρ hN hNc) x
  change HasDerivAt F (G t) t
  refine hasDerivAt_of_weak_equation (f := F) (g := G) hJ hF hG ?_ ht
  intro η hηs hηc hηSupp
  have hSupp : tsupport η ⊆ interior J := by rwa [hJ.interior_eq]
  exact weak_equation_mul_I (F := F) (A := A) (η := η)
    (h.weak_equation_mollify hρ x (η := η) hηs hηc hSupp).2

end Blowup
