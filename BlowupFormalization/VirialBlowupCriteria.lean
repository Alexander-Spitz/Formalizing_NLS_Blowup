import BlowupFormalization.CubicVirial
import BlowupFormalization.ExteriorEstimate
import BlowupFormalization.GagliardoNirenberg
import BlowupFormalization.MassConservation
import BlowupFormalization.RadialTail
import BlowupFormalization.ScaleSelection
import BlowupFormalization.Section5

/-! # Virial blow-up criteria for weak solutions -/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Blowup

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- The nonlinear density integrated over any fixed measurable region is continuous in time. -/
theorem IsNLSSolution.continuousOn_setIntegral_potential
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) {S : Set ℝ²} (hS : MeasurableSet S) :
    ContinuousOn (fun t ↦ ∫ x in S, ‖u t x‖ ^ (p + 1)) J := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a : ℝ² → ℂ := S.indicator (fun _ ↦ 1)
  have ha : MemLp a ∞ := memLp_top_of_bound
    (measurable_const.indicator hS).aestronglyMeasurable 1 (.of_forall fun x ↦ by
      by_cases hx : x ∈ S <;> simp [a, hx])
  have hU (t : J) := (h.h1 t t.property).memL2
  have hN (t : J) := (h.h1 t t.property).memLp_nonlinearity hp
  have hPair := continuous_weighted_pairing ha
    (f := fun t : J ↦ u t) (g := fun (t : J) x ↦ nonlinearity p (u t x))
    hU hN h.continuous_toLp (h.continuous_nonlinearity_toLp hp)
  apply (Complex.continuous_re.comp hPair).congr
  intro t
  change (∫ x, starRingEnd ℂ (u t x) * (a x * nonlinearity p (u t x))).re =
    ∫ x in S, ‖u t x‖ ^ (p + 1)
  have hRe := integral_re (integrable_weighted_pairing ha (hU t) (hN t))
  simp only [RCLike.re_eq_complex_re] at hRe
  rw [← hRe]
  rw [← integral_indicator hS]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change (starRingEnd ℂ (u t x) * (a x * nonlinearity p (u t x))).re =
    S.indicator (fun x ↦ ‖u t x‖ ^ (p + 1)) x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, show a x = 1 from indicator_of_mem hx _]
    simpa only [Complex.ofReal_one, one_mul] using re_weighted_nonlinearity hp 1 (u t x)
  · simp [a, hx]

private theorem tendsto_setIntegral_norm_gt_zero {f : ℝ² → ℝ}
    (hf : Integrable f) (h₀ : ∀ x, 0 ≤ f x) :
    Tendsto (fun n : ℕ ↦ ∫ x in {x : ℝ² | (n : ℝ) < ‖x‖}, f x) atTop (𝓝 0) := by
  let S (n : ℕ) := {x : ℝ² | (n : ℝ) < ‖x‖}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hInd : Tendsto (fun n ↦ ∫ x, (S n).indicator f x) atTop (𝓝 (∫ _ : ℝ², (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence f
    · exact .of_forall fun n ↦ (hf.indicator (hS n)).aestronglyMeasurable
    · refine .of_forall fun n ↦ .of_forall fun x ↦ ?_
      by_cases hx : x ∈ S n <;> simp [hx, Real.norm_of_nonneg (h₀ x), h₀ x]
    · exact hf
    · refine .of_forall fun x ↦ tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNot : x ∉ S n := fun hx ↦
        (not_lt_of_ge (hN.le.trans (Nat.cast_le.mpr hn))) hx
      exact (indicator_of_notMem hNot f).symm
  simpa only [integral_indicator (hS _), integral_zero, S] using hInd

/-- On a compact portion of the time domain, the exterior nonlinear mass tends uniformly
to zero as the radius tends to infinity. -/
theorem IsNLSSolution.tendstoUniformlyOn_exterior_potential
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) {K : Set ℝ}
    (hK : IsCompact K) (hKJ : K ⊆ J) :
    TendstoUniformlyOn (fun n : ℕ ↦ fun t ↦ ∫ x in {x : ℝ² | (n : ℝ) < ‖x‖},
      ‖u t x‖ ^ (p + 1)) (fun _ ↦ 0) atTop K := by
  have hS (n : ℕ) : MeasurableSet {x : ℝ² | (n : ℝ) < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  refine Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun n ↦ (h.continuousOn_setIntegral_potential hp (hS n)).mono hKJ) ?_
    continuousOn_const (fun t ht ↦ tendsto_setIntegral_norm_gt_zero
      ((h.h1 t (hKJ ht)).integrable_nonlinear_density hp) (fun _ ↦ by positivity))
  intro t ht m n hmn
  refine setIntegral_mono_set ((h.h1 t (hKJ ht)).integrable_nonlinear_density hp).integrableOn
    (.of_forall fun _ ↦ by positivity) (.of_forall fun x hx ↦ ?_)
  exact (Nat.cast_le.mpr hmn).trans_lt (show (n : ℝ) < ‖x‖ from hx)

private theorem gradNormSq_nonneg (D : Fin 2 → ℝ² → ℂ) : 0 ≤ gradNormSq D :=
  integral_nonneg (fun _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem variance_le_quadratic (h : IsNLSSolution p J u Du) (hp : 3 ≤ p)
    {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {T a : ℝ} (hT : 0 ≤ T) (hTime : Icc 0 T ⊆ interior J)
    (hAcc : ∀ t ∈ Icc 0 T, virialSecondDeriv p A (u t) (Du t) ≤ -2 * a) :
    (∫ x, A x * ‖u T x‖ ^ 2) ≤
      (∫ x, A x * ‖u 0 x‖ ^ 2) + T * |virialFirstDeriv A (u 0) (Du 0)| - a * T ^ 2 := by
  let V (s : ℝ) := ∫ x, A x * ‖u s x‖ ^ 2
  let C (s : ℝ) := virialFirstDeriv A (u s) (Du s)
  let B (s : ℝ) := virialSecondDeriv p A (u s) (Du s)
  have hV (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivAt V (C s) s :=
    h.hasDerivAt_localizedVariance hp hA (hTime hs)
  have hC (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivAt C (B s) s :=
    h.hasDerivAt_virialFirstDeriv hp hA (hTime hs)
  have hQuadratic (s : ℝ) : HasDerivAt (fun t ↦ a * t ^ 2) (2 * a * s) s := by
    convert ((hasDerivAt_id' s).pow 2).const_mul a using 1
    ring
  have hLinear (s : ℝ) : HasDerivAt (fun t ↦ 2 * a * t) (2 * a) s := by
    simpa only [mul_one] using (hasDerivAt_id' s).const_mul (2 * a)
  have hW (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt (fun t ↦ V t + a * t ^ 2) (C s + 2 * a * s) (Icc 0 T) s :=
    ((hV s hs).add (hQuadratic s)).hasDerivWithinAt
  have hW' (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivWithinAt (fun t ↦ C t + 2 * a * t) (B s + 2 * a) (Icc 0 T) s :=
    ((hC s hs).add (hLinear s)).hasDerivWithinAt
  have hBound := le_tangent_of_second_deriv_nonpos hT hW hW' (fun s hs ↦ by
    have hab : B s ≤ -2 * a := hAcc s hs
    linarith)
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] at hBound
  change V T ≤ V 0 + T * |C 0| - a * T ^ 2
  linarith only [hBound, mul_le_mul_of_nonneg_left (le_abs_self (C 0)) hT]

private theorem exists_time_quadratic_dominates {a b c : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) :
    ∃ T : ℝ, 0 < T ∧ b + T * c < a * T ^ 2 := by
  let T := max 1 ((b + c + 1) / a)
  have hT : 1 ≤ T := le_max_left _ _
  have hBig : b + c + 1 ≤ a * T := by
    simpa only [mul_comm a] using (div_le_iff₀ ha).mp (le_max_right 1 ((b + c + 1) / a))
  refine ⟨T, by linarith, ?_⟩
  calc
    b + T * c ≤ T * (b + c) := by nlinarith only [mul_nonneg hb (sub_nonneg.mpr hT)]
    _ < T * (a * T) := mul_lt_mul_of_pos_left (by linarith) (by linarith)
    _ = _ := by ring

private theorem exists_radius_mass_error_small {D M e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, D * M / (n : ℝ) < e :=
  (tendsto_const_div_atTop_nhds_zero_nat (D * M)).eventually_lt_const he

private theorem mass_error_le {D M Q : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hQ : 1 ≤ Q)
    {m : ℝ} (hm : m ≤ M) :
    D * m / Q ^ 2 ≤ D * M / Q := by
  have hQ' : 0 < Q := by linarith
  calc
    _ ≤ D * M / Q ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hD) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hD hM) hQ' (by nlinarith)

private theorem acceleration_of_error_bounds {p e V E K P M : ℝ}
    (hp : 3 ≤ p) (he : 0 < e) (hEnergy : E ≤ -e)
    (hVir : V ≤ 8 * (p - 1) * E - 4 * (p - 3) * K + P + M)
    (hTail : P ≤ e + 2 * (p - 3) * K) (hMass : M ≤ e) :
    V ≤ -4 * (p - 1) * e - 2 * (p - 3) * K := by
  have hE := mul_le_mul_of_nonneg_left hEnergy (show 0 ≤ 8 * (p - 1) by linarith)
  have hE' : 2 * e ≤ 4 * (p - 1) * e := mul_le_mul_of_nonneg_right (by linarith) he.le
  calc
    _ ≤ 8 * (p - 1) * (-e) - 4 * (p - 3) * K + (e + 2 * (p - 3) * K) + e :=
      hVir.trans (add_le_add (add_le_add (sub_le_sub_right hE _) hTail) hMass)
    _ = (-8 * (p - 1) * e - 2 * (p - 3) * K) + 2 * e := by ring
    _ ≤ _ := by nlinarith only [hE']

/-- A weak solution with finite initial variance and energy uniformly bounded away from
zero on the negative side cannot exist for all forward times. -/
theorem IsNLSSolution.false_of_finite_initial_variance
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) (hTime : Ici (0 : ℝ) ⊆ interior J)
    {e : ℝ} (he : 0 < e)
    (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e)
    (hVar : Integrable (fun x ↦ ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2)) : False := by
  obtain ⟨C, D, hC, hD, hBound⟩ := virialSecondDeriv_virialWeight_le
  let M := mass (u 0)
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hMass (t : ℝ) (ht : 0 ≤ t) : mass (u t) ≤ M :=
    (h.mass_eq hp ht (fun _ hs ↦ hTime hs.1)).le
  let B := ∫ x, ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2
  let c := 4 * Real.sqrt (gradNormSq (Du 0)) * Real.sqrt B
  let a := 2 * (p - 1) * e
  let L := (2 * (p - 1) / (p + 1)) * C
  have hB : 0 ≤ B := integral_nonneg (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have ha : 0 < a := mul_pos (mul_pos two_pos (by linarith)) he
  have hL : 0 ≤ L := mul_nonneg (div_nonneg (by linarith) (by linarith)) hC
  obtain ⟨T, hT, hLarge⟩ := exists_time_quadratic_dominates (c := c) ha hB
  have hSegment : Icc 0 T ⊆ interior J := fun _ ht ↦ hTime ht.1
  have hUniform := h.tendstoUniformlyOn_exterior_potential hp isCompact_Icc
    (hSegment.trans interior_subset)
  have hε : 0 < e / (L + 1) := div_pos he (by linarith)
  have hTails := Metric.tendstoUniformlyOn_iff.mp hUniform _ hε
  have hSmall := exists_radius_mass_error_small (D := D) (M := M) he
  obtain ⟨n, hn, hErr, hTail⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hSmall.and hTails)).exists
  let Q : ℝ := n
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hn
  have hQ' : 0 < Q := by linarith
  have hAcc (t : ℝ) (ht : t ∈ Icc 0 T) :
      virialSecondDeriv p (virialWeight Q) (u t) (Du t) ≤ -2 * a := by
    have hData := h.h1 t (interior_subset (hSegment ht))
    have hVir := hBound hp hQ' hData.memL2 hData.memL2_partial
      (hData.integrable_nonlinear_density hp)
    have hTailPos : 0 ≤ ∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1) :=
      integral_nonneg (fun _ ↦ by positivity)
    have hTailAt := hTail t ht
    rw [dist_comm, Real.dist_eq, sub_zero] at hTailAt
    have hTailLt : (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1)) < e / (L + 1) :=
      (le_abs_self _).trans_lt hTailAt
    have hWeighted : L * (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤ e := by
      have hProd := (le_div_iff₀ (by linarith : 0 < L + 1)).mp hTailLt.le
      nlinarith only [hProd, hTailPos]
    have hMassErr := (mass_error_le hD hM hQ (hMass t ht.1)).trans hErr.le
    have hK := mul_nonneg (show 0 ≤ 2 * (p - 3) by linarith) (gradNormSq_nonneg (Du t))
    have hTailErr := hWeighted.trans (le_add_of_nonneg_right hK)
    have hTotal := acceleration_of_error_bounds hp he (hEnergy t ht.1) hVir hTailErr hMassErr
    exact hTotal.trans (by dsimp [a]; nlinarith only [hK])
  have hu₀ := h.h1 0 (interior_subset (hTime (mem_Ici.mpr le_rfl)))
  have hV0 : (∫ x, virialWeight Q x * ‖u 0 x‖ ^ 2) ≤ B := by
    have hA := virialWeight_isTestFunction hQ'
    have hIntegrable : Integrable (fun x ↦ virialWeight Q x * ‖u 0 x‖ ^ 2) :=
      hu₀.memL2.norm.integrable_sq.mul_of_top_right
        (hA.1.continuous.memLp_of_hasCompactSupport hA.2)
    exact integral_mono hIntegrable hVar
      (fun x ↦ mul_le_mul_of_nonneg_right (virialWeight_le_sq hQ' x) (sq_nonneg _))
  have hC0 : |virialFirstDeriv (virialWeight Q) (u 0) (Du 0)| ≤ c :=
    (eq_4_7_deriv hu₀ hQ').trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV0) (by positivity))
  have hV := variance_le_quadratic h hp (virialWeight_isTestFunction hQ') hT.le hSegment hAcc
  have hNonneg : 0 ≤ ∫ x, virialWeight Q x * ‖u T x‖ ^ 2 :=
    integral_nonneg (fun x ↦ mul_nonneg (virialWeight_nonneg Q x) (sq_nonneg _))
  linarith only [hNonneg, hV, hV0, mul_le_mul_of_nonneg_left hC0 hT.le, hLarge]

/-- A global weak solution with uniformly negative energy is impossible when its
exterior potential is bounded by a decaying coefficient times one plus the kinetic term. -/
theorem IsNLSSolution.false_of_exterior_potential_bound
    (h : IsNLSSolution p J u Du) (hp : 3 < p) (hTime : Ici (0 : ℝ) ⊆ interior J)
    {e L : ℝ} (he : 0 < e)
    (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e)
    (hTail : ∀ t ≥ 0, ∀ Q ≥ 1,
      (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤
        (L / Q) * (1 + gradNormSq (Du t))) : False := by
  obtain ⟨C, D, hC, hD, hBound⟩ := virialSecondDeriv_virialWeight_le
  let M := mass (u 0)
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hMass (t : ℝ) (ht : 0 ≤ t) : mass (u t) ≤ M :=
    (h.mass_eq hp.le ht (fun _ hs ↦ hTime hs.1)).le
  let a := 2 * (p - 1) * e
  let c := (2 * (p - 1) / (p + 1)) * C
  have hc : 0 ≤ c := mul_nonneg (div_nonneg (by linarith) (by linarith)) hC
  have ha : 0 < a := mul_pos (mul_pos two_pos (by linarith)) he
  have hε : 0 < min e (2 * (p - 3)) := lt_min he (by linarith)
  have hExteriorSmall : ∀ᶠ n : ℕ in atTop, c * L / (n : ℝ) < min e (2 * (p - 3)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (c * L)).eventually_lt_const hε
  obtain ⟨n, hn, hErr, hExt⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and
      ((exists_radius_mass_error_small (D := D) (M := M) he).and hExteriorSmall)).exists
  let Q : ℝ := n
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast hn
  have hQ' : 0 < Q := by linarith
  have hAcc (t : ℝ) (ht : 0 ≤ t) :
      virialSecondDeriv p (virialWeight Q) (u t) (Du t) ≤ -2 * a := by
    have hData := h.h1 t (interior_subset (hTime ht))
    have hVir := hBound hp.le hQ' hData.memL2 hData.memL2_partial
      (hData.integrable_nonlinear_density hp.le)
    have hK := gradNormSq_nonneg (Du t)
    have hExt₁ := hExt.le.trans (min_le_left _ _)
    have hExt₂ := hExt.le.trans (min_le_right _ _)
    have hWeighted := mul_le_mul_of_nonneg_left (hTail t ht Q hQ) hc
    have hAbsorb : c * ((L / Q) * (1 + gradNormSq (Du t))) ≤
        e + 2 * (p - 3) * gradNormSq (Du t) := by
      rw [← mul_assoc, ← mul_div_assoc, mul_add, mul_one]
      exact add_le_add hExt₁ (mul_le_mul_of_nonneg_right hExt₂ hK)
    have hMassErr := (mass_error_le hD hM hQ (hMass t ht)).trans hErr.le
    have hLoss := mul_nonneg (show 0 ≤ 2 * (p - 3) by linarith) hK
    have hTailErr := hWeighted.trans hAbsorb
    have hTotal := acceleration_of_error_bounds hp.le he (hEnergy t ht) hVir hTailErr hMassErr
    exact hTotal.trans (by dsimp [a]; nlinarith only [hLoss])
  let B := ∫ x, virialWeight Q x * ‖u 0 x‖ ^ 2
  let b := |virialFirstDeriv (virialWeight Q) (u 0) (Du 0)|
  have hB : 0 ≤ B := integral_nonneg (fun x ↦ mul_nonneg (virialWeight_nonneg Q x) (sq_nonneg _))
  obtain ⟨T, hT, hLarge⟩ := exists_time_quadratic_dominates (c := b) ha hB
  have hV := variance_le_quadratic h hp.le (virialWeight_isTestFunction hQ') hT.le
    (fun _ ht ↦ hTime ht.1)
    (fun t ht ↦ hAcc t ht.1)
  have hNonneg : 0 ≤ ∫ x, virialWeight Q x * ‖u T x‖ ^ 2 :=
    integral_nonneg (fun x ↦ mul_nonneg (virialWeight_nonneg Q x) (sq_nonneg _))
  change B + T * b < a * T ^ 2 at hLarge
  change (∫ x, virialWeight Q x * ‖u T x‖ ^ 2) ≤ B + T * b - a * T ^ 2 at hV
  linarith only [hV, hNonneg, hLarge]

/-- For 3 < p ≤ 5, a radial weak solution whose energy stays uniformly negative
cannot exist at all forward times. -/
theorem IsNLSSolution.false_of_radial_forward
    (h : IsNLSSolution p J u Du) (hp : 3 < p) (hp₅ : p ≤ 5)
    (hTime : Ici (0 : ℝ) ⊆ interior J) {e : ℝ} (he : 0 < e)
    (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e)
    (hRadial : ∀ t ≥ 0, IsRadialAE (u t)) : False := by
  let M := mass (u 0)
  let β := (p - 1) / 2
  let A := radialTailConstant * Real.sqrt M
  let L := M * A ^ β
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hA : 0 ≤ A := mul_nonneg radialTailConstant_nonneg (Real.sqrt_nonneg _)
  have hL : 0 ≤ L := mul_nonneg hM (Real.rpow_nonneg hA _)
  have hβ : 1 ≤ β := by dsimp [β]; linarith
  refine h.false_of_exterior_potential_bound hp hTime (L := L) he hEnergy ?_
  intro t ht Q hQ
  let K := gradNormSq (Du t)
  have hK : 0 ≤ K := gradNormSq_nonneg _
  have hQ' : 0 < Q := by linarith
  have hMass : mass (u t) = M := h.mass_eq hp.le ht (fun _ hs ↦ hTime hs.1)
  have hData := h.h1 t (interior_subset (hTime ht))
  have hTail := hData.radial_exterior_integral_le (hRadial t ht) hp.le hQ'
  rw [hMass] at hTail
  have hSqrt : (Real.sqrt K) ^ β = K ^ ((p - 1) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hK]
    congr 1
    dsimp [β]
    ring
  have hPow : K ^ ((p - 1) / 4) ≤ 1 + K := by
    by_cases hSmall : K ≤ 1
    · exact (Real.rpow_le_one hK hSmall (by linarith)).trans (le_add_of_nonneg_right hK)
    · have hLarge := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hSmall)
        (show (p - 1) / 4 ≤ 1 by linarith)
      exact (by simpa only [Real.rpow_one] using hLarge : K ^ ((p - 1) / 4) ≤ K).trans
        (le_add_of_nonneg_left zero_le_one)
  have hQβ : Q ≤ Q ^ β := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ hβ
  have hDiv : K ^ ((p - 1) / 4) / Q ^ β ≤ (1 + K) / Q :=
    (div_le_div_of_nonneg_right hPow (Real.rpow_nonneg hQ'.le _)).trans
      (div_le_div_of_nonneg_left (by positivity) hQ' hQβ)
  calc
    _ ≤ M * (A * Real.sqrt K / Q) ^ β := hTail
    _ = L * (K ^ ((p - 1) / 4) / Q ^ β) := by
      rw [Real.div_rpow (mul_nonneg hA (Real.sqrt_nonneg _)) hQ'.le,
        Real.mul_rpow hA (Real.sqrt_nonneg _), hSqrt]
      dsimp only [L]
      ring
    _ ≤ L * ((1 + K) / Q) := mul_le_mul_of_nonneg_left hDiv hL
    _ = _ := by change _ = L / Q * (1 + K); ring

/-- A cubic weak solution that stays radial and has uniformly negative energy
cannot exist at all forward times, even if its initial variance is infinite. -/
theorem IsNLSSolution.false_of_radial_cubic_forward
    (h : IsNLSSolution 3 J u Du) (hTime : Ici (0 : ℝ) ⊆ interior J)
    {e : ℝ} (he : 0 < e) (hEnergy : ∀ t ≥ 0, energy 3 (u t) (Du t) ≤ -e)
    (hRadial : ∀ t ≥ 0, IsRadialAE (u t)) : False := by
  obtain ⟨C, D, hC, hD, hBound⟩ := virialSecondDeriv_cubicVirialWeight_le
  let M := mass (u 0)
  let E := C * M ^ 3 + D * M
  let R := max 1 (E / (8 * e))
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hR : 1 ≤ R := le_max_left _ _
  have hR' : 0 < R := zero_lt_one.trans_le hR
  have hRadius : E / (8 * e) ≤ R := le_max_right _ _
  have hScale : E / R ^ 2 ≤ 8 * e := by
    calc
      _ ≤ E / R := div_le_div_of_nonneg_left hE hR' (by nlinarith)
      _ ≤ _ := (div_le_iff₀ hR').mpr (by
        simpa only [mul_comm (8 * e)] using
          (div_le_iff₀ (by positivity : 0 < 8 * e)).mp hRadius)
  let A := cubicVirialWeight R
  let V (s : ℝ) := ∫ x, A x * ‖u s x‖ ^ 2
  have hA : IsTestFunction A := cubicVirialWeight_isTestFunction hR'
  obtain ⟨L, hL⟩ := cubicVirialWeight_bddBelow hR'
  have hMass (t : ℝ) (ht : 0 ≤ t) : mass (u t) = M :=
    h.mass_eq le_rfl ht (fun _ hs ↦ hTime hs.1)
  have hLow (t : ℝ) (ht : 0 ≤ t) : L * M ≤ V t := by
    have hData := (h.h1 t (interior_subset (hTime ht))).memL2.norm.integrable_sq
    have hInt : Integrable (fun x ↦ A x * ‖u t x‖ ^ 2) :=
      hData.mul_of_top_right (hA.1.continuous.memLp_top_of_hasCompactSupport hA.2 _)
    rw [← hMass t ht, mass, ← integral_const_mul]
    exact integral_mono (hData.const_mul L) hInt
      (fun x ↦ mul_le_mul_of_nonneg_right (hL x) (sq_nonneg _))
  let a := 4 * e
  let b := |V 0| + |L| * M
  let c := |virialFirstDeriv A (u 0) (Du 0)|
  obtain ⟨T, hT, hLarge⟩ := exists_time_quadratic_dominates (c := c)
    (show 0 < a by dsimp [a]; positivity) (show 0 ≤ b by dsimp [b]; positivity)
  have hAcc (t : ℝ) (ht : t ∈ Icc 0 T) :
      virialSecondDeriv 3 A (u t) (Du t) ≤ -2 * a := by
    have hData := h.h1 t (interior_subset (hTime ht.1))
    have hVir := hBound hR' hData (hRadial t ht.1)
    rw [hMass t ht.1] at hVir
    change virialSecondDeriv 3 A (u t) (Du t) ≤ 16 * energy 3 (u t) (Du t) + E / R ^ 2 at hVir
    dsimp only [a]
    linarith only [hVir, hScale, hEnergy t ht.1]
  have hV := variance_le_quadratic h le_rfl hA hT.le (fun _ ht ↦ hTime ht.1) hAcc
  change V T ≤ V 0 + T * c - a * T ^ 2 at hV
  have hAbs := mul_le_mul_of_nonneg_right (neg_le_abs L) hM
  dsimp only [b] at hLarge
  linarith only [hV, hLow T hT.le, hLarge, hAbs, le_abs_self (V 0)]

/-- Radial weak solutions with a uniform negative energy bound cannot be forward global
in the full lower range 3 ≤ p ≤ 5. -/
theorem IsNLSSolution.false_of_radial_forward_of_le_five
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) (hp₅ : p ≤ 5)
    (hTime : Ici (0 : ℝ) ⊆ interior J) {e : ℝ} (he : 0 < e)
    (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e)
    (hRadial : ∀ t ≥ 0, IsRadialAE (u t)) : False := by
  rcases hp.eq_or_lt with rfl | hp'
  · exact h.false_of_radial_cubic_forward hTime he hEnergy hRadial
  · exact h.false_of_radial_forward hp' hp₅ hTime he hEnergy hRadial

/-- Uniformly negative energy gives a positive lower bound for the squared gradient
on the forward ray, using mass conservation and the homogeneous inequality. -/
theorem IsNLSSolution.exists_pos_le_gradNormSq_forward
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) (hTime : Ici (0 : ℝ) ⊆ interior J)
    {e : ℝ} (he : 0 < e) (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e) :
    ∃ g : ℝ, 0 < g ∧ ∀ t ≥ 0, g ≤ gradNormSq (Du t) := by
  have hM : 0 ≤ mass (u 0) := integral_nonneg (fun _ ↦ sq_nonneg _)
  obtain ⟨g, hg, hLower⟩ :=
    exists_pos_le_gradNormSq_of_energy_le_neg hp (M := mass (u 0) + 1) (by positivity) he
  refine ⟨g, hg, fun t ht ↦ ?_⟩
  have hEq := h.mass_eq hp ht (fun _ hs ↦ hTime hs.1)
  exact hLower (u t) (Du t) (h.h1 t (interior_subset (hTime ht)))
    (by rw [hEq]; linarith) (hEnergy t ht)

private theorem kinetic_primitives_lower {K : ℝ → ℝ} (hK : ContinuousOn K (Ici 0))
    {g T : ℝ} (hg : ∀ t ≥ 0, g ≤ K t) (hT : 0 ≤ T) :
    g * T ≤ (∫ t in 0..T, K t) ∧
      g * T ^ 2 / 2 ≤ ∫ t in 0..T, (T - t) * K t := by
  let k (t : ℝ) := K (max 0 t)
  have hk : Continuous k := hK.comp_continuous (continuous_const.max continuous_id')
    (fun t ↦ le_max_left 0 t)
  have hEq (t : ℝ) (ht : t ∈ Icc 0 T) : k t = K t := by dsimp [k]; rw [max_eq_right ht.1]
  have hLower (t : ℝ) (ht : t ∈ Icc 0 T) : g ≤ k t := (hEq t ht).symm ▸ hg t ht.1
  constructor
  · refine (integral_ge_of_ge hk hT hLower).trans_eq (intervalIntegral.integral_congr ?_)
    rw [uIcc_of_le hT]
    exact hEq
  · refine (weighted_integral_ge_of_ge hk hT hLower).trans_eq (intervalIntegral.integral_congr ?_)
    rw [uIcc_of_le hT]
    exact fun t ht ↦ congrArg ((T - t) * ·) (hEq t ht)

private theorem initial_virial_bound_of_scale {v : ℝ² → ℂ} {Dv : Fin 2 → ℝ² → ℂ}
    (hv : IsH1 v Dv) {p T S I c g : ℝ} (hp : 3 < p) (hS : 0 < S) (hg : 0 < g)
    (hI : 0 ≤ I) (hc₁ : 2 / (p - 3) ≤ c)
    (hc₂ : 128 * gradNormSq Dv / (g * (p - 3) ^ 2) ≤ c)
    (hV : compactMoment v S ≤ I / c) (hT : T ^ 2 ≤ 2 * I / g) :
    (∫ x, virialWeight (2 * S) x * ‖v x‖ ^ 2) +
      T * |virialFirstDeriv (virialWeight (2 * S)) v Dv| ≤ (p - 3) * I := by
  let V := ∫ x, virialWeight (2 * S) x * ‖v x‖ ^ 2
  have hV₀ : 0 ≤ V :=
    integral_nonneg (fun x ↦ mul_nonneg (virialWeight_nonneg _ x) (sq_nonneg _))
  have hK := gradNormSq_nonneg Dv
  have hCur := eq_4_7_deriv hv (Q := 2 * S) (by positivity)
  have hSq := pow_le_pow_left₀ (abs_nonneg _) hCur 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hK, Real.sq_sqrt hV₀] at hSq
  norm_num at hSq
  exact eq_5_5 (sub_pos.mpr hp) hg hI hK hc₁ hc₂
    ((eq_4_7_value hv.memL2 hS).trans hV) hV₀ (by simpa only [sq_abs] using hSq) hT

/-- The superquintic forward contradiction in Section 5, conditional on the
exterior estimate (3.6) and a uniform negative energy bound. -/
theorem IsNLSSolution.false_of_superquintic_exterior_estimate
    (h : IsNLSSolution p J u Du) (hp : 5 < p) (hTime : Ici (0 : ℝ) ⊆ interior J)
    {e c₀ ε₀ Cₑ : ℝ} (he : 0 < e) (hc₀ : 0 < c₀) (hε₀ : 0 < ε₀) (hCₑ : 0 ≤ Cₑ)
    (hEnergy : ∀ t ≥ 0, energy p (u t) (Du t) ≤ -e)
    (hExterior : ∀ {T S : ℝ}, 0 < T → 1 ≤ S → T / S ^ 2 ≤ c₀ →
      exteriorEps p T S u Du ≤ ε₀ →
      ∃ R ∈ Icc S (2 * S), ∀ t ∈ Icc 0 T,
        (∫ x in {x : ℝ² | R < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤
          Cₑ * exteriorEps p T S u Du ^ (p - 1) *
            ((∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2) +
              mass (u 0) / S ^ 2)) : False := by
  have hp₃ : 3 < p := by linarith
  by_cases hVar : Integrable (fun x ↦ ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2)
  · exact h.false_of_finite_initial_variance hp₃.le hTime he hEnergy hVar
  obtain ⟨C, D, hC, hD, hBound⟩ := virialSecondDeriv_virialWeight_le
  obtain ⟨g, hg, hLower⟩ := h.exists_pos_le_gradNormSq_forward hp₃.le hTime he hEnergy
  let M := mass (u 0)
  let K (t : ℝ) := gradNormSq (Du t)
  let H := compactMoment (u 0)
  let A := (2 * (p - 1) / (p + 1)) * C
  let L := A * Cₑ
  let c := max 1 (max (2 / (p - 3)) (128 * K 0 / (g * (p - 3) ^ 2)))
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (by linarith) (by linarith)) hC
  have hL : 0 ≤ L := mul_nonneg hA hCₑ
  have hc : 0 < c := zero_lt_one.trans_le (le_max_left _ _)
  have hc₁ : 2 / (p - 3) ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hc₂ : 128 * K 0 / (g * (p - 3) ^ 2) ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  let b := min e (2 * (p - 3))
  let η := min ε₀ (min 1 (b / (L + 1)))
  let δ := min (c₀ * g) (η ^ 2 / 8)
  have hb : 0 < b := lt_min he (by linarith)
  have hη : 0 < η := lt_min hε₀ (lt_min one_pos (div_pos hb (by linarith)))
  have hδ : 0 < δ := lt_min (mul_pos hc₀ hg) (by positivity)
  have hηε : η ≤ ε₀ := min_le_left _ _
  have hη₁ : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηb : η ≤ b / (L + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLb : L * η ≤ b := by
    have hs := (le_div_iff₀ (by linarith : 0 < L + 1)).mp hηb
    nlinarith only [hs, hη.le]
  let N := 1 + M / g + M + (2 * h1Norm (u 0) (Du 0) / η) ^ 2 + D * M / e
  have hMg : 0 ≤ M / g := div_nonneg hM hg.le
  have hDMe : 0 ≤ D * M / e := div_nonneg (mul_nonneg hD hM) he.le
  have hN₁ : 1 ≤ N := by dsimp [N]; linarith [sq_nonneg (2 * h1Norm (u 0) (Du 0) / η)]
  have hu₀ := h.h1 0 (interior_subset (hTime (mem_Ici.mpr le_rfl)))
  have hK : ContinuousOn K (Ici 0) := h.continuousOn_gradNormSq.mono (hTime.trans interior_subset)
  obtain ⟨T, S, hNT, hNS, hS, hMoment, hScale⟩ :=
    exists_good_scale K hK g hg hLower H (compactMoment_monotoneOn hu₀.memL2)
      (compactMoment_continuousOn hu₀.memL2) (compactMoment_tendsto_atTop hu₀.memL2 hVar)
      (compactMoment_integrableOn hu₀.memL2) c hc δ hδ N
  have hT : 1 ≤ T := hN₁.trans hNT
  have hT' : 0 < T := by linarith
  have hS' : 0 < S := by linarith
  obtain ⟨hF, hI⟩ := kinetic_primitives_lower hK hLower hT'.le
  have hSmallT : T / S ^ 2 ≤ c₀ := by
    have hF' : g ≤ ∫ t in 0..T, K t :=
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hg.le : g ≤ g * T).trans hF
    apply (div_le_iff₀ (sq_pos_of_pos hS')).2
    have hTimeF := (div_le_iff₀ (sq_pos_of_pos hS')).mp (hScale.trans (min_le_left _ _))
    have hTimeG := mul_le_mul_of_nonneg_left hF' hT'.le
    exact (le_of_mul_le_mul_right
      (show T * g ≤ (c₀ * S ^ 2) * g by nlinarith only [hTimeG, hTimeF]) hg)
  have hEps : exteriorEps p T S u Du ≤ η := by
    apply eps_le_of_scales (h := h1Norm (u 0) (Du 0))
      hp₃.le hT hS hg hF hM ?_ hη (Real.sqrt_nonneg _) ?_
      (hScale.trans (min_le_right _ _))
    · dsimp [N] at hNS
      linarith [sq_nonneg (2 * h1Norm (u 0) (Du 0) / η)]
    · dsimp only [N] at hNS
      linarith only [hNS, hMg, hM, hDMe]
  obtain ⟨R, hR, hEst⟩ := hExterior hT' hS hSmallT (hEps.trans hηε)
  have hQ : 0 < 2 * S := by positivity
  have h1Q : 1 ≤ 2 * S := by linarith
  have hMsmall : M / S ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hS')).2
    dsimp [N] at hNS
    nlinarith only [hNS, hMg, hDMe, hS, sq_nonneg (2 * h1Norm (u 0) (Du 0) / η),
      mul_nonneg hS'.le (sub_nonneg.mpr hS)]
  have hDsmall : D * M / (2 * S) ≤ e := by
    have hD' : D * M / e ≤ 2 * S := by
      dsimp only [N] at hNS
      linarith only [hNS, hS, hMg, hM, sq_nonneg (2 * h1Norm (u 0) (Du 0) / η)]
    exact (div_le_iff₀ hQ).2 (by simpa only [mul_comm e] using (div_le_iff₀ he).mp hD')
  have hEps₀ : 0 ≤ exteriorEps p T S u Du := by
    unfold exteriorEps
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg hS'.le _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg hT'.le _) (Real.sqrt_nonneg _))
  have hCoeff : L * exteriorEps p T S u Du ^ (p - 1) ≤ b := by
    have hPow := Real.rpow_le_rpow hEps₀ hEps (by linarith : 0 ≤ p - 1)
    have hηPow : η ^ (p - 1) ≤ η := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hη hη₁ (show 1 ≤ p - 1 by linarith)
    exact (mul_le_mul_of_nonneg_left (hPow.trans hηPow) hL).trans hLb
  have hSeg : Icc 0 T ⊆ interior J := fun _ ht ↦ hTime ht.1
  have hAcceleration (t : ℝ) (ht : t ∈ Icc 0 T) :
      virialSecondDeriv p (virialWeight (2 * S)) (u t) (Du t) ≤
        -4 * (p - 1) * e - 2 * (p - 3) * K t := by
    have hData := h.h1 t (interior_subset (hSeg ht))
    have hU := hData.integrable_nonlinear_density hp₃.le
    have hMass := h.mass_eq hp₃.le ht.1 (fun _ hs ↦ hTime hs.1)
    have hGrad := ((hData.memL2_partial 0).norm.integrable_sq.add
      (hData.memL2_partial 1).norm.integrable_sq)
    have hGradTail : (∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2) ≤ K t :=
      setIntegral_le_integral hGrad (.of_forall fun _ ↦ by positivity)
    have hTail :
        (∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤
          Cₑ * exteriorEps p T S u Du ^ (p - 1) * (K t + 1) :=
      (setIntegral_mono_set hU.integrableOn (.of_forall fun _ ↦ by positivity)
        (.of_forall fun _ hx ↦ hR.2.trans_lt hx)).trans
        ((hEst t ht).trans (mul_le_mul_of_nonneg_left (add_le_add hGradTail hMsmall)
          (mul_nonneg hCₑ (Real.rpow_nonneg hEps₀ _))))
    have hWeighted :
        A * (∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1)) ≤
          e + 2 * (p - 3) * K t := by
      calc
        _ ≤ A * (Cₑ * exteriorEps p T S u Du ^ (p - 1) * (K t + 1)) :=
          mul_le_mul_of_nonneg_left hTail hA
        _ = (L * exteriorEps p T S u Du ^ (p - 1)) * (K t + 1) := by dsimp [L]; ring
        _ ≤ b * (K t + 1) :=
          mul_le_mul_of_nonneg_right hCoeff (add_nonneg (gradNormSq_nonneg _) zero_le_one)
        _ ≤ _ := by
          rw [mul_add, mul_one, add_comm]
          exact add_le_add (min_le_left _ _)
            (mul_le_mul_of_nonneg_right (min_le_right _ _) (gradNormSq_nonneg _))
    exact acceleration_of_error_bounds hp₃.le he (hEnergy t ht.1)
      (hBound hp₃.le hQ hData.memL2 hData.memL2_partial hU) hWeighted
      ((mass_error_le hD hM h1Q hMass.le).trans hDsmall)
  have hT_sq : T ^ 2 ≤ 2 * (∫ t in 0..T, (T - t) * K t) / g := by
    apply (le_div_iff₀ hg).2
    nlinarith only [hI]
  have hI₀ : 0 ≤ ∫ t in 0..T, (T - t) * K t :=
    (by positivity : 0 ≤ g * T ^ 2 / 2).trans hI
  exact h.false_of_terminal_virial_bounds hp₃.le he hQ hT' hSeg hAcceleration
    (initial_virial_bound_of_scale hu₀ hp₃ hS' hg hI₀ hc₁ hc₂ hMoment hT_sq)

end Blowup
