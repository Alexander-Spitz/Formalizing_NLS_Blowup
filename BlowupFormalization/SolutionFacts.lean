import BlowupFormalization.Defs

/-!
# Elementary facts about solutions and about the initial datum

* restricting a solution to a smaller time interval;
* continuity of `t ↦ ‖∇u(t)‖₂²`;
* the compact moments `H(S) = ∫_{|x| ≤ 10S} |x|² |u₀|²` of (5.3) and the bound behind (5.6).
-/

open MeasureTheory Filter Topology

namespace Blowup

variable {p : ℝ} {J J' : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- A solution on `J` is a solution on every `J' ⊆ J`. -/
theorem IsNLSSolution.mono (h : IsNLSSolution p J u Du) (hJ : J' ⊆ J) :
    IsNLSSolution p J' u Du where
  h1 t ht := h.h1 t (hJ ht)
  continuous_L2 t ht := (h.continuous_L2 t (hJ ht)).mono_left (nhdsWithin_mono t hJ)
  continuous_grad_L2 t ht j := (h.continuous_grad_L2 t (hJ ht) j).mono_left (nhdsWithin_mono t hJ)
  weak_equation φ hφ hc hs :=
    h.weak_equation φ hφ hc (hs.trans (Set.prod_mono (interior_mono hJ) le_rfl))

/-- The norm in `L²` is the square root of the integral of the squared pointwise norm. -/
private lemma norm_toLp_two {f : ℝ² → ℂ} (hf : MemLp f 2) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2) := by
  rw [Lp.norm_toLp, toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow, one_div]

private lemma continuous_toLp_two {f : ℝ → ℝ² → ℂ} (hf : ∀ t : J, MemLp (f t) 2)
    (hlim : ∀ t ∈ J, Tendsto (fun s ↦ ∫ x, ‖f s x - f t x‖ ^ 2) (𝓝[J] t) (𝓝 0)) :
    Continuous (fun t : J ↦ (hf t).toLp (f t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hval : Tendsto Subtype.val (𝓝 t) (𝓝[J] ↑t) :=
    tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.continuousAt, .of_forall Subtype.property⟩
  have hs := (hlim t t.property).comp hval
  simp only [← MemLp.toLp_sub, norm_toLp_two, Pi.sub_apply]
  simpa only [Real.sqrt_zero, Function.comp_def] using hs.sqrt

/-- A solution is continuous on its time domain as a map into the `L²` space. -/
theorem IsNLSSolution.continuous_toLp (h : IsNLSSolution p J u Du) :
    Continuous (fun t : J ↦ (h.h1 t t.property).memL2.toLp (u t)) :=
  continuous_toLp_two (f := u) (fun t ↦ (h.h1 t t.property).memL2) h.continuous_L2

/-- Each weak spatial derivative is continuous on the time domain as a map into `L²`. -/
theorem IsNLSSolution.continuous_grad_toLp (h : IsNLSSolution p J u Du) (j : Fin 2) :
    Continuous (fun t : J ↦ ((h.h1 t t.property).memL2_partial j).toLp (Du t j)) :=
  continuous_toLp_two (f := fun t ↦ Du t j) (fun t ↦ (h.h1 t t.property).memL2_partial j)
    (fun t ht ↦ h.continuous_grad_L2 t ht j)

/-- `t ↦ ‖∇u(t)‖₂²` is continuous on `J`, since `∇u ∈ C(J; L²)`. -/
theorem IsNLSSolution.continuousOn_gradNormSq (h : IsNLSSolution p J u Du) :
    ContinuousOn (fun t ↦ gradNormSq (Du t)) J := by
  let D (j : Fin 2) (t : J) := ((h.h1 t t.property).memL2_partial j).toLp (Du t j)
  have hD (j : Fin 2) : Continuous (D j) := h.continuous_grad_toLp j
  rw [continuousOn_iff_continuous_domRestrict]
  apply ((hD 0).norm.pow 2 |>.add ((hD 1).norm.pow 2)).congr
  intro t
  have hDj := (h.h1 t t.property).memL2_partial
  simp only [Pi.add_apply, Pi.pow_apply, D, norm_toLp_two,
    Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))]
  exact (integral_add (hDj 0).norm.integrable_sq (hDj 1).norm.integrable_sq).symm

/-- The compact moment (5.3): `H(S) = ∫_{|x| ≤ 10S} |x|² |u₀|²`. -/
noncomputable def compactMoment (u₀ : ℝ² → ℂ) (S : ℝ) : ℝ :=
  ∫ x in Metric.closedBall (0 : ℝ²) (10 * S), ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2

/-- On a ball the variance density is bounded by the mass density times the squared radius. -/
theorem variance_integrableOn_closedBall {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) (r : ℝ) :
    IntegrableOn (fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2) (Metric.closedBall 0 r) := by
  refine ((hu₀.norm.integrable_sq.const_mul (r ^ 2)).integrableOn).mono' ?_ ?_
  · exact (continuous_norm.pow 2).aestronglyMeasurable.mul hu₀.norm.integrable_sq.1.restrict
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hx' : ‖x‖ ≤ r := by simpa using hx
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr

/-- Enlarging the ball increases the integral of the nonnegative variance density. -/
private lemma compactMoment_mono {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) :
    Monotone (compactMoment u₀) := by
  intro S T hST
  apply setIntegral_mono_set (variance_integrableOn_closedBall hu₀ _)
    (.of_forall fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact .of_forall fun _ hx ↦ Metric.closedBall_subset_closedBall (by gcongr : 10 * S ≤ 10 * T) hx

theorem compactMoment_monotoneOn {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) :
    MonotoneOn (compactMoment u₀) (Set.Ici 1) := by
  exact (compactMoment_mono hu₀).monotoneOn _

theorem compactMoment_continuousOn {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) :
    ContinuousOn (compactMoment u₀) (Set.Ici 1) := by
  classical
  intro S hS
  apply ContinuousAt.continuousWithinAt
  let B (T : ℝ) := Metric.closedBall (0 : ℝ²) (10 * T)
  let f := fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2
  have hB (T : ℝ) : MeasurableSet (B T) := measurableSet_closedBall
  have hrepr (T : ℝ) : compactMoment u₀ T = ∫ x, (B T).indicator f x :=
    (integral_indicator (hB T)).symm
  rw [funext hrepr]
  apply continuousAt_of_dominated (bound := (B (S + 1)).indicator f)
  · exact .of_forall fun T ↦ ((variance_integrableOn_closedBall hu₀ _).integrable_indicator
      (hB T)).aestronglyMeasurable
  · filter_upwards [gt_mem_nhds (show S < S + 1 by linarith)] with T hT
    filter_upwards with x
    by_cases hx : x ∈ B T
    · have hx' : x ∈ B (S + 1) := Metric.closedBall_subset_closedBall
          (by linarith : 10 * T ≤ 10 * (S + 1)) hx
      simp [Set.indicator_of_mem, hx, hx', f, Real.norm_of_nonneg (by positivity :
        0 ≤ ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2)]
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      exact Set.indicator_nonneg (fun x _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) _
  · exact (variance_integrableOn_closedBall hu₀ _).integrable_indicator (hB _)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume.addHaar_sphere (0 : ℝ²) (10 * S))] with x hx
    have hne : ‖x‖ ≠ 10 * S := by simpa [Metric.mem_sphere] using hx
    have hc : ContinuousAt (fun T : ℝ ↦ 10 * T) S := by fun_prop
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [hc.tendsto.eventually (lt_mem_nhds hlt)] with T hT
      exact Set.indicator_of_mem (by simpa [B, Metric.mem_closedBall] using hT.le) _
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [hc.tendsto.eventually (gt_mem_nhds hgt)] with T hT
      exact Set.indicator_of_notMem (by simpa [B, Metric.mem_closedBall] using hT.not_ge) _

/-- If `|x| u₀ ∉ L²` then `H(S) → ∞`. -/
theorem compactMoment_tendsto_atTop {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2)
    (hvar : ¬ Integrable (fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2)) :
    Tendsto (compactMoment u₀) atTop atTop := by
  apply (compactMoment_mono hu₀).tendsto_atTop_atTop
  intro K
  by_contra! hbounded
  apply hvar
  have hcover : AECover volume atTop (fun S : ℝ ↦ Metric.closedBall (0 : ℝ²) (10 * S)) :=
    aecover_closedBall ((tendsto_const_mul_atTop_of_pos (by norm_num)).2 tendsto_id)
  exact hcover.integrable_of_integral_bounded_of_nonneg_ae K
    (fun S ↦ variance_integrableOn_closedBall hu₀ _) (.of_forall fun x ↦ by positivity)
    (.of_forall fun S ↦ (hbounded S).le)

/-- Integrating the inverse cube above a positive cutoff gives half its inverse square. -/
private lemma inverse_cube_tail {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun S : ℝ ↦ S ^ (-3 : ℝ)) (Set.Ici a) ∧
      (∫ S in Set.Ici a, S ^ (-3 : ℝ)) = 1 / (2 * a ^ 2) := by
  constructor
  · exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)
  · rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by norm_num) ha]
    norm_num [Real.rpow_neg ha.le, Real.rpow_two]
    ring

/-- The computation behind (5.6): `∫₁^∞ H(S)/S³ dS < ∞` (it is `≲ M`), by Tonelli. -/
theorem compactMoment_integrableOn {u₀ : ℝ² → ℂ} (hu₀ : MemLp u₀ 2) :
    IntegrableOn (fun S ↦ compactMoment u₀ S / S ^ 3) (Set.Ioi 1) := by
  classical
  let a (x : ℝ²) := max 1 (‖x‖ / 10)
  let f (x : ℝ²) := ‖x‖ ^ 2 * ‖u₀ x‖ ^ 2
  let A := {z : ℝ² × ℝ | a z.1 ≤ z.2}
  let F := A.indicator (fun z : ℝ² × ℝ ↦ f z.1 * z.2 ^ (-3 : ℝ))
  have ha (x : ℝ²) : 0 < a x := zero_lt_one.trans_le (le_max_left _ _)
  have hf : AEStronglyMeasurable f := (continuous_norm.pow 2).aestronglyMeasurable.mul
    hu₀.norm.integrable_sq.1
  have hA : MeasurableSet A := isClosed_le (by dsimp [a]; fun_prop) continuous_snd |>.measurableSet
  have hF : AEStronglyMeasurable F (volume.prod volume) :=
    (hf.comp_fst.mul (measurable_snd.pow measurable_const).aestronglyMeasurable).indicator hA
  have hslice (x : ℝ²) : (fun S ↦ F (x, S)) =
      (Set.Ici (a x)).indicator (fun S ↦ f x * S ^ (-3 : ℝ)) := by
    funext S
    by_cases hS : a x ≤ S <;> simp [F, A, Set.indicator, hS]
  -- Integrate in the scale variable first. The cutoff cancels the quadratic spatial weight.
  have hprod : Integrable F (volume.prod volume) := by
    apply (integrable_prod_iff hF).2
    constructor
    · filter_upwards with x
      rw [hslice x]
      exact IntegrableOn.integrable_indicator ((inverse_cube_tail (ha x)).1.const_mul (f x))
        measurableSet_Ici
    · refine (hu₀.norm.integrable_sq.const_mul 50).mono' hF.norm.integral_prod_right' ?_
      filter_upwards with x
      have hpos (S : ℝ) : 0 ≤ F (x, S) := by
        by_cases hS : a x ≤ S
        · simp only [F, Set.indicator_of_mem (show (x, S) ∈ A from hS)]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (Real.rpow_nonneg ((ha x).le.trans hS) _)
        · simp [F, A, hS]
      simp_rw [Real.norm_of_nonneg (hpos _)]
      rw [Real.norm_of_nonneg (integral_nonneg hpos), hslice, integral_indicator measurableSet_Ici,
        integral_const_mul, (inverse_cube_tail (ha x)).2]
      have hx : ‖x‖ ≤ 10 * a x := by
        have := le_max_right 1 (‖x‖ / 10)
        dsimp [a]
        linarith
      have hsq : ‖x‖ ^ 2 ≤ (10 * a x) ^ 2 := by gcongr
      change (‖x‖ ^ 2 * ‖u₀ x‖ ^ 2) * (1 / (2 * a x ^ 2)) ≤ 50 * ‖u₀ x‖ ^ 2
      rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 2 * a x ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖u₀ x‖)]
  -- In the opposite order the spatial slice is exactly the defining ball for H(S).
  apply hprod.integral_prod_right.integrableOn.congr_fun _ measurableSet_Ioi
  intro S hS
  have hS' : 1 < S := hS
  have hslice' : (fun x ↦ F (x, S)) =
      (Metric.closedBall (0 : ℝ²) (10 * S)).indicator (fun x ↦ f x * S ^ (-3 : ℝ)) := by
    funext x
    have hiff : (x, S) ∈ A ↔ x ∈ Metric.closedBall (0 : ℝ²) (10 * S) := by
      simp [A, a, max_le_iff, hS'.le, div_le_iff₀, mul_comm, Metric.mem_closedBall]
    by_cases hx : (x, S) ∈ A
    · simp [F, hx, hiff.mp hx]
    · simp [F, hx, mt hiff.mpr hx]
  change (∫ x, F (x, S)) = compactMoment u₀ S / S ^ 3
  rw [hslice', integral_indicator measurableSet_closedBall, integral_mul_const]
  change compactMoment u₀ S * S ^ (-3 : ℝ) = compactMoment u₀ S / S ^ 3
  rw [Real.rpow_neg (by linarith), div_eq_mul_inv]
  norm_num

end Blowup
