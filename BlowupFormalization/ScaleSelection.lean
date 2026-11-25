import Mathlib

open MeasureTheory Filter Topology

namespace Blowup

/-- FTC for the primitives in (5.2) and (5.6), with continuity only on the relevant ray. -/
private lemma hasDerivAt_ray_integral {f : ℝ → ℝ} {a x : ℝ}
    (hf : ContinuousOn f (Set.Ici a)) (hx : a < x) :
    HasDerivAt (fun u ↦ ∫ t in a..u, f t) (f x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hf.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hx.le
  · exact (hf.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact hf.continuousAt (Ici_mem_nhds hx)

/-- The lower bound for the first primitive in (5.2). -/
private lemma kinetic_integral_lower {K : ℝ → ℝ} {g T : ℝ}
    (hK : ContinuousOn K (Set.Ici 0)) (hKg : ∀ t ≥ 0, g ≤ K t) (hT : 0 ≤ T) :
    g * T ≤ ∫ t in (0)..T, K t := by
  calc
    g * T = ∫ _ in (0)..T, g := by simp [mul_comm]
    _ ≤ _ := intervalIntegral.integral_mono_on hT (intervalIntegrable_const)
      ((hK.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT) fun t ht ↦ hKg t ht.1

/-- Subtracting the first moment gives the weighted integral in (5.1). -/
private lemma weighted_integral_eq {K : ℝ → ℝ} {T : ℝ}
    (hK : ContinuousOn K (Set.Ici 0)) (hT : 0 ≤ T) :
    (∫ t in (0)..T, (T - t) * K t) =
      T * (∫ t in (0)..T, K t) - ∫ t in (0)..T, t * K t := by
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
  · exact ((continuousOn_const.mul hK).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT
  · exact ((continuousOn_id.mul hK).mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT

/-- Differentiating the moment formula for (5.1) gives the identity `I' = F` in (5.2). -/
private lemma hasDerivAt_weighted_moment {K : ℝ → ℝ} {T : ℝ}
    (hK : ContinuousOn K (Set.Ici 0)) (hT : 0 < T) :
    HasDerivAt (fun u ↦ u * (∫ t in (0)..u, K t) - ∫ t in (0)..u, t * K t)
      (∫ t in (0)..T, K t) T := by
  simpa using! ((hasDerivAt_id' T).fun_mul (hasDerivAt_ray_integral hK hT)).fun_sub
    (hasDerivAt_ray_integral (continuousOn_id.mul hK) hT)

/-- Truncations of the integral in (5.6) are uniformly bounded above, even for signed `H`. -/
private lemma radial_integral_upper {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioi 1))
    {S : ℝ} (hS : 1 ≤ S) :
    (∫ s in (1)..S, f s) ≤ ∫ s in Set.Ioi 1, ‖f s‖ := by
  rw [intervalIntegral.integral_of_le hS]
  exact (le_abs_self _).trans <| (norm_integral_le_integral_norm _).trans <|
    setIntegral_mono_set hf.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
      Set.Ioc_subset_Ioi_self.eventuallySubset

/-- Differential form of (5.6). For a moving radius the terms involving its derivative
combine into a multiple of the gap `c H(S) - I(T)` from (5.7). -/
private lemma hasDerivAt_scale_balance {I S P : ℝ → ℝ} {T F v h c δ : ℝ}
    (hI : HasDerivAt I F T) (hS : HasDerivAt S v T)
    (hP : HasDerivAt P (h / S T ^ 3) (S T)) (hT : 0 < T) (hpos : 0 < S T)
    (hsq : T * F = δ * S T ^ 2) :
    HasDerivAt (fun t ↦ 2 * c * P (S t) + I t / S t ^ 2 - δ * Real.log t)
      (2 * v * (c * h - I T) / S T ^ 3) T := by
  convert (((hP.comp T hS).const_mul (2 * c)).fun_add
    (hI.fun_div (hS.fun_pow 2) (pow_ne_zero _ hpos.ne'))).fun_sub
      ((Real.hasDerivAt_log hT.ne').const_mul δ) using 1
  · rfl
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  have hF : F = δ * S T ^ 2 / T := (eq_div_iff hT.ne').2 (by simpa [mul_comm] using hsq)
  rw [hF]
  field_simp [hpos.ne', hT.ne']
  ring

/-- A bounded quantity cannot grow at least as fast as `δ log T`.
This is the logarithmic divergence at the end of the proof of (5.7). -/
private lemma log_growth_contradiction {Q : ℝ → ℝ} {δ B : ℝ} (hδ : 0 < δ)
    (hbounded : ∀ᶠ t in atTop, Q t ≤ B)
    (hgrowth : ∀ᶠ t in atTop, ∃ d ≥ 0,
      HasDerivAt (fun u ↦ Q u - δ * Real.log u) d t) : False := by
  obtain ⟨a, ha⟩ := (hbounded.and hgrowth).exists_forall_of_atTop
  let D := fun t ↦ Q t - δ * Real.log t
  have hD (t : ℝ) (ht : a ≤ t) : DifferentiableAt ℝ D t :=
    ((ha t ht).2.choose_spec.2).differentiableAt
  have hmono : MonotoneOn D (Set.Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a)
    · exact fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt
    · exact fun t ht ↦ (hD t (interior_subset ht)).differentiableWithinAt
    · intro t ht
      obtain ⟨d, hd, hder⟩ := (ha t (interior_subset ht)).2
      exact hder.deriv.symm ▸ hd
  have hlog := (Real.tendsto_log_atTop.const_mul_atTop hδ).eventually_gt_atTop (B - D a)
  obtain ⟨t, ht, hlt⟩ := ((eventually_ge_atTop a).and hlog).exists
  have hle := hmono (Set.mem_Ici.mpr (le_refl a)) ht ht
  change D a ≤ Q t - δ * Real.log t at hle
  change B - D a < δ * Real.log t at hlt
  linarith [(ha t ht).1]

/-- The explicit radius saturating the second bound in (5.7) has nonnegative derivative. -/
private lemma radius_derivative {F : ℝ → ℝ} {T k δ : ℝ}
    (hF : HasDerivAt F k T) (hT : 0 < T) (hpos : 0 < F T) (hk : 0 ≤ k) (hδ : 0 < δ) :
    ∃ v ≥ 0, HasDerivAt (fun t ↦ Real.sqrt (t * F t / δ)) v T := by
  have h := (((hasDerivAt_id' T).fun_mul hF).div_const δ).sqrt
    (show T * F T / δ ≠ 0 by positivity)
  refine ⟨_, ?_, h⟩
  positivity

-- The explicit radius also works without the monotonicity and growth hypotheses on H.
set_option linter.unusedVariables false in
/-- Choice of scales in Section 5, (5.3)–(5.7). `K t = ‖∇u(t)‖₂²`, `F(T) = ∫₀ᵀ K`,
`I(T) = ∫₀ᵀ (T - t) K(t) dt`, `H(S) = ∫_{|x| ≤ 10 S} |x|² |u₀|²`. If `H` is unbounded but
`∫₁^∞ H(S)/S³ dS < ∞`, there are arbitrarily large `T` and `S` with `H(S) ≤ I(T)/c` and
`T F(T) / S² ≤ δ`. -/
theorem exists_good_scale
    (K : ℝ → ℝ) (hK : ContinuousOn K (Set.Ici 0)) (g : ℝ) (hg : 0 < g) (hKg : ∀ t ≥ 0, g ≤ K t)
    (H : ℝ → ℝ) (hHmono : MonotoneOn H (Set.Ici 1)) (hHcont : ContinuousOn H (Set.Ici 1))
    (hHtop : Tendsto H atTop atTop)
    (hHint : IntegrableOn (fun S ↦ H S / S ^ 3) (Set.Ioi 1))
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 < δ) (T₀ : ℝ) :
    ∃ T S : ℝ, T₀ ≤ T ∧ T₀ ≤ S ∧ 1 ≤ S ∧
      H S ≤ (∫ t in (0)..T, (T - t) * K t) / c ∧
      T * (∫ t in (0)..T, K t) / S ^ 2 ≤ δ := by
  -- Prescribing the radius from the second inequality avoids inverting H in (5.3).
  let F := fun T : ℝ ↦ ∫ t in (0)..T, K t
  let I := fun T : ℝ ↦ T * F T - ∫ t in (0)..T, t * K t
  let S := fun T : ℝ ↦ Real.sqrt (T * F T / δ)
  let P := fun R : ℝ ↦ ∫ s in (1)..R, H s / s ^ 3
  have hFtop : Tendsto F atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_id.const_mul_atTop hg)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT using kinetic_integral_lower hK hKg hT
  have hStop : Tendsto S atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_id.atTop_mul_atTop₀ hFtop).atTop_div_const hδ)
  have hlarge : ∀ᶠ T in atTop, 0 < T ∧ T₀ ≤ T ∧ T₀ ≤ S T ∧ 1 < S T ∧ 0 < F T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop T₀,
      hStop.eventually_ge_atTop T₀, hStop.eventually_gt_atTop 1, hFtop.eventually_gt_atTop 0]
      with T ht ht₀ hs₀ hs hf using ⟨ht, ht₀, hs₀, hs, hf⟩
  have hsq (T : ℝ) (ht : 0 < T) (hf : 0 < F T) : T * F T = δ * S T ^ 2 := by
    dsimp [S]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  -- The radial primitive is bounded by (5.6), and I ≤ T F bounds the second term by δ.
  -- If every large time failed (5.7), the scale balance would make Q - δ log nondecreasing.
  let Q := fun T ↦ 2 * c * P (S T) + I T / S T ^ 2
  apply Classical.byContradiction
  intro hfail
  apply log_growth_contradiction (Q := Q) (δ := δ) hδ
    (B := 2 * c * (∫ s in Set.Ioi 1, ‖H s / s ^ 3‖) + δ)
  · filter_upwards [hlarge] with T ⟨ht, _, _, hs, hf⟩
    have hmoment : 0 ≤ ∫ t in (0)..T, t * K t :=
      intervalIntegral.integral_nonneg ht.le fun t h ↦ mul_nonneg h.1 (hg.le.trans (hKg t h.1))
    have hI : I T ≤ T * F T := sub_le_self _ hmoment
    exact add_le_add (mul_le_mul_of_nonneg_left (radial_integral_upper hHint hs.le) (by positivity))
      ((div_le_iff₀ (by positivity : 0 < S T ^ 2)).2 (hI.trans_eq (hsq T ht hf)))
  · filter_upwards [hlarge] with T ⟨ht, ht₀, hs₀, hs, hf⟩
    have hspos : 0 < S T := lt_trans zero_lt_one hs
    have heq := hsq T ht hf
    have hgap : I T < c * H (S T) := by
      by_contra! hle
      apply hfail
      refine ⟨T, S T, ht₀, hs₀, hs.le, ?_, (div_le_iff₀ (pow_pos hspos 2)).2 heq.le⟩
      rw [weighted_integral_eq hK ht.le, le_div_iff₀ hc, mul_comm]
      exact hle
    obtain ⟨v, hv, hS⟩ := radius_derivative (hasDerivAt_ray_integral hK ht) ht hf
      (hg.le.trans (hKg T ht.le)) hδ
    have hrad : ContinuousOn (fun s ↦ H s / s ^ 3) (Set.Ici 1) :=
      hHcont.div (continuousOn_id.pow 3) fun s hs ↦ pow_ne_zero _ (by
        have : 1 ≤ s := hs
        linarith)
    refine ⟨_, ?_, hasDerivAt_scale_balance (hasDerivAt_weighted_moment hK ht) hS
      (hasDerivAt_ray_integral hrad hs) ht hspos heq⟩
    exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hgap.le)) (by positivity)

end Blowup
