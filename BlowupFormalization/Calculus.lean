import Mathlib

/-!
# One-variable calculus used in Section 5

`le_tangent_of_second_deriv_nonpos`: if `f'' ≤ 0` on `[0, T]` then
`f(T) ≤ f(0) + T f'(0)`. This is the step "integrating (5.8) twice".
-/

namespace Blowup

/-- If `f' ≤ 0` on `[0, T]` (derivatives taken within `[0, T]`), then `f` is antitone there. -/
theorem antitoneOn_Icc_of_hasDerivWithinAt {T : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t)
    (hf' : ∀ t ∈ Set.Icc 0 T, f' t ≤ 0) : AntitoneOn f (Set.Icc 0 T) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc 0 T)
    (fun t ht ↦ (hf t ht).continuousWithinAt) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · rw [interior_Icc] at ht ⊢
    exact (hf t (Set.Ioo_subset_Icc_self ht)).mono Set.Ioo_subset_Icc_self
  · rw [interior_Icc] at ht
    exact hf' t (Set.Ioo_subset_Icc_self ht)

/-- **Concavity bound.** If `f'' ≤ 0` on `[0, T]` then `f(T) ≤ f(0) + T f'(0)`. -/
theorem le_tangent_of_second_deriv_nonpos {T : ℝ} (hT : 0 ≤ T) {f f' f'' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f (f' t) (Set.Icc 0 T) t)
    (hf' : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt f' (f'' t) (Set.Icc 0 T) t)
    (hf'' : ∀ t ∈ Set.Icc 0 T, f'' t ≤ 0) : f T ≤ f 0 + T * f' 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hT' : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  -- `f'` is antitone, so `f' t ≤ f' 0`.
  have hanti := antitoneOn_Icc_of_hasDerivWithinAt hf' hf''
  -- hence `g t = f t - f 0 - t f'(0)` has nonpositive derivative and is antitone.
  have hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s ↦ f s - f 0 - s * f' 0)
      (f' t - f' 0) (Set.Icc 0 T) t := by
    intro t ht
    have := ((hf t ht).sub_const (f 0)).sub ((hasDerivWithinAt_id t _).mul_const (f' 0))
    simp only [id, one_mul] at this
    exact this
  have := antitoneOn_Icc_of_hasDerivWithinAt hg
    (fun t ht ↦ sub_nonpos.mpr (hanti h0 ht ht.1)) h0 hT' hT
  simp at this
  linarith

/-- FTC: `(∫₀ᵗ k)' = k(t)` for continuous `k`. -/
theorem hasDerivAt_integral_zero {k : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ s in (0)..t, k s) (k t) t :=
  intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
    (hk.stronglyMeasurableAtFilter _ _) hk.continuousAt

/-- `(∫₀ᵗ (t - s) k(s) ds)' = ∫₀ᵗ k` for continuous `k`; this is `I' = F` in (5.2). -/
theorem hasDerivAt_weighted_integral {k : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ s in (0)..t, (t - s) * k s) (∫ s in (0)..t, k s) t := by
  have hsplit : (fun t ↦ ∫ s in (0)..t, (t - s) * k s) =
      fun t ↦ t * (∫ s in (0)..t, k s) - ∫ s in (0)..t, s * k s := by
    funext t
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (f := fun s ↦ t * k s) (g := fun s ↦ s * k s)
      ((hk.intervalIntegrable _ _).const_mul t)
      ((continuous_id'.mul hk).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rw [hsplit]
  have h1 := (hasDerivAt_id' t).mul (hasDerivAt_integral_zero hk t)
  have h2 := hasDerivAt_integral_zero (continuous_id'.mul hk) t
  convert h1.sub h2 using 1
  simp only [Pi.mul_apply]
  ring

/-- `F(T) = ∫₀ᵀ k ≥ g T` if `k ≥ g` on `[0, T]`. -/
theorem integral_ge_of_ge {k : ℝ → ℝ} (hk : Continuous k) {g T : ℝ} (hT : 0 ≤ T)
    (hkg : ∀ t ∈ Set.Icc 0 T, g ≤ k t) : g * T ≤ ∫ t in (0)..T, k t := by
  have := intervalIntegral.integral_mono_on hT (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    (hk.intervalIntegrable 0 T) hkg
  simpa [mul_comm] using this

/-- `I(T) = ∫₀ᵀ (T - t) k(t) dt ≥ g T²/2` if `k ≥ g` on `[0, T]`. -/
theorem weighted_integral_ge_of_ge {k : ℝ → ℝ} (hk : Continuous k) {g T : ℝ} (hT : 0 ≤ T)
    (hkg : ∀ t ∈ Set.Icc 0 T, g ≤ k t) :
    g * T ^ 2 / 2 ≤ ∫ t in (0)..T, (T - t) * k t := by
  have hmono := intervalIntegral.integral_mono_on hT
    (((continuous_const.sub continuous_id').mul continuous_const).intervalIntegrable
      (μ := MeasureTheory.volume) 0 T)
    (((continuous_const.sub continuous_id').mul hk).intervalIntegrable
      (μ := MeasureTheory.volume) 0 T)
    (fun t ht ↦ mul_le_mul_of_nonneg_left (hkg t ht) (sub_nonneg.mpr ht.2))
  have hcomp : ∫ t in (0)..T, (T - t) * g = g * T ^ 2 / 2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id'.intervalIntegrable 0 T), integral_id]
    simp
    ring
  simp only [Pi.mul_apply, Pi.sub_apply] at hmono
  linarith

end Blowup
