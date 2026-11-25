import Mathlib

/-!
# A compact virial weight

We construct the *deficit* from the parabola first. Start with the parabola
`s² - m` on the positive half-line, continue it to the left of `9 / 2` along
its tangent there, and take the maximum with zero. Even reflection gives a
convex profile which vanishes on `[-9 / 4, 9 / 4]`.

We smooth this profile by averaging translates against an even bump of mass
one and radius `1 / 4`. Choosing `m` to be its second moment makes the smoothed
deficit agree exactly with the parabola in the tails. Subtracting the deficit
from the parabola gives the weight. The derivative estimates then follow from
convexity and the supporting tangent inequality.
-/

open scoped ContDiff

noncomputable section

namespace VirialWeight

open MeasureTheory Set

/-- The bump whose normalization supplies the averaging kernel. -/
private def bump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- Average with respect to the normalized bump centered at zero. -/
private def avg (f : ℝ → ℝ) : ℝ := ∫ t, bump.normed volume t * f t

/-- Continuous functions are integrable against the compactly supported kernel. -/
private lemma integrable_weighted {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun t ↦ bump.normed volume t * f t) :=
  (bump.continuous_normed.mul hf).integrable_of_hasCompactSupport
    bump.hasCompactSupport_normed.mul_right

/-- Only translations by less than a quarter occur in the average. -/
private lemma abs_lt_radius {t : ℝ} (ht : bump.normed volume t ≠ 0) : |t| < 1 / 4 := by
  change t ∈ Function.support (bump.normed volume) at ht
  rw [bump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  exact ht

/-- To compare averages it suffices to compare on the open support of the kernel. -/
private lemma avg_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t : ℝ, |t| < 1 / 4 → f t ≤ g t) : avg f ≤ avg g := by
  apply integral_mono (integrable_weighted hf) (integrable_weighted hg)
  intro t
  by_cases ht : bump.normed volume t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_left (h t (abs_lt_radius ht)) (bump.nonneg_normed t)

/-- Values outside the kernel's support do not affect the average. -/
private lemma avg_congr {f g : ℝ → ℝ} (h : ∀ t : ℝ, |t| < 1 / 4 → f t = g t) :
    avg f = avg g := by
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : bump.normed volume t = 0
  · simp [ht]
  · rw [h t (abs_lt_radius ht)]

/-- Normalization makes the average preserve constants. -/
private lemma avg_const (c : ℝ) : avg (fun _ ↦ c) = c := by
  simp [avg, integral_mul_const, bump.integral_normed]

/-- Averaging is additive on continuous functions. -/
private lemma avg_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    avg (fun t ↦ f t + g t) = avg f + avg g := by
  simp only [avg, mul_add, integral_add (integrable_weighted hf) (integrable_weighted hg)]

/-- Scalar factors pass through the average. -/
private lemma avg_mul (c : ℝ) (f : ℝ → ℝ) :
    avg (fun t ↦ c * f t) = c * avg f := by
  simp only [avg, mul_left_comm (bump.normed volume _) c, integral_const_mul]

/-- Reflection preserves the average because the kernel is even. -/
private lemma avg_reflect (f : ℝ → ℝ) : avg (fun t ↦ f (-t)) = avg f := by
  simpa only [avg, bump.normed_neg] using
    (integral_neg_eq_self (fun t ↦ bump.normed volume t * f t) (μ := volume))

/-- The first moment vanishes by reflection. -/
private lemma avg_id : avg (fun t ↦ t) = 0 := by
  have h := avg_mul (-1) (fun t ↦ t)
  simp only [neg_one_mul] at h
  have even_mean := avg_reflect (fun t ↦ t)
  change avg (fun t ↦ -t) = avg (fun t ↦ t) at even_mean
  linarith

/-- Second moment of the kernel, used to cancel the constant introduced by smoothing. -/
private def moment := avg (fun t ↦ t ^ 2)

/-- The radius of the kernel bounds its second moment. -/
private lemma moment_bounds : 0 ≤ moment ∧ moment ≤ 1 / 16 := by
  constructor
  · exact integral_nonneg fun t ↦ mul_nonneg (bump.nonneg_normed t) (sq_nonneg t)
  · calc
      moment ≤ avg (fun _ ↦ 1 / 16) := by
        apply avg_mono (f := fun t ↦ t ^ 2) (by fun_prop) continuous_const
        intro t ht
        nlinarith [sq_abs t, abs_nonneg t]
      _ = _ := avg_const _

/-- Subtracting the second moment makes the average of a translated square exact. -/
private lemma avg_shifted_square (r : ℝ) :
    avg (fun t ↦ (r - t) ^ 2 - moment) = r ^ 2 := by
  have expand (t : ℝ) :
      (r - t) ^ 2 - moment = (r ^ 2 - moment) + ((-2 * r) * t + t ^ 2) := by ring
  simp_rw [expand]
  rw [avg_add continuous_const (by fun_prop), avg_const,
    avg_add (by fun_prop) (by fun_prop), avg_mul, avg_id]
  change _ + (_ * 0 + moment) = _
  ring

/-- Tangent continuation of the shifted parabola, truncated at zero and reflected. -/
private def profile (x : ℝ) : ℝ :=
  max 0 (9 * |x| - ((9 / 2) ^ 2 + moment) + (max 0 (|x| - 9 / 2)) ^ 2)

/-- The profile is assembled from continuous functions. -/
@[local fun_prop] private lemma profile_continuous : Continuous profile := by
  unfold profile
  fun_prop

/-- The squared positive part is convex since its argument is convex and nonnegative. -/
private lemma profile_convex : ConvexOn ℝ univ profile := by
  have habs : ConvexOn ℝ univ (fun x : ℝ ↦ |x|) := convexOn_norm convex_univ
  have hzero := convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set ℝ))
  have hpos := hzero.sup (habs.add_const (-(9 / 2)))
  have htangent := (habs.smul (c := 9) (by norm_num)).add_const (-((9 / 2) ^ 2 + moment))
  unfold profile
  simp only [sub_eq_add_neg]
  exact hzero.sup (htangent.add (hpos.pow (fun x _ ↦ le_max_left _ _) 2))

/-- On the inner interval the tangent is below zero. -/
private lemma profile_inner {x : ℝ} (hx : |x| ≤ 9 / 4) : profile x = 0 := by
  unfold profile
  rw [max_eq_left (show |x| - 9 / 2 ≤ 0 by linarith)]
  apply max_eq_left
  linarith [moment_bounds.1]

/-- In the tails the squared positive part recovers the original parabola. -/
private lemma profile_outer {x : ℝ} (hx : 9 / 2 ≤ |x|) : profile x = x ^ 2 - moment := by
  unfold profile
  rw [max_eq_right (show 0 ≤ |x| - 9 / 2 by linarith)]
  have heq : 9 * |x| - ((9 / 2) ^ 2 + moment) + (|x| - 9 / 2) ^ 2 = x ^ 2 - moment := by
    nlinarith [sq_abs x]
  rw [heq, max_eq_right]
  nlinarith [sq_abs x, moment_bounds.2, sq_nonneg (|x| - 1)]

/-- Above radius one both zero and the tangent lie below the shifted parabola. -/
private lemma profile_le_square {x : ℝ} (hx : 1 ≤ |x|) : profile x ≤ x ^ 2 - moment := by
  rcases le_total (9 / 2) |x| with hout | hin
  · exact (profile_outer hout).le
  unfold profile
  rw [max_eq_left (show |x| - 9 / 2 ≤ 0 by linarith)]
  apply max_le
  · nlinarith [moment_bounds.2, sq_abs x, sq_nonneg (|x| - 1)]
  · nlinarith [sq_abs x, sq_nonneg (|x| - 9 / 2)]

/-- The smoothed deficit is the convolution of the kernel with the convex profile. -/
private def deficit (r : ℝ) : ℝ := avg (fun t ↦ profile (r - t))

/-- Convolution with the compactly supported smooth factor smooths the profile. -/
private lemma deficit_smooth : ContDiff ℝ ∞ deficit :=
  bump.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    bump.contDiff_normed profile_continuous.locallyIntegrable

/-- Reflection of both the profile and the kernel leaves the deficit unchanged. -/
private lemma deficit_even (r : ℝ) : deficit (-r) = deficit r := by
  unfold deficit
  rw [← avg_reflect (fun t ↦ profile (-r - t))]
  have reflect (t : ℝ) : -r - -t = -(r - t) := by ring
  simp only [reflect, profile, abs_neg]

/-- The truncated profile and its average are nonnegative. -/
private lemma deficit_nonneg (r : ℝ) : 0 ≤ deficit r :=
  integral_nonneg fun t ↦ mul_nonneg (bump.nonneg_normed t) (le_max_left _ _)

/-- The convexity inequality for the profile can be averaged at a common translation. -/
private lemma deficit_convex : ConvexOn ℝ univ deficit := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul, deficit]
  calc
    _ ≤ avg (fun t ↦ a * profile (x - t) + b * profile (y - t)) := by
      apply avg_mono (profile_continuous.comp (by fun_prop)) (by fun_prop)
      intro t _
      have h := profile_convex.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
      simp only [smul_eq_mul] at h
      rwa [show a * (x - t) + b * (y - t) = a * x + b * y - t by
        linear_combination -t * hab] at h
    _ = _ := by rw [avg_add (by fun_prop) (by fun_prop), avg_mul, avg_mul]

/-- Translating by the support radius leaves an inner interval of radius two. -/
private lemma deficit_inner {r : ℝ} (hr : |r| ≤ 2) : deficit r = 0 := by
  calc
    deficit r = avg (fun _ ↦ 0) := by
      apply avg_congr
      intro t ht
      apply profile_inner
      linarith [abs_sub r t]
    _ = 0 := avg_const _

/-- Reverse triangle inequality in the form needed for the outer intervals. -/
private lemma radius_le_shift (r t : ℝ) : |r| ≤ |r - t| + |t| := by
  simpa using (abs_add_le (r - t) t)

/-- In the tails every sampled value belongs to the same shifted parabola. -/
private lemma deficit_outer {r : ℝ} (hr : 19 / 4 ≤ |r|) : deficit r = r ^ 2 := by
  calc
    deficit r = avg (fun t ↦ (r - t) ^ 2 - moment) := by
      apply avg_congr
      intro t ht
      exact profile_outer (by linarith [radius_le_shift r t])
    _ = r ^ 2 := avg_shifted_square r

/-- Away from the flat core we can compare every sample to the shifted parabola. -/
private lemma deficit_le_square (r : ℝ) : deficit r ≤ r ^ 2 := by
  by_cases hr : |r| ≤ 2
  · rw [deficit_inner hr]
    exact sq_nonneg _
  · calc
      deficit r ≤ avg (fun t ↦ (r - t) ^ 2 - moment) := by
        apply avg_mono (profile_continuous.comp (by fun_prop)) (by fun_prop)
        intro t ht
        exact profile_le_square (by linarith [radius_le_shift r t])
      _ = _ := avg_shifted_square r

/-- The graph of a differentiable convex function lies above each of its tangents. -/
private lemma tangent_le {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g) (hd : Differentiable ℝ g)
    (x y : ℝ) : g x + deriv g x * (y - x) ≤ g y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := hg.deriv_le_slope (mem_univ x) (mem_univ y) h (hd x)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    linarith
  · simp
  · have hs := hg.slope_le_deriv (mem_univ y) (mem_univ x) h (hd x)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    linarith

/-- Subtracting the convex deficit from the parabola gives the virial weight. -/
private def weight (r : ℝ) : ℝ := r ^ 2 - deficit r

/-- First derivative of the weight, expressed in terms of the deficit. -/
private lemma deriv_weight : deriv weight = fun r ↦ 2 * r - deriv deficit r := by
  funext r
  unfold weight
  rw [deriv_fun_sub (by fun_prop) (deficit_smooth.differentiable (by simp) r), deriv_pow_field]
  norm_num

/-- Monotonicity of the deficit's derivative bounds the curvature of the weight. -/
private lemma curvature_bound (r : ℝ) : deriv (deriv weight) r ≤ 2 := by
  have hd := deficit_smooth.differentiable (by simp)
  have hmono : Monotone (deriv deficit) :=
    monotoneOn_univ.mp (deficit_convex.monotoneOn_deriv fun x _ ↦ hd x)
  have hd' := (contDiff_infty_iff_deriv.mp deficit_smooth).2.differentiable (by simp)
  rw [deriv_weight, deriv_fun_sub (by fun_prop) (hd' r)]
  simp [hmono.deriv_nonneg]

/-- Evaluate the tangent bound at the minimum of the quadratic upper bound for the weight. -/
private lemma gradient_bound (r : ℝ) : deriv weight r ^ 2 ≤ 4 * weight r := by
  let d := 2 * r - deriv deficit r
  have ht := tangent_le deficit_convex (deficit_smooth.differentiable (by simp)) r (r - d / 2)
  have hn := deficit_le_square (r - d / 2)
  rw [deriv_weight]
  dsimp [d, weight] at *
  nlinarith

end VirialWeight

open VirialWeight in
/-- **Lemma 4.1.** There is an even nonnegative φ ∈ C_c^∞(ℝ) with φ(r) = r² for |r| ≤ 1,
supp φ ⊂ (-5, 5), φ'' ≤ 2. Moreover φ(r) ≤ r² and |φ'(r)|² ≤ 4 φ(r). -/
theorem lemma_4_1 : ∃ φ : ℝ → ℝ,
    ContDiff ℝ ∞ φ ∧ (∀ r, φ (-r) = φ r) ∧ (∀ r, 0 ≤ φ r) ∧
    (∀ r, |r| ≤ 1 → φ r = r ^ 2) ∧ Function.support φ ⊆ Set.Ioo (-5) 5 ∧
    (∀ r, deriv (deriv φ) r ≤ 2) ∧ (∀ r, φ r ≤ r ^ 2) ∧ (∀ r, deriv φ r ^ 2 ≤ 4 * φ r) ∧
    ConvexOn ℝ Set.univ (fun r ↦ r ^ 2 - φ r) := by
  refine ⟨weight, (contDiff_id.pow 2).sub deficit_smooth, ?_, ?_, ?_, ?_,
    curvature_bound, ?_, gradient_bound, ?_⟩
  · intro r
    simp [weight, deficit_even]
  · exact fun r ↦ sub_nonneg.mpr (deficit_le_square r)
  · intro r hr
    simp [weight, deficit_inner (r := r) (by linarith)]
  · intro r hr
    have h : |r| < 19 / 4 := lt_of_not_ge fun hout ↦ hr (by simp [weight, deficit_outer hout])
    exact abs_lt.mp (lt_trans h (by norm_num : (19 : ℝ) / 4 < 5))
  · exact fun r ↦ sub_le_self _ (deficit_nonneg r)
  · simpa only [weight, sub_sub_cancel] using deficit_convex
