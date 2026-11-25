import BlowupFormalization.Defs
import BlowupFormalization.VirialWeight

open MeasureTheory
open scoped ContDiff

namespace Blowup

/-- The profile φ of Lemma 4.1 (a fixed choice). -/
noncomputable def φ : ℝ → ℝ := Classical.choose lemma_4_1

/-- The localized virial weight (4.2): A_Q(x) = Q² φ(|x| / Q). -/
noncomputable def virialWeight (Q : ℝ) (x : ℝ²) : ℝ := Q ^ 2 * φ (‖x‖ / Q)

open Filter Set Metric Topology

/-- The facts about the fixed profile used in the planar estimates. -/
private structure ProfileProperties : Prop where
  smooth : ContDiff ℝ ∞ φ
  nonneg : ∀ r, 0 ≤ φ r
  quadratic : ∀ r, |r| ≤ 1 → φ r = r ^ 2
  support : Function.support φ ⊆ Ioo (-5) 5
  le_sq : ∀ r, φ r ≤ r ^ 2
  deficit_convex : ConvexOn ℝ univ (fun r ↦ r ^ 2 - φ r)

/-- Extract the needed bounds and convexity from Lemma 4.1. -/
private lemma profile_spec : ProfileProperties := by
  obtain ⟨smooth, _, nonneg, quadratic, support, _, le_sq, _, convex⟩ :=
    Classical.choose_spec lemma_4_1
  exact ⟨smooth, nonneg, quadratic, support, le_sq, convex⟩

/-- The localized weight agrees with the squared norm throughout the closed ball. -/
theorem virialWeight_eq_sq {Q : ℝ} (hQ : 0 < Q) {x : ℝ²} (hx : ‖x‖ ≤ Q) :
    virialWeight Q x = ‖x‖ ^ 2 := by
  unfold virialWeight
  rw [profile_spec.quadratic _ (by rwa [abs_of_nonneg (by positivity), div_le_one hQ])]
  field_simp

/-- Nonnegativity also holds for zero and negative scales. -/
theorem virialWeight_nonneg (Q : ℝ) (x : ℝ²) : 0 ≤ virialWeight Q x :=
  mul_nonneg (sq_nonneg Q) (profile_spec.nonneg _)

/-- The squared norm is a global upper bound. -/
theorem virialWeight_le_sq {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) : virialWeight Q x ≤ ‖x‖ ^ 2 := by
  calc
    virialWeight Q x ≤ Q ^ 2 * (‖x‖ / Q) ^ 2 :=
      mul_le_mul_of_nonneg_left (profile_spec.le_sq _) (sq_nonneg Q)
    _ = _ := by field_simp

/-- The weight vanishes at and beyond radius 5Q. -/
theorem virialWeight_eq_zero {Q : ℝ} (hQ : 0 < Q) {x : ℝ²} (hx : 5 * Q ≤ ‖x‖) :
    virialWeight Q x = 0 := by
  have hr : 5 ≤ ‖x‖ / Q := (le_div_iff₀ hQ).2 hx
  have hz : φ (‖x‖ / Q) = 0 := by
    by_contra h
    exact hr.not_gt (profile_spec.support h).2
  simp [virialWeight, hz]

/-- Inside the open ball, all derivatives can be taken on the quadratic model. -/
private lemma eventuallyEq_norm_sq {Q : ℝ} (hQ : 0 < Q) {x : ℝ²} (hx : ‖x‖ < Q) :
    virialWeight Q =ᶠ[𝓝 x] fun y ↦ ‖y‖ ^ 2 := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const hx] with y hy
  exact virialWeight_eq_sq hQ hy.le

/-- The quadratic model gives smoothness at the origin, and the outer cutoff gives compact support. -/
theorem virialWeight_isTestFunction {Q : ℝ} (hQ : 0 < Q) : IsTestFunction (virialWeight Q) := by
  constructor
  · apply contDiff_iff_contDiffAt.2
    intro x
    by_cases hx : x = 0
    · subst x
      exact (contDiff_norm_sq ℝ).contDiffAt.congr_of_eventuallyEq
        (eventuallyEq_norm_sq hQ (by simpa using hQ))
    · exact contDiffAt_const.mul (profile_spec.smooth.contDiffAt.comp x
        ((contDiffAt_norm ℝ hx).div_const Q))
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ²) (5 * Q))
    intro x hx
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact virialWeight_eq_zero hQ hx.le

/-- Smoothness is preserved by coordinate differentiation. -/
private lemma smooth_partial {f : ℝ² → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    ContDiff ℝ ∞ (partialDeriv j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The Laplacian preserves smoothness and compact support. -/
private lemma test_laplacian {f : ℝ² → ℝ} (hf : IsTestFunction f) :
    IsTestFunction (laplacian f) := by
  constructor
  · exact (smooth_partial (smooth_partial hf.1 0) 0).add (smooth_partial (smooth_partial hf.1 1) 1)
  · have hs {g : ℝ² → ℝ} (hg : HasCompactSupport g) (j : Fin 2) :
        HasCompactSupport (partialDeriv j g) := hg.fderiv_apply _ _
    exact (hs (hs hf.2 0) 0).add (hs (hs hf.2 1) 1)

/-- The partial derivatives of the squared Euclidean norm are twice the coordinates. -/
private lemma partial_norm_sq (j : Fin 2) :
    partialDeriv j (fun x : ℝ² ↦ ‖x‖ ^ 2) = fun x ↦ 2 * x j := by
  funext x
  simp [partialDeriv, EuclideanSpace.inner_single_right, two_smul, two_mul]

/-- Each diagonal second derivative of the squared norm is two. -/
private lemma laplacian_norm_sq (x : ℝ²) : laplacian (fun y : ℝ² ↦ ‖y‖ ^ 2) x = 4 := by
  have diag (j : Fin 2) : partialDeriv j (fun y : ℝ² ↦ 2 * y j) x = 2 := by
    let p := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) j
    change fderiv ℝ (fun y ↦ 2 * p y) x _ = 2
    rw [(p.hasFDerivAt.const_mul 2).fderiv]
    simp [p, EuclideanSpace.single]
  norm_num [laplacian, partial_norm_sq, diag]

/-- ΔA_Q = 4 on |x| ≤ Q. -/
theorem laplacian_virialWeight_eq_four {Q : ℝ} (hQ : 0 < Q) {x : ℝ²} (hx : ‖x‖ ≤ Q) :
    laplacian (virialWeight Q) x = 4 := by
  have hball : EqOn (laplacian (virialWeight Q)) (fun _ ↦ 4) (ball 0 Q) := by
    intro y hy
    have h := eventuallyEq_norm_sq hQ (by simpa using hy : ‖y‖ < Q)
    have hp (j : Fin 2) : partialDeriv j (virialWeight Q) =ᶠ[𝓝 y]
        partialDeriv j (fun u : ℝ² ↦ ‖u‖ ^ 2) := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with u hu
      exact congrArg (fun L : ℝ² →L[ℝ] ℝ ↦ L (EuclideanSpace.single j 1)) hu
    rw [← laplacian_norm_sq y]
    exact congrArg₂ (· + ·)
      (congrArg (fun L : ℝ² →L[ℝ] ℝ ↦ L (EuclideanSpace.single 0 1)) (hp 0).fderiv_eq)
      (congrArg (fun L : ℝ² →L[ℝ] ℝ ↦ L (EuclideanSpace.single 1 1)) (hp 1).fderiv_eq)
  apply hball.closure (test_laplacian (virialWeight_isTestFunction hQ)).1.continuous continuous_const
  simpa [closure_ball _ hQ.ne'] using hx

/-- Each coordinate differentiation of a dilated function contributes one dilation factor. -/
private lemma partial_dilate {f : ℝ² → ℝ} (hf : Differentiable ℝ f) (a b : ℝ) (j : Fin 2) :
    partialDeriv j (fun x ↦ a * f (b • x)) = fun x ↦ (a * b) * partialDeriv j f (b • x) := by
  funext x
  have hd := ((hf (b • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul b)).const_mul a
  unfold partialDeriv
  simp only [Function.comp_apply] at hd
  rw [hd.fderiv]
  simp [mul_assoc]

/-- The two derivatives in the Laplacian contribute the square of the dilation factor. -/
private lemma laplacian_dilate {f : ℝ² → ℝ} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    laplacian (fun x ↦ a * f (b • x)) = fun x ↦ (a * b ^ 2) * laplacian f (b • x) := by
  funext x
  unfold laplacian
  simp only [partial_dilate (hf.differentiable (by simp)),
    partial_dilate ((smooth_partial hf _).differentiable (by simp))]
  ring

/-- The weight at scale Q is obtained by dilating the unit-scale weight. -/
private lemma weight_dilate {Q : ℝ} (hQ : 0 < Q) :
    virialWeight Q = fun x ↦ Q ^ 2 * virialWeight 1 (Q⁻¹ • x) := by
  funext x
  simp [virialWeight, norm_smul, Real.norm_eq_abs, abs_of_pos hQ, div_eq_inv_mul]

/-- The Laplacian has scaling degree zero. -/
private lemma laplacian_weight_dilate {Q : ℝ} (hQ : 0 < Q) :
    laplacian (virialWeight Q) = fun x ↦ laplacian (virialWeight 1) (Q⁻¹ • x) := by
  rw [weight_dilate hQ, laplacian_dilate (virialWeight_isTestFunction one_pos).1]
  simp [hQ.ne']

/-- A continuous compactly supported test function has a global absolute bound. -/
private lemma test_abs_bound {f : ℝ² → ℝ} (hf : IsTestFunction f) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := ((hf.2.isCompact_range hf.1.continuous).image continuous_abs).bddAbove
  exact ⟨C, fun x ↦ hC ⟨_, ⟨x, rfl⟩, rfl⟩⟩

/-- ΔA_Q is bounded uniformly in Q. -/
theorem laplacian_virialWeight_bound :
    ∃ C, ∀ Q > 0, ∀ x : ℝ², |laplacian (virialWeight Q) x| ≤ C := by
  obtain ⟨C, hC⟩ := test_abs_bound (test_laplacian (virialWeight_isTestFunction one_pos))
  refine ⟨C, fun Q hQ x ↦ ?_⟩
  rw [laplacian_weight_dilate hQ]
  exact hC _

/-- (4.3) ‖Δ²A_Q‖_∞ ≲ Q⁻². -/
theorem bilaplacian_virialWeight_bound :
    ∃ C, ∀ Q > 0, ∀ x : ℝ², |laplacian (laplacian (virialWeight Q)) x| ≤ C / Q ^ 2 := by
  have hΔ := test_laplacian (virialWeight_isTestFunction one_pos)
  obtain ⟨C, hC⟩ := test_abs_bound (test_laplacian hΔ)
  refine ⟨C, fun Q hQ x ↦ ?_⟩
  rw [laplacian_weight_dilate hQ]
  have scale := laplacian_dilate hΔ.1 1 Q⁻¹
  simp only [one_mul] at scale
  rw [scale, abs_mul, abs_of_nonneg (sq_nonneg _), inv_pow, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

/-- The convex profile deficit attains its minimum at zero, so it is nondecreasing on [0, ∞). -/
private lemma deficit_mono : MonotoneOn (fun r : ℝ ↦ r ^ 2 - φ r) (Ici 0) := by
  intro r hr s _ hrs
  have hmin (u : ℝ) : 0 ≤ u ^ 2 - φ u := sub_nonneg.mpr (profile_spec.le_sq u)
  have hzero := profile_spec.quadratic 0 (by norm_num)
  change 0 ≤ r at hr
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    simpa [hzero] using hmin s
  · apply profile_spec.deficit_convex.le_right_of_left_le'' (mem_univ 0) (mem_univ s) h hrs
    simpa [hzero] using hmin r

/-- Composition of the nondecreasing convex deficit with the scaled norm is convex. -/
private lemma convex_deficit {Q : ℝ} (hQ : 0 < Q) :
    ConvexOn ℝ univ (fun x : ℝ² ↦ ‖x‖ ^ 2 - virialWeight Q x) := by
  let ψ := fun r : ℝ ↦ r ^ 2 - φ r
  have scaled (x : ℝ²) : ‖x‖ ^ 2 - virialWeight Q x = Q ^ 2 * ψ (‖x‖ / Q) := by
    dsimp [virialWeight, ψ]
    field_simp
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [scaled, smul_eq_mul]
  have hn := (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ²))).2 hx hy ha hb hab
  have hm : ψ (‖a • x + b • y‖ / Q) ≤ ψ (a * (‖x‖ / Q) + b * (‖y‖ / Q)) := by
    apply deficit_mono
    · exact div_nonneg (norm_nonneg _) hQ.le
    · exact add_nonneg (mul_nonneg ha (div_nonneg (norm_nonneg _) hQ.le))
        (mul_nonneg hb (div_nonneg (norm_nonneg _) hQ.le))
    · simpa [add_div, mul_div_assoc, smul_eq_mul] using div_le_div_of_nonneg_right hn hQ.le
  have hc := profile_spec.deficit_convex.2 (mem_univ (‖x‖ / Q)) (mem_univ (‖y‖ / Q)) ha hb hab
  have hbnd := mul_le_mul_of_nonneg_left (hm.trans hc) (sq_nonneg Q)
  dsimp only [smul_eq_mul] at hbnd
  linarith only [hbnd]

/-- Real directions expressed in the same coordinate basis used by partialDeriv. -/
private noncomputable def direction (a b : ℝ) : ℝ² :=
  a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1

/-- The derivative along a line is the corresponding linear combination of partials. -/
private lemma hasDerivAt_line {f : ℝ² → ℝ} (hf : Differentiable ℝ f) (x : ℝ²) (a b t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • direction a b))
      (a * partialDeriv 0 f (x + t • direction a b) +
       b * partialDeriv 1 f (x + t • direction a b)) t := by
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • direction a b) (direction a b) t := by
    simpa using (((hasDerivAt_id' t).smul_const (direction a b)).const_add x)
  simpa [Function.comp_def, direction, partialDeriv] using
    (hf _).hasFDerivAt.comp_hasDerivAt t hl

/-- In line coordinates the squared norm is an explicit quadratic polynomial. -/
private lemma norm_sq_line (x : ℝ²) (a b t : ℝ) :
    ‖x + t • direction a b‖ ^ 2 = (x 0 + t * a) ^ 2 + (x 1 + t * b) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, direction, PiLp.add_apply,
    PiLp.smul_apply, EuclideanSpace.single, PiLp.single_apply]

/-- Restricting the planar deficit to an affine line gives a convex function of one variable. -/
private lemma convex_line {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) (a b : ℝ) :
    ConvexOn ℝ univ (fun t : ℝ ↦ ‖x + t • direction a b‖ ^ 2 -
      virialWeight Q (x + t • direction a b)) := by
  simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm x] using
    (convex_deficit hQ).comp_affineMap (AffineMap.lineMap x (x + direction a b))

/-- The derivative of the line deficit splits into the quadratic and weight terms. -/
private lemma hasDerivAt_deficit_line {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) (a b t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ‖x + s • direction a b‖ ^ 2 - virialWeight Q (x + s • direction a b))
      (2 * (x 0 + t * a) * a + 2 * (x 1 + t * b) * b -
        (a * partialDeriv 0 (virialWeight Q) (x + t • direction a b) +
         b * partialDeriv 1 (virialWeight Q) (x + t • direction a b))) t := by
  simp_rw [norm_sq_line]
  have coord (j : Fin 2) (c : ℝ) : HasDerivAt (fun s : ℝ ↦ (x j + s * c) ^ 2)
      (2 * (x j + t * c) * c) t := by
    simpa using ((((hasDerivAt_id' t).mul_const c).const_add (x j)).fun_pow 2)
  exact ((coord 0 a).add (coord 1 b)).sub
    (hasDerivAt_line ((virialWeight_isTestFunction hQ).1.differentiable (by simp)) x a b t)

/-- (4.3) |∇A_Q|² ≤ 4 A_Q. -/
theorem grad_virialWeight_sq_le {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) :
    partialDeriv 0 (virialWeight Q) x ^ 2 + partialDeriv 1 (virialWeight Q) x ^ 2 ≤
      4 * virialWeight Q x := by
  let a := -(partialDeriv 0 (virialWeight Q) x) / 2
  let b := -(partialDeriv 1 (virialWeight Q) x) / 2
  -- Compare the tangent at zero with the secant to the point displaced by −∇A_Q/2.
  have ht := (convex_line hQ x a b).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
    zero_lt_one (hasDerivAt_deficit_line hQ x a b 0)
  simp only [slope_def_field, sub_zero, div_one, norm_sq_line, zero_mul, one_mul, zero_smul,
    one_smul, add_zero] at ht
  dsimp [a, b] at ht
  nlinarith only [ht, virialWeight_nonneg Q (x + direction a b)]

/-- On a real line, monotonicity of the derivative bounds the second derivative of the weight. -/
private lemma hessian_real {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) (a b : ℝ) :
    a * (a * partialDeriv 0 (partialDeriv 0 (virialWeight Q)) x +
         b * partialDeriv 1 (partialDeriv 0 (virialWeight Q)) x) +
    b * (a * partialDeriv 0 (partialDeriv 1 (virialWeight Q)) x +
         b * partialDeriv 1 (partialDeriv 1 (virialWeight Q)) x) ≤ 2 * (a ^ 2 + b ^ 2) := by
  have hd := hasDerivAt_deficit_line hQ x a b
  have hm := monotoneOn_univ.mp ((convex_line hQ x a b).monotoneOn_deriv
    (fun t _ ↦ (hd t).differentiableAt))
  have hn := hm.deriv_nonneg (x := 0)
  rw [funext (fun t ↦ (hd t).deriv)] at hn
  have coord (j : Fin 2) (c : ℝ) :
      HasDerivAt (fun t : ℝ ↦ 2 * (x j + t * c) * c) (2 * c * c) 0 := by
    simpa using (((((hasDerivAt_id' (0 : ℝ)).mul_const c).const_add (x j)).const_mul 2).mul_const c)
  have hp (j : Fin 2) := hasDerivAt_line
    ((smooth_partial (virialWeight_isTestFunction hQ).1 j).differentiable (by simp)) x a b 0
  rw [(((coord 0 a).fun_add (coord 1 b)).fun_sub
    (((hp 0).const_mul a).fun_add ((hp 1).const_mul b))).deriv] at hn
  simp only [zero_smul, add_zero] at hn
  linarith only [hn]

/-- D²A_Q ≤ 2 as a quadratic form (the paper's A_Q'' ≤ 2), tested on complex vectors. -/
theorem hessian_virialWeight_le {Q : ℝ} (hQ : 0 < Q) (x : ℝ²) (z : Fin 2 → ℂ) :
    ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k (virialWeight Q)) x * (z j * starRingEnd ℂ (z k)).re
    ≤ 2 * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) := by
  -- The real and imaginary parts contribute two real quadratic forms.
  simp only [Fin.sum_univ_two, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  linarith only [hessian_real hQ x (z 0).re (z 1).re, hessian_real hQ x (z 0).im (z 1).im]

end Blowup
