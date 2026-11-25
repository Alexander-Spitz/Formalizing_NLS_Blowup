import BlowupFormalization.LocalizedVirial

/-! # Continuity of the localized variance and first virial expression -/

open MeasureTheory
open scoped ENNReal

namespace Blowup

/-- A real test function is an essentially bounded complex coefficient. -/
theorem testFunction_memLp_top_complex {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    MemLp (fun x ↦ (A x : ℂ)) ∞ :=
  (Complex.continuous_ofReal.comp hA.1.continuous).memLp_top_of_hasCompactSupport
    (hA.2.comp_left Complex.ofReal_zero) volume

/-- The product of two L² functions with an L∞ coefficient is integrable. -/
theorem integrable_weighted_pairing {a f g : ℝ² → ℂ}
    (ha : MemLp a ∞) (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun x ↦ starRingEnd ℂ (f x) * (a x * g x)) :=
  hf.star.integrable_mul (ha.mul (r := 2) hg)

/-- A weighted spatial pairing is the L² inner product after Hölder multiplication
by the bounded coefficient. -/
theorem weighted_pairing_eq_inner {a f g : ℝ² → ℂ}
    (ha : MemLp a ∞) (hf : MemLp f 2) (hg : MemLp g 2) :
    inner ℂ (hf.toLp f)
      ((ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure ℝ²) ∞ 2 2
        (ha.toLp a) (hg.toLp g)) =
        ∫ x, starRingEnd ℂ (f x) * (a x * g x) := by
  let A := ha.toLp a
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure ℝ²) ∞ 2 2 A
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, ha.coeFn_toLp, hg.coeFn_toLp,
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) A (hg.toLp g)] with x hfx hax hgx hM
  change inner ℂ (hf.toLp f x) ((M (hg.toLp g)) x) = starRingEnd ℂ (f x) * (a x * g x)
  change (M (hg.toLp g)) x = A x * (hg.toLp g) x at hM
  change A x = a x at hax
  rw [RCLike.inner_apply', hfx, hM, hax, hgx]

private lemma continuous_weighted_pairing {X : Type*} [TopologicalSpace X]
    {a : ℝ² → ℂ} (ha : MemLp a ∞) {f g : X → ℝ² → ℂ}
    (hf : ∀ t, MemLp (f t) 2) (hg : ∀ t, MemLp (g t) 2)
    (hf_cont : Continuous (fun t ↦ (hf t).toLp (f t)))
    (hg_cont : Continuous (fun t ↦ (hg t).toLp (g t))) :
    Continuous (fun t ↦ ∫ x, starRingEnd ℂ (f t x) * (a x * g t x)) := by
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure ℝ²) ∞ 2 2 (ha.toLp a)
  exact (hf_cont.inner (𝕜 := ℂ) (M.continuous.comp hg_cont)).congr
    (fun t ↦ weighted_pairing_eq_inner ha (hf t) (hg t))

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- The localized variance (4.2) is continuous on the solution's time domain. -/
theorem IsNLSSolution.continuousOn_localizedVariance (h : IsNLSSolution p J u Du)
    {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    ContinuousOn (fun t ↦ ∫ x, A x * ‖u t x‖ ^ 2) J := by
  rw [continuousOn_iff_continuous_domRestrict]
  have ha := testFunction_memLp_top_complex hA
  have hu (t : J) := (h.h1 t t.property).memL2
  have hc := continuous_weighted_pairing (f := fun t : J ↦ u t) (g := fun t : J ↦ u t)
    ha hu hu h.continuous_toLp h.continuous_toLp
  apply (Complex.continuous_re.comp hc).congr
  intro t
  have hInt := integrable_weighted_pairing ha (hu t) (hu t)
  refine (integral_re hInt).symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_))
  change (starRingEnd ℂ (u t x) * ((A x : ℂ) * u t x)).re = A x * ‖u t x‖ ^ 2
  rw [mul_left_comm, mul_comm (starRingEnd ℂ (u t x)), Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.ofReal_re]

/-- The expression on the right of (4.4) is continuous on the solution's time domain. -/
theorem IsNLSSolution.continuousOn_virialFirstDeriv (h : IsNLSSolution p J u Du)
    {A : ℝ² → ℝ} (hA : IsTestFunction A) :
    ContinuousOn (fun t ↦ virialFirstDeriv A (u t) (Du t)) J := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a (j : Fin 2) (x : ℝ²) : ℂ := Complex.ofReal (partialDeriv j A x)
  let F (j : Fin 2) (t : J) (x : ℝ²) := starRingEnd ℂ (u t x) * (a j x * Du t j x)
  have ha (j : Fin 2) : MemLp (a j) ∞ := testFunction_memLp_top_complex (hA.partialDeriv j)
  have hu (t : J) := (h.h1 t t.property).memL2
  have hDu (j : Fin 2) (t : J) := (h.h1 t t.property).memL2_partial j
  have hCont (j : Fin 2) : Continuous (fun t ↦ ∫ x, F j t x) :=
    continuous_weighted_pairing (f := fun t : J ↦ u t) (g := fun t : J ↦ Du t j)
      (ha j) hu (hDu j) h.continuous_toLp (h.continuous_grad_toLp j)
  have hTwo : Continuous (fun _ : J ↦ (2 : ℝ)) := continuous_const
  apply (hTwo.mul (Complex.continuous_im.comp ((hCont 0).add (hCont 1)))).congr
  intro t
  have hInt (j : Fin 2) : Integrable (F j t) := integrable_weighted_pairing (ha j) (hu t) (hDu j t)
  change 2 * ((∫ x, F 0 t x) + (∫ x, F 1 t x)).im = virialFirstDeriv A (u t) (Du t)
  have hIm : (∫ x, F 0 t x + F 1 t x).im = ∫ x, (F 0 t x + F 1 t x).im :=
    (integral_im ((hInt 0).add (hInt 1))).symm
  rw [← integral_add (hInt 0) (hInt 1), hIm]
  unfold virialFirstDeriv
  simp only [F, a, mul_add]

end Blowup
