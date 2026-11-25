import BlowupFormalization.LocalizedVirial

/-! # Static upper bound for the localized virial expression -/

open MeasureTheory

namespace Blowup

private lemma hessian_integral_le {Q : ℝ} (hQ : 0 < Q) {Du : Fin 2 → ℝ² → ℂ}
    (hDu : ∀ j, MemLp (Du j) 2) :
    (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k (virialWeight Q)) x * (Du j x * starRingEnd ℂ (Du k x)).re)
      ≤ 2 * gradNormSq Du := by
  have hA := virialWeight_isTestFunction hQ
  have hTerm (j k : Fin 2) : Integrable (fun x ↦
      partialDeriv j (partialDeriv k (virialWeight Q)) x *
        (Du j x * starRingEnd ℂ (Du k x)).re) := by
    have hWeight := (hA.partialDeriv k).partialDeriv j
    have hPair : Integrable (fun x ↦ Du j x * starRingEnd ℂ (Du k x)) :=
      (hDu j).integrable_mul (hDu k).star
    exact hPair.re.mul_of_top_right
      (hWeight.1.continuous.memLp_top_of_hasCompactSupport hWeight.2 _)
  have hSum : Integrable (fun x ↦ ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k (virialWeight Q)) x *
        (Du j x * starRingEnd ℂ (Du k x)).re) :=
    integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hTerm j k))
  have hGrad := (hDu 0).norm.integrable_sq.add (hDu 1).norm.integrable_sq
  rw [gradNormSq, ← integral_const_mul]
  exact integral_mono hSum (hGrad.const_mul 2) (fun x ↦ hessian_virialWeight_le hQ x (Du · x))

private lemma neg_laplacian_integral_le {Q B : ℝ} (hQ : 0 < Q)
    (hB : ∀ x, |laplacian (virialWeight Q) x| ≤ B)
    {f : ℝ² → ℝ} (hf : Integrable f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    -(∫ x, laplacian (virialWeight Q) x * f x) ≤
      -4 * (∫ x, f x) + (4 + B) * (∫ x in {x : ℝ² | Q < ‖x‖}, f x) := by
  let exterior : Set ℝ² := {x | Q < ‖x‖}
  have hExterior : MeasurableSet exterior :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hWeight := (virialWeight_isTestFunction hQ).laplacian
  have hΔ : Integrable (fun x ↦ laplacian (virialWeight Q) x * f x) :=
    hf.mul_of_top_right (hWeight.1.continuous.memLp_top_of_hasCompactSupport hWeight.2 _)
  have hPointwise (x : ℝ²) : 4 * f x - laplacian (virialWeight Q) x * f x ≤
      (4 + B) * exterior.indicator f x := by
    by_cases hx : Q < ‖x‖
    · rw [← sub_mul, Set.indicator_of_mem (show x ∈ exterior from hx)]
      have hLower := (neg_le_abs (laplacian (virialWeight Q) x)).trans (hB x)
      exact mul_le_mul_of_nonneg_right (by linarith only [hLower]) (hf_nonneg x)
    · rw [laplacian_virialWeight_eq_four hQ (le_of_not_gt hx),
        Set.indicator_of_notMem (show x ∉ exterior from hx), sub_self, mul_zero]
  have h := integral_mono ((hf.const_mul 4).sub hΔ)
    ((hf.integrableOn.integrable_indicator hExterior).const_mul (4 + B)) hPointwise
  rw [integral_sub' (hf.const_mul 4) hΔ, integral_const_mul, integral_const_mul,
    integral_indicator hExterior] at h
  change _ ≤ -4 * (∫ x, f x) + (4 + B) * (∫ x in exterior, f x)
  linarith only [h]

private lemma neg_bilaplacian_integral_le {Q D : ℝ} (hQ : 0 < Q)
    (hD : ∀ x, |laplacian (laplacian (virialWeight Q)) x| ≤ D / Q ^ 2)
    {u : ℝ² → ℂ} (hu : MemLp u 2) :
    -(∫ x, laplacian (laplacian (virialWeight Q)) x * ‖u x‖ ^ 2) ≤
      D * mass u / Q ^ 2 := by
  have hDensity := hu.norm.integrable_sq
  have hWeight := (virialWeight_isTestFunction hQ).laplacian.laplacian
  have hWeighted := hDensity.mul_of_top_right
    (hWeight.1.continuous.memLp_top_of_hasCompactSupport hWeight.2 _)
  rw [← integral_neg]
  calc
    _ ≤ ∫ x, (D / Q ^ 2) * ‖u x‖ ^ 2 := by
      refine integral_mono hWeighted.neg (hDensity.const_mul _) (fun x ↦ ?_)
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (hD x)) (sq_nonneg _)
    _ = D * mass u / Q ^ 2 := by
      rw [integral_const_mul, mass]
      ring

/-- The right-hand side of (4.5) satisfies the static bound underlying (4.6). -/
theorem virialSecondDeriv_virialWeight_le :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {p Q : ℝ} {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ},
        3 ≤ p → 0 < Q → MemLp u 2 → (∀ j, MemLp (Du j) 2) →
        Integrable (fun x ↦ ‖u x‖ ^ (p + 1)) →
        virialSecondDeriv p (virialWeight Q) u Du ≤
          8 * (p - 1) * energy p u Du - 4 * (p - 3) * gradNormSq Du +
          (2 * (p - 1) / (p + 1)) * C * (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u x‖ ^ (p + 1)) +
          D * mass u / Q ^ 2 := by
  obtain ⟨B, hB⟩ := laplacian_virialWeight_bound
  obtain ⟨D, hD⟩ := bilaplacian_virialWeight_bound
  have hB_nonneg : 0 ≤ B := (abs_nonneg _).trans (hB 1 one_pos 0)
  have hD_nonneg : 0 ≤ D := by
    simpa using (abs_nonneg _).trans (hD 1 one_pos 0)
  refine ⟨4 + B, D, by positivity, hD_nonneg, ?_⟩
  intro p Q u Du hp hQ hu hDu hPotential
  let a := 2 * (p - 1) / (p + 1)
  have ha : 0 ≤ a := div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hHess := hessian_integral_le hQ hDu
  have hLap := neg_laplacian_integral_le hQ (hB Q hQ) hPotential
    (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hBilap := neg_bilaplacian_integral_le hQ (hD Q hQ) hu
  unfold virialSecondDeriv
  calc
    _ ≤ 8 * gradNormSq Du + a * (-4 * potentialTerm p u +
        (4 + B) * (∫ x in {x : ℝ² | Q < ‖x‖}, ‖u x‖ ^ (p + 1))) +
        D * mass u / Q ^ 2 := by
      have hLap' := mul_le_mul_of_nonneg_left hLap ha
      unfold potentialTerm
      change 4 * _ - a * _ - _ ≤ _
      linarith only [hHess, hLap', hBilap]
    _ = _ := by
      unfold energy
      dsimp only [a]
      ring

end Blowup
