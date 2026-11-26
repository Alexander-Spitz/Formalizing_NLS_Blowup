import BlowupFormalization.LocalizedVirial

/-! # Static upper bound for the localized virial expression -/

open MeasureTheory

namespace Blowup

private lemma integrable_hessian_pairing {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {Du : Fin 2 → ℝ² → ℂ} (hDu : ∀ j, MemLp (Du j) 2) :
    Integrable (fun x ↦ ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k A) x * (Du j x * starRingEnd ℂ (Du k x)).re) := by
  have hTerm (j k : Fin 2) : Integrable (fun x ↦
      partialDeriv j (partialDeriv k A) x *
        (Du j x * starRingEnd ℂ (Du k x)).re) := by
    have hWeight := (hA.partialDeriv k).partialDeriv j
    have hPair : Integrable (fun x ↦ Du j x * starRingEnd ℂ (Du k x)) :=
      (hDu j).integrable_mul (hDu k).star
    exact hPair.re.mul_of_top_right
      (hWeight.1.continuous.memLp_top_of_hasCompactSupport hWeight.2 _)
  exact integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hTerm j k))

private lemma hessian_integral_le {Q : ℝ} (hQ : 0 < Q) {Du : Fin 2 → ℝ² → ℂ}
    (hDu : ∀ j, MemLp (Du j) 2) :
    (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k (virialWeight Q)) x * (Du j x * starRingEnd ℂ (Du k x)).re)
      ≤ 2 * gradNormSq Du := by
  have hSum := integrable_hessian_pairing (virialWeight_isTestFunction hQ) hDu
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

private lemma neg_bilaplacian_integral_le {A : ℝ² → ℝ} (hA : IsTestFunction A)
    {D : ℝ}
    (hD : ∀ x, |laplacian (laplacian A) x| ≤ D)
    {u : ℝ² → ℂ} (hu : MemLp u 2) :
    -(∫ x, laplacian (laplacian A) x * ‖u x‖ ^ 2) ≤
      D * mass u := by
  have hDensity := hu.norm.integrable_sq
  have hWeight := hA.laplacian.laplacian
  have hWeighted := hDensity.mul_of_top_right
    (hWeight.1.continuous.memLp_top_of_hasCompactSupport hWeight.2 _)
  rw [← integral_neg]
  calc
    _ ≤ ∫ x, (D) * ‖u x‖ ^ 2 := by
      refine integral_mono hWeighted.neg (hDensity.const_mul _) (fun x ↦ ?_)
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (hD x)) (sq_nonneg _)
    _ = D * mass u := by rw [integral_const_mul, mass]

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
  have hBilap := neg_bilaplacian_integral_le (virialWeight_isTestFunction hQ) (hD Q hQ) hu
  rw [div_mul_eq_mul_div] at hBilap
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

/-- At the cubic exponent the Hessian deficit supplies a weighted negative kinetic term.
The Laplacian deficit costs the corresponding weighted fourth power of the field. -/
theorem virialSecondDeriv_cubic_le_of_cutoff {A W : ℝ² → ℝ}
    (hA : IsTestFunction A) (hW : Continuous W) (hW₀ : ∀ x, 0 ≤ W x) (hW₁ : ∀ x, W x ≤ 1)
    {B D : ℝ}
    (hHessian : ∀ x (z : Fin 2 → ℂ),
      ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
        (z j * starRingEnd ℂ (z k)).re ≤
          2 * (1 - W x ^ 2) * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2))
    (hLaplacian : ∀ x, 4 - laplacian A x ≤ B * W x)
    (hBilaplacian : ∀ x, |laplacian (laplacian A) x| ≤ D)
    {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hF : Integrable (fun x ↦ ‖u x‖ ^ (4 : ℝ))) :
    virialSecondDeriv 3 A u Du ≤
      16 * energy 3 u Du -
        8 * (∫ x, W x ^ 2 * (‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2)) +
        B * (∫ x, W x * ‖u x‖ ^ (4 : ℝ)) + D * mass u := by
  let K (x : ℝ²) := ‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2
  let F (x : ℝ²) := ‖u x‖ ^ (4 : ℝ)
  have hK : Integrable K := (hu.memL2_partial 0).norm.integrable_sq.add
    (hu.memL2_partial 1).norm.integrable_sq
  have hWtop : MemLp W ⊤ := memLp_top_of_bound hW.aestronglyMeasurable 1
    (.of_forall fun x ↦ by rw [Real.norm_of_nonneg (hW₀ x)]; exact hW₁ x)
  have hWsq : MemLp (fun x ↦ W x ^ 2) ⊤ := memLp_top_of_bound
    (hW.pow 2).aestronglyMeasurable 1 (.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith only [hW₀ x, hW₁ x, mul_nonneg (hW₀ x) (sub_nonneg.mpr (hW₁ x))])
  have hWK : Integrable (fun x ↦ W x ^ 2 * K x) := hK.mul_of_top_right hWsq
  have hWF : Integrable (fun x ↦ W x * F x) := hF.mul_of_top_right hWtop
  have hHess :
      (∫ x, ∑ j : Fin 2, ∑ k : Fin 2, partialDeriv j (partialDeriv k A) x *
        (Du j x * starRingEnd ℂ (Du k x)).re) ≤
          2 * (gradNormSq Du - ∫ x, W x ^ 2 * K x) := by
    calc
      _ ≤ ∫ x, 2 * (K x - W x ^ 2 * K x) := by
        refine integral_mono (integrable_hessian_pairing hA hu.memL2_partial)
          ((hK.sub hWK).const_mul 2) (fun x ↦ ?_)
        exact (hHessian x (fun j ↦ Du j x)).trans_eq (by dsimp [K]; ring)
      _ = _ := by
        rw [integral_const_mul, integral_sub hK hWK]
        rfl
  have hΔ : Integrable (fun x ↦ laplacian A x * F x) := hF.mul_of_top_right
    (hA.laplacian.1.continuous.memLp_top_of_hasCompactSupport hA.laplacian.2 _)
  have hLap : -(∫ x, laplacian A x * F x) ≤
      -4 * (∫ x, F x) + B * (∫ x, W x * F x) := by
    have h := integral_mono ((hF.const_mul 4).sub hΔ) (hWF.const_mul B) (fun x ↦ by
      change 4 * F x - laplacian A x * F x ≤ B * (W x * F x)
      rw [← sub_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hLaplacian x) (Real.rpow_nonneg (norm_nonneg _) _))
    rw [integral_sub' (hF.const_mul 4) hΔ, integral_const_mul, integral_const_mul] at h
    linarith only [h]
  have hBilap := neg_bilaplacian_integral_le hA hBilaplacian hu.memL2
  unfold virialSecondDeriv energy potentialTerm
  simp only [show (3 : ℝ) + 1 = 4 by norm_num,
    show (2 : ℝ) * (3 - 1) / 4 = 1 by norm_num, one_mul]
  change 4 * _ - (∫ x, laplacian A x * F x) - _ ≤
    16 * (gradNormSq Du / 2 - (∫ x, F x) / 4) - 8 * (∫ x, W x ^ 2 * K x) +
      B * (∫ x, W x * F x) + D * mass u
  linarith only [hHess, hLap, hBilap]

end Blowup
