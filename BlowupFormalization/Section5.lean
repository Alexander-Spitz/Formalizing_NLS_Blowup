import BlowupFormalization.Calculus

/-! # Scalar estimates for the scale and virial argument in Section 5 -/

namespace Blowup

/-- The two summands of `ε` in (3.5) are small at the scales of (5.7):
if `S ≥ (2h/η)²`, `S ≥ M/g`, `F ≥ gT`, `T ≥ 1` and `T F/S² ≤ η²/8`, then
`S^{-1/2} h + T^{1/(p-1)} (F/S² + M T/S⁴)^{1/2} ≤ η`. -/
theorem eps_le_of_scales {p T S h F M g η : ℝ} (hp : 3 ≤ p) (hT : 1 ≤ T) (hS : 1 ≤ S)
    (hg : 0 < g) (hF : g * T ≤ F) (hM : 0 ≤ M) (hSM : M / g ≤ S) (hη : 0 < η) (hh : 0 ≤ h)
    (hSh : (2 * h / η) ^ 2 ≤ S) (hTF : T * F / S ^ 2 ≤ η ^ 2 / 8) :
    S ^ (-(1 : ℝ) / 2) * h + T ^ (1 / (p - 1)) * Real.sqrt (F / S ^ 2 + M * T / S ^ 4) ≤ η := by
  have hS0 : 0 < S := by linarith
  have hsqS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  -- first summand: `S^{-1/2} h ≤ η/2`
  have h1 : S ^ (-(1 : ℝ) / 2) * h ≤ η / 2 := by
    have hpow : S ^ (-(1 : ℝ) / 2) = (Real.sqrt S)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hS0.le]; congr 1; ring
    have hle : 2 * h / η ≤ Real.sqrt S := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * h / η)]; exact Real.sqrt_le_sqrt hSh
    rw [hpow, inv_mul_le_iff₀ hsqS]
    rw [div_le_iff₀ hη] at hle
    linarith
  -- second summand: `T^{1/(p-1)} (F/S² + MT/S⁴)^{1/2} ≤ (2 T F/S²)^{1/2} ≤ η/2`
  have h2 : T ^ (1 / (p - 1)) * Real.sqrt (F / S ^ 2 + M * T / S ^ 4) ≤ η / 2 := by
    have hFpos : 0 ≤ F := le_trans (by positivity) hF
    have hMgS : M ≤ g * S ^ 2 := by
      rw [div_le_iff₀ hg] at hSM; nlinarith
    have hX : F / S ^ 2 + M * T / S ^ 4 ≤ 2 * F / S ^ 2 := by
      have : M * T / S ^ 4 ≤ F / S ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : M * T ≤ F * S ^ 2 := by nlinarith
        nlinarith [sq_nonneg S]
      linarith [show 2 * F / S ^ 2 = F / S ^ 2 + F / S ^ 2 by ring]
    have hTpow : T ^ (1 / (p - 1)) ≤ Real.sqrt T := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_le hT
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    calc T ^ (1 / (p - 1)) * Real.sqrt (F / S ^ 2 + M * T / S ^ 4)
        ≤ Real.sqrt T * Real.sqrt (2 * F / S ^ 2) :=
          mul_le_mul hTpow (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * (T * F / S ^ 2)) := by
          rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
      _ ≤ Real.sqrt ((η / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = η / 2 := Real.sqrt_sq (by linarith)
  linarith

/-- The arithmetic of **(5.5)**: if `V(0) ≤ I/c`, `V'(0)² ≤ 16 G(0)² V(0)` (4.7),
`T² ≤ 2I/g` (5.2) and `c` satisfies (5.4), then `V(0) + T V'(0) ≤ (p-3) I`. -/
theorem eq_5_5 {p V₀ V₁ T I K₀ g c : ℝ} (hp3 : 0 < p - 3) (hg : 0 < g) (hI : 0 ≤ I)
    (hK₀ : 0 ≤ K₀) (hc1 : 2 / (p - 3) ≤ c) (hc2 : 128 * K₀ / (g * (p - 3) ^ 2) ≤ c)
    (hV₀ : V₀ ≤ I / c) (hV₀nn : 0 ≤ V₀) (hV₁ : V₁ ^ 2 ≤ 16 * K₀ * V₀) (hT : T ^ 2 ≤ 2 * I / g) :
    V₀ + T * V₁ ≤ (p - 3) * I := by
  have hc : 0 < c := lt_of_lt_of_le (div_pos two_pos hp3) hc1
  have hIc : I / c ≤ (p - 3) / 2 * I := by
    calc I / c ≤ I / (2 / (p - 3)) := div_le_div_of_nonneg_left hI (div_pos two_pos hp3) hc1
      _ = (p - 3) / 2 * I := by field_simp
  have h128 : 128 * K₀ ≤ c * (g * (p - 3) ^ 2) := by
    rwa [div_le_iff₀ (by positivity)] at hc2
  have hsq : (T * V₁) ^ 2 ≤ ((p - 3) / 2 * I) ^ 2 := by
    calc (T * V₁) ^ 2 = T ^ 2 * V₁ ^ 2 := by ring
      _ ≤ (2 * I / g) * (16 * K₀ * (I / c)) := by
          apply mul_le_mul hT (hV₁.trans (by gcongr)) (sq_nonneg _) (by positivity)
      _ = 32 * K₀ * I ^ 2 / (g * c) := by field_simp; ring
      _ ≤ ((p - 3) / 2 * I) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right h128 (sq_nonneg I), sq_nonneg I]
  have hTV : T * V₁ ≤ (p - 3) / 2 * I := by
    have hnn : 0 ≤ (p - 3) / 2 * I := by positivity
    nlinarith [sq_nonneg (T * V₁ - (p - 3) / 2 * I), sq_nonneg (T * V₁ + (p - 3) / 2 * I)]
  linarith

/-- The bound (5.8) and the initial estimate (5.5) force the localized variance to be
strictly negative at time T. Here K is the squared gradient norm along the solution. -/
theorem terminal_virial_neg {p e T : ℝ} {V V₁ V₂ K : ℝ → ℝ}
    (hp : 3 ≤ p) (he : 0 < e) (hT : 0 < T)
    (hK : ContinuousOn K (Set.Icc 0 T)) (hK_nonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ K t)
    (hV : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt V (V₁ t) (Set.Icc 0 T) t)
    (hV₁ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt V₁ (V₂ t) (Set.Icc 0 T) t)
    (hV₂ : ∀ t ∈ Set.Icc 0 T, V₂ t ≤ -4 * (p - 1) * e - 2 * (p - 3) * K t)
    (hInitial : V 0 + T * |V₁ 0| ≤ (p - 3) * (∫ s in 0..T, (T - s) * K s)) :
    V T < 0 := by
  -- Extend K continuously by its endpoint values to use the integral derivative lemmas.
  let k (t : ℝ) := K (min T (max 0 t))
  have hk : Continuous k := hK.comp_continuous
    (continuous_const.min (continuous_const.max continuous_id'))
    (fun t ↦ ⟨le_min hT.le (le_max_left 0 t), min_le_left T _⟩)
  have hAgreement (t : ℝ) (ht : t ∈ Set.Icc 0 T) : k t = K t := by
    simp only [k, max_eq_right ht.1, min_eq_right ht.2]
  have hIntegral : (∫ s in 0..T, (T - s) * k s) = ∫ s in 0..T, (T - s) * K s := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hT.le]
    intro s hs
    exact congrArg ((T - s) * ·) (hAgreement s hs)
  let a := 2 * (p - 1) * e
  let b := 2 * (p - 3)
  -- Add the double integral of the negative acceleration bound to obtain a concave function.
  let W (t : ℝ) := V t + a * t ^ 2 + b * (∫ s in 0..t, (t - s) * k s)
  let W₁ (t : ℝ) := V₁ t + 2 * a * t + b * (∫ s in 0..t, k s)
  have hQuadratic (t : ℝ) : HasDerivAt (fun s ↦ a * s ^ 2) (2 * a * t) t := by
    convert ((hasDerivAt_id' t).pow 2).const_mul a using 1
    ring
  have hW (t : ℝ) (ht : t ∈ Set.Icc 0 T) : HasDerivWithinAt W (W₁ t) (Set.Icc 0 T) t :=
    ((hV t ht).add (hQuadratic t).hasDerivWithinAt).add
      ((hasDerivAt_weighted_integral hk t).const_mul b).hasDerivWithinAt
  have hW₁ (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      HasDerivWithinAt W₁ (V₂ t + 2 * a + b * k t) (Set.Icc 0 T) t := by
    have hLinear : HasDerivAt (fun s ↦ 2 * a * s) (2 * a) t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul (2 * a)
    exact ((hV₁ t ht).add hLinear.hasDerivWithinAt).add
      ((hasDerivAt_integral_zero hk t).const_mul b).hasDerivWithinAt
  have hTangent := le_tangent_of_second_deriv_nonpos hT.le hW hW₁ (fun t ht ↦ by
    rw [hAgreement t ht]
    dsimp only [a, b]
    linarith only [hV₂ t ht])
  norm_num [W, W₁, hIntegral] at hTangent
  have hInitial' : V 0 + T * V₁ 0 ≤ (p - 3) * (∫ s in 0..T, (T - s) * K s) :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) hT.le)).trans hInitial
  have hWeighted_nonneg : 0 ≤ ∫ s in 0..T, (T - s) * K s :=
    intervalIntegral.integral_nonneg hT.le
      (fun s hs ↦ mul_nonneg (sub_nonneg.mpr hs.2) (hK_nonneg s hs))
  have hLoss := mul_nonneg (sub_nonneg.mpr hp) hWeighted_nonneg
  have hp' : 0 < p - 1 := by linarith
  have hStrict : 0 < a * T ^ 2 := by
    dsimp only [a]
    positivity
  dsimp only [b] at hTangent
  linarith only [hTangent, hInitial', hLoss, hStrict]

end Blowup
