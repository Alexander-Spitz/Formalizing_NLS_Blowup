import Mathlib

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

end Blowup
