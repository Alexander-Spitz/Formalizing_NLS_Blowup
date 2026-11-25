module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exponents for the exterior evolution

The real exponent identities in (3.1), together with the arithmetic used in
(3.2), Lemma 3.1, and the fractional product and chain rules in Proposition 3.2.
-/

@[expose] public section

namespace Blowup.ExteriorExponents

/-- The fractional derivative order for the exterior evolution. -/
noncomputable def sigma (p : ℝ) : ℝ := 1 / 2 - 2 / (p - 1)

/-- The spatial Strichartz exponent paired with time exponent `p`. -/
noncomputable def r (p : ℝ) : ℝ := 2 * p / (p - 4)

/-- The time exponent for the point-source term. -/
noncomputable def q (p : ℝ) : ℝ := 2 * (p - 1) / (p + 1)

/-- The spatial Sobolev exponent paired with time exponent `∞` in (3.2). -/
noncomputable def m (p : ℝ) : ℝ := (p - 1) / 2

/-- The spatial Sobolev exponent paired with time exponent `p` in (3.2). -/
noncomputable def b (p : ℝ) : ℝ := p * (p - 1) / 2

/-- The exponent `ℓ` for the fractional derivatives of the coefficients in (3.13). -/
noncomputable def ell (p : ℝ) : ℝ := 1 / sigma p

variable {p : ℝ}

theorem sigma_pos (hp : 5 < p) : 0 < sigma p := by
  have hden : 0 < p - 1 := by linarith
  rw [sigma, sub_pos, div_lt_iff₀ hden]
  linarith

theorem sigma_lt_half (hp : 5 < p) : sigma p < 1 / 2 := by
  have hden : 0 < p - 1 := by linarith
  have hdiv : 0 < 2 / (p - 1) := div_pos (by norm_num) hden
  rw [sigma]
  linarith

theorem two_lt_r (hp : 5 < p) : 2 < r p := by
  have hden : 0 < p - 4 := by linarith
  rw [r, lt_div_iff₀ hden]
  linarith

theorem one_lt_q (hp : 5 < p) : 1 < q p := by
  have hden : 0 < p + 1 := by linarith
  rw [q, lt_div_iff₀ hden]
  linarith

theorem q_lt_two (hp : 5 < p) : q p < 2 := by
  have hden : 0 < p + 1 := by linarith
  rw [q, div_lt_iff₀ hden]
  linarith

theorem q_lt_p (hp : 5 < p) : q p < p :=
  (q_lt_two hp).trans (by linarith)

theorem two_lt_m (hp : 5 < p) : 2 < m p := by
  rw [m]
  linarith

theorem b_eq_p_mul_m (p : ℝ) : b p = p * m p := by
  unfold b m
  ring

theorem m_lt_b (hp : 5 < p) : m p < b p := by
  have hm : 0 < m p := lt_trans (by norm_num) (two_lt_m hp)
  calc
    m p = 1 * m p := (one_mul _).symm
    _ < p * m p := mul_lt_mul_of_pos_right (by linarith) hm
    _ = b p := (b_eq_p_mul_m p).symm

theorem one_lt_b (hp : 5 < p) : 1 < b p :=
  (show (1 : ℝ) < 2 by norm_num).trans ((two_lt_m hp).trans (m_lt_b hp))

theorem two_lt_ell (hp : 5 < p) : 2 < ell p := by
  rw [ell, lt_div_iff₀ (sigma_pos hp)]
  linarith [sigma_lt_half hp]

/-- The first spatial Sobolev relation in (3.2). -/
theorem one_div_m (p : ℝ) : 1 / m p = 1 / 2 - sigma p := by
  rw [m, one_div_div, sigma]
  ring

/-- The second spatial Sobolev relation in (3.2). -/
theorem one_div_b (hp : 5 < p) : 1 / b p = 1 / r p - sigma p := by
  have hp0 : p ≠ 0 := by linarith
  have hden : p - 1 ≠ 0 := by linarith
  rw [b, r, one_div_div, one_div_div, sigma]
  field_simp [hp0, hden]
  ring

/-- The finite-exponent one-dimensional Schrödinger admissibility conditions of §2. -/
theorem schrodinger_admissible (hp : 5 < p) :
    4 ≤ p ∧ 2 ≤ r p ∧ 2 / p + 1 / r p = 1 / 2 := by
  refine ⟨by linarith, (two_lt_r hp).le, ?_⟩
  have hp0 : p ≠ 0 := by linarith
  rw [r, one_div_div]
  field_simp [hp0]
  ring

/-- The Fourier weight exponent after the change of variables in (3.4). -/
theorem sigma_sub_half (p : ℝ) : sigma p - 1 / 2 = -(2 / (p - 1)) := by
  unfold sigma
  ring

/-- The exponent relation for fractional integration and Hölder in Lemma 3.1. -/
theorem one_div_q_sub_half (hp : 5 < p) :
    1 / q p - 1 / 2 = 1 / (p - 1) := by
  have hden : p - 1 ≠ 0 := by linarith
  rw [q, one_div_div]
  field_simp [hden]
  ring

/-- The fractional product rule uses `1 / ℓ + 1 / m = 1 / 2`. -/
theorem product_rule_exponents (p : ℝ) : 1 / ell p + 1 / m p = 1 / 2 := by
  rw [ell, one_div_div, div_one, one_div_m]
  ring

/-- The fractional chain rule uses `(p - 1) / b + 1 / r = 1 / 2`. -/
theorem chain_rule_exponents (hp : 5 < p) : (p - 1) / b p + 1 / r p = 1 / 2 := by
  have hb : (p - 1) / b p = 2 / p := by
    have hp0 : p ≠ 0 := by linarith
    have hden : p - 1 ≠ 0 := by linarith
    rw [b]
    field_simp [hp0, hden]
  rw [hb]
  exact (schrodinger_admissible hp).2.2

end Blowup.ExteriorExponents
