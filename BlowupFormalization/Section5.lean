import BlowupFormalization.LocalizedVirial
import BlowupFormalization.ExteriorEstimate
import BlowupFormalization.ScaleSelection
import BlowupFormalization.Calculus

/-!
# Section 5: no global forward solution

We prove that a radial `H¹` solution with negative energy cannot exist on `[0, ∞)`.

* `finite_variance_contradiction`: the case `|x| u₀ ∈ L²`, via the classical virial identity.
* `infinite_variance_contradiction`: the case `|x| u₀ ∉ L²`. This follows the paper: the
  localized virial identity at the scales `(T, S)` chosen in (5.7), the exterior estimate
  (Proposition 3.2), and the concavity argument after (5.8).
-/

open MeasureTheory Filter

namespace Blowup

variable {p : ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- The quadratic tail `a T² > b + c T` eventually holds for `a > 0`. -/
private lemma exists_large_T {a b c : ℝ} (ha : 0 < a) :
    ∃ T > 0, b + c * T < a * T ^ 2 := by
  have hq : 0 ≤ (|b| + |c|) / a := by positivity
  refine ⟨1 + (|b| + |c|) / a, by linarith, ?_⟩
  set T := 1 + (|b| + |c|) / a
  have hT : 1 ≤ T := by simp only [T]; linarith
  have haT : a * T = a + |b| + |c| := by simp only [T]; field_simp; ring
  have h1 : c * T ≤ |c| * T := mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith)
  have h2 : b ≤ |b| * T := by nlinarith [abs_nonneg b, le_abs_self b]
  have h3 : a * T ^ 2 = (a + |b| + |c|) * T := by rw [sq, ← mul_assoc, haT]
  nlinarith

/-- **The finite-variance case** ("For finite-variance data, the conclusion follows from the
usual virial identity"): `V'' = 8(p−1)E − 4(p−3)‖∇u‖² ≤ 8(p−1)E < 0` forces `V < 0`. -/
theorem finite_variance_contradiction (hp : 3 < p) (hsol : IsNLSSolution p (Set.Ici 0) u Du)
    (hE : energy p (u 0) (Du 0) < 0)
    (hvar : Integrable (fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2)) : False := by
  have hp1 : 1 < p := by linarith
  set E := energy p (u 0) (Du 0)
  set V : ℝ → ℝ := fun s ↦ ∫ x, ‖x‖ ^ 2 * ‖u s x‖ ^ 2
  set V' : ℝ → ℝ := fun s ↦ 4 * ∫ x,
    (starRingEnd ℂ (u s x) * ((x 0 : ℂ) * Du s 0 x + (x 1 : ℂ) * Du s 1 x)).im
  obtain ⟨T, hT, hTbig⟩ := exists_large_T (a := -(4 * (p - 1) * E)) (b := V 0) (c := V' 0)
    (by nlinarith)
  have hsolT := hsol.mono (Set.Icc_subset_Ici_self : Set.Icc 0 T ⊆ Set.Ici 0)
  have hvir := classical_virial hp1 hsolT hvar
  -- `W(t) = V(t) - 4(p-1)E t²` is concave on `[0, T]`.
  have hW := le_tangent_of_second_deriv_nonpos hT.le
    (f := fun s ↦ V s - 4 * (p - 1) * E * s ^ 2)
    (f' := fun s ↦ V' s - 8 * (p - 1) * E * s)
    (f'' := fun s ↦ (8 * gradNormSq (Du s) - 8 * (p - 1) / (p + 1) * potentialTerm p (u s))
      - 8 * (p - 1) * E)
    (fun t ht ↦ by
      have := (hvir t ht).1.sub ((hasDerivWithinAt_pow 2 t (s := Set.Icc 0 T)).const_mul
        (4 * (p - 1) * E))
      convert this using 1; push_cast; ring)
    (fun t ht ↦ by
      have := (hvir t ht).2.sub ((hasDerivWithinAt_id t (Set.Icc 0 T)).const_mul
        (8 * (p - 1) * E))
      convert this using 1
      · funext s; simp [V']
      · ring)
    (fun t ht ↦ by
      -- energy conservation: `pot/(p+1) = ‖∇u‖²/2 − E`
      have hcons := (conservation_laws hp1 hsolT t ht).2
      have hK : 0 ≤ gradNormSq (Du t) := integral_nonneg fun _ ↦ by positivity
      simp only [energy] at hcons
      have hpp : (0 : ℝ) < p + 1 := by linarith
      have : 8 * (p - 1) / (p + 1) * potentialTerm p (u t) =
          8 * (p - 1) * (potentialTerm p (u t) / (p + 1)) := by ring
      rw [this]
      have hpot : potentialTerm p (u t) / (p + 1) = gradNormSq (Du t) / 2 - E := by
        simp only [E, energy]; linarith
      rw [hpot]
      nlinarith)
  have hV : 0 ≤ V T := integral_nonneg fun _ ↦ by positivity
  simp only [mul_zero, sub_zero, zero_pow two_ne_zero] at hW
  nlinarith

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

/-- **(5.8)**, the absorption step: inserting the exterior estimate (3.6) into (4.6) at
`Q = 2S ≥ R`, and using that `C₆ C₂ ε^{p-1}` and `M/S²` are small, gives
`V_Q''(t) ≤ 4(p-1)E - 2(p-3)‖∇u(t)‖₂²`, i.e. `≤ -4(p-1)e - 2(p-3)G(t)²`. -/
theorem eq_5_8 (hp : 5 < p) {T S R C₆ C₂ ε : ℝ} (hsol : IsNLSSolution p (Set.Icc 0 T) u Du)
    (hS : 0 < S) (hR : R ≤ 2 * S) (hC₆ : 0 < C₆) (hC₂ε : 0 ≤ C₂ * ε ^ (p - 1))
    (hsmall : C₆ * C₂ * ε ^ (p - 1) ≤ min (2 * (p - 3)) 1)
    (hmass : (1 + C₆ / 4) * mass (u 0) ≤ -(4 * (p - 1) * energy p (u 0) (Du 0)) * S ^ 2)
    (h46 : ∀ t ∈ Set.Icc 0 T, virialSecondDeriv p (virialWeight (2 * S)) (u t) (Du t) ≤
      8 * (p - 1) * energy p (u 0) (Du 0) - 4 * (p - 3) * gradNormSq (Du t)
        + C₆ * (∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1))
        + C₆ * mass (u 0) / (2 * S) ^ 2)
    (hext : ∀ t ∈ Set.Icc 0 T, ∫ x in {x : ℝ² | R < ‖x‖}, ‖u t x‖ ^ (p + 1) ≤
      C₂ * ε ^ (p - 1) *
        ((∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2) + mass (u 0) / S ^ 2)) :
    ∀ t ∈ Set.Icc 0 T, virialSecondDeriv p (virialWeight (2 * S)) (u t) (Du t) ≤
      4 * (p - 1) * energy p (u 0) (Du 0) - 2 * (p - 3) * gradNormSq (Du t) := by
  intro t ht
  have hp1 : 1 < p := by linarith
  have hut : IsH1 (u t) (Du t) := hsol.h1 t ht
  obtain ⟨CGN, -, hGN⟩ := gagliardo_nirenberg hp1
  have hint : Integrable (fun x ↦ ‖u t x‖ ^ (p + 1)) := by
    have := (hGN _ _ hut).1.integrable_norm_rpow (by simp; linarith) (by simp)
    simpa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ p + 1)] using this
  -- the exterior of `2S ≥ R` lies in the exterior of `R`
  have hextQ : ∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1) ≤
      ∫ x in {x : ℝ² | R < ‖x‖}, ‖u t x‖ ^ (p + 1) := by
    refine setIntegral_mono_set hint.integrableOn (.of_forall fun x ↦ by positivity) ?_
    exact Filter.Eventually.of_forall fun x (hx : 2 * S < ‖x‖) ↦ (show R < ‖x‖ by linarith)
  -- the exterior kinetic energy is at most the full kinetic energy
  set gR := ∫ x in {x : ℝ² | R < ‖x‖}, ‖Du t 0 x‖ ^ 2 + ‖Du t 1 x‖ ^ 2
  have hgR : gR ≤ gradNormSq (Du t) :=
    setIntegral_le_integral
      ((hut.memL2_partial 0).norm.integrable_sq.add (hut.memL2_partial 1).norm.integrable_sq)
      (.of_forall fun x ↦ by positivity)
  have hgRnn : 0 ≤ gR :=
    setIntegral_nonneg (measurableSet_lt measurable_const measurable_norm) fun x _ ↦ by positivity
  set K := gradNormSq (Du t)
  set M := mass (u 0)
  set X := M / S ^ 2
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ by positivity
  have hX : 0 ≤ X := by positivity
  set m := min (2 * (p - 3)) 1
  have hm1 : m ≤ 2 * (p - 3) := min_le_left _ _
  have hm2 : m ≤ 1 := min_le_right _ _
  -- absorption of the exterior term
  have habs : C₆ * ∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1) ≤ 2 * (p - 3) * K + X := by
    have h1 : C₆ * ∫ x in {x : ℝ² | 2 * S < ‖x‖}, ‖u t x‖ ^ (p + 1) ≤
        (C₆ * C₂ * ε ^ (p - 1)) * (gR + X) := by
      have := mul_le_mul_of_nonneg_left (hextQ.trans (hext t ht)) hC₆.le
      linarith [show C₆ * (C₂ * ε ^ (p - 1) * (gR + X)) = C₆ * C₂ * ε ^ (p - 1) * (gR + X) by ring]
    have h2 : (C₆ * C₂ * ε ^ (p - 1)) * (gR + X) ≤ m * (K + X) :=
      mul_le_mul hsmall (by linarith) (by positivity) (le_min (by linarith) zero_le_one)
    have h3 : m * K ≤ 2 * (p - 3) * K := mul_le_mul_of_nonneg_right hm1 (hgRnn.trans hgR)
    have h4 : m * X ≤ X := mul_le_of_le_one_left hX hm2
    linarith [show m * (K + X) = m * K + m * X by ring]
  -- the mass terms: `X + C₆ M/(2S)² ≤ -4(p-1)E`
  have hmass' : X + C₆ * M / (2 * S) ^ 2 ≤ -(4 * (p - 1) * energy p (u 0) (Du 0)) := by
    have : X + C₆ * M / (2 * S) ^ 2 = (1 + C₆ / 4) * M / S ^ 2 := by
      simp only [X]; field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    exact hmass
  have h := h46 t ht
  simp only [K, X, M] at habs hmass' h ⊢
  have h := h46 t ht
  simp only [K, X, M] at habs hmass' h ⊢
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

set_option maxHeartbeats 400000 in
/-- **The infinite-variance case** (the main argument of Section 5). -/
theorem infinite_variance_contradiction (hp : 5 < p) (hsol : IsNLSSolution p (Set.Ici 0) u Du)
    (hrad : IsRadial (u 0)) (hE : energy p (u 0) (Du 0) < 0)
    (hvar : ¬ Integrable (fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2)) : False := by
  have hp1 : 1 < p := by linarith
  have hp3 : 0 < p - 3 := by linarith
  have hsolT : ∀ T, IsNLSSolution p (Set.Icc 0 T) u Du :=
    fun T ↦ hsol.mono Set.Icc_subset_Ici_self
  have hu0 : IsH1 (u 0) (Du 0) := hsol.h1 0 (Set.mem_Ici.mpr le_rfl)
  have hM : 0 ≤ mass (u 0) := integral_nonneg fun _ ↦ by positivity
  have hK0 : 0 ≤ gradNormSq (Du 0) := integral_nonneg fun _ ↦ by positivity
  have hh : 0 ≤ h1Norm (u 0) (Du 0) := Real.sqrt_nonneg _
  have ha : 0 < -(4 * (p - 1) * energy p (u 0) (Du 0)) := by nlinarith
  /- (5.2): `G(t)² = ‖∇u(t)‖₂² ≥ g`; we extend `t ↦ ‖∇u(t)‖₂²` continuously to `t < 0`. -/
  obtain ⟨g, hg, hKg⟩ := kinetic_lower_bound hp1 hsol hE
  obtain ⟨K, hKcont, hKeq⟩ : ∃ K : ℝ → ℝ, Continuous K ∧ ∀ t, 0 ≤ t → K t = gradNormSq (Du t) :=
    ⟨fun t ↦ gradNormSq (Du (max t 0)),
      hsol.continuousOn_gradNormSq.comp_continuous (continuous_id.max continuous_const)
        (fun t ↦ Set.mem_Ici.mpr (le_max_right t 0)),
      fun t ht ↦ by simp only [max_eq_left ht]⟩
  have hKg' : ∀ t ≥ 0, g ≤ K t := fun t ht ↦ by rw [hKeq t ht]; exact hKg t ht
  /- The constants of (4.6) and of Proposition 3.2. -/
  obtain ⟨C₆, hC₆, h46⟩ := eq_4_6 hp
  obtain ⟨c₀, ε₀, C₂, hc₀, hε₀, hC₂, h32⟩ := proposition_3_2 hp
  /- (5.4), in squared form. -/
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, 2 / (p - 3) ≤ c ∧
      128 * gradNormSq (Du 0) / (g * (p - 3) ^ 2) ≤ c :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hc : 0 < c := lt_of_lt_of_le (div_pos two_pos hp3) hc1
  /- Smallness thresholds: `ε ≤ η` makes `C₆ C₂ ε^{p-1} ≤ min (2(p-3)) 1`. -/
  obtain ⟨η, hη, hηε₀, hη1, hηsmall⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ ε₀ ∧ η ≤ 1 ∧
      C₆ * C₂ * η ≤ min (2 * (p - 3)) 1 := by
    have hm : 0 < min (2 * (p - 3)) 1 := lt_min (by linarith) one_pos
    refine ⟨min ε₀ (min 1 (min (2 * (p - 3)) 1 / (C₆ * C₂))), lt_min hε₀ (lt_min one_pos
      (div_pos hm (mul_pos hC₆ hC₂))), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      ?_⟩
    calc C₆ * C₂ * min ε₀ (min 1 (min (2 * (p - 3)) 1 / (C₆ * C₂)))
        ≤ C₆ * C₂ * (min (2 * (p - 3)) 1 / (C₆ * C₂)) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _))
            (mul_pos hC₆ hC₂).le
      _ = min (2 * (p - 3)) 1 := by field_simp
  obtain ⟨δ, hδ, hδc₀, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ c₀ * g ∧ δ ≤ η ^ 2 / 8 :=
    ⟨_, lt_min (mul_pos hc₀ hg) (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨T₀, hT₀1, hT₀h, hT₀M, hT₀a⟩ : ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      (2 * h1Norm (u 0) (Du 0) / η) ^ 2 ≤ T₀ ∧ mass (u 0) / g ≤ T₀ ∧
      (1 + C₆ / 4) * mass (u 0) / -(4 * (p - 1) * energy p (u 0) (Du 0)) ≤ T₀ :=
    ⟨max 1 (max _ (max _ _)), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩
  /- (5.7): the scales `T` and `S`. -/
  obtain ⟨T, S, hT, hS, hS1, hHS, hTFS⟩ := exists_good_scale K hKcont.continuousOn g hg hKg'
    (compactMoment (u 0)) (compactMoment_monotoneOn hu0.memL2)
    (compactMoment_continuousOn hu0.memL2) (compactMoment_tendsto_atTop hu0.memL2 hvar)
    (compactMoment_integrableOn hu0.memL2) c hc δ hδ T₀
  have hT1 : 1 ≤ T := hT₀1.trans hT
  have hT0 : 0 < T := by linarith
  have hS0 : 0 < S := by linarith
  have hF : g * T ≤ ∫ t in (0)..T, K t :=
    integral_ge_of_ge hKcont hT0.le (fun t ht ↦ hKg' t ht.1)
  have hI : g * T ^ 2 / 2 ≤ ∫ t in (0)..T, (T - t) * K t :=
    weighted_integral_ge_of_ge hKcont hT0.le (fun t ht ↦ hKg' t ht.1)
  have hI0 : 0 ≤ ∫ t in (0)..T, (T - t) * K t := le_trans (by positivity) hI
  have hFeq : ∫ t in (0)..T, gradNormSq (Du t) = ∫ t in (0)..T, K t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hT0.le] at ht
    exact (hKeq t ht.1).symm
  /- The hypotheses of Proposition 3.2 at `(T, S)`. -/
  have hε : exteriorEps p T S u Du ≤ η := by
    unfold exteriorEps
    rw [hFeq]
    exact eps_le_of_scales (by linarith) hT1 hS1 hg hF hM (hT₀M.trans hS) hη hh (hT₀h.trans hS)
      (hTFS.trans hδη)
  have hεnn : 0 ≤ exteriorEps p T S u Du := by
    unfold exteriorEps; positivity
  have hTS : T / S ^ 2 ≤ c₀ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : T * (∫ t in (0)..T, K t) ≤ δ * S ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at hTFS
    have hFnn : 0 ≤ ∫ t in (0)..T, K t := (by positivity : 0 ≤ g * T).trans hF
    have h3 : g * T ≤ T * (∫ t in (0)..T, K t) := by
      have := mul_le_mul_of_nonneg_right hT1 hFnn
      linarith
    have h4 : g * T ≤ g * (c₀ * S ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hδc₀ (sq_nonneg S)]
    exact le_of_mul_le_mul_left h4 hg
  obtain ⟨R, hR, hext⟩ := h32 T u Du hT0 (hsolT T) hrad S hS1 hTS (hε.trans hηε₀)
  /- (5.8) on `[0, T]` at `Q = 2S`. -/
  have hpow : exteriorEps p T S u Du ^ (p - 1) ≤ η :=
    (Real.rpow_le_self_of_le_one hεnn (hε.trans hη1) (by linarith)).trans hε
  have hmass : (1 + C₆ / 4) * mass (u 0) ≤ -(4 * (p - 1) * energy p (u 0) (Du 0)) * S ^ 2 := by
    have := hT₀a.trans hS
    rw [div_le_iff₀ ha] at this
    have hSS : S ≤ S ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hSS ha.le
    linarith
  have h58 := eq_5_8 hp (hsolT T) hS0 hR.2 hC₆
    (mul_nonneg hC₂.le (Real.rpow_nonneg hεnn _))
    ((mul_le_mul_of_nonneg_left hpow (mul_pos hC₆ hC₂).le).trans hηsmall) hmass
    (fun t ht ↦ h46 T u Du (hsolT T) (2 * S) (by positivity) t ht) hext
  /- Integrating (5.8) twice: `W(t) = V(t) - 2(p-1)E t² + 2(p-3) I(t)` is concave. -/
  have hQ : 0 < 2 * S := by positivity
  have hvir := localized_virial hp1 (hsolT T) (virialWeight (2 * S))
    (virialWeight_isTestFunction hQ)
  have hW := le_tangent_of_second_deriv_nonpos hT0.le
    (f := fun s ↦ (∫ x, virialWeight (2 * S) x * ‖u s x‖ ^ 2)
      - 2 * (p - 1) * energy p (u 0) (Du 0) * s ^ 2 + 2 * (p - 3) * ∫ r in (0)..s, (s - r) * K r)
    (f' := fun s ↦ virialFirstDeriv (virialWeight (2 * S)) (u s) (Du s)
      - 4 * (p - 1) * energy p (u 0) (Du 0) * s + 2 * (p - 3) * ∫ r in (0)..s, K r)
    (f'' := fun s ↦ virialSecondDeriv p (virialWeight (2 * S)) (u s) (Du s)
      - 4 * (p - 1) * energy p (u 0) (Du 0) + 2 * (p - 3) * K s)
    (fun t ht ↦ by
      have := ((hvir t ht).1.sub ((hasDerivWithinAt_pow 2 t (s := Set.Icc 0 T)).const_mul
        (2 * (p - 1) * energy p (u 0) (Du 0)))).add
        (((hasDerivAt_weighted_integral hKcont t).hasDerivWithinAt).const_mul (2 * (p - 3)))
      convert this using 1; push_cast; ring)
    (fun t ht ↦ by
      have := ((hvir t ht).2.sub ((hasDerivWithinAt_id t (Set.Icc 0 T)).const_mul
        (4 * (p - 1) * energy p (u 0) (Du 0)))).add
        (((hasDerivAt_integral_zero hKcont t).hasDerivWithinAt).const_mul (2 * (p - 3)))
      convert this using 1
      · funext s; simp
      · ring)
    (fun t ht ↦ by rw [hKeq t ht.1]; linarith [h58 t ht])
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero]
    at hW
  /- (5.5) and the final contradiction `0 ≤ V_Q(T) < 0`. -/
  have h55 := eq_5_5 hp3 hg hI0 hK0 hc1 hc2
    ((eq_4_7_value hu0.memL2 hS0).trans hHS)
    (integral_nonneg fun x ↦ mul_nonneg (virialWeight_nonneg _ _) (by positivity))
    (eq_4_7_deriv hu0 hQ) (by rw [le_div_iff₀ hg]; nlinarith [hI])
  have hVT : 0 ≤ ∫ x, virialWeight (2 * S) x * ‖u T x‖ ^ 2 :=
    integral_nonneg fun x ↦ mul_nonneg (virialWeight_nonneg _ _) (by positivity)
  have hET : 2 * (p - 1) * energy p (u 0) (Du 0) * T ^ 2 < 0 := by
    have : 0 < T ^ 2 := by positivity
    nlinarith
  linarith [mul_nonneg hp3.le hI0]

end Blowup
