import BlowupFormalization.Mollification

/-! # Convergence of spatial mollifiers in L² -/

open Filter MeasureTheory Topology
open scoped Convolution Pointwise

namespace Blowup

/-- Mollification distributes over differences of L² functions. -/
theorem mollify_sub {ρ : ℝ² → ℝ} {f g : ℝ² → ℂ} (hρ : IsTestFunction ρ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    mollify ρ (f - g) = mollify ρ f - mollify ρ g := by
  funext x
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hInt (v : ℝ² → ℂ) (hv : MemLp v 2) :
      Integrable (fun y ↦ (ρ (x - y) : ℂ) * v y) :=
    (hρ.2.convolutionExists_right (μ := volume) L (hv.locallyIntegrable (by norm_num))
      hρ.1.continuous x).integrable
  simp only [mollify_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (hInt f hf) (hInt g hg)

private theorem mass_add_le {f g : ℝ² → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    mass (f + g) ≤ 2 * mass f + 2 * mass g := by
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hsum := (memLp_two_iff_integrable_sq_norm (hf.add hg).aestronglyMeasurable).mp (hf.add hg)
  have hInt := integral_mono hsum ((hfi.const_mul 2).add (hgi.const_mul 2)) (fun x ↦ by
    change ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2
    calc
      _ ≤ (‖f x‖ + ‖g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)])
  simpa only [mass, Pi.add_apply, integral_add (hfi.const_mul 2) (hgi.const_mul 2),
    integral_const_mul] using hInt

variable {ρ : ℕ → ℝ² → ℝ} {r : ℕ → ℝ}

private theorem tendsto_mass_mollify_sub_of_compact
    (hρ : ∀ n, IsTestFunction (ρ n)) (hNonneg : ∀ n x, 0 ≤ ρ n x)
    (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) {g : ℝ² → ℂ}
    (hg : Continuous g) (hgSupp : HasCompactSupport g) (hgLp : MemLp g 2) :
    Tendsto (fun n ↦ mass (mollify (ρ n) g - g)) atTop (𝓝 0) := by
  have hUniform (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop,
      ∀ x, ‖mollify (ρ n) g x - g x‖ ≤ ε := by
    obtain ⟨δ, hδ, hClose⟩ := Metric.uniformContinuous_iff.mp
      (hgSupp.uniformContinuous_of_continuous hg) ε hε
    filter_upwards [hr.eventually (eventually_lt_nhds hδ)] with n hn x
    rw [← dist_eq_norm]
    unfold mollify
    rw [convolution_flip]
    exact dist_convolution_le hε.le ((hSupport n).trans (Metric.closedBall_subset_ball hn))
      (hNonneg n) (hIntegral n) hg.aestronglyMeasurable (fun y hy ↦ (hClose hy).le)
  let K := (tsupport g + Metric.closedBall (0 : ℝ²) 1) ∪ tsupport g
  have hK : IsCompact K :=
    (hgSupp.isCompact.add (isCompact_closedBall _ _)).union hgSupp.isCompact
  have hEventuallySupport : ∀ᶠ n in atTop, Function.support (mollify (ρ n) g) ⊆ K := by
    filter_upwards [hr.eventually (eventually_lt_nhds zero_lt_one)] with n hn
    have hKernel : Function.support (ρ n) ⊆ Metric.closedBall 0 1 :=
      (hSupport n).trans (Metric.closedBall_subset_closedBall hn.le)
    refine (support_convolution_subset _).trans ?_
    exact (Set.add_subset_add (subset_tsupport g) hKernel).trans Set.subset_union_left
  let F (n : ℕ) (x : ℝ²) : ℝ := ‖mollify (ρ n) g x - g x‖ ^ 2
  let bound := K.indicator (fun _ ↦ (1 : ℝ))
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (((contDiff_mollify (hρ n) hgLp).continuous.sub hg).norm.pow 2).aestronglyMeasurable
  have hBoundInt : Integrable bound :=
    (integrableOn_const (C := (1 : ℝ)) hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hBound : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, ‖F n x‖ ≤ bound x := by
    filter_upwards [hEventuallySupport, hUniform 1 zero_lt_one] with n hSupp hNorm
    refine .of_forall fun x ↦ ?_
    by_cases hx : x ∈ K
    · rw [show bound x = 1 from Set.indicator_of_mem hx _,
        Real.norm_of_nonneg (sq_nonneg _)]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hNorm x) 2).trans_eq (one_pow _)
    · have hgn : g x = 0 := Function.notMem_support.mp
        (fun h ↦ hx (Set.subset_union_right (subset_tsupport g h)))
      have hmn : mollify (ρ n) g x = 0 := Function.notMem_support.mp (fun h ↦ hx (hSupp h))
      simp only [F, hgn, hmn, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact (Set.indicator_of_notMem hx _).symm.le
  have hLimit (x : ℝ²) : Tendsto (fun n ↦ F n x) atTop (𝓝 0) := by
    have hNorm : Tendsto (fun n ↦ ‖mollify (ρ n) g x - g x‖) atTop (𝓝 0) := by
      refine tendsto_order.2 ⟨fun _ h ↦ .of_forall fun _ ↦ h.trans_le (norm_nonneg _), ?_⟩
      intro ε hε
      filter_upwards [hUniform (ε / 2) (half_pos hε)] with n hn
      exact (hn x).trans_lt (half_lt_self hε)
    simpa only [F, zero_pow (by decide : 2 ≠ 0)] using hNorm.pow 2
  simpa only [mass, Pi.sub_apply, F, integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (F := F) (f := fun _ ↦ (0 : ℝ)) bound (.of_forall hMeas)
      hBound hBoundInt (.of_forall hLimit))

/-- Nonnegative kernels of integral one and shrinking support converge to the identity in L². -/
theorem tendsto_mass_mollify_sub (hρ : ∀ n, IsTestFunction (ρ n))
    (hNonneg : ∀ n x, 0 ≤ ρ n x) (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) {f : ℝ² → ℂ} (hf : MemLp f 2) :
    Tendsto (fun n ↦ mass (mollify (ρ n) f - f)) atTop (𝓝 0) := by
  refine tendsto_order.2
    ⟨fun _ h ↦ .of_forall fun _ ↦ h.trans_le (integral_nonneg fun _ ↦ sq_nonneg _), ?_⟩
  intro ε hε
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) := by simpa using hf
  obtain ⟨g, hgSupp, hClose, hg, hgLp'⟩ :=
    hf'.exists_hasCompactSupport_integral_rpow_sub_le (by norm_num) (show 0 < ε / 16 by positivity)
  have hgLp : MemLp g 2 := by simpa using hgLp'
  have hClose' : mass (f - g) ≤ ε / 16 := by
    simpa only [mass, Pi.sub_apply, Real.rpow_two] using hClose
  have hConv := tendsto_mass_mollify_sub_of_compact hρ hNonneg hIntegral hSupport hr hg hgSupp hgLp
  filter_upwards [hConv.eventually (eventually_lt_nhds (show 0 < ε / 8 by positivity))] with n hn
  have hDiff := hf.sub hgLp
  have hM := memLp_mollify (hρ n) hDiff
  have hError := (memLp_mollify (hρ n) hgLp).sub hgLp
  have hContract : mass (mollify (ρ n) (f - g)) ≤ mass (f - g) := by
    simpa only [Real.norm_of_nonneg (hNonneg n _), hIntegral n, one_pow, one_mul] using
      mass_mollify_le (hρ n) hDiff
  have hEq : mollify (ρ n) f - f =
      mollify (ρ n) (f - g) + ((mollify (ρ n) g - g) + -(f - g)) := by
    rw [mollify_sub (hρ n) hf hgLp]
    abel
  have hInner := mass_add_le hError hDiff.neg
  have hNeg : mass (-(f - g)) = mass (f - g) := by simp only [mass, Pi.neg_apply, norm_neg]
  rw [hNeg] at hInner
  rw [hEq]
  have hOuter := mass_add_le hM (hError.add hDiff.neg)
  linarith

/-- Each classical derivative of the mollified function converges in L² to the corresponding weak
derivative. -/
theorem IsH1.tendsto_mass_partialDeriv_mollify_sub {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hρ : ∀ n, IsTestFunction (ρ n))
    (hNonneg : ∀ n x, 0 ≤ ρ n x) (hIntegral : ∀ n, ∫ x, ρ n x = 1)
    (hSupport : ∀ n, Function.support (ρ n) ⊆ Metric.closedBall 0 (r n))
    (hr : Tendsto r atTop (𝓝 0)) (j : Fin 2) :
    Tendsto (fun n ↦ mass (partialDeriv j (mollify (ρ n) u) - Du j)) atTop (𝓝 0) := by
  have hDeriv (n : ℕ) := hu.partialDeriv_mollify (hρ n) j
  simp only [hDeriv]
  exact tendsto_mass_mollify_sub hρ hNonneg hIntegral hSupport hr (hu.memL2_partial j)

end Blowup
