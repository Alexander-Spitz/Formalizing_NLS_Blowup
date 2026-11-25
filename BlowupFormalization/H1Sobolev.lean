import BlowupFormalization.H1Data
import BlowupFormalization.MollifierConvergence
import BlowupFormalization.SolutionFacts

/-! # Sobolev and nonlinear estimates for the two-dimensional NLS -/

open Filter MeasureTheory Topology
open scoped ContDiff ENNReal

namespace Blowup

private lemma nonlinearity_eq_smul (p : ℝ) :
    nonlinearity p = (fun z : ℂ ↦ ‖z‖ ^ (p - 1)) • (id : ℂ → ℂ) := by
  funext z
  change _ = (‖z‖ ^ (p - 1) : ℝ) • z
  rw [Complex.real_smul]
  rfl

private lemma differentiable_nonlinearity {p : ℝ} (hp : 2 < p) :
    Differentiable ℝ (nonlinearity p) := by
  rw [nonlinearity_eq_smul]
  exact (differentiable_norm_rpow (E := ℂ) (show 1 < p - 1 by linarith)).smul differentiable_id

private lemma norm_fderiv_nonlinearity_le {p : ℝ} (hp : 2 < p) (z : ℂ) :
    ‖fderiv ℝ (nonlinearity p) z‖ ≤ p * ‖z‖ ^ (p - 1) := by
  let m : ℂ → ℝ := fun z ↦ ‖z‖ ^ (p - 1)
  have hm : Differentiable ℝ m := differentiable_norm_rpow (by linarith)
  rw [nonlinearity_eq_smul]
  change ‖fderiv ℝ (m • id : ℂ → ℂ) z‖ ≤ _
  rw [fderiv_smul (hm z) (differentiable_id z), fderiv_id]
  calc
    _ ≤ ‖m z • ContinuousLinearMap.id ℝ ℂ‖ + ‖(fderiv ℝ m z).smulRight z‖ :=
      norm_add_le _ _
    _ = m z + ((p - 1) * ‖z‖ ^ (p - 1 - 1)) * ‖z‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one,
        ContinuousLinearMap.norm_smulRight_apply, norm_fderiv_norm_id_rpow _ (by linarith)]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add_one' (by positivity) (by linarith)]
      have he : p - 1 - 1 + 1 = p - 1 := by ring
      rw [he]
      dsimp [m]
      ring

/-- Pointwise difference estimate for the focusing nonlinearity. -/
theorem norm_nonlinearity_sub_le {p : ℝ} (hp : 2 < p) (z w : ℂ) :
    ‖nonlinearity p z - nonlinearity p w‖ ≤
      p * (‖z‖ ^ (p - 1) + ‖w‖ ^ (p - 1)) * ‖z - w‖ := by
  let R := max ‖z‖ ‖w‖
  have hz : z ∈ Metric.closedBall (0 : ℂ) R := by
    simp [Metric.mem_closedBall, dist_zero_right, R]
  have hw : w ∈ Metric.closedBall (0 : ℂ) R := by
    simp [Metric.mem_closedBall, dist_zero_right, R]
  have hBound (y : ℂ) (hy : y ∈ Metric.closedBall (0 : ℂ) R) :
      ‖fderiv ℝ (nonlinearity p) y‖ ≤ p * R ^ (p - 1) := by
    have hy' : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    exact (norm_fderiv_nonlinearity_le hp y).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hy' (by linarith))
        (by linarith))
  have hL := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ differentiable_nonlinearity hp y) hBound hw hz
  refine hL.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rcases max_cases ‖z‖ ‖w‖ with h | h
  · rw [show R = ‖z‖ from h.1]
    exact le_add_of_nonneg_right (by positivity)
  · rw [show R = ‖w‖ from h.1]
    exact le_add_of_nonneg_left (by positivity)

private lemma norm_nonlinearity {p : ℝ} (hp : 1 < p) (z : ℂ) :
    ‖nonlinearity p z‖ = ‖z‖ ^ p := by
  rw [nonlinearity, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_add_one' (by positivity) (by linarith)]
  congr 1
  ring

/-- A function in L^{2p} has nonlinearity in L². -/
theorem memLp_nonlinearity {p : ℝ} (hp : 2 < p) {f : ℝ² → ℂ}
    (hf : MemLp f (ENNReal.ofReal (2 * p))) : MemLp (fun x ↦ nonlinearity p (f x)) 2 := by
  have hC := (differentiable_nonlinearity hp).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable
  have hNorm := hf.aestronglyMeasurable.norm.aemeasurable.pow_const p |>.aestronglyMeasurable
  rw [memLp_iff]
  have hEq : eLpNorm (fun x ↦ nonlinearity p (f x)) 2 volume =
      eLpNorm (fun x ↦ ‖f x‖ ^ p) 2 volume :=
    eLpNorm_congr_norm_ae hC hNorm (.of_forall fun x ↦ by
      rw [norm_nonlinearity (by linarith), Real.norm_of_nonneg (by positivity)])
  rw [hEq, eLpNorm_norm_rpow _ hf.aestronglyMeasurable (by linarith : 0 < p)]
  have he : (2 : ℝ≥0∞) * ENNReal.ofReal p = ENNReal.ofReal (2 * p) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [he]
  exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hf.eLpNorm_ne_top

/-- The L² difference of two nonlinear terms is controlled by the L^{2p} difference of
their arguments and their L^{2p} norms. -/
theorem eLpNorm_nonlinearity_sub_le {p : ℝ} (hp : 2 < p) {f g : ℝ² → ℂ}
    (hf : MemLp f (ENNReal.ofReal (2 * p))) (hg : MemLp g (ENNReal.ofReal (2 * p))) :
    eLpNorm (fun x ↦ nonlinearity p (f x) - nonlinearity p (g x)) 2 volume ≤
      ENNReal.ofReal p *
        ((eLpNorm f (ENNReal.ofReal (2 * p)) volume ^ (p - 1) +
          eLpNorm g (ENNReal.ofReal (2 * p)) volume ^ (p - 1)) *
          eLpNorm (f - g) (ENNReal.ofReal (2 * p)) volume) := by
  let q : ℝ≥0∞ := ENNReal.ofReal (2 * p)
  let r : ℝ≥0∞ := ENNReal.ofReal (2 * p / (p - 1))
  let m (v : ℝ² → ℂ) (x : ℝ²) : ℝ := ‖v x‖ ^ (p - 1)
  have hp' : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hpq : Real.HolderTriple (2 * p / (p - 1)) (2 * p) 2 :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  let _ : ENNReal.HolderTriple r q 2 := by simpa [r, q] using hpq.ennrealOfReal
  have hm (v : ℝ² → ℂ) (hv : MemLp v q) : AEStronglyMeasurable (m v) volume :=
    (hv.aestronglyMeasurable.norm.aemeasurable.pow_const (p - 1)).aestronglyMeasurable
  have he : r * ENNReal.ofReal (p - 1) = q := by
    unfold r q
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hPow (v : ℝ² → ℂ) (hv : MemLp v q) :
      eLpNorm (m v) r volume = eLpNorm v q volume ^ (p - 1) := by
    simpa only [he] using eLpNorm_norm_rpow (p := r) v hv.aestronglyMeasurable hp'
  have hN := ((memLp_nonlinearity hp hf).sub (memLp_nonlinearity hp hg)).aestronglyMeasurable
  have hP : eLpNorm (fun x ↦ nonlinearity p (f x) - nonlinearity p (g x)) 2 volume ≤
      ENNReal.ofReal p * eLpNorm ((m f + m g) • (f - g)) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hN _ 2
    refine .of_forall fun x ↦ ?_
    change ‖nonlinearity p (f x) - nonlinearity p (g x)‖ ≤
      p * ‖(m f x + m g x) • (f x - g x)‖
    rw [norm_smul, Real.norm_of_nonneg (by dsimp [m]; positivity), ← mul_assoc]
    exact norm_nonlinearity_sub_le hp (f x) (g x)
  have hHr : 1 ≤ r := by
    have hReal : (1 : ℝ) ≤ 2 * p / (p - 1) := (le_div_iff₀ hp').2 (by linarith)
    exact_mod_cast ENNReal.ofReal_le_ofReal hReal
  have hH := eLpNorm_smul_le_mul_eLpNorm (p := r) (q := q) (r := 2)
    ((hm f hf).add (hm g hg)) (hf.sub hg).aestronglyMeasurable
  have hTriangle := eLpNorm_add_le (f := m f) (g := m g) (μ := volume) hHr
  rw [hPow f hf, hPow g hg] at hTriangle
  exact hP.trans (mul_le_mul_right (hH.trans (mul_le_mul_left hTriangle _)) _)

/-- Taking the focusing nonlinearity sends L^{2p} continuity to L² continuity. -/
theorem continuous_toLp_nonlinearity {T : Type*} [TopologicalSpace T]
    {p : ℝ} (hp : 2 < p) [Fact (1 ≤ ENNReal.ofReal (2 * p))] {f : T → ℝ² → ℂ}
    (hf : ∀ t, MemLp (f t) (ENNReal.ofReal (2 * p)))
    (hcont : Continuous (fun t ↦ (hf t).toLp (f t))) :
    Continuous (fun t ↦ (memLp_nonlinearity hp (hf t)).toLp (fun x ↦ nonlinearity p (f t x))) := by
  let q := ENNReal.ofReal (2 * p)
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have hInput : Tendsto (fun s ↦ (hf s).toLp (f s)) (𝓝 t) (𝓝 ((hf t).toLp (f t))) :=
    hcont.continuousAt
  have hNorm : Tendsto (fun s ↦ eLpNorm (f s) q volume) (𝓝 t)
      (𝓝 (eLpNorm (f t) q volume)) := by
    simpa only [q, Lp.eNorm_toLp] using hInput.eNorm
  have hDiff : Tendsto (fun s ↦ eLpNorm (f s - f t) q volume) (𝓝 t) (𝓝 0) := by
    simpa only [q, ← MemLp.toLp_sub, Lp.eNorm_toLp] using
      tendsto_iff_eNorm_sub_tendsto_zero.1 hInput
  have hPow := (ENNReal.continuous_rpow_const (y := p - 1)).tendsto _ |>.comp hNorm
  let a := eLpNorm (f t) q volume ^ (p - 1)
  have ha : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (hf t).eLpNorm_ne_top
  have hSum : Tendsto (fun s ↦ eLpNorm (f s) q volume ^ (p - 1) + a) (𝓝 t) (𝓝 (a + a)) :=
    hPow.add tendsto_const_nhds
  have hMajorant : Tendsto (fun s ↦ ENNReal.ofReal p *
      ((eLpNorm (f s) q volume ^ (p - 1) + a) * eLpNorm (f s - f t) q volume)) (𝓝 t) (𝓝 0) := by
    have hProd := ENNReal.Tendsto.mul hSum (Or.inr (by simp)) hDiff
      (Or.inr (ENNReal.add_ne_top.mpr ⟨ha, ha⟩))
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal p) hProd
      (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_iff_eNorm_sub_tendsto_zero.2
  simp only [← MemLp.toLp_sub, Lp.eNorm_toLp]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hMajorant
    (fun _ ↦ zero_le) (fun s ↦ eLpNorm_nonlinearity_sub_le hp (hf s) (hf t))

private lemma two_mul_ofReal (q : ℝ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal (2 * q) := by
  rw [ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- One Sobolev iteration on the plane, obtained by applying the L¹ derivative
inequality to the k-th power of the norm and then using Hölder. -/
theorem eLpNorm_sobolev_power_step {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) {k : ℝ} (hk : 1 < k) :
    eLpNorm u (ENNReal.ofReal (2 * k)) volume ^ k ≤
      (eLpNormLESNormFDerivOneConst (E := ℝ²) volume 2 : ℝ≥0∞) * ENNReal.ofReal k *
        (eLpNorm u (ENNReal.ofReal (2 * (k - 1))) volume ^ (k - 1) *
          eLpNorm (fderiv ℝ u) 2 volume) := by
  let v : ℝ² → ℝ := fun x ↦ ‖u x‖ ^ k
  let g : ℝ² → ℝ := fun x ↦ ‖u x‖ ^ (k - 1)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow hk
  have hvc : HasCompactSupport v := huc.norm.rpow_const (by linarith)
  have hg : AEStronglyMeasurable g volume :=
    (hu.continuous.aestronglyMeasurable.norm.aemeasurable.pow_const (k - 1)).aestronglyMeasurable
  have hdu := (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable (μ := volume)
  have hFactor :
      eLpNorm (fderiv ℝ v) 1 volume ≤ ENNReal.ofReal k * eLpNorm (g • fderiv ℝ u) 1 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (hv.continuous_fderiv one_ne_zero).aestronglyMeasurable _ 1
    refine .of_forall fun x ↦ ?_
    have hx : 0 ≤ g x := Real.rpow_nonneg (norm_nonneg _) _
    change ‖fderiv ℝ v x‖ ≤ k * ‖g x • fderiv ℝ u x‖
    rw [norm_smul, Real.norm_of_nonneg hx, ← mul_assoc]
    exact norm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) (x := x) hk
  have hHolder : eLpNorm (g • fderiv ℝ u) 1 volume ≤
      eLpNorm g 2 volume * eLpNorm (fderiv ℝ u) 2 volume :=
    eLpNorm_smul_le_mul_eLpNorm hg hdu
  have hK : 0 < k := by linarith
  have hK' : 0 < k - 1 := sub_pos.mpr hk
  have hV : eLpNorm v 2 volume = eLpNorm u (ENNReal.ofReal (2 * k)) volume ^ k := by
    rw [show v = (fun x ↦ ‖u x‖ ^ k) from rfl,
      eLpNorm_norm_rpow _ hu.continuous.aestronglyMeasurable hK, two_mul_ofReal]
  have hG : eLpNorm g 2 volume =
      eLpNorm u (ENNReal.ofReal (2 * (k - 1))) volume ^ (k - 1) := by
    rw [show g = (fun x ↦ ‖u x‖ ^ (k - 1)) from rfl,
      eLpNorm_norm_rpow _ hu.continuous.aestronglyMeasurable hK', two_mul_ofReal]
  have hDim : Module.finrank ℝ ℝ² = 2 := by simp
  have hExp : NNReal.HolderConjugate (Module.finrank ℝ ℝ²) 2 := by
    rw [hDim]
    exact NNReal.HolderConjugate.two_two
  rw [← hV, ← hG, mul_assoc]
  exact (eLpNorm_le_eLpNorm_fderiv_one volume hv hvc hExp).trans
    (mul_le_mul_right (hFactor.trans (mul_le_mul_right hHolder _)) _)

/-- A compactly supported C¹ function on the plane satisfies the inhomogeneous Sobolev
bound at every positive even integer exponent. -/
theorem exists_eLpNorm_sobolev_bound_even (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : ℝ² → ℂ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u (ENNReal.ofReal (2 * (n + 1))) volume ≤
        C * (eLpNorm u 2 volume + eLpNorm (fderiv ℝ u) 2 volume) := by
  induction n with
  | zero =>
    refine ⟨1, by simp, fun u _ _ ↦ ?_⟩
    norm_num
  | succ n ih =>
    obtain ⟨C, hC, hInd⟩ := ih
    let k : ℝ := n + 2
    have hk : 1 < k := by dsimp [k]; linarith [show 0 ≤ (n : ℝ) by positivity]
    have hk' : k - 1 = (n : ℝ) + 1 := by dsimp [k]; ring
    let S := (eLpNormLESNormFDerivOneConst (E := ℝ²) volume 2 : ℝ≥0∞) * ENNReal.ofReal k
    let B := (S * C ^ (k - 1)) ^ k⁻¹
    have hB : B ≠ ⊤ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg (by linarith) hC))
    refine ⟨B, hB, fun u hu huc ↦ ?_⟩
    let H := eLpNorm u 2 volume + eLpNorm (fderiv ℝ u) 2 volume
    have hTwo : eLpNorm (fderiv ℝ u) 2 volume ≤ H := self_le_add_left _ _
    have hInd' : eLpNorm u (ENNReal.ofReal (2 * (k - 1))) volume ≤ C * H := by
      rw [hk']
      exact hInd u hu huc
    have hPower : eLpNorm u (ENNReal.ofReal (2 * k)) volume ^ k ≤ (B * H) ^ k := by
      calc
        _ ≤ S * (eLpNorm u (ENNReal.ofReal (2 * (k - 1))) volume ^ (k - 1) *
            eLpNorm (fderiv ℝ u) 2 volume) :=
          eLpNorm_sobolev_power_step hu huc hk
        _ ≤ S * ((C * H) ^ (k - 1) * H) := by gcongr
        _ = _ := by
          have hH : H ^ (k - 1) * H = H ^ k := by
            calc
              _ = H ^ (k - 1) * H ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
              _ = _ := by
                rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one]
                congr 1
                ring
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ k - 1),
            mul_assoc (C ^ (k - 1)), hH, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ k)]
          rw [show B ^ k = S * C ^ (k - 1) from ENNReal.rpow_inv_rpow (by linarith) _]
          ac_rfl
    have h := (ENNReal.rpow_le_rpow_iff (by linarith : 0 < k)).mp hPower
    have he : (n.succ : ℝ) + 1 = k := by
      push_cast
      dsimp [k]
      ring
    rw [he]
    exact h

private lemma exists_cutoffs :
    ∃ χ : ℕ → ℝ² → ℝ, ∃ D : ℝ, 0 ≤ D ∧
      (∀ n, ContDiff ℝ 1 (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ D) ∧
      (∀ x, ∀ᶠ n in atTop, χ n x = 1) := by
  let bump : ContDiffBump (0 : ℝ²) := ⟨1, 2, by norm_num, by norm_num⟩
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let χ (n : ℕ) (x : ℝ²) := bump (r n • x)
  obtain ⟨D, hD, hB⟩ := bump.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) bump.contDiff 1
  refine ⟨χ, D, hD, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨bump.contDiff.comp (contDiff_id.const_smul (r n)),
      bump.hasCompactSupport.comp_smul (hr n).ne'⟩
  · exact fun n x ↦ ⟨bump.nonneg, bump.le_one⟩
  · intro n x
    have hScale : r n ≤ 1 := by
      dsimp [r]
      apply (div_le_iff₀ (by positivity)).2
      norm_num
    have hDiff : fderiv ℝ (χ n) x =
        (fderiv ℝ bump (r n • x)).comp (r n • ContinuousLinearMap.id ℝ ℝ²) := by
      have hlin := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (r n)
      exact ((bump.contDiff (n := 1)).differentiable one_ne_zero (r n • x)
        |>.hasFDerivAt.comp x hlin).fderiv
    rw [hDiff]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_of_nonneg (hr n).le]
    exact (mul_le_mul_of_nonneg_right
      (by simpa only [norm_iteratedFDeriv_one] using hB 1 le_rfl (r n • x)) (hr n).le).trans
      (mul_le_of_le_one_right hD hScale)
  · intro x
    have hLim : Tendsto (fun n ↦ r n • x) atTop (𝓝 (0 : ℝ²)) := by
      have h : Tendsto (fun n ↦ r n • x) atTop (𝓝 ((0 : ℝ) • x)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.smul_const x
      rwa [zero_smul] at h
    have hBall : Metric.closedBall (0 : ℝ²) 1 ∈ 𝓝 (0 : ℝ²) :=
      Metric.closedBall_mem_nhds _ zero_lt_one
    exact (hLim.eventually_mem hBall).mono
      fun n hn ↦ bump.one_of_mem_closedBall hn

/-- The same even-exponent Sobolev estimate holds for smooth functions without compact
support, via cutoffs whose first derivatives are uniformly bounded. -/
theorem exists_eLpNorm_sobolev_bound_even_of_contDiff (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : ℝ² → ℂ, ContDiff ℝ 1 u →
      eLpNorm u (ENNReal.ofReal (2 * (n + 1))) volume ≤
        C * (eLpNorm u 2 volume + eLpNorm (fderiv ℝ u) 2 volume) := by
  obtain ⟨χ, D, hD, hχ, hχ01, hχDeriv, hχLim⟩ := exists_cutoffs
  obtain ⟨C, hC, hBound⟩ := exists_eLpNorm_sobolev_bound_even n
  refine ⟨C * (1 + ENNReal.ofReal D), ENNReal.mul_ne_top hC (by finiteness),
    fun u hu ↦ ?_⟩
  let U (i : ℕ) := χ i • u
  have hU (i : ℕ) : ContDiff ℝ 1 (U i) := ((hχ i).1).smul hu
  have hUc (i : ℕ) : HasCompactSupport (U i) := (hχ i).2.smul_right
  have hUa (i : ℕ) : AEStronglyMeasurable (U i) volume := (hU i).continuous.aestronglyMeasurable
  have hLim : ∀ᵐ x ∂volume, Tendsto (fun i ↦ U i x) atTop (𝓝 (u x)) :=
    .of_forall fun x ↦ tendsto_const_nhds.congr' ((hχLim x).mono fun i hi ↦ by
      change u x = χ i x • u x
      rw [hi, one_smul])
  have hMass (i : ℕ) : eLpNorm (U i) 2 volume ≤ eLpNorm u 2 volume := by
    apply eLpNorm_mono_ae (hUa i)
    refine .of_forall fun x ↦ ?_
    change ‖χ i x • u x‖ ≤ ‖u x‖
    rw [norm_smul, Real.norm_of_nonneg (hχ01 i x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 i x).2
  have hDeriv (i : ℕ) : eLpNorm (fderiv ℝ (U i)) 2 volume ≤
      eLpNorm (fderiv ℝ u) 2 volume + ENNReal.ofReal D * eLpNorm u 2 volume := by
    let V (x : ℝ²) := χ i x • fderiv ℝ u x
    let W (x : ℝ²) := (fderiv ℝ (χ i) x).smulRight (u x)
    have hEq : fderiv ℝ (U i) = V + W := funext fun x ↦ fderiv_smul
      (((hχ i).1.differentiable one_ne_zero) x) (hu.differentiable one_ne_zero x)
    rw [hEq]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · have hVc : Continuous V := ((hχ i).1.continuous).smul
        (hu.continuous_fderiv one_ne_zero)
      apply eLpNorm_mono_ae hVc.aestronglyMeasurable
      refine .of_forall fun x ↦ ?_
      dsimp [V]
      rw [norm_smul, Real.norm_of_nonneg (hχ01 i x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 i x).2
    · have hWd : Continuous W := by
        have h1 := ((hχ i).1).continuous_fderiv one_ne_zero
        have h2 := hu.continuous
        dsimp [W]
        fun_prop
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hWd.aestronglyMeasurable _ 2
      refine .of_forall fun x ↦ ?_
      dsimp [W]
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hχDeriv i x) (norm_nonneg _)
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm hUa u hu.continuous.aestronglyMeasurable hLim).trans ?_
  apply Filter.liminf_le_of_frequently_le'
  exact (Eventually.of_forall fun i ↦ (hBound (U i) (hU i) (hUc i)).trans (by
    rw [mul_assoc]
    apply mul_le_mul_right
    calc
      _ ≤ _ := add_le_add (hMass i) (hDeriv i)
      _ = (eLpNorm u 2 volume + eLpNorm (fderiv ℝ u) 2 volume) +
          ENNReal.ofReal D * eLpNorm u 2 volume := (add_assoc _ _ _).symm
      _ ≤ _ := by
        rw [add_mul, one_mul, mul_add]
        gcongr
        exact self_le_add_right _ _)).frequently

private lemma norm_fderiv_le_partialDeriv (u : ℝ² → ℂ) (x : ℝ²) :
    ‖fderiv ℝ u x‖ ≤ ‖partialDeriv 0 u x‖ + ‖partialDeriv 1 u x‖ := by
  let L := fderiv ℝ u x
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun y ↦ ?_
  have hBasis : y = y 0 • EuclideanSpace.single 0 1 + y 1 • EuclideanSpace.single 1 1 := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]
  conv_lhs => rw [hBasis]
  rw [map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul]
  calc
    _ ≤ ‖y‖ * ‖partialDeriv 0 u x‖ + ‖y‖ * ‖partialDeriv 1 u x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le y 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le y 1) (norm_nonneg _))
    _ = _ := by ring

private lemma eLpNorm_fderiv_le_partialDeriv {u : ℝ² → ℂ} (hu : ContDiff ℝ 1 u) :
    eLpNorm (fderiv ℝ u) 2 volume ≤
      eLpNorm (partialDeriv 0 u) 2 volume + eLpNorm (partialDeriv 1 u) 2 volume := by
  have hDiff := (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable (μ := volume)
  have hCont (j : Fin 2) : Continuous (partialDeriv j u) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine (eLpNorm_mono_ae_real hDiff (.of_forall (norm_fderiv_le_partialDeriv u))).trans ?_
  have hSum := eLpNorm_add_le (f := fun x ↦ ‖partialDeriv 0 u x‖)
    (g := fun x ↦ ‖partialDeriv 1 u x‖) (μ := volume) (p := 2) (by norm_num)
  change eLpNorm (fun x ↦ ‖partialDeriv 0 u x‖ + ‖partialDeriv 1 u x‖) 2 volume ≤ _ at hSum
  simpa only [eLpNorm_norm _ (hCont 0).aestronglyMeasurable,
    eLpNorm_norm _ (hCont 1).aestronglyMeasurable] using hSum

private lemma eLpNorm_two_eq_ofReal_sqrt_mass {u : ℝ² → ℂ} (hu : MemLp u 2) :
    eLpNorm u 2 volume = ENNReal.ofReal (Real.sqrt (mass u)) := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp [mass, Real.sqrt_eq_rpow, one_div]

private lemma eLpNorm_mollify_two_le {ρ : ℝ² → ℝ} (hρ : IsTestFunction ρ)
    (hNonneg : ∀ x, 0 ≤ ρ x) (hIntegral : ∫ x, ρ x = 1)
    {f : ℝ² → ℂ} (hf : MemLp f 2) :
    eLpNorm (mollify ρ f) 2 volume ≤ eLpNorm f 2 volume := by
  rw [eLpNorm_two_eq_ofReal_sqrt_mass (memLp_mollify hρ hf),
    eLpNorm_two_eq_ofReal_sqrt_mass hf]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  simpa only [Real.norm_of_nonneg (hNonneg _), hIntegral, one_pow, one_mul] using
    mass_mollify_le hρ hf

/-- The even-exponent Sobolev bound for weak H¹ functions, including their given weak
derivatives. A subsequence of normalized mollifications converges almost everywhere. -/
theorem exists_eLpNorm_h1_bound_even (n : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ), IsH1 u Du →
      eLpNorm u (ENNReal.ofReal (2 * (n + 1))) volume ≤ C *
        (eLpNorm u 2 volume + eLpNorm (Du 0) 2 volume + eLpNorm (Du 1) 2 volume) := by
  obtain ⟨C, hC, hBound⟩ := exists_eLpNorm_sobolev_bound_even_of_contDiff n
  refine ⟨C, hC, fun u Du hu ↦ ?_⟩
  let U (i : ℕ) := mollify (normalizedMollifier i) u
  have hU (i : ℕ) : ContDiff ℝ 1 (U i) :=
    (contDiff_mollify (normalizedMollifier_isTestFunction i) hu.memL2).of_le (by simp)
  have hUl (i : ℕ) : MemLp (U i) 2 := memLp_mollify (normalizedMollifier_isTestFunction i) hu.memL2
  have hContraction (i : ℕ) {f : ℝ² → ℂ} (hf : MemLp f 2) :
      eLpNorm (mollify (normalizedMollifier i) f) 2 volume ≤ eLpNorm f 2 volume :=
    eLpNorm_mollify_two_le (normalizedMollifier_isTestFunction i)
      (normalizedMollifier_nonneg i) (normalizedMollifier_integral i) hf
  have hGradient (i : ℕ) : eLpNorm (fderiv ℝ (U i)) 2 volume ≤
      eLpNorm (Du 0) 2 volume + eLpNorm (Du 1) 2 volume := by
    refine (eLpNorm_fderiv_le_partialDeriv (hU i)).trans ?_
    change eLpNorm (partialDeriv 0 (mollify (normalizedMollifier i) u)) 2 volume +
        eLpNorm (partialDeriv 1 (mollify (normalizedMollifier i) u)) 2 volume ≤ _
    rw [hu.partialDeriv_mollify (normalizedMollifier_isTestFunction i) 0,
      hu.partialDeriv_mollify (normalizedMollifier_isTestFunction i) 1]
    exact add_le_add (hContraction i (hu.memL2_partial 0))
      (hContraction i (hu.memL2_partial 1))
  have hConv : Tendsto (fun i ↦ eLpNorm (U i - u) 2 volume) atTop (𝓝 0) := by
    simp_rw [eLpNorm_two_eq_ofReal_sqrt_mass ((hUl _).sub hu.memL2)]
    have h := tendsto_mass_mollify_sub normalizedMollifier_isTestFunction normalizedMollifier_nonneg
      normalizedMollifier_integral normalizedMollifier_support tendsto_mollifierRadius
      hu.memL2
    simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h.sqrt
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hConv
  obtain ⟨v, _, hAE⟩ := hMeasure.exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun i ↦ (hUl (v i)).aestronglyMeasurable) u hu.memL2.aestronglyMeasurable hAE).trans ?_
  apply Filter.liminf_le_of_frequently_le'
  refine (Eventually.of_forall fun i ↦ (hBound (U (v i)) (hU (v i))).trans ?_).frequently
  rw [add_assoc]
  exact mul_le_mul_right (add_le_add (hContraction (v i) hu.memL2) (hGradient (v i))) C

private lemma eLpNorm_intermediate_le {u : ℝ² → ℂ}
    (hu : AEStronglyMeasurable u volume) {q s : ℝ} (hq : 2 < q) (hqs : q < s)
    {M : ℝ≥0∞} (hTwo : eLpNorm u 2 volume ≤ M)
    (hS : eLpNorm u (ENNReal.ofReal s) volume ≤ M) :
    eLpNorm u (ENNReal.ofReal q) volume ≤ M := by
  let a : ℝ := (s - q) / (s - 2)
  let b : ℝ := (q - 2) / (s - 2)
  have hd : 0 < s - 2 := by linarith
  have ha : 0 < a := div_pos (sub_pos.mpr hqs) hd
  have hb : 0 < b := div_pos (sub_pos.mpr hq) hd
  have hSum : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hExp : 2 * a + s * b = q := by
    dsimp [a, b]
    field_simp
    ring
  have hHolder : Real.HolderConjugate a⁻¹ b⁻¹ :=
    ⟨by simpa using hSum, inv_pos.mpr ha, inv_pos.mpr hb⟩
  let _ : ENNReal.HolderTriple (ENNReal.ofReal a⁻¹) (ENNReal.ofReal b⁻¹) 1 := by
    simpa using hHolder.ennrealOfReal
  let f (x : ℝ²) := ‖u x‖ₑ ^ (2 * a)
  let g (x : ℝ²) := ‖u x‖ₑ ^ (s * b)
  have hf : AEStronglyMeasurable f volume :=
    ENNReal.continuous_rpow_const.comp_aestronglyMeasurable hu.eNorm.aestronglyMeasurable
  have hg : AEStronglyMeasurable g volume :=
    ENNReal.continuous_rpow_const.comp_aestronglyMeasurable hu.eNorm.aestronglyMeasurable
  have hfExp : ENNReal.ofReal a⁻¹ * ENNReal.ofReal (2 * a) = 2 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : a⁻¹ * (2 * a) = 2 := by field_simp
    norm_num [he]
  have hgExp : ENNReal.ofReal b⁻¹ * ENNReal.ofReal (s * b) = ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hs : 0 < s := by linarith
  have hfNorm : eLpNorm f (ENNReal.ofReal a⁻¹) volume = eLpNorm u 2 volume ^ (2 * a) := by
    simpa only [hfExp] using eLpNorm_eNorm_rpow (p := ENNReal.ofReal a⁻¹) u hu
      (show 0 < 2 * a by positivity)
  have hgNorm : eLpNorm g (ENNReal.ofReal b⁻¹) volume =
      eLpNorm u (ENNReal.ofReal s) volume ^ (s * b) := by
    simpa only [hgExp] using eLpNorm_eNorm_rpow (p := ENNReal.ofReal b⁻¹) u hu
      (show 0 < s * b by positivity)
  have hq0 : 0 < q := by linarith
  apply (ENNReal.rpow_le_rpow_iff hq0).1
  have hqNorm := eLpNorm_eNorm_rpow (p := 1) u hu hq0
  rw [one_mul] at hqNorm
  rw [← hqNorm]
  have hEq : (fun x ↦ ‖u x‖ₑ ^ q) = f * g := by
    funext x
    change (‖u x‖ₑ : ℝ≥0∞) ^ q = ‖u x‖ₑ ^ (2 * a) * ‖u x‖ₑ ^ (s * b)
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hExp]
  rw [hEq]
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal a⁻¹) volume * eLpNorm g (ENNReal.ofReal b⁻¹) volume :=
      eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal hf hg
    _ ≤ M ^ (2 * a) * M ^ (s * b) := by
      rw [hfNorm, hgNorm]
      gcongr
    _ = _ := by rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hExp]

/-- Every finite exponent q ≥ 2 satisfies an inhomogeneous H¹ Sobolev bound on the plane. -/
theorem exists_eLpNorm_h1_bound (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ), IsH1 u Du →
      eLpNorm u (ENNReal.ofReal q) volume ≤ C *
        (eLpNorm u 2 volume + eLpNorm (Du 0) 2 volume + eLpNorm (Du 1) 2 volume) := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  obtain ⟨C, hC, hEven⟩ := exists_eLpNorm_h1_bound_even n
  refine ⟨1 + C, by finiteness, fun u Du hu ↦ ?_⟩
  let H := eLpNorm u 2 volume + eLpNorm (Du 0) 2 volume + eLpNorm (Du 1) 2 volume
  have hM : eLpNorm u 2 volume ≤ (1 + C) * H := by
    rw [add_mul, one_mul]
    exact ((self_le_add_right _ _).trans (self_le_add_right _ _)).trans (self_le_add_right _ _)
  rcases hq.eq_or_lt with rfl | hq'
  · simpa using hM
  have hqs : q < 2 * ((n : ℝ) + 1) := by linarith
  apply eLpNorm_intermediate_le hu.memL2.aestronglyMeasurable hq' hqs hM
  exact (hEven u Du hu).trans (mul_le_mul_left (self_le_add_left _ _) _)

/-- Weak H¹ functions on the plane belong to every finite L^q with q ≥ 2. -/
theorem IsH1.memLp_of_two_le {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) {q : ℝ} (hq : 2 ≤ q) : MemLp u (ENNReal.ofReal q) := by
  obtain ⟨C, hC, hBound⟩ := exists_eLpNorm_h1_bound q hq
  have hFinite :
      C * (eLpNorm u 2 volume + eLpNorm (Du 0) 2 volume + eLpNorm (Du 1) 2 volume) < ⊤ :=
    ENNReal.mul_lt_top hC.lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hu.memL2.eLpNorm_lt_top,
        (hu.memL2_partial 0).eLpNorm_lt_top⟩, (hu.memL2_partial 1).eLpNorm_lt_top⟩)
  exact (hBound u Du hu).trans_lt hFinite

/-- Strong convergence of H¹ data implies Lᵠ convergence for every finite real q ≥ 2. -/
theorem IsH1.tendsto_toLp_of_two_le {ι : Type*} {l : Filter ι}
    {f : ι → ℝ² → ℂ} {Df : ι → Fin 2 → ℝ² → ℂ}
    {g : ℝ² → ℂ} {Dg : Fin 2 → ℝ² → ℂ} (hg : IsH1 g Dg)
    (hf : ∀ i, IsH1 (f i) (Df i)) {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)]
    (hFun : Tendsto (fun i ↦ (hf i).memL2.toLp (f i)) l (𝓝 (hg.memL2.toLp g)))
    (hGrad : ∀ j, Tendsto (fun i ↦ ((hf i).memL2_partial j).toLp (Df i j)) l
      (𝓝 ((hg.memL2_partial j).toLp (Dg j)))) :
    Tendsto (fun i ↦ ((hf i).memLp_of_two_le hq).toLp (f i)) l
      (𝓝 ((hg.memLp_of_two_le hq).toLp g)) := by
  obtain ⟨C, hC, hBound⟩ := exists_eLpNorm_h1_bound q hq
  apply tendsto_iff_eNorm_sub_tendsto_zero.2
  simp only [← MemLp.toLp_sub, Lp.eNorm_toLp]
  have hU : Tendsto (fun i ↦ eLpNorm (f i - g) 2 volume) l (𝓝 0) := by
    simpa only [← MemLp.toLp_sub, Lp.eNorm_toLp] using
      tendsto_iff_eNorm_sub_tendsto_zero.1 hFun
  have hD (j : Fin 2) :
      Tendsto (fun i ↦ eLpNorm (Df i j - Dg j) 2 volume) l (𝓝 0) := by
    simpa only [← MemLp.toLp_sub, Lp.eNorm_toLp] using
      tendsto_iff_eNorm_sub_tendsto_zero.1 (hGrad j)
  have hSum : Tendsto (fun i ↦
      eLpNorm (f i - g) 2 volume + eLpNorm (Df i 0 - Dg 0) 2 volume +
        eLpNorm (Df i 1 - Dg 1) 2 volume) l (𝓝 0) := by
    simpa only [zero_add] using (hU.add (hD 0)).add (hD 1)
  have hMajorant := ENNReal.Tendsto.const_mul (a := C) hSum (Or.inr hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using hMajorant) (fun _ ↦ zero_le) (fun i ↦ ?_)
  exact hBound (f i - g) (Df i - Dg) ((hf i).sub hg)

/-- Weak H¹ time continuity implies Lᵠ time continuity for every finite real q ≥ 2. -/
theorem IsNLSSolution.continuous_toLp_of_two_le
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) {q : ℝ} (hq : 2 ≤ q) [Fact (1 ≤ ENNReal.ofReal q)] :
    Continuous (fun t : J ↦ ((h.h1 t t.property).memLp_of_two_le hq).toLp (u t)) :=
  continuous_iff_continuousAt.2 fun t ↦ (h.h1 t t.property).tendsto_toLp_of_two_le
    (fun s : J ↦ h.h1 s s.property) hq h.continuous_toLp.continuousAt
    (fun j ↦ (h.continuous_grad_toLp j).continuousAt)

/-- The focusing nonlinearity of weak H¹ data belongs to L² for every real p ≥ 3. -/
theorem IsH1.memLp_nonlinearity {p : ℝ} {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hp : 3 ≤ p) : MemLp (fun x ↦ nonlinearity p (u x)) 2 :=
  Blowup.memLp_nonlinearity (by linarith) (hu.memLp_of_two_le (by linarith : 2 ≤ 2 * p))

/-- The nonlinear density in the energy is integrable for weak H¹ data. -/
theorem IsH1.integrable_nonlinear_density {p : ℝ} {u : ℝ² → ℂ} {Du : Fin 2 → ℝ² → ℂ}
    (hu : IsH1 u Du) (hp : 3 ≤ p) : Integrable (fun x ↦ ‖u x‖ ^ (p + 1)) := by
  have hp' : 0 < p + 1 := by linarith
  have h := (hu.memLp_of_two_le (by linarith : 2 ≤ p + 1)).integrable_norm_rpow
    (by simp [hp']) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hp'.le] using h

/-- The nonlinearity of a weak H¹ solution is continuous into L² on its time domain. -/
theorem IsNLSSolution.continuous_nonlinearity_toLp
    {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}
    (h : IsNLSSolution p J u Du) (hp : 3 ≤ p) :
    Continuous (fun t : J ↦ ((h.h1 t t.property).memLp_nonlinearity hp).toLp
      (fun x ↦ nonlinearity p (u t x))) := by
  have hq : 2 ≤ 2 * p := by linarith
  have hp' : 2 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal (2 * p)) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  exact continuous_toLp_nonlinearity (f := fun t : J ↦ u t) hp'
    (fun t ↦ (h.h1 t t.property).memLp_of_two_le hq) (h.continuous_toLp_of_two_le hq)

end Blowup
