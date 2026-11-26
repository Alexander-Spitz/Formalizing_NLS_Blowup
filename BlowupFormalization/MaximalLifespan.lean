import BlowupFormalization.ExteriorEstimate
import BlowupFormalization.H1Data
import BlowupFormalization.MassConservation
import BlowupFormalization.TimeReversal

/-! # Finite maximal lifespans and the continuation criterion -/

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace Blowup

variable {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ}

/-- Excluding both time rays forces the open connected maximal lifespan to have
two finite endpoints, with time zero strictly between them. -/
theorem IsMaximalNLSSolution.exists_eq_Ioo_of_excludes_rays
    (h : IsMaximalNLSSolution p J u Du) (hForward : ¬ Ici 0 ⊆ J) (hBackward : ¬ Iic 0 ⊆ J) :
    ∃ Tminus Tplus : ℝ, 0 < Tminus ∧ 0 < Tplus ∧ J = Ioo (-Tminus) Tplus := by
  obtain ⟨a, ha, haJ⟩ := not_subset.mp hBackward
  obtain ⟨b, hb, hbJ⟩ := not_subset.mp hForward
  have hBoundedBelow : BddBelow J := ⟨a, fun t ht ↦ le_of_not_gt fun hta ↦
    haJ (h.ordConnected.out ht h.zero_mem ⟨hta.le, ha⟩)⟩
  have hBoundedAbove : BddAbove J := ⟨b, fun t ht ↦ le_of_not_gt fun hbt ↦
    hbJ (h.ordConnected.out h.zero_mem ht ⟨hb, hbt.le⟩)⟩
  have hNonempty : J.Nonempty := ⟨0, h.zero_mem⟩
  have hInf := isGLB_csInf hNonempty hBoundedBelow
  have hSup := isLUB_csSup hNonempty hBoundedAbove
  have hEq : J = Ioo (sInf J) (sSup J) := by
    apply Subset.antisymm
    · intro t ht
      obtain ⟨l, r, _, hNbr, hSub⟩ :=
        exists_Icc_mem_subset_of_mem_nhds (h.isOpen.mem_nhds ht)
      have hInner : t ∈ Ioo l r := by
        rw [← interior_Icc]
        exact mem_interior_iff_mem_nhds.mpr hNbr
      exact ⟨(hInf.1 (hSub ⟨le_rfl, hInner.1.le.trans hInner.2.le⟩)).trans_lt hInner.1,
        hInner.2.trans_le (hSup.1 (hSub ⟨hInner.1.le.trans hInner.2.le, le_rfl⟩))⟩
    · intro t ht
      obtain ⟨l, hlJ, hlt⟩ := (isGLB_lt_iff hInf).mp ht.1
      obtain ⟨r, hrJ, htr⟩ := (lt_isLUB_iff hSup).mp ht.2
      exact h.ordConnected.out hlJ hrJ ⟨hlt.le, htr.le⟩
  have hZero : (0 : ℝ) ∈ Ioo (sInf J) (sSup J) := hEq ▸ h.zero_mem
  exact ⟨-sInf J, sSup J, neg_pos.mpr hZero.1, hZero.2, by simpa only [neg_neg] using hEq⟩

/-- An extension is a weak solution on an open interval containing the old time domain,
agreeing with the old solution in H¹ throughout that domain and defined past `T`. -/
def HasNLSExtensionPast (p : ℝ) (J : Set ℝ) (u : ℝ → ℝ² → ℂ)
    (Du : ℝ → Fin 2 → ℝ² → ℂ) (T : ℝ) : Prop :=
  ∃ (K : Set ℝ) (v : ℝ → ℝ² → ℂ) (Dv : ℝ → Fin 2 → ℝ² → ℂ),
    IsOpen K ∧ K.OrdConnected ∧ J ⊆ K ∧ (∃ s ∈ K, T < s) ∧
      IsNLSSolution p K v Dv ∧ ∀ s ∈ J, SameH1Data (v s) (u s) (Dv s) (Du s)

/-- The H¹ continuation input from local solution theory. If a fixed H¹ bound holds
arbitrarily close to a finite right endpoint from within the lifespan, the solution extends
past that endpoint. -/
def H1ForwardContinuation : Prop :=
  ∀ {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ},
    3 ≤ p → IsMaximalNLSSolution p J u Du → ∀ {T : ℝ}, IsLUB J T →
      (∃ C : ℝ, ∃ᶠ t in 𝓝[J] T, h1Norm (u t) (Du t) ≤ C) →
        HasNLSExtensionPast p J u Du T

/-- A maximal weak solution cannot have a continuation past an upper bound of its domain. -/
theorem IsMaximalNLSSolution.not_hasNLSExtensionPast
    (h : IsMaximalNLSSolution p J u Du) {T : ℝ} (hUpper : T ∈ upperBounds J) :
    ¬ HasNLSExtensionPast p J u Du T := by
  rintro ⟨K, v, Dv, hOpen, hOrd, hSub, ⟨s, hsK, hTs⟩, hSol, hAgreement⟩
  have hRestrict := (h.restrict_of_same_data K v Dv hOpen hOrd (hSub h.zero_mem)
    hSol (hAgreement 0 h.zero_mem)).1
  exact (not_lt_of_ge (hUpper (hRestrict hsK))) hTs

/-- Mass on a maximal lifespan agrees with the mass at time zero. -/
theorem IsMaximalNLSSolution.mass_eq_initial
    (h : IsMaximalNLSSolution p J u Du) (hp : 3 ≤ p) {t : ℝ} (ht : t ∈ J) :
    mass (u t) = mass (u 0) := by
  by_cases hPos : 0 ≤ t
  · refine h.isSolution.mass_eq hp hPos ?_
    rw [h.isOpen.interior_eq]
    exact h.ordConnected.out h.zero_mem ht
  · symm
    refine h.isSolution.mass_eq hp (le_of_not_ge hPos) ?_
    rw [h.isOpen.interior_eq]
    exact h.ordConnected.out ht h.zero_mem

/-- Mass conservation and forward continuation force the gradient norm to diverge at
every finite right endpoint of a maximal lifespan. -/
theorem IsMaximalNLSSolution.tendsto_gradNorm_at_right
    (h : IsMaximalNLSSolution p J u Du) (hp : 3 ≤ p) (hCont : H1ForwardContinuation)
    {T : ℝ} (hEndpoint : IsLUB J T) :
    Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] T) atTop := by
  by_contra hNot
  obtain ⟨C, hC⟩ := not_forall.mp (fun hAll ↦ hNot (tendsto_atTop.2 hAll))
  have hFreq : ∃ᶠ t in 𝓝[J] T, Real.sqrt (gradNormSq (Du t)) < C := by
    simpa only [not_le] using Filter.not_eventually.mp hC
  have hBound : ∃ᶠ t in 𝓝[J] T, h1Norm (u t) (Du t) ≤
      Real.sqrt (mass (u 0) + C ^ 2) := by
    apply (hFreq.and_eventually self_mem_nhdsWithin).mono
    rintro t ⟨hGrad, ht⟩
    have hNonneg : 0 ≤ gradNormSq (Du t) :=
      integral_nonneg (fun _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hGrad.le 2
    rw [Real.sq_sqrt hNonneg] at hSq
    unfold h1Norm
    rw [h.mass_eq_initial hp ht]
    exact Real.sqrt_le_sqrt (add_le_add le_rfl hSq)
  exact (h.not_hasNLSExtensionPast hEndpoint.1) (hCont hp h hEndpoint ⟨_, hBound⟩)

/-- The same continuation input gives divergence at the left endpoint by conjugate time reversal. -/
theorem IsMaximalNLSSolution.tendsto_gradNorm_at_left
    (h : IsMaximalNLSSolution p J u Du) (hp : 3 ≤ p) (hCont : H1ForwardContinuation)
    {T : ℝ} (hEndpoint : IsGLB J T) :
    Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] T) atTop := by
  have hReflected : IsLUB ((Neg.neg : ℝ → ℝ) ⁻¹' J) (-T) := by
    constructor
    · intro s hs
      simpa only [neg_neg] using neg_le_neg (hEndpoint.1 (show -s ∈ J from hs))
    · intro s hs
      have hLower : -s ∈ lowerBounds J := by
        intro t ht
        have hMem : -t ∈ (Neg.neg : ℝ → ℝ) ⁻¹' J := by simpa using ht
        simpa only [neg_neg] using neg_le_neg (hs hMem)
      simpa only [neg_neg] using neg_le_neg (hEndpoint.2 hLower)
  exact (tendsto_gradNorm_conj_time_reversal_iff Du J T).1
    (h.conj_time_reversal.tendsto_gradNorm_at_right hp hCont hReflected)

/-- Exclusion of both time rays gives the finite lifespan and both gradient limits,
conditional on H¹ continuation. -/
theorem IsMaximalNLSSolution.finite_lifespan_and_gradient_divergence
    (h : IsMaximalNLSSolution p J u Du) (hp : 3 ≤ p) (hCont : H1ForwardContinuation)
    (hForward : ¬ Ici 0 ⊆ J) (hBackward : ¬ Iic 0 ⊆ J) :
    ∃ Tminus Tplus : ℝ, 0 < Tminus ∧ 0 < Tplus ∧ J = Ioo (-Tminus) Tplus ∧
      Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] (-Tminus)) atTop ∧
      Tendsto (fun t ↦ Real.sqrt (gradNormSq (Du t))) (𝓝[J] Tplus) atTop := by
  obtain ⟨Tminus, Tplus, hMinus, hPlus, hEq⟩ := h.exists_eq_Ioo_of_excludes_rays hForward hBackward
  have hOrdered : -Tminus < Tplus := (neg_lt_zero.mpr hMinus).trans hPlus
  have hLeft : IsGLB J (-Tminus) := by rw [hEq]; exact isGLB_Ioo hOrdered
  have hRight : IsLUB J Tplus := by rw [hEq]; exact isLUB_Ioo hOrdered
  exact ⟨Tminus, Tplus, hMinus, hPlus, hEq, h.tendsto_gradNorm_at_left hp hCont hLeft,
    h.tendsto_gradNorm_at_right hp hCont hRight⟩

/-- The forward virial input at a fixed exponent, stated for radial weak solutions
whose energy is bounded above by a strictly negative constant. -/
def ForwardRadialBlowupCriterion (p : ℝ) : Prop :=
  ∀ {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ},
    IsNLSSolution p J u Du → Ici 0 ⊆ interior J → ∀ {e : ℝ}, 0 < e →
      (∀ t ≥ 0, energy p (u t) (Du t) ≤ -e) → (∀ t ≥ 0, IsRadialAE (u t)) → False

/-- The same forward criterion excludes both time rays when radiality and the energy
bound hold along the maximal solution. -/
theorem IsMaximalNLSSolution.excludes_rays_of_forward_radial_criterion
    (h : IsMaximalNLSSolution p J u Du) (hCriterion : ForwardRadialBlowupCriterion p)
    {e : ℝ} (he : 0 < e) (hEnergy : ∀ t ∈ J, energy p (u t) (Du t) ≤ -e)
    (hRadial : ∀ t ∈ J, IsRadialAE (u t)) :
    (¬ Ici 0 ⊆ J) ∧ (¬ Iic 0 ⊆ J) := by
  constructor
  · intro hTime
    exact hCriterion h.isSolution (by simpa only [h.isOpen.interior_eq] using hTime) he
      (fun t ht ↦ hEnergy t (hTime ht)) (fun t ht ↦ hRadial t (hTime ht))
  · intro hTime
    have hMem (t : ℝ) (ht : 0 ≤ t) : -t ∈ J := hTime (mem_Iic.mpr (neg_nonpos.mpr ht))
    have hReverse := h.conj_time_reversal
    have hForward : Ici 0 ⊆ interior ((Neg.neg : ℝ → ℝ) ⁻¹' J) := by
      rw [hReverse.isOpen.interior_eq]
      exact fun t ht ↦ hMem t (mem_Ici.mp ht)
    exact hCriterion hReverse.isSolution hForward he
      (fun t ht ↦ by simpa only [energy_conj] using hEnergy (-t) (hMem t ht))
      (fun t ht ↦ (hRadial (-t) (hMem t ht)).conj)

/-- The solution-theory inputs needed to pass from the forward virial criterion
to the frozen two-sided blow-up statement. -/
structure MaximalH1SolutionTheory : Prop where
  exists_maximal : ∀ {p : ℝ} {u₀ : ℝ² → ℂ} {Du₀ : Fin 2 → ℝ² → ℂ},
    3 ≤ p → IsH1 u₀ Du₀ →
    ∃ (J : Set ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ),
      IsMaximalNLSSolution p J u Du ∧ SameH1Data (u 0) u₀ (Du 0) Du₀
  conserves_energy : ∀ {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ},
    3 ≤ p → IsMaximalNLSSolution p J u Du →
      ∀ t ∈ J, energy p (u t) (Du t) = energy p (u 0) (Du 0)
  preserves_radiality : ∀ {p : ℝ} {J : Set ℝ} {u : ℝ → ℝ² → ℂ} {Du : ℝ → Fin 2 → ℝ² → ℂ},
    3 ≤ p → IsMaximalNLSSolution p J u Du → IsRadialAE (u 0) → ∀ t ∈ J, IsRadialAE (u t)
  continues_forward : H1ForwardContinuation

/-- The frozen statement follows from the stated solution theory and the forward virial
criterion at every exponent in the target range. -/
theorem radialNLSFiniteTimeBlowup_of_solution_theory
    (hTheory : MaximalH1SolutionTheory)
    (hCriterion : ∀ p : ℝ, 3 ≤ p → ForwardRadialBlowupCriterion p) :
    RadialNLSFiniteTimeBlowup := by
  intro p u₀ Du₀ hp hu₀ hRadial₀ hNeg
  obtain ⟨J, u, Du, hMax, hSame⟩ := hTheory.exists_maximal hp hu₀
  have hInitialRadial : IsRadialAE (u 0) := by
    obtain ⟨w, hw, hRep⟩ := hRadial₀
    exact ⟨w, hw, hSame.1.trans hRep⟩
  let e := -energy p u₀ Du₀
  have he : 0 < e := neg_pos.mpr hNeg
  have hEnergyBound (t : ℝ) (ht : t ∈ J) : energy p (u t) (Du t) ≤ -e := by
    rw [hTheory.conserves_energy hp hMax t ht, hSame.energy_eq p]
    simp only [e, neg_neg, le_refl]
  obtain ⟨hForward, hBackward⟩ := hMax.excludes_rays_of_forward_radial_criterion
    (hCriterion p hp) he hEnergyBound (hTheory.preserves_radiality hp hMax hInitialRadial)
  obtain ⟨Tminus, Tplus, hMinus, hPlus, hEq, hLeft, hRight⟩ :=
    hMax.finite_lifespan_and_gradient_divergence hp hTheory.continues_forward hForward hBackward
  subst J
  exact ⟨Tminus, Tplus, u, Du, hMinus, hPlus, hSame, hMax, hLeft, hRight⟩

end Blowup
