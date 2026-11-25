import BlowupFormalization.Defs

/-!
# Assumed results from the literature

**This is the only file that contains axioms.** Each axiom is a standard result
that `main.pdf` cites rather than proves. `#print axioms Blowup.theorem_1_1` lists
exactly which of them the main theorem uses.

Each axiom must be *true*. A false axiom would make every theorem vacuous. So
each statement is written so that it holds for the precise Lean definitions in
`Defs.lean`. For example, statements about solutions never claim anything
pointwise in `x` that could fail after changing `u t` on a null set.

Sources:
* [Caz] T. Cazenave, *Semilinear Schrödinger equations*, Courant Lecture Notes 10, 2003
  (reference [1] of the paper).
* [GN] Gagliardo–Nirenberg inequality, see e.g. [Caz, Ch. 1].
-/

open MeasureTheory

namespace Blowup

/-! ## Notation for the virial identities (4.4)–(4.5) -/

/-- Right-hand side of (4.4): `2 Im ∫ ū ∇A·∇u`. -/
noncomputable def virialFirstDeriv (A : ℝ² → ℝ) (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  2 * ∫ x, (starRingEnd ℂ (u x) *
    (((partialDeriv 0 A x : ℝ) : ℂ) * Du 0 x + ((partialDeriv 1 A x : ℝ) : ℂ) * Du 1 x)).im

/-- Right-hand side of (4.5), written for a general (not necessarily radial) weight:
`4 Re ∫ Σⱼₖ ∂ⱼ∂ₖA ∂ⱼu ∂ₖū − 2(p−1)/(p+1) ∫ ΔA |u|^{p+1} − ∫ Δ²A |u|²`.
For radial `A` and `u` the first term is the paper's `4 ∫ A'' |u_r|²`. -/
noncomputable def virialSecondDeriv (p : ℝ) (A : ℝ² → ℝ) (u : ℝ² → ℂ)
    (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  4 * (∫ x, ∑ j : Fin 2, ∑ k : Fin 2,
      partialDeriv j (partialDeriv k A) x * (Du j x * starRingEnd ℂ (Du k x)).re)
  - 2 * (p - 1) / (p + 1) * (∫ x, laplacian A x * ‖u x‖ ^ (p + 1))
  - ∫ x, laplacian (laplacian A) x * ‖u x‖ ^ 2

/-! ## The axioms -/

/-- **Conservation of mass and energy** for `H¹` solutions (see [Caz, Ch. 4], the H¹ theory).
In two dimensions every power `p > 1` is `H¹`-subcritical. -/
axiom conservation_laws {p : ℝ} (hp : 1 < p) {T : ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (hsol : IsNLSSolution p (Set.Icc 0 T) u Du) :
    ∀ t ∈ Set.Icc 0 T,
      mass (u t) = mass (u 0) ∧ energy p (u t) (Du t) = energy p (u 0) (Du 0)

/-- **Sobolev embedding and Gagliardo–Nirenberg inequality** in `ℝ²` (see [Caz, Ch. 1]):
`H¹(ℝ²) ⊂ L^{p+1}` and `‖f‖_{p+1}^{p+1} ≤ C ‖f‖₂² ‖∇f‖₂^{p-1}`. -/
axiom gagliardo_nirenberg {p : ℝ} (hp : 1 < p) :
    ∃ C > 0, ∀ (f : ℝ² → ℂ) (Df : Fin 2 → ℝ² → ℂ), IsH1 f Df →
      MemLp f (ENNReal.ofReal (p + 1)) ∧
      potentialTerm p f ≤ C * mass f * gradNormSq Df ^ ((p - 1) / 2)

/-- **Localized virial identities (4.4)–(4.5)** for a smooth compactly supported weight `A`:
`V(t) = ∫ A |u(t)|²` is twice differentiable on `[0, T]` with
`V' = virialFirstDeriv` and `V'' = virialSecondDeriv`
(see [Caz, Ch. 6]; for `H¹` solutions they follow by approximation, as the paper notes). -/
axiom localized_virial {p : ℝ} (hp : 1 < p) {T : ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (hsol : IsNLSSolution p (Set.Icc 0 T) u Du)
    (A : ℝ² → ℝ) (hA : IsTestFunction A) :
    ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s ↦ ∫ x, A x * ‖u s x‖ ^ 2)
        (virialFirstDeriv A (u t) (Du t)) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s ↦ virialFirstDeriv A (u s) (Du s))
        (virialSecondDeriv p A (u t) (Du t)) (Set.Icc 0 T) t

/-- **Classical virial identity** for finite-variance data (see [Caz, Ch. 6])
(the "usual virial identity" of the introduction). If `|x| u₀ ∈ L²`, then
`V(t) = ∫ |x|² |u(t)|²` satisfies `V' = 4 Im ∫ ū x·∇u` and
`V'' = 8 ‖∇u‖₂² − 8(p−1)/(p+1) ‖u‖_{p+1}^{p+1}`. -/
axiom classical_virial {p : ℝ} (hp : 1 < p) {T : ℝ} {u : ℝ → ℝ² → ℂ}
    {Du : ℝ → Fin 2 → ℝ² → ℂ} (hsol : IsNLSSolution p (Set.Icc 0 T) u Du)
    (hvar : Integrable (fun x : ℝ² ↦ ‖x‖ ^ 2 * ‖u 0 x‖ ^ 2)) :
    ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s ↦ ∫ x, ‖x‖ ^ 2 * ‖u s x‖ ^ 2)
        (4 * ∫ x, (starRingEnd ℂ (u t x) * ((x 0 : ℂ) * Du t 0 x + (x 1 : ℂ) * Du t 1 x)).im)
        (Set.Icc 0 T) t ∧
      HasDerivWithinAt
        (fun s ↦ 4 * ∫ x,
          (starRingEnd ℂ (u s x) * ((x 0 : ℂ) * Du s 0 x + (x 1 : ℂ) * Du s 1 x)).im)
        (8 * gradNormSq (Du t) - 8 * (p - 1) / (p + 1) * potentialTerm p (u t))
        (Set.Icc 0 T) t

end Blowup
