import Mathlib

/-!
# Basic definitions

The spatial and PDE definitions use explicit integrals and weak gradients so
they can be compared with the paper directly.

* `ℝ²` is the Euclidean plane.
* A function `u₀ : ℝ² → ℂ` is in `H¹` with weak partial derivatives `Du₀ j`
  (`IsH1 u₀ Du₀`) if `u₀` and both `Du₀ j` are in `L²` and integrate by parts
  against every smooth compactly supported test function.
* `mass`, `gradNormSq`, `energy` are `M(u) = ‖u‖₂²`, `‖∇u‖₂²` and
  `E_p(u) = ½‖∇u‖₂² − 1/(p+1) ‖u‖_{p+1}^{p+1}` from (1.2).
* `IsNLSSolution p J u Du` says that `u ∈ C(J; H¹(ℝ²))` (with weak gradient
  `Du`) solves `i u_t + Δu + |u|^{p-1} u = 0` in the sense of distributions on
  the interior of the time interval `J`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Blowup

/-- The plane `ℝ²`. -/
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The partial derivative `∂ⱼ f(x)` of a (classically differentiable) function on `ℝ²`. -/
noncomputable def partialDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : Fin 2) (f : ℝ² → F) (x : ℝ²) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

/-- The Laplacian `Δf = ∂₀∂₀f + ∂₁∂₁f` on `ℝ²`. -/
noncomputable def laplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ² → F) (x : ℝ²) : F :=
  partialDeriv 0 (partialDeriv 0 f) x + partialDeriv 1 (partialDeriv 1 f) x

/-- A test function on `ℝ²`: real valued, smooth, compactly supported. -/
def IsTestFunction (φ : ℝ² → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- `u ∈ H¹(ℝ²)`, with weak partial derivatives `Du 0`, `Du 1`:
`u, ∂ⱼu ∈ L²` and `∫ u ∂ⱼφ = -∫ (∂ⱼu) φ` for every test function `φ`. -/
structure IsH1 (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : Prop where
  memL2 : MemLp u 2
  memL2_partial : ∀ j, MemLp (Du j) 2
  integration_by_parts : ∀ φ : ℝ² → ℝ, IsTestFunction φ → ∀ j,
    ∫ x, u x * ((partialDeriv j φ x : ℝ) : ℂ) = -∫ x, Du j x * (φ x : ℂ)

/-- `u` is radial: it depends only on `|x|`. -/
def IsRadial (u : ℝ² → ℂ) : Prop :=
  ∀ x y : ℝ², ‖x‖ = ‖y‖ → u x = u y

/-- The mass `M(u) = ‖u‖₂² = ∫ |u|²` from (1.2). -/
noncomputable def mass (u : ℝ² → ℂ) : ℝ :=
  ∫ x, ‖u x‖ ^ 2

/-- The kinetic term `‖∇u‖₂² = ∫ |∂₀u|² + |∂₁u|²`. -/
noncomputable def gradNormSq (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  ∫ x, ‖Du 0 x‖ ^ 2 + ‖Du 1 x‖ ^ 2

/-- The potential term `‖u‖_{p+1}^{p+1} = ∫ |u|^{p+1}`. -/
noncomputable def potentialTerm (p : ℝ) (u : ℝ² → ℂ) : ℝ :=
  ∫ x, ‖u x‖ ^ (p + 1)

/-- The energy `E_p(u) = ½ ‖∇u‖₂² − 1/(p+1) ‖u‖_{p+1}^{p+1}` from (1.2). -/
noncomputable def energy (p : ℝ) (u : ℝ² → ℂ) (Du : Fin 2 → ℝ² → ℂ) : ℝ :=
  gradNormSq Du / 2 - potentialTerm p u / (p + 1)

/-- The focusing nonlinearity `N_p(z) = |z|^{p-1} z`. -/
noncomputable def nonlinearity (p : ℝ) (z : ℂ) : ℂ :=
  (‖z‖ ^ (p - 1) : ℝ) * z

/-- The integrand obtained by testing the focusing NLS against `φ`. -/
noncomputable def nlsTestIntegrand (p : ℝ) (u : ℝ → ℝ² → ℂ) (φ : ℝ → ℝ² → ℝ)
    (t : ℝ) (x : ℝ²) : ℂ :=
  u t x * (-Complex.I * ((deriv (fun s ↦ φ s x) t : ℝ) : ℂ) + ((laplacian (φ t) x : ℝ) : ℂ))
    + nonlinearity p (u t x) * (φ t x : ℂ)

/-- `u` solves (1.1) on the time interval `J` in the following sense
(the standard `H¹` solutions of [Cazenave]):

* for every `t ∈ J`, `u t ∈ H¹(ℝ²)` with weak partial derivatives `Du t`;
* `t ↦ u t` and `t ↦ Du t` are continuous into `L²` on `J`, i.e. `u ∈ C(J; H¹)`;
* for every smooth compactly supported test function `φ(t, x)` whose support lies in
  `(interior J) × ℝ²`,
  `∫∫ u (-i ∂ₜφ + Δφ) + |u|^{p-1} u φ dx dt = 0`,
  with integrability for both integrals. This is (1.1) tested against `φ`. -/
structure IsNLSSolution (p : ℝ) (J : Set ℝ) (u : ℝ → ℝ² → ℂ) (Du : ℝ → Fin 2 → ℝ² → ℂ) :
    Prop where
  h1 : ∀ t ∈ J, IsH1 (u t) (Du t)
  continuous_L2 : ∀ t ∈ J,
    Tendsto (fun s ↦ ∫ x, ‖u s x - u t x‖ ^ 2) (𝓝[J] t) (𝓝 0)
  continuous_grad_L2 : ∀ t ∈ J, ∀ j,
    Tendsto (fun s ↦ ∫ x, ‖Du s j x - Du t j x‖ ^ 2) (𝓝[J] t) (𝓝 0)
  weak_equation : ∀ φ : ℝ → ℝ² → ℝ,
    ContDiff ℝ ∞ (Function.uncurry φ) → HasCompactSupport (Function.uncurry φ) →
    tsupport (Function.uncurry φ) ⊆ interior J ×ˢ Set.univ →
    (∀ t, Integrable (nlsTestIntegrand p u φ t)) ∧
      Integrable (fun t ↦ ∫ x, nlsTestIntegrand p u φ t x) ∧
      ∫ t, ∫ x, nlsTestIntegrand p u φ t x = 0

end Blowup
