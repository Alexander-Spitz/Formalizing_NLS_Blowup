# Formalization progress: finite-time blow-up for radial 2D NLS (main.pdf)

**Target:** `Blowup.RadialNLSFiniteTimeBlowup` in
[`Specification.lean`](BlowupFormalization/Specification.lean). It states
finite-time blow-up and divergence of the gradient norm in both time
directions for every real `p ≥ 3` and radial H¹ initial datum of negative
energy. The proof combines `3 ≤ p < 5` (Ogawa–Tsutsumi), `p = 5`
(Guevara–Carreon), and `p > 5` (`main.pdf`).

**Trust boundary:** Mathlib is the only direct dependency. All proofs, including
results cited by the paper, must use only Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. The initial scaffold is available at
commit `3183ab12b0877a270f4210db571b2ff0d5333196`.

## Checked foundation

| Module | Content |
|---|---|
| `Defs.lean`, `SolutionFacts.lean` | Weak H¹ solutions, elementary solution facts, and compact moments |
| `Specification.lean` | The target proposition, including the unique maximal lifespan and both limits |
| `VirialWeight.lean`, `WeightProperties.lean` | Lemma 4.1 and the weight bounds |
| `Calculus.lean`, `ScaleSelection.lean`, `Section5.lean` | Calculus, scale selection, and scalar estimates |
| `ExteriorEstimate.lean`, `LocalizedVirial.lean` | Definitions used by the exterior and virial estimates |

## First proof round

These results are merged on `main`.

| Module | Result | PR |
|---|---|---|
| `H1Data.lean` | `SameH1Data` preserves `IsH1`, mass, squared gradient norm, and energy. | [#3](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/3) |
| `LocalizedVirial.lean` | `eq_4_7_value` bounds the initial localized variance by `compactMoment`. | [#4](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/4) |
| `ExteriorExponents.lean` | The exponents in (3.1)–(3.2) satisfy Schrödinger admissibility and the point-source Hölder relation for `p > 5`. | [#5](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/5) |

## Second proof round

These results are merged on `main`.

| Module | Result | PR |
|---|---|---|
| `LocalizedVirial.lean` | `eq_4_7_deriv` bounds the first virial expression by four times the product of the gradient norm and the square root of the localized variance. | [#6](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/6) |
| `LocalizedVirialBound.lean` | `virialSecondDeriv_virialWeight_le` proves the static estimate underlying (4.6) for `p ≥ 3` when the nonlinear density is integrable. | [#7](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/7) |
| `TimeReversal.lean` | `IsNLSSolution.conj_time_reversal` reflects weak solutions in time with complex conjugation. Conjugation preserves H¹ membership, mass, squared gradient norm, energy, and radiality. | [#8](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/8) |

## Third proof round

These results are merged on `main`.

| Module | Result | PR |
|---|---|---|
| `Section5.lean` | `terminal_virial_neg` integrates the acceleration and initial bounds to prove strict negativity of the terminal variance. | [#9](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/9) |
| `TimeReversal.lean` | Conjugate time reversal preserves maximality and transfers within-lifespan gradient limits at reflected endpoints. | [#10](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/10) |
| `SmoothVirial.lean` | `hasDerivAt_localizedVariance_of_smooth_nls` establishes (4.4) for jointly `C²` solutions of the pointwise equation. | [#11](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/11) |

## Fourth proof round

These results are merged on `main`.

| Module | Result | PR |
|---|---|---|
| `SmoothVirial.lean` | The first virial identity allows a pointwise forcing term, whose contribution is bounded by the product of the spatial L² norms. | [#12](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/12) |
| `VirialContinuity.lean` | The localized variance and first virial expression are continuous on the time domain of a weak solution. | [#13](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/13) |
| `Mollification.lean` | Spatial mollification maps L² data into smooth L² functions, commutes with the weak partial derivatives, and bounds the mass by the squared L¹ norm of the kernel times the input mass. | [#14](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/14) |

## Fifth proof round

These results are merged on `main`.

| Module | Result | PR |
|---|---|---|
| `SmoothVirial.lean` | The forced first identity needs only joint C¹ regularity and a C² spatial slice. Locally uniform convergence of the first virial terms and errors passes the derivative identity to the limit. | [#15](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/15) |
| `MollifierConvergence.lean` | Normalized shrinking kernels approximate weak H¹ functions and their weak partial derivatives in L². | [#16](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/16) |
| `MollifiedEquation.lean` | The spatially mollified weak equation holds at each spatial point against every temporal test in the interior of the time domain. | [#17](https://github.com/Alexander-Spitz/Formalizing_NLS_Blowup/pull/17) |

## First localized virial identity for weak solutions

`IsNLSSolution.hasDerivAt_localizedVariance` in
[`WeakFirstVirial.lean`](BlowupFormalization/WeakFirstVirial.lean) proves (4.4)
for every real `p ≥ 3`, every smooth compactly supported real weight, and
every interior time of a weak H¹ solution. The proof uses the weak H¹ Sobolev
embedding, continuity of the nonlinearity in L², and passage to the limit in
the forced identity for spatially mollified solutions.

## Proof obligations

- Prove the H¹ solution theory used by the paper: local existence and
  uniqueness, radiality preservation, conservation, continuation, and the
  Gagliardo–Nirenberg inequality for the chosen H¹ representation.
- Prove the second localized virial identity for weak H¹ solutions to apply
  the acceleration bound in (4.6), and the classical virial identities as needed.
- Formalize the localized virial arguments for `3 ≤ p < 5` and for `p = 5`.
- Prove the required dispersive estimates (including the cited prerequisites),
  Lemma 3.1, and Proposition 3.2.
- Assemble the superquintic contradiction from Section 5. Combine the three
  power ranges, using conjugate time reversal `u(t,x) ↦ conj (u(-t,x))` and
  the continuation criterion to prove the full target.

## Notes / decisions log

- Lemma 4.1 construction (simpler than the paper's log-averaging, same
  statement): let Φ(r) = r² − m − ((R₀ − r)⁺)² with R₀ = 9/2, G(r) = max(0, Φ(|r|)),
  g = G ∗ ρ for an even normed bump ρ supported in [−1/4, 1/4] with
  second moment m, and φ(r) = r² − g(r). Then g is convex ⇒ φ'' ≤ 2;
  φ = r² on |r| ≤ 2; φ = 0 on |r| ≥ 19/4.
- In (4.5) we use the general Hessian form 4 Re∫ ∂ⱼ∂ₖA ∂ⱼu ∂ₖū. The bound
  D²A ≤ 2I follows from convexity of |x|² − A. Radiality of u is not needed
  in Section 4.
