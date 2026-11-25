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

## Proof obligations

- Prove the H¹ solution theory used by the paper: local existence and
  uniqueness, radiality preservation, conservation, continuation, and the
  Gagliardo–Nirenberg inequality for the chosen H¹ representation.
- Prove the classical and localized virial identities, then (4.6)–(4.7).
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
