# Formalization progress: finite-time blow-up for radial 2D NLS (main.pdf)

**Target:** Theorem 1.1 of `main.pdf`, **only for 5 < p < ∞**. (The PDF's
"5 ≤ p" is a typo. p = 5 and lower powers are covered by other work.)

**Trust boundary (decided by the author):** the paper's own arguments are proved.
Only results the paper *cites* are assumed. Every one of them is an `axiom` in
`BlowupFormalization/Assumptions.lean`, with a docstring naming its source.
Nothing is assumed anywhere else. `#print axioms` on the main theorem lists
exactly which of them are used.

**Readability rules:** Lean names follow the paper's numbering (`lemma_4_1`,
`eq_4_6`, …). Docstrings quote the paper. There are few auxiliary
definitions, and all of them live in `Defs.lean`.

## File layout (planned)

| File | Content | Status |
|---|---|---|
| `Defs.lean` | ℝ², radial functions, H¹ with explicit weak gradient, mass, energy, NLS weak solution | todo |
| `Assumptions.lean` | cited results (Section 2, Cazenave H¹ theory, virial identities, GN/Sobolev) as axioms | todo |
| `Exponents.lean` | the exponent identities (3.1) and the facts derived from them | todo |
| `VirialWeight.lean` | Lemma 4.1 (fully proved) + weight properties (4.3) | todo |
| `LocalizedVirial.lean` | (4.6), (4.7) from the assumed identities (4.4)/(4.5) | todo |
| `PointSource.lean` | Lemma 3.1 | todo |
| `ExteriorEstimate.lean` | Proposition 3.2 | todo |
| `AbstractContradiction.lean` | the real-analysis core of Section 5 ((5.3)–(5.8)) | todo |
| `MainTheorem.lean` | Theorem 1.1 for 5 < p | todo |

## Order of work

1. Defs + statement of the main theorem (so the target is fixed early).
2. Lemma 4.1 (self-contained, no assumptions).
3. Section 5 real-analysis core.
4. Section 4 consequences (4.3), (4.6), (4.7).
5. Section 3 (Lemma 3.1, Prop 3.2): the biggest part.
6. Assemble; `#print axioms`; review every axiom for truth.

## Notes / decisions log

- Lemma 4.1 construction (simpler than the paper's log-averaging, same
  statement): let Φ(r) = r² − m − ((R₀ − r)⁺)² with R₀ = 9/2, G(r) = max(0, Φ(|r|)),
  g = G ∗ ρ for an even normed bump ρ supported in [−1/4, 1/4] with
  second moment m, and φ(r) = r² − g(r). Then g is convex ⇒ φ'' ≤ 2;
  φ = r² on |r| ≤ 2; φ = 0 on |r| ≥ 19/4.
- In (4.5) we use the general Hessian form 4 Re∫ ∂ⱼ∂ₖA ∂ⱼu ∂ₖū. The bound
  D²A ≤ 2I follows from convexity of |x|² − A. Radiality of u is not needed
  in Section 4.

## Current state

(update after each milestone)
