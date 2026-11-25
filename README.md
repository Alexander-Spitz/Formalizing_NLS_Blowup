# Formalizing radial NLS blow-up

Lean formalization of finite-time blow-up in both time directions for radial
two-dimensional focusing NLS with negative energy and real `p ≥ 3`.
The target proposition is [`Blowup.RadialNLSFiniteTimeBlowup`](BlowupFormalization/Specification.lean).
The superquintic case `p > 5` follows the argument in [the paper](main.pdf).
[Mathlib](https://github.com/leanprover-community/mathlib4) is the sole direct
Lake dependency. The checked development uses only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Results cited in the paper
are proof obligations in [PROGRESS.md](PROGRESS.md).

## Frozen statement

The protected tag `nls-blowup-spec-v1` points to
`1a95801e84b28b23d7ab9b51cb60fe9cbb95db9d`. It fixes the exact target
proposition, its PDE and initial-data definitions, and the Lean and Mathlib
versions used to interpret them. The project proof must inhabit
`Blowup.RadialNLSFiniteTimeBlowup`.

To inspect the statement at the frozen revision:

```sh
git fetch origin tag nls-blowup-spec-v1
git show nls-blowup-spec-v1:BlowupFormalization/Specification.lean
```

## Run the proof check

Install [Elan](https://lean-lang.org/install/) and Python 3.11 or newer. From
this repository's root, run the same check used in GitHub Actions.

```sh
LEAN_NUM_THREADS=2 python3 .github/check_proofs.py --get-mathlib-cache
```

Omit `--get-mathlib-cache` when the dependency cache is already available.
The check compares the frozen files with the protected tag, builds the library,
audits each declaration's transitive axiom footprint, and replays the proof
modules through the Lean kernel.
Keep project Lean sources in `BlowupFormalization/` so all of them are built
and checked. The initial scaffold and its unfinished arguments remain
available at commit `3183ab12b0877a270f4210db571b2ff0d5333196`.

The `main` ruleset requires a pull request, an up-to-date branch, and the
**Lean kernel and axioms** status check from GitHub Actions.

## Parallel proof work

Start a Codex session in this trusted checkout and ask it to coordinate a
proof round with subagents. For example, “Run the first proof round from
`PROGRESS.md` with separate worktrees. Review each branch before opening its
PR.” [AGENTS.md](AGENTS.md) defines the coordinator's review and publication
workflow. [PROGRESS.md](PROGRESS.md#first-proof-round) records the first
independent tasks.
