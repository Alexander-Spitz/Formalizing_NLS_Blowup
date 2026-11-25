# Formalizing radial NLS blow-up

Lean formalization of finite-time blow-up in both time directions for radial
two-dimensional focusing NLS with negative energy and real `p ≥ 3`.
The target proposition is [`Blowup.RadialNLSFiniteTimeBlowup`](BlowupFormalization/Specification.lean).
The superquintic case `p > 5` follows the argument in [the paper](main.pdf).
[Mathlib](https://github.com/leanprover-community/mathlib4) is the sole direct
Lake dependency. The checked development uses only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Results cited in the paper
are proof obligations in [PROGRESS.md](PROGRESS.md).

## Run the proof check

Install [Elan](https://lean-lang.org/install/) and Python 3.11 or newer. From
this repository's root, run the same check used in GitHub Actions.

```sh
LEAN_NUM_THREADS=2 python3 .github/check_proofs.py --get-mathlib-cache
```

Omit `--get-mathlib-cache` when the dependency cache is already available.
The check builds the library, audits each declaration's transitive axiom
footprint, and replays the proof modules through the Lean kernel.
Keep project Lean sources in `BlowupFormalization/` so all of them are built
and checked. The initial scaffold and its unfinished arguments remain
available at commit `3183ab12b0877a270f4210db571b2ff0d5333196`.

## Enforce the check on GitHub

Once the workflow has reported its first result, create an active branch
ruleset for `main` under **Settings → Rules → Rulesets**. Require a pull
request, an up-to-date branch, and the **Lean kernel and axioms** status
check from GitHub Actions. Leave the bypass list empty. Require code-owner
review for CI and dependency changes when a reviewer distinct from the PR
author is available.
