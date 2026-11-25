# Coordinating Lean proofs

The final proof must establish `Blowup.RadialNLSFiniteTimeBlowup` for every
real `p ≥ 3`. The protected tag `nls-blowup-spec-v1` fixes the statement, its
PDE definitions, and the Lean and Mathlib pins. Use Mathlib and Lean's
standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Close each
submitted proof without project axioms, `sorry`, `admit`, or `native_decide`.

## Coordinator

When the owner asks to run a proof round, the top-level agent coordinates
it. Read `PROGRESS.md`, fetch `origin/main`, and select up to three ready,
independent tasks. Give each task an exact mathematical claim, paper section,
dependencies, owned files, and a success command. Split large arguments at
reusable lemmas. Assign a single owner to each file.

Create one worktree per task from the latest fetched `origin/main`.

```sh
git fetch origin main
bash scripts/new-proof-worktree.sh <task-slug>
```

The helper creates `proof/<task-slug>` under `.proof-worktrees/` and copies
compatible prepared dependencies if available. Reuse a worktree for follow-up
on the same task. If it has no package cache, initialize it with
`lake exe cache get` from that worktree. Keep each checkout's `.lake/build`
separate.

Spawn `lean_proof_worker` subagents where custom roles are available. Give
workers the absolute worktree path, branch, base commit, owned files, claim,
and checks. Pass the same instructions to a built-in worker if custom roles
are unavailable. Read each report and send corrections back to the same
worker. Schedule dependent work after its prerequisites land on `main`.

## Worker

Run commands and edit only in the assigned worktree. Work within the assigned
files and look for existing Mathlib lemmas before adding helpers. Use
`lake build +BlowupFormalization.ModuleName` to iterate, and identify the
claims and conditions that remain open. Report a missing dependency to the
coordinator promptly so it can be assigned or the scope adjusted.

Report the branch, base commit, changed files, Lean declarations, relevant
paper references, the checks you actually ran, and any remaining obligations.
Leave the edits in your worktree for review. The coordinator owns publication,
shared import changes, and updates to `PROGRESS.md`.

## Review and publish

The coordinator reviews the actual diff before creating a PR. Compare each
statement with the assignment and the source, including quantifiers, endpoint
cases, and assumptions. Inspect `#print axioms` for the new public theorems.
Update the branch to the latest `origin/main`, then commit the reviewed
candidate locally and run the same gate as GitHub on that checkout.

```sh
LEAN_NUM_THREADS=2 python3 .github/check_proofs.py
```

After the coordinator review and local gate pass, run the independent Claude
review in the same worktree. Give it the assigned mathematical claim and the
source reference. Supply any relevant Lean dependencies with `--context`.

```sh
python3 scripts/review-proof-with-claude.py --base origin/main \
  --claim 'State the exact assigned result and paper section here.'
```

The script sends the committed diff, claim, frozen specification and
definitions, and explicitly selected Lean context to Claude Code. Its
review session has no file, shell, or GitHub tools. An approval is valid for
the base and proof commit printed in the result. Resolve blocking findings
and repeat the coordinator, Lean, and Claude checks on the revised commit.
If Claude is unavailable or needs further context, keep the candidate local
until the independent review passes.

Push the approved commit and open one PR per reviewed milestone. Include the
declarations, paper reference, dependencies, Lean check result, and Claude
model and verdict in its description. Verify the required **Lean kernel and
axioms** check passes for the published PR. The owner decides when to merge.
Update recorded progress from merged results.
