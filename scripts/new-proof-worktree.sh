#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 || ! $1 =~ ^[a-z0-9]+(-[a-z0-9]+)*$ ]]; then
  printf 'Usage: %s task-slug\n' "$0" >&2
  exit 2
fi

repo=$(git rev-parse --show-toplevel)
base=$(git -C "$repo" rev-parse --verify 'refs/remotes/origin/main^{commit}')
worktree="$repo/.proof-worktrees/$1"
git -C "$repo" worktree add -b "proof/$1" "$worktree" "$base" >&2

# Reuse the coordinator's prepared dependencies when the versions match.
# Each checkout gets its own writable package cache and project build directory.
if [[ -f "$repo/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]] &&
    cmp -s "$repo/lake-manifest.json" "$worktree/lake-manifest.json" &&
    cmp -s "$repo/lean-toolchain" "$worktree/lean-toolchain"; then
  mkdir -p "$worktree/.lake"
  package_copy=$(mktemp -d "$worktree/.lake/packages.XXXXXX")
  trap 'rm -rf -- "$package_copy"' EXIT
  cp -a --reflink=auto "$repo/.lake/packages/." "$package_copy/"
  mv "$package_copy" "$worktree/.lake/packages"
fi

printf '%s\n' "$worktree"
