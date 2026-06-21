#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
checker="$repo_root/scripts/check-trivial-fin-ext.awk"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

write_case() {
  local name="$1"
  local body="$2"
  local file="$tmpdir/$name.lean"
  printf '%s\n' "$body" >"$file"
  printf '%s\n' "$file"
}

expect_rejects() {
  local name="$1"
  local body="$2"
  local file
  file="$(write_case "$name" "$body")"
  if awk -f "$checker" "$file" >/dev/null 2>&1; then
    printf 'expected %s to be rejected\n' "$name" >&2
    return 1
  fi
}

expect_accepts() {
  local name="$1"
  local body="$2"
  local file
  file="$(write_case "$name" "$body")"
  if ! awk -f "$checker" "$file" >/dev/null 2>&1; then
    printf 'expected %s to be accepted\n' "$name" >&2
    awk -f "$checker" "$file" >&2 || true
    return 1
  fi
}

expect_rejects adjacent $'theorem bad : True := by\n  apply Fin.ext\n  rfl'
expect_rejects blank_line $'theorem bad : True := by\n  apply Fin.ext\n\n  rfl'
expect_rejects comment_between $'theorem bad : True := by\n  apply Fin.ext\n  -- value equality is reflexive\n  rfl'
expect_rejects bullet_same_line $'theorem bad : True := by\n  apply Fin.ext\n  · rfl'
expect_rejects bullet_next_line $'theorem bad : True := by\n  apply Fin.ext\n  ·\n    exact rfl'
expect_rejects same_line_tactic $'theorem bad : True := by\n  apply Fin.ext; rfl'
expect_rejects exact_fin_ext $'theorem bad : True := by\n  exact Fin.ext rfl'

expect_accepts substantive_value_proof $'theorem ok : True := by\n  apply Fin.ext\n  exact hidx'
expect_accepts shared_helper $'theorem ok : True := by\n  exact fin_eq_of_val_eq rfl'

printf 'trivial Fin.ext audit tests: ok\n'
