#!/usr/bin/env bash
set -euo pipefail

fail() {
  printf 'audit: %s\n' "$*" >&2
  exit 1
}

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

tmpdir="$(mktemp -d)"
cleanup() {
  rm -rf "$tmpdir"
}
trap cleanup EXIT

if ! git check-ignore -q references/; then
  fail "references/ must be ignored by repository configuration"
fi

if git grep -n -E '^[[:space:]]*(admit|axiom|unsafe|opaque|partial)([[:space:]]|$)' -- '*.lean'; then
  fail "forbidden proof substitute or unsafe declaration found"
fi

if git grep -n 'implemented_by' -- '*.lean'; then
  fail "implemented_by proof substitute found"
fi

sorry_hits="$tmpdir/sorry-hits.txt"
if git grep -n -E '(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)' -- '*.lean' >"$sorry_hits"; then
  while IFS= read -r hit; do
    file="${hit%%:*}"
    rest="${hit#*:}"
    line="${rest%%:*}"
    start=$((line > 3 ? line - 3 : 1))
    context="$(sed -n "${start},${line}p" "$file")"
    if ! printf '%s\n' "$context" | grep -Eiq 'unfinished|blueprint|proof-gap|pending proof|pending proof work|diagnostic'; then
      cat "$sorry_hits" >&2
      fail "unclassified sorry found; label it as unfinished blueprinting, pending proof work, proof-gap evidence, or diagnostic"
    fi
  done <"$sorry_hits"
fi

bash scripts/test-trivial-fin-ext-audit.sh

mapfile -t lean_files < <(git ls-files '*.lean')
if ! awk -f scripts/check-trivial-fin-ext.awk "${lean_files[@]}"; then
  fail "trivial inline Fin reconstruction proof found; use fin_eq_of_val_eq or a more specific helper"
fi

printf 'audit: ok\n'
