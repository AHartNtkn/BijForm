#!/usr/bin/env bash
set -euo pipefail

fail() {
  printf 'audit: %s\n' "$*" >&2
  exit 1
}

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build

if ! git check-ignore -q references/; then
  fail "references/ must be ignored by repository configuration"
fi

if git grep -n -E '^[[:space:]]*(admit|axiom|unsafe|opaque|partial)([[:space:]]|$)' -- '*.lean'; then
  fail "forbidden proof substitute or unsafe declaration found"
fi

if git grep -n 'implemented_by' -- '*.lean'; then
  fail "implemented_by proof substitute found"
fi

if git grep -n -E '(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)' -- '*.lean' >/tmp/bijform-sorry-hits.txt; then
  while IFS= read -r hit; do
    file="${hit%%:*}"
    rest="${hit#*:}"
    line="${rest%%:*}"
    start=$((line > 3 ? line - 3 : 1))
    context="$(sed -n "${start},${line}p" "$file")"
    if ! printf '%s\n' "$context" | grep -Eiq 'unfinished|blueprint|proof-gap|pending proof|pending proof work|diagnostic'; then
      cat /tmp/bijform-sorry-hits.txt >&2
      fail "unclassified sorry found; label it as unfinished blueprinting, pending proof work, proof-gap evidence, or diagnostic"
    fi
  done </tmp/bijform-sorry-hits.txt
fi

if git grep -n -E 'QuotientPresentation\.inn($|[^R[:alnum:]_])|QuotientPresentation\.inn_layer_sound|HBTChildSwap_inn_branch_sound' -- README.md BijForm; then
  fail "stale quotient declaration name found"
fi

if git grep -n -E '^def [A-Za-z0-9_]*WellFoundedCode[[:space:]]*:' -- BijForm/Examples; then
  fail "example exposes a pass-through WellFoundedCode alias"
fi

printf 'audit: ok\n'
