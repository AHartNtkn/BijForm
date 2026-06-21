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

if git grep -n 'singleSortedFiniteSyntaxIso' -- BijForm; then
  fail "finite-coding syntax wrapper must not ignore finite coding data"
fi

if git grep -n 'OutputIndexInversion\.ofIso' -- BijForm/Examples; then
  fail "examples must not use low-level opaque output-index inversion"
fi

if git grep -n '\.toWellFoundedCode' -- BijForm/Examples; then
  fail "examples must expose generated-code APIs instead of WellFoundedCode backend conversion"
fi

if git grep -n -E 'Fin\.ext[[:space:]]+rfl' -- BijForm/StringDiagram/Bridge/GraphRenderRelation.lean; then
  fail "trivial inline Fin reconstruction proof found in GraphRenderRelation; use a shared helper"
fi

if awk '
  /apply[[:space:]]+Fin\.ext/ {
    prevLine = $0
    prevNr = NR
    pending = 1
    next
  }
  pending {
    if ($0 ~ /^[[:space:]]*(rfl|exact[[:space:]]+rfl)[[:space:]]*$/) {
      printf "%s:%d:%s\n%s:%d:%s\n", FILENAME, prevNr, prevLine, FILENAME, NR, $0
      found = 1
    }
    pending = 0
  }
  END { exit found ? 0 : 1 }
' BijForm/StringDiagram/Bridge/GraphRenderRelation.lean; then
  fail "trivial inline Fin reconstruction proof found in GraphRenderRelation; use fin_eq_of_val_eq or a more specific helper"
fi

printf 'audit: ok\n'
