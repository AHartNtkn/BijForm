function trim(s) {
  sub(/^[[:space:]]+/, "", s)
  sub(/[[:space:]]+$/, "", s)
  return s
}

function strip_comments(s,   out, i, rest, linePos, openPos, closePos) {
  out = ""
  i = 1
  while (i <= length(s)) {
    rest = substr(s, i)
    if (blockDepth > 0) {
      openPos = index(rest, "/-")
      closePos = index(rest, "-/")
      if (openPos == 0 && closePos == 0) {
        return out
      }
      if (closePos == 0 || (openPos != 0 && openPos < closePos)) {
        blockDepth++
        i += openPos + 1
      } else {
        blockDepth--
        i += closePos + 1
      }
    } else {
      linePos = index(rest, "--")
      openPos = index(rest, "/-")
      if (linePos == 0 && openPos == 0) {
        out = out rest
        break
      }
      if (linePos != 0 && (openPos == 0 || linePos < openPos)) {
        out = out substr(rest, 1, linePos - 1)
        break
      }
      out = out substr(rest, 1, openPos - 1)
      blockDepth++
      i += openPos + 1
    }
  }
  return out
}

function strip_bullets(s) {
  s = trim(s)
  while (s ~ /^·([[:space:]]|$)/) {
    sub(/^·[[:space:]]*/, "", s)
    s = trim(s)
  }
  return s
}

function normalized(s) {
  return strip_bullets(trim(strip_comments(s)))
}

function report(startFile, startLine, startText, endLine, endText) {
  printf "%s:%d:%s\n%s:%d:%s\n", startFile, startLine, startText, FILENAME, endLine, endText > "/dev/stderr"
  found = 1
}

{
  norm = normalized($0)

  if (norm ~ /(^|[;[:space:]])exact[[:space:]]+Fin\.ext[[:space:]]+rfl($|[;[:space:]])/) {
    report(FILENAME, NR, $0, NR, $0)
  }

  if (norm ~ /(^|[;[:space:]])apply[[:space:]]+Fin\.ext[[:space:]]*;[[:space:]]*(exact[[:space:]]+)?rfl($|[;[:space:]])/) {
    report(FILENAME, NR, $0, NR, $0)
  }

  if (pending) {
    if (norm == "") {
      next
    }
    if (norm == "rfl" || norm == "exact rfl") {
      report(pendingFile, pendingLine, pendingText, NR, $0)
    }
    pending = 0
  }

  if (norm == "apply Fin.ext") {
    pending = 1
    pendingFile = FILENAME
    pendingLine = NR
    pendingText = $0
  }
}

END {
  exit found ? 1 : 0
}
