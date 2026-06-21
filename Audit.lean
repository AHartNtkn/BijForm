import Lean

def main : IO Unit := do
  let out ← IO.Process.output {
    cmd := "bash"
    args := #["scripts/audit.sh"]
  }
  unless out.stdout.isEmpty do
    IO.print out.stdout
  unless out.stderr.isEmpty do
    IO.eprint out.stderr
  if out.exitCode != 0 then
    throw <| IO.userError s!"audit failed with exit code {out.exitCode}"
