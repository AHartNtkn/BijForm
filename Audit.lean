import Lean

def runProcess (cmd : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  unless out.stdout.isEmpty do
    IO.print out.stdout
  unless out.stderr.isEmpty do
    IO.eprint out.stderr
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"command failed with exit code {out.exitCode}: {cmd} {String.intercalate " " args.toList}"

def repoRoot : IO String := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["rev-parse", "--show-toplevel"]
  }
  unless out.stderr.isEmpty do
    IO.eprint out.stderr
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"failed to locate repository root with exit code {out.exitCode}"
  pure out.stdout.trimAscii.toString

def main : IO Unit := do
  let root ← repoRoot
  runProcess "lake" #["--dir", root, "build"]
  runProcess "bash" #[root ++ "/scripts/audit-checks.sh"]
