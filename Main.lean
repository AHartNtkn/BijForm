import BijForm

def main : IO Unit :=
  IO.println s!"BijForm pairing examples: {(List.range 10).map BijForm.Pairing.decode}"
