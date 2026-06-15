import BijForm.DependentPolynomial

namespace BijForm
namespace Examples

open DepPoly

/-- Constructors for the height-bounded-tree example from the Gödel-encoding
post: leaves carry a natural label, branches have two children. -/
inductive HBTCtor where
  | leaf
  | branch
deriving DecidableEq, Repr

def HBTParam : HBTCtor → Type
  | .leaf => Nat × Nat
  | .branch => Nat

def HBTOut : (c : HBTCtor) → HBTParam c → Nat
  | HBTCtor.leaf, p => p.1
  | HBTCtor.branch, (n : Nat) => n + 1

def HBTPos : (c : HBTCtor) → HBTParam c → Type
  | HBTCtor.leaf, _ => Empty
  | HBTCtor.branch, _ => Bool

def HBTInput : {c : HBTCtor} → (p : HBTParam c) → HBTPos c p → Nat
  | HBTCtor.leaf, _, q => nomatch q
  | HBTCtor.branch, (n : Nat), _ => n

/-- Raw height-bounded-tree polynomial.  The branch constructor outputs `n+1`;
`HBTInversion` below is the same-fiber inversion of that output index. -/
def HBTPoly : DepPoly Nat where
  Ctor := HBTCtor
  Param := HBTParam
  out := HBTOut
  Pos := HBTPos
  input := HBTInput

/-- Index-local constructor codes for height-bounded trees.  At target height
`i`, a branch code must include an explicit predecessor `m` with `m + 1 = i`.
This is the Lean form of the bounded-height-tree refactoring from the post. -/
inductive HBTCode (i : Nat) where
  | leaf (label : Nat)
  | branch (m : Nat) (out_eq : m + 1 = i)

def HBTDecode (i : Nat) : HBTCode i → Fiber HBTPoly i
  | .leaf label => ⟨.leaf, (i, label), rfl⟩
  | .branch m h => ⟨.branch, m, h⟩

def HBTEncode (i : Nat) : Fiber HBTPoly i → HBTCode i
  | ⟨.leaf, p, h⟩ =>
      have _ : HBTPoly.out HBTCtor.leaf p = i := h
      .leaf (i := i) p.2
  | ⟨.branch, m, h⟩ => .branch (i := i) m h

theorem HBT_decode_encode (i : Nat) (f : Fiber HBTPoly i) :
    HBTDecode i (HBTEncode i f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | leaf =>
        cases param with
        | mk n label =>
          cases out_eq
          rfl
    | branch =>
        rfl

theorem HBT_encode_decode (i : Nat) (c : HBTCode i) :
    HBTEncode i (HBTDecode i c) = c := by
  cases c with
  | leaf label => rfl
  | branch m h => rfl

/-- The non-opaque output-index inversion for the height-bounded-tree example. -/
def HBTInversion : OutputIndexInversion HBTPoly where
  Code := HBTCode
  decode := HBTDecode
  encode := HBTEncode
  decode_encode := HBT_decode_encode
  encode_decode := HBT_encode_decode

/-- The fiber of branch constructors at height zero is empty. -/
theorem no_zero_height_branch (f : Fiber HBTPoly 0) (hctor : f.ctor = .branch) :
    False := by
  cases f with
  | mk ctor param out_eq =>
    cases hctor
    cases out_eq

/-- The fiber of branch constructors at `m+1` contains the predecessor `m`. -/
def branchAtSucc (m : Nat) : Fiber HBTPoly (m + 1) :=
  HBTDecode (m + 1) (.branch m rfl)

end Examples
end BijForm
