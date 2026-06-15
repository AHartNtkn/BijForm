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

/-- Constructors for the numeric-expression family from the Peano-expression
section: variables, zero, successor, addition, and multiplication. -/
inductive NumCtor where
  | var
  | zero
  | succ
  | plus
  | times
deriving DecidableEq, Repr

def NumParam : NumCtor → Type
  | .var => Σ k : Nat, Fin (k + 1)
  | .zero => Nat
  | .succ => Nat
  | .plus => Nat
  | .times => Nat

def NumOut : (c : NumCtor) → NumParam c → Nat
  | .var, p => p.1
  | .zero, k => k
  | .succ, k => k
  | .plus, k => k
  | .times, k => k

def NumPos : (c : NumCtor) → NumParam c → Type
  | .var, _ => Empty
  | .zero, _ => Empty
  | .succ, _ => Unit
  | .plus, _ => Bool
  | .times, _ => Bool

def NumInput : {c : NumCtor} → (p : NumParam c) → NumPos c p → Nat
  | .var, _, q => nomatch q
  | .zero, _, q => nomatch q
  | .succ, k, _ => k
  | .plus, k, _ => k
  | .times, k, _ => k

/-- Dependent polynomial for numeric expressions indexed by available variables. -/
def NumPoly : DepPoly Nat where
  Ctor := NumCtor
  Param := NumParam
  out := NumOut
  Pos := NumPos
  input := NumInput

inductive NumCode (k : Nat) where
  | var (v : Fin (k + 1))
  | zero
  | succ
  | plus
  | times

def NumDecode (k : Nat) : NumCode k → Fiber NumPoly k
  | .var v => ⟨.var, ⟨k, v⟩, rfl⟩
  | .zero => ⟨.zero, k, rfl⟩
  | .succ => ⟨.succ, k, rfl⟩
  | .plus => ⟨.plus, k, rfl⟩
  | .times => ⟨.times, k, rfl⟩

def NumEncode (k : Nat) : Fiber NumPoly k → NumCode k
  | ⟨.var, p, h⟩ =>
      have _ : NumPoly.out NumCtor.var p = k := h
      .var (k := k) (h ▸ p.2)
  | ⟨.zero, _, _⟩ => .zero
  | ⟨.succ, _, _⟩ => .succ
  | ⟨.plus, _, _⟩ => .plus
  | ⟨.times, _, _⟩ => .times

theorem Num_decode_encode (k : Nat) (f : Fiber NumPoly k) :
    NumDecode k (NumEncode k f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | var =>
        cases param with
        | mk k' v =>
          cases out_eq
          rfl
    | zero =>
        cases out_eq
        rfl
    | succ =>
        cases out_eq
        rfl
    | plus =>
        cases out_eq
        rfl
    | times =>
        cases out_eq
        rfl

theorem Num_encode_decode (k : Nat) (c : NumCode k) :
    NumEncode k (NumDecode k c) = c := by
  cases c <;> rfl

/-- Output-index inversion for numeric expressions.  This is the same-fiber
case: the output index is simply exposed as the local context size `k`. -/
def NumInversion : OutputIndexInversion NumPoly where
  Code := NumCode
  decode := NumDecode
  encode := NumEncode
  decode_encode := Num_decode_encode
  encode_decode := Num_encode_decode

/-- Constructors for Peano formulas indexed by context size. -/
inductive PeanoCtor where
  | eq
  | not
  | implies
  | forallE
deriving DecidableEq, Repr

def PeanoParam : PeanoCtor → Type
  | .eq => Σ k : Nat, Mu NumPoly k × Mu NumPoly k
  | .not => Nat
  | .implies => Nat
  | .forallE => Nat

def PeanoOut : (c : PeanoCtor) → PeanoParam c → Nat
  | .eq, p => p.1
  | .not, k => k
  | .implies, k => k
  | .forallE, k => k

def PeanoPos : (c : PeanoCtor) → PeanoParam c → Type
  | .eq, _ => Empty
  | .not, _ => Unit
  | .implies, _ => Bool
  | .forallE, _ => Unit

def PeanoInput : {c : PeanoCtor} → (p : PeanoParam c) → PeanoPos c p → Nat
  | PeanoCtor.eq, _, q => nomatch q
  | PeanoCtor.not, (k : Nat), _ => k
  | PeanoCtor.implies, (k : Nat), _ => k
  | PeanoCtor.forallE, (k : Nat), _ => k + 1

/-- Dependent polynomial for Peano formulas. -/
def PeanoPoly : DepPoly Nat where
  Ctor := PeanoCtor
  Param := PeanoParam
  out := PeanoOut
  Pos := PeanoPos
  input := PeanoInput

inductive PeanoCode (k : Nat) where
  | eq (lhs rhs : Mu NumPoly k)
  | not
  | implies
  | forallE

def PeanoDecode (k : Nat) : PeanoCode k → Fiber PeanoPoly k
  | .eq lhs rhs => ⟨.eq, ⟨k, (lhs, rhs)⟩, rfl⟩
  | .not => ⟨.not, k, rfl⟩
  | .implies => ⟨.implies, k, rfl⟩
  | .forallE => ⟨.forallE, k, rfl⟩

def PeanoEncode (k : Nat) : Fiber PeanoPoly k → PeanoCode k
  | ⟨.eq, p, h⟩ =>
      have _ : PeanoPoly.out PeanoCtor.eq p = k := h
      .eq (k := k) (h ▸ p.2.1) (h ▸ p.2.2)
  | ⟨.not, _, _⟩ => .not
  | ⟨.implies, _, _⟩ => .implies
  | ⟨.forallE, _, _⟩ => .forallE

theorem Peano_decode_encode (k : Nat) (f : Fiber PeanoPoly k) :
    PeanoDecode k (PeanoEncode k f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | eq =>
        cases param with
        | mk k' pair =>
          cases pair with
          | mk lhs rhs =>
            cases out_eq
            rfl
    | not =>
        cases out_eq
        rfl
    | implies =>
        cases out_eq
        rfl
    | forallE =>
        cases out_eq
        rfl

theorem Peano_encode_decode (k : Nat) (c : PeanoCode k) :
    PeanoEncode k (PeanoDecode k c) = c := by
  cases c <;> rfl

/-- Output-index inversion for Peano formulas.  The `forallE` constructor keeps
the output context at `k` while its recursive child lives at `k+1`. -/
def PeanoInversion : OutputIndexInversion PeanoPoly where
  Code := PeanoCode
  decode := PeanoDecode
  encode := PeanoEncode
  decode_encode := Peano_decode_encode
  encode_decode := Peano_encode_decode

end Examples
end BijForm
