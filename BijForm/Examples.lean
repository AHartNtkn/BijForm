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

/-- Upper bounds for sorted trees.  `none` represents infinity. -/
abbrev Bound :=
  Option Nat

def Bound.le (x : Nat) : Bound → Prop
  | none => True
  | some m => x ≤ m

abbrev SortedIx :=
  Nat × Bound

def BoundedPivot (i : SortedIx) : Type :=
  { x : Nat // i.1 ≤ x ∧ Bound.le x i.2 }

/-- Constructors for the sorted-tree example. -/
inductive SortedCtor where
  | leaf
  | branch
deriving DecidableEq, Repr

def SortedParam : SortedCtor → Type
  | .leaf => SortedIx
  | .branch => Σ i : SortedIx, BoundedPivot i

def SortedOut : (c : SortedCtor) → SortedParam c → SortedIx
  | .leaf, i => i
  | .branch, p => p.1

def SortedPos : (c : SortedCtor) → SortedParam c → Type
  | .leaf, _ => Empty
  | .branch, _ => Bool

def SortedInput : {c : SortedCtor} → (p : SortedParam c) → SortedPos c p → SortedIx
  | SortedCtor.leaf, _, q => nomatch q
  | SortedCtor.branch, p, (side : Bool) =>
      if side then
        (p.2.1, p.1.2)
      else
        (p.1.1, some p.2.1)

/-- Dependent polynomial for sorted trees indexed by lower and upper bounds. -/
def SortedPoly : DepPoly SortedIx where
  Ctor := SortedCtor
  Param := SortedParam
  out := SortedOut
  Pos := SortedPos
  input := SortedInput

inductive SortedCode (i : SortedIx) where
  | leaf
  | branch (pivot : BoundedPivot i)

def SortedDecode (i : SortedIx) : SortedCode i → Fiber SortedPoly i
  | .leaf => ⟨.leaf, i, rfl⟩
  | .branch pivot => ⟨.branch, ⟨i, pivot⟩, rfl⟩

def SortedEncode (i : SortedIx) : Fiber SortedPoly i → SortedCode i
  | ⟨.leaf, _, _⟩ => .leaf
  | ⟨.branch, p, h⟩ =>
      have _ : SortedPoly.out SortedCtor.branch p = i := h
      .branch (i := i) (h ▸ p.2)

theorem Sorted_decode_encode (i : SortedIx) (f : Fiber SortedPoly i) :
    SortedDecode i (SortedEncode i f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | leaf =>
        cases out_eq
        rfl
    | branch =>
        cases param with
        | mk i' pivot =>
          cases out_eq
          rfl

theorem Sorted_encode_decode (i : SortedIx) (c : SortedCode i) :
    SortedEncode i (SortedDecode i c) = c := by
  cases c <;> rfl

/-- Output-index inversion for sorted trees.  The branch code exposes the
bounded pivot whose children move to `(lower, pivot)` and `(pivot, upper)`. -/
def SortedInversion : OutputIndexInversion SortedPoly where
  Code := SortedCode
  decode := SortedDecode
  encode := SortedEncode
  decode_encode := Sorted_decode_encode
  encode_decode := Sorted_encode_decode

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

/-- Readable syntax family for height-bounded trees. -/
inductive HBTSyntax : Nat → Type
  | leaf {i : Nat} (label : Nat) : HBTSyntax i
  | branch {m : Nat} : HBTSyntax m → HBTSyntax m → HBTSyntax (m + 1)

namespace HBTSyntax

def rank : ∀ {i : Nat}, HBTSyntax i → Nat
  | _, leaf _ => 0
  | _, branch lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end HBTSyntax

def HBTObjToSyntax (i : Nat) : Obj HBTPoly HBTSyntax i → HBTSyntax i
  | ⟨.leaf, p, h, _child⟩ =>
      have _ : p.1 = i := h
      .leaf p.2
  | ⟨.branch, _m, h, child⟩ =>
      h ▸ (.branch (child false) (child true))

def HBTSyntaxToObj (i : Nat) : HBTSyntax i → Obj HBTPoly HBTSyntax i
  | .leaf label => ⟨.leaf, (i, label), rfl, fun q => nomatch q⟩
  | @HBTSyntax.branch m lhs rhs =>
      ⟨.branch, m, rfl, fun (b : Bool) => if b then rhs else lhs⟩

theorem HBTObj_left_inv (i : Nat) :
    Function.LeftInverse (HBTSyntaxToObj i) (HBTObjToSyntax i) := by
  intro layer
  cases layer with
  | mk ctor param out_eq child =>
    cases ctor with
    | leaf =>
        cases param with
        | mk n label =>
          cases out_eq
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
    | branch =>
        cases out_eq
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl

theorem HBTObj_right_inv (i : Nat) :
    Function.RightInverse (HBTSyntaxToObj i) (HBTObjToSyntax i) := by
  intro t
  cases t <;> simp [HBTObjToSyntax, HBTSyntaxToObj]

def HBTObjIso (i : Nat) : Obj HBTPoly HBTSyntax i ≃ᵢ HBTSyntax i where
  toFun := HBTObjToSyntax i
  invFun := HBTSyntaxToObj i
  left_inv := HBTObj_left_inv i
  right_inv := HBTObj_right_inv i

theorem HBT_child_rank_lt :
    ∀ {i : Nat} (z : HBTSyntax i)
      (q : HBTPoly.Pos ((HBTObjIso i).invFun z).ctor ((HBTObjIso i).invFun z).param),
      HBTSyntax.rank (((HBTObjIso i).invFun z).child q) < HBTSyntax.rank z := by
  intro i z q
  cases z with
  | leaf label => cases q
  | branch lhs rhs =>
      cases q
      · simpa [HBTObjIso, HBTSyntaxToObj, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))
      · simpa [HBTObjIso, HBTSyntaxToObj, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))

def HBTWellFoundedCode : WellFoundedCode HBTPoly HBTSyntax where
  step := HBTObjIso
  rank := fun _ t => HBTSyntax.rank t
  child_rank_lt := HBT_child_rank_lt

/-- Height-bounded trees as the generic initial algebra are bijective with
readable syntax.  The branch case is the output-index-change example: it
constructs a tree at height `m + 1` from two children at height `m`. -/
def HBTSyntaxIso (i : Nat) : Mu HBTPoly i ≃ᵢ HBTSyntax i :=
  initialAlgebraCoding HBTPoly HBTSyntax HBTWellFoundedCode i

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

/-- Readable syntax family for numeric expressions. -/
inductive NumSyntax : Nat → Type
  | var {k : Nat} (v : Fin (k + 1)) : NumSyntax k
  | zero {k : Nat} : NumSyntax k
  | succ {k : Nat} : NumSyntax k → NumSyntax k
  | plus {k : Nat} : NumSyntax k → NumSyntax k → NumSyntax k
  | times {k : Nat} : NumSyntax k → NumSyntax k → NumSyntax k

namespace NumSyntax

def rank : ∀ {k : Nat}, NumSyntax k → Nat
  | _, var _ => 0
  | _, zero => 0
  | _, succ e => rank e + 1
  | _, plus lhs rhs => Nat.max (rank lhs) (rank rhs) + 1
  | _, times lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end NumSyntax

def NumObjToSyntax (k : Nat) : Obj NumPoly NumSyntax k → NumSyntax k
  | ⟨.var, p, h, _child⟩ =>
      .var (h ▸ p.2)
  | ⟨.zero, _, _h, _child⟩ =>
      .zero
  | ⟨.succ, _p, h, child⟩ =>
      .succ (h ▸ child ())
  | ⟨.plus, _p, h, child⟩ =>
      .plus (h ▸ child false) (h ▸ child true)
  | ⟨.times, _p, h, child⟩ =>
      .times (h ▸ child false) (h ▸ child true)

def NumSyntaxToObj (k : Nat) : NumSyntax k → Obj NumPoly NumSyntax k
  | .var v => ⟨.var, ⟨k, v⟩, rfl, fun q => nomatch q⟩
  | .zero => ⟨.zero, k, rfl, fun q => nomatch q⟩
  | .succ e => ⟨.succ, k, rfl, fun _ => e⟩
  | .plus lhs rhs => ⟨.plus, k, rfl, fun (b : Bool) => if b then rhs else lhs⟩
  | .times lhs rhs => ⟨.times, k, rfl, fun (b : Bool) => if b then rhs else lhs⟩

theorem NumObj_left_inv (k : Nat) :
    Function.LeftInverse (NumSyntaxToObj k) (NumObjToSyntax k) := by
  intro layer
  cases layer with
  | mk ctor param out_eq child =>
    cases ctor with
      | var =>
          cases param with
          | mk k' v =>
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
      | zero =>
          cases out_eq
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | succ =>
          cases out_eq
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          rfl
      | plus =>
          cases out_eq
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl
      | times =>
          cases out_eq
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl

theorem NumObj_right_inv (k : Nat) :
    Function.RightInverse (NumSyntaxToObj k) (NumObjToSyntax k) := by
  intro e
  cases e <;> simp [NumObjToSyntax, NumSyntaxToObj]

def NumObjIso (k : Nat) : Obj NumPoly NumSyntax k ≃ᵢ NumSyntax k where
  toFun := NumObjToSyntax k
  invFun := NumSyntaxToObj k
  left_inv := NumObj_left_inv k
  right_inv := NumObj_right_inv k

theorem Num_child_rank_lt :
    ∀ {k : Nat} (z : NumSyntax k)
      (q : NumPoly.Pos ((NumObjIso k).invFun z).ctor ((NumObjIso k).invFun z).param),
      NumSyntax.rank (((NumObjIso k).invFun z).child q) < NumSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | zero => cases q
  | succ e =>
      cases q
      simp [NumObjIso, NumSyntaxToObj, NumSyntax.rank]
  | plus lhs rhs =>
      cases q
      · simpa [NumObjIso, NumSyntaxToObj, NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumObjIso, NumSyntaxToObj, NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))
  | times lhs rhs =>
      cases q
      · simpa [NumObjIso, NumSyntaxToObj, NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumObjIso, NumSyntaxToObj, NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))

def NumWellFoundedCode : WellFoundedCode NumPoly NumSyntax where
  step := NumObjIso
  rank := fun _ e => NumSyntax.rank e
  child_rank_lt := Num_child_rank_lt

/-- Numeric expressions as the generic initial algebra are bijective with the
readable recursive syntax family. -/
def NumSyntaxIso (k : Nat) : Mu NumPoly k ≃ᵢ NumSyntax k :=
  initialAlgebraCoding NumPoly NumSyntax NumWellFoundedCode k

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

/-- Readable syntax family for Peano formulas. -/
inductive PeanoSyntax : Nat → Type
  | eq {k : Nat} (lhs rhs : Mu NumPoly k) : PeanoSyntax k
  | not {k : Nat} : PeanoSyntax k → PeanoSyntax k
  | implies {k : Nat} : PeanoSyntax k → PeanoSyntax k → PeanoSyntax k
  | forallE {k : Nat} : PeanoSyntax (k + 1) → PeanoSyntax k

namespace PeanoSyntax

def rank : ∀ {k : Nat}, PeanoSyntax k → Nat
  | _, eq _ _ => 0
  | _, not e => rank e + 1
  | _, implies lhs rhs => Nat.max (rank lhs) (rank rhs) + 1
  | _, forallE e => rank e + 1

end PeanoSyntax

def PeanoObjToSyntax (k : Nat) : Obj PeanoPoly PeanoSyntax k → PeanoSyntax k
  | ⟨.eq, p, h, _child⟩ =>
      .eq (h ▸ p.2.1) (h ▸ p.2.2)
  | ⟨.not, _p, h, child⟩ =>
      .not (h ▸ child ())
  | ⟨.implies, _p, h, child⟩ =>
      .implies (h ▸ child false) (h ▸ child true)
  | ⟨.forallE, _p, h, child⟩ =>
      h ▸ (.forallE (child ()))

def PeanoSyntaxToObj (k : Nat) : PeanoSyntax k → Obj PeanoPoly PeanoSyntax k
  | .eq lhs rhs => ⟨.eq, ⟨k, (lhs, rhs)⟩, rfl, fun q => nomatch q⟩
  | .not e => ⟨.not, k, rfl, fun _ => e⟩
  | .implies lhs rhs => ⟨.implies, k, rfl, fun (b : Bool) => if b then rhs else lhs⟩
  | .forallE e => ⟨.forallE, k, rfl, fun _ => e⟩

theorem PeanoObj_left_inv (k : Nat) :
    Function.LeftInverse (PeanoSyntaxToObj k) (PeanoObjToSyntax k) := by
  intro layer
  cases layer with
  | mk ctor param out_eq child =>
    cases ctor with
    | eq =>
        cases param with
        | mk k' pair =>
          cases pair with
          | mk lhs rhs =>
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
    | not =>
        cases out_eq
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl
    | implies =>
        cases out_eq
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl
    | forallE =>
        cases out_eq
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl

theorem PeanoObj_right_inv (k : Nat) :
    Function.RightInverse (PeanoSyntaxToObj k) (PeanoObjToSyntax k) := by
  intro e
  cases e <;> simp [PeanoObjToSyntax, PeanoSyntaxToObj]

def PeanoObjIso (k : Nat) : Obj PeanoPoly PeanoSyntax k ≃ᵢ PeanoSyntax k where
  toFun := PeanoObjToSyntax k
  invFun := PeanoSyntaxToObj k
  left_inv := PeanoObj_left_inv k
  right_inv := PeanoObj_right_inv k

theorem Peano_child_rank_lt :
    ∀ {k : Nat} (z : PeanoSyntax k)
      (q : PeanoPoly.Pos ((PeanoObjIso k).invFun z).ctor ((PeanoObjIso k).invFun z).param),
      PeanoSyntax.rank (((PeanoObjIso k).invFun z).child q) < PeanoSyntax.rank z := by
  intro k z q
  cases z with
  | eq lhs rhs => cases q
  | not e =>
      cases q
      simp [PeanoObjIso, PeanoSyntaxToObj, PeanoSyntax.rank]
  | implies lhs rhs =>
      cases q
      · simpa [PeanoObjIso, PeanoSyntaxToObj, PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
      · simpa [PeanoObjIso, PeanoSyntaxToObj, PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
  | forallE e =>
      cases q
      simp [PeanoObjIso, PeanoSyntaxToObj, PeanoSyntax.rank]

def PeanoWellFoundedCode : WellFoundedCode PeanoPoly PeanoSyntax where
  step := PeanoObjIso
  rank := fun _ e => PeanoSyntax.rank e
  child_rank_lt := Peano_child_rank_lt

/-- Peano formulas as the generic initial algebra are bijective with readable
syntax, including the `forall` branch whose child is in context `k + 1`. -/
def PeanoSyntaxIso (k : Nat) : Mu PeanoPoly k ≃ᵢ PeanoSyntax k :=
  initialAlgebraCoding PeanoPoly PeanoSyntax PeanoWellFoundedCode k

end Examples
end BijForm
