import BijForm.DependentPolynomial
import BijForm.NatCoding

namespace BijForm
namespace Examples

open DepPoly

/-- Reference syntax family for height-bounded trees: leaves may appear at any
height, while branches increase the height bound by one. -/
inductive HBTSyntax : Nat → Type
  | leaf {i : Nat} (label : Nat) : HBTSyntax i
  | branch {m : Nat} : HBTSyntax m → HBTSyntax m → HBTSyntax (m + 1)

namespace HBTSyntax

def rank : ∀ {i : Nat}, HBTSyntax i → Nat
  | _, leaf _ => 0
  | _, branch lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end HBTSyntax

/-- Polynomial constructors for height-bounded trees: leaves carry a natural
label, branches have two children. -/
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

/-- Index-local constructor codes for height-bounded trees. At target height
`i`, a branch code must include an explicit predecessor `m` with `m + 1 = i`. -/
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

def HBTLayerToSyntax (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i → HBTSyntax i
  | ⟨.leaf label, _child⟩ =>
      .leaf label
  | ⟨.branch _m h, child⟩ =>
      h ▸ (.branch (child false) (child true))

def HBTSyntaxToLayer (i : Nat) :
    HBTSyntax i → CodeLayer HBTPoly HBTInversion HBTSyntax i
  | .leaf label =>
      ⟨.leaf label, fun q => nomatch q⟩
  | @HBTSyntax.branch m lhs rhs =>
      ⟨.branch m rfl, fun (b : Bool) => if b then rhs else lhs⟩

theorem HBTLayer_left_inv (i : Nat) :
    Function.LeftInverse (HBTSyntaxToLayer i) (HBTLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | leaf label =>
        have hchild : (fun q => nomatch q) = child := by
          funext q
          cases q
        cases hchild
        rfl
    | branch m h =>
        cases h
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl

theorem HBTLayer_right_inv (i : Nat) :
    Function.RightInverse (HBTSyntaxToLayer i) (HBTLayerToSyntax i) := by
  intro t
  cases t <;> simp [HBTLayerToSyntax, HBTSyntaxToLayer]

def HBTLayerIso (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i ≃ᵢ HBTSyntax i where
  toFun := HBTLayerToSyntax i
  invFun := HBTSyntaxToLayer i
  left_inv := HBTLayer_left_inv i
  right_inv := HBTLayer_right_inv i

theorem HBT_layer_child_rank_lt :
    ∀ {i : Nat} (z : HBTSyntax i)
      (q : HBTPoly.Pos
          (HBTInversion.decode i ((HBTLayerIso i).invFun z).1).ctor
          (HBTInversion.decode i ((HBTLayerIso i).invFun z).1).param),
      HBTSyntax.rank (((HBTLayerIso i).invFun z).2 q) < HBTSyntax.rank z := by
  intro i z q
  cases z with
  | leaf label => cases q
  | branch lhs rhs =>
      cases q
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion, HBTDecode,
          HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion, HBTDecode,
          HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))

/--
Generated-layer coding data for height-bounded trees. The example supplies only
the local layer coding over `HBTInversion`; the full object-layer step is
produced by `GeneratedLayerCode.toWellFoundedCode`.
-/
def HBTGeneratedLayerCode : GeneratedLayerCode HBTPoly HBTSyntax where
  inversion := HBTInversion
  layer := HBTLayerIso
  rank := fun _ t => HBTSyntax.rank t
  child_rank_lt := HBT_layer_child_rank_lt

def HBTWellFoundedCode : WellFoundedCode HBTPoly HBTSyntax :=
  HBTGeneratedLayerCode.toWellFoundedCode

/-- Height-bounded trees as the generic initial algebra are bijective with
readable syntax through generated layer coding. -/
def HBTSyntaxIso (i : Nat) : Mu HBTPoly i ≃ᵢ HBTSyntax i :=
  HBTGeneratedLayerCode.iso i

def HBTNatZeroLayerIso :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) 0 ≃ᵢ Nat where
  toFun
    | ⟨.leaf label, _child⟩ => label
    | ⟨.branch _ h, _child⟩ => by cases h
  invFun n := ⟨.leaf n, fun q => nomatch q⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | leaf label =>
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
        | branch m h => cases h
  right_inv := by
    intro n
    rfl

def HBTNatSuccLayerSumIso (m : Nat) :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) (m + 1) ≃ᵢ
      (Nat ⊕ (Nat × Nat)) where
  toFun
    | ⟨.leaf label, _child⟩ => Sum.inl label
    | ⟨.branch _ _h, child⟩ => Sum.inr (child false, child true)
  invFun
    | Sum.inl label => ⟨.leaf label, fun q => nomatch q⟩
    | Sum.inr p => ⟨.branch m rfl, fun
        | false => p.1
        | true => p.2⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | leaf label =>
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
        | branch k h =>
            cases h
            have hchild : child = (fun
                | false => child false
                | true => child true) := by
              funext q
              cases q <;> rfl
            rw [hchild]
            rfl
  right_inv := by
    intro x
    cases x with
    | inl label => rfl
    | inr p =>
        cases p
        rfl

def HBTNatSuccLayerIso (m : Nat) :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) (m + 1) ≃ᵢ Nat :=
  Iso.trans (HBTNatSuccLayerSumIso m)
    (Iso.trans (Iso.sum (Iso.refl Nat) NatCoding.prodNat) NatCoding.sumNat)

def HBTNatLayerIso :
    ∀ i, CodeLayer HBTPoly HBTInversion (fun _ => Nat) i ≃ᵢ Nat
  | 0 => HBTNatZeroLayerIso
  | m + 1 => HBTNatSuccLayerIso m

theorem HBTNat_child_lt :
    ∀ {i : Nat} (n : Nat)
      (q : HBTPoly.Pos
          (HBTInversion.decode i ((HBTNatLayerIso i).invFun n).1).ctor
          (HBTInversion.decode i ((HBTNatLayerIso i).invFun n).1).param),
      (((HBTNatLayerIso i).invFun n).2 q) < n := by
  intro i n
  cases i with
  | zero =>
      intro q
      cases q
  | succ m =>
      dsimp [HBTNatLayerIso, HBTNatSuccLayerIso, Iso.trans, Iso.sum]
      generalize hsum : NatCoding.sumNat.invFun n = s
      cases s with
      | inl label =>
          intro q
          cases q
      | inr pairCode =>
          intro q
          have hright := NatCoding.sumNat.right_inv n
          rw [hsum] at hright
          simp [NatCoding.sumNat] at hright
          cases q
          · change (NatCoding.prodNat.invFun pairCode).1 < n
            have hle := NatCoding.prodNat_fst_le pairCode
            omega
          · change (NatCoding.prodNat.invFun pairCode).2 < n
            have hle := NatCoding.prodNat_snd_le pairCode
            omega

/-- Generated Nat coding data for height-bounded trees. The recursive encoder
and decoder are produced by `GeneratedNatCode`, not by an example-specific
recursive function. -/
def HBTNatGeneratedCode : GeneratedNatCode HBTPoly where
  inversion := HBTInversion
  layer := HBTNatLayerIso
  child_lt := HBTNat_child_lt

def HBTNatIso (i : Nat) : Mu HBTPoly i ≃ᵢ Nat :=
  HBTNatGeneratedCode.iso i

def HBTSyntaxNatIso (i : Nat) : HBTSyntax i ≃ᵢ Nat :=
  Iso.trans (Iso.symm (HBTSyntaxIso i)) (HBTNatIso i)

/-- Upper bounds for sorted trees.  `none` represents infinity. -/
abbrev Bound :=
  Option Nat

def Bound.le (x : Nat) : Bound → Prop
  | none => True
  | some m => x ≤ m

instance (x : Nat) (b : Bound) : Decidable (Bound.le x b) := by
  cases b with
  | none => exact isTrue trivial
  | some m => exact inferInstanceAs (Decidable (x ≤ m))

abbrev SortedIx :=
  Nat × Bound

def BoundedPivot (i : SortedIx) : Type :=
  { x : Nat // i.1 ≤ x ∧ Bound.le x i.2 }

theorem BoundedPivot.bound_le {i : SortedIx} (pivot : BoundedPivot i) :
    Bound.le i.1 i.2 := by
  cases i with
  | mk lower upper =>
    cases upper with
    | none => trivial
    | some upper =>
        rcases pivot with ⟨x, hx⟩
        dsimp [Bound.le] at hx ⊢
        omega

def BoundedPivotFiniteIso (lower upper : Nat) (h : lower ≤ upper) :
    BoundedPivot (lower, some upper) ≃ᵢ Fin (upper - lower + 1) where
  toFun pivot := ⟨pivot.1 - lower, by
    rcases pivot with ⟨x, hx⟩
    dsimp [BoundedPivot, Bound.le] at hx
    have hsub : x - lower ≤ upper - lower := Nat.sub_le_sub_right hx.2 lower
    exact Nat.lt_succ_of_le hsub⟩
  invFun code := ⟨lower + code.val, by
    constructor
    · omega
    · dsimp [Bound.le]
      have hcode := code.isLt
      omega⟩
  left_inv := by
    intro pivot
    apply Subtype.ext
    rcases pivot with ⟨x, hx⟩
    dsimp [BoundedPivot, Bound.le] at hx
    exact Nat.add_sub_of_le hx.1
  right_inv := by
    intro code
    apply Fin.ext
    exact Nat.add_sub_cancel_left lower code.val

def BoundedPivotInfiniteIso (lower : Nat) :
    BoundedPivot (lower, none) ≃ᵢ Nat where
  toFun pivot := pivot.1 - lower
  invFun offset := ⟨lower + offset, by
    constructor
    · omega
    · trivial⟩
  left_inv := by
    intro pivot
    apply Subtype.ext
    rcases pivot with ⟨x, hx⟩
    dsimp [BoundedPivot, Bound.le] at hx
    exact Nat.add_sub_of_le hx.1
  right_inv := by
    intro offset
    exact Nat.add_sub_cancel_left lower offset

/-- Reference syntax family for sorted trees indexed by lower and upper bounds.
A branch chooses a pivot in bounds, then recursively narrows the child bounds. -/
inductive SortedSyntax : SortedIx → Type
  | leaf {i : SortedIx} : SortedSyntax i
  | branch {i : SortedIx} (pivot : BoundedPivot i) :
      SortedSyntax (i.1, some pivot.1) → SortedSyntax (pivot.1, i.2) →
        SortedSyntax i

namespace SortedSyntax

def rank : ∀ {i : SortedIx}, SortedSyntax i → Nat
  | _, leaf => 0
  | _, branch _ lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end SortedSyntax

/-- Polynomial constructors for the sorted-tree example. -/
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

def SortedLayerToSyntax (i : SortedIx) :
    CodeLayer SortedPoly SortedInversion SortedSyntax i → SortedSyntax i
  | ⟨.leaf, _child⟩ =>
      .leaf
  | ⟨.branch pivot, child⟩ =>
      .branch pivot (child false) (child true)

def SortedSyntaxToLayer (i : SortedIx) :
    SortedSyntax i → CodeLayer SortedPoly SortedInversion SortedSyntax i
  | .leaf =>
      ⟨.leaf, fun q => nomatch q⟩
  | .branch pivot lhs rhs =>
      ⟨.branch pivot, fun
        | false => lhs
        | true => rhs⟩

theorem SortedLayer_left_inv (i : SortedIx) :
    Function.LeftInverse (SortedSyntaxToLayer i) (SortedLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | leaf =>
        have hchild : (fun q => nomatch q) = child := by
          funext q
          cases q
        cases hchild
        rfl
    | branch pivot =>
        have hchild : child = (fun
            | false => child false
            | true => child true) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl

theorem SortedLayer_right_inv (i : SortedIx) :
    Function.RightInverse (SortedSyntaxToLayer i) (SortedLayerToSyntax i) := by
  intro t
  cases t with
  | leaf => rfl
  | branch pivot lhs rhs => rfl

def SortedLayerIso (i : SortedIx) :
    CodeLayer SortedPoly SortedInversion SortedSyntax i ≃ᵢ SortedSyntax i where
  toFun := SortedLayerToSyntax i
  invFun := SortedSyntaxToLayer i
  left_inv := SortedLayer_left_inv i
  right_inv := SortedLayer_right_inv i

theorem Sorted_layer_child_rank_lt :
    ∀ {i : SortedIx} (z : SortedSyntax i)
      (q : SortedPoly.Pos
          (SortedInversion.decode i ((SortedLayerIso i).invFun z).1).ctor
          (SortedInversion.decode i ((SortedLayerIso i).invFun z).1).param),
      SortedSyntax.rank (((SortedLayerIso i).invFun z).2 q) < SortedSyntax.rank z := by
  intro i z q
  cases z with
  | leaf => cases q
  | branch pivot lhs rhs =>
      cases q
      · simpa [SortedLayerIso, SortedSyntaxToLayer, SortedInversion, SortedDecode,
          SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))
      · simpa [SortedLayerIso, SortedSyntaxToLayer, SortedInversion, SortedDecode,
          SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))

def SortedGeneratedLayerCode : GeneratedLayerCode SortedPoly SortedSyntax where
  inversion := SortedInversion
  layer := SortedLayerIso
  rank := fun _ t => SortedSyntax.rank t
  child_rank_lt := Sorted_layer_child_rank_lt

def SortedWellFoundedCode : WellFoundedCode SortedPoly SortedSyntax :=
  SortedGeneratedLayerCode.toWellFoundedCode

/-- Sorted trees as the generic initial algebra are bijective with readable
syntax through generated layer coding. -/
def SortedSyntaxIso (i : SortedIx) : Mu SortedPoly i ≃ᵢ SortedSyntax i :=
  SortedGeneratedLayerCode.iso i

def SortedShape (i : SortedIx) : CodeShape :=
  if Bound.le i.1 i.2 then .infinite else .finite 1

abbrev SortedCarrier (i : SortedIx) : Type :=
  (SortedShape i).Carrier

namespace SortedCarrier

def toNat {i : SortedIx} (h : Bound.le i.1 i.2) (z : SortedCarrier i) : Nat := by
  dsimp [SortedCarrier, SortedShape] at z
  rw [if_pos h] at z
  exact z

def ofNat {i : SortedIx} (h : Bound.le i.1 i.2) (n : Nat) : SortedCarrier i := by
  dsimp [SortedCarrier, SortedShape]
  rw [if_pos h]
  exact n

theorem toNat_ofNat {i : SortedIx} (h : Bound.le i.1 i.2) (n : Nat) :
    toNat h (ofNat h n) = n := by
  simp [toNat, ofNat, SortedCarrier, SortedShape, h]

theorem ofNat_toNat {i : SortedIx} (h : Bound.le i.1 i.2) (z : SortedCarrier i) :
    ofNat h (toNat h z) = z := by
  simp [toNat, ofNat, SortedCarrier, SortedShape, h]

def toFinOne {i : SortedIx} (h : ¬Bound.le i.1 i.2) (z : SortedCarrier i) : Fin 1 := by
  dsimp [SortedCarrier, SortedShape] at z
  rw [if_neg h] at z
  exact z

def ofFinOne {i : SortedIx} (h : ¬Bound.le i.1 i.2) (n : Fin 1) : SortedCarrier i := by
  dsimp [SortedCarrier, SortedShape]
  rw [if_neg h]
  exact n

theorem toFinOne_ofFinOne {i : SortedIx} (h : ¬Bound.le i.1 i.2) (n : Fin 1) :
    toFinOne h (ofFinOne h n) = n := by
  simp [toFinOne, ofFinOne, SortedCarrier, SortedShape, h]

theorem ofFinOne_toFinOne {i : SortedIx} (h : ¬Bound.le i.1 i.2) (z : SortedCarrier i) :
    ofFinOne h (toFinOne h z) = z := by
  simp [toFinOne, ofFinOne, SortedCarrier, SortedShape, h]

def natIso {i : SortedIx} (h : Bound.le i.1 i.2) : SortedCarrier i ≃ᵢ Nat where
  toFun := toNat h
  invFun := ofNat h
  left_inv := ofNat_toNat h
  right_inv := toNat_ofNat h

def finOneIso {i : SortedIx} (h : ¬Bound.le i.1 i.2) : SortedCarrier i ≃ᵢ Fin 1 where
  toFun := toFinOne h
  invFun := ofFinOne h
  left_inv := ofFinOne_toFinOne h
  right_inv := toFinOne_ofFinOne h

end SortedCarrier

def SortedInvalidLayerIso (i : SortedIx) (h : ¬Bound.le i.1 i.2) :
    CodeLayer SortedPoly SortedInversion SortedCarrier i ≃ᵢ SortedCarrier i :=
  Iso.trans
    { toFun := fun layer =>
        match layer with
        | ⟨.leaf, _child⟩ => ⟨0, by decide⟩
        | ⟨.branch pivot, _child⟩ => False.elim (h pivot.bound_le)
      invFun := fun _ => ⟨.leaf, fun q => nomatch q⟩
      left_inv := by
        intro layer
        cases layer with
        | mk code child =>
          cases code with
          | leaf =>
              have hchild : (fun q => nomatch q) = child := by
                funext q
                cases q
              cases hchild
              rfl
          | branch pivot =>
              exact False.elim (h pivot.bound_le)
      right_inv := by
        intro code
        apply Fin.ext
        omega }
    (Iso.symm (SortedCarrier.finOneIso h))

abbrev SortedFiniteLayerShape (lower upper : Nat) :=
  Fin 1 ⊕ (Fin (upper - lower + 1) × (Nat × Nat))

def SortedFiniteLayerShapeIso (lower upper : Nat) (h : lower ≤ upper) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper) ≃ᵢ
      SortedFiniteLayerShape lower upper where
  toFun
    | ⟨.leaf, _child⟩ => Sum.inl ⟨0, by decide⟩
    | ⟨.branch pivot, child⟩ =>
        Sum.inr
          ((BoundedPivotFiniteIso lower upper h).toFun pivot,
            (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false),
             SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)))
  invFun
    | Sum.inl _ => ⟨.leaf, fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotFiniteIso lower upper h).invFun payload.1
        ⟨.branch pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1 payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, some upper)) pivot.property.2 payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | leaf =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | branch pivot =>
          dsimp
          rw [(BoundedPivotFiniteIso lower upper h).left_inv pivot]
          have hchild :
              (fun
                | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
                    (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false))
                | true => SortedCarrier.ofNat (i := (pivot.1, some upper)) pivot.property.2
                    (SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true))) = child := by
            funext q
            cases q
            · exact SortedCarrier.ofNat_toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
            · exact SortedCarrier.ofNat_toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)
          rw [hchild]
  right_inv := by
    intro shape
    cases shape with
    | inl tag =>
        apply congrArg Sum.inl
        apply Fin.ext
        omega
    | inr payload =>
        cases payload with
        | mk pivotCode pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp
            rw [(BoundedPivotFiniteIso lower upper h).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

def SortedFiniteBranchPayloadIso (lower upper : Nat) :
    (Fin (upper - lower + 1) × (Nat × Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.prod (Iso.refl (Fin (upper - lower + 1))) NatCoding.prodNat)
    (NatCoding.finProdNat (upper - lower + 1) (by omega))

def SortedFiniteLayerNatIso (lower upper : Nat) (h : lower ≤ upper) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper) ≃ᵢ Nat :=
  Iso.trans (SortedFiniteLayerShapeIso lower upper h)
    (Iso.trans (Iso.sum (Iso.refl (Fin 1)) (SortedFiniteBranchPayloadIso lower upper))
      (NatCoding.finPlusNat 1))

def SortedFiniteLayerIso (lower upper : Nat) (h : lower ≤ upper) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper) ≃ᵢ
      SortedCarrier (lower, some upper) :=
  Iso.trans (SortedFiniteLayerNatIso lower upper h)
    (Iso.symm (SortedCarrier.natIso h))

abbrev SortedInfiniteLayerShape :=
  Fin 1 ⊕ (Nat × (Nat × Nat))

def SortedInfiniteLayerShapeIso (lower : Nat) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none) ≃ᵢ
      SortedInfiniteLayerShape where
  toFun
    | ⟨.leaf, _child⟩ => Sum.inl ⟨0, by decide⟩
    | ⟨.branch pivot, child⟩ =>
        Sum.inr
          ((BoundedPivotInfiniteIso lower).toFun pivot,
            (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false),
             SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true)))
  invFun
    | Sum.inl _ => ⟨.leaf, fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotInfiniteIso lower).invFun payload.1
        ⟨.branch pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1 payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, none)) pivot.property.2 payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | leaf =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | branch pivot =>
          dsimp
          rw [(BoundedPivotInfiniteIso lower).left_inv pivot]
          have hchild :
              (fun
                | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
                    (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false))
                | true => SortedCarrier.ofNat (i := (pivot.1, none)) pivot.property.2
                    (SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true))) = child := by
            funext q
            cases q
            · exact SortedCarrier.ofNat_toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
            · exact SortedCarrier.ofNat_toNat (i := (pivot.1, none)) pivot.property.2 (child true)
          rw [hchild]
  right_inv := by
    intro shape
    cases shape with
    | inl tag =>
        apply congrArg Sum.inl
        apply Fin.ext
        omega
    | inr payload =>
        cases payload with
        | mk pivotCode pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp
            rw [(BoundedPivotInfiniteIso lower).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

def SortedInfiniteBranchPayloadIso :
    (Nat × (Nat × Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.prod (Iso.refl Nat) NatCoding.prodNat) NatCoding.prodNat

def SortedInfiniteLayerNatIso (lower : Nat) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none) ≃ᵢ Nat :=
  Iso.trans (SortedInfiniteLayerShapeIso lower)
    (Iso.trans (Iso.sum (Iso.refl (Fin 1)) SortedInfiniteBranchPayloadIso)
      (NatCoding.finPlusNat 1))

def SortedInfiniteLayerIso (lower : Nat) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none) ≃ᵢ
      SortedCarrier (lower, none) :=
  Iso.trans (SortedInfiniteLayerNatIso lower)
    (Iso.symm (SortedCarrier.natIso trivial))

def SortedShapeLayerIso :
    ∀ i, CodeLayer SortedPoly SortedInversion SortedCarrier i ≃ᵢ SortedCarrier i
  | (lower, none) => SortedInfiniteLayerIso lower
  | (lower, some upper) =>
      if h : lower ≤ upper then
        SortedFiniteLayerIso lower upper h
      else
        SortedInvalidLayerIso (lower, some upper) h

def SortedCarrierRank (i : SortedIx) (z : SortedCarrier i) : Nat :=
  if h : Bound.le i.1 i.2 then
    SortedCarrier.toNat h z
  else
    0

theorem SortedFiniteLayerNat_child_rank_lt (lower upper : Nat) (h : lower ≤ upper) :
    ∀ (n : Nat)
      (q : SortedPoly.Pos
          (SortedInversion.decode (lower, some upper)
            ((SortedFiniteLayerNatIso lower upper h).invFun n).1).ctor
          (SortedInversion.decode (lower, some upper)
            ((SortedFiniteLayerNatIso lower upper h).invFun n).1).param),
      SortedCarrierRank
          (SortedPoly.input
            (SortedInversion.decode (lower, some upper)
              ((SortedFiniteLayerNatIso lower upper h).invFun n).1).param q)
          (((SortedFiniteLayerNatIso lower upper h).invFun n).2 q) < n := by
  intro n
  generalize hz : (SortedFiniteLayerNatIso lower upper h).invFun n = layer
  have hn : (SortedFiniteLayerNatIso lower upper h).toFun layer = n := by
    rw [← hz]
    exact (SortedFiniteLayerNatIso lower upper h).right_inv n
  intro q
  change SortedCarrierRank
      (SortedPoly.input (SortedInversion.decode (lower, some upper) layer.1).param q)
      (layer.2 q) < n
  cases layer with
  | mk code child =>
    cases code with
    | leaf => cases q
    | branch pivot =>
      let lhsCode :=
        SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
      let rhsCode :=
        SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)
      let pairCode := NatCoding.prodNat.toFun (lhsCode, rhsCode)
      let payloadCode := (SortedFiniteBranchPayloadIso lower upper).toFun
        ((BoundedPivotFiniteIso lower upper h).toFun pivot, (lhsCode, rhsCode))
      have hn_payload : 1 + payloadCode = n := by
        simpa [payloadCode, pairCode, lhsCode, rhsCode, SortedFiniteLayerNatIso,
          SortedFiniteLayerShapeIso, SortedFiniteBranchPayloadIso, Iso.trans,
          Iso.sum, Iso.prod, NatCoding.finPlusNat] using hn
      have hpayload_lt : payloadCode < n := by omega
      have hpair_le_payload : pairCode ≤ payloadCode := by
        simpa [payloadCode, pairCode, lhsCode, rhsCode, SortedFiniteBranchPayloadIso,
          Iso.trans, Iso.prod] using
          NatCoding.finProdNat_toFun_snd_le (upper - lower + 1) (by omega)
            (((BoundedPivotFiniteIso lower upper h).toFun pivot), pairCode)
      have hpivotUpper : pivot.1 ≤ upper := pivot.property.2
      cases q
      · have hchild_le_pair : lhsCode ≤ pairCode := by
          simpa [pairCode, lhsCode, rhsCode, NatCoding.prodNat] using
            NatCoding.prodNat_fst_le (NatCoding.prodNat.toFun (lhsCode, rhsCode))
        have hlt : lhsCode < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hchild_le_pair hpair_le_payload) hpayload_lt
        simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion, SortedDecode,
          Bound.le, lhsCode, pivot.property.1] using hlt
      · have hchild_le_pair : rhsCode ≤ pairCode := by
          simpa [pairCode, lhsCode, rhsCode, NatCoding.prodNat] using
            NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (lhsCode, rhsCode))
        have hlt : rhsCode < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hchild_le_pair hpair_le_payload) hpayload_lt
        simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion, SortedDecode,
          Bound.le, rhsCode, hpivotUpper] using hlt

theorem SortedInfiniteLayerNat_child_rank_lt (lower : Nat) :
    ∀ (n : Nat)
      (q : SortedPoly.Pos
          (SortedInversion.decode (lower, none)
            ((SortedInfiniteLayerNatIso lower).invFun n).1).ctor
          (SortedInversion.decode (lower, none)
            ((SortedInfiniteLayerNatIso lower).invFun n).1).param),
      SortedCarrierRank
          (SortedPoly.input
            (SortedInversion.decode (lower, none)
              ((SortedInfiniteLayerNatIso lower).invFun n).1).param q)
          (((SortedInfiniteLayerNatIso lower).invFun n).2 q) < n := by
  intro n
  generalize hz : (SortedInfiniteLayerNatIso lower).invFun n = layer
  have hn : (SortedInfiniteLayerNatIso lower).toFun layer = n := by
    rw [← hz]
    exact (SortedInfiniteLayerNatIso lower).right_inv n
  intro q
  change SortedCarrierRank
      (SortedPoly.input (SortedInversion.decode (lower, none) layer.1).param q)
      (layer.2 q) < n
  cases layer with
  | mk code child =>
    cases code with
    | leaf => cases q
    | branch pivot =>
      let lhsCode :=
        SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
      let rhsCode :=
        SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true)
      let pairCode := NatCoding.prodNat.toFun (lhsCode, rhsCode)
      let pivotCode := (BoundedPivotInfiniteIso lower).toFun pivot
      let payloadCode := SortedInfiniteBranchPayloadIso.toFun (pivotCode, (lhsCode, rhsCode))
      have hn_payload : 1 + payloadCode = n := by
        simpa [payloadCode, pivotCode, pairCode, lhsCode, rhsCode,
          SortedInfiniteLayerNatIso, SortedInfiniteLayerShapeIso,
          SortedInfiniteBranchPayloadIso, Iso.trans, Iso.sum, Iso.prod,
          NatCoding.finPlusNat] using hn
      have hpayload_lt : payloadCode < n := by omega
      have hpair_le_payload : pairCode ≤ payloadCode := by
        simpa [payloadCode, pivotCode, pairCode, lhsCode, rhsCode,
          SortedInfiniteBranchPayloadIso, Iso.trans, Iso.prod] using
          NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (pivotCode, pairCode))
      cases q
      · have hchild_le_pair : lhsCode ≤ pairCode := by
          simpa [pairCode, lhsCode, rhsCode, NatCoding.prodNat] using
            NatCoding.prodNat_fst_le (NatCoding.prodNat.toFun (lhsCode, rhsCode))
        have hlt : lhsCode < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hchild_le_pair hpair_le_payload) hpayload_lt
        simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion, SortedDecode,
          Bound.le, lhsCode, pivot.property.1] using hlt
      · have hchild_le_pair : rhsCode ≤ pairCode := by
          simpa [pairCode, lhsCode, rhsCode, NatCoding.prodNat] using
            NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (lhsCode, rhsCode))
        have hlt : rhsCode < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans hchild_le_pair hpair_le_payload) hpayload_lt
        simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion, SortedDecode,
          Bound.le, rhsCode] using hlt

theorem SortedShape_child_rank_lt :
    ∀ {i : SortedIx} (z : SortedCarrier i)
      (q : SortedPoly.Pos
          (SortedInversion.decode i ((SortedShapeLayerIso i).invFun z).1).ctor
          (SortedInversion.decode i ((SortedShapeLayerIso i).invFun z).1).param),
      SortedCarrierRank
          (SortedPoly.input (SortedInversion.decode i ((SortedShapeLayerIso i).invFun z).1).param q)
          (((SortedShapeLayerIso i).invFun z).2 q) < SortedCarrierRank i z := by
  intro i z
  cases i with
  | mk lower upper =>
    cases upper with
    | none =>
      simpa [SortedShapeLayerIso, SortedInfiniteLayerIso, Iso.trans, Iso.symm,
        SortedCarrier.natIso, SortedCarrierRank, Bound.le] using
        SortedInfiniteLayerNat_child_rank_lt lower
          (SortedCarrier.toNat (i := (lower, none)) trivial z)
    | some upper =>
      by_cases h : lower ≤ upper
      · dsimp [SortedShapeLayerIso]
        rw [dif_pos h]
        dsimp [SortedFiniteLayerIso, Iso.trans, Iso.symm, SortedCarrier.natIso]
        change ∀ q, SortedCarrierRank
          (SortedPoly.input (SortedInversion.decode (lower, some upper)
            ((SortedFiniteLayerNatIso lower upper h).invFun
              (SortedCarrier.toNat (i := (lower, some upper)) h z)).1).param q)
          (((SortedFiniteLayerNatIso lower upper h).invFun
              (SortedCarrier.toNat (i := (lower, some upper)) h z)).2 q) <
            SortedCarrierRank (lower, some upper) z
        simpa [SortedCarrierRank, Bound.le, h] using
          SortedFiniteLayerNat_child_rank_lt lower upper h
            (SortedCarrier.toNat (i := (lower, some upper)) h z)
      · dsimp [SortedShapeLayerIso]
        rw [dif_neg h]
        dsimp [SortedInvalidLayerIso, Iso.trans, Iso.symm, SortedCarrier.finOneIso]
        intro q
        cases q

def SortedGeneratedShapeCode : GeneratedShapeCode SortedPoly where
  shape := SortedShape
  inversion := SortedInversion
  layer := SortedShapeLayerIso
  rank := SortedCarrierRank
  child_rank_lt := SortedShape_child_rank_lt

def SortedShapeIso (i : SortedIx) : Mu SortedPoly i ≃ᵢ SortedCarrier i :=
  SortedGeneratedShapeCode.iso i

def SortedSyntaxShapeIso (i : SortedIx) : SortedSyntax i ≃ᵢ SortedCarrier i :=
  Iso.trans (Iso.symm (SortedSyntaxIso i)) (SortedShapeIso i)

/-- At the empty finite interval `(1, some 0)`, sorted trees have no branch
constructor because no pivot can satisfy both bounds. -/
theorem Sorted_empty_interval_subsingleton :
    Subsingleton (SortedSyntax (1, some 0)) := by
  constructor
  intro a b
  cases a with
  | leaf =>
      cases b with
      | leaf => rfl
      | branch pivot lhs rhs =>
          rcases pivot with ⟨x, hx⟩
          dsimp [BoundedPivot, Bound.le] at hx
          omega
  | branch pivot lhs rhs =>
      rcases pivot with ⟨x, hx⟩
      dsimp [BoundedPivot, Bound.le] at hx
      omega

def SortedEmptyCarrierFinOneIso : SortedCarrier (1, some 0) ≃ᵢ Fin 1 :=
  SortedCarrier.finOneIso (by
    dsimp [Bound.le]
    omega)

def SortedEmptySyntaxFinOneIso : SortedSyntax (1, some 0) ≃ᵢ Fin 1 :=
  Iso.trans (SortedSyntaxShapeIso (1, some 0)) SortedEmptyCarrierFinOneIso

/-- Reference syntax family for numeric expressions indexed by the number of
available variables. -/
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

/-- Polynomial constructors for numeric expressions: variables, zero,
successor, addition, and multiplication. -/
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

def NumLayerToSyntax (k : Nat) :
    CodeLayer NumPoly NumInversion NumSyntax k → NumSyntax k
  | ⟨.var v, _child⟩ =>
      .var v
  | ⟨.zero, _child⟩ =>
      .zero
  | ⟨.succ, child⟩ =>
      .succ (child ())
  | ⟨.plus, child⟩ =>
      .plus (child false) (child true)
  | ⟨.times, child⟩ =>
      .times (child false) (child true)

def NumSyntaxToLayer (k : Nat) :
    NumSyntax k → CodeLayer NumPoly NumInversion NumSyntax k
  | .var v => ⟨.var v, fun q => nomatch q⟩
  | .zero => ⟨.zero, fun q => nomatch q⟩
  | .succ e => ⟨.succ, fun _ => e⟩
  | .plus lhs rhs => ⟨.plus, fun (b : Bool) => if b then rhs else lhs⟩
  | .times lhs rhs => ⟨.times, fun (b : Bool) => if b then rhs else lhs⟩

theorem NumLayer_left_inv (k : Nat) :
    Function.LeftInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
      | var v =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | zero =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | succ =>
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          rfl
      | plus =>
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl
      | times =>
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl

theorem NumLayer_right_inv (k : Nat) :
    Function.RightInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro e
  cases e <;> simp [NumLayerToSyntax, NumSyntaxToLayer]

def NumLayerIso (k : Nat) :
    CodeLayer NumPoly NumInversion NumSyntax k ≃ᵢ NumSyntax k where
  toFun := NumLayerToSyntax k
  invFun := NumSyntaxToLayer k
  left_inv := NumLayer_left_inv k
  right_inv := NumLayer_right_inv k

theorem Num_layer_child_rank_lt :
    ∀ {k : Nat} (z : NumSyntax k)
      (q : NumPoly.Pos
          (NumInversion.decode k ((NumLayerIso k).invFun z).1).ctor
          (NumInversion.decode k ((NumLayerIso k).invFun z).1).param),
      NumSyntax.rank (((NumLayerIso k).invFun z).2 q) < NumSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | zero => cases q
  | succ e =>
      cases q
      simp [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode, NumSyntax.rank]
  | plus lhs rhs =>
      cases q
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))
  | times lhs rhs =>
      cases q
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))

def NumGeneratedLayerCode : GeneratedLayerCode NumPoly NumSyntax where
  inversion := NumInversion
  layer := NumLayerIso
  rank := fun _ e => NumSyntax.rank e
  child_rank_lt := Num_layer_child_rank_lt

def NumWellFoundedCode : WellFoundedCode NumPoly NumSyntax :=
  NumGeneratedLayerCode.toWellFoundedCode

/-- Numeric expressions as the generic initial algebra are bijective with the
readable recursive syntax family through generated layer coding. -/
def NumSyntaxIso (k : Nat) : Mu NumPoly k ≃ᵢ NumSyntax k :=
  NumGeneratedLayerCode.iso k

abbrev NumNatLayerShape (k : Nat) :=
  Fin (k + 2) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)))

def NumNatLayerShapeTo (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k → NumNatLayerShape k
  | ⟨.var v, _child⟩ => Sum.inl ⟨v.val, by omega⟩
  | ⟨.zero, _child⟩ => Sum.inl ⟨k + 1, by omega⟩
  | ⟨.succ, child⟩ => Sum.inr (Sum.inl (child ()))
  | ⟨.plus, child⟩ => Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨.times, child⟩ => Sum.inr (Sum.inr (Sum.inr (child false, child true)))

def NumNatLayerShapeInv (k : Nat) :
    NumNatLayerShape k → CodeLayer NumPoly NumInversion (fun _ => Nat) k
  | Sum.inl tag =>
      if h : tag.val < k + 1 then
        ⟨.var ⟨tag.val, h⟩, fun q => nomatch q⟩
      else
        ⟨.zero, fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨.succ, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨.plus, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr p)) => ⟨.times, fun
      | false => p.1
      | true => p.2⟩

theorem NumNatLayerShape_left_inv (k : Nat) :
    Function.LeftInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
  intro x
  cases x with
  | mk code child =>
      cases code with
      | var v =>
          cases v with
          | mk val isLt =>
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              rw [dif_pos isLt]
              have hchild : (fun q => nomatch q) = child := by
                funext q
                cases q
              cases hchild
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              funext q
              cases q
      | zero =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hnot : ¬k + 1 < k + 1 := by omega
          rw [dif_neg hnot]
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | succ =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
          rfl
      | plus =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]
      | times =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]

theorem NumNatLayerShape_right_inv (k : Nat) :
    Function.RightInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
  intro x
  cases x with
  | inl tag =>
      dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
      by_cases h : tag.val < k + 1
      · rw [dif_pos h]
      · rw [dif_neg h]
        exact congrArg Sum.inl (Fin.ext (by
          have hlt := tag.isLt
          change k + 1 = tag.val
          omega))
  | inr tail =>
      cases tail with
      | inl child => rfl
      | inr rest =>
          cases rest with
          | inl p =>
              cases p
              rfl
          | inr p =>
              cases p
              rfl

def NumNatLayerShapeIso (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k ≃ᵢ NumNatLayerShape k where
  toFun := NumNatLayerShapeTo k
  invFun := NumNatLayerShapeInv k
  left_inv := NumNatLayerShape_left_inv k
  right_inv := NumNatLayerShape_right_inv k

def NumNatTailIso : (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat))) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) (Iso.sum NatCoding.prodNat NatCoding.prodNat))
    NatCoding.sum3Nat

def NumNatLayerIso (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k ≃ᵢ Nat :=
  Iso.trans (NumNatLayerShapeIso k)
    (Iso.trans (Iso.sum (Iso.refl (Fin (k + 2))) NumNatTailIso)
      (NatCoding.finPlusNat (k + 2)))

theorem NumNat_child_lt :
    ∀ {k : Nat} (n : Nat)
      (q : NumPoly.Pos
          (NumInversion.decode k ((NumNatLayerIso k).invFun n).1).ctor
          (NumInversion.decode k ((NumNatLayerIso k).invFun n).1).param),
      (((NumNatLayerIso k).invFun n).2 q) < n := by
  intro k n
  generalize hz : (NumNatLayerIso k).invFun n = z
  have hn : (NumNatLayerIso k).toFun z = n := by
    rw [← hz]
    exact (NumNatLayerIso k).right_inv n
  change ∀ q : NumPoly.Pos (NumInversion.decode k z.1).ctor
      (NumInversion.decode k z.1).param,
    z.2 q < n
  cases z with
  | mk code child =>
      cases code with
      | var v =>
          intro q
          cases q
      | zero =>
          intro q
          cases q
      | succ =>
          intro q
          cases q
          let c := child ()
          have hn' : k + 2 + 2 * c = n := by
            simpa [c, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, NatCoding.sum3Nat, Iso.trans, Iso.sum,
              NatCoding.finPlusNat, NatCoding.sumNat] using hn
          change c < n
          rw [← hn']
          have heq : c + (k + 2 + c) = k + 2 + 2 * c := by
            rw [Nat.two_mul]
            ac_rfl
          have hlt : c < c + (k + 2 + c) :=
            Nat.lt_add_of_pos_right (by omega : 0 < k + 2 + c)
          rw [← heq]
          exact hlt
      | plus =>
          intro q
          let pcode := NatCoding.prodNat.toFun (child false, child true)
          have hn' : k + 2 + (2 * (2 * pcode) + 1) = n := by
            simpa [pcode, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, NatCoding.sum3Nat, Iso.trans, Iso.sum,
              NatCoding.finPlusNat, NatCoding.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_fst_le (NatCoding.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 3 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 3 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 3 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 3 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 3 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 3 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
      | times =>
          intro q
          let pcode := NatCoding.prodNat.toFun (child false, child true)
          have hn' : k + 2 + (2 * (2 * pcode + 1) + 1) = n := by
            simpa [pcode, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, NatCoding.sum3Nat, Iso.trans, Iso.sum,
              NatCoding.finPlusNat, NatCoding.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_fst_le (NatCoding.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 5 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode + 1) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 5 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 5 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 5 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode + 1) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 5 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 5 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt

def NumNatGeneratedCode : GeneratedNatCode NumPoly where
  inversion := NumInversion
  layer := NumNatLayerIso
  child_lt := NumNat_child_lt

def NumNatIso (k : Nat) : Mu NumPoly k ≃ᵢ Nat :=
  NumNatGeneratedCode.iso k

def NumSyntaxNatIso (k : Nat) : NumSyntax k ≃ᵢ Nat :=
  Iso.trans (Iso.symm (NumSyntaxIso k)) (NumNatIso k)

/-- Reference syntax family for Peano formulas indexed by context size.
Equality compares already-coded numeric terms in the same context. -/
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

/-- Polynomial constructors for Peano formulas indexed by context size. -/
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

def PeanoLayerToSyntax (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion PeanoSyntax k → PeanoSyntax k
  | ⟨.eq lhs rhs, _child⟩ =>
      .eq lhs rhs
  | ⟨.not, child⟩ =>
      .not (child ())
  | ⟨.implies, child⟩ =>
      .implies (child false) (child true)
  | ⟨.forallE, child⟩ =>
      .forallE (child ())

def PeanoSyntaxToLayer (k : Nat) :
    PeanoSyntax k → CodeLayer PeanoPoly PeanoInversion PeanoSyntax k
  | .eq lhs rhs => ⟨.eq lhs rhs, fun q => nomatch q⟩
  | .not e => ⟨.not, fun _ => e⟩
  | .implies lhs rhs => ⟨.implies, fun (b : Bool) => if b then rhs else lhs⟩
  | .forallE e => ⟨.forallE, fun _ => e⟩

theorem PeanoLayer_left_inv (k : Nat) :
    Function.LeftInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | eq lhs rhs =>
        have hchild : (fun q => nomatch q) = child := by
          funext q
          cases q
        cases hchild
        rfl
    | not =>
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl
    | implies =>
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl
    | forallE =>
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl

theorem PeanoLayer_right_inv (k : Nat) :
    Function.RightInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro e
  cases e <;> simp [PeanoLayerToSyntax, PeanoSyntaxToLayer]

def PeanoLayerIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion PeanoSyntax k ≃ᵢ PeanoSyntax k where
  toFun := PeanoLayerToSyntax k
  invFun := PeanoSyntaxToLayer k
  left_inv := PeanoLayer_left_inv k
  right_inv := PeanoLayer_right_inv k

theorem Peano_layer_child_rank_lt :
    ∀ {k : Nat} (z : PeanoSyntax k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k ((PeanoLayerIso k).invFun z).1).ctor
          (PeanoInversion.decode k ((PeanoLayerIso k).invFun z).1).param),
      PeanoSyntax.rank (((PeanoLayerIso k).invFun z).2 q) < PeanoSyntax.rank z := by
  intro k z q
  cases z with
  | eq lhs rhs => cases q
  | not e =>
      cases q
      simp [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
        PeanoSyntax.rank]
  | implies lhs rhs =>
      cases q
      · simpa [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
      · simpa [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
  | forallE e =>
      cases q
      simp [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
        PeanoSyntax.rank]

def PeanoGeneratedLayerCode : GeneratedLayerCode PeanoPoly PeanoSyntax where
  inversion := PeanoInversion
  layer := PeanoLayerIso
  rank := fun _ e => PeanoSyntax.rank e
  child_rank_lt := Peano_layer_child_rank_lt

def PeanoWellFoundedCode : WellFoundedCode PeanoPoly PeanoSyntax :=
  PeanoGeneratedLayerCode.toWellFoundedCode

/-- Peano formulas as the generic initial algebra are bijective with readable
syntax through generated layer coding, including the `forall` branch whose
child is in context `k + 1`. -/
def PeanoSyntaxIso (k : Nat) : Mu PeanoPoly k ≃ᵢ PeanoSyntax k :=
  PeanoGeneratedLayerCode.iso k

abbrev PeanoNatLayerShape :=
  (Nat × Nat) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ Nat))

def PeanoNatLayerShapeTo (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k → PeanoNatLayerShape
  | ⟨.eq lhs rhs, _child⟩ => Sum.inl ((NumNatIso k).toFun lhs, (NumNatIso k).toFun rhs)
  | ⟨.not, child⟩ => Sum.inr (Sum.inl (child ()))
  | ⟨.implies, child⟩ => Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨.forallE, child⟩ => Sum.inr (Sum.inr (Sum.inr (child ())))

def PeanoNatLayerShapeInv (k : Nat) :
    PeanoNatLayerShape → CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k
  | Sum.inl p =>
      ⟨.eq ((NumNatIso k).invFun p.1) ((NumNatIso k).invFun p.2),
        fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨.not, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨.implies, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr child)) => ⟨.forallE, fun _ => child⟩

theorem PeanoNatLayerShape_left_inv (k : Nat) :
    Function.LeftInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
  intro x
  cases x with
  | mk code child =>
      cases code with
      | eq lhs rhs =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rw [(NumNatIso k).left_inv lhs, (NumNatIso k).left_inv rhs]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | not =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
          rfl
      | implies =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]
      | forallE =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
          rfl

theorem PeanoNatLayerShape_right_inv (k : Nat) :
    Function.RightInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
  intro x
  cases x with
  | inl p =>
      cases p
      simp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
  | inr tail =>
      cases tail with
      | inl child => rfl
      | inr rest =>
          cases rest with
          | inl p =>
              cases p
              rfl
          | inr child => rfl

def PeanoNatLayerShapeIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k ≃ᵢ PeanoNatLayerShape where
  toFun := PeanoNatLayerShapeTo k
  invFun := PeanoNatLayerShapeInv k
  left_inv := PeanoNatLayerShape_left_inv k
  right_inv := PeanoNatLayerShape_right_inv k

def PeanoNatLayerIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k ≃ᵢ Nat :=
  Iso.trans (PeanoNatLayerShapeIso k)
    (Iso.trans (Iso.sum NatCoding.prodNat
      (Iso.sum (Iso.refl Nat) (Iso.sum NatCoding.prodNat (Iso.refl Nat))))
      NatCoding.sum4Nat)

theorem PeanoNat_child_lt :
    ∀ {k : Nat} (n : Nat)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k ((PeanoNatLayerIso k).invFun n).1).ctor
          (PeanoInversion.decode k ((PeanoNatLayerIso k).invFun n).1).param),
      (((PeanoNatLayerIso k).invFun n).2 q) < n := by
  intro k n
  generalize hz : (PeanoNatLayerIso k).invFun n = z
  have hn : (PeanoNatLayerIso k).toFun z = n := by
    rw [← hz]
    exact (PeanoNatLayerIso k).right_inv n
  change ∀ q : PeanoPoly.Pos (PeanoInversion.decode k z.1).ctor
      (PeanoInversion.decode k z.1).param,
    z.2 q < n
  cases z with
  | mk code child =>
      cases code with
      | eq lhs rhs =>
          intro q
          cases q
      | not =>
          intro q
          cases q
          let c := child ()
          have hn' : 2 * (2 * c) + 1 = n := by
            simpa [c, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              NatCoding.sum4Nat, Iso.trans, Iso.sum, NatCoding.sum3Nat,
              NatCoding.sumNat] using hn
          change c < n
          rw [← hn']
          exact Nat.lt_succ_of_le (by
            rw [Nat.two_mul, Nat.two_mul]
            simp [Nat.add_assoc])
      | implies =>
          intro q
          let pcode := NatCoding.prodNat.toFun (child false, child true)
          have hn' : 2 * (2 * (2 * pcode) + 1) + 1 = n := by
            simpa [pcode, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              NatCoding.sum4Nat, Iso.trans, Iso.sum, NatCoding.sum3Nat,
              NatCoding.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_fst_le (NatCoding.prodNat.toFun (child false, child true))
            have hpair_lt : pcode < 2 * (2 * (2 * pcode) + 1) + 1 :=
              Nat.lt_succ_of_le (by
                rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
                simp [Nat.add_assoc])
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, NatCoding.prodNat] using
                NatCoding.prodNat_snd_le (NatCoding.prodNat.toFun (child false, child true))
            have hpair_lt : pcode < 2 * (2 * (2 * pcode) + 1) + 1 :=
              Nat.lt_succ_of_le (by
                rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
                simp [Nat.add_assoc])
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
      | forallE =>
          intro q
          cases q
          let c := child ()
          have hn' : 2 * (2 * (2 * c + 1) + 1) + 1 = n := by
            simpa [c, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              NatCoding.sum4Nat, Iso.trans, Iso.sum, NatCoding.sum3Nat,
              NatCoding.sumNat] using hn
          change c < n
          rw [← hn']
          exact Nat.lt_succ_of_le (by
            rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
            simp [Nat.add_assoc])

def PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly where
  inversion := PeanoInversion
  layer := PeanoNatLayerIso
  child_lt := PeanoNat_child_lt

def PeanoNatIso (k : Nat) : Mu PeanoPoly k ≃ᵢ Nat :=
  PeanoNatGeneratedCode.iso k

def PeanoSyntaxNatIso (k : Nat) : PeanoSyntax k ≃ᵢ Nat :=
  Iso.trans (Iso.symm (PeanoSyntaxIso k)) (PeanoNatIso k)

end Examples
end BijForm
