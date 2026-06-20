import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly

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

/-- Output-index inversion for sorted trees.  The branch code exposes the
bounded pivot whose children move to `(lower, pivot)` and `(pivot, upper)`. -/
def SortedInversion : OutputIndexInversion SortedPoly :=
  OutputIndexInversion.canonical SortedPoly

private def sortedLeafFiber (i : SortedIx) : Fiber SortedPoly i :=
  ⟨SortedCtor.leaf, i, rfl⟩

private def sortedBranchFiber (i : SortedIx) (pivot : BoundedPivot i) : Fiber SortedPoly i :=
  ⟨SortedCtor.branch, ⟨i, pivot⟩, rfl⟩

def SortedLayerToSyntax (i : SortedIx) :
    CodeLayer SortedPoly SortedInversion SortedSyntax i → SortedSyntax i
  | ⟨⟨.leaf, _param, h⟩, _child⟩ => by
      cases h
      exact .leaf
  | ⟨⟨.branch, param, h⟩, child⟩ => by
      cases param with
      | mk _i pivot =>
          cases h
          exact .branch pivot (child false) (child true)

def SortedSyntaxToLayer (i : SortedIx) :
    SortedSyntax i → CodeLayer SortedPoly SortedInversion SortedSyntax i
  | .leaf =>
      ⟨sortedLeafFiber i, fun q => nomatch q⟩
  | .branch pivot lhs rhs =>
      ⟨sortedBranchFiber i pivot, fun
        | false => lhs
        | true => rhs⟩

theorem SortedLayer_left_inv (i : SortedIx) :
    Function.LeftInverse (SortedSyntaxToLayer i) (SortedLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | leaf =>
          cases out_eq
          have hchild : (fun q => nomatch q) = child := by
            child_eta_empty
          cases hchild
          rfl
      | branch =>
          cases param with
          | mk _i pivot =>
            cases out_eq
            have hchild : child = (fun
                | false => child false
                | true => child true) := by
              child_eta_bool
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
      · simpa [SortedLayerIso, SortedSyntaxToLayer, SortedInversion,
          OutputIndexInversion.canonical, sortedBranchFiber, SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))
      · simpa [SortedLayerIso, SortedSyntaxToLayer, SortedInversion,
          OutputIndexInversion.canonical, sortedBranchFiber, SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))

def SortedGeneratedCode : GeneratedCode SortedPoly SortedSyntax where
  inversion := SortedInversion
  layer := SortedLayerIso
  rank := fun _ t => SortedSyntax.rank t
  child_rank_lt := Sorted_layer_child_rank_lt

def SortedWellFoundedCode : WellFoundedCode SortedPoly SortedSyntax :=
  SortedGeneratedCode.toWellFoundedCode

/-- Sorted trees as the generic initial algebra are bijective with readable
syntax through generated layer coding. -/
def SortedSyntaxIso (i : SortedIx) : Mu SortedPoly i ≃ᵢ SortedSyntax i :=
  SortedGeneratedCode.iso i

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
        | ⟨⟨.leaf, _param, hout⟩, _child⟩ => by
            cases hout
            exact ⟨0, by decide⟩
        | ⟨⟨.branch, param, hout⟩, _child⟩ => by
            cases param with
            | mk _i pivot =>
                cases hout
                exact False.elim (h pivot.bound_le)
      invFun := fun _ => ⟨sortedLeafFiber i, fun q => nomatch q⟩
      left_inv := by
        intro layer
        cases layer with
        | mk code child =>
          cases code with
          | mk ctor param out_eq =>
            cases ctor with
            | leaf =>
                cases out_eq
                have hchild : (fun q => nomatch q) = child := by
                  child_eta_empty
                cases hchild
                rfl
            | branch =>
                cases param with
                | mk _i pivot =>
                    cases out_eq
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
    | ⟨⟨.leaf, _param, hout⟩, _child⟩ => by
        cases hout
        exact Sum.inl ⟨0, by decide⟩
    | ⟨⟨.branch, param, hout⟩, child⟩ => by
        cases param with
        | mk _i pivot =>
            cases hout
            exact Sum.inr
              ((BoundedPivotFiniteIso lower upper h).toFun pivot,
                (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false),
                 SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)))
  invFun
    | Sum.inl _ => ⟨sortedLeafFiber (lower, some upper), fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotFiniteIso lower upper h).invFun payload.1
        ⟨sortedBranchFiber (lower, some upper) pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1 payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, some upper)) pivot.property.2 payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | mk ctor param out_eq =>
        cases ctor with
        | leaf =>
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              child_eta_empty
            cases hchild
            rfl
        | branch =>
            cases param with
            | mk _i pivot =>
                cases out_eq
                dsimp [sortedBranchFiber]
                rw [(BoundedPivotFiniteIso lower upper h).left_inv pivot]
                have hchild :
                    child =
                    (fun
                      | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
                          (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false))
                      | true => SortedCarrier.ofNat (i := (pivot.1, some upper)) pivot.property.2
                          (SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true))) := by
                  funext q
                  cases q
                  · exact (SortedCarrier.ofNat_toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)).symm
                  · exact (SortedCarrier.ofNat_toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)).symm
                apply Sigma.ext
                · rfl
                · exact heq_of_eq hchild.symm
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
            dsimp [sortedBranchFiber]
            rw [(BoundedPivotFiniteIso lower upper h).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

def SortedFiniteLayerNatIso (lower upper : Nat) (h : lower ≤ upper) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper) ≃ᵢ Nat :=
  Iso.trans (SortedFiniteLayerShapeIso lower upper h)
    (CodeAlgebra.finPrefixNat 1
      (CodeAlgebra.finProdProdNat (upper - lower + 1) (by omega)))

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
    | ⟨⟨.leaf, _param, hout⟩, _child⟩ => by
        cases hout
        exact Sum.inl ⟨0, by decide⟩
    | ⟨⟨.branch, param, hout⟩, child⟩ => by
        cases param with
        | mk _i pivot =>
            cases hout
            exact Sum.inr
              ((BoundedPivotInfiniteIso lower).toFun pivot,
                (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false),
                 SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true)))
  invFun
    | Sum.inl _ => ⟨sortedLeafFiber (lower, none), fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotInfiniteIso lower).invFun payload.1
        ⟨sortedBranchFiber (lower, none) pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1 payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, none)) pivot.property.2 payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | mk ctor param out_eq =>
        cases ctor with
        | leaf =>
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              child_eta_empty
            cases hchild
            rfl
        | branch =>
            cases param with
            | mk _i pivot =>
                cases out_eq
                dsimp [sortedBranchFiber]
                rw [(BoundedPivotInfiniteIso lower).left_inv pivot]
                have hchild :
                    child =
                    (fun
                      | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
                          (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false))
                      | true => SortedCarrier.ofNat (i := (pivot.1, none)) pivot.property.2
                          (SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true))) := by
                  funext q
                  cases q
                  · exact (SortedCarrier.ofNat_toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)).symm
                  · exact (SortedCarrier.ofNat_toNat (i := (pivot.1, none)) pivot.property.2 (child true)).symm
                apply Sigma.ext
                · rfl
                · exact heq_of_eq hchild.symm
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
            dsimp [sortedBranchFiber]
            rw [(BoundedPivotInfiniteIso lower).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

def SortedInfiniteLayerNatIso (lower : Nat) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none) ≃ᵢ Nat :=
  Iso.trans (SortedInfiniteLayerShapeIso lower)
    (CodeAlgebra.finPrefixNat 1 CodeAlgebra.natProdProdNat)

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

theorem SortedFiniteLayerNat_layer_child_rank_lt (lower upper : Nat) (h : lower ≤ upper) :
    ∀ (layer : CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper))
      (q : SortedPoly.Pos
          (SortedInversion.decode (lower, some upper)
            layer.1).ctor
          (SortedInversion.decode (lower, some upper)
            layer.1).param),
      SortedCarrierRank
          (SortedPoly.input
            (SortedInversion.decode (lower, some upper)
              layer.1).param q)
          (layer.2 q) < (SortedFiniteLayerNatIso lower upper h).toFun layer := by
  intro layer
  intro q
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | leaf =>
          cases out_eq
          cases q
      | branch =>
          cases param with
          | mk _i pivot =>
            cases out_eq
            let lhsCode :=
              SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
            let rhsCode :=
              SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2 (child true)
            let payloadCode :=
              (CodeAlgebra.finProdProdNat (upper - lower + 1) (by omega)).toFun
              ((BoundedPivotFiniteIso lower upper h).toFun pivot, (lhsCode, rhsCode))
            have hparent :
                (SortedFiniteLayerNatIso lower upper h).toFun
                    ⟨sortedBranchFiber (lower, some upper) pivot, child⟩ =
                  1 + payloadCode := by
              simp [payloadCode, lhsCode, rhsCode, SortedFiniteLayerNatIso,
                SortedFiniteLayerShapeIso, CodeAlgebra.finPrefixNat,
                CodeAlgebra.finProdProdNat, Iso.trans, Iso.sum, Iso.prod,
                CodeAlgebra.finPlusNat, Iso.refl, sortedBranchFiber]
            have hpayload_lt :
                payloadCode <
                  (SortedFiniteLayerNatIso lower upper h).toFun
                    ⟨sortedBranchFiber (lower, some upper) pivot, child⟩ := by
              rw [hparent]
              omega
            have hpivotUpper : pivot.1 ≤ upper := pivot.property.2
            cases q
            · have hchild_le_payload : lhsCode ≤ payloadCode := by
                simpa [payloadCode, lhsCode, rhsCode] using
                  CodeAlgebra.finProdProdNat_toFun_snd_fst_le
                    (upper - lower + 1) (by omega)
                    (((BoundedPivotFiniteIso lower upper h).toFun pivot), (lhsCode, rhsCode))
              have hlt :
                  lhsCode <
                    (SortedFiniteLayerNatIso lower upper h).toFun
                      ⟨sortedBranchFiber (lower, some upper) pivot, child⟩ :=
                Nat.lt_of_le_of_lt hchild_le_payload hpayload_lt
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                pivot.property.1] using hlt
            · have hchild_le_payload : rhsCode ≤ payloadCode := by
                simpa [payloadCode, lhsCode, rhsCode] using
                  CodeAlgebra.finProdProdNat_toFun_snd_snd_le
                    (upper - lower + 1) (by omega)
                    (((BoundedPivotFiniteIso lower upper h).toFun pivot), (lhsCode, rhsCode))
              have hlt :
                  rhsCode <
                    (SortedFiniteLayerNatIso lower upper h).toFun
                      ⟨sortedBranchFiber (lower, some upper) pivot, child⟩ :=
                Nat.lt_of_le_of_lt hchild_le_payload hpayload_lt
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, rhsCode,
                hpivotUpper] using hlt

theorem SortedInfiniteLayerNat_layer_child_rank_lt (lower : Nat) :
    ∀ (layer : CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none))
      (q : SortedPoly.Pos
          (SortedInversion.decode (lower, none)
            layer.1).ctor
          (SortedInversion.decode (lower, none)
            layer.1).param),
      SortedCarrierRank
          (SortedPoly.input
            (SortedInversion.decode (lower, none)
              layer.1).param q)
          (layer.2 q) < (SortedInfiniteLayerNatIso lower).toFun layer := by
  intro layer
  intro q
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | leaf =>
          cases out_eq
          cases q
      | branch =>
          cases param with
          | mk _i pivot =>
            cases out_eq
            let lhsCode :=
              SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1 (child false)
            let rhsCode :=
              SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2 (child true)
            let pivotCode := (BoundedPivotInfiniteIso lower).toFun pivot
            let payloadCode := CodeAlgebra.natProdProdNat.toFun (pivotCode, (lhsCode, rhsCode))
            have hparent :
                (SortedInfiniteLayerNatIso lower).toFun
                    ⟨sortedBranchFiber (lower, none) pivot, child⟩ =
                  1 + payloadCode := by
              simp [payloadCode, pivotCode, lhsCode, rhsCode,
                SortedInfiniteLayerNatIso, SortedInfiniteLayerShapeIso,
                CodeAlgebra.finPrefixNat, CodeAlgebra.natProdProdNat, Iso.trans,
                Iso.sum, Iso.prod, CodeAlgebra.finPlusNat, Iso.refl, sortedBranchFiber]
            have hpayload_lt :
                payloadCode < (SortedInfiniteLayerNatIso lower).toFun
                  ⟨sortedBranchFiber (lower, none) pivot, child⟩ := by
              rw [hparent]
              omega
            cases q
            · have hchild_le_payload : lhsCode ≤ payloadCode := by
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using
                  CodeAlgebra.natProdProdNat_toFun_snd_fst_le
                    (pivotCode, (lhsCode, rhsCode))
              have hlt :
                  lhsCode < (SortedInfiniteLayerNatIso lower).toFun
                    ⟨sortedBranchFiber (lower, none) pivot, child⟩ :=
                Nat.lt_of_le_of_lt hchild_le_payload hpayload_lt
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                pivot.property.1] using hlt
            · have hchild_le_payload : rhsCode ≤ payloadCode := by
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using
                  CodeAlgebra.natProdProdNat_toFun_snd_snd_le
                    (pivotCode, (lhsCode, rhsCode))
              have hlt :
                  rhsCode < (SortedInfiniteLayerNatIso lower).toFun
                    ⟨sortedBranchFiber (lower, none) pivot, child⟩ :=
                Nat.lt_of_le_of_lt hchild_le_payload hpayload_lt
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, rhsCode] using hlt

theorem SortedShape_layer_child_rank_lt :
    ∀ {i : SortedIx} (layer : CodeLayer SortedPoly SortedInversion SortedCarrier i)
      (q : SortedPoly.Pos
          (SortedInversion.decode i layer.1).ctor
          (SortedInversion.decode i layer.1).param),
      SortedCarrierRank
          (SortedPoly.input (SortedInversion.decode i layer.1).param q)
          (layer.2 q) < SortedCarrierRank i ((SortedShapeLayerIso i).toFun layer) := by
  intro i layer
  cases i with
  | mk lower upper =>
    cases upper with
    | none =>
      intro q
      simpa [SortedShapeLayerIso, SortedInfiniteLayerIso, Iso.trans, Iso.symm,
        SortedCarrier.natIso, SortedCarrierRank, Bound.le] using
        SortedInfiniteLayerNat_layer_child_rank_lt lower layer q
    | some upper =>
      by_cases h : lower ≤ upper
      · dsimp [SortedShapeLayerIso]
        rw [dif_pos h]
        intro q
        simpa [SortedShapeLayerIso, SortedFiniteLayerIso, Iso.trans, Iso.symm,
          SortedCarrier.natIso, SortedCarrier.toNat_ofNat, SortedCarrierRank, Bound.le, h] using
          SortedFiniteLayerNat_layer_child_rank_lt lower upper h layer q
      · dsimp [SortedShapeLayerIso]
        rw [dif_neg h]
        cases layer with
        | mk code child =>
          cases code with
          | mk ctor param out_eq =>
            cases ctor with
            | leaf =>
                cases out_eq
                intro q
                cases q
            | branch =>
                cases param with
                | mk _i pivot =>
                    cases out_eq
                    exact False.elim (h pivot.bound_le)

def SortedGeneratedShapeCode : GeneratedShapeCode SortedPoly :=
  GeneratedShapeCode.ofLayerChildRank SortedShape SortedInversion SortedShapeLayerIso
    SortedCarrierRank
    (by
      intro i layer q
      exact SortedShape_layer_child_rank_lt layer q)

def SortedShapeIso (i : SortedIx) : Mu SortedPoly i ≃ᵢ SortedCarrier i :=
  SortedGeneratedShapeCode.iso i

def SortedSyntaxShapeIso (i : SortedIx) : SortedSyntax i ≃ᵢ SortedCarrier i :=
  Iso.trans (Iso.symm (SortedSyntaxIso i)) (SortedShapeIso i)

def SortedSyntaxNatIsoOfBound (i : SortedIx) (h : Bound.le i.1 i.2) :
    SortedSyntax i ≃ᵢ Nat :=
  Iso.trans (SortedSyntaxShapeIso i) (SortedCarrier.natIso h)

def SortedSyntaxFinOneIsoOfNotBound (i : SortedIx) (h : ¬Bound.le i.1 i.2) :
    SortedSyntax i ≃ᵢ Fin 1 :=
  Iso.trans (SortedSyntaxShapeIso i) (SortedCarrier.finOneIso h)

def SortedSyntaxInfiniteNatIso (lower : Nat) :
    SortedSyntax (lower, none) ≃ᵢ Nat :=
  SortedSyntaxNatIsoOfBound (lower, none) trivial

def SortedSyntaxFiniteNatIso (lower upper : Nat) (h : lower ≤ upper) :
    SortedSyntax (lower, some upper) ≃ᵢ Nat :=
  SortedSyntaxNatIsoOfBound (lower, some upper) h

def SortedSyntaxInvalidFiniteIso (lower upper : Nat) (h : ¬lower ≤ upper) :
    SortedSyntax (lower, some upper) ≃ᵢ Fin 1 :=
  SortedSyntaxFinOneIsoOfNotBound (lower, some upper) h

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
  SortedSyntaxInvalidFiniteIso 1 0 (by omega)

end Examples
end BijForm
