import BijForm.InitialAlgebra
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
    exact fin_eq_of_val_eq (Nat.add_sub_cancel_left lower code.val)

private theorem sortedFinitePayloadPositive (lower upper : Nat) (_h : lower ≤ upper) :
    0 < upper - lower + 1 := by
  omega

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

theorem Sorted_layer_child_rank_lt :
    ∀ {i : SortedIx} (z : SortedSyntax i)
      (q : SortedPoly.Pos
          (SortedInversion.decode i
            (SortedSyntaxToLayer i z).1).ctor
          (SortedInversion.decode i
            (SortedSyntaxToLayer i z).1).param),
      SortedSyntax.rank ((SortedSyntaxToLayer i z).2 q) <
        SortedSyntax.rank z := by
  intro i z q
  cases z with
  | leaf => cases q
  | branch pivot lhs rhs =>
      cases q
      · simpa [SortedSyntaxToLayer, SortedInversion,
          OutputIndexInversion.canonical, sortedBranchFiber, SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))
      · simpa [SortedSyntaxToLayer, SortedInversion,
          OutputIndexInversion.canonical, sortedBranchFiber, SortedSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (SortedSyntax.rank lhs) (SortedSyntax.rank rhs))

def SortedSyntaxPresentation : SyntaxPresentation SortedPoly SortedInversion SortedSyntax :=
  SyntaxPresentation.ofLayerMaps
    SortedLayerToSyntax
    SortedSyntaxToLayer
    (by
      intro i layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | leaf =>
              cases out_eq
              child_eta_rfl child
          | branch =>
              cases param with
              | mk _i pivot =>
                cases out_eq
                child_eta_rfl child)
    (by
      intro i t
      cases t with
      | leaf => rfl
      | branch pivot lhs rhs => rfl)
    (fun _ t => SortedSyntax.rank t)
    Sorted_layer_child_rank_lt

def SortedGeneratedCode : GeneratedCode SortedPoly SortedSyntax :=
  SortedSyntaxPresentation.generatedCode

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

def natIso {i : SortedIx} (h : Bound.le i.1 i.2) : SortedCarrier i ≃ᵢ Nat :=
  CodeShape.carrierNatIso SortedShape i (by
    simp [SortedShape, h])

def finOneIso {i : SortedIx} (h : ¬Bound.le i.1 i.2) : SortedCarrier i ≃ᵢ Fin 1 :=
  CodeShape.carrierFinIso SortedShape i (by
    simp [SortedShape, h])

end SortedCarrier

abbrev SortedFiniteConstructorPayload (lower upper : Nat) :=
  Fin 1 ⊕ (Fin (upper - lower + 1) × (Nat × Nat))

private abbrev SortedInfiniteConstructorPayload :=
  Fin 1 ⊕ (Nat × (Nat × Nat))

abbrev SortedLayerShape : SortedIx → Type :=
  SortedCarrier

private def SortedFiniteConstructorPayloadIso (lower upper : Nat) (h : lower ≤ upper) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, some upper) ≃ᵢ
      SortedFiniteConstructorPayload lower upper where
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
                (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1
                  (child false),
                 SortedCarrier.toNat (i := (pivot.1, some upper)) pivot.property.2
                  (child true)))
  invFun
    | Sum.inl _ => ⟨sortedLeafFiber (lower, some upper), fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotFiniteIso lower upper h).invFun payload.1
        ⟨sortedBranchFiber (lower, some upper) pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
              payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, some upper)) pivot.property.2
              payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | mk ctor param out_eq =>
        cases ctor with
        | leaf =>
            cases out_eq
            child_eta_rfl child
        | branch =>
            cases param with
            | mk _i pivot =>
                cases out_eq
                dsimp [sortedBranchFiber]
                rw [(BoundedPivotFiniteIso lower upper h).left_inv pivot]
                have hchild :
                    child =
                    (fun
                      | false => SortedCarrier.ofNat (i := (lower, some pivot.1))
                          pivot.property.1
                          (SortedCarrier.toNat (i := (lower, some pivot.1))
                            pivot.property.1 (child false))
                      | true => SortedCarrier.ofNat (i := (pivot.1, some upper))
                          pivot.property.2
                          (SortedCarrier.toNat (i := (pivot.1, some upper))
                            pivot.property.2 (child true))) := by
                  funext q
                  cases q
                  · exact (SortedCarrier.ofNat_toNat (i := (lower, some pivot.1))
                      pivot.property.1 (child false)).symm
                  · exact (SortedCarrier.ofNat_toNat (i := (pivot.1, some upper))
                      pivot.property.2 (child true)).symm
                apply Sigma.ext
                · rfl
                · exact heq_of_eq hchild.symm
  right_inv := by
    intro shape
    cases shape with
    | inl tag =>
      apply congrArg Sum.inl
      exact (fin_one_eq tag ⟨0, by decide⟩).symm
    | inr payload =>
        cases payload with
        | mk pivotCode pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp [sortedBranchFiber]
            rw [(BoundedPivotFiniteIso lower upper h).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

private def SortedInfiniteConstructorPayloadIso (lower : Nat) :
    CodeLayer SortedPoly SortedInversion SortedCarrier (lower, none) ≃ᵢ
      SortedInfiniteConstructorPayload where
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
                (SortedCarrier.toNat (i := (lower, some pivot.1)) pivot.property.1
                  (child false),
                 SortedCarrier.toNat (i := (pivot.1, none)) pivot.property.2
                  (child true)))
  invFun
    | Sum.inl _ => ⟨sortedLeafFiber (lower, none), fun q => nomatch q⟩
    | Sum.inr payload =>
        let pivot := (BoundedPivotInfiniteIso lower).invFun payload.1
        ⟨sortedBranchFiber (lower, none) pivot, fun
          | false => SortedCarrier.ofNat (i := (lower, some pivot.1)) pivot.property.1
              payload.2.1
          | true => SortedCarrier.ofNat (i := (pivot.1, none)) pivot.property.2
              payload.2.2⟩
  left_inv := by
    intro layer
    cases layer with
    | mk code child =>
      cases code with
      | mk ctor param out_eq =>
        cases ctor with
        | leaf =>
            cases out_eq
            child_eta_rfl child
        | branch =>
            cases param with
            | mk _i pivot =>
                cases out_eq
                dsimp [sortedBranchFiber]
                rw [(BoundedPivotInfiniteIso lower).left_inv pivot]
                have hchild :
                    child =
                    (fun
                      | false => SortedCarrier.ofNat (i := (lower, some pivot.1))
                          pivot.property.1
                          (SortedCarrier.toNat (i := (lower, some pivot.1))
                            pivot.property.1 (child false))
                      | true => SortedCarrier.ofNat (i := (pivot.1, none))
                          pivot.property.2
                          (SortedCarrier.toNat (i := (pivot.1, none))
                            pivot.property.2 (child true))) := by
                  funext q
                  cases q
                  · exact (SortedCarrier.ofNat_toNat (i := (lower, some pivot.1))
                      pivot.property.1 (child false)).symm
                  · exact (SortedCarrier.ofNat_toNat (i := (pivot.1, none))
                      pivot.property.2 (child true)).symm
                apply Sigma.ext
                · rfl
                · exact heq_of_eq hchild.symm
  right_inv := by
    intro shape
    cases shape with
    | inl tag =>
      apply congrArg Sum.inl
      exact (fin_one_eq tag ⟨0, by decide⟩).symm
    | inr payload =>
        cases payload with
        | mk pivotCode pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp [sortedBranchFiber]
            rw [(BoundedPivotInfiniteIso lower).right_inv pivotCode]
            rw [SortedCarrier.toNat_ofNat, SortedCarrier.toNat_ofNat]

private def SortedCarrierLayerIso (i : SortedIx) :
    CodeLayer SortedPoly SortedInversion SortedCarrier i ≃ᵢ SortedCarrier i where
  toFun := by
    cases i with
    | mk lower upper =>
      cases upper with
      | none =>
          exact fun layer =>
            SortedCarrier.ofNat (i := (lower, none)) trivial
              ((Iso.trans (SortedInfiniteConstructorPayloadIso lower)
                (CodeAlgebra.finPrefixNat 1 CodeAlgebra.natProdProdNat)).toFun layer)
      | some upper =>
          exact fun layer =>
            if h : lower ≤ upper then
              SortedCarrier.ofNat (i := (lower, some upper)) h
                ((Iso.trans (SortedFiniteConstructorPayloadIso lower upper h)
                  (CodeAlgebra.finPrefixNat 1
                    (CodeAlgebra.finProdProdNat (upper - lower + 1)
                      (sortedFinitePayloadPositive lower upper h)))).toFun layer)
            else
              match layer with
              | ⟨⟨.leaf, _param, hout⟩, _child⟩ => by
                  cases hout
                  exact SortedCarrier.ofFinOne (i := (lower, some upper)) h ⟨0, by decide⟩
              | ⟨⟨.branch, param, hout⟩, _child⟩ => by
                  cases param with
                  | mk _i pivot =>
                      cases hout
                      exact False.elim (h pivot.bound_le)
  invFun := by
    cases i with
    | mk lower upper =>
      cases upper with
      | none =>
          exact fun z =>
            (Iso.trans (SortedInfiniteConstructorPayloadIso lower)
              (CodeAlgebra.finPrefixNat 1 CodeAlgebra.natProdProdNat)).invFun
              (SortedCarrier.toNat (i := (lower, none)) trivial z)
      | some upper =>
          exact fun z =>
            if h : lower ≤ upper then
              (Iso.trans (SortedFiniteConstructorPayloadIso lower upper h)
                (CodeAlgebra.finPrefixNat 1
                  (CodeAlgebra.finProdProdNat (upper - lower + 1)
                    (sortedFinitePayloadPositive lower upper h)))).invFun
                (SortedCarrier.toNat (i := (lower, some upper)) h z)
            else
              ⟨sortedLeafFiber (lower, some upper), fun q => nomatch q⟩
  left_inv := by
    cases i with
    | mk lower upper =>
      cases upper with
      | none =>
          intro layer
          simp [SortedCarrier.toNat_ofNat]
      | some upper =>
          intro layer
          by_cases h : lower ≤ upper
          · simp [h, SortedCarrier.toNat_ofNat]
          · cases layer with
            | mk code child =>
              cases code with
              | mk ctor param out_eq =>
                cases ctor with
                | leaf =>
                    cases out_eq
                    simp [h]
                    child_eta_rfl child
                | branch =>
                    cases param with
                    | mk _i pivot =>
                        cases out_eq
                        exact False.elim (h pivot.bound_le)
  right_inv := by
    cases i with
    | mk lower upper =>
      cases upper with
      | none =>
          intro z
          simp [SortedCarrier.ofNat_toNat]
      | some upper =>
          intro z
          by_cases h : lower ≤ upper
          · simp [h, SortedCarrier.ofNat_toNat]
          · haveI : Subsingleton (SortedCarrier (lower, some upper)) := by
              dsimp [SortedCarrier, SortedShape, Bound.le]
              rw [if_neg h]
              constructor
              intro a b
              exact fin_one_eq a b
            exact Subsingleton.elim _ _

def SortedCarrierRank (i : SortedIx) (z : SortedCarrier i) : Nat :=
  if h : Bound.le i.1 i.2 then
    SortedCarrier.toNat h z
  else
    0

theorem SortedFiniteConstructorPayload_child_rank_lt (lower upper : Nat) (h : lower ≤ upper) :
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
          (layer.2 q) <
        SortedCarrierRank (lower, some upper)
          ((SortedCarrierLayerIso (lower, some upper)).toFun layer) := by
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
              (CodeAlgebra.finProdProdNat (upper - lower + 1)
                (sortedFinitePayloadPositive lower upper h)).toFun
              ((BoundedPivotFiniteIso lower upper h).toFun pivot, (lhsCode, rhsCode))
            have hpivotUpper : pivot.1 ≤ upper := pivot.property.2
            cases q
            · have hchild_le_payload : lhsCode ≤ payloadCode := by
                simpa [payloadCode, lhsCode, rhsCode] using
                  CodeAlgebra.finProdProdNat_toFun_snd_fst_le
                    (upper - lower + 1) (by omega)
                    (((BoundedPivotFiniteIso lower upper h).toFun pivot), (lhsCode, rhsCode))
              have hlt :
                  lhsCode < (CodeAlgebra.finPrefixNat 1
                    (CodeAlgebra.finProdProdNat (upper - lower + 1)
                      (sortedFinitePayloadPositive lower upper h))).toFun
                      (Sum.inr (((BoundedPivotFiniteIso lower upper h).toFun pivot),
                        (lhsCode, rhsCode))) := by
                have hprefix := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
                  1 (by decide)
                  (CodeAlgebra.finProdProdNat (upper - lower + 1)
                    (sortedFinitePayloadPositive lower upper h))
                  (a := ((BoundedPivotFiniteIso lower upper h).toFun pivot,
                    (lhsCode, rhsCode))) hchild_le_payload
                simpa [payloadCode, lhsCode, rhsCode] using hprefix
              have hcarrier :
                  SortedCarrierRank (lower, some upper)
                    ((SortedCarrierLayerIso (lower, some upper)).toFun
                      ⟨sortedBranchFiber (lower, some upper) pivot, child⟩) =
                    (CodeAlgebra.finPrefixNat 1
                      (CodeAlgebra.finProdProdNat (upper - lower + 1)
                        (sortedFinitePayloadPositive lower upper h))).toFun
                        (Sum.inr (((BoundedPivotFiniteIso lower upper h).toFun pivot),
                          (lhsCode, rhsCode))) := by
                simp [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                  OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                  rhsCode,
                  SortedCarrierLayerIso, SortedFiniteConstructorPayloadIso, Iso.trans,
                  Function.comp, SortedCarrier.toNat,
                  SortedCarrier.ofNat, SortedCarrier, SortedShape, h]
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                pivot.property.1] using (lt_of_lt_of_eq hlt hcarrier.symm)
            · have hchild_le_payload : rhsCode ≤ payloadCode := by
                simpa [payloadCode, lhsCode, rhsCode] using
                  CodeAlgebra.finProdProdNat_toFun_snd_snd_le
                    (upper - lower + 1) (by omega)
                    (((BoundedPivotFiniteIso lower upper h).toFun pivot), (lhsCode, rhsCode))
              have hlt :
                  rhsCode < (CodeAlgebra.finPrefixNat 1
                    (CodeAlgebra.finProdProdNat (upper - lower + 1)
                      (sortedFinitePayloadPositive lower upper h))).toFun
                      (Sum.inr (((BoundedPivotFiniteIso lower upper h).toFun pivot),
                        (lhsCode, rhsCode))) := by
                have hprefix := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
                  1 (by decide)
                  (CodeAlgebra.finProdProdNat (upper - lower + 1)
                    (sortedFinitePayloadPositive lower upper h))
                  (a := ((BoundedPivotFiniteIso lower upper h).toFun pivot,
                    (lhsCode, rhsCode))) hchild_le_payload
                simpa [payloadCode, lhsCode, rhsCode] using hprefix
              have hcarrier :
                  SortedCarrierRank (lower, some upper)
                    ((SortedCarrierLayerIso (lower, some upper)).toFun
                      ⟨sortedBranchFiber (lower, some upper) pivot, child⟩) =
                    (CodeAlgebra.finPrefixNat 1
                      (CodeAlgebra.finProdProdNat (upper - lower + 1)
                        (sortedFinitePayloadPositive lower upper h))).toFun
                        (Sum.inr (((BoundedPivotFiniteIso lower upper h).toFun pivot),
                          (lhsCode, rhsCode))) := by
                simp [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                  OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                  rhsCode,
                  SortedCarrierLayerIso, SortedFiniteConstructorPayloadIso, Iso.trans,
                  Function.comp, SortedCarrier.toNat,
                  SortedCarrier.ofNat, SortedCarrier, SortedShape, h]
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, rhsCode,
                hpivotUpper] using (lt_of_lt_of_eq hlt hcarrier.symm)

theorem SortedInfiniteConstructorPayload_child_rank_lt (lower : Nat) :
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
          (layer.2 q) <
        SortedCarrierRank (lower, none)
          ((SortedCarrierLayerIso (lower, none)).toFun layer) := by
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
            cases q
            · have hchild_le_payload : lhsCode ≤ payloadCode := by
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using
                  CodeAlgebra.natProdProdNat_toFun_snd_fst_le
                    (pivotCode, (lhsCode, rhsCode))
              have hlt :
                  lhsCode < (CodeAlgebra.finPrefixNat 1 CodeAlgebra.natProdProdNat).toFun
                    (Sum.inr (pivotCode, (lhsCode, rhsCode))) := by
                have hprefix := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
                  1 (by decide) CodeAlgebra.natProdProdNat
                  (a := (pivotCode, (lhsCode, rhsCode))) hchild_le_payload
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using hprefix
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, lhsCode,
                pivot.property.1, SortedCarrierLayerIso] using hlt
            · have hchild_le_payload : rhsCode ≤ payloadCode := by
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using
                  CodeAlgebra.natProdProdNat_toFun_snd_snd_le
                    (pivotCode, (lhsCode, rhsCode))
              have hlt :
                  rhsCode < (CodeAlgebra.finPrefixNat 1 CodeAlgebra.natProdProdNat).toFun
                    (Sum.inr (pivotCode, (lhsCode, rhsCode))) := by
                have hprefix := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
                  1 (by decide) CodeAlgebra.natProdProdNat
                  (a := (pivotCode, (lhsCode, rhsCode))) hchild_le_payload
                simpa [payloadCode, pivotCode, lhsCode, rhsCode] using hprefix
              simpa [SortedCarrierRank, SortedPoly, SortedInput, SortedInversion,
                OutputIndexInversion.canonical, sortedBranchFiber, Bound.le, rhsCode,
                SortedCarrierLayerIso] using hlt

def SortedLayerPresentation :
    LayerPresentation SortedPoly SortedInversion SortedCarrier :=
  LayerPresentation.ofCarrierLayerIso SortedCarrierLayerIso SortedCarrierRank (by
    intro i z q
    cases i with
    | mk lower upper =>
      cases upper with
      | none =>
          have hlt := SortedInfiniteConstructorPayload_child_rank_lt lower
            ((SortedCarrierLayerIso (lower, none)).invFun z) q
          have hparent :
              SortedCarrierRank (lower, none)
                ((SortedCarrierLayerIso (lower, none)).toFun
                  ((SortedCarrierLayerIso (lower, none)).invFun z)) =
              SortedCarrierRank (lower, none) z :=
            congrArg (SortedCarrierRank (lower, none))
              ((SortedCarrierLayerIso (lower, none)).right_inv z)
          simpa [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
            SortedLayerShape, Iso.refl, SortedCarrierRank, Bound.le] using
            (lt_of_lt_of_eq hlt hparent)
      | some upper =>
          by_cases h : lower ≤ upper
          · revert q
            intro q
            have hlt := SortedFiniteConstructorPayload_child_rank_lt lower upper h
              ((SortedCarrierLayerIso (lower, some upper)).invFun z) q
            have hparent :
                SortedCarrierRank (lower, some upper)
                  ((SortedCarrierLayerIso (lower, some upper)).toFun
                    ((SortedCarrierLayerIso (lower, some upper)).invFun z)) =
                SortedCarrierRank (lower, some upper) z :=
              congrArg (SortedCarrierRank (lower, some upper))
                ((SortedCarrierLayerIso (lower, some upper)).right_inv z)
            simpa [SortedLayerShape, Iso.refl, SortedCarrierRank, Bound.le, h] using
              (lt_of_lt_of_eq hlt hparent)
          · revert q
            dsimp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
              SortedLayerShape, SortedCarrierRank, Bound.le, h]
            intro q
            dsimp [SortedCarrierLayerIso, Iso.refl] at q
            rw [dif_neg h] at q
            change SortedPoly.Pos SortedCtor.leaf (lower, some upper) at q
            cases q)

def SortedShapeLayerPresentation :
    ShapeLayerPresentation SortedPoly SortedInversion :=
  ShapeLayerPresentation.ofLayerPresentation SortedShape SortedLayerPresentation

def SortedGeneratedShapeCode : GeneratedShapeCode SortedPoly :=
  SortedShapeLayerPresentation.generatedCode

def SortedShapeIso (i : SortedIx) : Mu SortedPoly i ≃ᵢ SortedCarrier i :=
  SortedGeneratedShapeCode.iso i

def SortedSyntaxShapeIso (i : SortedIx) : SortedSyntax i ≃ᵢ SortedCarrier i :=
  GeneratedCode.shapeCodeIso SortedGeneratedCode SortedGeneratedShapeCode i

def SortedSyntaxNatIsoOfBound (i : SortedIx) (h : Bound.le i.1 i.2) :
    SortedSyntax i ≃ᵢ Nat :=
  GeneratedCode.shapeNatIso SortedGeneratedCode SortedGeneratedShapeCode i (by
    cases i with
    | mk lower upper =>
        cases upper with
        | none => rfl
        | some upper =>
            change SortedShape (lower, some upper) = CodeShape.infinite
            dsimp [SortedShape, Bound.le] at h ⊢
            rw [if_pos h])

def SortedSyntaxFinOneIsoOfNotBound (i : SortedIx) (h : ¬Bound.le i.1 i.2) :
    SortedSyntax i ≃ᵢ Fin 1 :=
  GeneratedCode.shapeFinIso SortedGeneratedCode SortedGeneratedShapeCode i (by
    cases i with
    | mk lower upper =>
        cases upper with
        | none => exact False.elim (h trivial)
        | some upper =>
            change SortedShape (lower, some upper) = CodeShape.finite 1
            dsimp [SortedShape, Bound.le] at h ⊢
            rw [if_neg h])

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
