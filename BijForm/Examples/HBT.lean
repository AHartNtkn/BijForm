import BijForm.RankDescent

namespace BijForm
namespace Examples

open DepPoly


/-- Reference syntax family for height-bounded trees: leaves may appear at any
height, while branches increase the height bound by one. -/
inductive HBTSyntax : Nat → Type
  | leaf {i : Nat} (label : Nat) : HBTSyntax i
  | branch {m : Nat} : HBTSyntax m → HBTSyntax m → HBTSyntax (m + 1)

namespace HBTSyntax

@[simp]
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

/-- The non-opaque output-index inversion for the height-bounded-tree example. -/
def HBTInversion : OutputIndexInversion HBTPoly :=
  OutputIndexInversion.canonical HBTPoly

/-- The fiber of branch constructors at height zero is empty. -/
theorem no_zero_height_branch (f : Fiber HBTPoly 0) (hctor : f.ctor = .branch) :
    False := by
  cases f with
  | mk ctor param out_eq =>
    cases hctor
    cases out_eq

/-- The fiber of branch constructors at `m+1` contains the predecessor `m`. -/
def branchAtSucc (m : Nat) : Fiber HBTPoly (m + 1) :=
  ⟨HBTCtor.branch, (m : Nat), rfl⟩

def HBTLayerToSyntax (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i → HBTSyntax i
  | ⟨⟨.leaf, p, h⟩, _child⟩ => by
      cases p with
      | mk height label =>
        cases h
        exact .leaf label
  | ⟨⟨.branch, m, h⟩, child⟩ => by
      cases h
      exact .branch (child false) (child true)

def HBTSyntaxToLayer (i : Nat) :
    HBTSyntax i → CodeLayer HBTPoly HBTInversion HBTSyntax i
  | .leaf label =>
      ⟨⟨HBTCtor.leaf, ((i, label) : Nat × Nat), rfl⟩, fun q => nomatch q⟩
  | @HBTSyntax.branch m lhs rhs =>
      ⟨⟨HBTCtor.branch, (m : Nat), rfl⟩, fun
        | false => lhs
        | true => rhs⟩

theorem HBT_layer_child_rank_lt :
    ∀ {i : Nat} (z : HBTSyntax i)
        (q : HBTPoly.Pos
          (HBTInversion.decode i (HBTSyntaxToLayer i z).1).ctor
          (HBTInversion.decode i (HBTSyntaxToLayer i z).1).param),
      HBTSyntax.rank ((HBTSyntaxToLayer i z).2 q) <
        HBTSyntax.rank z := by
  finish_rank_descent

/--
Generated coding data for height-bounded trees. The example supplies only
the local layer coding over `HBTInversion`; the full object-layer step is
produced by the generated-code construction.
-/
def HBTSyntaxPresentation : SyntaxPresentation HBTPoly HBTInversion HBTSyntax :=
  SyntaxPresentation.ofLayerIso
    (fun i =>
      { toFun := HBTLayerToSyntax i
        invFun := HBTSyntaxToLayer i
        left_inv :=
          CodeLayer.canonical_left_inv_by_fiber
            (toCarrier := HBTLayerToSyntax)
            (fromCarrier := HBTSyntaxToLayer) (by
              intro i ctor param out_eq child
              cases ctor with
              | leaf =>
                  cases param with
                  | mk height label =>
                    finish_code_layer_left_inv out_eq child
              | branch =>
                  finish_code_layer_left_inv out_eq child) i
        right_inv := by
          intro t
          cases t <;> simp [HBTLayerToSyntax, HBTSyntaxToLayer] })
    (fun _ t => HBTSyntax.rank t)
    HBT_layer_child_rank_lt

def HBTGeneratedCode : GeneratedCode HBTPoly HBTSyntax :=
  HBTSyntaxPresentation.generatedCode

/-- Height-bounded trees as the generic initial algebra are bijective with
readable syntax through generated layer coding. -/
def HBTSyntaxIso (i : Nat) : Mu HBTPoly i ≃ᵢ HBTSyntax i :=
  HBTGeneratedCode.iso i

def HBTNatLayerShape : Nat → Type
  | 0 => Nat
  | _ + 1 => Nat ⊕ (Nat × Nat)

def HBTNatLayerCarrierIso : ∀ i, HBTNatLayerShape i ≃ᵢ Nat
  | 0 => Iso.refl Nat
  | _ + 1 => CodeAlgebra.sumProdNat

def HBTNatLayerShapeLayerPresentation :
    CodeLayerPresentation HBTPoly HBTInversion (fun _ => Nat) HBTNatLayerShape :=
  CodeLayerPresentation.ofMaps
    (fun
      | 0, ⟨⟨.leaf, p, h⟩, _child⟩ => by
          cases p with
          | mk height label =>
            cases h
            exact label
      | 0, ⟨⟨.branch, m, h⟩, _child⟩ => by cases h
      | m + 1, ⟨⟨.leaf, p, h⟩, _child⟩ => by
          cases p with
          | mk height label =>
            cases h
            exact Sum.inl label
      | m + 1, ⟨⟨.branch, _k, _h⟩, child⟩ =>
          Sum.inr (child false, child true))
    (fun
      | 0, n =>
          ⟨⟨HBTCtor.leaf, ((0, n) : Nat × Nat), rfl⟩, fun q => nomatch q⟩
      | m + 1, shape =>
          match shape with
          | Sum.inl label =>
              ⟨⟨HBTCtor.leaf, ((m + 1, label) : Nat × Nat), rfl⟩,
                fun q => nomatch q⟩
          | Sum.inr p => ⟨⟨HBTCtor.branch, (m : Nat), rfl⟩, fun
              | false => p.1
              | true => p.2⟩)
    (CodeLayer.canonical_left_inv_by_fiber (by
      intro i ctor param out_eq child
      cases i with
      | zero =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                finish_code_layer_left_inv out_eq child
          | branch => cases out_eq
      | succ m =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                finish_code_layer_left_inv out_eq child
          | branch =>
              finish_code_layer_left_inv out_eq child))
    (by
      intro i shape
      cases i with
      | zero =>
          rfl
      | succ m =>
          cases shape with
          | inl label => rfl
          | inr p =>
              cases p
              rfl)

def HBTNatLayerPresentation : NatLayerPresentation HBTPoly HBTInversion :=
  LayerPresentation.ofShapeChildRank
    HBTNatLayerShapeLayerPresentation
    HBTNatLayerCarrierIso
    (fun _ n => n)
    (by
    finish_rank_descent [HBTNatLayerShape, HBTNatLayerShapeLayerPresentation,
      HBTNatLayerCarrierIso])

/-- Generated Nat coding data for height-bounded trees. The recursive encoder
and decoder are produced by `GeneratedNatCode`, not by an example-specific
recursive function. -/
def HBTNatGeneratedCode : GeneratedNatCode HBTPoly :=
  LayerPresentation.generatedCode HBTNatLayerPresentation

def HBTNatIso (i : Nat) : Mu HBTPoly i ≃ᵢ Nat :=
  HBTNatGeneratedCode.iso i

def HBTSyntaxNatIso (i : Nat) : HBTSyntax i ≃ᵢ Nat :=
  GeneratedCode.codeIso HBTGeneratedCode HBTNatGeneratedCode i

end Examples
end BijForm
