import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

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

def HBTSyntaxLayerPresentation :
    CodeLayerPresentation HBTPoly HBTInversion HBTSyntax HBTSyntax :=
  CodeLayerPresentation.ofMaps
    HBTLayerToSyntax
    HBTSyntaxToLayer
    (by
      intro i layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                cases out_eq
                have hchild : (fun q => nomatch q) = child := by
                  child_eta_empty
                cases hchild
                rfl
          | branch =>
              cases out_eq
              have hchild : child = (fun
                  | false => child false
                  | true => child true) := by
                child_eta_bool
              rw [hchild]
              rfl)
    (by
      intro i t
      cases t <;> simp [HBTLayerToSyntax, HBTSyntaxToLayer])

theorem HBT_layer_child_rank_lt :
    ∀ {i : Nat} (z : HBTSyntax i)
          (q : HBTPoly.Pos
          (HBTInversion.decode i ((HBTSyntaxLayerPresentation.iso i).invFun z).1).ctor
          (HBTInversion.decode i ((HBTSyntaxLayerPresentation.iso i).invFun z).1).param),
      HBTSyntax.rank (((HBTSyntaxLayerPresentation.iso i).invFun z).2 q) <
        HBTSyntax.rank z := by
  intro i z q
  cases z with
  | leaf label => cases q
  | branch lhs rhs =>
      cases q
      · simpa [CodeLayerPresentation.iso, HBTSyntaxLayerPresentation, HBTSyntaxToLayer,
          HBTInversion,
          OutputIndexInversion.canonical, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))
      · simpa [CodeLayerPresentation.iso, HBTSyntaxLayerPresentation, HBTSyntaxToLayer,
          HBTInversion,
          OutputIndexInversion.canonical, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))

/--
Generated coding data for height-bounded trees. The example supplies only
the local layer coding over `HBTInversion`; the full object-layer step is
produced by `GeneratedCode.toWellFoundedCode`.
-/
def HBTSyntaxPresentation : SyntaxPresentation HBTPoly HBTInversion HBTSyntax :=
  SyntaxPresentation.ofLayer
    HBTSyntaxLayerPresentation
    (fun _ t => HBTSyntax.rank t)
    HBT_layer_child_rank_lt

def HBTGeneratedCode : GeneratedCode HBTPoly HBTSyntax :=
  HBTSyntaxPresentation.generatedCode

def HBTWellFoundedCode : WellFoundedCode HBTPoly HBTSyntax :=
  HBTGeneratedCode.toWellFoundedCode

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
    (by
      intro i x
      cases i with
      | zero =>
          cases x with
          | mk code child =>
              cases code with
              | mk ctor param out_eq =>
                cases ctor with
                | leaf =>
                    cases param with
                    | mk height label =>
                      cases out_eq
                      have hchild : (fun q => nomatch q) = child := by
                        child_eta_empty
                      cases hchild
                      rfl
                | branch => cases out_eq
      | succ m =>
          cases x with
          | mk code child =>
              cases code with
              | mk ctor param out_eq =>
                cases ctor with
                | leaf =>
                    cases param with
                    | mk height label =>
                      cases out_eq
                      have hchild : (fun q => nomatch q) = child := by
                        child_eta_empty
                      cases hchild
                      rfl
                | branch =>
                    cases out_eq
                    have hchild : child = (fun
                        | false => child false
                        | true => child true) := by
                      child_eta_bool
                    rw [hchild]
                    rfl)
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

def HBTNatLayerShapePresentation :
    LayerShapePresentation HBTPoly HBTInversion (fun _ => Nat) HBTNatLayerShape :=
  LayerShapePresentation.ofComponents
    HBTNatLayerShapeLayerPresentation
    HBTNatLayerCarrierIso
    (fun _ n => n)
    (by
    intro i n
    cases i with
    | zero =>
        intro q
        cases q
    | succ m =>
        let layerIso :=
          (HBTNatLayerShapeLayerPresentation.transCarrier HBTNatLayerCarrierIso).iso (m + 1)
        change
          ∀ q : HBTPoly.Pos
            (HBTInversion.decode (m + 1) (layerIso.invFun n).1).ctor
            (HBTInversion.decode (m + 1) (layerIso.invFun n).1).param,
            (layerIso.invFun n).2 q < n
        dsimp [layerIso, CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
          HBTNatLayerCarrierIso, HBTNatLayerShapeLayerPresentation]
        generalize hsum : CodeAlgebra.sumProdNat.invFun n = s
        cases s with
        | inl label =>
            intro q
            cases q
        | inr pair =>
            intro q
            cases q
            · change pair.1 < n
              exact CodeAlgebra.sumProdNat_invFun_inr_fst_lt hsum
            · change pair.2 < n
              exact CodeAlgebra.sumProdNat_invFun_inr_snd_lt hsum)

def HBTNatLayerPresentation : NatLayerPresentation HBTPoly HBTInversion :=
  HBTNatLayerShapePresentation.toNatLayerPresentation (by
    intro i n q
    exact HBTNatLayerShapePresentation.child_rank_lt n q)

/-- Generated Nat coding data for height-bounded trees. The recursive encoder
and decoder are produced by `GeneratedNatCode`, not by an example-specific
recursive function. -/
def HBTNatGeneratedCode : GeneratedNatCode HBTPoly :=
  HBTNatLayerPresentation.generatedCode

def HBTNatIso (i : Nat) : Mu HBTPoly i ≃ᵢ Nat :=
  HBTNatGeneratedCode.iso i

def HBTSyntaxNatIso (i : Nat) : HBTSyntax i ≃ᵢ Nat :=
  GeneratedCode.natCodeIso HBTGeneratedCode HBTNatGeneratedCode i

end Examples
end BijForm
