import BijForm.QuotientPolynomial
import BijForm.Examples.HBT

namespace BijForm
namespace Examples

open DepPoly

/-
Diagnostic quotient example: this file shows how a constructor-layer quotient
feeds the generic quotient-polynomial coding theorem. It deliberately leaves
the quotient code carrier as an indexed quotient of the generated Nat code;
it is not yet a completed concrete normal-form encoding to `Nat` or `Fin k`.
-/

/-- One-step quotient relation for height-bounded trees modulo swapping the
two children of a branch node. -/
inductive HBTSwapLayerRel :
    ∀ i, Obj HBTPoly (Mu HBTPoly) i → Obj HBTPoly (Mu HBTPoly) i → Prop
  | branch {m : Nat} (lhs rhs : Mu HBTPoly m) :
      HBTSwapLayerRel (m + 1)
        { ctor := .branch
          param := m
          out_eq := rfl
          child := fun
            | false => lhs
            | true => rhs }
        { ctor := .branch
          param := m
          out_eq := rfl
          child := fun
            | false => rhs
            | true => lhs }

/-- Quotient presentation for height-bounded trees where branch children are
unordered. -/
def HBTChildSwapQuotient : QuotientPresentation HBTPoly where
  LayerRel := HBTSwapLayerRel

/-- Height-bounded trees modulo branch-child swapping, generated from the
dependent-polynomial quotient presentation. -/
abbrev HBTChildSwap (i : Nat) : Type :=
  HBTChildSwapQuotient.Carrier i

/-- The quotient equates a branch with the same branch whose two children are
swapped. -/
theorem HBTChildSwap_branch_sound {m : Nat} (lhs rhs : Mu HBTPoly m) :
    HBTChildSwapQuotient.ofMu
        (Mu.sup (P := HBTPoly) .branch m rfl
          (fun
            | false => lhs
            | true => rhs))
      =
      HBTChildSwapQuotient.ofMu
        (Mu.sup (P := HBTPoly) .branch m rfl
          (fun
            | false => rhs
            | true => lhs)) := by
  apply QuotientPresentation.sound
  exact QuotientPresentation.Rel.layer (HBTSwapLayerRel.branch lhs rhs)

/-- Raw branch layer used to state constructor-surface quotient equations. -/
def HBTRawBranchObj {m : Nat} (lhs rhs : Mu HBTPoly m) :
    Obj HBTPoly (Mu HBTPoly) (m + 1) where
  ctor := HBTCtor.branch
  param := m
  out_eq := rfl
  child := fun
    | false => lhs
    | true => rhs

/-- The branch-swap layer relation is respected by the quotient constructor
from already-quotiented child layers. -/
theorem HBTChildSwap_inn_branch_sound {m : Nat} (lhs rhs : Mu HBTPoly m) :
    HBTChildSwapQuotient.inn
        (Obj.map (fun i => HBTChildSwapQuotient.ofMu (i := i))
          (HBTRawBranchObj lhs rhs))
      =
      HBTChildSwapQuotient.inn
        (Obj.map (fun i => HBTChildSwapQuotient.ofMu (i := i))
          (HBTRawBranchObj rhs lhs)) := by
  exact HBTChildSwapQuotient.inn_layer_sound
    (HBTSwapLayerRel.branch lhs rhs)

/-- The Nat-code relation induced by the branch-swap quotient and the existing
generated Nat coding for height-bounded trees. -/
abbrev HBTChildSwapNatCodeRel (i : Nat) (a b : Nat) : Prop :=
  HBTChildSwapQuotient.CodeRel HBTNatGeneratedCode.toWellFoundedCode i a b

/-- Canonical code carrier for branch-swap quotient trees: quotient the
generated Nat code by the transported branch-swap relation. -/
abbrev HBTChildSwapNatCode (i : Nat) : Type :=
  HBTChildSwapQuotient.CodeCarrier HBTNatGeneratedCode.toWellFoundedCode i

/-- The generic quotient-polynomial theorem specializes to a coding of
height-bounded branch-swap quotient trees by a quotient of the generated Nat
code. -/
def HBTChildSwapNatCodeIso (i : Nat) :
    HBTChildSwap i ≃ᵢ HBTChildSwapNatCode i :=
  HBTChildSwapQuotient.codeIso HBTNatGeneratedCode.toWellFoundedCode i

/-- Readable height-bounded syntax transported to the generated branch-swap
quotient relation through `HBTSyntaxIso`. -/
def HBTSyntaxSwapRel (i : Nat) (x y : HBTSyntax i) : Prop :=
  QuotientPresentation.Rel HBTChildSwapQuotient i
    ((HBTSyntaxIso i).invFun x) ((HBTSyntaxIso i).invFun y)

/-- The readable syntax branch-swap relation as an explicit setoid. -/
def HBTSyntaxSwapSetoid (i : Nat) : Setoid (HBTSyntax i) where
  r := HBTSyntaxSwapRel i
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact QuotientPresentation.Rel.refl ((HBTSyntaxIso i).invFun x)
    · intro x y hxy
      exact QuotientPresentation.Rel.symm hxy
    · intro x y z hxy hyz
      exact QuotientPresentation.Rel.trans hxy hyz

/-- Readable height-bounded syntax modulo branch-child swapping. -/
abbrev HBTSyntaxChildSwap (i : Nat) : Type :=
  Quotient (HBTSyntaxSwapSetoid i)

/-- The readable syntax quotient is the generated quotient-polynomial carrier. -/
def HBTSyntaxChildSwapIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwap i where
  toFun :=
    Quotient.lift
      (fun (x : HBTSyntax i) =>
        HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
      (by
        intro x y hxy
        exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
  invFun :=
    Quotient.lift
      (fun (x : Mu HBTPoly i) =>
        Quotient.mk (HBTSyntaxSwapSetoid i) ((HBTSyntaxIso i).toFun x))
      (by
        intro x y hxy
        apply Quotient.sound
        change QuotientPresentation.Rel HBTChildSwapQuotient i
          ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun x))
          ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun y))
        rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
        exact hxy)
  left_inv := by
    intro q
    exact Quotient.ind (s := HBTSyntaxSwapSetoid i)
      (motive := fun q => Quotient.lift
        (fun (x : Mu HBTPoly i) =>
          Quotient.mk (HBTSyntaxSwapSetoid i) ((HBTSyntaxIso i).toFun x))
        (by
          intro x y hxy
          apply Quotient.sound
          change QuotientPresentation.Rel HBTChildSwapQuotient i
            ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun x))
            ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun y))
          rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
          exact hxy)
        (Quotient.lift
          (fun (x : HBTSyntax i) =>
            HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
          (by
            intro x y hxy
            exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
          q) = q)
      (fun x => by
        simp
        change Quotient.mk (HBTSyntaxSwapSetoid i)
            ((HBTSyntaxIso i).toFun ((HBTSyntaxIso i).invFun x))
          = Quotient.mk (HBTSyntaxSwapSetoid i) x
        rw [(HBTSyntaxIso i).right_inv x])
      q
  right_inv := by
    intro q
    exact Quotient.ind (s := QuotientPresentation.setoid HBTChildSwapQuotient i)
      (motive := fun q => Quotient.lift
        (fun (x : HBTSyntax i) =>
          HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
        (by
          intro x y hxy
          exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
        (Quotient.lift
          (fun (x : Mu HBTPoly i) =>
            Quotient.mk (HBTSyntaxSwapSetoid i) ((HBTSyntaxIso i).toFun x))
          (by
            intro x y hxy
            apply Quotient.sound
            change QuotientPresentation.Rel HBTChildSwapQuotient i
              ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun x))
              ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun y))
            rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
            exact hxy)
          q) = q)
      (fun x => by
        change HBTChildSwapQuotient.ofMu
            ((HBTSyntaxIso i).invFun ((HBTSyntaxIso i).toFun x))
          = HBTChildSwapQuotient.ofMu x
        rw [(HBTSyntaxIso i).left_inv x])
      q

/-- Diagnostic public encoding theorem for readable branch-swap quotient
syntax. The code carrier is still the quotient of the generated Nat code by the
transported branch-swap relation; this is not a completed concrete Nat normal
form for unordered height-bounded trees. -/
def HBTSyntaxChildSwapNatCodeIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwapNatCode i :=
  Iso.trans (HBTSyntaxChildSwapIso i) (HBTChildSwapNatCodeIso i)

end Examples
end BijForm
