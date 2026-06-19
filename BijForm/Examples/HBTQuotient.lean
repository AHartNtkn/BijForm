import BijForm.QuotientPolynomial
import BijForm.Examples.HBT

namespace BijForm
namespace Examples

open DepPoly

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

/-- Readable height-bounded syntax modulo branch-child swapping. -/
abbrev HBTSyntaxChildSwap (i : Nat) : Type :=
  Quot (HBTSyntaxSwapRel i)

/-- The readable syntax quotient is the generated quotient-polynomial carrier. -/
def HBTSyntaxChildSwapIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwap i where
  toFun :=
    Quot.lift
      (fun x => HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
      (by
        intro x y hxy
        exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
  invFun :=
    Quot.lift
      (fun x => Quot.mk (HBTSyntaxSwapRel i) ((HBTSyntaxIso i).toFun x))
      (by
        intro x y hxy
        apply Quot.sound
        dsimp [HBTSyntaxSwapRel]
        rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
        exact hxy)
  left_inv := by
    intro q
    exact Quot.ind (r := HBTSyntaxSwapRel i)
      (β := fun q => Quot.lift
        (fun x => Quot.mk (HBTSyntaxSwapRel i) ((HBTSyntaxIso i).toFun x))
        (by
          intro x y hxy
          apply Quot.sound
          dsimp [HBTSyntaxSwapRel]
          rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
          exact hxy)
        (Quot.lift
          (fun x => HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
          (by
            intro x y hxy
            exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
          q) = q)
      (fun x => by
        simp
        change Quot.mk (HBTSyntaxSwapRel i)
            ((HBTSyntaxIso i).toFun ((HBTSyntaxIso i).invFun x))
          = Quot.mk (HBTSyntaxSwapRel i) x
        rw [(HBTSyntaxIso i).right_inv x])
      q
  right_inv := by
    intro q
    exact Quot.ind (r := QuotientPresentation.Rel HBTChildSwapQuotient i)
      (β := fun q => Quot.lift
        (fun x => HBTChildSwapQuotient.ofMu ((HBTSyntaxIso i).invFun x))
        (by
          intro x y hxy
          exact QuotientPresentation.sound HBTChildSwapQuotient hxy)
        (Quot.lift
          (fun x => Quot.mk (HBTSyntaxSwapRel i) ((HBTSyntaxIso i).toFun x))
          (by
            intro x y hxy
            apply Quot.sound
            dsimp [HBTSyntaxSwapRel]
            rw [(HBTSyntaxIso i).left_inv x, (HBTSyntaxIso i).left_inv y]
            exact hxy)
          q) = q)
      (fun x => by
        simp [QuotientPresentation.ofMu])
      q

/-- Public encoding theorem for readable branch-swap quotient syntax. The code
carrier is the quotient of the generated Nat code by the transported
branch-swap relation; the encoder is not hand-written for this example. -/
def HBTSyntaxChildSwapNatCodeIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwapNatCode i :=
  Iso.trans (HBTSyntaxChildSwapIso i) (HBTChildSwapNatCodeIso i)

end Examples
end BijForm
