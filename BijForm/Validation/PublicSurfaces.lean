import BijForm.Examples

namespace BijForm
namespace Validation

open DepPoly
open Examples

example : HBTInversion = OutputIndexInversion.canonical HBTPoly := rfl
example : NumInversion = OutputIndexInversion.canonical NumPoly := rfl
example : LamInversion = OutputIndexInversion.canonical LamPoly := rfl
example : FinChainInversion = OutputIndexInversion.canonical FinChainPoly := rfl
example : SortedInversion = OutputIndexInversion.canonical SortedPoly := rfl
example : PeanoInversion = OutputIndexInversion.canonical PeanoPoly := rfl
example :
    SymmetricInteractionNetInversion =
      StringDiagram.inversion SymmetricInteractionNetSignature :=
  rfl
example :
    Examples.TypedBinding.NFInversion =
      BijForm.TypedBinding.inversion Examples.TypedBinding.NFSignature :=
  rfl

example : GeneratedCode HBTPoly HBTSyntax := HBTGeneratedCode
example : GeneratedNatCode HBTPoly := HBTNatGeneratedCode
example (i : Nat) : HBTSyntax i ≃ᵢ Nat := HBTSyntaxNatIso i

example : GeneratedCode NumPoly NumSyntax := NumGeneratedCode
example : GeneratedNatCode NumPoly := NumNatGeneratedCode
example (k : Nat) : NumSyntax k ≃ᵢ Nat := NumSyntaxNatIso k

example : GeneratedCode PeanoPoly PeanoSyntax := PeanoGeneratedCode
example : GeneratedNatCode PeanoPoly := PeanoNatGeneratedCode
example (k : Nat) : PeanoSyntax k ≃ᵢ Nat := PeanoSyntaxNatIso k

example : GeneratedCode LamPoly LamSyntax := LamGeneratedCode
example : GeneratedRankedNatCode LamPoly := LamNatGeneratedCode
example (k : Nat) : LamSyntax k ≃ᵢ Nat := LamSyntaxNatIso k
example : LamSyntax 0 ≃ᵢ Nat := ClosedLamSyntaxNatIso

example : GeneratedCode FinChainPoly FinChainSyntax := FinChainGeneratedCode
example : GeneratedShapeCode FinChainPoly := FinChainGeneratedShapeCode
example (i : Nat) : FinChainSyntax i ≃ᵢ Fin (FinChainSize i) :=
  FinChainSyntaxFinIso i

example : GeneratedCode SortedPoly SortedSyntax := SortedGeneratedCode
example : GeneratedShapeCode SortedPoly := SortedGeneratedShapeCode
example (i : SortedIx) : SortedSyntax i ≃ᵢ SortedCarrier i :=
  SortedSyntaxShapeIso i
example (i : SortedIx) (h : Bound.le i.1 i.2) : SortedSyntax i ≃ᵢ Nat :=
  SortedSyntaxNatIsoOfBound i h
example (i : SortedIx) (h : ¬Bound.le i.1 i.2) :
    SortedSyntax i ≃ᵢ Fin 1 :=
  SortedSyntaxFinOneIsoOfNotBound i h

example : QuotientPresentation HBTPoly := HBTChildSwapQuotient
example {m : Nat} (lhs rhs : Mu HBTPoly m) :
    HBTChildSwapQuotient.innRaw (HBTRawBranchObj lhs rhs) =
      HBTChildSwapQuotient.innRaw (HBTRawBranchObj rhs lhs) :=
  HBTChildSwap_innRaw_branch_sound lhs rhs
example (i : Nat) : HBTChildSwap i ≃ᵢ Nat :=
  HBTChildSwapNatIso i
example (i : Nat) : HBTSyntaxChildSwap i ≃ᵢ Nat :=
  HBTSyntaxChildSwapNatIso i

example :
    StringDiagram.SingleSortedFiniteCodingData
      SymmetricInteractionNetSignature :=
  SymmetricInteractionNetCodingData
example :
    GeneratedShapeCode SymmetricInteractionNetPoly :=
  SymmetricInteractionNetGeneratedShapeCode
example : SymmetricInteractionNetDiag [] ≃ᵢ Fin 1 :=
  SymmetricInteractionNetSyntaxEmptyFinOneIso
example
    (active : SymmetricInteractionNetSignature.Port)
    (frontier : List SymmetricInteractionNetSignature.Port) :
    SymmetricInteractionNetDiag (active :: frontier) ≃ᵢ Nat :=
  SymmetricInteractionNetSyntaxNonemptyNatIso active frontier
example : SymmetricInteractionNetOpenGraphQuotient [] ≃ᵢ Fin 1 :=
  SymmetricInteractionNetOpenGraphEmptyFinOneIso
example
    (active : SymmetricInteractionNetSignature.Port)
    (frontier : List SymmetricInteractionNetSignature.Port) :
    SymmetricInteractionNetOpenGraphQuotient (active :: frontier) ≃ᵢ Nat :=
  SymmetricInteractionNetOpenGraphNonemptyNatIso active frontier

example :
    BijForm.TypedBinding.LayerShapeCodingData
      Examples.TypedBinding.NFSignature :=
  Examples.TypedBinding.NFLayerShapeCodingData
example (Γ : List Examples.TypedBinding.NFSort)
    (t : Examples.TypedBinding.NFSort) :
    Examples.TypedBinding.NFTerm Γ t ≃ᵢ
      Examples.TypedBinding.NFCode (Γ, t) :=
  Examples.TypedBinding.NFSyntaxCodeIso Γ t
example (Γ : List Examples.TypedBinding.NFSort) :
    Examples.TypedBinding.NormalExp Γ ≃ᵢ Nat :=
  Examples.TypedBinding.NormalExpNatIso Γ
example (Γ : List Examples.TypedBinding.NFSort) :
    Examples.TypedBinding.AppTerm Γ ≃ᵢ
      (Fin (Examples.TypedBinding.appTermCount Γ) × Nat) :=
  Examples.TypedBinding.AppTermCodeIso Γ
example : Examples.TypedBinding.NFClosed ≃ᵢ Nat :=
  Examples.TypedBinding.NFClosedNatIso
example : Examples.TypedBinding.AppTerm [] ≃ᵢ Empty :=
  Examples.TypedBinding.ClosedAppTermEmptyIso

end Validation
end BijForm
