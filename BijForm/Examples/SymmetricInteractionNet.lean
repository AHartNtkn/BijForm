import BijForm.StringDiagram.FiniteCoding

namespace BijForm
namespace Examples

open DepPoly
open StringDiagram

/-- Node labels for the standard symmetric interaction-net signature. -/
inductive SymmetricInteractionNetNode where
  | dup
  | erase
  | cons
deriving DecidableEq, Repr

/-- All wires in the untyped symmetric interaction-net signature share one type. -/
abbrev SymmetricInteractionNetWire : Type := Unit

/-- Ordered arity of each symmetric interaction-net node. -/
def SymmetricInteractionNetArity : SymmetricInteractionNetNode → Nat
  | .dup => 3
  | .erase => 1
  | .cons => 3

/-- Every port in the untyped signature carries the unique wire type. -/
def SymmetricInteractionNetPort
    (node : SymmetricInteractionNetNode)
    (_slot : Fin (SymmetricInteractionNetArity node)) :
    SymmetricInteractionNetWire :=
  ()

/-- The standard untyped symmetric interaction-net string-diagram signature. -/
def SymmetricInteractionNetSignature : Signature :=
  Unoriented.signature
    SymmetricInteractionNetWire
    SymmetricInteractionNetNode
    SymmetricInteractionNetArity
    SymmetricInteractionNetPort

@[simp] theorem SymmetricInteractionNetSignature_arity_dup :
    SymmetricInteractionNetSignature.arity SymmetricInteractionNetNode.dup = 3 := rfl
@[simp] theorem SymmetricInteractionNetSignature_arity_erase :
    SymmetricInteractionNetSignature.arity SymmetricInteractionNetNode.erase = 1 := rfl
@[simp] theorem SymmetricInteractionNetSignature_arity_cons :
    SymmetricInteractionNetSignature.arity SymmetricInteractionNetNode.cons = 3 := rfl

private abbrev SINUnaryEntry :=
  SymmetricInteractionNetSignature.UnaryEntry

private abbrev SINNonUnaryEntry :=
  SymmetricInteractionNetSignature.NonUnaryEntry

private def SINUnaryEntryIso : SINUnaryEntry ≃ᵢ Fin 1 where
  toFun _ := ⟨0, by decide⟩
  invFun _ :=
    ⟨⟨SymmetricInteractionNetNode.erase, ⟨0, by decide⟩⟩, rfl⟩
  left_inv := by
    intro entry
    cases entry with
    | mk raw hraw =>
        apply Subtype.ext
        cases raw with
        | mk node slot =>
            cases node with
            | dup =>
                change SymmetricInteractionNetArity SymmetricInteractionNetNode.dup = 1 at hraw
                simp [SymmetricInteractionNetArity] at hraw
            | erase =>
                cases slot with
                | mk val hval =>
                    have hval0 : val = 0 := by
                      change val < SymmetricInteractionNetArity SymmetricInteractionNetNode.erase at hval
                      simp [SymmetricInteractionNetArity] at hval
                      omega
                    subst val
                    rfl
            | cons =>
                change SymmetricInteractionNetArity SymmetricInteractionNetNode.cons = 1 at hraw
                simp [SymmetricInteractionNetArity] at hraw
  right_inv := by
    intro tag
    apply Fin.ext
    omega

private def SINNonUnaryEntry.toFin6 : SINNonUnaryEntry → Fin 6
  | ⟨⟨.dup, entry⟩, _⟩ => ⟨entry.val, by
      have hentry : entry.val < 3 := by
        simp
      omega⟩
  | ⟨⟨.erase, _entry⟩, hnon⟩ => False.elim (hnon rfl)
  | ⟨⟨.cons, entry⟩, _⟩ => ⟨entry.val + 3, by
      have hentry : entry.val < 3 := by
        simp
      omega⟩

private def SINNonUnaryEntry.ofFin6 : Fin 6 → SINNonUnaryEntry
  | ⟨0, _⟩ => ⟨⟨.dup, ⟨0, by decide⟩⟩, by decide⟩
  | ⟨1, _⟩ => ⟨⟨.dup, ⟨1, by decide⟩⟩, by decide⟩
  | ⟨2, _⟩ => ⟨⟨.dup, ⟨2, by decide⟩⟩, by decide⟩
  | ⟨3, _⟩ => ⟨⟨.cons, ⟨0, by decide⟩⟩, by decide⟩
  | ⟨4, _⟩ => ⟨⟨.cons, ⟨1, by decide⟩⟩, by decide⟩
  | ⟨5, _⟩ => ⟨⟨.cons, ⟨2, by decide⟩⟩, by decide⟩
  | ⟨n + 6, h⟩ => False.elim (by omega)

private theorem SINNonUnaryEntry.toFin6_ofFin6 (tag : Fin 6) :
    SINNonUnaryEntry.toFin6 (SINNonUnaryEntry.ofFin6 tag) = tag := by
  cases tag with
  | mk val hval =>
      have hcases :
          val = 0 ∨ val = 1 ∨ val = 2 ∨ val = 3 ∨ val = 4 ∨ val = 5 := by
        omega
      rcases hcases with h | h | h | h | h | h <;>
        subst val <;>
        simp [SINNonUnaryEntry.toFin6, SINNonUnaryEntry.ofFin6]

private theorem SINNonUnaryEntry.toFin6_injective :
    Function.Injective SINNonUnaryEntry.toFin6 := by
  intro left right h
  apply Subtype.ext
  cases left with
  | mk leftRaw leftNon =>
      cases right with
      | mk rightRaw rightNon =>
          cases leftRaw with
          | mk leftNode leftEntry =>
              cases rightRaw with
              | mk rightNode rightEntry =>
                  cases leftNode with
                  | dup =>
                      cases rightNode with
                      | dup =>
                          refine Sigma.ext rfl ?_
                          apply heq_of_eq
                          apply Fin.ext
                          have hval := congrArg Fin.val h
                          simpa [SINNonUnaryEntry.toFin6] using hval
                      | erase => exact False.elim (rightNon rfl)
                      | cons =>
                          exfalso
                          have hval := congrArg Fin.val h
                          have hleft : leftEntry.val < 3 := by
                            simp
                          have hright : rightEntry.val < 3 := by
                            simp
                          simp [SINNonUnaryEntry.toFin6] at hval
                          omega
                  | erase => exact False.elim (leftNon rfl)
                  | cons =>
                      cases rightNode with
                      | dup =>
                          exfalso
                          have hval := congrArg Fin.val h
                          have hleft : leftEntry.val < 3 := by
                            simp
                          have hright : rightEntry.val < 3 := by
                            simp
                          simp [SINNonUnaryEntry.toFin6] at hval
                          omega
                      | erase => exact False.elim (rightNon rfl)
                      | cons =>
                          refine Sigma.ext rfl ?_
                          apply heq_of_eq
                          apply Fin.ext
                          have hval := congrArg Fin.val h
                          simp [SINNonUnaryEntry.toFin6] at hval
                          omega

private def SINNonUnaryEntryIso : SINNonUnaryEntry ≃ᵢ Fin 6 :=
  Iso.ofRightInverseInjective
    SINNonUnaryEntry.toFin6
    SINNonUnaryEntry.ofFin6
    SINNonUnaryEntry.toFin6_ofFin6
    SINNonUnaryEntry.toFin6_injective

/-- Finite single-sorted coding data for the SIN signature. -/
def SymmetricInteractionNetCodingData :
    SingleSortedFiniteCodingData SymmetricInteractionNetSignature where
  compatibleAll := by
    intro left right
    cases left
    cases right
    rfl
  arity_pos := by
    intro node
    cases node <;> decide
  rankScale := 4
  arity_lt_rankScale := by
    intro node
    cases node <;> decide
  unaryCount := 1
  unaryCount_pos := by decide
  unaryIso := SINUnaryEntryIso
  nonUnaryCount := 6
  nonUnaryCount_pos := by decide
  nonUnaryIso := SINNonUnaryEntryIso

/-- Ordered-frontier symmetric interaction-net traversal syntax. -/
abbrev SymmetricInteractionNetDiag
    (boundary : List SymmetricInteractionNetSignature.Port) : Type :=
  StringDiagram.Diag SymmetricInteractionNetSignature boundary

/-- Dependent polynomial generated by the symmetric interaction-net signature. -/
abbrev SymmetricInteractionNetPoly :
    DepPoly (List SymmetricInteractionNetSignature.Port) :=
  BijForm.StringDiagram.poly SymmetricInteractionNetSignature

/-- Same-fiber constructor data for the SIN traversal polynomial. -/
abbrev SymmetricInteractionNetInversion :
    OutputIndexInversion SymmetricInteractionNetPoly :=
  BijForm.StringDiagram.inversion SymmetricInteractionNetSignature

/-- Generated coding data for symmetric interaction-net diagrams. -/
abbrev SymmetricInteractionNetGeneratedCode :
    GeneratedCode SymmetricInteractionNetPoly
      (fun boundary => StringDiagram.Diag SymmetricInteractionNetSignature boundary) :=
  BijForm.StringDiagram.generatedCode SymmetricInteractionNetSignature

/-- Generated-code equivalence for symmetric interaction-net diagrams. -/
abbrev SymmetricInteractionNetSyntaxIso
    (boundary : List SymmetricInteractionNetSignature.Port) :
    Mu SymmetricInteractionNetPoly boundary ≃ᵢ
      SymmetricInteractionNetDiag boundary :=
  singleSortedFiniteSyntaxIso
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData
    boundary

/-- Semantic open port-hypergraphs over the symmetric interaction-net signature. -/
abbrev SymmetricInteractionNetOpenGraph
    (boundary : List SymmetricInteractionNetSignature.Port) : Type :=
  OpenPortHypergraph SymmetricInteractionNetSignature boundary

/-- Semantic open port-hypergraphs up to ordered-boundary-preserving isomorphism. -/
abbrev SymmetricInteractionNetOpenGraphQuotient
    (boundary : List SymmetricInteractionNetSignature.Port) : Type :=
  OpenPortHypergraphUpToIso SymmetricInteractionNetSignature boundary

/-- Encoding of symmetric interaction-net diagrams by semantic open graphs. -/
abbrev SymmetricInteractionNetOpenGraphIso
    (boundary : List SymmetricInteractionNetSignature.Port) :
    SymmetricInteractionNetDiag boundary ≃ᵢ
      SymmetricInteractionNetOpenGraphQuotient boundary :=
  diagOpenPortHypergraphIso SymmetricInteractionNetSignature boundary

/-- Generated finite/infinite carrier shape for symmetric interaction-net diagrams. -/
abbrev SymmetricInteractionNetShape :
    List SymmetricInteractionNetSignature.Port → CodeShape :=
  openFrontierShape SymmetricInteractionNetSignature

/-- Generated shape-code data for symmetric interaction-net diagrams. -/
abbrev SymmetricInteractionNetGeneratedShapeCode :
    GeneratedShapeCode SymmetricInteractionNetPoly :=
  singleSortedFiniteGeneratedShapeCode
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData

/-- Empty-frontier SIN traversal syntax is the singleton finite carrier. -/
def SymmetricInteractionNetSyntaxEmptyFinOneIso :
    SymmetricInteractionNetDiag [] ≃ᵢ Fin 1 :=
  singleSortedFiniteSyntaxEmptyFinOneIso
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData

/-- Nonempty-frontier SIN traversal syntax is a natural-number carrier. -/
def SymmetricInteractionNetSyntaxNonemptyNatIso
    (active : SymmetricInteractionNetSignature.Port)
    (frontier : List SymmetricInteractionNetSignature.Port) :
    SymmetricInteractionNetDiag (active :: frontier) ≃ᵢ Nat :=
  singleSortedFiniteSyntaxNonemptyNatIso
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData
    active
    frontier

/-- Empty-frontier SIN open graphs inherit the singleton syntax carrier. -/
def SymmetricInteractionNetOpenGraphEmptyFinOneIso :
    SymmetricInteractionNetOpenGraphQuotient [] ≃ᵢ Fin 1 :=
  singleSortedFiniteOpenGraphEmptyFinOneIso
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData

/-- Nonempty-frontier SIN open graphs inherit the natural-number syntax carrier. -/
def SymmetricInteractionNetOpenGraphNonemptyNatIso
    (active : SymmetricInteractionNetSignature.Port)
    (frontier : List SymmetricInteractionNetSignature.Port) :
    SymmetricInteractionNetOpenGraphQuotient (active :: frontier) ≃ᵢ Nat :=
  singleSortedFiniteOpenGraphNonemptyNatIso
    SymmetricInteractionNetSignature
    SymmetricInteractionNetCodingData
    active
    frontier

end Examples
end BijForm
