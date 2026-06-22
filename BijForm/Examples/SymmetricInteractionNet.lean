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

private abbrev SINEntry :=
  SymmetricInteractionNetSignature.Entry

private def SINEntry.decidableEq : DecidableEq SINEntry
  | ⟨.dup, left⟩, ⟨.dup, right⟩ =>
      if h : left = right then isTrue (by cases h; rfl)
      else isFalse (by intro heq; cases heq; exact h rfl)
  | ⟨.dup, _⟩, ⟨.erase, _⟩ => isFalse (by intro h; cases h)
  | ⟨.dup, _⟩, ⟨.cons, _⟩ => isFalse (by intro h; cases h)
  | ⟨.erase, _⟩, ⟨.dup, _⟩ => isFalse (by intro h; cases h)
  | ⟨.erase, left⟩, ⟨.erase, right⟩ =>
      if h : left = right then isTrue (by cases h; rfl)
      else isFalse (by intro heq; cases heq; exact h rfl)
  | ⟨.erase, _⟩, ⟨.cons, _⟩ => isFalse (by intro h; cases h)
  | ⟨.cons, _⟩, ⟨.dup, _⟩ => isFalse (by intro h; cases h)
  | ⟨.cons, _⟩, ⟨.erase, _⟩ => isFalse (by intro h; cases h)
  | ⟨.cons, left⟩, ⟨.cons, right⟩ =>
      if h : left = right then isTrue (by cases h; rfl)
      else isFalse (by intro heq; cases heq; exact h rfl)

private instance : DecidableEq SINEntry := SINEntry.decidableEq
private def SINUnaryEntries : List SINEntry := [⟨SymmetricInteractionNetNode.erase, ⟨0, by decide⟩⟩]
private def SINNonUnaryEntries : List SINEntry :=
  [⟨SymmetricInteractionNetNode.dup, ⟨0, by decide⟩⟩,
   ⟨SymmetricInteractionNetNode.dup, ⟨1, by decide⟩⟩, ⟨SymmetricInteractionNetNode.dup, ⟨2, by decide⟩⟩,
   ⟨SymmetricInteractionNetNode.cons, ⟨0, by decide⟩⟩,
   ⟨SymmetricInteractionNetNode.cons, ⟨1, by decide⟩⟩, ⟨SymmetricInteractionNetNode.cons, ⟨2, by decide⟩⟩]

private def SINUnaryEntryTable : FiniteSubtypeTable SINEntry
    (fun entry => SymmetricInteractionNetSignature.arity entry.1 = 1) where
  values := SINUnaryEntries
  nodup := by decide
  sound := by
    intro i
    cases i with
    | mk val hval =>
        have hval0 : val = 0 := by
          simp [SINUnaryEntries] at hval
          omega
        subst val
        rfl
  complete := by
    intro entry h
    cases entry with
    | mk node slot =>
        cases node with
        | dup =>
            change SymmetricInteractionNetArity SymmetricInteractionNetNode.dup = 1 at h
            simp [SymmetricInteractionNetArity] at h
        | erase =>
            cases slot with
            | mk val hval =>
                have hval0 : val = 0 := by
                  change val < SymmetricInteractionNetArity SymmetricInteractionNetNode.erase at hval
                  simp [SymmetricInteractionNetArity] at hval
                  omega
                subst val
                exact ⟨⟨0, by decide⟩, rfl⟩
        | cons =>
            change SymmetricInteractionNetArity SymmetricInteractionNetNode.cons = 1 at h
            simp [SymmetricInteractionNetArity] at h

private def SINNonUnaryEntryTable : FiniteSubtypeTable SINEntry
    (fun entry => SymmetricInteractionNetSignature.arity entry.1 ≠ 1) where
  values := SINNonUnaryEntries
  nodup := by decide
  sound := by
    intro i
    cases i with
    | mk val hval =>
        have hcases :
            val = 0 ∨ val = 1 ∨ val = 2 ∨ val = 3 ∨ val = 4 ∨ val = 5 := by
          simp [SINNonUnaryEntries] at hval
          omega
        rcases hcases with h | h | h | h | h | h
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.dup ≠ 1
          decide
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.dup ≠ 1
          decide
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.dup ≠ 1
          decide
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.cons ≠ 1
          decide
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.cons ≠ 1
          decide
        · subst val
          change SymmetricInteractionNetArity SymmetricInteractionNetNode.cons ≠ 1
          decide
  complete := by
    intro entry h
    cases entry with
    | mk node slot =>
        cases node with
        | dup =>
            cases slot with
            | mk val hval =>
                if hval0 : val = 0 then
                  subst val
                  exact ⟨⟨0, by decide⟩, rfl⟩
                else if hval1 : val = 1 then
                  subst val
                  exact ⟨⟨1, by decide⟩, rfl⟩
                else
                  have hval2 : val = 2 := by
                    change val < SymmetricInteractionNetArity SymmetricInteractionNetNode.dup at hval
                    simp [SymmetricInteractionNetArity] at hval
                    omega
                  subst val
                  exact ⟨⟨2, by decide⟩, rfl⟩
        | erase =>
            exact False.elim (h rfl)
        | cons =>
            cases slot with
            | mk val hval =>
                if hval0 : val = 0 then
                  subst val
                  exact ⟨⟨3, by decide⟩, rfl⟩
                else if hval1 : val = 1 then
                  subst val
                  exact ⟨⟨4, by decide⟩, rfl⟩
                else
                  have hval2 : val = 2 := by
                    change val < SymmetricInteractionNetArity SymmetricInteractionNetNode.cons at hval
                    simp [SymmetricInteractionNetArity] at hval
                    omega
                  subst val
                  exact ⟨⟨5, by decide⟩, rfl⟩

/-- Finite single-sorted coding data for the SIN signature. -/
def SymmetricInteractionNetCodingData :
    SingleSortedFiniteCodingData SymmetricInteractionNetSignature where
  compatibleAll := by
    intro left right
    cases left
    cases right
    rfl
  rankScale := 4
  arity_lt_rankScale := by
    intro node
    cases node <;> decide
  unaryCount := SINUnaryEntryTable.values.length
  unaryCount_pos := by decide
  unaryIso := SINUnaryEntryTable.iso
  nonUnaryCount := SINNonUnaryEntryTable.values.length
  nonUnaryCount_pos := by decide
  nonUnaryIso := SINNonUnaryEntryTable.iso

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
  BijForm.StringDiagram.syntaxIso SymmetricInteractionNetSignature boundary

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
