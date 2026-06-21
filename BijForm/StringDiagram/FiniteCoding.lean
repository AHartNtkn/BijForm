import BijForm.StringDiagram.Polynomial
import BijForm.StringDiagram.Bridge

namespace BijForm
namespace StringDiagram

open DepPoly

/--
Finite/infinite carrier shape for open frontier diagrams: the empty frontier has
only `finish`, while each nonempty frontier is assigned a natural-number code.
-/
def openFrontierShape (Sig : Signature) :
    List Sig.Port → CodeShape
  | [] => .finite 1
  | _ :: _ => .infinite

/--
Reusable data for finite single-sorted string-diagram coding.

The data records the signature-level facts needed by the generic finite
frontier compiler. `compatibleAll` captures the single-sorted condition:
every open frontier port can connect to every constructor/frontier port. The
counts expose the finite branch tables used by the generic compiler rather than
letting examples define private branch encoders.
-/
structure SingleSortedFiniteCodingData (Sig : Signature) where
  compatibleAll : ∀ left right : Sig.Port, Sig.compatible left right
  nodeCount : Nat
  nodeCount_pos : 0 < nodeCount
  entryCount : Nat
  entryCount_pos : 0 < entryCount
  recursiveEntryCount : Nat
  recursiveEntryCount_pos : 0 < recursiveEntryCount

/--
Generic generated shape-code target for finite single-sorted string diagrams.

Unfinished: the statement is intentionally located at the generic string-diagram
coding boundary. The missing proof is the reusable finite branch-table compiler:
it must build the one-step layer isomorphism and rank descent from
`SingleSortedFiniteCodingData`, rather than from any example-local branch table.
-/
def singleSortedFiniteGeneratedShapeCode
    (Sig : Signature) (_data : SingleSortedFiniteCodingData Sig) :
    GeneratedShapeCode (poly Sig) where
  shape := openFrontierShape Sig
  inversion := inversion Sig
  layer := by
    intro boundary
    -- Unfinished: generic finite single-sorted layer presentation.
    sorry
  rank
    | [], _ => 0
    | _ :: _, n => n
  child_rank_lt := by
    -- Unfinished: generic rank descent for the finite single-sorted compiler.
    intro boundary z q
    sorry

/-- Generated-code equivalence for finite single-sorted string-diagram syntax. -/
def singleSortedFiniteSyntaxIso
    (Sig : Signature) (_data : SingleSortedFiniteCodingData Sig)
    (boundary : List Sig.Port) :
    Mu (poly Sig) boundary ≃ᵢ Diag Sig boundary :=
  syntaxIso Sig boundary

/-- Empty-frontier syntax is generated as the singleton finite carrier. -/
def singleSortedFiniteSyntaxEmptyFinOneIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    Diag Sig [] ≃ᵢ Fin 1 :=
  GeneratedCode.shapeFinIso
    (generatedCode Sig)
    (singleSortedFiniteGeneratedShapeCode Sig data)
    [] rfl

/-- Nonempty-frontier syntax is generated as a natural-number carrier. -/
def singleSortedFiniteSyntaxNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    Diag Sig (active :: frontier) ≃ᵢ Nat :=
  GeneratedCode.shapeNatIso
    (generatedCode Sig)
    (singleSortedFiniteGeneratedShapeCode Sig data)
    (active :: frontier) rfl

/-- Empty-frontier open graphs inherit the singleton finite syntax carrier. -/
def singleSortedFiniteOpenGraphEmptyFinOneIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    OpenPortHypergraphUpToIso Sig [] ≃ᵢ Fin 1 :=
  Iso.trans (Iso.symm (diagOpenPortHypergraphIso Sig []))
    (singleSortedFiniteSyntaxEmptyFinOneIso Sig data)

/-- Nonempty-frontier open graphs inherit the natural-number syntax carrier. -/
def singleSortedFiniteOpenGraphNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig (active :: frontier) ≃ᵢ Nat :=
  Iso.trans (Iso.symm (diagOpenPortHypergraphIso Sig (active :: frontier)))
    (singleSortedFiniteSyntaxNonemptyNatIso Sig data active frontier)

end StringDiagram
end BijForm
