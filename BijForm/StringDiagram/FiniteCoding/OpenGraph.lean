import BijForm.StringDiagram.FiniteCoding.Syntax
import BijForm.StringDiagram.Bridge

namespace BijForm
namespace StringDiagram

open DepPoly

/-- Open graphs for any frontier inherit the generated syntax shape carrier. -/
def singleSortedFiniteOpenGraphShapeIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (boundary : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig boundary ≃ᵢ
      (openFrontierShape Sig boundary).Carrier :=
  Iso.trans (Iso.symm (diagOpenPortHypergraphIso Sig boundary))
    (singleSortedFiniteSyntaxShapeIso Sig data boundary)

/-- Empty-frontier open graphs inherit the singleton finite syntax carrier. -/
def singleSortedFiniteOpenGraphEmptyFinOneIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    OpenPortHypergraphUpToIso Sig [] ≃ᵢ Fin 1 :=
  Iso.trans (singleSortedFiniteOpenGraphShapeIso Sig data [])
    (CodeShape.finiteIso rfl)

/-- Nonempty-frontier open graphs inherit the natural-number syntax carrier. -/
def singleSortedFiniteOpenGraphNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig (active :: frontier) ≃ᵢ Nat :=
  Iso.trans (singleSortedFiniteOpenGraphShapeIso Sig data (active :: frontier))
    (CodeShape.infiniteIso rfl)

end StringDiagram
end BijForm
