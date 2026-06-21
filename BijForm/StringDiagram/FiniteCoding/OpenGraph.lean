import BijForm.StringDiagram.FiniteCoding.Syntax
import BijForm.StringDiagram.Bridge

namespace BijForm
namespace StringDiagram

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
