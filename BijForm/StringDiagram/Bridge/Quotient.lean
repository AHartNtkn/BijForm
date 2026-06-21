import BijForm.StringDiagram.Bridge.RenderRelation

namespace BijForm
namespace StringDiagram

open DepPoly

/-- Typed open boundary-connected port-hypergraphs quotiented by ordered
boundary-preserving isomorphism. -/
def OpenPortHypergraphUpToIso (Sig : Signature) (boundary : List Sig.Port) :
    Type :=
  Quotient (OpenPortHypergraph.isoSetoid Sig boundary)

/--
The owned graph-to-`Diag` traversal is invariant under
ordered-boundary-preserving isomorphism.  This is the well-definedness
theorem for descending `OpenPortHypergraph.fromGraph` to
`OpenPortHypergraphUpToIso`.
-/
theorem OpenPortHypergraph.fromGraph_respects_iso
    {Sig : Signature} {boundary : List Sig.Port}
    {G H : OpenPortHypergraph Sig boundary}
    (h : OpenPortHypergraph.isoRel G H) :
    OpenPortHypergraph.fromGraph G = OpenPortHypergraph.fromGraph H := by
  rcases h with ⟨e⟩
  simpa [OpenPortHypergraph.fromGraph] using
    SearchState.toDiag_isoRelated e
      (SearchState.initial G) (SearchState.initial H)
      (SearchState.initial_isoRelated e)
      (SearchState.initial_frontierComplete G)
      (SearchState.initial_frontierComplete H)

/--
Inverse law: rendering a syntax diagram to a semantic graph and then running
the owned first-pending traversal recovers the original syntax exactly.
-/
theorem Diag.fromGraph_toOpenPortHypergraph
    {Sig : Signature} {boundary : List Sig.Port}
    (d : Diag Sig boundary) :
    OpenPortHypergraph.fromGraph (Diag.toOpenPortHypergraph d) = d := by
  let hv := renderTraceFromBoundary_validIds d
  let hp := renderTraceFromBoundary_endpointPartition d
  let hn := renderTraceFromBoundary_nodeIncidentNodup d
  let pref := renderTraceFromBoundary_endpointPrefix d
  let ho := renderTraceFromBoundary_ownerIdPartition d
  let hall := renderTraceFromBoundary_allConstructorsReachBoundary d
  let ev := RenderState.openEvidenceOfInvariants hv hp hn pref ho hall
  have hrel :
      OpenPortHypergraph.SearchState.RenderPrefixRelated ev
        (RenderState.initial Sig boundary)
        (OpenPortHypergraph.SearchState.initial ev.toOpenPortHypergraph) := by
    simpa [ev, RenderState.openEvidenceOfInvariants,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      Diag.toOpenPortHypergraph] using
      OpenPortHypergraph.SearchState.initial_renderPrefixRelated d
  have hcomplete :
      (OpenPortHypergraph.SearchState.initial ev.toOpenPortHypergraph).FrontierComplete :=
    OpenPortHypergraph.SearchState.initial_frontierComplete ev.toOpenPortHypergraph
  have hreplay :=
    Diag.toDiag_of_renderPrefixRelated d (RenderState.initial Sig boundary)
      (RenderState.initial_validIds boundary)
      (RenderState.initial_endpointPartition boundary)
      (RenderState.initial_nodeIncidentNodup boundary)
      ({ suffix := []
         endpoints_eq := by simp [RenderState.initial] } :
        (RenderState.initial Sig boundary).EndpointPrefix boundary)
      (RenderState.initial_ownerIdPartition boundary)
      (RenderState.initial_reachability boundary)
      hv hp hn pref ho hall
      (OpenPortHypergraph.SearchState.initial ev.toOpenPortHypergraph)
      hrel hcomplete
  simpa [OpenPortHypergraph.fromGraph, Diag.toOpenPortHypergraph, ev,
    RenderState.openEvidenceOfInvariants, renderTraceFromBoundary_openEvidence,
    renderTraceFromBoundary_graphEvidence] using hreplay

/--
Inverse law: traversing an open graph to syntax and rendering that syntax
gives an ordered-boundary-preserving isomorphic semantic graph.
-/
theorem OpenPortHypergraph.toOpenPortHypergraph_fromGraph_iso
    {Sig : Signature} {boundary : List Sig.Port}
    (G : OpenPortHypergraph Sig boundary) :
    OpenPortHypergraph.isoRel
      (Diag.toOpenPortHypergraph (OpenPortHypergraph.fromGraph G)) G := by
  let d := OpenPortHypergraph.fromGraph G
  let hcomplete :=
    OpenPortHypergraph.SearchState.initial_frontierComplete G
  let rst0 := RenderState.initial Sig boundary
  have htrace :=
    OpenPortHypergraph.SearchState.GraphRenderRelated.toDiag
      (OpenPortHypergraph.SearchState.initial G)
      hcomplete
      rst0
      (RenderState.initial_validIds boundary)
      (OpenPortHypergraph.SearchState.initial_graphRenderRelated G)
  rcases htrace with ⟨finalSt, hfinal, hrelFinal⟩
  let hv := Diag.renderTraceFromBoundary_validIds d
  let hp := Diag.renderTraceFromBoundary_endpointPartition d
  let hn := Diag.renderTraceFromBoundary_nodeIncidentNodup d
  let pref := Diag.renderTraceFromBoundary_endpointPrefix d
  let ho := Diag.renderTraceFromBoundary_ownerIdPartition d
  let hall := Diag.renderTraceFromBoundary_allConstructorsReachBoundary d
  have hexhausted : finalSt.GraphExhausted :=
    finalSt.graphExhausted_of_empty_frontier hfinal
  refine ⟨?_⟩
  simpa [d, OpenPortHypergraph.fromGraph, Diag.toOpenPortHypergraph,
    Diag.renderTraceFromBoundary, Diag.renderTraceFromBoundary_openEvidence,
    Diag.renderTraceFromBoundary_graphEvidence,
    RenderState.openEvidenceOfInvariants] using
    OpenPortHypergraph.SearchState.GraphRenderRelated.toPortHypergraphIso
      hv hp hn pref ho hall hrelFinal hexhausted

/--
Semantic bridge assembly between traversal syntax and open port-hypergraphs up
to ordered-boundary-preserving isomorphism.
-/
def diagOpenPortHypergraphIso (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary where
  toFun d :=
    Quotient.mk (OpenPortHypergraph.isoSetoid Sig boundary)
      (Diag.toOpenPortHypergraph d)
  invFun :=
    Quotient.lift
      (fun G : OpenPortHypergraph Sig boundary => OpenPortHypergraph.fromGraph G)
      (by
        intro G H h
        exact OpenPortHypergraph.fromGraph_respects_iso h)
  left_inv := by
    intro d
    exact Diag.fromGraph_toOpenPortHypergraph d
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro G
    exact Quotient.sound
      (OpenPortHypergraph.toOpenPortHypergraph_fromGraph_iso G)

end StringDiagram
end BijForm
