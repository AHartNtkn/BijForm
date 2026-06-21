import BijForm.StringDiagram.Hypergraph

namespace BijForm
namespace StringDiagram

open DepPoly

namespace OpenPortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/--
State for the boundary-rooted graph-to-syntax traversal.  The pending endpoint
list is ordered, and its labels are exactly the `Diag` frontier index.
-/
structure TraversalState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  seenNode : Fin G.raw.nodeCount → Prop
  processedEdge : Fin G.raw.edgeCount → Prop
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → ¬ processedEdge (G.raw.endpointEdge endpoint)

namespace TraversalState

/--
The completeness invariant missing from the current traversal proof.  Every
unprocessed boundary endpoint, and every unprocessed endpoint of an already
seen constructor, must occur in the ordered pending frontier.
-/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : TraversalState G frontier) : Prop :=
  ∀ endpoint : Fin G.raw.endpointCount,
    ¬ st.processedEdge (G.raw.endpointEdge endpoint) →
      ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length),
        PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
          match owner with
          | .boundary _ => endpoint ∈ st.pending
          | .constructor node _ => st.seenNode node → endpoint ∈ st.pending

end TraversalState

/--
Finite, data-carrying state for the owned graph-to-syntax search.

`TraversalState` is the proof-level invariant surface.  `SearchState` keeps the
same pending frontier together with finite lists of seen constructors and
processed edges, so a later traversal implementation can make constructor
choices as data and then project those choices back to the proof-level
invariants.
-/
structure SearchState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  pending_nodup : pending.Nodup
  seenNodes : List (Fin G.raw.nodeCount)
  processedEdges : List (Fin G.raw.edgeCount)
  processedEdges_nodup : processedEdges.Nodup
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → G.raw.endpointEdge endpoint ∉ processedEdges
  pending_owner_seen :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending →
        ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length),
          PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
            match owner with
            | .boundary _ => True
            | .constructor node _ => node ∈ seenNodes
  unseen_incident_unprocessed :
    ∀ node : Fin G.raw.nodeCount,
      node ∉ seenNodes →
        ∀ slot : Fin (G.raw.incident node).length,
          G.raw.endpointEdge ((G.raw.incident node).get slot) ∉ processedEdges

namespace SearchState

private theorem cast_pending {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).pending = st.pending := by
  cases h
  rfl

private theorem cast_seenNodes {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).seenNodes = st.seenNodes := by
  cases h
  rfl

private theorem cast_processedEdges {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).processedEdges = st.processedEdges := by
  cases h
  rfl

private theorem nodePortsExcept_eq_of_val
    {nodeA nodeB : Sig.Node}
    (hnode : nodeA = nodeB)
    {entryA : Fin (Sig.arity nodeA)} {entryB : Fin (Sig.arity nodeB)}
    (hval : entryA.val = entryB.val) :
    Sig.nodePortsExcept nodeA entryA =
      Sig.nodePortsExcept nodeB entryB := by
  cases hnode
  have hentry : entryA = entryB := Fin.ext hval
  cases hentry
  rfl

def seenNode {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (node : Fin G.raw.nodeCount) : Prop :=
  node ∈ st.seenNodes

def processedEdge {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (edge : Fin G.raw.edgeCount) : Prop :=
  edge ∈ st.processedEdges

theorem processedEdges_length_le {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    st.processedEdges.length ≤ G.raw.edgeCount :=
  list_length_le_fin_of_nodup st.processedEdges st.processedEdges_nodup

def remainingEdges {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Nat :=
  G.raw.edgeCount - st.processedEdges.length

theorem processedEdges_length_lt_of_pending
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    (hactive : active ∈ st.pending) :
    st.processedEdges.length < G.raw.edgeCount := by
  have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
    st.pending_unprocessed active hactive
  have hnodup :
      (G.raw.endpointEdge active :: st.processedEdges).Nodup := by
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  have hle :
      (G.raw.endpointEdge active :: st.processedEdges).length ≤
        G.raw.edgeCount :=
    list_length_le_fin_of_nodup
      (G.raw.endpointEdge active :: st.processedEdges) hnodup
  have hsucc :
      st.processedEdges.length + 1 ≤ G.raw.edgeCount := by
    simpa using hle
  exact Nat.lt_of_succ_le hsucc

def toTraversalState {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    TraversalState G frontier where
  pending := st.pending
  pending_labels := st.pending_labels
  seenNode := st.seenNode
  processedEdge := st.processedEdge
  pending_unprocessed := by
    intro endpoint hpending hprocessed
    exact st.pending_unprocessed endpoint hpending hprocessed

/-- Proof-level frontier completeness for a finite search state. -/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop :=
  st.toTraversalState.FrontierComplete

/-- Frontier completeness transports across a cast of the frontier index. -/
theorem frontierComplete_cast {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier)
    (hc : st.FrontierComplete) :
    (h ▸ st).FrontierComplete := by
  cases h
  exact hc

/-- Initial finite search state: the ordered boundary endpoints are pending. -/
def initial (G : OpenPortHypergraph Sig boundary) : SearchState G boundary where
  pending := List.ofFn G.raw.boundaryPort
  pending_labels := by
    apply List.ext_getElem
    · simp [List.length_ofFn]
    · intro i hleft hright
      rw [List.getElem_map]
      rw [List.getElem_ofFn]
      exact G.raw.boundary_label ⟨i, hright⟩
  pending_nodup :=
    list_nodup_ofFn_injective G.raw.boundaryPort G.raw.boundary_injective
  seenNodes := []
  processedEdges := []
  processedEdges_nodup := by
    simp
  pending_unprocessed := by
    intro _endpoint _hpending
    simp
  pending_owner_seen := by
    intro endpoint hpending owner howner
    rw [List.mem_ofFn] at hpending
    rcases hpending with ⟨boundaryIndex, hboundary⟩
    cases owner with
    | boundary _ =>
        trivial
    | constructor node slot =>
        have hboundaryOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = endpoint := by
          exact hboundary
        have hconstructorOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = endpoint := howner
        rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
        have hboundaryEq :
            (.boundary boundaryIndex :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hboundaryOwner
        have hconstructorEq :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
        have himpossible :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) =
              .boundary boundaryIndex := by
          exact hconstructorEq.trans hboundaryEq.symm
        cases himpossible
  unseen_incident_unprocessed := by
    intro _node _hunseen _slot
    simp

theorem initial_frontierComplete (G : OpenPortHypergraph Sig boundary) :
    (initial G).FrontierComplete := by
  intro endpoint _hunprocessed owner howner
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          G.raw.boundaryPort boundaryIndex = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      have hmem :
          G.raw.boundaryPort boundaryIndex ∈ List.ofFn G.raw.boundaryPort :=
        (List.mem_ofFn).mpr ⟨boundaryIndex, rfl⟩
      rw [hownerEndpoint] at hmem
      simpa [FrontierComplete, toTraversalState, initial] using hmem
  | constructor node _slot =>
      intro hseen
      simp [toTraversalState, initial, seenNode] at hseen

/--
Correspondence between a renderer prefix and an executable search state over
the final rendered graph.  Pending endpoints are exactly the renderer frontier,
processed edges are exactly the rendered edge prefix, and seen constructors are
exactly the rendered node prefix.
-/
structure RenderPrefixRelated
    {frontier : List Sig.Port}
    {final : RenderState Sig []}
    (ev : RenderState.OpenPortHypergraphEvidence final boundary)
    (rst : RenderState Sig frontier)
    (sst : SearchState ev.toOpenPortHypergraph frontier) : Prop where
  pending_vals :
    sst.pending.map (fun endpoint => endpoint.val) = rst.frontierIds
  processed_prefix :
    ∀ edge : Fin ev.toOpenPortHypergraph.raw.edgeCount,
      edge ∈ sst.processedEdges ↔ edge.val < rst.edges.length
  seen_prefix :
    ∀ node : Fin ev.toOpenPortHypergraph.raw.nodeCount,
      node ∈ sst.seenNodes ↔ node.val < rst.nodes.length

theorem RenderPrefixRelated.cast
    {frontier frontier' : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig frontier}
    {sst : SearchState ev.toOpenPortHypergraph frontier}
    (h : frontier = frontier')
    (hrel : RenderPrefixRelated ev rst sst) :
    RenderPrefixRelated ev (h ▸ rst) (h ▸ sst) := by
  cases h
  exact hrel

theorem RenderPrefixRelated.cast_cancel_left
    {frontier frontier' : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig frontier'}
    {sst : SearchState ev.toOpenPortHypergraph frontier}
    (h : frontier = frontier')
    (hrel : RenderPrefixRelated ev (h.symm ▸ rst) sst) :
    RenderPrefixRelated ev rst (h ▸ sst) := by
  cases h
  exact hrel

theorem RenderPrefixRelated.pending_cons_values
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: frontier)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds) :
    active.val = activeId ∧ rest.map (fun endpoint => endpoint.val) = restIds := by
  have hvals :
      (active :: rest).map (fun endpoint => endpoint.val) =
        activeId :: restIds := by
    rw [← hpending, hrel.pending_vals, hids]
  simpa using hvals

theorem initial_renderPrefixRelated
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderPrefixRelated
      (Diag.renderTraceFromBoundary_openEvidence d)
      (RenderState.initial Sig boundary)
      (initial (Diag.toOpenPortHypergraph d)) where
  pending_vals := by
    apply List.ext_getElem
    · simp [initial, RenderState.initial]
    · intro i _hleft hright
      dsimp [initial, RenderState.initial, Diag.toOpenPortHypergraph,
        Diag.renderTraceFromBoundary_openEvidence,
        Diag.renderTraceFromBoundary_graphEvidence,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.boundaryEvidenceOfPrefix]
      simp
  processed_prefix := by
    intro edge
    simp [initial, RenderState.initial]
  seen_prefix := by
    intro node
    simp [initial, RenderState.initial]

/--
State correspondence for two first-pending traversals over isomorphic graph
representatives.  The frontier labels are already the shared type index; this
relation records the stronger endpoint/node/edge correspondence needed for
traversal-invariance proofs.
-/
structure IsoRelated {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    {frontier : List Sig.Port}
    (left : SearchState G frontier) (right : SearchState H frontier) : Prop where
  pending_eq :
    right.pending = left.pending.map e.endpointEquiv.toFun
  seenNodes_eq :
    right.seenNodes = left.seenNodes.map e.nodeEquiv.toFun
  processedEdges_eq :
    right.processedEdges = left.processedEdges.map e.edgeEquiv.toFun

theorem initial_isoRelated {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw) :
    IsoRelated e (initial G) (initial H) where
  pending_eq := by
    apply List.ext_getElem
    · simp [initial]
    · intro i hleft hright
      simp [initial, e.boundary_preserved]
  seenNodes_eq := by
    simp [initial]
  processedEdges_eq := by
    simp [initial]

theorem IsoRelated.pending_cons {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hleft : left.pending = active :: rest) :
    right.pending =
      e.endpointEquiv.toFun active :: rest.map e.endpointEquiv.toFun := by
  rw [hr.pending_eq, hleft]
  rfl

theorem IsoRelated.pending_mem_preserved {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {endpoint : Fin G.raw.endpointCount}
    (hmem : endpoint ∈ left.pending) :
    e.endpointEquiv.toFun endpoint ∈ right.pending := by
  rw [hr.pending_eq]
  exact List.mem_map.mpr ⟨endpoint, hmem, rfl⟩

theorem IsoRelated.pending_mem_reflected {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {endpoint : Fin H.raw.endpointCount}
    (hmem : endpoint ∈ right.pending) :
    e.endpointEquiv.invFun endpoint ∈ left.pending := by
  rw [hr.pending_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨endpoint', hendpoint', heq⟩
  have hpre : e.endpointEquiv.invFun endpoint = endpoint' := by
    rw [← heq]
    simp
  simpa [hpre] using hendpoint'

theorem IsoRelated.seen_mem_preserved {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {node : Fin G.raw.nodeCount}
    (hmem : node ∈ left.seenNodes) :
    e.nodeEquiv.toFun node ∈ right.seenNodes := by
  rw [hr.seenNodes_eq]
  exact List.mem_map.mpr ⟨node, hmem, rfl⟩

theorem IsoRelated.seen_mem_reflected {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {node : Fin H.raw.nodeCount}
    (hmem : node ∈ right.seenNodes) :
    e.nodeEquiv.invFun node ∈ left.seenNodes := by
  rw [hr.seenNodes_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨node', hnode', heq⟩
  have hpre : e.nodeEquiv.invFun node = node' := by
    rw [← heq]
    simp
  simpa [hpre] using hnode'

theorem IsoRelated.processed_mem_preserved
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {edge : Fin G.raw.edgeCount}
    (hmem : edge ∈ left.processedEdges) :
    e.edgeEquiv.toFun edge ∈ right.processedEdges := by
  rw [hr.processedEdges_eq]
  exact List.mem_map.mpr ⟨edge, hmem, rfl⟩

theorem IsoRelated.processed_mem_reflected
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {edge : Fin H.raw.edgeCount}
    (hmem : edge ∈ right.processedEdges) :
    e.edgeEquiv.invFun edge ∈ left.processedEdges := by
  rw [hr.processedEdges_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨edge', hedge', heq⟩
  have hpre : e.edgeEquiv.invFun edge = edge' := by
    rw [← heq]
    simp
  simpa [hpre] using hedge'

theorem IsoRelated.transport_contracts
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hleft : left.pending = active :: rest)
    {leftEndpoint : Fin G.raw.endpointCount}
    {rightEndpoint : Fin H.raw.endpointCount}
    (hleftPending : leftEndpoint ∈ left.pending)
    (hrightPending : rightEndpoint ∈ right.pending)
    {leftNode : Fin G.raw.nodeCount}
    {rightNode : Fin H.raw.nodeCount}
    (hleftSeen : leftNode ∈ left.seenNodes)
    (hrightSeen : rightNode ∈ right.seenNodes)
    {leftEdge : Fin G.raw.edgeCount}
    {rightEdge : Fin H.raw.edgeCount}
    (hleftProcessed : leftEdge ∈ left.processedEdges)
    (hrightProcessed : rightEdge ∈ right.processedEdges) :
    right.pending =
        e.endpointEquiv.toFun active ::
          rest.map e.endpointEquiv.toFun ∧
      e.endpointEquiv.toFun leftEndpoint ∈ right.pending ∧
      e.endpointEquiv.invFun rightEndpoint ∈ left.pending ∧
      e.nodeEquiv.toFun leftNode ∈ right.seenNodes ∧
      e.nodeEquiv.invFun rightNode ∈ left.seenNodes ∧
      e.edgeEquiv.toFun leftEdge ∈ right.processedEdges ∧
      e.edgeEquiv.invFun rightEdge ∈ left.processedEdges := by
  exact ⟨hr.pending_cons hleft,
    hr.pending_mem_preserved hleftPending,
    hr.pending_mem_reflected hrightPending,
    hr.seen_mem_preserved hleftSeen,
    hr.seen_mem_reflected hrightSeen,
    hr.processed_mem_preserved hleftProcessed,
    hr.processed_mem_reflected hrightProcessed⟩

theorem pending_cons_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    (active :: rest).Nodup := by
  simpa [hpending] using st.pending_nodup

theorem active_not_mem_rest {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    active ∉ rest := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.1

theorem rest_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.Nodup := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.2

theorem pending_labels_cons {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel ∧
      rest.map G.raw.endpointLabel = restLabels := by
  have hlabels :
      (active :: rest).map G.raw.endpointLabel =
        activeLabel :: restLabels := by
    simpa [hpending] using st.pending_labels
  simpa using hlabels

theorem active_label_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel :=
  (st.pending_labels_cons hpending).1

theorem rest_labels_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.map G.raw.endpointLabel = restLabels :=
  (st.pending_labels_cons hpending).2

def restLabelIndex {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) : Fin restLabels.length :=
  let hrest := st.rest_labels_eq hpending
  Fin.cast (by
    rw [← hrest]
    simp) mate

theorem restLabelIndex_get {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) :
    restLabels.get (st.restLabelIndex hpending mate) =
      G.raw.endpointLabel (rest.get mate) := by
  have hrest := st.rest_labels_eq hpending
  cases hrest
  simp [restLabelIndex]

theorem IsoRelated.restLabelIndex {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length) :
    right.restLabelIndex (hr.pending_cons hpending) (Fin.cast (by simp) mate) =
      left.restLabelIndex hpending mate := by
  apply Fin.ext
  rfl

theorem constructor_seen_of_pending {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    {endpoint : Fin G.raw.endpointCount}
    (hpending : endpoint ∈ st.pending)
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    (howner :
      PortHypergraph.endpointOwnerEndpoint G.raw (.constructor node slot) =
        endpoint) :
    node ∈ st.seenNodes :=
  st.pending_owner_seen endpoint hpending (.constructor node slot) howner

end SearchState

/--
The local step condition needed by the first-pending traversal.  For the
active endpoint and the remaining ordered pending endpoints, the edge mate must
either already be in the remaining pending list, giving a `connect`, or be an
ordered port of an unseen constructor, giving a `bud`.
-/
def FirstPendingStepReady (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Prop :=
  (∃ mate : Fin rest.length,
    PortHypergraph.EdgeMate G.raw active (rest.get mate)) ∨
  (∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length),
    PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot) ∧
      ¬ seenNode node)

/--
Data for one first-pending traversal step.  This is the constructor-level
choice object that `Diag` construction needs: either the active endpoint
connects to a later pending endpoint, or it enters an unseen constructor at an
ordered slot.
-/
inductive FirstPendingStep (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Type where
  | connect
      (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
      FirstPendingStep G seenNode active rest
  | bud
      (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (unseen : ¬ seenNode node) :
      FirstPendingStep G seenNode active rest

namespace FirstPendingStep

theorem ready {G : OpenPortHypergraph Sig boundary}
    {seenNode : Fin G.raw.nodeCount → Prop}
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (step : FirstPendingStep G seenNode active rest) :
    FirstPendingStepReady G seenNode active rest := by
  cases step with
  | connect mate hmate =>
      exact Or.inl ⟨mate, hmate⟩
  | bud node slot hmate unseen =>
      exact Or.inr ⟨node, slot, hmate, unseen⟩

end FirstPendingStep

namespace SearchState

theorem connect_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    Sig.compatible activeLabel
      (restLabels.get (st.restLabelIndex hpending mate)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hmateLabel := st.restLabelIndex_get hpending mate
  rw [hactive] at hcompat
  rw [← hmateLabel] at hcompat
  exact hcompat

def budEntry {G : OpenPortHypergraph Sig boundary}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length) :
    Fin (Sig.arity (G.raw.nodeLabel node)) :=
  Fin.cast (G.raw.incident_length node) slot

theorem budEntry_val_preserved {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length) :
    (budEntry (G := H) (e.nodeEquiv.toFun node)
        (PortHypergraphIso.incidenceSlotPreserved e node slot)).val =
      (budEntry (G := G) node slot).val := by
  simp [budEntry, PortHypergraphIso.incidenceSlotPreserved]

theorem bud_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)) :
    Sig.compatible activeLabel
      (Sig.port (G.raw.nodeLabel node) (budEntry node slot)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hslot := G.raw.incidence_label node slot
  rw [hactive] at hcompat
  rw [hslot] at hcompat
  exact hcompat

def connectChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    SearchState G (eraseFin restLabels (st.restLabelIndex hpending mate)) where
  pending := eraseFin rest mate
  pending_labels := by
    calc
      (eraseFin rest mate).map G.raw.endpointLabel =
          eraseFin (rest.map G.raw.endpointLabel) (Fin.cast (by simp) mate) :=
        map_eraseFin G.raw.endpointLabel rest mate
      _ = eraseFin restLabels (st.restLabelIndex hpending mate) := by
        have hrest := st.rest_labels_eq hpending
        cases hrest
        simp [restLabelIndex]
  pending_nodup :=
    nodup_eraseFin rest mate (st.rest_nodup hpending)
  seenNodes := st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  processedEdges_nodup := by
    have hactivePending : active ∈ st.pending := by
      rw [hpending]
      simp
    have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
      st.pending_unprocessed active hactivePending
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        exact st.active_not_mem_rest hpending (by
          simpa [hactiveEndpoint] using hrestMem)
      have hendpointMate : endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmateNotMem :
          rest.get mate ∉ eraseFin rest mate :=
        get_not_mem_eraseFin_of_nodup rest mate (st.rest_nodup hpending)
      exact hmateNotMem (by simpa [hendpointMate] using hmem)
    · exact st.pending_unprocessed endpoint hstPending hold
  pending_owner_seen := by
    intro endpoint hmem owner howner
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    exact st.pending_owner_seen endpoint hstPending owner howner
  unseen_incident_unprocessed := by
    intro node hunseen slot hprocessed
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · let endpoint := (G.raw.incident node).get slot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hownerActive :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = active := by
          change (G.raw.incident node).get slot = active
          exact hactiveEndpoint.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending hownerActive
        exact hunseen hseen
      have hendpointMate :
          endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmatePending : rest.get mate ∈ st.pending := by
        rw [hpending]
        right
        exact List.get_mem rest mate
      have hownerMate :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = rest.get mate := by
        change (G.raw.incident node).get slot = rest.get mate
        exact hendpointMate
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hmatePending hownerMate
      exact hunseen hseen
    · exact st.unseen_incident_unprocessed node hunseen slot hold

theorem connectChild_frontierComplete {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (hcomplete : st.FrontierComplete) :
    (st.connectChild hpending mate hmate).FrontierComplete := by
  intro endpoint hunprocessed owner howner
  have hchildUnprocessed :
      G.raw.endpointEdge endpoint ∉
        G.raw.endpointEdge active :: st.processedEdges := by
    simpa [FrontierComplete, toTraversalState, connectChild, processedEdge]
      using hunprocessed
  have hnotActiveEdge :
      G.raw.endpointEdge endpoint ≠ G.raw.endpointEdge active := by
    intro hedge
    exact hchildUnprocessed (by simp [hedge])
  have holdUnprocessed :
      G.raw.endpointEdge endpoint ∉ st.processedEdges := by
    intro hold
    exact hchildUnprocessed (by simp [hold])
  have old_pending_to_child
      (holdPending : endpoint ∈ st.pending) :
      endpoint ∈ eraseFin rest mate := by
    have hrest : endpoint ∈ rest := by
      rw [hpending] at holdPending
      exact list_mem_tail_of_mem_cons_ne holdPending (by
        intro hactiveEndpoint
        exact hnotActiveEdge (by
          rw [← hactiveEndpoint]))
    have hnotMate : endpoint ≠ rest.get mate := by
      intro hendpointMate
      exact hnotActiveEdge (by
        rw [hendpointMate]
        exact hmate.2.symm)
    exact mem_eraseFin_of_mem_ne_get rest mate hrest hnotMate
  cases owner with
  | boundary boundaryIndex =>
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.boundary boundaryIndex) howner
      simpa [FrontierComplete, toTraversalState, connectChild]
        using old_pending_to_child holdPending
  | constructor node slot =>
      intro hseen
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.constructor node slot) howner hseen
      simpa [FrontierComplete, toTraversalState, connectChild, seenNode]
        using old_pending_to_child holdPending

def budChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    SearchState G
      (restLabels ++
        Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot)) where
  pending := rest ++ eraseFin (G.raw.incident node) slot
  pending_labels := by
    calc
      (rest ++ eraseFin (G.raw.incident node) slot).map
          G.raw.endpointLabel =
          rest.map G.raw.endpointLabel ++
            (eraseFin (G.raw.incident node) slot).map G.raw.endpointLabel := by
        simp
      _ = restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot) := by
        rw [st.rest_labels_eq hpending,
          G.raw.incident_labels_except node slot]
        rfl
  pending_nodup := by
    apply nodup_append_of_nodup_disjoint
    · exact st.rest_nodup hpending
    · exact nodup_eraseFin (G.raw.incident node) slot
        (G.raw.incident_nodup node)
    · intro endpoint hrest hnew
      have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnew
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      have howner :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot') = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hstPending howner
      exact hunseen hseen
  seenNodes := node :: st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  processedEdges_nodup := by
    have hactivePending : active ∈ st.pending := by
      rw [hpending]
      simp
    have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
      st.pending_unprocessed active hactivePending
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    simp at hmem
    simp at hprocessed
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          exact st.active_not_mem_rest hpending (by
            simpa [hactiveEndpoint] using hrest)
        have hendpointMate :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hstPending (by
            change (G.raw.incident node).get slot = endpoint
            exact hendpointMate.symm)
        exact hunseen hseen
      · exact st.pending_unprocessed endpoint hstPending hold
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          have hactivePending : active ∈ st.pending := by
            rw [hpending]
            simp
          have hseen : node ∈ st.seenNodes :=
            st.constructor_seen_of_pending hactivePending (by
              change (G.raw.incident node).get slot' = active
              exact hslot'.trans hactiveEndpoint.symm)
          exact hunseen hseen
        have hendpointEntry :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hentryNotMem :
            (G.raw.incident node).get slot ∉
              eraseFin (G.raw.incident node) slot :=
          get_not_mem_eraseFin_of_nodup (G.raw.incident node) slot
            (G.raw.incident_nodup node)
        exact hentryNotMem (by simpa [hendpointEntry] using hnewEndpoint)
      · have holdSlot :
            G.raw.endpointEdge ((G.raw.incident node).get slot') ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hunseen slot'
        exact holdSlot (by
          rw [hslot']
          exact hold)
  pending_owner_seen := by
    intro endpoint hmem owner howner
    simp at hmem
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hseen : ownerNode ∈ st.seenNodes :=
            st.constructor_seen_of_pending hstPending howner
          simp [hseen]
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hconstructorOwner :
              PortHypergraph.endpointOwnerEndpoint G.raw
                  (.constructor node slot') = endpoint := by
            simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
          rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
          have hnewEq :
              (.constructor node slot' :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
          have hownerEq :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using howner
          have hsame :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) =
                .constructor node slot' := hownerEq.trans hnewEq.symm
          cases hsame
          simp
  unseen_incident_unprocessed := by
    intro otherNode hotherUnseen otherSlot hprocessed
    have hotherNotSeen : otherNode ∉ st.seenNodes := by
      intro hseen
      exact hotherUnseen (by simp [hseen])
    simp at hprocessed
    rcases hprocessed with hnewProcessed | hold
    · let endpoint := (G.raw.incident otherNode).get otherSlot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hseen : otherNode ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending (by
            change (G.raw.incident otherNode).get otherSlot = active
            exact hactiveEndpoint.symm)
        exact hotherNotSeen hseen
      have hendpointEntry :
          endpoint = (G.raw.incident node).get slot := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
          huniq ((G.raw.incident node).get slot) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hownerOther :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor otherNode otherSlot) =
            endpoint := rfl
      have hownerNode :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) =
            endpoint := by
        change (G.raw.incident node).get slot = endpoint
        exact hendpointEntry.symm
      rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
      have hotherEq :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerOther
      have hnodeEq :
          (.constructor node slot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerNode
      have hsame :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) =
            .constructor node slot := hotherEq.trans hnodeEq.symm
      cases hsame
      exact hotherUnseen (by simp)
    · exact st.unseen_incident_unprocessed otherNode hotherNotSeen otherSlot hold

theorem budChild_frontierComplete {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    (hcomplete : st.FrontierComplete) :
    (st.budChild hpending node slot hmate hunseen).FrontierComplete := by
  intro endpoint hunprocessed owner howner
  have hchildUnprocessed :
      G.raw.endpointEdge endpoint ∉
        G.raw.endpointEdge active :: st.processedEdges := by
    simpa [FrontierComplete, toTraversalState, budChild, processedEdge]
      using hunprocessed
  have hnotActiveEdge :
      G.raw.endpointEdge endpoint ≠ G.raw.endpointEdge active := by
    intro hedge
    exact hchildUnprocessed (by simp [hedge])
  have holdUnprocessed :
      G.raw.endpointEdge endpoint ∉ st.processedEdges := by
    intro hold
    exact hchildUnprocessed (by simp [hold])
  have old_pending_to_child
      (holdPending : endpoint ∈ st.pending) :
      endpoint ∈ rest ++ eraseFin (G.raw.incident node) slot := by
    have hrest : endpoint ∈ rest := by
      rw [hpending] at holdPending
      exact list_mem_tail_of_mem_cons_ne holdPending (by
        intro hactiveEndpoint
        exact hnotActiveEdge (by
          rw [← hactiveEndpoint]))
    exact List.mem_append_left _ hrest
  cases owner with
  | boundary boundaryIndex =>
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.boundary boundaryIndex) howner
      simpa [FrontierComplete, toTraversalState, budChild]
        using old_pending_to_child holdPending
  | constructor ownerNode ownerSlot =>
      intro hseen
      have hseen' : ownerNode ∈ node :: st.seenNodes := by
        simpa [FrontierComplete, toTraversalState, budChild, seenNode]
          using hseen
      simp at hseen'
      rcases hseen' with hnew | holdSeen
      · cases hnew
        have hownerEndpoint :
            (G.raw.incident node).get ownerSlot = endpoint := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hnotEntry :
            endpoint ≠ (G.raw.incident node).get slot := by
          intro hendpointEntry
          exact hnotActiveEdge (by
            rw [hendpointEntry]
            exact hmate.2.symm)
        have hmemIncident :
            endpoint ∈ G.raw.incident node := by
          rw [← hownerEndpoint]
          exact List.get_mem (G.raw.incident node) ownerSlot
        have hmemExcept :
            endpoint ∈ eraseFin (G.raw.incident node) slot :=
          mem_eraseFin_of_mem_ne_get (G.raw.incident node) slot
            hmemIncident hnotEntry
        exact List.mem_append_right rest hmemExcept
      · have holdPending :
            endpoint ∈ st.pending :=
          hcomplete endpoint holdUnprocessed
            (.constructor ownerNode ownerSlot) howner holdSeen
        simpa [FrontierComplete, toTraversalState, budChild, seenNode]
          using old_pending_to_child holdPending

theorem connectChild_remainingEdges_lt {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    (st.connectChild hpending mate hmate).remainingEdges < st.remainingEdges := by
  have hactive : active ∈ st.pending := by
    rw [hpending]
    simp
  have hlt := st.processedEdges_length_lt_of_pending hactive
  simp [remainingEdges, connectChild]
  omega

theorem connectChild_proof_irrel {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate₁ hmate₂ : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    st.connectChild hpending mate hmate₁ =
      st.connectChild hpending mate hmate₂ := by
  have hproof : hmate₁ = hmate₂ := Subsingleton.elim _ _
  cases hproof
  rfl

theorem budChild_remainingEdges_lt {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    (st.budChild hpending node slot hmate hunseen).remainingEdges <
      st.remainingEdges := by
  have hactive : active ∈ st.pending := by
    rw [hpending]
    simp
  have hlt := st.processedEdges_length_lt_of_pending hactive
  simp [remainingEdges, budChild]
  omega

theorem budChild_proof_irrel {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate₁ hmate₂ :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen₁ hunseen₂ : node ∉ st.seenNodes) :
    st.budChild hpending node slot hmate₁ hunseen₁ =
      st.budChild hpending node slot hmate₂ hunseen₂ := by
  have hmateProof : hmate₁ = hmate₂ := Subsingleton.elim _ _
  have hunseenProof : hunseen₁ = hunseen₂ := Subsingleton.elim _ _
  cases hmateProof
  cases hunseenProof
  rfl

theorem RenderPrefixRelated.connectChild_of_new_edge
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: frontier)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        (rest.get mate))
    (childRst :
      RenderState Sig (eraseFin frontier (sst.restLabelIndex hpending mate)))
    (hpendingVals :
      (sst.connectChild hpending mate hmate).pending.map
          (fun endpoint => endpoint.val) = childRst.frontierIds)
    (hactiveEdge :
      (ev.toOpenPortHypergraph.raw.endpointEdge active).val =
        rst.edges.length)
    (hedgesLength : childRst.edges.length = rst.edges.length + 1)
    (hnodesLength : childRst.nodes.length = rst.nodes.length) :
    RenderPrefixRelated ev childRst
      (sst.connectChild hpending mate hmate) where
  pending_vals := hpendingVals
  processed_prefix := by
    intro edge
    constructor
    · intro hmem
      simp [connectChild] at hmem
      rcases hmem with hnew | hold
      · have hval : edge.val = rst.edges.length := by
          rw [hnew]
          exact hactiveEdge
        omega
      · have holdLt := (hrel.processed_prefix edge).1 hold
        omega
    · intro hlt
      have hlt' : edge.val < rst.edges.length + 1 := by
        simpa [hedgesLength] using hlt
      have hcases : edge.val < rst.edges.length ∨
          edge.val = rst.edges.length := by
        omega
      simp [connectChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.processed_prefix edge).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hactiveEdge.symm
  seen_prefix := by
    intro node
    constructor
    · intro hmem
      simp [connectChild] at hmem
      have hlt := (hrel.seen_prefix node).1 hmem
      omega
    · intro hlt
      simp [connectChild]
      have hltOld : node.val < rst.nodes.length := by
        omega
      exact (hrel.seen_prefix node).2 hltOld

theorem RenderPrefixRelated.connectChild_pending_vals
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: frontier)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (searchMate : Fin rest.length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        (rest.get searchMate))
    (rendererMate : Fin frontier.length)
    (ok : Sig.compatible activeLabel (frontier.get rendererMate))
    (hindex : searchMate.val = rendererMate.val) :
    (sst.connectChild hpending searchMate hmate).pending.map
        (fun endpoint => endpoint.val) =
      (Diag.connectStep rendererMate ok rst).frontierIds := by
  cases hidsCase : rst.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil rst hidsCase)
  | cons activeId restIds =>
      have hids : rst.frontierIds = activeId :: restIds := hidsCase
      have hvals := hrel.pending_cons_values hpending hids
      have hrestLen : restIds.length = frontier.length := by
        have hlen := rst.frontierIds_length
        rw [hids] at hlen
        exact Nat.succ.inj hlen
      rw [Diag.connectStep_frontierIds rendererMate ok rst hids]
      simp [connectChild]
      have hmap :
          (eraseFin rest searchMate).map (fun endpoint => endpoint.val) =
            eraseFin (rest.map (fun endpoint => endpoint.val))
              (Fin.cast (by simp) searchMate) := by
        exact map_eraseFin (fun endpoint => endpoint.val) rest searchMate
      rw [hmap]
      calc
        eraseFin (rest.map (fun endpoint => endpoint.val))
            (Fin.cast (by simp) searchMate) =
          eraseFin restIds
            (Fin.cast (by rw [← hvals.2])
              (Fin.cast (by simp) searchMate)) := by
            exact eraseFin_eq_of_eq hvals.2 (Fin.cast (by simp) searchMate)
        _ = eraseFin restIds (Fin.cast hrestLen.symm rendererMate) := by
            apply congrArg
            apply Fin.ext
            exact hindex

theorem RenderPrefixRelated.budChild_pending_vals
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: restLabels)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: restLabels)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (node : Fin ev.toOpenPortHypergraph.raw.nodeCount)
    (slot : Fin (ev.toOpenPortHypergraph.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        ((ev.toOpenPortHypergraph.raw.incident node).get slot))
    (hunseen : node ∉ sst.seenNodes)
    (rendererNode : Sig.Node)
    (entry : Fin (Sig.arity rendererNode))
    (ok : Sig.compatible activeLabel (Sig.port rendererNode entry))
    (hincidentVals :
      (ev.toOpenPortHypergraph.raw.incident node).map
          (fun endpoint => endpoint.val) =
        Diag.freshNodeEndpoints rst.nextEndpoint (Sig.arity rendererNode))
    (hslot : slot.val = entry.val) :
    (sst.budChild hpending node slot hmate hunseen).pending.map
        (fun endpoint => endpoint.val) =
      (Diag.budStep rendererNode entry ok rst).frontierIds := by
  cases hidsCase : rst.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil rst hidsCase)
  | cons activeId restIds =>
      have hids : rst.frontierIds = activeId :: restIds := hidsCase
      have hvals := hrel.pending_cons_values hpending hids
      rw [Diag.budStep_frontierIds rendererNode entry ok rst hids]
      simp [budChild]
      rw [hvals.2]
      have hmap :
          (eraseFin (ev.toOpenPortHypergraph.raw.incident node) slot).map
              (fun endpoint => endpoint.val) =
            eraseFin
              ((ev.toOpenPortHypergraph.raw.incident node).map
                (fun endpoint => endpoint.val))
              (Fin.cast (by simp) slot) := by
        exact map_eraseFin (fun endpoint => endpoint.val)
          (ev.toOpenPortHypergraph.raw.incident node) slot
      rw [hmap]
      apply congrArg (fun tail => restIds ++ tail)
      calc
        eraseFin
            ((ev.toOpenPortHypergraph.raw.incident node).map
              (fun endpoint => endpoint.val))
            (Fin.cast (by simp) slot) =
          eraseFin (Diag.freshNodeEndpoints rst.nextEndpoint
              (Sig.arity rendererNode))
            (Fin.cast (by rw [← hincidentVals])
              (Fin.cast (by simp) slot)) := by
            exact eraseFin_eq_of_eq hincidentVals (Fin.cast (by simp) slot)
        _ =
          eraseFin (Diag.freshNodeEndpoints rst.nextEndpoint
              (Sig.arity rendererNode))
            (Fin.cast (by simp [Diag.freshNodeEndpoints]) entry) := by
            apply congrArg
            apply Fin.ext
            exact hslot

theorem RenderPrefixRelated.budChild_of_new_edge_node
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: restLabels)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: restLabels)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (node : Fin ev.toOpenPortHypergraph.raw.nodeCount)
    (slot : Fin (ev.toOpenPortHypergraph.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        ((ev.toOpenPortHypergraph.raw.incident node).get slot))
    (hunseen : node ∉ sst.seenNodes)
    (childRst :
      RenderState Sig
        (restLabels ++
          Sig.nodePortsExcept (ev.toOpenPortHypergraph.raw.nodeLabel node)
            (budEntry node slot)))
    (hpendingVals :
      (sst.budChild hpending node slot hmate hunseen).pending.map
          (fun endpoint => endpoint.val) = childRst.frontierIds)
    (hactiveEdge :
      (ev.toOpenPortHypergraph.raw.endpointEdge active).val =
        rst.edges.length)
    (hnewNode : node.val = rst.nodes.length)
    (hedgesLength : childRst.edges.length = rst.edges.length + 1)
    (hnodesLength : childRst.nodes.length = rst.nodes.length + 1) :
    RenderPrefixRelated ev childRst
      (sst.budChild hpending node slot hmate hunseen) where
  pending_vals := hpendingVals
  processed_prefix := by
    intro edge
    constructor
    · intro hmem
      simp [budChild] at hmem
      rcases hmem with hnew | hold
      · have hval : edge.val = rst.edges.length := by
          rw [hnew]
          exact hactiveEdge
        omega
      · have holdLt := (hrel.processed_prefix edge).1 hold
        omega
    · intro hlt
      have hlt' : edge.val < rst.edges.length + 1 := by
        simpa [hedgesLength] using hlt
      have hcases : edge.val < rst.edges.length ∨
          edge.val = rst.edges.length := by
        omega
      simp [budChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.processed_prefix edge).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hactiveEdge.symm
  seen_prefix := by
    intro candidate
    constructor
    · intro hmem
      simp [budChild] at hmem
      rcases hmem with hnew | hold
      · have hval : candidate.val = rst.nodes.length := by
          rw [hnew]
          exact hnewNode
        omega
      · have holdLt := (hrel.seen_prefix candidate).1 hold
        omega
    · intro hlt
      have hlt' : candidate.val < rst.nodes.length + 1 := by
        simpa [hnodesLength] using hlt
      have hcases : candidate.val < rst.nodes.length ∨
          candidate.val = rst.nodes.length := by
        omega
      simp [budChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.seen_prefix candidate).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hnewNode.symm

theorem IsoRelated.connectChild
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    let rightPending := hr.pending_cons hpending
    let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
      Fin.cast (by simp) mate
    let rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((rest.map e.endpointEquiv.toFun).get rightMate) := by
      have hget :
          (rest.map e.endpointEquiv.toFun).get rightMate =
            e.endpointEquiv.toFun (rest.get mate) := by
        simp [rightMate]
      rw [hget]
      exact PortHypergraphIso.edgeMate_preserved e hmate
    IsoRelated e
      (left.connectChild hpending mate hmate)
      (right.connectChild rightPending rightMate rightMateEdge) := by
  dsimp
  constructor
  · exact (map_eraseFin e.endpointEquiv.toFun rest mate).symm
  · exact hr.seenNodes_eq
  · change H.raw.endpointEdge (e.endpointEquiv.toFun active) ::
        right.processedEdges =
      (G.raw.endpointEdge active :: left.processedEdges).map
        e.edgeEquiv.toFun
    rw [e.endpoint_edge_preserved active, hr.processedEdges_eq]
    rfl

theorem IsoRelated.connectChild_with
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((rest.map e.endpointEquiv.toFun).get (Fin.cast (by simp) mate))) :
    IsoRelated e
      (left.connectChild hpending mate hmate)
      (right.connectChild (hr.pending_cons hpending)
        (Fin.cast (by simp) mate) rightMateEdge) := by
  have hbase := hr.connectChild hpending mate hmate
  dsimp at hbase
  have hchild :
      right.connectChild (hr.pending_cons hpending)
          (Fin.cast (by simp) mate) (by
            have hget :
                (rest.map e.endpointEquiv.toFun).get (Fin.cast (by simp) mate) =
                  e.endpointEquiv.toFun (rest.get mate) := by
              simp
            rw [hget]
            exact PortHypergraphIso.edgeMate_preserved e hmate) =
        right.connectChild (hr.pending_cons hpending)
          (Fin.cast (by simp) mate) rightMateEdge := by
    exact right.connectChild_proof_irrel (hr.pending_cons hpending)
      (Fin.cast (by simp) mate) _ rightMateEdge
  rw [← hchild]
  exact hbase

theorem IsoRelated.budChild
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ left.seenNodes) :
    let rightPending := hr.pending_cons hpending
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    let rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((H.raw.incident rightNode).get rightSlot) := by
      have hslot :
          (H.raw.incident rightNode).get rightSlot =
            e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
        PortHypergraphIso.incidence_get_preserved e node slot
      rw [hslot]
      exact PortHypergraphIso.edgeMate_preserved e hmate
    let rightUnseen : rightNode ∉ right.seenNodes := by
      intro hseen
      have hpre := hr.seen_mem_reflected hseen
      exact hunseen (by simpa [rightNode] using hpre)
    let hfrontier :
        restLabels ++
            Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
              (budEntry (G := H) rightNode rightSlot) =
          restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node)
              (budEntry (G := G) node slot) := by
      have hentryVal :
          (budEntry (G := H) (e.nodeEquiv.toFun node)
              (PortHypergraphIso.incidenceSlotPreserved e node slot)).val =
            (budEntry (G := G) node slot).val := by
        simp [budEntry, PortHypergraphIso.incidenceSlotPreserved]
      exact congrArg (fun tail => restLabels ++ tail)
        (nodePortsExcept_eq_of_val
          (e.node_label_preserved node).symm hentryVal)
    IsoRelated e
      (left.budChild hpending node slot hmate hunseen)
      (hfrontier ▸
        right.budChild rightPending rightNode rightSlot rightMateEdge
          rightUnseen) := by
  dsimp
  constructor
  · rw [cast_pending]
    calc
      rest.map e.endpointEquiv.toFun ++
          eraseFin (H.raw.incident (e.nodeEquiv.toFun node))
            (PortHypergraphIso.incidenceSlotPreserved e node slot) =
        rest.map e.endpointEquiv.toFun ++
          eraseFin ((G.raw.incident node).map e.endpointEquiv.toFun)
            (Fin.cast (by simp) slot) := by
          congr 1
          have hincident :
              H.raw.incident (e.nodeEquiv.toFun node) =
                (G.raw.incident node).map e.endpointEquiv.toFun :=
            (e.incidence_preserved node).symm
          rw [eraseFin_eq_of_eq hincident
            (PortHypergraphIso.incidenceSlotPreserved e node slot)]
          apply congrArg
          apply Fin.ext
          rfl
      _ = rest.map e.endpointEquiv.toFun ++
          (eraseFin (G.raw.incident node) slot).map e.endpointEquiv.toFun := by
          rw [map_eraseFin]
      _ =
          (rest ++ eraseFin (G.raw.incident node) slot).map
            e.endpointEquiv.toFun := by
          rw [List.map_append]
  · rw [cast_seenNodes]
    change e.nodeEquiv.toFun node :: right.seenNodes =
      (node :: left.seenNodes).map e.nodeEquiv.toFun
    rw [hr.seenNodes_eq]
    rfl
  · rw [cast_processedEdges]
    change H.raw.endpointEdge (e.endpointEquiv.toFun active) ::
        right.processedEdges =
      (G.raw.endpointEdge active :: left.processedEdges).map
        e.edgeEquiv.toFun
    rw [e.endpoint_edge_preserved active, hr.processedEdges_eq]
    rfl

theorem IsoRelated.budChild_with
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ left.seenNodes)
    (rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((H.raw.incident (e.nodeEquiv.toFun node)).get
          (PortHypergraphIso.incidenceSlotPreserved e node slot)))
    (rightUnseen : e.nodeEquiv.toFun node ∉ right.seenNodes) :
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    let hfrontier :
        restLabels ++
            Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
              (budEntry (G := H) rightNode rightSlot) =
          restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node)
              (budEntry (G := G) node slot) := by
      have hentryVal := budEntry_val_preserved e node slot
      exact congrArg (fun tail => restLabels ++ tail)
        (nodePortsExcept_eq_of_val
          (e.node_label_preserved node).symm hentryVal)
    IsoRelated e
      (left.budChild hpending node slot hmate hunseen)
      (hfrontier ▸
        right.budChild (hr.pending_cons hpending) rightNode rightSlot
          rightMateEdge rightUnseen) := by
  dsimp
  have hbase := hr.budChild hpending node slot hmate hunseen
  dsimp at hbase
  have hmateProof :
      (by
        have hslot :
            (H.raw.incident (e.nodeEquiv.toFun node)).get
                (PortHypergraphIso.incidenceSlotPreserved e node slot) =
              e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
          PortHypergraphIso.incidence_get_preserved e node slot
        rw [hslot]
        exact PortHypergraphIso.edgeMate_preserved e hmate) =
      rightMateEdge := Subsingleton.elim _ _
  have hunseenProof :
      (by
        intro hseen
        have hpre := hr.seen_mem_reflected hseen
        exact hunseen (by simpa [seenNode] using hpre)) =
      rightUnseen := Subsingleton.elim _ _
  cases hmateProof
  cases hunseenProof
  exact hbase

end SearchState

/--
Search the ordered pending tail for a `connect` step.  A successful result
carries the exact mate index and edge-mate proof consumed by `Diag.connect`.
-/
def firstPendingConnectSearch? (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G seenNode active rest) :=
  (List.finRange rest.length).findSome? fun mate =>
    match PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | some hmate => some (FirstPendingStep.connect mate hmate.proof)
    | none => none

theorem firstPendingConnectSearch?_exists_of_witness
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ step : FirstPendingStep G seenNode active rest,
      firstPendingConnectSearch? G seenNode active rest = some step := by
  unfold firstPendingConnectSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange mate
  · have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingConnectSearch?_some_connect
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G seenNode active rest}
    (hstep : firstPendingConnectSearch? G seenNode active rest = some step) :
    ∃ (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)),
      step = FirstPendingStep.connect mate hmate := by
  unfold firstPendingConnectSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨mate, _hmem, hcandidate⟩
  cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
      (rest.get mate) with
  | none =>
      rw [hcase] at hcandidate
      cases hcandidate
  | some data =>
      rw [hcase] at hcandidate
      injection hcandidate with hstepEq
      exact ⟨mate, data.proof, hstepEq.symm⟩

namespace SearchState

/--
Search unseen constructors in representative order for a `bud` step.  The
successful slot is the constructor port joined to the active endpoint.
-/
def firstPendingBudSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  (List.finRange G.raw.nodeCount).findSome? fun node =>
    if hseen : node ∈ st.seenNodes then
      none
    else
      (List.finRange (G.raw.incident node).length).findSome? fun slot =>
        match PortHypergraph.edgeMateCandidate? G.raw active
            ((G.raw.incident node).get slot) with
        | some hmate =>
            some (FirstPendingStep.bud node slot hmate.proof
              (by simpa [seenNode] using hseen))
        | none => none

theorem firstPendingBudSearch?_exists_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingBudSearch? active rest = some step := by
  unfold firstPendingBudSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange node
  · have hnodeUnseen : node ∉ st.seenNodes := by
      simpa [seenNode] using hunseen
    simp [hnodeUnseen]
    refine ⟨slot, ?_⟩
    have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingBudSearch?_some_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (hstep : st.firstPendingBudSearch? active rest = some step) :
    ∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen : ¬ st.seenNode node),
      step = FirstPendingStep.bud node slot hmate hunseen := by
  unfold firstPendingBudSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨node, _hnodeMem, hnodeCandidate⟩
  by_cases hseen : node ∈ st.seenNodes
  · simp [hseen] at hnodeCandidate
  · simp [hseen] at hnodeCandidate
    rcases List.exists_of_findSome?_eq_some hnodeCandidate with
      ⟨slot, _hslotMem, hslotCandidate⟩
    change
      (match PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
        | some hmate => some (FirstPendingStep.bud node slot
            hmate.proof (by simpa [seenNode] using hseen))
        | none => none) = some step at hslotCandidate
    cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
        ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hslotCandidate
        cases hslotCandidate
    | some data =>
        rw [hcase] at hslotCandidate
        injection hslotCandidate with hstepEq
        exact ⟨node, slot, data.proof, by simpa [seenNode] using hseen,
          hstepEq.symm⟩

/--
Executable first-pending search.  It tries the remaining pending frontier
first, then unseen constructor ports.  The returned value is constructor data,
not an eliminated `Prop` witness.
-/
def firstPendingStepSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  match firstPendingConnectSearch? G st.seenNode active rest with
  | some step => some step
  | none => st.firstPendingBudSearch? active rest

/-- A successful bud result from the executable first-pending search certifies
that the pending-tail connect search failed. -/
theorem firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    {hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)}
    {hunseen : ¬ st.seenNode node}
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    firstPendingConnectSearch? G st.seenNode active rest = none := by
  unfold firstPendingStepSearch? at hstep
  cases hconnect :
      firstPendingConnectSearch? G st.seenNode active rest with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          G st.seenNode hconnect with
        ⟨mate, hmate, hstepEq⟩
      rw [hconnect, hstepEq] at hstep
      cases hstep

theorem firstPendingStepSearch?_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (_hstep : st.firstPendingStepSearch? active rest = some step) :
    FirstPendingStepReady G st.seenNode active rest :=
  step.ready

theorem firstPendingStepSearch?_exists_of_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hready : FirstPendingStepReady G st.seenNode active rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step := by
  rcases hready with hconnect | hbud
  · rcases hconnect with ⟨mate, hmate⟩
    rcases firstPendingConnectSearch?_exists_of_witness
        G st.seenNode mate hmate with ⟨step, hstep⟩
    unfold firstPendingStepSearch?
    rw [hstep]
    exact ⟨step, rfl⟩
  · rcases hbud with ⟨node, slot, hmate, hunseen⟩
    unfold firstPendingStepSearch?
    cases hconnect :
        firstPendingConnectSearch? G st.seenNode active rest with
    | some step =>
        exact ⟨step, rfl⟩
    | none =>
        rcases st.firstPendingBudSearch?_exists_of_witness
            node slot hmate hunseen with ⟨step, hstep⟩
        exact ⟨step, by simp [hstep]⟩

theorem firstPendingStepSearch?_some_connect_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ (mate' : Fin rest.length)
      (hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate')),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate' hmate') := by
  rcases firstPendingConnectSearch?_exists_of_witness
      G st.seenNode mate hmate with ⟨step, hstep⟩
  rcases firstPendingConnectSearch?_some_connect
      G st.seenNode hstep with ⟨mate', hmate', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hstep]
  exact ⟨mate', hmate', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_connect_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hrestNodup : rest.Nodup)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate') := by
  rcases st.firstPendingStepSearch?_some_connect_of_witness mate hmate with
    ⟨mate', hmate', hstep⟩
  have hget : rest.get mate' = rest.get mate := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq (rest.get mate') hmate').trans
      (huniq (rest.get mate) hmate).symm
  have hmateEq : mate' = mate :=
    list_get_injective_of_nodup rest hrestNodup hget
  subst mate'
  exact ⟨hmate', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_connect
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
      Fin.cast (by simp) mate
    ∃ rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((rest.map e.endpointEquiv.toFun).get rightMate),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.connect rightMate rightMateEdge) := by
  dsimp
  let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
    Fin.cast (by simp) mate
  have hget :
      (rest.map e.endpointEquiv.toFun).get rightMate =
        e.endpointEquiv.toFun (rest.get mate) := by
    simp [rightMate]
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((rest.map e.endpointEquiv.toFun).get rightMate) := by
    rw [hget]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have hrightPending := hr.pending_cons hpending
  have hrightNodup :
      (rest.map e.endpointEquiv.toFun).Nodup :=
    right.rest_nodup hrightPending
  rcases right.firstPendingStepSearch?_some_connect_exact_of_witness
      hrightNodup rightMate rightMateEdge with
    ⟨rightMateEdge', hstep⟩
  exact ⟨rightMateEdge', hstep⟩

theorem IsoRelated.firstPendingConnectSearch?_none
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (_hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (_hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none) :
    firstPendingConnectSearch? H right.seenNode (e.endpointEquiv.toFun active)
        (rest.map e.endpointEquiv.toFun) = none := by
  cases hright :
      firstPendingConnectSearch? H right.seenNode
        (e.endpointEquiv.toFun active) (rest.map e.endpointEquiv.toFun) with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          H right.seenNode hright with
        ⟨rightMate, hmateRight, _hstepEq⟩
      let leftMate : Fin rest.length :=
        Fin.cast (by simp) rightMate
      have hget :
          (rest.map e.endpointEquiv.toFun).get rightMate =
            e.endpointEquiv.toFun (rest.get leftMate) := by
        simp [leftMate]
      have hmateRight' :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            (e.endpointEquiv.toFun (rest.get leftMate)) := by
        simpa [hget] using hmateRight
      have hmateLeft :
          PortHypergraph.EdgeMate G.raw active (rest.get leftMate) := by
        have hreflected := PortHypergraphIso.edgeMate_reflected e hmateRight'
        simpa using hreflected
      rcases firstPendingConnectSearch?_exists_of_witness
          G left.seenNode leftMate hmateLeft with
        ⟨leftStep, hleftStep⟩
      rw [hconnect] at hleftStep
      cases hleftStep

theorem firstPendingStepSearch?_some_bud_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (node' : Fin G.raw.nodeCount)
      (slot' : Fin (G.raw.incident node').length)
      (hmate' :
        PortHypergraph.EdgeMate G.raw active
          ((G.raw.incident node').get slot'))
      (hunseen' : ¬ st.seenNode node'),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node' slot' hmate' hunseen') := by
  rcases st.firstPendingBudSearch?_exists_of_witness
      node slot hmate hunseen with ⟨step, hstep⟩
  rcases st.firstPendingBudSearch?_some_bud hstep with
    ⟨node', slot', hmate', hunseen', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hconnect, hstep]
  exact ⟨node', slot', hmate', hunseen', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_bud_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (hmate' :
          PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen' : ¬ st.seenNode node),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate' hunseen') := by
  rcases st.firstPendingStepSearch?_some_bud_of_witness
      hconnect node slot hmate hunseen with
    ⟨node', slot', hmate', hunseen', hstep⟩
  have hendpointEq :
      (G.raw.incident node').get slot' = (G.raw.incident node).get slot := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq ((G.raw.incident node').get slot') hmate').trans
      (huniq ((G.raw.incident node).get slot) hmate).symm
  have hownerEq :
      (.constructor node' slot' :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      (.constructor node slot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) := by
    let endpoint := (G.raw.incident node).get slot
    rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
    have hleft :
        (.constructor node' slot' :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      exact hendpointEq
    have hright :
        (.constructor node slot :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      rfl
    exact hleft.trans hright.symm
  cases hownerEq
  exact ⟨hmate', hunseen', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_bud
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ left.seenNode node) :
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    ∃ (rightMateEdge :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            ((H.raw.incident rightNode).get rightSlot))
      (rightUnseen : ¬ right.seenNode rightNode),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.bud rightNode rightSlot rightMateEdge
          rightUnseen) := by
  dsimp
  let rightNode := e.nodeEquiv.toFun node
  let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((H.raw.incident rightNode).get rightSlot) := by
    have hslot :
        (H.raw.incident rightNode).get rightSlot =
          e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
      PortHypergraphIso.incidence_get_preserved e node slot
    rw [hslot]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have rightUnseen : ¬ right.seenNode rightNode := by
    intro hseen
    have hpre := hr.seen_mem_reflected hseen
    exact hunseen (by simpa [rightNode, seenNode] using hpre)
  have hconnectRight :=
    hr.firstPendingConnectSearch?_none hpending hconnect
  rcases right.firstPendingStepSearch?_some_bud_exact_of_witness
      hconnectRight rightNode rightSlot rightMateEdge rightUnseen with
    ⟨rightMateEdge', rightUnseen', hstep⟩
  exact ⟨rightMateEdge', rightUnseen', hstep⟩

end SearchState

/--
The global traversal-readiness invariant for an open representative.  It is
the missing totality statement for the owned graph-to-`Diag` search: every
nonempty ordered pending state has the constructor choice required by the
syntax.
-/
def FirstPendingTraversalReady (G : OpenPortHypergraph Sig boundary) : Prop :=
  ∀ {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : TraversalState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)},
    st.FrontierComplete →
    st.pending = active :: rest →
      FirstPendingStepReady G st.seenNode active rest

/--
Frontier completeness makes the first-pending traversal step locally total.
Initial completeness and step preservation are the remaining state-invariant
obligations for the owned graph-to-`Diag` traversal.
-/
theorem firstPendingTraversalReady_of_frontierComplete
    (G : OpenPortHypergraph Sig boundary) :
    FirstPendingTraversalReady G := by
  intro activeLabel restLabels st active rest hcomplete hpending
  rcases PortHypergraph.edgeMate_existsUnique G.raw active with
    ⟨mate, hmate, _hmateUniq⟩
  have hactiveMem : active ∈ st.pending := by
    rw [hpending]
    simp
  have hactiveUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge active) :=
    st.pending_unprocessed active hactiveMem
  have hmateUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge mate) := by
    intro hprocessed
    exact hactiveUnprocessed (by simpa [hmate.2] using hprocessed)
  have mate_pending_tail
      (hmatePending : mate ∈ st.pending) : mate ∈ rest := by
    rw [hpending] at hmatePending
    exact list_mem_tail_of_mem_cons_ne hmatePending (by
      intro hactiveMate
      exact hmate.1 hactiveMate)
  have connect_of_pending (hmatePending : mate ∈ st.pending) :
      FirstPendingStepReady G st.seenNode active rest := by
    have hrest : mate ∈ rest := mate_pending_tail hmatePending
    rcases list_exists_get_of_mem rest hrest with ⟨mateIndex, hget⟩
    refine Or.inl ⟨mateIndex, ?_⟩
    rw [hget]
    exact hmate
  rcases G.raw.endpoint_owner mate with ⟨owner, howner, _huniq⟩
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.boundary boundaryIndex) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      exact connect_of_pending
        (hcomplete mate hmateUnprocessed (.boundary boundaryIndex)
          hownerEndpoint)
  | constructor node slot =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      by_cases hseen : st.seenNode node
      · exact connect_of_pending
          (hcomplete mate hmateUnprocessed (.constructor node slot)
            hownerEndpoint hseen)
      · refine Or.inr ⟨node, slot, ?_, hseen⟩
        rw [show (G.raw.incident node).get slot = mate by
          simpa [PortHypergraph.endpointOwnerEndpoint] using hownerEndpoint]
        exact hmate

/--
A finite search state inherits first-pending step readiness from its projected
proof-level traversal state.  This still returns a `Prop`; the data-producing
search must construct `FirstPendingStep` directly.
-/
theorem SearchState.firstPendingStepReady_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
      FirstPendingStepReady G st.seenNode active rest :=
  (firstPendingTraversalReady_of_frontierComplete G)
    st.toTraversalState hcomplete hpending

theorem SearchState.firstPendingStepSearch?_exists_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step :=
  st.firstPendingStepSearch?_exists_of_ready
    (st.firstPendingStepReady_of_frontierComplete hcomplete hpending)

namespace SearchState

/--
Owned graph-to-syntax traversal from a finite search state.  The recursion
always processes the first pending endpoint.  The `none` search branch is
impossible by `firstPendingStepSearch?_exists_of_frontierComplete`, and child
recursion decreases the finite count of unprocessed edges.
-/
def toDiag {G : OpenPortHypergraph Sig boundary} :
    ∀ {frontier : List Sig.Port},
      (st : SearchState G frontier) → st.FrontierComplete → Diag Sig frontier
  | [], _st, _hcomplete => Diag.finish
  | activeLabel :: restLabels, st, hcomplete =>
      match hpending : st.pending with
      | [] =>
          False.elim (by
            have hlabels := st.pending_labels
            rw [hpending] at hlabels
            simp at hlabels)
      | active :: rest =>
          match hstep : st.firstPendingStepSearch? active rest with
          | none =>
              False.elim (by
                rcases st.firstPendingStepSearch?_exists_of_frontierComplete
                    hcomplete hpending with ⟨step, hsome⟩
                rw [hstep] at hsome
                cases hsome)
          | some step =>
              match step with
              | FirstPendingStep.connect mate hmate =>
                  Diag.connect
                    (st.restLabelIndex hpending mate)
                    (st.connect_compatible hpending mate hmate)
                    (toDiag
                      (st.connectChild hpending mate hmate)
                      (st.connectChild_frontierComplete hpending mate hmate
                        hcomplete))
              | FirstPendingStep.bud node slot hmate hunseen =>
                  Diag.bud
                    (G.raw.nodeLabel node)
                    (budEntry node slot)
                    (st.bud_compatible hpending node slot hmate)
                    (toDiag
                      (st.budChild hpending node slot hmate
                        (by simpa [seenNode] using hunseen))
                      (st.budChild_frontierComplete hpending node slot hmate
                        (by simpa [seenNode] using hunseen) hcomplete))
termination_by frontier st _hcomplete => st.remainingEdges
decreasing_by
  · exact st.connectChild_remainingEdges_lt hpending mate hmate
  · exact st.budChild_remainingEdges_lt hpending node slot hmate
      (by simpa [seenNode] using hunseen)

/-- The owned traversal result is independent of the proof of frontier
completeness supplied to it. -/
theorem toDiag_frontierComplete_irrel {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    (h₁ h₂ : st.FrontierComplete) :
    st.toDiag h₁ = st.toDiag h₂ := by
  have hproof : h₁ = h₂ := Subsingleton.elim _ _
  cases hproof
  rfl

/-- Traversal commutes with casting the frontier index of a search state. -/
theorem toDiag_cast {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier)
    (hc : st.FrontierComplete) :
    (h ▸ st).toDiag (frontierComplete_cast h st hc) =
      h ▸ st.toDiag hc := by
  cases h
  rfl

/-- Empty-frontier traversal computes to `finish`. -/
theorem toDiag_empty {G : OpenPortHypergraph Sig boundary}
    (st : SearchState G []) (hcomplete : st.FrontierComplete) :
    st.toDiag hcomplete = Diag.finish := by
  rw [SearchState.toDiag.eq_def]

/-- Connect-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_connect {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate)) :
    st.toDiag hcomplete =
      Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate)
        ((st.connectChild hpending mate hmate).toDiag
          (st.connectChild_frontierComplete hpending mate hmate hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect mate' hmate' =>
          rw [hstep] at hstep'
          injection hstep' with hconnect
          cases hconnect
          simp
      | bud _node _slot _hmate' _hunseen =>
          rw [hstep] at hstep'
          cases hstep'

/-- Bud-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_bud {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node)
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    st.toDiag hcomplete =
      Diag.bud
        (G.raw.nodeLabel node)
        (budEntry node slot)
        (st.bud_compatible hpending node slot hmate)
        ((st.budChild hpending node slot hmate
            (by simpa [seenNode] using hunseen)).toDiag
          (st.budChild_frontierComplete hpending node slot hmate
            (by simpa [seenNode] using hunseen) hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect _mate' _hmate' =>
          rw [hstep] at hstep'
          cases hstep'
      | bud _node' _slot' _hmate' _hunseen' =>
          rw [hstep] at hstep'
          injection hstep' with hbud
          cases hbud
          simp

/-- The owned graph-to-syntax traversal is invariant under related
ordered-boundary-preserving isomorphic search states. -/
theorem toDiag_isoRelated
    {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    {frontier : List Sig.Port}
    (left : SearchState G frontier) (right : SearchState H frontier)
    (hrel : IsoRelated e left right)
    (hleft : left.FrontierComplete) (hright : right.FrontierComplete) :
    left.toDiag hleft = right.toDiag hright := by
  induction frontier, left, hleft using SearchState.toDiag.induct with
  | case1 st hcomplete _hcomplete =>
      rw [toDiag_empty]
      rw [toDiag_empty]
  | case2 activeLabel restLabels active rest mate hmate st _hcomplete
      hcomplete hpending hstep _hstep ih =>
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_connect hpending mate hmate with
        ⟨rightMateEdge, hrightStep⟩
      have hchildRel :=
        hrel.connectChild_with hpending mate hmate rightMateEdge
      have hchild :=
        ih (right.connectChild hrightPending (Fin.cast (by simp) mate)
              rightMateEdge) hchildRel
          (right.connectChild_frontierComplete hrightPending
            (Fin.cast (by simp) mate) rightMateEdge hright)
      rw [toDiag_connect st hcomplete hpending mate hmate hstep]
      rw [toDiag_connect right hright hrightPending
        (Fin.cast (by simp) mate) rightMateEdge hrightStep]
      have hidx := hrel.restLabelIndex hpending mate
      cases hidx
      have hok :
          right.connect_compatible hrightPending (Fin.cast (by simp) mate)
              rightMateEdge =
            st.connect_compatible hpending mate hmate := Subsingleton.elim _ _
      cases hok
      exact congrArg (fun child => Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) child) hchild
  | case3 activeLabel restLabels active rest node slot hmate st _hcomplete
      hcomplete hpending hunseen hstep _hstep ih =>
      have hconnect :=
        st.firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud hstep
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_bud hpending hconnect node slot
          hmate hunseen with
        ⟨rightMateEdge, rightUnseen, hrightStep⟩
      let rightNode := e.nodeEquiv.toFun node
      let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
      have rightUnseenMem : rightNode ∉ right.seenNodes := by
        simpa [rightNode, seenNode] using rightUnseen
      have leftUnseenMem : node ∉ st.seenNodes := by
        simpa [seenNode] using hunseen
      have hfrontier :
          restLabels ++
              Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
                (budEntry (G := H) rightNode rightSlot) =
            restLabels ++
              Sig.nodePortsExcept (G.raw.nodeLabel node)
                (budEntry (G := G) node slot) := by
        have hentryVal := budEntry_val_preserved e node slot
        exact congrArg (fun tail => restLabels ++ tail)
          (nodePortsExcept_eq_of_val
            (e.node_label_preserved node).symm hentryVal)
      let rightChild :=
        hfrontier ▸
          right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem
      have hchildRel :
          IsoRelated e
            (st.budChild hpending node slot hmate leftUnseenMem)
            rightChild := by
        dsimp [rightChild, rightNode, rightSlot, hfrontier]
        exact hrel.budChild_with hpending node slot hmate leftUnseenMem
          rightMateEdge rightUnseenMem
      have hrightChildCompleteUncast :
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).FrontierComplete :=
        right.budChild_frontierComplete hrightPending rightNode rightSlot
          rightMateEdge rightUnseenMem hright
      have hrightChildComplete : rightChild.FrontierComplete := by
        dsimp [rightChild]
        exact frontierComplete_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchild := ih rightChild hchildRel hrightChildComplete
      rw [toDiag_bud st hcomplete hpending node slot hmate hunseen hstep]
      rw [toDiag_bud right hright hrightPending rightNode rightSlot
        rightMateEdge rightUnseen hrightStep]
      have hrightChildDiagCast :
          rightChild.toDiag hrightChildComplete =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        dsimp [rightChild, hrightChildComplete]
        exact toDiag_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchildCast :
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
              (st.budChild_frontierComplete hpending node slot hmate
                leftUnseenMem hcomplete) =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        exact hchild.trans hrightChildDiagCast
      exact Diag.bud_transport
        (hnode := (e.node_label_preserved node).symm)
        (hentryVal := budEntry_val_preserved e node slot)
        (okA := st.bud_compatible hpending node slot hmate)
        (okB := right.bud_compatible hrightPending rightNode rightSlot
          rightMateEdge)
        (childA :=
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
            (st.budChild_frontierComplete hpending node slot hmate
              leftUnseenMem hcomplete))
        (childB :=
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).toDiag hrightChildCompleteUncast)
        hfrontier hchildCast

end SearchState

def fromGraph (G : OpenPortHypergraph Sig boundary) : Diag Sig boundary :=
  (SearchState.initial G).toDiag (SearchState.initial_frontierComplete G)

namespace SearchState

/-- Semantic exhaustion for a finite search state: all constructors have been
seen and all edges have been consumed by traversal steps. -/
structure GraphExhausted {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop where
  allNodesSeen : ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes
  allEdgesProcessed : ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges

theorem pending_ne_nil_of_reachable_unprocessed
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    {endpoint : Fin G.raw.endpointCount}
    (hreach : PortHypergraph.PortReachesBoundary G.raw endpoint)
    (hunprocessed : G.raw.endpointEdge endpoint ∉ st.processedEdges) :
    st.pending ≠ [] := by
  induction hreach with
  | boundary b =>
      intro hpendingNil
      have hmem :
          G.raw.boundaryPort b ∈ st.pending :=
        hcomplete (G.raw.boundaryPort b) hunprocessed (.boundary b) rfl
      rw [hpendingNil] at hmem
      cases hmem
  | throughEdge sameEdge _different _reach ih =>
      apply ih
      intro hprocessed
      exact hunprocessed (by
        rw [← sameEdge]
        exact hprocessed)
  | throughConstructor node fromSlot toSlot hp hq _reach ih =>
      by_cases hseen : node ∈ st.seenNodes
      · intro hpendingNil
        have htoUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get toSlot) ∉
              st.processedEdges := by
          rw [hq]
          exact hunprocessed
        have hmem :
            (G.raw.incident node).get toSlot ∈ st.pending :=
          hcomplete ((G.raw.incident node).get toSlot) htoUnprocessed
            (.constructor node toSlot) rfl hseen
        rw [hpendingNil] at hmem
        cases hmem
      · have hfromUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get fromSlot) ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hseen fromSlot
        apply ih
        rw [← hp]
        exact hfromUnprocessed

theorem allNodesSeen_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes := by
  intro node
  by_cases hseen : node ∈ st.seenNodes
  · exact hseen
  · rcases G.allConstructorsReachBoundary node with ⟨slot, hreach⟩
    have hunprocessed :
        G.raw.endpointEdge ((G.raw.incident node).get slot) ∉
          st.processedEdges :=
      st.unseen_incident_unprocessed node hseen slot
    have hnonempty :=
      st.pending_ne_nil_of_reachable_unprocessed hcomplete hreach hunprocessed
    exact False.elim (hnonempty hpendingNil)

theorem allEdgesProcessed_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges := by
  intro edge
  by_cases hprocessed : edge ∈ st.processedEdges
  · exact hprocessed
  · rcases G.raw.edge_two_endpoints edge with
      ⟨left, _right, _hdiff, hleft, _hright, _hall⟩
    have hleftUnprocessed :
        G.raw.endpointEdge left ∉ st.processedEdges := by
      intro hleftProcessed
      exact hprocessed (by simpa [hleft] using hleftProcessed)
    rcases G.raw.endpoint_owner left with ⟨owner, howner, _huniq⟩
    cases owner with
    | boundary boundaryIndex =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.boundary boundaryIndex)
            hownerEndpoint
        rw [hpendingNil] at hmem
        cases hmem
    | constructor node slot =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hseen : node ∈ st.seenNodes :=
          st.allNodesSeen_of_pending_nil hcomplete hpendingNil node
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.constructor node slot)
            hownerEndpoint hseen
        rw [hpendingNil] at hmem
        cases hmem

theorem graphExhausted_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    st.GraphExhausted where
  allNodesSeen := st.allNodesSeen_of_pending_nil hcomplete hpendingNil
  allEdgesProcessed := st.allEdgesProcessed_of_pending_nil hcomplete hpendingNil

theorem pending_eq_nil_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G []) :
    st.pending = [] := by
  cases hpending : st.pending with
  | nil => rfl
  | cons active rest =>
      have hlabels := st.pending_labels
      rw [hpending] at hlabels
      simp at hlabels

theorem graphExhausted_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G [])
    (hcomplete : st.FrontierComplete) :
    st.GraphExhausted :=
  st.graphExhausted_of_pending_nil hcomplete
    st.pending_eq_nil_of_empty_frontier

end SearchState

def isoRel (G H : OpenPortHypergraph Sig boundary) : Prop :=
  Nonempty (PortHypergraphIso G.raw H.raw)

def isoSetoid (Sig : Signature) (boundary : List Sig.Port) :
    Setoid (OpenPortHypergraph Sig boundary) where
  r := isoRel
  iseqv := by
    constructor
    · intro G
      exact ⟨PortHypergraphIso.refl G.raw⟩
    · intro G H h
      rcases h with ⟨e⟩
      exact ⟨PortHypergraphIso.symm e⟩
    · intro G H K hGH hHK
      rcases hGH with ⟨eGH⟩
      rcases hHK with ⟨eHK⟩
      exact ⟨PortHypergraphIso.trans eGH eHK⟩

end OpenPortHypergraph

end StringDiagram
end BijForm
