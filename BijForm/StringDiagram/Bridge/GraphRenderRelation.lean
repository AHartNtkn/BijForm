import BijForm.StringDiagram.Bridge.SyntaxRoundTrip

namespace BijForm
namespace StringDiagram

open DepPoly

namespace OpenPortHypergraph
namespace SearchState

variable {Sig : Signature} {boundary : List Sig.Port}

/--
Constructive correspondence between a renderer prefix and traversal over an
original graph.  It records the identifier maps that align rendered endpoint,
edge, and node indices with original graph indices in traversal order; semantic
labels are tracked separately by the corresponding preservation fields.
-/
structure GraphRenderRelated (G : OpenPortHypergraph Sig boundary)
    {frontier : List Sig.Port}
    (rst : RenderState Sig frontier) (st : SearchState G frontier) : Prop where
  endpoint_nodup : (endpointOrder G st).Nodup
  edge_nodup : (edgeOrder st).Nodup
  node_nodup : (nodeOrder st).Nodup
  endpoint_length : rst.endpoints.length = (endpointOrder G st).length
  edge_length : rst.edges.length = (edgeOrder st).length
  node_length : rst.nodes.length = (nodeOrder st).length
  frontier_id_bound :
    ∀ id : Fin rst.frontierIds.length,
      rst.frontierIds.get id < rst.endpoints.length
  pending_length : rst.frontierIds.length = st.pending.length
  pending_id :
    ∀ id : Fin rst.frontierIds.length,
      (endpointOrder G st).get
          (listIndexCast (endpointOrder G st) endpoint_length
            ⟨rst.frontierIds.get id, frontier_id_bound id⟩) =
        st.pending.get (listIndexCast st.pending pending_length id)
  endpoint_label :
    ∀ endpoint : Fin rst.endpoints.length,
      rst.endpoints.get endpoint =
        G.raw.endpointLabel
          ((endpointOrder G st).get
            (listIndexCast (endpointOrder G st) endpoint_length endpoint))
  edge_label :
    ∀ edge : Fin rst.edges.length,
      (rst.edges.get edge).label =
        G.raw.edgeLabel
          ((edgeOrder st).get (listIndexCast (edgeOrder st) edge_length edge))
  edge_left_bound :
    ∀ edge : Fin rst.edges.length,
      (rst.edges.get edge).left < rst.endpoints.length
  edge_right_bound :
    ∀ edge : Fin rst.edges.length,
      (rst.edges.get edge).right < rst.endpoints.length
  edge_left :
    ∀ edge : Fin rst.edges.length,
      G.raw.endpointEdge
          ((endpointOrder G st).get
            (listIndexCast (endpointOrder G st) endpoint_length
              ⟨(rst.edges.get edge).left, edge_left_bound edge⟩)) =
        (edgeOrder st).get (listIndexCast (edgeOrder st) edge_length edge)
  edge_right :
    ∀ edge : Fin rst.edges.length,
      G.raw.endpointEdge
          ((endpointOrder G st).get
            (listIndexCast (endpointOrder G st) endpoint_length
              ⟨(rst.edges.get edge).right, edge_right_bound edge⟩)) =
        (edgeOrder st).get (listIndexCast (edgeOrder st) edge_length edge)
  node_label :
    ∀ node : Fin rst.nodes.length,
      (rst.nodes.get node).label =
        G.raw.nodeLabel
          ((nodeOrder st).get (listIndexCast (nodeOrder st) node_length node))
  node_incident_length :
    ∀ node : Fin rst.nodes.length,
      (rst.nodes.get node).incident.length =
        (G.raw.incident
          ((nodeOrder st).get
            (listIndexCast (nodeOrder st) node_length node))).length
  node_incident_bound :
    ∀ (node : Fin rst.nodes.length)
      (slot : Fin (rst.nodes.get node).incident.length),
      (rst.nodes.get node).incident.get slot < rst.endpoints.length
  node_incident :
    ∀ (node : Fin rst.nodes.length)
      (slot : Fin (rst.nodes.get node).incident.length),
      (endpointOrder G st).get
          (listIndexCast (endpointOrder G st) endpoint_length
            ⟨(rst.nodes.get node).incident.get slot,
              node_incident_bound node slot⟩) =
        (G.raw.incident
          ((nodeOrder st).get
            (listIndexCast (nodeOrder st) node_length node))).get
            (listIndexCast
              (G.raw.incident
                ((nodeOrder st).get
                  (listIndexCast (nodeOrder st) node_length node)))
              (node_incident_length node) slot)

namespace GraphRenderRelated

def endpointIndex {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (endpoint : Fin rst.endpoints.length) : Fin (endpointOrder G st).length :=
  listIndexCast (endpointOrder G st) hrel.endpoint_length endpoint

def edgeIndex {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (edge : Fin rst.edges.length) : Fin (edgeOrder st).length :=
  listIndexCast (edgeOrder st) hrel.edge_length edge

def nodeIndex {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (node : Fin rst.nodes.length) : Fin (nodeOrder st).length :=
  listIndexCast (nodeOrder st) hrel.node_length node

def nodeIncidentIndex {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (node : Fin rst.nodes.length)
    (slot : Fin (rst.nodes.get node).incident.length) :
    Fin (G.raw.incident ((nodeOrder st).get (hrel.nodeIndex node))).length :=
  listIndexCast
    (G.raw.incident ((nodeOrder st).get (hrel.nodeIndex node)))
    (by simpa [nodeIndex] using hrel.node_incident_length node)
    slot

def pendingIndex {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (id : Fin rst.frontierIds.length) : Fin st.pending.length :=
  listIndexCast st.pending hrel.pending_length id

@[simp]
theorem endpointIndex_val {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (endpoint : Fin rst.endpoints.length) :
    (hrel.endpointIndex endpoint).val = endpoint.val :=
  rfl

@[simp]
theorem edgeIndex_val {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (edge : Fin rst.edges.length) :
    (hrel.edgeIndex edge).val = edge.val :=
  rfl

@[simp]
theorem nodeIndex_val {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (node : Fin rst.nodes.length) :
    (hrel.nodeIndex node).val = node.val :=
  rfl

@[simp]
theorem nodeIncidentIndex_val {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (node : Fin rst.nodes.length)
    (slot : Fin (rst.nodes.get node).incident.length) :
    (hrel.nodeIncidentIndex node slot).val = slot.val :=
  rfl

@[simp]
theorem pendingIndex_val {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    (id : Fin rst.frontierIds.length) :
    (hrel.pendingIndex id).val = id.val :=
  rfl

structure FrontierPendingFields (G : OpenPortHypergraph Sig boundary)
    {frontier : List Sig.Port}
    (rst : RenderState Sig frontier) (st : SearchState G frontier)
    (endpoint_length : rst.endpoints.length = (endpointOrder G st).length) :
    Prop where
  frontier_id_bound :
    ∀ id : Fin rst.frontierIds.length,
      rst.frontierIds.get id < rst.endpoints.length
  pending_length : rst.frontierIds.length = st.pending.length
  pending_id :
    ∀ id : Fin rst.frontierIds.length,
      (endpointOrder G st).get
          (listIndexCast (endpointOrder G st) endpoint_length
            ⟨rst.frontierIds.get id, frontier_id_bound id⟩) =
        st.pending.get (listIndexCast st.pending pending_length id)

structure NodeIncidentFields (G : OpenPortHypergraph Sig boundary)
    {frontier : List Sig.Port}
    (rst : RenderState Sig frontier) (st : SearchState G frontier)
    (node_length : rst.nodes.length = (nodeOrder st).length) : Prop where
  node_incident_length :
    ∀ node : Fin rst.nodes.length,
      (rst.nodes.get node).incident.length =
        (G.raw.incident
          ((nodeOrder st).get
            (listIndexCast (nodeOrder st) node_length node))).length
  node_incident_bound :
    ∀ (node : Fin rst.nodes.length)
      (slot : Fin (rst.nodes.get node).incident.length),
      (rst.nodes.get node).incident.get slot < rst.endpoints.length

end GraphRenderRelated

theorem GraphRenderRelated.edge_left_of_endpoint_val
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    {endpoint : Fin rst.endpoints.length} {edge : Fin rst.edges.length}
    (hleft : endpoint.val = (rst.edges.get edge).left) :
    G.raw.endpointEdge
        ((endpointOrder G st).get
          (hrel.endpointIndex endpoint)) =
      (edgeOrder st).get (hrel.edgeIndex edge) := by
  have hendpoint :
      endpoint =
        (⟨(rst.edges.get edge).left, hrel.edge_left_bound edge⟩ :
          Fin rst.endpoints.length) :=
    fin_eq_of_val_eq hleft
  rw [hendpoint]
  exact hrel.edge_left edge

theorem GraphRenderRelated.edge_right_of_endpoint_val
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    {endpoint : Fin rst.endpoints.length} {edge : Fin rst.edges.length}
    (hright : endpoint.val = (rst.edges.get edge).right) :
    G.raw.endpointEdge
        ((endpointOrder G st).get
          (hrel.endpointIndex endpoint)) =
      (edgeOrder st).get (hrel.edgeIndex edge) := by
  have hendpoint :
      endpoint =
        (⟨(rst.edges.get edge).right, hrel.edge_right_bound edge⟩ :
          Fin rst.endpoints.length) :=
    fin_eq_of_val_eq hright
  rw [hendpoint]
  exact hrel.edge_right edge

theorem initial_graphRenderRelated
    (G : OpenPortHypergraph Sig boundary) :
    GraphRenderRelated G (RenderState.initial Sig boundary) (initial G) where
  endpoint_nodup := by
    simpa [endpointOrder, initial] using
      list_nodup_ofFn_injective G.raw.boundaryPort G.raw.boundary_injective
  edge_nodup := by
    simp [edgeOrder, initial]
  node_nodup := by
    simp [nodeOrder, initial]
  endpoint_length := by
    simp [endpointOrder, RenderState.initial, initial]
  edge_length := by
    simp [edgeOrder, RenderState.initial, initial]
  node_length := by
    simp [nodeOrder, RenderState.initial, initial]
  frontier_id_bound := by
    intro id
    simpa [RenderState.initial] using id.isLt
  pending_length := by
    simp [RenderState.initial, initial]
  pending_id := by
    intro id
    dsimp [RenderState.initial, initial, endpointOrder]
    simp
  endpoint_label := by
    intro endpoint
    dsimp [RenderState.initial, endpointOrder, initial]
    simpa using (G.raw.boundary_label endpoint).symm
  edge_label := by
    intro edge
    nomatch edge
  edge_left_bound := by
    intro edge
    nomatch edge
  edge_right_bound := by
    intro edge
    nomatch edge
  edge_left := by
    intro edge
    nomatch edge
  edge_right := by
    intro edge
    nomatch edge
  node_label := by
    intro node
    nomatch node
  node_incident_length := by
    intro node
    nomatch node
  node_incident_bound := by
    intro node
    nomatch node
  node_incident := by
    intro node
    nomatch node

theorem GraphRenderRelated.seenNodes_nodup
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st) :
    st.seenNodes.Nodup := by
  simpa [nodeOrder] using list_nodup_reverse hrel.node_nodup

theorem GraphRenderRelated.pending_cons_values
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds) :
    (endpointOrder G st).get
        (hrel.endpointIndex
          ⟨activeId, by
            have hbound := hrel.frontier_id_bound
              (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
            simpa [hids] using hbound⟩) = active ∧
      ∀ id : Fin restIds.length,
        (endpointOrder G st).get
            (hrel.endpointIndex
              ⟨restIds.get id, by
                have hbound := hrel.frontier_id_bound
                  (⟨id.val + 1, by rw [hids]; simp [id.isLt]⟩ :
                    Fin rst.frontierIds.length)
                simpa [hids] using hbound⟩) =
          rest.get (listIndexCast rest (by
            have hpendingLen := hrel.pending_length
            rw [hids, hpending] at hpendingLen
            exact Nat.succ.inj hpendingLen) id) := by
  constructor
  · have h := hrel.pending_id
      (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
    have hcast :
        (hrel.pendingIndex
            (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length) :
          Fin st.pending.length) =
        ⟨0, by rw [hpending]; simp⟩ := by
      exact fin_eq_of_val_eq rfl
    simpa [hids, hpending, hcast] using h
  · intro id
    have h := hrel.pending_id
      (⟨id.val + 1, by rw [hids]; simp [id.isLt]⟩ :
        Fin rst.frontierIds.length)
    have htailLen :
        restIds.length = rest.length := by
      have hpendingLen := hrel.pending_length
      rw [hids, hpending] at hpendingLen
      exact Nat.succ.inj hpendingLen
    have hcast :
        (hrel.pendingIndex
            (⟨id.val + 1, by rw [hids]; simp [id.isLt]⟩ :
              Fin rst.frontierIds.length) :
          Fin st.pending.length) =
        ⟨id.val + 1, by
          rw [hpending]
          simp
          rw [← htailLen]
          exact id.isLt⟩ := by
      exact fin_eq_of_val_eq rfl
    have htailCast :
        (⟨id.val, by simpa [htailLen] using id.isLt⟩ :
          Fin rest.length) =
        listIndexCast rest htailLen id := by
      exact fin_eq_of_val_eq rfl
    simpa [hids, hpending, hcast, htailCast] using h

theorem GraphRenderRelated.frontier_id_bound_of_mem
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    {id : Nat} (hmem : id ∈ rst.frontierIds) :
    id < rst.endpoints.length := by
  let idx := listIndexOfMem rst.frontierIds id hmem
  have hbound := hrel.frontier_id_bound idx
  have hget := listIndexOfMem_get rst.frontierIds id hmem
  rw [hget] at hbound
  exact hbound

theorem GraphRenderRelated.connectChild_frontierPending
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).endpoints.length =
        (endpointOrder G (st.connectChild hpending mate hmate)).length) :
    GraphRenderRelated.FrontierPendingFields G
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst)
      (st.connectChild hpending mate hmate)
      hchildEndpointLength := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  have hrestIdsLen : restIds.length = frontier.length :=
    RenderState.frontierIds_cons_tail_length rst hids
  have htailLen : restIds.length = rest.length := by
    have hlen := hrel.pending_length
    rw [hids, hpending] at hlen
    exact Nat.succ.inj hlen
  let idx : Fin restIds.length := listIndexCast restIds hrestIdsLen.symm rendererMate
  have hidxVal : idx.val = mate.val := by
    simp [idx, rendererMate, SearchState.restLabelIndex]
  have hpendingVals := hrel.pending_cons_values hpending hids
  have hchildIds :=
    Diag.connectStep_frontierIds rendererMate ok rst hids
  have hchildFrontierBound :
      ∀ id : Fin (Diag.connectStep rendererMate ok rst).frontierIds.length,
        (Diag.connectStep rendererMate ok rst).frontierIds.get id <
          (Diag.connectStep rendererMate ok rst).endpoints.length := by
    intro id
    have hmemChild :
        (Diag.connectStep rendererMate ok rst).frontierIds.get id ∈
          eraseFin restIds idx := by
      rw [← hchildIds]
      exact List.get_mem (Diag.connectStep rendererMate ok rst).frontierIds id
    have hmemRest :
        (Diag.connectStep rendererMate ok rst).frontierIds.get id ∈
          restIds :=
      mem_of_mem_eraseFin restIds idx hmemChild
    have holdMem :
        (Diag.connectStep rendererMate ok rst).frontierIds.get id ∈
          rst.frontierIds := by
      rw [hids]
      right
      exact hmemRest
    have hbound := hrel.frontier_id_bound_of_mem holdMem
    change
      (Diag.connectStep rendererMate ok rst).frontierIds.get id <
        (Diag.connectStep rendererMate ok rst).endpoints.length
    rw [Diag.connectStep_endpoints rendererMate ok rst]
    exact hbound
  have hchildPendingLen :
      (Diag.connectStep rendererMate ok rst).frontierIds.length =
        (st.connectChild hpending mate hmate).pending.length := by
    rw [hchildIds]
    exact eraseFin_length_eq_of_length_eq htailLen idx mate
  refine
    { frontier_id_bound := hchildFrontierBound
      pending_length := hchildPendingLen
      pending_id := ?_ }
  intro id
  have hmemChild :
      (Diag.connectStep rendererMate ok rst).frontierIds.get id ∈
        eraseFin restIds idx := by
    rw [← hchildIds]
    exact List.get_mem (Diag.connectStep rendererMate ok rst).frontierIds id
  have hboundChild :
      (Diag.connectStep rendererMate ok rst).frontierIds.get id <
        rst.endpoints.length := by
    have hmemRest :
        (Diag.connectStep rendererMate ok rst).frontierIds.get id ∈
          restIds :=
      mem_of_mem_eraseFin restIds idx hmemChild
    exact hrel.frontier_id_bound_of_mem (by
      rw [hids]
      right
      exact hmemRest)
  have haligned :
      ∃ hbound :
        (Diag.connectStep rendererMate ok rst).frontierIds.get id <
            rst.endpoints.length,
        (endpointOrder G st).get
            (hrel.endpointIndex
              ⟨(Diag.connectStep rendererMate ok rst).frontierIds.get id,
                hbound⟩) =
          (st.connectChild hpending mate hmate).pending.get
            (listIndexCast
              (st.connectChild hpending mate hmate).pending
              hchildPendingLen id) := by
    have hrestRel :
        IndexedListRel
          (fun raw endpoint =>
            ∃ hbound : raw < rst.endpoints.length,
              (endpointOrder G st).get
                  (hrel.endpointIndex ⟨raw, hbound⟩) =
                endpoint)
          restIds rest := by
      refine { length := htailLen, get := ?_ }
      intro n hid hrest
      refine ⟨hrel.frontier_id_bound_of_mem ?_, ?_⟩
      · rw [hids]
        right
        exact List.get_mem restIds ⟨n, hid⟩
      · have hidx :
            (⟨n, hrest⟩ : Fin rest.length) =
              listIndexCast rest htailLen ⟨n, hid⟩ := by
          exact fin_eq_of_val_eq rfl
        rw [hidx]
        exact hpendingVals.2 ⟨n, hid⟩
    have herased := hrestRel.erase idx mate hidxVal
    have hget :=
      herased.get id.val
        (by
          exact (congrArg List.length hchildIds) ▸ id.isLt)
        (by
          exact hchildPendingLen ▸ id.isLt)
    simpa [hchildIds, connectChild] using hget
  rcases haligned with ⟨hbound, hget⟩
  have hfin :
      (⟨(Diag.connectStep rendererMate ok rst).frontierIds.get id,
          hbound⟩ : Fin rst.endpoints.length) =
        ⟨(Diag.connectStep rendererMate ok rst).frontierIds.get id,
          hboundChild⟩ := by
    exact fin_eq_of_val_eq rfl
  have hendpointOrder :
      endpointOrder G (st.connectChild hpending mate hmate) =
        endpointOrder G st :=
    endpointOrder_connectChild st hpending mate hmate
  simpa [hendpointOrder, Diag.connectStep_endpoints rendererMate ok rst,
    hfin] using hget

theorem GraphRenderRelated.connectChild_edgeEndpointBounds
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds) :
    (Diag.connectStep (st.restLabelIndex hpending mate)
      (st.connect_compatible hpending mate hmate) rst).EdgeEndpointBounds := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  have hrestIdsLen : restIds.length = frontier.length :=
    RenderState.frontierIds_cons_tail_length rst hids
  let idx : Fin restIds.length := listIndexCast restIds hrestIdsLen.symm rendererMate
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hconnectRenderEdgeLeft :
      horderTrace.renderEdge.left = activeId := by
    simp [horderTrace, connectChild_orderTrace]
  have hconnectRenderEdgeRight :
      horderTrace.renderEdge.right = restIds.get idx := by
    simp [horderTrace, connectChild_orderTrace, idx, rendererMate]
  have hstepEndpointLength :
      rst.endpoints.length =
        (Diag.connectStep rendererMate ok rst).endpoints.length :=
    (congrArg List.length
      (Diag.connectStep_endpoints rendererMate ok rst)).symm
  have hleftBoundRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge _ =>
          renderEdge.left <
            (Diag.connectStep rendererMate ok rst).endpoints.length) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge _ _
      exact Nat.lt_of_lt_of_eq (hrel.edge_left_bound prefixEdge)
        hstepEndpointLength
    · intro suffixEdge _ _
      have hbound :
          activeId <
            (Diag.connectStep rendererMate ok rst).endpoints.length := by
        exact Nat.lt_of_lt_of_eq
          (by
            simpa using
              hrel.frontier_id_bound_of_mem
                (by
                  rw [hids]
                  simp))
          hstepEndpointLength
      simpa [hconnectRenderEdgeLeft] using hbound
  have hrightBoundRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge _ =>
          renderEdge.right <
            (Diag.connectStep rendererMate ok rst).endpoints.length) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge _ _
      exact Nat.lt_of_lt_of_eq (hrel.edge_right_bound prefixEdge)
        hstepEndpointLength
    · intro suffixEdge _ _
      have hbound :
          restIds.get idx <
            (Diag.connectStep rendererMate ok rst).endpoints.length := by
        exact Nat.lt_of_lt_of_eq
          (by
            simpa using
              hrel.frontier_id_bound_of_mem (by
                rw [hids]
                right
                exact List.get_mem restIds idx))
          hstepEndpointLength
      simpa [hconnectRenderEdgeRight] using hbound
  refine { left := ?_, right := ?_ }
  · intro edge
    exact AppendTraceRelation.get hleftBoundRel edge
  · intro edge
    exact AppendTraceRelation.get hrightBoundRel edge

theorem GraphRenderRelated.connectChild_nodeIncidentFields
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildNodeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).nodes.length =
        (nodeOrder (st.connectChild hpending mate hmate)).length) :
    GraphRenderRelated.NodeIncidentFields G
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst)
      (st.connectChild hpending mate hmate)
      hchildNodeLength := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  refine { node_incident_length := ?_, node_incident_bound := ?_ }
  · intro node
    let oldNode : Fin rst.nodes.length :=
      listIndexCast rst.nodes
        (congrArg List.length (Diag.connectStep_nodes rendererMate ok rst)) node
    let childNode : Fin
        (nodeOrder (st.connectChild hpending mate hmate)).length :=
      listIndexCast (nodeOrder (st.connectChild hpending mate hmate))
        hchildNodeLength node
    let oldOrderNode : Fin (nodeOrder st).length :=
      hrel.nodeIndex oldNode
    have hnodeGet :=
      Diag.connectStep_nodes_get rendererMate ok rst node
    have hnodeOrder :
        (nodeOrder (st.connectChild hpending mate hmate)).get childNode =
          (nodeOrder st).get oldOrderNode := by
      exact horderTrace.node.get_prefix_at_right_of_val_eq
        childNode oldOrderNode rfl
    calc
      ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.length =
          (rst.nodes.get oldNode).incident.length := by
        exact congrArg (fun renderNode => renderNode.incident.length) hnodeGet
      _ = (G.raw.incident ((nodeOrder st).get oldOrderNode)).length :=
          hrel.node_incident_length oldNode
      _ =
        (G.raw.incident
          ((nodeOrder (st.connectChild hpending mate hmate)).get
            childNode)).length := by
          exact congrArg (fun graphNode => (G.raw.incident graphNode).length)
            hnodeOrder.symm
  · intro node slot
    let oldNode : Fin rst.nodes.length :=
      listIndexCast rst.nodes
        (congrArg List.length (Diag.connectStep_nodes rendererMate ok rst)) node
    have hnodeGet :=
      Diag.connectStep_nodes_get rendererMate ok rst node
    let oldSlot : Fin (rst.nodes.get oldNode).incident.length :=
      listIndexCast (rst.nodes.get oldNode).incident
        (congrArg (fun renderNode => renderNode.incident.length) hnodeGet) slot
    have hincidentGet :
        ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot =
          (rst.nodes.get oldNode).incident.get oldSlot := by
      exact list_get_of_eq (congrArg RenderNode.incident hnodeGet) slot
    rw [hincidentGet]
    exact Nat.lt_of_lt_of_eq (hrel.node_incident_bound oldNode oldSlot)
      (congrArg List.length
        (Diag.connectStep_endpoints rendererMate ok rst)).symm

theorem GraphRenderRelated.connectChild_nodeIncident
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).endpoints.length =
        (endpointOrder G (st.connectChild hpending mate hmate)).length)
    (hchildNodeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).nodes.length =
        (nodeOrder (st.connectChild hpending mate hmate)).length)
    (hnodeIncidentFields :
      GraphRenderRelated.NodeIncidentFields G
        (Diag.connectStep (st.restLabelIndex hpending mate)
          (st.connect_compatible hpending mate hmate) rst)
        (st.connectChild hpending mate hmate)
        hchildNodeLength) :
    ∀ (node :
        Fin (Diag.connectStep (st.restLabelIndex hpending mate)
          (st.connect_compatible hpending mate hmate) rst).nodes.length)
      (slot :
        Fin (((Diag.connectStep (st.restLabelIndex hpending mate)
          (st.connect_compatible hpending mate hmate) rst).nodes.get node).incident.length)),
      (endpointOrder G (st.connectChild hpending mate hmate)).get
          (listIndexCast
            (endpointOrder G (st.connectChild hpending mate hmate))
            hchildEndpointLength
            ⟨((Diag.connectStep (st.restLabelIndex hpending mate)
                (st.connect_compatible hpending mate hmate) rst).nodes.get node).incident.get slot,
              hnodeIncidentFields.node_incident_bound node slot⟩) =
        (G.raw.incident
          ((nodeOrder (st.connectChild hpending mate hmate)).get
            (listIndexCast
              (nodeOrder (st.connectChild hpending mate hmate))
              hchildNodeLength node))).get
          (listIndexCast
            (G.raw.incident
              ((nodeOrder (st.connectChild hpending mate hmate)).get
                (listIndexCast
                  (nodeOrder (st.connectChild hpending mate hmate))
                  hchildNodeLength node)))
            (hnodeIncidentFields.node_incident_length node) slot) := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  intro node slot
  let oldNode : Fin rst.nodes.length :=
    listIndexCast rst.nodes
      (congrArg List.length (Diag.connectStep_nodes rendererMate ok rst)) node
  let childNode : Fin
      (nodeOrder (st.connectChild hpending mate hmate)).length :=
    listIndexCast (nodeOrder (st.connectChild hpending mate hmate))
      hchildNodeLength node
  let oldOrderNode : Fin (nodeOrder st).length :=
    hrel.nodeIndex oldNode
  have hnodeGet :=
    Diag.connectStep_nodes_get rendererMate ok rst node
  let oldSlot : Fin (rst.nodes.get oldNode).incident.length :=
    listIndexCast (rst.nodes.get oldNode).incident
      (congrArg (fun renderNode => renderNode.incident.length) hnodeGet) slot
  have hincidentGet :
      ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot =
        (rst.nodes.get oldNode).incident.get oldSlot := by
    exact list_get_of_eq (congrArg RenderNode.incident hnodeGet) slot
  have hnodeOrder :
      (nodeOrder (st.connectChild hpending mate hmate)).get childNode =
        (nodeOrder st).get oldOrderNode := by
    exact horderTrace.node.get_prefix_at_right_of_val_eq
      childNode oldOrderNode rfl
  let childEndpoint :
      Fin (endpointOrder G
        (st.connectChild hpending mate hmate)).length :=
    listIndexCast (endpointOrder G (st.connectChild hpending mate hmate))
      hchildEndpointLength
      ⟨((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot,
        hnodeIncidentFields.node_incident_bound node slot⟩
  let oldEndpoint : Fin (endpointOrder G st).length :=
    hrel.endpointIndex
      ⟨(rst.nodes.get oldNode).incident.get oldSlot,
        hrel.node_incident_bound oldNode oldSlot⟩
  have hendpoint :
      (endpointOrder G (st.connectChild hpending mate hmate)).get
          childEndpoint =
        (endpointOrder G st).get oldEndpoint := by
    exact list_get_of_eq_of_val_eq
      (endpointOrder_connectChild st hpending mate hmate)
      childEndpoint oldEndpoint
      (by simpa [childEndpoint, oldEndpoint] using hincidentGet)
  let childGraphSlot :
      Fin (G.raw.incident
        ((nodeOrder (st.connectChild hpending mate hmate)).get
          childNode)).length :=
    listIndexCast
      (G.raw.incident
        ((nodeOrder (st.connectChild hpending mate hmate)).get childNode))
      (hnodeIncidentFields.node_incident_length node) slot
  let oldGraphSlot :
      Fin (G.raw.incident ((nodeOrder st).get oldOrderNode)).length :=
    hrel.nodeIncidentIndex oldNode oldSlot
  have hgraphIncident :
      (G.raw.incident ((nodeOrder st).get oldOrderNode)).get
          oldGraphSlot =
        (G.raw.incident
          ((nodeOrder (st.connectChild hpending mate hmate)).get
            childNode)).get childGraphSlot := by
    exact (list_get_of_eq_of_val_eq
      (congrArg G.raw.incident hnodeOrder)
      childGraphSlot oldGraphSlot rfl).symm
  calc
    (endpointOrder G (st.connectChild hpending mate hmate)).get
        childEndpoint =
      (endpointOrder G st).get oldEndpoint := hendpoint
    _ =
      (G.raw.incident ((nodeOrder st).get oldOrderNode)).get
          oldGraphSlot := hrel.node_incident oldNode oldSlot
    _ =
      (G.raw.incident
      ((nodeOrder (st.connectChild hpending mate hmate)).get
          childNode)).get childGraphSlot := hgraphIncident

theorem GraphRenderRelated.connectChild_nodeLabel
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildNodeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).nodes.length =
        (nodeOrder (st.connectChild hpending mate hmate)).length) :
    ∀ node : Fin (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).nodes.length,
      ((Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).nodes.get node).label =
        G.raw.nodeLabel
          ((nodeOrder (st.connectChild hpending mate hmate)).get
            (listIndexCast
              (nodeOrder (st.connectChild hpending mate hmate))
              hchildNodeLength node)) := by
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hlabelRel :
      AppendTraceRelation horderTrace.node
        (fun renderNode graphNode =>
          renderNode.label = G.raw.nodeLabel graphNode) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixNode graphNode hval
      have hidx : graphNode = hrel.nodeIndex prefixNode := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx] using hrel.node_label prefixNode
    · intro renderNodeIdx _graphNode _hval
      exact fin_zero_elim renderNodeIdx
  intro node
  have hidx :
      horderTrace.node.rightIndex node =
        listIndexCast
          (nodeOrder (st.connectChild hpending mate hmate))
          hchildNodeLength node := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using AppendTraceRelation.get hlabelRel node

theorem GraphRenderRelated.connectChild_edgeLabel
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEdgeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length =
        (edgeOrder (st.connectChild hpending mate hmate)).length) :
    ∀ edge : Fin (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length,
      ((Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.get edge).label =
        G.raw.edgeLabel
          ((edgeOrder (st.connectChild hpending mate hmate)).get
            (listIndexCast
              (edgeOrder (st.connectChild hpending mate hmate))
              hchildEdgeLength edge)) := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hactiveLabel := (st.pending_labels_cons hpending).1
  have hlabelNew :
      Sig.portEdge activeLabel =
        G.raw.edgeLabel (G.raw.endpointEdge active) := by
    rw [← hactiveLabel]
    exact G.raw.endpoint_edge_label active
  have hlabelRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          renderEdge.label = G.raw.edgeLabel graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro oldEdge graphEdge hval
      have hidx : graphEdge = hrel.edgeIndex oldEdge := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx] using hrel.edge_label oldEdge
    · intro renderEdge graphEdge _hval
      simpa [horderTrace, connectChild_orderTrace] using hlabelNew
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast (edgeOrder (st.connectChild hpending mate hmate))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using AppendTraceRelation.get hlabelRel edge

theorem GraphRenderRelated.connectChild_edgeLeft
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).endpoints.length =
        (endpointOrder G (st.connectChild hpending mate hmate)).length)
    (hchildEdgeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length =
        (edgeOrder (st.connectChild hpending mate hmate)).length)
    (hchildEdgeBounds :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).EdgeEndpointBounds) :
    ∀ edge : Fin (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length,
      G.raw.endpointEdge
          ((endpointOrder G (st.connectChild hpending mate hmate)).get
            (listIndexCast
              (endpointOrder G (st.connectChild hpending mate hmate))
              hchildEndpointLength
              ⟨((Diag.connectStep (st.restLabelIndex hpending mate)
                    (st.connect_compatible hpending mate hmate) rst).edges.get edge).left,
                hchildEdgeBounds.left edge⟩)) =
        (edgeOrder (st.connectChild hpending mate hmate)).get
          (listIndexCast
            (edgeOrder (st.connectChild hpending mate hmate))
            hchildEdgeLength edge) := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hpendingVals := hrel.pending_cons_values hpending hids
  have hleftRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          ∀ hbound :
              renderEdge.left <
                (Diag.connectStep rendererMate ok rst).endpoints.length,
            G.raw.endpointEdge
              ((endpointOrder G (st.connectChild hpending mate hmate)).get
                (listIndexCast
                  (endpointOrder G (st.connectChild hpending mate hmate))
                  hchildEndpointLength
                  ⟨renderEdge.left, hbound⟩)) =
              graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge graphEdge hval hbound
      have hidx : graphEdge = hrel.edgeIndex prefixEdge := by
        exact fin_eq_of_val_eq hval.symm
      let childEndpoint :
          Fin (endpointOrder G
            (st.connectChild hpending mate hmate)).length :=
        listIndexCast
          (endpointOrder G (st.connectChild hpending mate hmate))
          hchildEndpointLength
          ⟨(rst.edges.get prefixEdge).left, hbound⟩
      let prefixEndpoint :
          Fin (endpointOrder G st).length :=
        hrel.endpointIndex
          ⟨(rst.edges.get prefixEdge).left, hrel.edge_left_bound prefixEdge⟩
      have hendpoint :
          (endpointOrder G (st.connectChild hpending mate hmate)).get
              childEndpoint =
            (endpointOrder G st).get prefixEndpoint := by
        exact list_get_of_eq_of_val_eq
          (endpointOrder_connectChild st hpending mate hmate)
          childEndpoint prefixEndpoint
          (by simp [childEndpoint, prefixEndpoint])
      calc
        G.raw.endpointEdge
            ((endpointOrder G (st.connectChild hpending mate hmate)).get
              childEndpoint) =
          G.raw.endpointEdge ((endpointOrder G st).get prefixEndpoint) := by
            exact congrArg G.raw.endpointEdge hendpoint
        _ = (edgeOrder st).get (hrel.edgeIndex prefixEdge) :=
            hrel.edge_left prefixEdge
        _ = (edgeOrder st).get graphEdge := by
            rw [hidx]
    · intro suffixEdge graphEdge hval hbound
      have hactiveBound : activeId < rst.endpoints.length := by
        have hbound := hrel.frontier_id_bound
          (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
        simpa [hids] using hbound
      let activeEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex ⟨activeId, hactiveBound⟩
      have hendpoint :
          (endpointOrder G (st.connectChild hpending mate hmate)).get
              (listIndexCast
                (endpointOrder G (st.connectChild hpending mate hmate))
                hchildEndpointLength
                ⟨activeId, by
                  simpa [horderTrace, connectChild_orderTrace] using
                    hbound⟩) =
            (endpointOrder G st).get activeEndpoint := by
        exact list_get_of_eq_of_val_eq
          (endpointOrder_connectChild st hpending mate hmate)
          (listIndexCast
            (endpointOrder G (st.connectChild hpending mate hmate))
            hchildEndpointLength
            ⟨activeId, by
              simpa [horderTrace, connectChild_orderTrace] using hbound⟩)
          activeEndpoint
          (by simp [activeEndpoint])
      have hcalc :
          G.raw.endpointEdge
              ((endpointOrder G (st.connectChild hpending mate hmate)).get
                (listIndexCast
                  (endpointOrder G (st.connectChild hpending mate hmate))
                  hchildEndpointLength
                  ⟨activeId, by
                    simpa [horderTrace, connectChild_orderTrace] using
                      hbound⟩)) =
            G.raw.endpointEdge active := by
        calc
          G.raw.endpointEdge
              ((endpointOrder G
                (st.connectChild hpending mate hmate)).get
                  (listIndexCast
                    (endpointOrder G (st.connectChild hpending mate hmate))
                    hchildEndpointLength
                    ⟨activeId, by
                      simpa [horderTrace, connectChild_orderTrace] using
                        hbound⟩)) =
            G.raw.endpointEdge ((endpointOrder G st).get activeEndpoint) := by
              exact congrArg G.raw.endpointEdge hendpoint
          _ = G.raw.endpointEdge active := by
              exact congrArg G.raw.endpointEdge hpendingVals.1
      simpa [horderTrace, connectChild_orderTrace] using hcalc
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast (edgeOrder (st.connectChild hpending mate hmate))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using
    (AppendTraceRelation.get hleftRel edge) (hchildEdgeBounds.left edge)

theorem GraphRenderRelated.connectChild_edgeRight
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).endpoints.length =
        (endpointOrder G (st.connectChild hpending mate hmate)).length)
    (hchildEdgeLength :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length =
        (edgeOrder (st.connectChild hpending mate hmate)).length)
    (hchildEdgeBounds :
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).EdgeEndpointBounds) :
    ∀ edge : Fin (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst).edges.length,
      G.raw.endpointEdge
          ((endpointOrder G (st.connectChild hpending mate hmate)).get
            (listIndexCast
              (endpointOrder G (st.connectChild hpending mate hmate))
              hchildEndpointLength
              ⟨((Diag.connectStep (st.restLabelIndex hpending mate)
                    (st.connect_compatible hpending mate hmate) rst).edges.get edge).right,
                hchildEdgeBounds.right edge⟩)) =
        (edgeOrder (st.connectChild hpending mate hmate)).get
          (listIndexCast
            (edgeOrder (st.connectChild hpending mate hmate))
            hchildEdgeLength edge) := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  have hrestIdsLen : restIds.length = frontier.length :=
    RenderState.frontierIds_cons_tail_length rst hids
  have htailLen : restIds.length = rest.length := by
    have hlen := hrel.pending_length
    rw [hids, hpending] at hlen
    exact Nat.succ.inj hlen
  let idx : Fin restIds.length := listIndexCast restIds hrestIdsLen.symm rendererMate
  have hidxVal : idx.val = mate.val := by
    simp [idx, rendererMate, SearchState.restLabelIndex]
  let horderTrace :=
    connectChild_orderTrace rst st hpending mate hmate hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hpendingVals := hrel.pending_cons_values hpending hids
  have hrightRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          ∀ hbound :
              renderEdge.right <
                (Diag.connectStep rendererMate ok rst).endpoints.length,
            G.raw.endpointEdge
              ((endpointOrder G (st.connectChild hpending mate hmate)).get
                (listIndexCast
                  (endpointOrder G (st.connectChild hpending mate hmate))
                  hchildEndpointLength
                  ⟨renderEdge.right, hbound⟩)) =
              graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge graphEdge hval hbound
      have hidx : graphEdge = hrel.edgeIndex prefixEdge := by
        exact fin_eq_of_val_eq hval.symm
      let childEndpoint :
          Fin (endpointOrder G
            (st.connectChild hpending mate hmate)).length :=
        listIndexCast
          (endpointOrder G (st.connectChild hpending mate hmate))
          hchildEndpointLength
          ⟨(rst.edges.get prefixEdge).right, hbound⟩
      let prefixEndpoint :
          Fin (endpointOrder G st).length :=
        hrel.endpointIndex
          ⟨(rst.edges.get prefixEdge).right, hrel.edge_right_bound prefixEdge⟩
      have hendpoint :
          (endpointOrder G (st.connectChild hpending mate hmate)).get
              childEndpoint =
            (endpointOrder G st).get prefixEndpoint := by
        exact list_get_of_eq_of_val_eq
          (endpointOrder_connectChild st hpending mate hmate)
          childEndpoint prefixEndpoint
          (by simp [childEndpoint, prefixEndpoint])
      calc
        G.raw.endpointEdge
            ((endpointOrder G (st.connectChild hpending mate hmate)).get
              childEndpoint) =
          G.raw.endpointEdge ((endpointOrder G st).get prefixEndpoint) := by
            exact congrArg G.raw.endpointEdge hendpoint
        _ = (edgeOrder st).get (hrel.edgeIndex prefixEdge) :=
            hrel.edge_right prefixEdge
        _ = (edgeOrder st).get graphEdge := by
            rw [hidx]
    · intro suffixEdge graphEdge hval hbound
      have hmateIdx : listIndexCast rest htailLen idx = mate := by
        exact fin_eq_of_val_eq hidxVal
      have hrestBound :
          restIds.get idx < rst.endpoints.length :=
        hrel.frontier_id_bound_of_mem (by
          rw [hids]
          right
          exact List.get_mem restIds idx)
      let restEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex ⟨restIds.get idx, hrestBound⟩
      have hrightEndpoint :
          (endpointOrder G st).get restEndpoint =
            rest.get mate := by
        simpa [restEndpoint, hmateIdx] using hpendingVals.2 idx
      have hendpoint :
          (endpointOrder G (st.connectChild hpending mate hmate)).get
              (listIndexCast
                (endpointOrder G (st.connectChild hpending mate hmate))
                hchildEndpointLength
                ⟨restIds.get idx, by
                  simpa [horderTrace, connectChild_orderTrace, idx,
                    rendererMate] using hbound⟩) =
            (endpointOrder G st).get restEndpoint := by
        exact list_get_of_eq_of_val_eq
          (endpointOrder_connectChild st hpending mate hmate)
          (listIndexCast
            (endpointOrder G (st.connectChild hpending mate hmate))
            hchildEndpointLength
            ⟨restIds.get idx, by
              simpa [horderTrace, connectChild_orderTrace, idx, rendererMate]
                using hbound⟩)
          restEndpoint
          (by simp [restEndpoint])
      have hcalc :
          G.raw.endpointEdge
              ((endpointOrder G (st.connectChild hpending mate hmate)).get
                (listIndexCast
                  (endpointOrder G (st.connectChild hpending mate hmate))
                  hchildEndpointLength
                  ⟨restIds.get idx, by
                    simpa [horderTrace, connectChild_orderTrace, idx,
                      rendererMate] using hbound⟩)) =
            G.raw.endpointEdge active := by
        calc
          G.raw.endpointEdge
              ((endpointOrder G
                (st.connectChild hpending mate hmate)).get
                  (listIndexCast
                    (endpointOrder G (st.connectChild hpending mate hmate))
                    hchildEndpointLength
                    ⟨restIds.get idx, by
                      simpa [horderTrace, connectChild_orderTrace, idx,
                        rendererMate] using hbound⟩)) =
            G.raw.endpointEdge ((endpointOrder G st).get restEndpoint) := by
              exact congrArg G.raw.endpointEdge hendpoint
          _ = G.raw.endpointEdge (rest.get mate) := by
              exact congrArg G.raw.endpointEdge hrightEndpoint
          _ = G.raw.endpointEdge active := hmate.2.symm
      simpa [horderTrace, connectChild_orderTrace, idx, rendererMate] using
        hcalc
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast (edgeOrder (st.connectChild hpending mate hmate))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using
    (AppendTraceRelation.get hrightRel edge) (hchildEdgeBounds.right edge)

theorem GraphRenderRelated.connectChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    GraphRenderRelated G
      (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst)
      (st.connectChild hpending mate hmate) := by
  let rendererMate := st.restLabelIndex hpending mate
  let ok := st.connect_compatible hpending mate hmate
  cases hids : rst.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil rst hids)
  | cons activeId restIds =>
      have hchildEndpointLength :
          (Diag.connectStep rendererMate ok rst).endpoints.length =
            (endpointOrder G (st.connectChild hpending mate hmate)).length := by
        rw [Diag.connectStep_endpoints rendererMate ok rst,
          endpointOrder_connectChild st hpending mate hmate]
        exact hrel.endpoint_length
      have hchildEdgeLength :
          (Diag.connectStep rendererMate ok rst).edges.length =
            (edgeOrder (st.connectChild hpending mate hmate)).length := by
        rw [Diag.connectStep_edges_length rendererMate ok rst,
          edgeOrder_connectChild st hpending mate hmate]
        simp [hrel.edge_length]
      have hchildNodeLength :
          (Diag.connectStep rendererMate ok rst).nodes.length =
            (nodeOrder (st.connectChild hpending mate hmate)).length := by
        rw [Diag.connectStep_nodes rendererMate ok rst,
          nodeOrder_connectChild st hpending mate hmate]
        exact hrel.node_length
      let hfrontierPending :=
        hrel.connectChild_frontierPending hpending mate hmate hids
          hchildEndpointLength
      let hchildEdgeBounds :=
        hrel.connectChild_edgeEndpointBounds hpending mate hmate hids
      let hnodeIncidentFields :=
        hrel.connectChild_nodeIncidentFields hpending mate hmate hids
          hchildNodeLength
      let hnodeIncident :=
        hrel.connectChild_nodeIncident hpending mate hmate hids
          hchildEndpointLength hchildNodeLength hnodeIncidentFields
      refine
        { endpoint_nodup := ?_
          edge_nodup := ?_
          node_nodup := ?_
          endpoint_length := ?_
          edge_length := ?_
          node_length := ?_
          frontier_id_bound := ?_
          pending_length := ?_
          pending_id := ?_
          endpoint_label := ?_
          edge_label := ?_
          edge_left_bound := ?_
          edge_right_bound := ?_
          edge_left := ?_
          edge_right := ?_
          node_label := ?_
          node_incident_length := ?_
          node_incident_bound := ?_
          node_incident := ?_ }
      · simpa [endpointOrder_connectChild st hpending mate hmate] using
          hrel.endpoint_nodup
      · rw [edgeOrder_connectChild st hpending mate hmate]
        exact edgeOrder_append_active_nodup st (by rw [hpending]; simp)
      · simpa [nodeOrder_connectChild st hpending mate hmate] using
          hrel.node_nodup
      · exact hchildEndpointLength
      · exact hchildEdgeLength
      · exact hchildNodeLength
      · exact hfrontierPending.frontier_id_bound
      · exact hfrontierPending.pending_length
      · exact hfrontierPending.pending_id
      · intro endpoint
        have hendpointGet :=
          Diag.connectStep_endpoints_get rendererMate ok rst endpoint
        rw [hendpointGet]
        simpa [endpointOrder_connectChild st hpending mate hmate] using
          hrel.endpoint_label
            (listIndexCast rst.endpoints
              (congrArg List.length
                (Diag.connectStep_endpoints rendererMate ok rst))
              endpoint)
      · intro edge
        exact hrel.connectChild_edgeLabel hpending mate hmate hids
          hchildEdgeLength edge
      · exact hchildEdgeBounds.left
      · exact hchildEdgeBounds.right
      · intro edge
        exact hrel.connectChild_edgeLeft hpending mate hmate hids
          hchildEndpointLength hchildEdgeLength hchildEdgeBounds edge
      · intro edge
        exact hrel.connectChild_edgeRight hpending mate hmate hids
          hchildEndpointLength hchildEdgeLength hchildEdgeBounds edge
      · intro node
        exact hrel.connectChild_nodeLabel hpending mate hmate hids
          hchildNodeLength node
      · intro node
        exact hnodeIncidentFields.node_incident_length node
      · intro node slot
        exact hnodeIncidentFields.node_incident_bound node slot
      · intro node slot
        exact hnodeIncident node slot

theorem GraphRenderRelated.budChild_frontierPending
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    (rv : rst.ValidIds)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length =
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length) :
    GraphRenderRelated.FrontierPendingFields G
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst)
      (st.budChild hpending node slot hmate hunseen)
      hchildEndpointLength := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  have htailLen : restIds.length = rest.length := by
    have hlen := hrel.pending_length
    rw [hids, hpending] at hlen
    exact Nat.succ.inj hlen
  let nodeEndpoints := Diag.freshNodeEndpoints rst.nextEndpoint
    (Sig.arity renderNode)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints
      (by simp [nodeEndpoints, Diag.freshNodeEndpoints, renderNode]) entry
  have hpendingVals := hrel.pending_cons_values hpending hids
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hchildIds :=
    Diag.budStep_frontierIds renderNode entry ok rst hids
  have hchildFrontierBound :
      ∀ id : Fin (Diag.budStep renderNode entry ok rst).frontierIds.length,
        (Diag.budStep renderNode entry ok rst).frontierIds.get id <
          (Diag.budStep renderNode entry ok rst).endpoints.length := by
    intro id
    have hmem :
        (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
          restIds ++ eraseFin nodeEndpoints entryIdx := by
      rw [← hchildIds]
      exact List.get_mem (Diag.budStep renderNode entry ok rst).frontierIds id
    rcases List.mem_append.mp hmem with hold | hnew
    · have holdMem :
          (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
            rst.frontierIds := by
        rw [hids]
        right
        exact hold
      have hbound := hrel.frontier_id_bound_of_mem holdMem
      change
        (Diag.budStep renderNode entry ok rst).frontierIds.get id <
          (Diag.budStep renderNode entry ok rst).endpoints.length
      rw [Diag.budStep_endpoints_length renderNode entry ok rst]
      omega
    · have hfresh :
          (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
            nodeEndpoints :=
        mem_of_mem_eraseFin nodeEndpoints entryIdx hnew
      have hbound := Diag.freshNodeEndpoints_mem_lt hfresh
      change
        (Diag.budStep renderNode entry ok rst).frontierIds.get id <
          (Diag.budStep renderNode entry ok rst).endpoints.length
      rw [Diag.budStep_endpoints_length renderNode entry ok rst]
      simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using hbound
  have hchildPendingLen :
      (Diag.budStep renderNode entry ok rst).frontierIds.length =
        (st.budChild hpending node slot hmate hunseen).pending.length := by
    rw [hchildIds]
    simp [SearchState.budChild, eraseFin_length, htailLen,
      renderNode, G.raw.incident_length node]
  refine
    { frontier_id_bound := hchildFrontierBound
      pending_length := hchildPendingLen
      pending_id := ?_ }
  intro id
  have hnodeEndpointsLen :
      nodeEndpoints.length = (G.raw.incident node).length := by
    simp [nodeEndpoints, renderNode, G.raw.incident_length node]
  have hentryIdxVal : entryIdx.val = slot.val := by
    simp [entryIdx, entry, SearchState.budEntry, nodeEndpoints,
      renderNode, Signature.nodePortIndexOfLength]
  let R := fun raw endpoint =>
    ∃ hbound : raw < (Diag.budStep renderNode entry ok rst).endpoints.length,
      (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
          (endpointOrderIndex
            (st.budChild hpending node slot hmate hunseen)
            hchildEndpointLength ⟨raw, hbound⟩) =
        endpoint
  have hleftRel : IndexedListRel R restIds rest := by
    refine { length := htailLen, get := ?_ }
    intro n hid hrest
    have holdBound :
        restIds.get ⟨n, hid⟩ < rst.endpoints.length :=
      hrel.frontier_id_bound_of_mem (by
        rw [hids]
        right
        exact List.get_mem restIds ⟨n, hid⟩)
    have hchildBound :
        restIds.get ⟨n, hid⟩ <
          (Diag.budStep renderNode entry ok rst).endpoints.length := by
      rw [Diag.budStep_endpoints_length renderNode entry ok rst]
      omega
    refine ⟨hchildBound, ?_⟩
    have hold :
        (endpointOrder G st).get
            (hrel.endpointIndex
              ⟨restIds.get ⟨n, hid⟩, holdBound⟩) =
          rest.get ⟨n, hrest⟩ := by
      have hidx :
          (⟨n, hrest⟩ : Fin rest.length) =
            listIndexCast rest htailLen ⟨n, hid⟩ := by
        exact fin_eq_of_val_eq rfl
      rw [hidx]
      exact hpendingVals.2 ⟨n, hid⟩
    let childEndpoint :
        Fin (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length :=
      endpointOrderIndex
        (st.budChild hpending node slot hmate hunseen)
        hchildEndpointLength
        ⟨restIds.get ⟨n, hid⟩, hchildBound⟩
    let oldEndpoint : Fin (endpointOrder G st).length :=
      hrel.endpointIndex
        ⟨restIds.get ⟨n, hid⟩, holdBound⟩
    have hchildOld :
        (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
            childEndpoint =
          (endpointOrder G st).get oldEndpoint :=
      horderTrace.endpoint.get_prefix_at_right_of_val_eq
        childEndpoint oldEndpoint (by simp [childEndpoint, oldEndpoint])
    exact hchildOld.trans hold
  have hrightRel :
      IndexedListRel R nodeEndpoints (G.raw.incident node) := by
    refine { length := hnodeEndpointsLen, get := ?_ }
    intro n hid hincident
    have hfreshMem :
        nodeEndpoints.get ⟨n, hid⟩ ∈ nodeEndpoints :=
      List.get_mem nodeEndpoints ⟨n, hid⟩
    have hfreshLt := Diag.freshNodeEndpoints_mem_lt hfreshMem
    have hchildBound :
        nodeEndpoints.get ⟨n, hid⟩ <
          (Diag.budStep renderNode entry ok rst).endpoints.length := by
      rw [Diag.budStep_endpoints_length renderNode entry ok rst]
      simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using hfreshLt
    refine ⟨hchildBound, ?_⟩
    let childEndpoint :
        Fin (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length :=
      endpointOrderIndex
        (st.budChild hpending node slot hmate hunseen)
        hchildEndpointLength
        ⟨nodeEndpoints.get ⟨n, hid⟩, hchildBound⟩
    let incidentEndpoint : Fin (G.raw.incident node).length :=
      ⟨n, hincident⟩
    have holdLen :
        (endpointOrder G st).length = rst.endpoints.length :=
      hrel.endpoint_length.symm
    have hle :
        (endpointOrder G st).length ≤ childEndpoint.val := by
      have hfreshGe := Diag.freshNodeEndpoints_mem_ge hfreshMem
      rw [holdLen]
      simpa [childEndpoint, nodeEndpoints, rv.nextEndpoint_eq] using
        hfreshGe
    have hsub :
        childEndpoint.val - (endpointOrder G st).length =
          incidentEndpoint.val := by
      rw [holdLen]
      simpa [childEndpoint, incidentEndpoint, nodeEndpoints] using
        Diag.freshNodeEndpoints_get_sub_of_eq
          (start := rst.nextEndpoint)
          (base := rst.endpoints.length)
          (arity := Sig.arity renderNode)
          rv.nextEndpoint_eq ⟨n, hid⟩
    exact horderTrace.endpoint.get_suffix_at_right_of_val_eq
      childEndpoint incidentEndpoint hle hsub
  have herasedRight := hrightRel.erase entryIdx slot hentryIdxVal
  let appendIndex : Fin (restIds ++ eraseFin nodeEndpoints entryIdx).length :=
    ⟨id.val, by
      have hlen :=
        congrArg List.length hchildIds
      exact Nat.lt_of_lt_of_eq id.isLt hlen⟩
  let pendingIndex : Fin (rest ++ eraseFin (G.raw.incident node) slot).length :=
    ⟨id.val, by
      have hlen :
          (Diag.budStep renderNode entry ok rst).frontierIds.length =
            (rest ++ eraseFin (G.raw.incident node) slot).length := by
        rw [hchildPendingLen]
        simp [SearchState.budChild]
      exact Nat.lt_of_lt_of_eq id.isLt hlen⟩
  have hall := hleftRel.append herasedRight
  rcases hall.get id.val appendIndex.isLt pendingIndex.isLt with
    ⟨hbound, hget⟩
  have hrawEq :
      (restIds ++ eraseFin nodeEndpoints entryIdx).get appendIndex =
        (Diag.budStep renderNode entry ok rst).frontierIds.get id := by
    exact (list_get_of_eq_of_val_eq hchildIds id appendIndex
      (by simp [appendIndex])).symm
  have htargetBound :=
    hchildFrontierBound id
  have hpendingIndex :
      (st.budChild hpending node slot hmate hunseen).pending.get
          (listIndexCast
            (st.budChild hpending node slot hmate hunseen).pending
            hchildPendingLen id) =
        (rest ++ eraseFin (G.raw.incident node) slot).get pendingIndex := by
    simp [listIndexCast, SearchState.budChild, pendingIndex]
  have hendpointIndex :
      listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨(Diag.budStep renderNode entry ok rst).frontierIds.get id,
            htargetBound⟩ =
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨(restIds ++ eraseFin nodeEndpoints entryIdx).get appendIndex,
            hbound⟩ := by
    exact fin_eq_of_val_eq hrawEq.symm
  rw [hendpointIndex]
  rw [hpendingIndex]
  exact hget

theorem GraphRenderRelated.budChild_nodeIncidentFields
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    (rv : rst.ValidIds)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildNodeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).nodes.length =
        (nodeOrder (st.budChild hpending node slot hmate hunseen)).length) :
    GraphRenderRelated.NodeIncidentFields G
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst)
      (st.budChild hpending node slot hmate hunseen)
      hchildNodeLength := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  have hchildValid :
      (Diag.budStep renderNode entry ok rst).ValidIds :=
    Diag.budStep_validIds renderNode entry ok rst rv
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hlengthRel :
      AppendTraceRelation horderTrace.node
        (fun renderNode graphNode =>
          renderNode.incident.length =
            (G.raw.incident graphNode).length) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixNode graphNode hval
      have hidx : graphNode = hrel.nodeIndex prefixNode := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx, nodeIndex] using hrel.node_incident_length prefixNode
    · intro suffixNode graphNode hval
      simpa [horderTrace, budChild_orderTrace, Diag.freshNodeEndpoints,
        renderNode] using (G.raw.incident_length node).symm
  refine { node_incident_length := ?_, node_incident_bound := ?_ }
  · intro renderIdx
    have hidx :
        horderTrace.node.rightIndex renderIdx =
          listIndexCast
            (nodeOrder (st.budChild hpending node slot hmate hunseen))
            hchildNodeLength renderIdx := by
      exact fin_eq_of_val_eq rfl
    simpa [hidx] using AppendTraceRelation.get hlengthRel renderIdx
  · intro renderIdx renderSlot
    exact hchildValid.node_incident_bound
      ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx)
      (List.get_mem (Diag.budStep renderNode entry ok rst).nodes renderIdx)
      renderSlot

theorem GraphRenderRelated.budChild_nodeIncident
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    (rv : rst.ValidIds)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length =
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length)
    (hchildNodeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).nodes.length =
        (nodeOrder (st.budChild hpending node slot hmate hunseen)).length)
    (hnodeIncidentFields :
      GraphRenderRelated.NodeIncidentFields G
        (Diag.budStep (G.raw.nodeLabel node)
          (SearchState.budEntry (G := G) node slot)
          (st.bud_compatible hpending node slot hmate) rst)
        (st.budChild hpending node slot hmate hunseen)
        hchildNodeLength) :
    ∀ (renderIdx :
        Fin (Diag.budStep (G.raw.nodeLabel node)
          (SearchState.budEntry (G := G) node slot)
          (st.bud_compatible hpending node slot hmate) rst).nodes.length)
      (renderSlot :
        Fin (((Diag.budStep (G.raw.nodeLabel node)
          (SearchState.budEntry (G := G) node slot)
          (st.bud_compatible hpending node slot hmate) rst).nodes.get renderIdx).incident.length)),
      (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
          (listIndexCast
            (endpointOrder G (st.budChild hpending node slot hmate hunseen))
            hchildEndpointLength
            ⟨((Diag.budStep (G.raw.nodeLabel node)
                (SearchState.budEntry (G := G) node slot)
                (st.bud_compatible hpending node slot hmate) rst).nodes.get
                  renderIdx).incident.get renderSlot,
              hnodeIncidentFields.node_incident_bound renderIdx renderSlot⟩) =
        (G.raw.incident
          ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
            (listIndexCast
              (nodeOrder (st.budChild hpending node slot hmate hunseen))
              hchildNodeLength renderIdx))).get
          (listIndexCast
            (G.raw.incident
              ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                (listIndexCast
                  (nodeOrder (st.budChild hpending node slot hmate hunseen))
                  hchildNodeLength renderIdx)))
            (hnodeIncidentFields.node_incident_length renderIdx) renderSlot) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let nodeEndpoints := Diag.freshNodeEndpoints rst.nextEndpoint
    (Sig.arity renderNode)
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hincidentRel :
      AppendTraceRelation horderTrace.node
        (fun rendered graphNode =>
          ∀ (renderSlot : Fin rendered.incident.length)
            (hbound :
              rendered.incident.get renderSlot <
                (Diag.budStep renderNode entry ok rst).endpoints.length)
            (hlen :
              rendered.incident.length =
                (G.raw.incident graphNode).length),
            (endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).get
                (listIndexCast
                  (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                  hchildEndpointLength
                  ⟨rendered.incident.get renderSlot, hbound⟩) =
              (G.raw.incident graphNode).get
                (listIndexCast (G.raw.incident graphNode)
                  hlen renderSlot)) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixNode graphNode hval renderSlot hbound hlen
      have hidx : graphNode = hrel.nodeIndex prefixNode := by
        exact fin_eq_of_val_eq hval.symm
      let childEndpoint :
          Fin (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).length :=
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨(rst.nodes.get prefixNode).incident.get renderSlot, hbound⟩
      let prefixEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex
          ⟨(rst.nodes.get prefixNode).incident.get renderSlot,
            hrel.node_incident_bound prefixNode renderSlot⟩
      have hendpoint :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (endpointOrder G st).get prefixEndpoint := by
        exact horderTrace.endpoint.get_prefix_at_right_of_val_eq
          childEndpoint prefixEndpoint
          (by simp [childEndpoint, prefixEndpoint])
      calc
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).get
            childEndpoint =
          (endpointOrder G st).get prefixEndpoint := hendpoint
        _ =
          (G.raw.incident
            ((nodeOrder st).get (hrel.nodeIndex prefixNode))).get
              (hrel.nodeIncidentIndex prefixNode renderSlot) := by
            simpa [nodeIndex] using hrel.node_incident prefixNode renderSlot
        _ =
          (G.raw.incident ((nodeOrder st).get graphNode)).get
              (listIndexCast (G.raw.incident ((nodeOrder st).get graphNode))
                hlen renderSlot) := by
            simp [hidx, nodeIndex, nodeIncidentIndex]
    · intro suffixNode graphNode hval renderSlot hbound hlen
      let freshSlot : Fin nodeEndpoints.length :=
        listIndexCast nodeEndpoints (by
          simp [horderTrace, budChild_orderTrace, nodeEndpoints,
            renderNode])
          renderSlot
      have hnodeBound :
          nodeEndpoints.get freshSlot <
            (Diag.budStep renderNode entry ok rst).endpoints.length := by
        simpa [freshSlot, horderTrace, budChild_orderTrace, nodeEndpoints,
          renderNode] using hbound
      let childEndpoint :
          Fin (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).length :=
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨nodeEndpoints.get freshSlot, hnodeBound⟩
      have hrawGe : rst.endpoints.length ≤ nodeEndpoints.get freshSlot := by
        have hfreshMem :
            nodeEndpoints.get freshSlot ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints freshSlot
        have hfreshGe := Diag.freshNodeEndpoints_mem_ge hfreshMem
        simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using hfreshGe
      let graphSlot : Fin (G.raw.incident node).length :=
        ⟨freshSlot.val, by
          have hslot : freshSlot.val < Sig.arity renderNode := by
            simpa [nodeEndpoints, Diag.freshNodeEndpoints] using
              freshSlot.isLt
          rw [G.raw.incident_length node]
          exact hslot⟩
      have hendpointRaw :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (G.raw.incident node).get graphSlot := by
        exact horderTrace.endpoint.get_suffix_at_right_of_val_eq
          childEndpoint graphSlot
          (by
            have holdLen :
                (endpointOrder G st).length = rst.endpoints.length :=
              hrel.endpoint_length.symm
            rw [holdLen]
            simpa [childEndpoint] using hrawGe)
          (by
            have holdLen :
                (endpointOrder G st).length = rst.endpoints.length :=
              hrel.endpoint_length.symm
            rw [holdLen]
            exact (Diag.freshNodeEndpoints_get_sub_of_eq
              (start := rst.nextEndpoint)
              (base := rst.endpoints.length)
              (arity := Sig.arity renderNode)
              rv.nextEndpoint_eq freshSlot).trans rfl)
      have hgraphSlotGet :
          (G.raw.incident node).get graphSlot =
            (G.raw.incident ([node].get graphNode)).get
              (listIndexCast (G.raw.incident ([node].get graphNode))
                hlen renderSlot) := by
        cases graphNode with
        | mk graphNodeVal graphNodeLt =>
            have hlt : graphNodeVal < 1 := by
              simpa using graphNodeLt
            have hval : graphNodeVal = 0 := by
              omega
            subst graphNodeVal
            simp [freshSlot, graphSlot]
      simpa [horderTrace, budChild_orderTrace, nodeEndpoints, renderNode,
        freshSlot, childEndpoint] using hendpointRaw.trans hgraphSlotGet
  intro renderIdx renderSlot
  have hnodeIdx :
      horderTrace.node.rightIndex renderIdx =
        listIndexCast
          (nodeOrder (st.budChild hpending node slot hmate hunseen))
          hchildNodeLength renderIdx := by
    exact fin_eq_of_val_eq rfl
  have hlen :
      ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.length =
        (G.raw.incident
          ((nodeOrder
            (st.budChild hpending node slot hmate hunseen)).get
              (horderTrace.node.rightIndex renderIdx))).length := by
    simpa [hnodeIdx] using
      hnodeIncidentFields.node_incident_length renderIdx
  simpa [hnodeIdx] using
    (AppendTraceRelation.get hincidentRel renderIdx)
      renderSlot
      (hnodeIncidentFields.node_incident_bound renderIdx renderSlot)
      hlen

theorem GraphRenderRelated.budChild_endpointLabel
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length =
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length) :
    ∀ endpoint : Fin (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length,
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.get endpoint =
        G.raw.endpointLabel
          ((endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              (listIndexCast
                (endpointOrder G
                  (st.budChild hpending node slot hmate hunseen))
                hchildEndpointLength endpoint)) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hendpointRel :
      AppendTraceRelation horderTrace.endpoint
        (fun renderEndpoint graphEndpoint =>
          renderEndpoint = G.raw.endpointLabel graphEndpoint) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEndpoint graphEndpoint hval
      have hidx : graphEndpoint = hrel.endpointIndex prefixEndpoint := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx] using hrel.endpoint_label prefixEndpoint
    · intro suffixPort suffixEndpoint hval
      have hinc := G.raw.incidence_label node suffixEndpoint
      simpa [Signature.nodePorts, renderNode, hval] using hinc.symm
  intro endpoint
  have hidx :
      horderTrace.endpoint.rightIndex endpoint =
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength endpoint := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using AppendTraceRelation.get hendpointRel endpoint

theorem GraphRenderRelated.budChild_edgeLabel
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEdgeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length =
        (edgeOrder (st.budChild hpending node slot hmate hunseen)).length) :
    ∀ edge : Fin (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length,
      ((Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.get edge).label =
        G.raw.edgeLabel
          ((edgeOrder (st.budChild hpending node slot hmate hunseen)).get
            (listIndexCast
              (edgeOrder (st.budChild hpending node slot hmate hunseen))
              hchildEdgeLength edge)) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hactiveLabel := (st.pending_labels_cons hpending).1
  have hlabelNew :
      Sig.portEdge activeLabel =
        G.raw.edgeLabel (G.raw.endpointEdge active) := by
    rw [← hactiveLabel]
    exact G.raw.endpoint_edge_label active
  have hlabelRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          renderEdge.label = G.raw.edgeLabel graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro oldEdge graphEdge hval
      have hidx : graphEdge = hrel.edgeIndex oldEdge := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx] using hrel.edge_label oldEdge
    · intro renderEdge graphEdge _hval
      simpa [horderTrace, budChild_orderTrace] using hlabelNew
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast
          (edgeOrder (st.budChild hpending node slot hmate hunseen))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using AppendTraceRelation.get hlabelRel edge

theorem GraphRenderRelated.budChild_edgeLeft
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildEndpointLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length =
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length)
    (hchildEdgeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length =
        (edgeOrder (st.budChild hpending node slot hmate hunseen)).length)
    (hchildEdgeBounds :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).EdgeEndpointBounds) :
    ∀ edge : Fin (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length,
      G.raw.endpointEdge
          ((endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              (listIndexCast
                (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                hchildEndpointLength
                ⟨((Diag.budStep (G.raw.nodeLabel node)
                    (SearchState.budEntry (G := G) node slot)
                    (st.bud_compatible hpending node slot hmate) rst).edges.get edge).left,
                  hchildEdgeBounds.left edge⟩)) =
        (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
          (listIndexCast
            (edgeOrder (st.budChild hpending node slot hmate hunseen))
            hchildEdgeLength edge) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hpendingVals := hrel.pending_cons_values hpending hids
  have hleftRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          ∀ hbound :
              renderEdge.left <
                (Diag.budStep renderNode entry ok rst).endpoints.length,
            G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  (listIndexCast
                    (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                    hchildEndpointLength
                    ⟨renderEdge.left, hbound⟩)) =
              graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge graphEdge hval hbound
      have hidx : graphEdge = hrel.edgeIndex prefixEdge := by
        exact fin_eq_of_val_eq hval.symm
      let childEndpoint :
          Fin (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).length :=
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨(rst.edges.get prefixEdge).left, hbound⟩
      let prefixEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex
          ⟨(rst.edges.get prefixEdge).left,
            hrel.edge_left_bound prefixEdge⟩
      have hendpoint :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (endpointOrder G st).get prefixEndpoint := by
        exact horderTrace.endpoint.get_prefix_at_right_of_val_eq
          childEndpoint prefixEndpoint
          (by simp [childEndpoint, prefixEndpoint])
      calc
        G.raw.endpointEdge
            ((endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).get
                childEndpoint) =
          G.raw.endpointEdge ((endpointOrder G st).get prefixEndpoint) := by
            exact congrArg G.raw.endpointEdge hendpoint
        _ = (edgeOrder st).get (hrel.edgeIndex prefixEdge) :=
            hrel.edge_left prefixEdge
        _ = (edgeOrder st).get graphEdge := by
            rw [hidx]
    · intro suffixEdge graphEdge hval hbound
      have hactiveBound : activeId < rst.endpoints.length := by
        have hbound := hrel.frontier_id_bound
          (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
        simpa [hids] using hbound
      let activeEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex ⟨activeId, hactiveBound⟩
      have hendpoint :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              (listIndexCast
                (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                hchildEndpointLength
                ⟨activeId, by
                  simpa [horderTrace, budChild_orderTrace] using hbound⟩) =
            (endpointOrder G st).get activeEndpoint := by
        exact horderTrace.endpoint.get_prefix_at_right_of_val_eq
          (listIndexCast
            (endpointOrder G (st.budChild hpending node slot hmate hunseen))
            hchildEndpointLength
            ⟨activeId, by
              simpa [horderTrace, budChild_orderTrace] using hbound⟩)
          activeEndpoint
          (by simp [activeEndpoint])
      have hcalc :
          G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  (listIndexCast
                    (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                    hchildEndpointLength
                    ⟨activeId, by
                      simpa [horderTrace, budChild_orderTrace] using
                        hbound⟩)) =
            G.raw.endpointEdge active := by
        calc
          G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  (listIndexCast
                    (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                    hchildEndpointLength
                    ⟨activeId, by
                      simpa [horderTrace, budChild_orderTrace] using
                        hbound⟩)) =
            G.raw.endpointEdge ((endpointOrder G st).get activeEndpoint) := by
              exact congrArg G.raw.endpointEdge hendpoint
          _ = G.raw.endpointEdge active := by
              exact congrArg G.raw.endpointEdge hpendingVals.1
      simpa [horderTrace, budChild_orderTrace] using hcalc
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast
          (edgeOrder (st.budChild hpending node slot hmate hunseen))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using
    (AppendTraceRelation.get hleftRel edge) (hchildEdgeBounds.left edge)

theorem GraphRenderRelated.budChild_edgeRight
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hnextEndpoint : rst.nextEndpoint = rst.endpoints.length)
    (hchildEndpointLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).endpoints.length =
        (endpointOrder G
          (st.budChild hpending node slot hmate hunseen)).length)
    (hchildEdgeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length =
        (edgeOrder (st.budChild hpending node slot hmate hunseen)).length)
    (hchildEdgeBounds :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).EdgeEndpointBounds) :
    ∀ edge : Fin (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).edges.length,
      G.raw.endpointEdge
          ((endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              (listIndexCast
                (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                hchildEndpointLength
                ⟨((Diag.budStep (G.raw.nodeLabel node)
                    (SearchState.budEntry (G := G) node slot)
                    (st.bud_compatible hpending node slot hmate) rst).edges.get edge).right,
                  hchildEdgeBounds.right edge⟩)) =
        (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
          (listIndexCast
            (edgeOrder (st.budChild hpending node slot hmate hunseen))
            hchildEdgeLength edge) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let nodeEndpoints := Diag.freshNodeEndpoints rst.nextEndpoint
    (Sig.arity renderNode)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints
      (by simp [nodeEndpoints, Diag.freshNodeEndpoints, renderNode]) entry
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hrightRel :
      AppendTraceRelation horderTrace.edge
        (fun renderEdge graphEdge =>
          ∀ hbound :
              renderEdge.right <
                (Diag.budStep renderNode entry ok rst).endpoints.length,
            G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  (listIndexCast
                    (endpointOrder G (st.budChild hpending node slot hmate hunseen))
                    hchildEndpointLength
                    ⟨renderEdge.right, hbound⟩)) =
              graphEdge) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro prefixEdge graphEdge hval hbound
      have hidx : graphEdge = hrel.edgeIndex prefixEdge := by
        exact fin_eq_of_val_eq hval.symm
      let childEndpoint :
          Fin (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).length :=
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨(rst.edges.get prefixEdge).right, hbound⟩
      let prefixEndpoint : Fin (endpointOrder G st).length :=
        hrel.endpointIndex
          ⟨(rst.edges.get prefixEdge).right,
            hrel.edge_right_bound prefixEdge⟩
      have hendpoint :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (endpointOrder G st).get prefixEndpoint := by
        exact horderTrace.endpoint.get_prefix_at_right_of_val_eq
          childEndpoint prefixEndpoint
          (by simp [childEndpoint, prefixEndpoint])
      calc
        G.raw.endpointEdge
            ((endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).get
                childEndpoint) =
          G.raw.endpointEdge ((endpointOrder G st).get prefixEndpoint) := by
            exact congrArg G.raw.endpointEdge hendpoint
        _ = (edgeOrder st).get (hrel.edgeIndex prefixEdge) :=
            hrel.edge_right prefixEdge
        _ = (edgeOrder st).get graphEdge := by
            rw [hidx]
    · intro suffixEdge graphEdge hval hbound
      have hnodeBound :
          nodeEndpoints.get entryIdx <
            (Diag.budStep renderNode entry ok rst).endpoints.length := by
        simpa [horderTrace, budChild_orderTrace, nodeEndpoints, entryIdx,
          renderNode] using hbound
      let childEndpoint :
          Fin (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).length :=
        listIndexCast
          (endpointOrder G (st.budChild hpending node slot hmate hunseen))
          hchildEndpointLength
          ⟨nodeEndpoints.get entryIdx, hnodeBound⟩
      have hrawGe : rst.endpoints.length ≤ nodeEndpoints.get entryIdx := by
        have hfreshMem :
            nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints entryIdx
        have hfreshGe := Diag.freshNodeEndpoints_mem_ge hfreshMem
        simpa [nodeEndpoints, renderNode, hnextEndpoint] using hfreshGe
      have hrightBound :
          nodeEndpoints.get entryIdx <
            rst.endpoints.length + Sig.arity renderNode := by
        have hbound' := hnodeBound
        rw [Diag.budStep_endpoints_length (G.raw.nodeLabel node)
          (SearchState.budEntry (G := G) node slot)
          (st.bud_compatible hpending node slot hmate) rst] at hbound'
        simpa [renderNode, entry, ok] using hbound'
      let graphSlot : Fin (G.raw.incident node).length :=
        ⟨nodeEndpoints.get entryIdx - rst.endpoints.length, by
          rw [G.raw.incident_length node]
          change
            nodeEndpoints.get entryIdx - rst.endpoints.length <
              Sig.arity renderNode
          omega⟩
      have hendpointRaw :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (G.raw.incident node).get graphSlot := by
        exact horderTrace.endpoint.get_suffix_at_right_of_val_eq
          childEndpoint graphSlot
          (by
            have holdLen :
                (endpointOrder G st).length = rst.endpoints.length :=
              hrel.endpoint_length.symm
            rw [holdLen]
            simpa [childEndpoint] using hrawGe)
          (by
            have holdLen :
                (endpointOrder G st).length = rst.endpoints.length :=
              hrel.endpoint_length.symm
            rw [holdLen]
            simp [childEndpoint, graphSlot])
      have hentryIdxVal : entryIdx.val = slot.val := by
        simp [entryIdx, entry, SearchState.budEntry, nodeEndpoints,
          renderNode, Signature.nodePortIndexOfLength]
      have hedgeSlotIdx : graphSlot = slot := by
        exact fin_eq_of_val_eq (by
          change
            nodeEndpoints.get entryIdx - rst.endpoints.length = slot.val
          have hsub :
              nodeEndpoints.get entryIdx - rst.endpoints.length =
                entryIdx.val := by
            simpa [nodeEndpoints] using
              Diag.freshNodeEndpoints_get_sub_of_eq
                (start := rst.nextEndpoint)
                (base := rst.endpoints.length)
                (arity := Sig.arity renderNode)
                hnextEndpoint entryIdx
          exact hsub.trans hentryIdxVal)
      have hendpoint :
          (endpointOrder G
            (st.budChild hpending node slot hmate hunseen)).get
              childEndpoint =
            (G.raw.incident node).get slot := by
        simpa [hedgeSlotIdx] using hendpointRaw
      have hcalc :
          G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint) =
            G.raw.endpointEdge active := by
        calc
          G.raw.endpointEdge
              ((endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint) =
            G.raw.endpointEdge ((G.raw.incident node).get slot) := by
              exact congrArg G.raw.endpointEdge hendpoint
          _ = G.raw.endpointEdge active := hmate.2.symm
      simpa [horderTrace, budChild_orderTrace, nodeEndpoints, entryIdx,
        renderNode, childEndpoint] using hcalc
  intro edge
  have hidx :
      horderTrace.edge.rightIndex edge =
        listIndexCast
          (edgeOrder (st.budChild hpending node slot hmate hunseen))
          hchildEdgeLength edge := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using
    (AppendTraceRelation.get hrightRel edge) (hchildEdgeBounds.right edge)

theorem GraphRenderRelated.budChild_nodeLabel
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (hchildNodeLength :
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).nodes.length =
        (nodeOrder (st.budChild hpending node slot hmate hunseen)).length) :
    ∀ renderIdx : Fin (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).nodes.length,
      ((Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst).nodes.get renderIdx).label =
        G.raw.nodeLabel
          ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
            (listIndexCast
              (nodeOrder (st.budChild hpending node slot hmate hunseen))
              hchildNodeLength renderIdx)) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  let horderTrace :=
    budChild_orderTrace rst st hpending node slot hmate hunseen hids
      hrel.endpoint_length hrel.edge_length hrel.node_length
  have hlabelRel :
      AppendTraceRelation horderTrace.node
        (fun renderNode graphNode =>
          renderNode.label = G.raw.nodeLabel graphNode) := by
    refine { prefix_rel := ?_, suffix_rel := ?_ }
    · intro oldNode graphNode hval
      have hidx : graphNode = hrel.nodeIndex oldNode := by
        exact fin_eq_of_val_eq hval.symm
      simpa [hidx] using hrel.node_label oldNode
    · intro renderNodeIdx graphNode _hval
      simp [horderTrace, budChild_orderTrace]
  intro renderIdx
  have hidx :
      horderTrace.node.rightIndex renderIdx =
        listIndexCast
          (nodeOrder (st.budChild hpending node slot hmate hunseen))
          hchildNodeLength renderIdx := by
    exact fin_eq_of_val_eq rfl
  simpa [hidx] using AppendTraceRelation.get hlabelRel renderIdx

theorem GraphRenderRelated.budChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {st : SearchState G (activeLabel :: frontier)}
    (hrel : GraphRenderRelated G rst st)
    (rv : rst.ValidIds)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    GraphRenderRelated G
      (Diag.budStep (G.raw.nodeLabel node)
        (SearchState.budEntry (G := G) node slot)
        (st.bud_compatible hpending node slot hmate) rst)
      (st.budChild hpending node slot hmate hunseen) := by
  let renderNode := G.raw.nodeLabel node
  let entry := SearchState.budEntry (G := G) node slot
  let ok := st.bud_compatible hpending node slot hmate
  cases hids : rst.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil rst hids)
  | cons activeId restIds =>
      have hseenChildNodup :
          (node :: st.seenNodes).Nodup := by
        constructor
        · intro other hmem hnodeEq
          exact hunseen (by simpa [hnodeEq] using hmem)
        · exact hrel.seenNodes_nodup
      have hchildEndpointLength :
          (Diag.budStep renderNode entry ok rst).endpoints.length =
            (endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).length := by
        rw [Diag.budStep_endpoints_length renderNode entry ok rst,
          endpointOrder_budChild st hpending node slot hmate hunseen]
        have hincidentLen := G.raw.incident_length node
        simp [hrel.endpoint_length, hincidentLen, renderNode]
      have hchildEdgeLength :
          (Diag.budStep renderNode entry ok rst).edges.length =
            (edgeOrder (st.budChild hpending node slot hmate hunseen)).length := by
        rw [Diag.budStep_edges_length renderNode entry ok rst,
          edgeOrder_budChild st hpending node slot hmate hunseen]
        simp [hrel.edge_length]
      have hchildNodeLength :
          (Diag.budStep renderNode entry ok rst).nodes.length =
            (nodeOrder (st.budChild hpending node slot hmate hunseen)).length := by
        rw [Diag.budStep_nodes_length renderNode entry ok rst,
          nodeOrder_budChild st hpending node slot hmate hunseen]
        simp [hrel.node_length]
      have hchildValid :
          (Diag.budStep renderNode entry ok rst).ValidIds :=
        Diag.budStep_validIds renderNode entry ok rst rv
      let hchildEdgeBounds :=
        hchildValid.edgeEndpointBounds
      let hfrontierPending :=
        hrel.budChild_frontierPending rv hpending node slot hmate hunseen hids
          hchildEndpointLength
      let hnodeIncidentFields :=
        hrel.budChild_nodeIncidentFields rv hpending node slot hmate hunseen hids
          hchildNodeLength
      let hnodeIncident :=
        hrel.budChild_nodeIncident rv hpending node slot hmate hunseen hids
          hchildEndpointLength hchildNodeLength hnodeIncidentFields
      refine
        { endpoint_nodup := ?_
          edge_nodup := ?_
          node_nodup := ?_
          endpoint_length := ?_
          edge_length := ?_
          node_length := ?_
          frontier_id_bound := ?_
          pending_length := ?_
          pending_id := ?_
          endpoint_label := ?_
          edge_label := ?_
          edge_left_bound := ?_
          edge_right_bound := ?_
          edge_left := ?_
          edge_right := ?_
          node_label := ?_
          node_incident_length := ?_
          node_incident_bound := ?_
          node_incident := ?_ }
      · exact endpointOrder_nodup_of_seenNodes_nodup hseenChildNodup
      · rw [edgeOrder_budChild st hpending node slot hmate hunseen]
        exact edgeOrder_append_active_nodup st (by rw [hpending]; simp)
      · exact nodeOrder_nodup_of_seenNodes_nodup hseenChildNodup
      · exact hchildEndpointLength
      · exact hchildEdgeLength
      · exact hchildNodeLength
      · exact hfrontierPending.frontier_id_bound
      · exact hfrontierPending.pending_length
      · exact hfrontierPending.pending_id
      · intro endpoint
        exact hrel.budChild_endpointLabel hpending node slot hmate hunseen hids
          hchildEndpointLength endpoint
      · intro edge
        exact hrel.budChild_edgeLabel hpending node slot hmate hunseen hids
          hchildEdgeLength edge
      · intro edge
        exact hchildEdgeBounds.left edge
      · intro edge
        exact hchildEdgeBounds.right edge
      · intro edge
        exact hrel.budChild_edgeLeft hpending node slot hmate hunseen hids
          hchildEndpointLength hchildEdgeLength hchildEdgeBounds edge
      · intro edge
        exact hrel.budChild_edgeRight hpending node slot hmate hunseen hids
          rv.nextEndpoint_eq hchildEndpointLength hchildEdgeLength
          hchildEdgeBounds edge
      · intro renderIdx
        exact hrel.budChild_nodeLabel hpending node slot hmate hunseen hids
          hchildNodeLength renderIdx
      · intro renderIdx
        exact hnodeIncidentFields.node_incident_length renderIdx
      · intro renderIdx renderSlot
        exact hnodeIncidentFields.node_incident_bound renderIdx renderSlot
      · intro renderIdx renderSlot
        exact hnodeIncident renderIdx renderSlot

theorem GraphRenderRelated.finish
    {G : OpenPortHypergraph Sig boundary}
    {rst : RenderState Sig []} {st : SearchState G []}
    (hrel : GraphRenderRelated G rst st) :
    GraphRenderRelated G (Diag.renderTrace Diag.finish rst) st := by
  dsimp [Diag.renderTrace]
  refine
    { endpoint_nodup := hrel.endpoint_nodup
      edge_nodup := hrel.edge_nodup
      node_nodup := hrel.node_nodup
      endpoint_length := hrel.endpoint_length
      edge_length := hrel.edge_length
      node_length := hrel.node_length
      frontier_id_bound := ?_
      pending_length := ?_
      pending_id := ?_
      endpoint_label := hrel.endpoint_label
      edge_label := hrel.edge_label
      edge_left_bound := hrel.edge_left_bound
      edge_right_bound := hrel.edge_right_bound
      edge_left := hrel.edge_left
      edge_right := hrel.edge_right
      node_label := hrel.node_label
      node_incident_length := hrel.node_incident_length
      node_incident_bound := hrel.node_incident_bound
      node_incident := hrel.node_incident }
  · intro id
    nomatch id
  · rw [st.pending_eq_nil_of_empty_frontier]
    rfl
  · intro id
    nomatch id

theorem GraphRenderRelated.toDiag
    {G : OpenPortHypergraph Sig boundary} :
    ∀ {frontier : List Sig.Port}
      (st : SearchState G frontier) (hcomplete : st.FrontierComplete)
      (rst : RenderState Sig frontier),
      rst.ValidIds →
      GraphRenderRelated G rst st →
      ∃ (finalSt : SearchState G []) (_hfinal : finalSt.FrontierComplete),
        GraphRenderRelated G (Diag.renderTrace (st.toDiag hcomplete) rst)
          finalSt := by
  intro frontier st hcomplete rst rv hrel
  induction frontier, st, hcomplete using SearchState.toDiag.induct with
  | case1 st hcomplete _hcomplete =>
      refine ⟨st, hcomplete, ?_⟩
      rw [SearchState.toDiag_empty st hcomplete]
      exact hrel.finish
  | case2 activeLabel restLabels active rest mate hmate st _hcomplete
      hcomplete hpending hstep _hstep ih =>
      rw [SearchState.toDiag_connect st hcomplete hpending mate hmate hstep]
      rw [Diag.renderTrace_connect]
      let childSt := st.connectChild hpending mate hmate
      have hchildComplete : childSt.FrontierComplete :=
        st.connectChild_frontierComplete hpending mate hmate hcomplete
      have hchildValid :
          (Diag.connectStep (st.restLabelIndex hpending mate)
            (st.connect_compatible hpending mate hmate) rst).ValidIds :=
        Diag.connectStep_validIds (st.restLabelIndex hpending mate)
          (st.connect_compatible hpending mate hmate) rst rv
      have hchildRel :
          GraphRenderRelated G
            (Diag.connectStep (st.restLabelIndex hpending mate)
              (st.connect_compatible hpending mate hmate) rst)
            childSt :=
        hrel.connectChild hpending mate hmate
      exact ih (Diag.connectStep (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) rst)
        hchildValid hchildRel
  | case3 activeLabel restLabels active rest node slot hmate st _hcomplete
      hcomplete hpending hunseen hstep _hstep ih =>
      rw [SearchState.toDiag_bud st hcomplete hpending node slot hmate hunseen
        hstep]
      rw [Diag.renderTrace_bud]
      let childSt := st.budChild hpending node slot hmate
        (by simpa [SearchState.seenNode] using hunseen)
      have hchildComplete : childSt.FrontierComplete :=
        st.budChild_frontierComplete hpending node slot hmate
          (by simpa [SearchState.seenNode] using hunseen) hcomplete
      have hchildValid :
          (Diag.budStep (G.raw.nodeLabel node) (SearchState.budEntry node slot)
            (st.bud_compatible hpending node slot hmate) rst).ValidIds :=
        Diag.budStep_validIds (G.raw.nodeLabel node)
          (SearchState.budEntry node slot)
          (st.bud_compatible hpending node slot hmate) rst rv
      have hchildRel :
          GraphRenderRelated G
            (Diag.budStep (G.raw.nodeLabel node)
              (SearchState.budEntry node slot)
              (st.bud_compatible hpending node slot hmate) rst)
            childSt :=
        hrel.budChild rv hpending node slot hmate
          (by simpa [SearchState.seenNode] using hunseen)
      exact ih
        (Diag.budStep (G.raw.nodeLabel node)
          (SearchState.budEntry node slot)
          (st.bud_compatible hpending node slot hmate) rst)
        hchildValid hchildRel

theorem endpoint_mem_endpointOrder_of_graphExhausted
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} {st : SearchState G frontier}
    (hexhausted : st.GraphExhausted)
    (endpoint : Fin G.raw.endpointCount) :
    endpoint ∈ endpointOrder G st := by
  rcases G.raw.endpoint_owner endpoint with ⟨owner, howner, _huniq⟩
  cases owner with
  | boundary boundaryIndex =>
      apply List.mem_append_left
      rw [List.mem_ofFn]
      refine ⟨boundaryIndex, ?_⟩
      simpa [PortHypergraph.endpointOwnerEndpoint] using howner
  | constructor node slot =>
      apply List.mem_append_right
      rw [List.mem_flatMap]
      refine ⟨node, ?_, ?_⟩
      · simpa using hexhausted.allNodesSeen node
      · change endpoint ∈ G.raw.incident node
        have hendpoint :
            (G.raw.incident node).get slot = endpoint := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        rw [← hendpoint]
        exact List.get_mem (G.raw.incident node) slot

theorem edge_mem_edgeOrder_of_graphExhausted
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} {st : SearchState G frontier}
    (hexhausted : st.GraphExhausted)
    (edge : Fin G.raw.edgeCount) :
    edge ∈ edgeOrder st := by
  simpa [edgeOrder] using hexhausted.allEdgesProcessed edge

theorem node_mem_nodeOrder_of_graphExhausted
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} {st : SearchState G frontier}
    (hexhausted : st.GraphExhausted)
    (node : Fin G.raw.nodeCount) :
    node ∈ nodeOrder st := by
  simpa [nodeOrder] using hexhausted.allNodesSeen node

def GraphRenderRelated.toPortHypergraphIso
    {G : OpenPortHypergraph Sig boundary}
    {st : SearchState G []}
    {rst : RenderState Sig []}
    (traceEv : RenderState.RenderTraceEvidence rst boundary)
    (hrel : GraphRenderRelated G rst st)
    (hexhausted : st.GraphExhausted) :
    PortHypergraphIso traceEv.toOpenPortHypergraph.raw G.raw := by
  let R := traceEv.toOpenPortHypergraph.raw
  let endpointCover :
      ∀ endpoint : Fin G.raw.endpointCount,
        endpoint ∈ endpointOrder G st :=
    endpoint_mem_endpointOrder_of_graphExhausted hexhausted
  let edgeCover :
      ∀ edge : Fin G.raw.edgeCount,
        edge ∈ edgeOrder st :=
    edge_mem_edgeOrder_of_graphExhausted hexhausted
  let nodeCover :
      ∀ node : Fin G.raw.nodeCount,
        node ∈ nodeOrder st :=
    node_mem_nodeOrder_of_graphExhausted hexhausted
  let endpointEquiv : Fin R.endpointCount ≃ᵢ Fin G.raw.endpointCount :=
    Iso.trans (finCastIso hrel.endpoint_length)
      (listFinIso (endpointOrder G st) hrel.endpoint_nodup endpointCover)
  let edgeEquiv : Fin R.edgeCount ≃ᵢ Fin G.raw.edgeCount :=
    Iso.trans (finCastIso hrel.edge_length)
      (listFinIso (edgeOrder st) hrel.edge_nodup edgeCover)
  let nodeEquiv : Fin R.nodeCount ≃ᵢ Fin G.raw.nodeCount :=
    Iso.trans (finCastIso hrel.node_length)
      (listFinIso (nodeOrder st) hrel.node_nodup nodeCover)
  refine PortHypergraphIso.ofPreserved endpointEquiv edgeEquiv nodeEquiv ?_ ?_ ?_ ?_ ?_ ?_
  · intro b
    have hval :
        (R.boundaryPort b).val = b.val := by
      simpa [R, RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        RenderState.RenderTraceEvidence.toOpenPortHypergraph,
        RenderState.RenderTraceEvidence.openEvidence,
        RenderState.RenderTraceEvidence.graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants] using
        RenderState.boundaryEvidenceOfPrefix_boundaryPort_val
          traceEv.endpointPrefix b
    dsimp [endpointEquiv, Iso.trans, finCastIso, listFinIso]
    have hprefix :=
      list_get_append_left (List.ofFn G.raw.boundaryPort)
        (st.seenNodes.reverse.flatMap fun node => G.raw.incident node)
        (i := b.val)
        (by simp)
        (by simp; omega)
    have hboundary :
        (List.ofFn G.raw.boundaryPort).get ⟨b.val, by simp⟩ =
          G.raw.boundaryPort b := by
      simp
    change
      (List.ofFn G.raw.boundaryPort ++
          (st.seenNodes.reverse.flatMap fun node => G.raw.incident node)).get
        ⟨b.val, by simp; omega⟩ =
      G.raw.boundaryPort b
    exact hprefix.trans hboundary
  · intro endpoint
    dsimp [R, endpointEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.RenderTraceEvidence.toOpenPortHypergraph,
      RenderState.RenderTraceEvidence.openEvidence,
      RenderState.RenderTraceEvidence.graphEvidence,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.endpoint_label endpoint
  · intro edge
    dsimp [R, edgeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.RenderTraceEvidence.toOpenPortHypergraph,
      RenderState.RenderTraceEvidence.openEvidence,
      RenderState.RenderTraceEvidence.graphEvidence,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.edge_label edge
  · intro endpoint
    dsimp [R, endpointEquiv, edgeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.RenderTraceEvidence.toOpenPortHypergraph,
      RenderState.RenderTraceEvidence.openEvidence,
      RenderState.RenderTraceEvidence.graphEvidence,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition]
    let edgeIndex := RenderState.endpointEdgeOfPartition
      traceEv.endpointPartition endpoint
    have hside :
        endpoint.val = (rst.edges.get edgeIndex).left ∨
          endpoint.val = (rst.edges.get edgeIndex).right := by
      simpa [edgeIndex] using
        RenderState.endpointEdgeOfPartition_endpoint
          traceEv.endpointPartition endpoint
    rcases hside with hleft | hright
    · change
        G.raw.endpointEdge
            ((endpointOrder G st).get
              (hrel.endpointIndex endpoint)) =
          (edgeOrder st).get (hrel.edgeIndex edgeIndex)
      exact hrel.edge_left_of_endpoint_val hleft
    · change
        G.raw.endpointEdge
            ((endpointOrder G st).get
              (hrel.endpointIndex endpoint)) =
          (edgeOrder st).get (hrel.edgeIndex edgeIndex)
      exact hrel.edge_right_of_endpoint_val hright
  · intro node
    dsimp [R, nodeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.RenderTraceEvidence.toOpenPortHypergraph,
      RenderState.RenderTraceEvidence.openEvidence,
      RenderState.RenderTraceEvidence.graphEvidence,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.node_label node
  · intro node
    dsimp [R, endpointEquiv, nodeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.RenderTraceEvidence.toOpenPortHypergraph,
      RenderState.RenderTraceEvidence.openEvidence,
      RenderState.RenderTraceEvidence.graphEvidence,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.incidenceEvidenceOfValidIds,
      RenderState.incidentOfValidIds]
    apply List.ext_getElem
    · simpa using hrel.node_incident_length node
    · intro i hleft hright
      rw [List.getElem_map]
      let slot : Fin (rst.nodes.get node).incident.length :=
        ⟨i, by simpa using hleft⟩
      have hslotRight :
          i <
            (G.raw.incident
              ((nodeOrder st).get (hrel.nodeIndex node))).length := by
        simpa [slot] using hright
      have hslotCast :
          (hrel.nodeIncidentIndex node slot).val = i := rfl
      have hleftGet :
          (endpointOrder G st).get
              (hrel.endpointIndex
                ⟨(rst.nodes.get node).incident.get slot,
                  hrel.node_incident_bound node slot⟩) =
            (G.raw.incident
              ((nodeOrder st).get (hrel.nodeIndex node))).get
                (hrel.nodeIncidentIndex node slot) := by
        simpa [nodeIncidentIndex, nodeIndex] using hrel.node_incident node slot
      simpa [slot, hslotCast] using hleftGet

end SearchState
end OpenPortHypergraph

end StringDiagram
end BijForm
