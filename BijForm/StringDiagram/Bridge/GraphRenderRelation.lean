import BijForm.StringDiagram.Bridge.SyntaxRoundTrip

namespace BijForm
namespace StringDiagram

open DepPoly

namespace OpenPortHypergraph
namespace SearchState

variable {Sig : Signature} {boundary : List Sig.Port}

/-- Endpoint order induced by a graph traversal prefix. -/
def endpointOrder (G : OpenPortHypergraph Sig boundary)
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    List (Fin G.raw.endpointCount) :=
  List.ofFn G.raw.boundaryPort ++
    st.seenNodes.reverse.flatMap fun node => G.raw.incident node

/-- Edge order induced by a graph traversal prefix. -/
def edgeOrder {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    List (Fin G.raw.edgeCount) :=
  st.processedEdges.reverse

/-- Constructor-node order induced by a graph traversal prefix. -/
def nodeOrder {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    List (Fin G.raw.nodeCount) :=
  st.seenNodes.reverse

theorem incident_mem_node_eq
    {G : OpenPortHypergraph Sig boundary}
    {leftNode rightNode : Fin G.raw.nodeCount}
    {endpoint : Fin G.raw.endpointCount}
    (hleft : endpoint ∈ G.raw.incident leftNode)
    (hright : endpoint ∈ G.raw.incident rightNode) :
    leftNode = rightNode := by
  rcases list_exists_get_of_mem (G.raw.incident leftNode) hleft with
    ⟨leftSlot, hleftSlot⟩
  rcases list_exists_get_of_mem (G.raw.incident rightNode) hright with
    ⟨rightSlot, hrightSlot⟩
  have hsame :
      (.constructor leftNode leftSlot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      .constructor rightNode rightSlot :=
    PortHypergraph.endpointOwner_eq_of_endpoint G.raw
      (owner₁ := .constructor leftNode leftSlot)
      (owner₂ := .constructor rightNode rightSlot)
      (by simpa [PortHypergraph.endpointOwnerEndpoint] using hleftSlot)
      (by simpa [PortHypergraph.endpointOwnerEndpoint] using hrightSlot)
  cases hsame
  rfl

theorem boundary_mem_not_incident_mem
    {G : OpenPortHypergraph Sig boundary}
    {endpoint : Fin G.raw.endpointCount}
    (hboundary : endpoint ∈ List.ofFn G.raw.boundaryPort)
    {node : Fin G.raw.nodeCount}
    (hincident : endpoint ∈ G.raw.incident node) :
    False := by
  rcases (List.mem_ofFn.mp hboundary) with ⟨boundaryIndex, hboundaryEq⟩
  rcases list_exists_get_of_mem (G.raw.incident node) hincident with
    ⟨slot, hslot⟩
  have hsame :
      (.boundary boundaryIndex :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      .constructor node slot :=
    PortHypergraph.endpointOwner_eq_of_endpoint G.raw
      (owner₁ := .boundary boundaryIndex)
      (owner₂ := .constructor node slot)
      (by simpa [PortHypergraph.endpointOwnerEndpoint] using hboundaryEq)
      (by simpa [PortHypergraph.endpointOwnerEndpoint] using hslot)
  cases hsame

theorem incidentFlatMap_nodup_of_nodup
    {G : OpenPortHypergraph Sig boundary} :
    ∀ (nodes : List (Fin G.raw.nodeCount)),
      nodes.Nodup →
        (nodes.flatMap fun node => G.raw.incident node).Nodup
  | [], _hnodup => by simp
  | node :: nodes, hnodup => by
      have hsplit : node ∉ nodes ∧ nodes.Nodup := by
        simpa using hnodup
      apply nodup_append_of_nodup_disjoint
      · exact G.raw.incident_nodup node
      · exact incidentFlatMap_nodup_of_nodup nodes hsplit.2
      · intro endpoint hhead htail
        rw [← List.flatMap_def] at htail
        rw [List.mem_flatMap] at htail
        rcases htail with ⟨otherNode, hotherNode, hotherIncident⟩
        have hnodeEq :
            node = otherNode :=
          incident_mem_node_eq hhead hotherIncident
        exact hsplit.1 (by simpa [hnodeEq] using hotherNode)

theorem endpointOrder_nodup_of_seenNodes_nodup
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} {st : SearchState G frontier}
    (hseen : st.seenNodes.Nodup) :
    (endpointOrder G st).Nodup := by
  unfold endpointOrder
  apply nodup_append_of_nodup_disjoint
  · exact list_nodup_ofFn_injective G.raw.boundaryPort G.raw.boundary_injective
  · exact incidentFlatMap_nodup_of_nodup st.seenNodes.reverse
      (list_nodup_reverse hseen)
  · intro endpoint hboundary hincident
    rw [List.mem_flatMap] at hincident
    rcases hincident with ⟨node, _hnode, hincident⟩
    exact boundary_mem_not_incident_mem hboundary hincident

theorem edgeOrder_nodup
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    (edgeOrder st).Nodup := by
  simpa [edgeOrder] using list_nodup_reverse st.processedEdges_nodup

theorem edgeOrder_append_active_nodup
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    (hpending : active ∈ st.pending) :
    (edgeOrder st ++ [G.raw.endpointEdge active]).Nodup := by
  apply nodup_append_of_nodup_disjoint
  · exact edgeOrder_nodup st
  · simp
  · intro edge hmem hnew
    simp at hnew
    subst edge
    exact st.pending_unprocessed active hpending
      (by simpa [edgeOrder] using hmem)

theorem nodeOrder_nodup_of_seenNodes_nodup
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} {st : SearchState G frontier}
    (hseen : st.seenNodes.Nodup) :
    (nodeOrder st).Nodup := by
  simpa [nodeOrder] using list_nodup_reverse hseen

theorem pending_mem_endpointOrder
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {endpoint : Fin G.raw.endpointCount}
    (hpending : endpoint ∈ st.pending) :
    endpoint ∈ endpointOrder G st := by
  rcases G.raw.endpoint_owner endpoint with ⟨owner, howner, _huniq⟩
  cases owner with
  | boundary boundaryIndex =>
      apply List.mem_append_left
      rw [List.mem_ofFn]
      refine ⟨boundaryIndex, ?_⟩
      simpa [PortHypergraph.endpointOwnerEndpoint] using howner
  | constructor node slot =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      have hseen :
          node ∈ st.seenNodes :=
        st.pending_owner_seen endpoint hpending (.constructor node slot)
          hownerEndpoint
      apply List.mem_append_right
      rw [List.mem_flatMap]
      refine ⟨node, ?_, ?_⟩
      · simpa using hseen
      · change endpoint ∈ G.raw.incident node
        have hendpoint :
            (G.raw.incident node).get slot = endpoint := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        rw [← hendpoint]
        exact List.get_mem (G.raw.incident node) slot

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
          (Fin.cast endpoint_length
            ⟨rst.frontierIds.get id, frontier_id_bound id⟩) =
        st.pending.get (Fin.cast pending_length id)
  endpoint_label :
    ∀ endpoint : Fin rst.endpoints.length,
      rst.endpoints.get endpoint =
        G.raw.endpointLabel
          ((endpointOrder G st).get (Fin.cast endpoint_length endpoint))
  edge_label :
    ∀ edge : Fin rst.edges.length,
      (rst.edges.get edge).label =
        G.raw.edgeLabel
          ((edgeOrder st).get (Fin.cast edge_length edge))
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
            (Fin.cast endpoint_length
              ⟨(rst.edges.get edge).left, edge_left_bound edge⟩)) =
        (edgeOrder st).get (Fin.cast edge_length edge)
  edge_right :
    ∀ edge : Fin rst.edges.length,
      G.raw.endpointEdge
          ((endpointOrder G st).get
            (Fin.cast endpoint_length
              ⟨(rst.edges.get edge).right, edge_right_bound edge⟩)) =
        (edgeOrder st).get (Fin.cast edge_length edge)
  node_label :
    ∀ node : Fin rst.nodes.length,
      (rst.nodes.get node).label =
        G.raw.nodeLabel
          ((nodeOrder st).get (Fin.cast node_length node))
  node_incident_length :
    ∀ node : Fin rst.nodes.length,
      (rst.nodes.get node).incident.length =
        (G.raw.incident
          ((nodeOrder st).get (Fin.cast node_length node))).length
  node_incident_bound :
    ∀ (node : Fin rst.nodes.length)
      (slot : Fin (rst.nodes.get node).incident.length),
      (rst.nodes.get node).incident.get slot < rst.endpoints.length
  node_incident :
    ∀ (node : Fin rst.nodes.length)
      (slot : Fin (rst.nodes.get node).incident.length),
      (endpointOrder G st).get
          (Fin.cast endpoint_length
            ⟨(rst.nodes.get node).incident.get slot,
              node_incident_bound node slot⟩) =
        (G.raw.incident
          ((nodeOrder st).get (Fin.cast node_length node))).get
            (Fin.cast (node_incident_length node) slot)

theorem GraphRenderRelated.edge_left_of_endpoint_val
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    {rst : RenderState Sig frontier} {st : SearchState G frontier}
    (hrel : GraphRenderRelated G rst st)
    {endpoint : Fin rst.endpoints.length} {edge : Fin rst.edges.length}
    (hleft : endpoint.val = (rst.edges.get edge).left) :
    G.raw.endpointEdge
        ((endpointOrder G st).get
          (Fin.cast hrel.endpoint_length endpoint)) =
      (edgeOrder st).get (Fin.cast hrel.edge_length edge) := by
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
          (Fin.cast hrel.endpoint_length endpoint)) =
      (edgeOrder st).get (Fin.cast hrel.edge_length edge) := by
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

theorem endpointOrder_connectChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    endpointOrder G (st.connectChild hpending mate hmate) =
      endpointOrder G st := by
  simp [endpointOrder, connectChild]

theorem endpointOrder_connectChild_get
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (endpoint :
      Fin (endpointOrder G (st.connectChild hpending mate hmate)).length) :
    (endpointOrder G (st.connectChild hpending mate hmate)).get endpoint =
      (endpointOrder G st).get
        (Fin.cast
          (congrArg List.length
            (endpointOrder_connectChild st hpending mate hmate))
          endpoint) :=
  list_get_of_eq (endpointOrder_connectChild st hpending mate hmate) endpoint

theorem edgeOrder_connectChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    edgeOrder (st.connectChild hpending mate hmate) =
      edgeOrder st ++ [G.raw.endpointEdge active] := by
  simp [edgeOrder, connectChild]

theorem edgeOrder_connectChild_get_old
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (edge :
      Fin (edgeOrder (st.connectChild hpending mate hmate)).length)
    (hold : edge.val < (edgeOrder st).length) :
    (edgeOrder (st.connectChild hpending mate hmate)).get edge =
      (edgeOrder st).get ⟨edge.val, hold⟩ := by
  exact list_get_of_eq_append_left
    (edgeOrder_connectChild st hpending mate hmate) edge hold

theorem edgeOrder_connectChild_get_new
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (edge :
      Fin (edgeOrder (st.connectChild hpending mate hmate)).length)
    (hnew : edge.val = (edgeOrder st).length) :
    (edgeOrder (st.connectChild hpending mate hmate)).get edge =
      G.raw.endpointEdge active := by
  let i := edge.val
  have hchildSome :
      (edgeOrder (st.connectChild hpending mate hmate))[i]? =
        some ((edgeOrder (st.connectChild hpending mate hmate)).get edge) :=
    by simp [i]
  have hnewSome :
      (edgeOrder (st.connectChild hpending mate hmate))[i]? =
        some (G.raw.endpointEdge active) := by
    rw [edgeOrder_connectChild st hpending mate hmate]
    have hi : i = (edgeOrder st).length := by
      simpa [i] using hnew
    rw [hi]
    simp
  rw [hchildSome] at hnewSome
  injection hnewSome with hget

theorem nodeOrder_connectChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    nodeOrder (st.connectChild hpending mate hmate) =
      nodeOrder st := by
  simp [nodeOrder, connectChild]

theorem nodeOrder_connectChild_get
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (node : Fin (nodeOrder (st.connectChild hpending mate hmate)).length) :
    (nodeOrder (st.connectChild hpending mate hmate)).get node =
      (nodeOrder st).get
        (Fin.cast
          (congrArg List.length
            (nodeOrder_connectChild st hpending mate hmate))
          node) :=
  list_get_of_eq (nodeOrder_connectChild st hpending mate hmate) node

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
        (Fin.cast hrel.endpoint_length
          ⟨activeId, by
            have hbound := hrel.frontier_id_bound
              (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
            simpa [hids] using hbound⟩) = active ∧
      ∀ id : Fin restIds.length,
        (endpointOrder G st).get
            (Fin.cast hrel.endpoint_length
              ⟨restIds.get id, by
                have hbound := hrel.frontier_id_bound
                  (⟨id.val + 1, by rw [hids]; simp [id.isLt]⟩ :
                    Fin rst.frontierIds.length)
                simpa [hids] using hbound⟩) =
          rest.get (Fin.cast (by
            have hpendingLen := hrel.pending_length
            rw [hids, hpending] at hpendingLen
            exact Nat.succ.inj hpendingLen) id) := by
  constructor
  · have h := hrel.pending_id
      (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
    have hcast :
        (Fin.cast hrel.pending_length
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
        (Fin.cast hrel.pending_length
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
        Fin.cast htailLen id := by
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
      have hrestIdsLen : restIds.length = frontier.length := by
        exact RenderState.frontierIds_cons_tail_length rst hids
      have htailLen : restIds.length = rest.length := by
        have hlen := hrel.pending_length
        rw [hids, hpending] at hlen
        exact Nat.succ.inj hlen
      let idx : Fin restIds.length := Fin.cast hrestIdsLen.symm rendererMate
      have hidxVal : idx.val = mate.val := by
        simp [idx, rendererMate, SearchState.restLabelIndex]
      have hpendingVals := hrel.pending_cons_values hpending hids
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
      have hchildEdgeLeftBound :
          ∀ edge : Fin (Diag.connectStep rendererMate ok rst).edges.length,
            ((Diag.connectStep rendererMate ok rst).edges.get edge).left <
              (Diag.connectStep rendererMate ok rst).endpoints.length := by
        intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedgeEq :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                rst.edges.get oldEdge :=
            Diag.connectStep_edges_get_old rendererMate ok rst hids edge hold
          rw [hedgeEq]
          exact Nat.lt_of_lt_of_eq (hrel.edge_left_bound oldEdge)
            (congrArg List.length
              (Diag.connectStep_endpoints rendererMate ok rst)).symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.connectStep_edges_length rendererMate ok rst)
            omega
          have hnewEdge :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                { label := Sig.portEdge activeLabel
                  leftLabel := activeLabel
                  rightLabel := frontier.get rendererMate
                  left := activeId
                  right := restIds.get idx
                  left_label := rfl
                  right_label := (Sig.compatible_edge ok).symm
                  compatible := ok } :=
            by
              have hnew :=
                Diag.connectStep_edges_get_new rendererMate ok rst hids edge
                  hnewVal
              simpa [idx] using hnew
          rw [hnewEdge]
          exact Nat.lt_of_lt_of_eq
            (by
              simpa using
                hrel.frontier_id_bound_of_mem
                  (by
                    rw [hids]
                    simp))
            (congrArg List.length
              (Diag.connectStep_endpoints rendererMate ok rst)).symm
      have hchildEdgeRightBound :
          ∀ edge : Fin (Diag.connectStep rendererMate ok rst).edges.length,
            ((Diag.connectStep rendererMate ok rst).edges.get edge).right <
              (Diag.connectStep rendererMate ok rst).endpoints.length := by
        intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedgeEq :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                rst.edges.get oldEdge :=
            Diag.connectStep_edges_get_old rendererMate ok rst hids edge hold
          rw [hedgeEq]
          exact Nat.lt_of_lt_of_eq (hrel.edge_right_bound oldEdge)
            (congrArg List.length
              (Diag.connectStep_endpoints rendererMate ok rst)).symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.connectStep_edges_length rendererMate ok rst)
            omega
          have hnewEdge :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                { label := Sig.portEdge activeLabel
                  leftLabel := activeLabel
                  rightLabel := frontier.get rendererMate
                  left := activeId
                  right := restIds.get idx
                  left_label := rfl
                  right_label := (Sig.compatible_edge ok).symm
                  compatible := ok } :=
            by
              have hnew :=
                Diag.connectStep_edges_get_new rendererMate ok rst hids edge
                  hnewVal
              simpa [idx] using hnew
          rw [hnewEdge]
          exact Nat.lt_of_lt_of_eq
            (by
              simpa using
                hrel.frontier_id_bound_of_mem (by
                  rw [hids]
                  right
                  exact List.get_mem restIds idx))
            (congrArg List.length
              (Diag.connectStep_endpoints rendererMate ok rst)).symm
      have hchildNodeIncidentLength :
          ∀ node : Fin (Diag.connectStep rendererMate ok rst).nodes.length,
            ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.length =
              (G.raw.incident
                ((nodeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast hchildNodeLength node))).length := by
        intro node
        let oldNode : Fin rst.nodes.length :=
          Fin.cast (congrArg List.length
            (Diag.connectStep_nodes rendererMate ok rst)) node
        let childNode : Fin
            (nodeOrder (st.connectChild hpending mate hmate)).length :=
          Fin.cast hchildNodeLength node
        let oldOrderNode : Fin (nodeOrder st).length :=
          Fin.cast hrel.node_length oldNode
        have hnodeGet :=
          Diag.connectStep_nodes_get rendererMate ok rst node
        have hnodeOrderGet :=
          nodeOrder_connectChild_get st hpending mate hmate childNode
        have hnodeOrderIdx :
            Fin.cast
                (congrArg List.length
                  (nodeOrder_connectChild st hpending mate hmate))
                childNode = oldOrderNode := by
          exact fin_eq_of_val_eq rfl
        have hnodeOrder :
            (nodeOrder (st.connectChild hpending mate hmate)).get childNode =
              (nodeOrder st).get oldOrderNode := by
          simpa [hnodeOrderIdx] using hnodeOrderGet
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
      have hchildNodeIncidentBound :
          ∀ (node : Fin (Diag.connectStep rendererMate ok rst).nodes.length)
            (slot : Fin
              ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.length),
            ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot <
              (Diag.connectStep rendererMate ok rst).endpoints.length := by
        intro node slot
        let oldNode : Fin rst.nodes.length :=
          Fin.cast (congrArg List.length
            (Diag.connectStep_nodes rendererMate ok rst)) node
        have hnodeGet :=
          Diag.connectStep_nodes_get rendererMate ok rst node
        let oldSlot : Fin (rst.nodes.get oldNode).incident.length :=
          Fin.cast (congrArg (fun renderNode => renderNode.incident.length)
            hnodeGet) slot
        have hincidentGet :
            ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot =
              (rst.nodes.get oldNode).incident.get oldSlot := by
          exact list_get_of_eq (congrArg RenderNode.incident hnodeGet) slot
        rw [hincidentGet]
        exact Nat.lt_of_lt_of_eq (hrel.node_incident_bound oldNode oldSlot)
          (congrArg List.length
            (Diag.connectStep_endpoints rendererMate ok rst)).symm
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
      · intro id
        have hchildIds :=
          Diag.connectStep_frontierIds rendererMate ok rst hids
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
      · have hchildIds :=
          Diag.connectStep_frontierIds rendererMate ok rst hids
        rw [hchildIds]
        exact eraseFin_length_eq_of_length_eq htailLen idx mate
      · intro id
        have hchildIds :=
          Diag.connectStep_frontierIds rendererMate ok rst hids
        have hchildPendingLen :
            (Diag.connectStep rendererMate ok rst).frontierIds.length =
              (st.connectChild hpending mate hmate).pending.length := by
          rw [hchildIds]
          exact eraseFin_length_eq_of_length_eq htailLen idx mate
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
                  (Fin.cast hrel.endpoint_length
                    ⟨(Diag.connectStep rendererMate ok rst).frontierIds.get id,
                      hbound⟩) =
                (st.connectChild hpending mate hmate).pending.get
                  (Fin.cast hchildPendingLen id) := by
          have hrestPoint :
              ∀ (n : Nat) (hid : n < restIds.length)
                (hrest : n < rest.length),
                ∃ hbound : restIds.get ⟨n, hid⟩ < rst.endpoints.length,
                  (endpointOrder G st).get
                      (Fin.cast hrel.endpoint_length
                        ⟨restIds.get ⟨n, hid⟩, hbound⟩) =
                    rest.get ⟨n, hrest⟩ := by
            intro n hid hrest
            refine ⟨hrel.frontier_id_bound_of_mem ?_, ?_⟩
            · rw [hids]
              right
              exact List.get_mem restIds ⟨n, hid⟩
            · have hidx :
                  (⟨n, hrest⟩ : Fin rest.length) =
                    Fin.cast htailLen ⟨n, hid⟩ := by
                exact fin_eq_of_val_eq rfl
              rw [hidx]
              exact hpendingVals.2 ⟨n, hid⟩
          have herased :=
            eraseFin_pointwise_relation
              (R := fun raw endpoint =>
                ∃ hbound : raw < rst.endpoints.length,
                  (endpointOrder G st).get
                      (Fin.cast hrel.endpoint_length ⟨raw, hbound⟩) =
                    endpoint)
              htailLen hrestPoint idx mate hidxVal
              id.val
              (by
                exact (congrArg List.length hchildIds) ▸ id.isLt)
              (by
                exact hchildPendingLen ▸ id.isLt)
          simpa [hchildIds, connectChild] using herased
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
      · intro endpoint
        have hendpointGet :=
          Diag.connectStep_endpoints_get rendererMate ok rst endpoint
        rw [hendpointGet]
        simpa [endpointOrder_connectChild st hpending mate hmate] using
          hrel.endpoint_label
            (Fin.cast
              (congrArg List.length
                (Diag.connectStep_endpoints rendererMate ok rst))
              endpoint)
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedgeEq :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                rst.edges.get oldEdge :=
            Diag.connectStep_edges_get_old rendererMate ok rst hids edge hold
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hedgeOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            have hget :=
              edgeOrder_connectChild_get_old st hpending mate hmate
                childEdge (by simpa [hrel.edge_length] using hold)
            simpa [childEdge, oldEdge] using hget
          rw [hedgeEq, hedgeOrder]
          exact hrel.edge_label oldEdge
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.connectStep_edges_length rendererMate ok rst)
            omega
          have hnewEdge :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                { label := Sig.portEdge activeLabel
                  leftLabel := activeLabel
                  rightLabel := frontier.get rendererMate
                  left := activeId
                  right := restIds.get idx
                  left_label := rfl
                  right_label := (Sig.compatible_edge ok).symm
                  compatible := ok } :=
            by
              have hnew :=
                Diag.connectStep_edges_get_new rendererMate ok rst hids edge
                  hnewVal
              simpa [idx] using hnew
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hnewOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                G.raw.endpointEdge active := by
            have hget :=
              edgeOrder_connectChild_get_new st hpending mate hmate
                childEdge (by simp [childEdge, hnewVal, hrel.edge_length])
            simpa [childEdge] using hget
          rw [hnewEdge, hnewOrder]
          have hactiveLabel := st.active_label_eq hpending
          change Sig.portEdge activeLabel =
            G.raw.edgeLabel (G.raw.endpointEdge active)
          rw [← hactiveLabel]
          exact G.raw.endpoint_edge_label active
      · exact hchildEdgeLeftBound
      · exact hchildEdgeRightBound
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedgeEq :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                rst.edges.get oldEdge :=
            Diag.connectStep_edges_get_old rendererMate ok rst hids edge hold
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hedgeOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            have hget :=
              edgeOrder_connectChild_get_old st hpending mate hmate
                childEdge (by simpa [hrel.edge_length] using hold)
            simpa [childEdge, oldEdge] using hget
          let childEndpoint :
              Fin (endpointOrder G
                (st.connectChild hpending mate hmate)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.connectStep rendererMate ok rst).edges.get edge).left,
                hchildEdgeLeftBound edge⟩
          let oldEndpoint :
              Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨(rst.edges.get oldEdge).left, hrel.edge_left_bound oldEdge⟩
          have hendpoint :
              (endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            exact list_get_of_eq_of_val_eq
              (endpointOrder_connectChild st hpending mate hmate)
              childEndpoint oldEndpoint
              (by
                simpa [childEndpoint, oldEndpoint] using
                  congrArg RenderEdge.left hedgeEq)
          calc
            G.raw.endpointEdge
                ((endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) :=
                hrel.edge_left oldEdge
            _ =
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact hedgeOrder.symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.connectStep_edges_length rendererMate ok rst)
            omega
          have hnewEdge :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                { label := Sig.portEdge activeLabel
                  leftLabel := activeLabel
                  rightLabel := frontier.get rendererMate
                  left := activeId
                  right := restIds.get idx
                  left_label := rfl
                  right_label := (Sig.compatible_edge ok).symm
                  compatible := ok } :=
            by
              have hnew :=
                Diag.connectStep_edges_get_new rendererMate ok rst hids edge
                  hnewVal
              simpa [idx] using hnew
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hnewOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                G.raw.endpointEdge active := by
            have hget :=
              edgeOrder_connectChild_get_new st hpending mate hmate
                childEdge (by simp [childEdge, hnewVal, hrel.edge_length])
            simpa [childEdge] using hget
          let childEndpoint :
              Fin (endpointOrder G
                (st.connectChild hpending mate hmate)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.connectStep rendererMate ok rst).edges.get edge).left,
                hchildEdgeLeftBound edge⟩
          let oldEndpoint :
              Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨activeId, by
                have hbound := hrel.frontier_id_bound
                  (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
                simpa [hids] using hbound⟩
          have hendpoint :
              (endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            exact list_get_of_eq_of_val_eq
              (endpointOrder_connectChild st hpending mate hmate)
              childEndpoint oldEndpoint
              (by
                simpa [childEndpoint, oldEndpoint] using
                  congrArg RenderEdge.left hnewEdge)
          calc
            G.raw.endpointEdge
                ((endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = G.raw.endpointEdge active := by
                exact congrArg G.raw.endpointEdge hpendingVals.1
            _ =
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact hnewOrder.symm
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedgeEq :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                rst.edges.get oldEdge :=
            Diag.connectStep_edges_get_old rendererMate ok rst hids edge hold
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hedgeOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            have hget :=
              edgeOrder_connectChild_get_old st hpending mate hmate
                childEdge (by simpa [hrel.edge_length] using hold)
            simpa [childEdge, oldEdge] using hget
          let childEndpoint :
              Fin (endpointOrder G
                (st.connectChild hpending mate hmate)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.connectStep rendererMate ok rst).edges.get edge).right,
                hchildEdgeRightBound edge⟩
          let oldEndpoint :
              Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨(rst.edges.get oldEdge).right, hrel.edge_right_bound oldEdge⟩
          have hendpoint :
              (endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            exact list_get_of_eq_of_val_eq
              (endpointOrder_connectChild st hpending mate hmate)
              childEndpoint oldEndpoint
              (by
                simpa [childEndpoint, oldEndpoint] using
                  congrArg RenderEdge.right hedgeEq)
          calc
            G.raw.endpointEdge
                ((endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) :=
                hrel.edge_right oldEdge
            _ =
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact hedgeOrder.symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.connectStep_edges_length rendererMate ok rst)
            omega
          have hnewEdge :
              (Diag.connectStep rendererMate ok rst).edges.get edge =
                { label := Sig.portEdge activeLabel
                  leftLabel := activeLabel
                  rightLabel := frontier.get rendererMate
                  left := activeId
                  right := restIds.get idx
                  left_label := rfl
                  right_label := (Sig.compatible_edge ok).symm
                  compatible := ok } :=
            by
              have hnew :=
                Diag.connectStep_edges_get_new rendererMate ok rst hids edge
                  hnewVal
              simpa [idx] using hnew
          let childEdge :
              Fin (edgeOrder (st.connectChild hpending mate hmate)).length :=
            Fin.cast
              (by
                rw [Diag.connectStep_edges_length rendererMate ok rst,
                  edgeOrder_connectChild st hpending mate hmate]
                simp [hrel.edge_length])
              edge
          have hnewOrder :
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast
                    (by
                      rw [Diag.connectStep_edges_length rendererMate ok rst,
                        edgeOrder_connectChild st hpending mate hmate]
                      simp [hrel.edge_length])
                    edge) =
                G.raw.endpointEdge active := by
            have hget :=
              edgeOrder_connectChild_get_new st hpending mate hmate
                childEdge (by simp [childEdge, hnewVal, hrel.edge_length])
            simpa [childEdge] using hget
          have hmateIdx : Fin.cast htailLen idx = mate := by
            exact fin_eq_of_val_eq hidxVal
          have hrightEndpoint :
              (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length
                    ⟨restIds.get idx, hrel.frontier_id_bound_of_mem (by
                      rw [hids]
                      right
                      exact List.get_mem restIds idx)⟩) =
                rest.get mate := by
            simpa [hmateIdx] using hpendingVals.2 idx
          let childEndpoint :
              Fin (endpointOrder G
                (st.connectChild hpending mate hmate)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.connectStep rendererMate ok rst).edges.get edge).right,
                hchildEdgeRightBound edge⟩
          let oldEndpoint :
              Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨restIds.get idx, hrel.frontier_id_bound_of_mem (by
                rw [hids]
                right
                exact List.get_mem restIds idx)⟩
          have hendpoint :
              (endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            exact list_get_of_eq_of_val_eq
              (endpointOrder_connectChild st hpending mate hmate)
              childEndpoint oldEndpoint
              (by
                simpa [childEndpoint, oldEndpoint] using
                  congrArg RenderEdge.right hnewEdge)
          calc
            G.raw.endpointEdge
                ((endpointOrder G (st.connectChild hpending mate hmate)).get
                  childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = G.raw.endpointEdge active := by
                exact (congrArg G.raw.endpointEdge hrightEndpoint).trans
                  hmate.2.symm
            _ =
              (edgeOrder (st.connectChild hpending mate hmate)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact hnewOrder.symm
      · intro node
        let oldNode : Fin rst.nodes.length :=
          Fin.cast (congrArg List.length
            (Diag.connectStep_nodes rendererMate ok rst)) node
        let childNode : Fin
            (nodeOrder (st.connectChild hpending mate hmate)).length :=
          Fin.cast hchildNodeLength node
        let oldOrderNode : Fin (nodeOrder st).length :=
          Fin.cast hrel.node_length oldNode
        have hnodeGet :=
          Diag.connectStep_nodes_get rendererMate ok rst node
        have hnodeOrderGet :=
          nodeOrder_connectChild_get st hpending mate hmate childNode
        have hnodeOrderIdx :
            Fin.cast
                (congrArg List.length
                  (nodeOrder_connectChild st hpending mate hmate))
                childNode = oldOrderNode := by
          exact fin_eq_of_val_eq rfl
        have hnodeOrder :
            (nodeOrder (st.connectChild hpending mate hmate)).get childNode =
              (nodeOrder st).get oldOrderNode := by
          simpa [hnodeOrderIdx] using hnodeOrderGet
        calc
          ((Diag.connectStep rendererMate ok rst).nodes.get node).label =
              (rst.nodes.get oldNode).label := by
            exact congrArg RenderNode.label hnodeGet
          _ = G.raw.nodeLabel ((nodeOrder st).get oldOrderNode) :=
              hrel.node_label oldNode
          _ =
            G.raw.nodeLabel
              ((nodeOrder (st.connectChild hpending mate hmate)).get
                childNode) := by
              exact congrArg G.raw.nodeLabel hnodeOrder.symm
      · intro node
        exact hchildNodeIncidentLength node
      · intro node slot
        exact hchildNodeIncidentBound node slot
      · intro node slot
        let oldNode : Fin rst.nodes.length :=
          Fin.cast (congrArg List.length
            (Diag.connectStep_nodes rendererMate ok rst)) node
        let childNode : Fin
            (nodeOrder (st.connectChild hpending mate hmate)).length :=
          Fin.cast hchildNodeLength node
        let oldOrderNode : Fin (nodeOrder st).length :=
          Fin.cast hrel.node_length oldNode
        have hnodeGet :=
          Diag.connectStep_nodes_get rendererMate ok rst node
        let oldSlot : Fin (rst.nodes.get oldNode).incident.length :=
          Fin.cast (congrArg (fun renderNode => renderNode.incident.length)
            hnodeGet) slot
        have hincidentGet :
            ((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot =
              (rst.nodes.get oldNode).incident.get oldSlot := by
          exact list_get_of_eq (congrArg RenderNode.incident hnodeGet) slot
        have hnodeOrderGet :=
          nodeOrder_connectChild_get st hpending mate hmate childNode
        have hnodeOrderIdx :
            Fin.cast
                (congrArg List.length
                  (nodeOrder_connectChild st hpending mate hmate))
                childNode = oldOrderNode := by
          exact fin_eq_of_val_eq rfl
        have hnodeOrder :
            (nodeOrder (st.connectChild hpending mate hmate)).get childNode =
              (nodeOrder st).get oldOrderNode := by
          simpa [hnodeOrderIdx] using hnodeOrderGet
        let childEndpoint :
            Fin (endpointOrder G
              (st.connectChild hpending mate hmate)).length :=
          Fin.cast hchildEndpointLength
            ⟨((Diag.connectStep rendererMate ok rst).nodes.get node).incident.get slot,
              hchildNodeIncidentBound node slot⟩
        let oldEndpoint : Fin (endpointOrder G st).length :=
          Fin.cast hrel.endpoint_length
            ⟨(rst.nodes.get oldNode).incident.get oldSlot,
              hrel.node_incident_bound oldNode oldSlot⟩
        have hendpointGet :=
          list_get_of_eq
            (endpointOrder_connectChild st hpending mate hmate)
            childEndpoint
        have hendpointIdx :
            Fin.cast
                (congrArg List.length
                  (endpointOrder_connectChild st hpending mate hmate))
                childEndpoint = oldEndpoint := by
          exact fin_eq_of_val_eq
            (by simpa [childEndpoint, oldEndpoint] using hincidentGet)
        have hendpoint :
            (endpointOrder G (st.connectChild hpending mate hmate)).get
                childEndpoint =
              (endpointOrder G st).get oldEndpoint := by
          simpa [hendpointIdx] using hendpointGet
        let childGraphSlot :
            Fin (G.raw.incident
              ((nodeOrder (st.connectChild hpending mate hmate)).get
                childNode)).length :=
          Fin.cast (hchildNodeIncidentLength node) slot
        let oldGraphSlot :
            Fin (G.raw.incident ((nodeOrder st).get oldOrderNode)).length :=
          Fin.cast (hrel.node_incident_length oldNode) oldSlot
        have hgraphSlotIdx :
            Fin.cast
                (congrArg (fun graphNode => (G.raw.incident graphNode).length)
                  hnodeOrder)
                childGraphSlot = oldGraphSlot := by
          exact fin_eq_of_val_eq rfl
        have hgraphGet :=
          list_get_of_eq
            (congrArg G.raw.incident hnodeOrder)
            childGraphSlot
        have hgraphIncident :
            (G.raw.incident ((nodeOrder st).get oldOrderNode)).get
                oldGraphSlot =
              (G.raw.incident
                ((nodeOrder (st.connectChild hpending mate hmate)).get
                  childNode)).get childGraphSlot := by
          simpa [hgraphSlotIdx] using hgraphGet.symm
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

theorem endpointOrder_budChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    endpointOrder G (st.budChild hpending node slot hmate hunseen) =
      endpointOrder G st ++ G.raw.incident node := by
  simp [endpointOrder, SearchState.budChild, List.reverse_cons,
    List.flatMap_append]

theorem edgeOrder_budChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    edgeOrder (st.budChild hpending node slot hmate hunseen) =
      edgeOrder st ++ [G.raw.endpointEdge active] := by
  simp [edgeOrder, SearchState.budChild]

theorem nodeOrder_budChild
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    (st : SearchState G (activeLabel :: frontier))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    nodeOrder (st.budChild hpending node slot hmate hunseen) =
      nodeOrder st ++ [node] := by
  simp [nodeOrder, SearchState.budChild]

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
      have hrestIdsLen : restIds.length = frontier.length := by
        exact RenderState.frontierIds_cons_tail_length rst hids
      have htailLen : restIds.length = rest.length := by
        have hlen := hrel.pending_length
        rw [hids, hpending] at hlen
        exact Nat.succ.inj hlen
      let nodeEndpoints := Diag.freshNodeEndpoints rst.nextEndpoint
        (Sig.arity renderNode)
      let entryIdx : Fin nodeEndpoints.length :=
        Fin.cast (by simp [nodeEndpoints, Diag.freshNodeEndpoints, renderNode]) entry
      have hpendingVals := hrel.pending_cons_values hpending hids
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
      have endpointAt_old :
          ∀ {raw : Nat}
            (hold : raw < rst.endpoints.length)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).endpoints.length),
            (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildEndpointLength ⟨raw, hbound⟩) =
              (endpointOrder G st).get
                (Fin.cast hrel.endpoint_length ⟨raw, hold⟩) := by
        intro raw hold hbound
        have horder :=
          endpointOrder_budChild st hpending node slot hmate hunseen
        let childEndpoint :
            Fin (endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildEndpointLength ⟨raw, hbound⟩
        let oldEndpoint : Fin (endpointOrder G st).length :=
          Fin.cast hrel.endpoint_length ⟨raw, hold⟩
        exact list_get_of_eq_append_left_of_val_eq horder
          childEndpoint oldEndpoint (by simp [childEndpoint, oldEndpoint])
      have endpointAt_new :
          ∀ {raw : Nat}
            (hle : rst.endpoints.length ≤ raw)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).endpoints.length),
            (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildEndpointLength ⟨raw, hbound⟩) =
              (G.raw.incident node).get
                ⟨raw - rst.endpoints.length, by
                  rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
                  have hincidentLen := G.raw.incident_length node
                  rw [hincidentLen]
                  change raw - rst.endpoints.length < Sig.arity renderNode
                  omega⟩ := by
        intro raw hle hbound
        have horder :=
          endpointOrder_budChild st hpending node slot hmate hunseen
        let childEndpoint :
            Fin (endpointOrder G
              (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildEndpointLength ⟨raw, hbound⟩
        have hleOrder : (endpointOrder G st).length ≤ raw := by
          rw [← hrel.endpoint_length]
          exact hle
        let newEndpoint : Fin (G.raw.incident node).length :=
          ⟨raw - rst.endpoints.length, by
            rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
            have hincidentLen := G.raw.incident_length node
            rw [hincidentLen]
            change raw - rst.endpoints.length < Sig.arity renderNode
            omega⟩
        exact list_get_of_eq_append_right_of_val_eq horder
          childEndpoint newEndpoint hleOrder (by
            have holdLen :
                (endpointOrder G st).length = rst.endpoints.length :=
              hrel.endpoint_length.symm
            simp [childEndpoint, newEndpoint, holdLen])
      have edgeAt_old :
          ∀ {raw : Nat}
            (hold : raw < rst.edges.length)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).edges.length),
            (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildEdgeLength ⟨raw, hbound⟩) =
              (edgeOrder st).get
                (Fin.cast hrel.edge_length ⟨raw, hold⟩) := by
        intro raw hold hbound
        have horder :=
          edgeOrder_budChild st hpending node slot hmate hunseen
        let childEdge :
            Fin (edgeOrder (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildEdgeLength ⟨raw, hbound⟩
        let oldEdge : Fin (edgeOrder st).length :=
          Fin.cast hrel.edge_length ⟨raw, hold⟩
        exact list_get_of_eq_append_left_of_val_eq horder
          childEdge oldEdge (by simp [childEdge, oldEdge])
      have edgeAt_new :
          ∀ {raw : Nat}
            (hnew : raw = rst.edges.length)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).edges.length),
            (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildEdgeLength ⟨raw, hbound⟩) =
              G.raw.endpointEdge active := by
        intro raw hnew hbound
        have horder :=
          edgeOrder_budChild st hpending node slot hmate hunseen
        let childEdge :
            Fin (edgeOrder (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildEdgeLength ⟨raw, hbound⟩
        exact list_get_of_eq_append_cons_at_length horder childEdge
          (by simp [childEdge, hnew, hrel.edge_length])
      have nodeAt_old :
          ∀ {raw : Nat}
            (hold : raw < rst.nodes.length)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).nodes.length),
            (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildNodeLength ⟨raw, hbound⟩) =
              (nodeOrder st).get
                (Fin.cast hrel.node_length ⟨raw, hold⟩) := by
        intro raw hold hbound
        have horder :=
          nodeOrder_budChild st hpending node slot hmate hunseen
        let childNode :
            Fin (nodeOrder (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildNodeLength ⟨raw, hbound⟩
        let oldNode : Fin (nodeOrder st).length :=
          Fin.cast hrel.node_length ⟨raw, hold⟩
        exact list_get_of_eq_append_left_of_val_eq horder
          childNode oldNode (by simp [childNode, oldNode])
      have nodeAt_new :
          ∀ {raw : Nat}
            (hnew : raw = rst.nodes.length)
            (hbound : raw < (Diag.budStep renderNode entry ok rst).nodes.length),
            (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildNodeLength ⟨raw, hbound⟩) =
              node := by
        intro raw hnew hbound
        have horder :=
          nodeOrder_budChild st hpending node slot hmate hunseen
        let childNode :
            Fin (nodeOrder (st.budChild hpending node slot hmate hunseen)).length :=
          Fin.cast hchildNodeLength ⟨raw, hbound⟩
        exact list_get_of_eq_append_cons_at_length horder childNode
          (by simp [childNode, hnew, hrel.node_length])
      have hchildNodeIncidentLength :
          ∀ renderIdx : Fin (Diag.budStep renderNode entry ok rst).nodes.length,
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.length =
              (G.raw.incident
                ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildNodeLength renderIdx))).length := by
        intro renderIdx
        by_cases hold : renderIdx.val < rst.nodes.length
        · let oldNode : Fin rst.nodes.length := ⟨renderIdx.val, hold⟩
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                rst.nodes.get oldNode := by
            simpa [oldNode] using
              Diag.budStep_nodes_get_old renderNode entry ok rst
                renderIdx hold
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          let oldOrderNode : Fin (nodeOrder st).length :=
            Fin.cast hrel.node_length oldNode
          have horder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode =
                (nodeOrder st).get oldOrderNode := by
            simpa [childNode, oldOrderNode, oldNode] using
              nodeAt_old hold renderIdx.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.length =
                (rst.nodes.get oldNode).incident.length := by
              exact congrArg (fun renderNode => renderNode.incident.length)
                hnode
            _ = (G.raw.incident ((nodeOrder st).get oldOrderNode)).length :=
                hrel.node_incident_length oldNode
            _ =
              (G.raw.incident
                ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode)).length := by
                rw [horder]
        · have hnewVal : renderIdx.val = rst.nodes.length := by
            have hlen : renderIdx.val < rst.nodes.length + 1 := by
              exact Nat.lt_of_lt_of_eq renderIdx.isLt
                (Diag.budStep_nodes_length renderNode entry ok rst)
            omega
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                { label := renderNode
                  incident := Diag.freshNodeEndpoints rst.nextEndpoint
                    (Sig.arity renderNode) } := by
            simpa [renderNode] using
              Diag.budStep_nodes_get_new renderNode entry ok rst
                renderIdx hnewVal
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          have horder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode = node := by
            simpa [childNode] using nodeAt_new hnewVal renderIdx.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.length =
                (Diag.freshNodeEndpoints rst.nextEndpoint
                  (Sig.arity renderNode)).length := by
              exact congrArg (fun renderNode => renderNode.incident.length)
                hnode
            _ = Sig.arity renderNode := by
              simp [Diag.freshNodeEndpoints]
            _ = (G.raw.incident node).length := by
              rw [G.raw.incident_length node]
            _ =
              (G.raw.incident
                ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode)).length := by
                rw [horder]
      have hchildNodeIncidentBound :
          ∀ (renderIdx : Fin (Diag.budStep renderNode entry ok rst).nodes.length)
            (renderSlot :
              Fin ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.length),
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get renderSlot <
              (Diag.budStep renderNode entry ok rst).endpoints.length := by
        intro renderIdx renderSlot
        exact hchildValid.node_incident_bound
          ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx)
          (List.get_mem (Diag.budStep renderNode entry ok rst).nodes renderIdx)
          renderSlot
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
      · intro id
        have hchildIds :=
          Diag.budStep_frontierIds renderNode entry ok rst hids
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
      · have hchildIds :=
          Diag.budStep_frontierIds renderNode entry ok rst hids
        rw [hchildIds]
        simp [SearchState.budChild, eraseFin_length, htailLen,
          renderNode, G.raw.incident_length node]
      · intro id
        have hchildIds :=
          Diag.budStep_frontierIds renderNode entry ok rst hids
        have hchildPendingLen :
            (Diag.budStep renderNode entry ok rst).frontierIds.length =
              (st.budChild hpending node slot hmate hunseen).pending.length := by
          rw [hchildIds]
          simp [SearchState.budChild, eraseFin_length, htailLen,
            renderNode, G.raw.incident_length node]
        have hnodeEndpointsLen :
            nodeEndpoints.length = (G.raw.incident node).length := by
          simp [nodeEndpoints, renderNode, G.raw.incident_length node]
        have hentryIdxVal : entryIdx.val = slot.val := by
          simp [entryIdx, entry, SearchState.budEntry, nodeEndpoints,
            renderNode]
        let R := fun raw endpoint =>
          ∃ hbound : raw < (Diag.budStep renderNode entry ok rst).endpoints.length,
            (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                (Fin.cast hchildEndpointLength ⟨raw, hbound⟩) =
              endpoint
        have hleftRel :
            ∀ (n : Nat) (hid : n < restIds.length)
              (hrest : n < rest.length),
              R (restIds.get ⟨n, hid⟩) (rest.get ⟨n, hrest⟩) := by
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
                  (Fin.cast hrel.endpoint_length
                    ⟨restIds.get ⟨n, hid⟩, holdBound⟩) =
                rest.get ⟨n, hrest⟩ := by
            have hidx :
                (⟨n, hrest⟩ : Fin rest.length) =
                  Fin.cast htailLen ⟨n, hid⟩ := by
              exact fin_eq_of_val_eq rfl
            rw [hidx]
            exact hpendingVals.2 ⟨n, hid⟩
          have horder :=
            endpointOrder_budChild st hpending node slot hmate hunseen
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨restIds.get ⟨n, hid⟩, hchildBound⟩
          let oldEndpoint : Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨restIds.get ⟨n, hid⟩, holdBound⟩
          have hchildOld :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint :=
            list_get_of_eq_append_left_of_val_eq horder
              childEndpoint oldEndpoint (by simp [childEndpoint, oldEndpoint])
          exact hchildOld.trans hold
        have hrightRel :
            ∀ (n : Nat) (hid : n < nodeEndpoints.length)
              (hincident : n < (G.raw.incident node).length),
              R (nodeEndpoints.get ⟨n, hid⟩)
                ((G.raw.incident node).get ⟨n, hincident⟩) := by
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
          have horder :=
            endpointOrder_budChild st hpending node slot hmate hunseen
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
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
          exact list_get_of_eq_append_right_of_val_eq horder
            childEndpoint incidentEndpoint hle hsub
        have herasedRight :=
          eraseFin_pointwise_relation
            (R := R) hnodeEndpointsLen hrightRel entryIdx slot hentryIdxVal
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
        have hall :=
          append_pointwise_relation
            (R := R)
            htailLen
            (eraseFin_length_eq_of_length_eq hnodeEndpointsLen entryIdx slot)
            hleftRel
            herasedRight
            id.val
            appendIndex.isLt
            pendingIndex.isLt
        rcases hall with ⟨hbound, hget⟩
        have hrawEq :
            (restIds ++ eraseFin nodeEndpoints entryIdx).get appendIndex =
              (Diag.budStep renderNode entry ok rst).frontierIds.get id := by
          have hgetIds := list_get_of_eq hchildIds id
          have hcast :
              Fin.cast (congrArg List.length hchildIds) id = appendIndex := by
            exact fin_eq_of_val_eq rfl
          simpa [appendIndex, hcast] using hgetIds.symm
        have htargetBound :
            (Diag.budStep renderNode entry ok rst).frontierIds.get id <
              (Diag.budStep renderNode entry ok rst).endpoints.length := by
          have hmem :
              (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
                restIds ++ eraseFin nodeEndpoints entryIdx := by
            rw [← hchildIds]
            exact List.get_mem
              (Diag.budStep renderNode entry ok rst).frontierIds id
          rcases List.mem_append.mp hmem with hold | hnew
          · have holdMem :
                (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
                  rst.frontierIds := by
              rw [hids]
              right
              exact hold
            have hboundOld := hrel.frontier_id_bound_of_mem holdMem
            rw [Diag.budStep_endpoints_length renderNode entry ok rst]
            omega
          · have hfresh :
                (Diag.budStep renderNode entry ok rst).frontierIds.get id ∈
                  nodeEndpoints :=
              mem_of_mem_eraseFin nodeEndpoints entryIdx hnew
            have hfreshLt := Diag.freshNodeEndpoints_mem_lt hfresh
            rw [Diag.budStep_endpoints_length renderNode entry ok rst]
            simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using hfreshLt
        have hpendingIndex :
            (st.budChild hpending node slot hmate hunseen).pending.get
                (Fin.cast hchildPendingLen id) =
              (rest ++ eraseFin (G.raw.incident node) slot).get pendingIndex := by
          simp [SearchState.budChild, pendingIndex]
        have hendpointIndex :
            Fin.cast hchildEndpointLength
                ⟨(Diag.budStep renderNode entry ok rst).frontierIds.get id,
                  htargetBound⟩ =
              Fin.cast hchildEndpointLength
                ⟨(restIds ++ eraseFin nodeEndpoints entryIdx).get appendIndex,
                  hbound⟩ := by
          exact fin_eq_of_val_eq hrawEq.symm
        rw [hendpointIndex]
        rw [hpendingIndex]
        exact hget
      · intro endpoint
        by_cases hold : endpoint.val < rst.endpoints.length
        · let oldEndpoint : Fin rst.endpoints.length := ⟨endpoint.val, hold⟩
          have hrender :
              (Diag.budStep renderNode entry ok rst).endpoints.get endpoint =
                rst.endpoints.get oldEndpoint := by
            simpa [oldEndpoint] using
              Diag.budStep_endpoints_get_old renderNode entry ok rst
                endpoint hold
          have horder :
              (endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEndpointLength endpoint) =
                (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length oldEndpoint) := by
            simpa [oldEndpoint] using endpointAt_old hold endpoint.isLt
          calc
            (Diag.budStep renderNode entry ok rst).endpoints.get endpoint =
                rst.endpoints.get oldEndpoint := hrender
            _ =
                G.raw.endpointLabel
                  ((endpointOrder G st).get
                    (Fin.cast hrel.endpoint_length oldEndpoint)) :=
                hrel.endpoint_label oldEndpoint
            _ =
                G.raw.endpointLabel
                  ((endpointOrder G
                    (st.budChild hpending node slot hmate hunseen)).get
                      (Fin.cast hchildEndpointLength endpoint)) := by
                rw [horder]
        · have hle : rst.endpoints.length ≤ endpoint.val :=
            Nat.le_of_not_gt hold
          have hslotArity :
              endpoint.val - rst.endpoints.length < Sig.arity renderNode := by
            have hb :
                endpoint.val < rst.endpoints.length + Sig.arity renderNode := by
              exact Nat.lt_of_lt_of_eq endpoint.isLt
                (Diag.budStep_endpoints_length renderNode entry ok rst)
            omega
          let renderSlot : Fin (Sig.nodePorts renderNode).length :=
            ⟨endpoint.val - rst.endpoints.length, by
              simpa [Signature.nodePorts] using hslotArity⟩
          let graphSlot : Fin (G.raw.incident node).length :=
            ⟨endpoint.val - rst.endpoints.length, by
              rw [G.raw.incident_length node]
              change endpoint.val - rst.endpoints.length < Sig.arity renderNode
              exact hslotArity⟩
          have hrender :
              (Diag.budStep renderNode entry ok rst).endpoints.get endpoint =
                (Sig.nodePorts renderNode).get renderSlot := by
            simpa [renderSlot] using
              Diag.budStep_endpoints_get_new renderNode entry ok rst
                endpoint hle
          have horder :
              (endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEndpointLength endpoint) =
                (G.raw.incident node).get graphSlot := by
            simpa [graphSlot] using endpointAt_new hle endpoint.isLt
          have hlabel :
              (Sig.nodePorts renderNode).get renderSlot =
                G.raw.endpointLabel ((G.raw.incident node).get graphSlot) := by
            have hinc := G.raw.incidence_label node graphSlot
            rw [hinc]
            simp [Signature.nodePorts, renderNode, renderSlot, graphSlot]
          calc
            (Diag.budStep renderNode entry ok rst).endpoints.get endpoint =
                (Sig.nodePorts renderNode).get renderSlot := hrender
            _ =
                G.raw.endpointLabel ((G.raw.incident node).get graphSlot) :=
                hlabel
            _ =
                G.raw.endpointLabel
                  ((endpointOrder G
                    (st.budChild hpending node slot hmate hunseen)).get
                      (Fin.cast hchildEndpointLength endpoint)) := by
                rw [horder]
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedge :
              (Diag.budStep renderNode entry ok rst).edges.get edge =
                rst.edges.get oldEdge := by
            simpa [oldEdge] using
              Diag.budStep_edges_get_old renderNode entry ok rst hids
                edge hold
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            simpa [oldEdge] using edgeAt_old hold edge.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).edges.get edge).label =
                (rst.edges.get oldEdge).label := by
              exact congrArg RenderEdge.label hedge
            _ =
                G.raw.edgeLabel
                  ((edgeOrder st).get (Fin.cast hrel.edge_length oldEdge)) :=
                hrel.edge_label oldEdge
            _ =
                G.raw.edgeLabel
                  ((edgeOrder
                    (st.budChild hpending node slot hmate hunseen)).get
                      (Fin.cast hchildEdgeLength edge)) := by
                rw [horder]
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.budStep_edges_length renderNode entry ok rst)
            omega
          have hedgeLabel :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).label =
                Sig.portEdge activeLabel := by
            have hedge :=
              Diag.budStep_edges_get_new renderNode entry ok rst hids
                edge hnewVal
            exact congrArg RenderEdge.label hedge
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                G.raw.endpointEdge active := by
            simpa using edgeAt_new hnewVal edge.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).edges.get edge).label =
                Sig.portEdge activeLabel := hedgeLabel
            _ = G.raw.edgeLabel (G.raw.endpointEdge active) := by
              have hactiveLabel := st.active_label_eq hpending
              rw [← hactiveLabel]
              exact G.raw.endpoint_edge_label active
            _ =
                G.raw.edgeLabel
                  ((edgeOrder
                    (st.budChild hpending node slot hmate hunseen)).get
                      (Fin.cast hchildEdgeLength edge)) := by
              rw [horder]
      · intro edge
        exact hchildValid.edge_left_bound
          ((Diag.budStep renderNode entry ok rst).edges.get edge)
          (List.get_mem (Diag.budStep renderNode entry ok rst).edges edge)
      · intro edge
        exact hchildValid.edge_right_bound
          ((Diag.budStep renderNode entry ok rst).edges.get edge)
          (List.get_mem (Diag.budStep renderNode entry ok rst).edges edge)
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedge :
              (Diag.budStep renderNode entry ok rst).edges.get edge =
                rst.edges.get oldEdge := by
            simpa [oldEdge] using
              Diag.budStep_edges_get_old renderNode entry ok rst hids
                edge hold
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            simpa [oldEdge] using edgeAt_old hold edge.isLt
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                hchildValid.edge_left_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge)⟩
          let oldEndpoint : Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨(rst.edges.get oldEdge).left, hrel.edge_left_bound oldEdge⟩
          have hrawHold :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).left <
                rst.endpoints.length := by
            have hraw := congrArg RenderEdge.left hedge
            rw [hraw]
            exact hrel.edge_left_bound oldEdge
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length
                    ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                      hrawHold⟩) := by
            simpa [childEndpoint] using
              endpointAt_old hrawHold
                (hchildValid.edge_left_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge))
          have hidx :
              (Fin.cast hrel.endpoint_length
                  ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                    hrawHold⟩ :
                Fin (endpointOrder G st).length) = oldEndpoint := by
            exact fin_eq_of_val_eq (congrArg RenderEdge.left hedge)
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            rw [← hidx]
            exact hendpointRaw
          calc
            G.raw.endpointEdge
                ((endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                    childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) :=
                hrel.edge_left oldEdge
            _ =
              (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact horder.symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.budStep_edges_length renderNode entry ok rst)
            omega
          have hleftRaw :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).left =
                activeId := by
            have hedge :=
              Diag.budStep_edges_get_new renderNode entry ok rst hids
                edge hnewVal
            exact congrArg RenderEdge.left hedge
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                G.raw.endpointEdge active := by
            simpa using edgeAt_new hnewVal edge.isLt
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                hchildValid.edge_left_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge)⟩
          let oldEndpoint : Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨activeId, by
                have hbound := hrel.frontier_id_bound
                  (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
                simpa [hids] using hbound⟩
          have hrawHold :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).left <
                rst.endpoints.length := by
            rw [hleftRaw]
            have hbound := hrel.frontier_id_bound
              (⟨0, by rw [hids]; simp⟩ : Fin rst.frontierIds.length)
            simpa [hids] using hbound
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length
                    ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                      hrawHold⟩) := by
            simpa [childEndpoint] using
              endpointAt_old hrawHold
                (hchildValid.edge_left_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge))
          have hidx :
              (Fin.cast hrel.endpoint_length
                  ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).left,
                    hrawHold⟩ :
                Fin (endpointOrder G st).length) = oldEndpoint := by
            exact fin_eq_of_val_eq hleftRaw
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            rw [← hidx]
            exact hendpointRaw
          calc
            G.raw.endpointEdge
                ((endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                    childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = G.raw.endpointEdge active := by
                exact congrArg G.raw.endpointEdge hpendingVals.1
            _ =
              (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact horder.symm
      · intro edge
        by_cases hold : edge.val < rst.edges.length
        · let oldEdge : Fin rst.edges.length := ⟨edge.val, hold⟩
          have hedge :
              (Diag.budStep renderNode entry ok rst).edges.get edge =
                rst.edges.get oldEdge := by
            simpa [oldEdge] using
              Diag.budStep_edges_get_old renderNode entry ok rst hids
                edge hold
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) := by
            simpa [oldEdge] using edgeAt_old hold edge.isLt
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right,
                hchildValid.edge_right_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge)⟩
          let oldEndpoint : Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨(rst.edges.get oldEdge).right, hrel.edge_right_bound oldEdge⟩
          have hrawHold :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).right <
                rst.endpoints.length := by
            have hraw := congrArg RenderEdge.right hedge
            rw [hraw]
            exact hrel.edge_right_bound oldEdge
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length
                    ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right,
                      hrawHold⟩) := by
            simpa [childEndpoint] using
              endpointAt_old hrawHold
                (hchildValid.edge_right_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge))
          have hidx :
              (Fin.cast hrel.endpoint_length
                  ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right,
                    hrawHold⟩ :
                Fin (endpointOrder G st).length) = oldEndpoint := by
            exact fin_eq_of_val_eq (congrArg RenderEdge.right hedge)
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            rw [← hidx]
            exact hendpointRaw
          calc
            G.raw.endpointEdge
                ((endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                    childEndpoint) =
              G.raw.endpointEdge ((endpointOrder G st).get oldEndpoint) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = (edgeOrder st).get (Fin.cast hrel.edge_length oldEdge) :=
                hrel.edge_right oldEdge
            _ =
              (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact horder.symm
        · have hnewVal : edge.val = rst.edges.length := by
            have hlen : edge.val < rst.edges.length + 1 := by
              exact Nat.lt_of_lt_of_eq edge.isLt
                (Diag.budStep_edges_length renderNode entry ok rst)
            omega
          have hrightRaw :
              ((Diag.budStep renderNode entry ok rst).edges.get edge).right =
                nodeEndpoints.get entryIdx := by
            have hedge :=
              Diag.budStep_edges_get_new renderNode entry ok rst hids
                edge hnewVal
            simpa [nodeEndpoints, entryIdx, renderNode] using
              congrArg RenderEdge.right hedge
          have horder :
              (edgeOrder
                (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) =
                G.raw.endpointEdge active := by
            simpa using edgeAt_new hnewVal edge.isLt
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right,
                hchildValid.edge_right_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge)⟩
          have hrawGe :
              rst.endpoints.length ≤
                ((Diag.budStep renderNode entry ok rst).edges.get edge).right := by
            rw [hrightRaw]
            have hfreshMem :
                nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
              List.get_mem nodeEndpoints entryIdx
            have hfreshGe := Diag.freshNodeEndpoints_mem_ge hfreshMem
            simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using
              hfreshGe
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (G.raw.incident node).get
                  ⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right -
                      rst.endpoints.length,
                    by
                      have hbound :=
                        hchildValid.edge_right_bound
                          ((Diag.budStep renderNode entry ok rst).edges.get edge)
                          (List.get_mem
                            (Diag.budStep renderNode entry ok rst).edges edge)
                      rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
                      rw [G.raw.incident_length node]
                      change
                        ((Diag.budStep renderNode entry ok rst).edges.get edge).right -
                          rst.endpoints.length < Sig.arity renderNode
                      omega⟩ := by
            simpa [childEndpoint] using
              endpointAt_new hrawGe
                (hchildValid.edge_right_bound
                  ((Diag.budStep renderNode entry ok rst).edges.get edge)
                  (List.get_mem
                    (Diag.budStep renderNode entry ok rst).edges edge))
          have hentryIdxVal : entryIdx.val = slot.val := by
            simp [entryIdx, entry, SearchState.budEntry, nodeEndpoints,
              renderNode]
          have hslotIdx :
              (⟨((Diag.budStep renderNode entry ok rst).edges.get edge).right -
                    rst.endpoints.length,
                  by
                    have hbound :=
                      hchildValid.edge_right_bound
                        ((Diag.budStep renderNode entry ok rst).edges.get edge)
                        (List.get_mem
                          (Diag.budStep renderNode entry ok rst).edges edge)
                    rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
                    rw [G.raw.incident_length node]
                    change
                      ((Diag.budStep renderNode entry ok rst).edges.get edge).right -
                        rst.endpoints.length < Sig.arity renderNode
                    omega⟩ : Fin (G.raw.incident node).length) = slot := by
            exact fin_eq_of_val_eq (by
              change
                ((Diag.budStep renderNode entry ok rst).edges.get edge).right -
                  rst.endpoints.length = slot.val
              rw [hrightRaw]
              have hsub :
                  nodeEndpoints.get entryIdx - rst.endpoints.length =
                    entryIdx.val := by
                simpa [nodeEndpoints] using
                  Diag.freshNodeEndpoints_get_sub_of_eq
                    (start := rst.nextEndpoint)
                    (base := rst.endpoints.length)
                    (arity := Sig.arity renderNode)
                    rv.nextEndpoint_eq entryIdx
              exact hsub.trans hentryIdxVal)
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (G.raw.incident node).get slot := by
            rw [hslotIdx] at hendpointRaw
            exact hendpointRaw
          calc
            G.raw.endpointEdge
                ((endpointOrder G
                  (st.budChild hpending node slot hmate hunseen)).get
                    childEndpoint) =
              G.raw.endpointEdge ((G.raw.incident node).get slot) := by
                exact congrArg G.raw.endpointEdge hendpoint
            _ = G.raw.endpointEdge active := hmate.2.symm
            _ =
              (edgeOrder (st.budChild hpending node slot hmate hunseen)).get
                  (Fin.cast hchildEdgeLength edge) := by
                exact horder.symm
      · intro renderIdx
        by_cases hold : renderIdx.val < rst.nodes.length
        · let oldNode : Fin rst.nodes.length := ⟨renderIdx.val, hold⟩
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                rst.nodes.get oldNode := by
            simpa [oldNode] using
              Diag.budStep_nodes_get_old renderNode entry ok rst
                renderIdx hold
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          let oldOrderNode : Fin (nodeOrder st).length :=
            Fin.cast hrel.node_length oldNode
          have horder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode =
                (nodeOrder st).get oldOrderNode := by
            simpa [childNode, oldOrderNode, oldNode] using
              nodeAt_old hold renderIdx.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).label =
                (rst.nodes.get oldNode).label := by
              exact congrArg RenderNode.label hnode
            _ = G.raw.nodeLabel ((nodeOrder st).get oldOrderNode) :=
                hrel.node_label oldNode
            _ =
              G.raw.nodeLabel
                ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode) := by
                rw [horder]
        · have hnewVal : renderIdx.val = rst.nodes.length := by
            have hlen : renderIdx.val < rst.nodes.length + 1 := by
              exact Nat.lt_of_lt_of_eq renderIdx.isLt
                (Diag.budStep_nodes_length renderNode entry ok rst)
            omega
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                { label := renderNode
                  incident := Diag.freshNodeEndpoints rst.nextEndpoint
                    (Sig.arity renderNode) } := by
            simpa [renderNode] using
              Diag.budStep_nodes_get_new renderNode entry ok rst
                renderIdx hnewVal
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          have horder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode = node := by
            simpa [childNode] using nodeAt_new hnewVal renderIdx.isLt
          calc
            ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).label =
                renderNode := by
              exact congrArg RenderNode.label hnode
            _ = G.raw.nodeLabel node := by
              rfl
            _ =
              G.raw.nodeLabel
                ((nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode) := by
                rw [horder]
      · intro renderIdx
        exact hchildNodeIncidentLength renderIdx
      · intro renderIdx renderSlot
        exact hchildNodeIncidentBound renderIdx renderSlot
      · intro renderIdx renderSlot
        by_cases hold : renderIdx.val < rst.nodes.length
        · let oldNode : Fin rst.nodes.length := ⟨renderIdx.val, hold⟩
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                rst.nodes.get oldNode := by
            simpa [oldNode] using
              Diag.budStep_nodes_get_old renderNode entry ok rst
                renderIdx hold
          let oldSlot : Fin (rst.nodes.get oldNode).incident.length :=
            Fin.cast (congrArg (fun renderNode => renderNode.incident.length)
              hnode) renderSlot
          have hincidentGet :
              ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot =
                (rst.nodes.get oldNode).incident.get oldSlot := by
            exact list_get_of_eq (congrArg RenderNode.incident hnode)
              renderSlot
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot,
                hchildNodeIncidentBound renderIdx renderSlot⟩
          let oldEndpoint : Fin (endpointOrder G st).length :=
            Fin.cast hrel.endpoint_length
              ⟨(rst.nodes.get oldNode).incident.get oldSlot,
                hrel.node_incident_bound oldNode oldSlot⟩
          have hrawHold :
              ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot < rst.endpoints.length := by
            rw [hincidentGet]
            exact hrel.node_incident_bound oldNode oldSlot
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get
                  (Fin.cast hrel.endpoint_length
                    ⟨((Diag.budStep renderNode entry ok rst).nodes.get
                        renderIdx).incident.get renderSlot,
                      hrawHold⟩) := by
            simpa [childEndpoint] using
              endpointAt_old hrawHold
                (hchildNodeIncidentBound renderIdx renderSlot)
          have hendpointIdx :
              (Fin.cast hrel.endpoint_length
                  ⟨((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                      renderSlot,
                    hrawHold⟩ :
                Fin (endpointOrder G st).length) = oldEndpoint := by
            exact fin_eq_of_val_eq hincidentGet
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (endpointOrder G st).get oldEndpoint := by
            rw [← hendpointIdx]
            exact hendpointRaw
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          let oldOrderNode : Fin (nodeOrder st).length :=
            Fin.cast hrel.node_length oldNode
          have hnodeOrder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode =
                (nodeOrder st).get oldOrderNode := by
            simpa [childNode, oldOrderNode, oldNode] using
              nodeAt_old hold renderIdx.isLt
          let childGraphSlot :
              Fin (G.raw.incident
                ((nodeOrder
                  (st.budChild hpending node slot hmate hunseen)).get
                    childNode)).length :=
            Fin.cast (hchildNodeIncidentLength renderIdx) renderSlot
          let oldGraphSlot :
              Fin (G.raw.incident ((nodeOrder st).get oldOrderNode)).length :=
            Fin.cast (hrel.node_incident_length oldNode) oldSlot
          have hgraphSlotIdx :
              Fin.cast
                  (congrArg (fun graphNode =>
                    (G.raw.incident graphNode).length) hnodeOrder)
                  childGraphSlot = oldGraphSlot := by
            exact fin_eq_of_val_eq rfl
          have hgraphGet :=
            list_get_of_eq (congrArg G.raw.incident hnodeOrder)
              childGraphSlot
          have hgraphIncident :
              (G.raw.incident ((nodeOrder st).get oldOrderNode)).get
                  oldGraphSlot =
                (G.raw.incident
                  ((nodeOrder
                    (st.budChild hpending node slot hmate hunseen)).get
                      childNode)).get childGraphSlot := by
            simpa [hgraphSlotIdx] using hgraphGet.symm
          calc
            (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                childEndpoint =
              (endpointOrder G st).get oldEndpoint := hendpoint
            _ =
              (G.raw.incident ((nodeOrder st).get oldOrderNode)).get
                  oldGraphSlot := hrel.node_incident oldNode oldSlot
            _ =
              (G.raw.incident
                ((nodeOrder
                  (st.budChild hpending node slot hmate hunseen)).get
                    childNode)).get childGraphSlot := hgraphIncident
        · have hnewVal : renderIdx.val = rst.nodes.length := by
            have hlen : renderIdx.val < rst.nodes.length + 1 := by
              exact Nat.lt_of_lt_of_eq renderIdx.isLt
                (Diag.budStep_nodes_length renderNode entry ok rst)
            omega
          have hnode :
              (Diag.budStep renderNode entry ok rst).nodes.get renderIdx =
                { label := renderNode
                  incident := Diag.freshNodeEndpoints rst.nextEndpoint
                    (Sig.arity renderNode) } := by
            simpa [renderNode] using
              Diag.budStep_nodes_get_new renderNode entry ok rst
                renderIdx hnewVal
          let freshSlot : Fin nodeEndpoints.length :=
            Fin.cast (by
              rw [← congrArg (fun renderNode => renderNode.incident.length) hnode])
              renderSlot
          have hincidentGet :
              ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot =
                nodeEndpoints.get freshSlot := by
            have hget :=
              list_get_of_eq (congrArg RenderNode.incident hnode)
                renderSlot
            simpa [freshSlot, nodeEndpoints] using hget
          let childEndpoint :
              Fin (endpointOrder G
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildEndpointLength
              ⟨((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot,
                hchildNodeIncidentBound renderIdx renderSlot⟩
          have hrawGe :
              rst.endpoints.length ≤
                ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                  renderSlot := by
            rw [hincidentGet]
            have hfreshMem :
                nodeEndpoints.get freshSlot ∈ nodeEndpoints :=
              List.get_mem nodeEndpoints freshSlot
            have hfreshGe := Diag.freshNodeEndpoints_mem_ge hfreshMem
            simpa [nodeEndpoints, renderNode, rv.nextEndpoint_eq] using
              hfreshGe
          have hendpointRaw :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (G.raw.incident node).get
                  ⟨((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                      renderSlot - rst.endpoints.length,
                    by
                      have hbound := hchildNodeIncidentBound renderIdx renderSlot
                      rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
                      rw [G.raw.incident_length node]
                      change
                        ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                            renderSlot - rst.endpoints.length < Sig.arity renderNode
                      omega⟩ := by
            simpa [childEndpoint] using
              endpointAt_new hrawGe
                (hchildNodeIncidentBound renderIdx renderSlot)
          let graphSlot : Fin (G.raw.incident node).length :=
            ⟨freshSlot.val, by
              have hslot : freshSlot.val < Sig.arity renderNode := by
                simpa [nodeEndpoints, Diag.freshNodeEndpoints] using
                  freshSlot.isLt
              rw [G.raw.incident_length node]
              exact hslot⟩
          have hslotIdx :
              (⟨((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                    renderSlot - rst.endpoints.length,
                  by
                    have hbound := hchildNodeIncidentBound renderIdx renderSlot
                    rw [Diag.budStep_endpoints_length renderNode entry ok rst] at hbound
                    rw [G.raw.incident_length node]
                    change
                      ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                        renderSlot - rst.endpoints.length < Sig.arity renderNode
                    omega⟩ : Fin (G.raw.incident node).length) = graphSlot := by
            exact fin_eq_of_val_eq (by
              change
                ((Diag.budStep renderNode entry ok rst).nodes.get renderIdx).incident.get
                    renderSlot - rst.endpoints.length = freshSlot.val
              rw [hincidentGet]
              simpa [nodeEndpoints] using
                Diag.freshNodeEndpoints_get_sub_of_eq
                  (start := rst.nextEndpoint)
                  (base := rst.endpoints.length)
                  (arity := Sig.arity renderNode)
                  rv.nextEndpoint_eq freshSlot)
          have hendpoint :
              (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                  childEndpoint =
                (G.raw.incident node).get graphSlot := by
            rw [hslotIdx] at hendpointRaw
            exact hendpointRaw
          let childNode :
              Fin (nodeOrder
                (st.budChild hpending node slot hmate hunseen)).length :=
            Fin.cast hchildNodeLength renderIdx
          have hnodeOrder :
              (nodeOrder (st.budChild hpending node slot hmate hunseen)).get
                  childNode = node := by
            simpa [childNode] using nodeAt_new hnewVal renderIdx.isLt
          let childGraphSlot :
              Fin (G.raw.incident
                ((nodeOrder
                  (st.budChild hpending node slot hmate hunseen)).get
                    childNode)).length :=
            Fin.cast (hchildNodeIncidentLength renderIdx) renderSlot
          have hgraphSlotIdx :
              Fin.cast
                  (congrArg (fun graphNode =>
                    (G.raw.incident graphNode).length) hnodeOrder)
                  childGraphSlot = graphSlot := by
            exact fin_eq_of_val_eq rfl
          have hgraphGet :=
            list_get_of_eq (congrArg G.raw.incident hnodeOrder)
              childGraphSlot
          have hgraphIncident :
              (G.raw.incident node).get graphSlot =
                (G.raw.incident
                  ((nodeOrder
                    (st.budChild hpending node slot hmate hunseen)).get
                      childNode)).get childGraphSlot := by
            simpa [hgraphSlotIdx] using hgraphGet.symm
          calc
            (endpointOrder G (st.budChild hpending node slot hmate hunseen)).get
                childEndpoint =
              (G.raw.incident node).get graphSlot := hendpoint
            _ =
              (G.raw.incident
                ((nodeOrder
                  (st.budChild hpending node slot hmate hunseen)).get
                    childNode)).get childGraphSlot := hgraphIncident

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
    (hv : rst.ValidIds)
    (hp : rst.EndpointPartition)
    (hn : rst.NodeIncidentNodup)
    (pref : rst.EndpointPrefix boundary)
    (ho : rst.OwnerIdPartition boundary)
    (hall :
      PortHypergraph.AllConstructorsReachBoundary
        (RenderState.portHypergraphEvidenceOfInvariants
          hv hp hn pref ho).toPortHypergraph)
    (hrel : GraphRenderRelated G rst st)
    (hexhausted : st.GraphExhausted) :
    PortHypergraphIso
      (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw
      G.raw := by
  let R :=
    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw
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
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.openEvidenceOfInvariants,
        RenderState.portHypergraphEvidenceOfInvariants] using
        RenderState.boundaryEvidenceOfPrefix_boundaryPort_val pref b
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
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.openEvidenceOfInvariants,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.endpoint_label endpoint
  · intro edge
    dsimp [R, edgeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.openEvidenceOfInvariants,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.edge_label edge
  · intro endpoint
    dsimp [R, endpointEquiv, edgeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.openEvidenceOfInvariants,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition]
    let edgeIndex := RenderState.endpointEdgeOfPartition hp endpoint
    have hside :
        endpoint.val = (rst.edges.get edgeIndex).left ∨
          endpoint.val = (rst.edges.get edgeIndex).right := by
      simpa [edgeIndex] using
        RenderState.endpointEdgeOfPartition_endpoint hp endpoint
    rcases hside with hleft | hright
    · change
        G.raw.endpointEdge
            ((endpointOrder G st).get
              (Fin.cast hrel.endpoint_length endpoint)) =
          (edgeOrder st).get (Fin.cast hrel.edge_length edgeIndex)
      exact hrel.edge_left_of_endpoint_val hleft
    · change
        G.raw.endpointEdge
            ((endpointOrder G st).get
              (Fin.cast hrel.endpoint_length endpoint)) =
          (edgeOrder st).get (Fin.cast hrel.edge_length edgeIndex)
      exact hrel.edge_right_of_endpoint_val hright
  · intro node
    dsimp [R, nodeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.openEvidenceOfInvariants,
      RenderState.portHypergraphEvidenceOfInvariants]
    exact hrel.node_label node
  · intro node
    dsimp [R, endpointEquiv, nodeEquiv, Iso.trans, finCastIso, listFinIso,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.openEvidenceOfInvariants,
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
              ((nodeOrder st).get (Fin.cast hrel.node_length node))).length := by
        simpa [slot] using hright
      have hslotCast :
          (Fin.cast (hrel.node_incident_length node) slot).val = i := rfl
      have hleftGet :
          (endpointOrder G st).get
              (Fin.cast hrel.endpoint_length
                ⟨(rst.nodes.get node).incident.get slot,
                  hrel.node_incident_bound node slot⟩) =
            (G.raw.incident
              ((nodeOrder st).get (Fin.cast hrel.node_length node))).get
                (Fin.cast (hrel.node_incident_length node) slot) :=
        hrel.node_incident node slot
      simpa [slot, hslotCast] using hleftGet

end SearchState
end OpenPortHypergraph

end StringDiagram
end BijForm
