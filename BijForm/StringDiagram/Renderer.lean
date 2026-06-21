import BijForm.StringDiagram.Basic

namespace BijForm
namespace StringDiagram

open DepPoly

/-- An edge recorded by the concrete traversal renderer. -/
structure RenderEdge (Sig : Signature) where
  label : Sig.Edge
  leftLabel : Sig.Port
  rightLabel : Sig.Port
  left : Nat
  right : Nat
  left_label : Sig.portEdge leftLabel = label
  right_label : Sig.portEdge rightLabel = label
  compatible : Sig.compatible leftLabel rightLabel

/-- A constructor node recorded by the concrete traversal renderer. -/
structure RenderNode (Sig : Signature) where
  label : Sig.Node
  incident : List Nat

/--
Mutable-by-return construction state for rendering traversal syntax.

The `frontierIds` field stores endpoint identifiers in the same order as the
frontier in the type index.  `connect` consumes the head identifier and one
later identifier.  `bud` consumes the head identifier, allocates the ordered
constructor endpoints, connects the chosen entry endpoint, and appends the
remaining constructor endpoints to the frontier.
-/
structure RenderState (Sig : Signature) (frontier : List Sig.Port) where
  nextEndpoint : Nat
  endpoints : List Sig.Port
  edges : List (RenderEdge Sig)
  nodes : List (RenderNode Sig)
  frontierIds : List Nat
  frontierIds_length : frontierIds.length = frontier.length

namespace RenderState

variable (Sig : Signature)

def initial (boundary : List Sig.Port) : RenderState Sig boundary where
  nextEndpoint := boundary.length
  endpoints := boundary
  edges := []
  nodes := []
  frontierIds := List.range boundary.length
  frontierIds_length := by simp

theorem frontierIds_ne_nil {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    (st : RenderState Sig (active :: frontier)) :
    st.frontierIds ≠ [] := by
  intro hids
  have hlen := st.frontierIds_length
  rw [hids] at hlen
  simp at hlen

theorem cast_frontierIds {Sig : Signature}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : RenderState Sig frontier) :
    (h ▸ st).frontierIds = st.frontierIds := by
  cases h
  rfl

theorem cast_edges {Sig : Signature}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : RenderState Sig frontier) :
    (h ▸ st).edges = st.edges := by
  cases h
  rfl

theorem cast_nodes {Sig : Signature}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : RenderState Sig frontier) :
    (h ▸ st).nodes = st.nodes := by
  cases h
  rfl

/--
ID-level validity for a renderer state.  It is the proof layer that turns the
raw `Nat` endpoint identifiers stored in the trace into valid finite endpoint
indices with the labels required by semantic evidence.
-/
structure ValidIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  nextEndpoint_eq : st.nextEndpoint = st.endpoints.length
  frontier_bound :
    ∀ id : Nat, id ∈ st.frontierIds → id < st.endpoints.length
  frontier_label :
    ∀ (n : Nat) (hid : n < st.frontierIds.length)
      (hfrontier : n < frontier.length),
      st.endpoints.get
        ⟨st.frontierIds.get ⟨n, hid⟩,
          frontier_bound (st.frontierIds.get ⟨n, hid⟩)
            (List.get_mem st.frontierIds ⟨n, hid⟩)⟩ =
      frontier.get ⟨n, hfrontier⟩
  edge_left_bound :
    ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge.left < st.endpoints.length
  edge_right_bound :
    ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge.right < st.endpoints.length
  edge_left_label :
    ∀ (edge : RenderEdge Sig) (hmem : edge ∈ st.edges),
      st.endpoints.get ⟨edge.left, edge_left_bound edge hmem⟩ =
        edge.leftLabel
  edge_right_label :
    ∀ (edge : RenderEdge Sig) (hmem : edge ∈ st.edges),
      st.endpoints.get ⟨edge.right, edge_right_bound edge hmem⟩ =
        edge.rightLabel
  node_incident_length :
    ∀ node : RenderNode Sig, node ∈ st.nodes →
      node.incident.length = Sig.arity node.label
  node_incident_bound :
    ∀ (node : RenderNode Sig) (_hmem : node ∈ st.nodes)
      (slot : Fin node.incident.length),
      node.incident.get slot < st.endpoints.length
  node_incident_label :
    ∀ (node : RenderNode Sig) (hmem : node ∈ st.nodes)
      (slot : Fin node.incident.length),
      st.endpoints.get
        ⟨node.incident.get slot,
          node_incident_bound node hmem slot⟩ =
        Sig.port node.label
          (Fin.cast (node_incident_length node hmem) slot)

def edgeEndpointIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : List Nat :=
  st.edges.flatMap fun edge => [edge.left, edge.right]

/--
The endpoint-consumption invariant for renderer states.  Every endpoint ID is
either pending in the ordered frontier or has already been consumed by exactly
one rendered edge endpoint.  This is the invariant from which the semantic
`endpointEdge` map is later derived when the frontier is empty.
-/
structure EndpointPartition {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  frontier_nodup : st.frontierIds.Nodup
  consumed_nodup : st.edgeEndpointIds.Nodup
  consumed_bound :
    ∀ id : Nat, id ∈ st.edgeEndpointIds → id < st.endpoints.length
  frontier_consumed_disjoint :
    ∀ id : Nat, id ∈ st.frontierIds → id ∈ st.edgeEndpointIds → False
  endpoint_covered :
    ∀ id : Nat, id < st.endpoints.length →
      id ∈ st.frontierIds ∨ id ∈ st.edgeEndpointIds

/-- Every rendered constructor node stores each incident endpoint at most once. -/
structure NodeIncidentNodup {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  node_incident_nodup :
    ∀ node : RenderNode Sig, node ∈ st.nodes → node.incident.Nodup

def nodeIncidentIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : List Nat :=
  st.nodes.flatMap fun node => node.incident

def ownerEndpointIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : List Nat :=
  List.range boundary.length ++ st.nodeIncidentIds

/--
Endpoint-ID inventory for semantic owners.  Boundary positions own the initial
range of endpoint IDs, and rendered constructor nodes own their ordered
incident IDs.
-/
structure OwnerIdPartition {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : Prop where
  owner_nodup : (st.ownerEndpointIds boundary).Nodup
  owner_bound :
    ∀ id : Nat, id ∈ st.ownerEndpointIds boundary → id < st.endpoints.length
  owner_covered :
    ∀ id : Nat, id < st.endpoints.length → id ∈ st.ownerEndpointIds boundary

theorem OwnerIdPartition.boundaryIds_nodup
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (List.range boundary.length).Nodup :=
  nodup_append_left (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup)

theorem OwnerIdPartition.nodeIncidentIds_nodup
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    st.nodeIncidentIds.Nodup :=
  nodup_append_right (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup)

theorem OwnerIdPartition.boundary_nodeIncidentIds_disjoint
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) {id : Nat}
    (hboundary : id ∈ List.range boundary.length)
    (hnode : id ∈ st.nodeIncidentIds) : False :=
  nodup_append_disjoint (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup) hboundary hnode

/-- `base` occurs as the ordered prefix of a renderer state's endpoint list. -/
structure EndpointPrefix {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (base : List Sig.Port) where
  suffix : List Sig.Port
  endpoints_eq : st.endpoints = base ++ suffix

def EndpointPrefix.trans {Sig : Signature}
    {frontier frontier' : List Sig.Port}
    {st : RenderState Sig frontier} {st' : RenderState Sig frontier'}
    {base : List Sig.Port}
    (pref : EndpointPrefix st base)
    (next : EndpointPrefix st' st.endpoints) :
    EndpointPrefix st' base :=
  match pref, next with
  | ⟨prefSuffix, hpref⟩, ⟨nextSuffix, hnext⟩ =>
      { suffix := prefSuffix ++ nextSuffix
        endpoints_eq := by
          calc
            st'.endpoints = st.endpoints ++ nextSuffix := hnext
            _ = (base ++ prefSuffix) ++ nextSuffix := by
              exact congrArg (fun endpoints => endpoints ++ nextSuffix) hpref
            _ = base ++ (prefSuffix ++ nextSuffix) := by
              rw [List.append_assoc] }

/-- Ordered boundary evidence derived from a renderer endpoint-prefix proof. -/
structure BoundaryEvidence {Sig : Signature}
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  boundaryPort : Fin boundary.length → Fin st.endpoints.length
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length,
      st.endpoints.get (boundaryPort b) = boundary.get b

def boundaryEvidenceOfPrefix {Sig : Signature} {st : RenderState Sig []}
    {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary) :
    BoundaryEvidence st boundary where
  boundaryPort := fun b =>
    ⟨b.val, by
      rw [pref.endpoints_eq]
      simp
      omega⟩
  boundary_injective := by
    intro left right h
    apply Fin.ext
    change left.val = right.val
    exact congrArg (fun x : Fin st.endpoints.length => x.val) h
  boundary_label := by
    intro b
    have hbound : b.val < st.endpoints.length := by
      rw [pref.endpoints_eq]
      simp
      omega
    change st.endpoints[b.val]'hbound = boundary[b.val]
    have hopt : st.endpoints[b.val]? = boundary[b.val]? := by
      rw [pref.endpoints_eq]
      exact List.getElem?_append_left (l₁ := boundary)
        (l₂ := pref.suffix) b.isLt
    have hstSome :
        st.endpoints[b.val]? = some (st.endpoints[b.val]'hbound) :=
      List.getElem?_eq_getElem hbound
    have hboundarySome :
        boundary[b.val]? = some boundary[b.val] :=
      List.getElem?_eq_getElem b.isLt
    rw [hstSome, hboundarySome] at hopt
    simpa using hopt

theorem boundaryEvidenceOfPrefix_boundaryPort_val {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary) (b : Fin boundary.length) :
    ((boundaryEvidenceOfPrefix pref).boundaryPort b).val = b.val :=
  rfl

theorem boundaryEvidenceOfPrefix_exists_of_boundary_id {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary)
    (endpoint : Fin st.endpoints.length)
    (hboundary : endpoint.val ∈ List.range boundary.length) :
    ∃ b : Fin boundary.length,
      (boundaryEvidenceOfPrefix pref).boundaryPort b = endpoint := by
  let b : Fin boundary.length := ⟨endpoint.val, List.mem_range.mp hboundary⟩
  refine ⟨b, ?_⟩
  apply Fin.ext
  simp [b, boundaryEvidenceOfPrefix_boundaryPort_val pref b]

theorem initial_validIds {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).ValidIds where
  nextEndpoint_eq := by
    simp [initial]
  frontier_bound := by
    intro id hid
    simpa [initial] using hid
  frontier_label := by
    intro n hid hfrontier
    simp [initial]
  edge_left_bound := by
    intro edge hmem
    simp [initial] at hmem
  edge_right_bound := by
    intro edge hmem
    simp [initial] at hmem
  edge_left_label := by
    intro edge hmem
    simp [initial] at hmem
  edge_right_label := by
    intro edge hmem
    simp [initial] at hmem
  node_incident_length := by
    intro node hmem
    simp [initial] at hmem
  node_incident_bound := by
    intro node hmem slot
    simp [initial] at hmem
  node_incident_label := by
    intro node hmem slot
    simp [initial] at hmem

theorem initial_endpointPartition {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).EndpointPartition where
  frontier_nodup := by
    simp [initial, List.nodup_range]
  consumed_nodup := by
    simp [edgeEndpointIds, initial]
  consumed_bound := by
    intro id hmem
    simp [edgeEndpointIds, initial] at hmem
  frontier_consumed_disjoint := by
    intro id hfrontier hconsumed
    simp [edgeEndpointIds, initial] at hconsumed
  endpoint_covered := by
    intro id hid
    left
    simpa [initial] using (List.mem_range.mpr hid)

theorem initial_nodeIncidentNodup {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).NodeIncidentNodup where
  node_incident_nodup := by
    intro node hmem
    simp [initial] at hmem

theorem initial_ownerIdPartition {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).OwnerIdPartition boundary where
  owner_nodup := by
    simp [ownerEndpointIds, nodeIncidentIds, initial, List.nodup_range]
  owner_bound := by
    intro id hmem
    simpa [ownerEndpointIds, nodeIncidentIds, initial] using hmem
  owner_covered := by
    intro id hid
    simpa [ownerEndpointIds, nodeIncidentIds, initial] using
      (List.mem_range.mpr hid)

theorem EndpointPartition.endpoint_consumed_of_frontier_empty
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    endpoint.val ∈ st.edgeEndpointIds := by
  have hfrontierIds : st.frontierIds = [] := by
    cases hids : st.frontierIds with
    | nil => rfl
    | cons head tail =>
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen
  rcases hp.endpoint_covered endpoint.val endpoint.isLt with hfrontier | hconsumed
  · rw [hfrontierIds] at hfrontier
    cases hfrontier
  · exact hconsumed

def edgeEndpointIdsOfEdges {Sig : Signature}
    (edges : List (RenderEdge Sig)) : List Nat :=
  edges.flatMap fun edge => [edge.left, edge.right]

theorem edgeEndpointIdsOfEdges_tail_nodup
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    (edgeEndpointIdsOfEdges edges).Nodup := by
  simp [edgeEndpointIdsOfEdges] at hnodup
  exact hnodup.2.2

theorem edgeEndpointIdsOfEdges_left_not_tail
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    edge.left ∉ edgeEndpointIdsOfEdges edges := by
  intro hmem
  simp [edgeEndpointIdsOfEdges] at hnodup hmem
  rcases hmem with ⟨edge', hmem, hleft | hright⟩
  · exact (hnodup.1.2 edge' hmem).1 hleft
  · exact (hnodup.1.2 edge' hmem).2 hright

theorem edgeEndpointIdsOfEdges_right_not_tail
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    edge.right ∉ edgeEndpointIdsOfEdges edges := by
  intro hmem
  simp [edgeEndpointIdsOfEdges] at hnodup hmem
  rcases hmem with ⟨edge', hmem, hleft | hright⟩
  · exact (hnodup.2.1 edge' hmem).1 hleft
  · exact (hnodup.2.1 edge' hmem).2 hright

theorem edgeEndpointIdsOfEdges_mem_left
    {Sig : Signature}
    (edges : List (RenderEdge Sig)) (edgeIndex : Fin edges.length) :
    (edges.get edgeIndex).left ∈ edgeEndpointIdsOfEdges edges := by
  simp [edgeEndpointIdsOfEdges]
  exact ⟨edges.get edgeIndex, List.get_mem edges edgeIndex, Or.inl rfl⟩

theorem edgeEndpointIdsOfEdges_mem_right
    {Sig : Signature}
    (edges : List (RenderEdge Sig)) (edgeIndex : Fin edges.length) :
    (edges.get edgeIndex).right ∈ edgeEndpointIdsOfEdges edges := by
  simp [edgeEndpointIdsOfEdges]
  exact ⟨edges.get edgeIndex, List.get_mem edges edgeIndex, Or.inr rfl⟩

theorem edgeEndpointIdsOfEdges_get_left_ne_right
    {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)),
      (edgeEndpointIdsOfEdges edges).Nodup →
        ∀ edgeIndex : Fin edges.length,
          (edges.get edgeIndex).left ≠ (edges.get edgeIndex).right
  | [], _hnodup, edgeIndex => by
      cases edgeIndex with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | edge :: edges, hnodup, edgeIndex => by
      cases edgeIndex with
      | mk idx idxLt =>
          cases idx with
          | zero =>
              simp [edgeEndpointIdsOfEdges] at hnodup
              exact hnodup.1.1
          | succ idx =>
              have tailIndex : Fin edges.length :=
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩
              have hget :
                  (edge :: edges).get ⟨idx + 1, idxLt⟩ =
                    edges.get ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩ := rfl
              rw [hget]
              exact edgeEndpointIdsOfEdges_get_left_ne_right edges
                (edgeEndpointIdsOfEdges_tail_nodup edge edges hnodup)
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩

/--
Find the rendered edge that consumed an endpoint ID.  The input membership is
the consumed side of `EndpointPartition`, not a raw-ID guess.
-/
def edgeEndpointRefOfEndpointId {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)) {id : Nat},
      id ∈ edgeEndpointIdsOfEdges edges →
        { edge : Fin edges.length //
          id = (edges.get edge).left ∨ id = (edges.get edge).right }
  | [], _id, hmem => by
      simp [edgeEndpointIdsOfEdges] at hmem
  | edge :: edges, id, hmem => by
      by_cases hleft : id = edge.left
      · exact ⟨⟨0, by simp⟩, Or.inl hleft⟩
      · by_cases hright : id = edge.right
        · exact ⟨⟨0, by simp⟩, Or.inr hright⟩
        · have hmemAppend :
              id ∈ [edge.left, edge.right] ++ edgeEndpointIdsOfEdges edges := by
            simpa [edgeEndpointIdsOfEdges] using hmem
          have htail : id ∈ edgeEndpointIdsOfEdges edges := by
            rcases List.mem_append.mp hmemAppend with hhead | htail
            · simp at hhead
              rcases hhead with hleft' | hright'
              · exact False.elim (hleft hleft')
              · exact False.elim (hright hright')
            · exact htail
          rcases edgeEndpointRefOfEndpointId edges htail with
            ⟨edgeIndex, hside⟩
          refine ⟨⟨edgeIndex.val + 1, by simp [edgeIndex.isLt]⟩, ?_⟩
          simpa using hside

theorem edgeEndpointRefOfEndpointId_unique {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)) {id : Nat}
      (hmem : id ∈ edgeEndpointIdsOfEdges edges)
      (_hnodup : (edgeEndpointIdsOfEdges edges).Nodup)
      (edgeIndex : Fin edges.length),
      (id = (edges.get edgeIndex).left ∨
        id = (edges.get edgeIndex).right) →
        (edgeEndpointRefOfEndpointId edges hmem).1 = edgeIndex
  | [], _id, _hmem, _hnodup, edgeIndex, _hside => by
      cases edgeIndex with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | edge :: edges, id, hmem, hnodup, edgeIndex, hside => by
      cases edgeIndex with
      | mk idx idxLt =>
          cases idx with
          | zero =>
              simp at hside
              unfold edgeEndpointRefOfEndpointId
              rcases hside with hleftSide | hrightSide
              · simp [hleftSide]
              · by_cases hsame : edge.right = edge.left
                · simp [hrightSide, hsame]
                · simp [hrightSide, hsame]
          | succ idx =>
              let tailIndex : Fin edges.length :=
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩
              have hsideTail :
                  id = (edges.get tailIndex).left ∨
                    id = (edges.get tailIndex).right := by
                simpa [tailIndex] using hside
              unfold edgeEndpointRefOfEndpointId
              by_cases hleft : id = edge.left
              · have htailMem : edge.left ∈ edgeEndpointIdsOfEdges edges := by
                  rw [← hleft]
                  rcases hsideTail with htailLeft | htailRight
                  · rw [htailLeft]
                    exact edgeEndpointIdsOfEdges_mem_left edges tailIndex
                  · rw [htailRight]
                    exact edgeEndpointIdsOfEdges_mem_right edges tailIndex
                exact False.elim
                  (edgeEndpointIdsOfEdges_left_not_tail edge edges hnodup
                    htailMem)
              · by_cases hright : id = edge.right
                · have htailMem :
                      edge.right ∈ edgeEndpointIdsOfEdges edges := by
                    rw [← hright]
                    rcases hsideTail with htailLeft | htailRight
                    · rw [htailLeft]
                      exact edgeEndpointIdsOfEdges_mem_left edges tailIndex
                    · rw [htailRight]
                      exact edgeEndpointIdsOfEdges_mem_right edges tailIndex
                  exact False.elim
                    (edgeEndpointIdsOfEdges_right_not_tail edge edges hnodup
                      htailMem)
                · simp [hleft, hright]
                  have hmemTail : id ∈ edgeEndpointIdsOfEdges edges := by
                    simp [edgeEndpointIdsOfEdges] at hmem
                    rcases hmem with hleftMem | hrightMem | htail
                    · exact False.elim (hleft hleftMem)
                    · exact False.elim (hright hrightMem)
                    · simpa [edgeEndpointIdsOfEdges] using htail
                  have huniq :=
                    edgeEndpointRefOfEndpointId_unique edges hmemTail
                      (edgeEndpointIdsOfEdges_tail_nodup edge edges hnodup)
                      tailIndex hsideTail
                  simpa [tailIndex] using congrArg Fin.val huniq

def endpointEdgeOfPartition {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) : Fin st.edges.length :=
  (edgeEndpointRefOfEndpointId st.edges (id := endpoint.val) (by
    have hconsumed :=
      EndpointPartition.endpoint_consumed_of_frontier_empty hp endpoint
    simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hconsumed)).1

theorem endpointEdgeOfPartition_endpoint
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    endpoint.val =
        (st.edges.get (endpointEdgeOfPartition hp endpoint)).left ∨
      endpoint.val =
        (st.edges.get (endpointEdgeOfPartition hp endpoint)).right := by
  unfold endpointEdgeOfPartition
  have hconsumed :=
    EndpointPartition.endpoint_consumed_of_frontier_empty hp endpoint
  exact
    (edgeEndpointRefOfEndpointId st.edges (id := endpoint.val) (by
      simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hconsumed)).2

theorem endpointEdgeOfPartition_label
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    Sig.portEdge (st.endpoints.get endpoint) =
      (st.edges.get (endpointEdgeOfPartition hp endpoint)).label := by
  let edgeIndex := endpointEdgeOfPartition hp endpoint
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
    simpa [edgeIndex, edge] using
      endpointEdgeOfPartition_endpoint hp endpoint
  change Sig.portEdge (st.endpoints.get endpoint) = edge.label
  rcases hside with hleft | hright
  · have hfin : endpoint = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
      apply Fin.ext
      exact hleft
    calc
      Sig.portEdge (st.endpoints.get endpoint) =
          Sig.portEdge
            (st.endpoints.get
              ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩) := by
        rw [hfin]
      _ = Sig.portEdge edge.leftLabel := by
        rw [hv.edge_left_label edge hedgeMem]
      _ = edge.label := edge.left_label
  · have hfin : endpoint = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
      apply Fin.ext
      exact hright
    calc
      Sig.portEdge (st.endpoints.get endpoint) =
          Sig.portEdge
            (st.endpoints.get
              ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩) := by
        rw [hfin]
      _ = Sig.portEdge edge.rightLabel := by
        rw [hv.edge_right_label edge hedgeMem]
      _ = edge.label := edge.right_label

theorem endpointEdgeOfPartition_eq_of_endpoint_side
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length)
    (edgeIndex : Fin st.edges.length)
    (hside : endpoint.val = (st.edges.get edgeIndex).left ∨
      endpoint.val = (st.edges.get edgeIndex).right) :
    endpointEdgeOfPartition hp endpoint = edgeIndex := by
  unfold endpointEdgeOfPartition
  apply edgeEndpointRefOfEndpointId_unique
  · simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hp.consumed_nodup
  · exact hside

theorem endpointEdgeOfPartition_left
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).left,
          hv.edge_left_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inl rfl

theorem endpointEdgeOfPartition_right
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).right,
          hv.edge_right_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inr rfl

theorem edge_left_ne_right_of_partition
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    (st.edges.get edgeIndex).left ≠ (st.edges.get edgeIndex).right :=
  edgeEndpointIdsOfEdges_get_left_ne_right st.edges
    (by simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hp.consumed_nodup)
    edgeIndex

theorem edgeCompatibleOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (left right : Fin st.endpoints.length)
    (hsame : endpointEdgeOfPartition hp left = endpointEdgeOfPartition hp right)
    (hne : left ≠ right) :
    Sig.compatible (st.endpoints.get left) (st.endpoints.get right) := by
  let edgeIndex := endpointEdgeOfPartition hp left
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  have hleftSide : left.val = edge.left ∨ left.val = edge.right := by
    simpa [edgeIndex, edge] using endpointEdgeOfPartition_endpoint hp left
  have hrightEdge : endpointEdgeOfPartition hp right = edgeIndex := by
    exact hsame.symm
  have hrightSide : right.val = edge.left ∨ right.val = edge.right := by
    have hraw := endpointEdgeOfPartition_endpoint hp right
    simpa [edgeIndex, edge, hrightEdge] using hraw
  rcases hleftSide with hleftL | hleftR
  · rcases hrightSide with hrightL | hrightR
    · have hfin : left = right := by
        apply Fin.ext
        exact hleftL.trans hrightL.symm
      exact False.elim (hne hfin)
    · have hleftFin :
          left = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hleftL
      have hrightFin :
          right = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hrightR
      rw [hleftFin, hrightFin]
      rw [hv.edge_left_label edge hedgeMem]
      rw [hv.edge_right_label edge hedgeMem]
      exact edge.compatible
  · rcases hrightSide with hrightL | hrightR
    · have hleftFin :
          left = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hleftR
      have hrightFin :
          right = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hrightL
      rw [hleftFin, hrightFin]
      rw [hv.edge_right_label edge hedgeMem]
      rw [hv.edge_left_label edge hedgeMem]
      exact Sig.compatible_symm edge.compatible
    · have hfin : left = right := by
        apply Fin.ext
        exact hleftR.trans hrightR.symm
      exact False.elim (hne hfin)

theorem edgeTwoEndpointsOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    ∃ left right : Fin st.endpoints.length,
      left ≠ right ∧
      endpointEdgeOfPartition hp left = edgeIndex ∧
      endpointEdgeOfPartition hp right = edgeIndex ∧
      ∀ endpoint : Fin st.endpoints.length,
        endpointEdgeOfPartition hp endpoint = edgeIndex →
          endpoint = left ∨ endpoint = right := by
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  let leftEndpoint : Fin st.endpoints.length :=
    ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩
  let rightEndpoint : Fin st.endpoints.length :=
    ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩
  refine ⟨leftEndpoint, rightEndpoint, ?_, ?_, ?_, ?_⟩
  · intro hsame
    have hval : edge.left = edge.right := by
      exact congrArg Fin.val hsame
    exact edge_left_ne_right_of_partition hp edgeIndex hval
  · exact endpointEdgeOfPartition_left hv hp edgeIndex
  · exact endpointEdgeOfPartition_right hv hp edgeIndex
  · intro endpoint hendpointEdge
    have hsideRaw := endpointEdgeOfPartition_endpoint hp endpoint
    have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
      simpa [edge, hendpointEdge] using hsideRaw
    rcases hside with hleft | hright
    · left
      apply Fin.ext
      exact hleft
    · right
      apply Fin.ext
      exact hright

/--
The semantic endpoint-to-edge slice of graph evidence derived from renderer
invariants.  Full `PortHypergraphEvidence` additionally needs edge
compatibility, two-endpoint edge laws, boundary ports, constructor incidence,
and owner uniqueness.
-/
structure EndpointEdgeEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  endpointEdge : Fin st.endpoints.length → Fin st.edges.length
  endpoint_edge_label :
    ∀ endpoint : Fin st.endpoints.length,
      Sig.portEdge (st.endpoints.get endpoint) =
        (st.edges.get (endpointEdge endpoint)).label

def endpointEdgeEvidenceOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    EndpointEdgeEvidence st where
  endpointEdge := endpointEdgeOfPartition hp
  endpoint_edge_label := endpointEdgeOfPartition_label hv hp

/--
Renderer-derived semantic edge evidence.  This packages the endpoint-to-edge
assignment together with the compatibility and two-endpoint laws required by
`PortHypergraph`.
-/
structure EdgeEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  endpointEdgeEvidence : EndpointEdgeEvidence st
  edge_compatible :
    ∀ left right : Fin st.endpoints.length,
      endpointEdgeEvidence.endpointEdge left =
        endpointEdgeEvidence.endpointEdge right →
      left ≠ right →
        Sig.compatible (st.endpoints.get left) (st.endpoints.get right)
  edge_two_endpoints :
    ∀ edge : Fin st.edges.length,
      ∃ left right : Fin st.endpoints.length,
        left ≠ right ∧
        endpointEdgeEvidence.endpointEdge left = edge ∧
        endpointEdgeEvidence.endpointEdge right = edge ∧
        ∀ endpoint : Fin st.endpoints.length,
          endpointEdgeEvidence.endpointEdge endpoint = edge →
            endpoint = left ∨ endpoint = right

def edgeEvidenceOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    EdgeEvidence st where
  endpointEdgeEvidence := endpointEdgeEvidenceOfPartition hv hp
  edge_compatible := by
    intro left right hsame hne
    exact edgeCompatibleOfPartition hv hp left right hsame hne
  edge_two_endpoints := by
    intro edge
    exact edgeTwoEndpointsOfPartition hv hp edge

def incidentOfValidIds {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length) :
    List (Fin st.endpoints.length) :=
  List.ofFn fun slot : Fin ((st.nodes.get node).incident.length) =>
    ⟨(st.nodes.get node).incident.get slot,
      hv.node_incident_bound (st.nodes.get node)
        (List.get_mem st.nodes node) slot⟩

theorem incidentOfValidIds_map_val {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length) :
    (incidentOfValidIds hv node).map (fun endpoint => endpoint.val) =
      (st.nodes.get node).incident := by
  apply List.ext_getElem
  · simp [incidentOfValidIds]
  · intro i hleft hright
    simp [incidentOfValidIds]

theorem incidentOfValidIds_val_mem_nodeIncidentIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    ((incidentOfValidIds hv node).get slot).val ∈ st.nodeIncidentIds := by
  simp [incidentOfValidIds, nodeIncidentIds]
  refine ⟨st.nodes.get node, List.get_mem st.nodes node, ?_⟩
  exact List.get_mem (st.nodes.get node).incident
    (Fin.cast (by simp [incidentOfValidIds]) slot)

theorem incidentOfValidIds_exists_of_mem_nodeIncidentIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (endpoint : Fin st.endpoints.length)
    (hnode : endpoint.val ∈ st.nodeIncidentIds) :
    ∃ (node : Fin st.nodes.length)
      (slot : Fin (incidentOfValidIds hv node).length),
      (incidentOfValidIds hv node).get slot = endpoint := by
  have hnodeMem := hnode
  simp [nodeIncidentIds] at hnodeMem
  rcases hnodeMem with ⟨renderNode, hrenderNode, hincidentMem⟩
  rcases list_exists_get_of_mem st.nodes hrenderNode with
    ⟨node, hnodeEq⟩
  have hincidentMem' :
      endpoint.val ∈ (st.nodes.get node).incident := by
    rw [hnodeEq]
    exact hincidentMem
  rcases list_exists_get_of_mem (st.nodes.get node).incident
      hincidentMem' with
    ⟨rawSlot, hrawSlot⟩
  let slot : Fin (incidentOfValidIds hv node).length :=
    Fin.cast (by simp [incidentOfValidIds]) rawSlot
  refine ⟨node, slot, ?_⟩
  apply Fin.ext
  simpa [incidentOfValidIds, slot] using hrawSlot

theorem incidentOfValidIds_length {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length) :
    (incidentOfValidIds hv node).length =
      Sig.arity ((st.nodes.get node).label) :=
  by
    simpa [incidentOfValidIds] using
      hv.node_incident_length (st.nodes.get node) (List.get_mem st.nodes node)

theorem incidentOfValidIds_injective {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (hn : st.NodeIncidentNodup)
    (node : Fin st.nodes.length) :
    Function.Injective fun slot : Fin (incidentOfValidIds hv node).length =>
      (incidentOfValidIds hv node).get slot := by
  intro i j h
  have hi :
      (st.nodes.get node).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) i) =
        (st.nodes.get node).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) j) := by
    have hval := congrArg Fin.val h
    simpa [incidentOfValidIds] using hval
  have horig :=
    list_get_injective_of_nodup (st.nodes.get node).incident
      (hn.node_incident_nodup (st.nodes.get node)
        (List.get_mem st.nodes node)) hi
  apply Fin.ext
  have hval := congrArg Fin.val horig
  simpa using hval

theorem incidentOfValidIds_label {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    st.endpoints.get ((incidentOfValidIds hv node).get slot) =
      Sig.port ((st.nodes.get node).label)
        (Fin.cast (incidentOfValidIds_length hv node) slot) := by
  have hlabel :=
    hv.node_incident_label (st.nodes.get node)
      (List.get_mem st.nodes node)
      (Fin.cast (by simp [incidentOfValidIds]) slot)
  simpa [incidentOfValidIds, incidentOfValidIds_length] using hlabel

theorem boundaryEvidenceOfPrefix_ne_incidentOfValidIds {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary)
    (hv : st.ValidIds)
    (ho : st.OwnerIdPartition boundary)
    (b : Fin boundary.length) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    (boundaryEvidenceOfPrefix pref).boundaryPort b ≠
      (incidentOfValidIds hv node).get slot := by
  intro h
  have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) h
  have hboundary : b.val ∈ List.range boundary.length :=
    List.mem_range.mpr b.isLt
  have hnodeRaw :
      ((incidentOfValidIds hv node).get slot).val ∈ st.nodeIncidentIds :=
    incidentOfValidIds_val_mem_nodeIncidentIds hv node slot
  have hnode : b.val ∈ st.nodeIncidentIds := by
    have hval' :
        ((boundaryEvidenceOfPrefix pref).boundaryPort b).val =
          ((incidentOfValidIds hv node).get slot).val := by
      simpa using hval
    have hincident :
        ((incidentOfValidIds hv node).get slot).val = b.val := by
      exact hval'.symm.trans
        (boundaryEvidenceOfPrefix_boundaryPort_val pref b)
    exact hincident ▸ hnodeRaw
  exact ho.boundary_nodeIncidentIds_disjoint hboundary hnode

theorem nodeIncidentIds_get_node_eq_of_nodup {Sig : Signature} :
    ∀ (nodes : List (RenderNode Sig)),
      (nodes.flatMap fun node => node.incident).Nodup →
      ∀ {leftNode rightNode : Fin nodes.length}
        {leftSlot : Fin ((nodes.get leftNode).incident.length)}
        {rightSlot : Fin ((nodes.get rightNode).incident.length)},
        (nodes.get leftNode).incident.get leftSlot =
          (nodes.get rightNode).incident.get rightSlot →
        leftNode = rightNode
  | [], _hnodup, leftNode, _rightNode, _leftSlot, _rightSlot, _h => by
      cases leftNode with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | head :: tail, hnodup, leftNode, rightNode, leftSlot, rightSlot, h => by
      have hflat :
          (head.incident ++ tail.flatMap fun node => node.incident).Nodup := by
        simpa using hnodup
      cases leftNode with
      | mk leftVal leftLt =>
          cases rightNode with
          | mk rightVal rightLt =>
              cases leftVal with
              | zero =>
                  cases rightVal with
                  | zero => rfl
                  | succ rightTailVal =>
                      let rightTail : Fin tail.length :=
                        ⟨rightTailVal, Nat.lt_of_succ_lt_succ rightLt⟩
                      let rightSlotTail :
                          Fin ((tail.get rightTail).incident.length) :=
                        Fin.cast (by simp [rightTail]) rightSlot
                      have hleftMem :
                          head.incident.get leftSlot ∈ head.incident :=
                        List.get_mem head.incident leftSlot
                      have hrightMemRaw :
                          (tail.get rightTail).incident.get rightSlotTail ∈
                            tail.flatMap fun node => node.incident := by
                        simp
                        exact ⟨tail.get rightTail, List.get_mem tail rightTail,
                          List.get_mem (tail.get rightTail).incident rightSlotTail⟩
                      have heq :
                          head.incident.get leftSlot =
                            (tail.get rightTail).incident.get rightSlotTail := by
                        simpa [rightTail, rightSlotTail] using h
                      have hrightMem :
                          head.incident.get leftSlot ∈
                            tail.flatMap fun node => node.incident := by
                        rw [← heq] at hrightMemRaw
                        exact hrightMemRaw
                      exact False.elim
                        (nodup_append_disjoint head.incident
                          (tail.flatMap fun node => node.incident)
                          hflat hleftMem hrightMem)
              | succ leftTailVal =>
                  cases rightVal with
                  | zero =>
                      let leftTail : Fin tail.length :=
                        ⟨leftTailVal, Nat.lt_of_succ_lt_succ leftLt⟩
                      let leftSlotTail :
                          Fin ((tail.get leftTail).incident.length) :=
                        Fin.cast (by simp [leftTail]) leftSlot
                      have hleftMemRaw :
                          (tail.get leftTail).incident.get leftSlotTail ∈
                            tail.flatMap fun node => node.incident := by
                        simp
                        exact ⟨tail.get leftTail, List.get_mem tail leftTail,
                          List.get_mem (tail.get leftTail).incident leftSlotTail⟩
                      have heq :
                          (tail.get leftTail).incident.get leftSlotTail =
                            head.incident.get rightSlot := by
                        simpa [leftTail, leftSlotTail] using h
                      have hleftMem :
                          head.incident.get rightSlot ∈
                            tail.flatMap fun node => node.incident := by
                        rw [heq] at hleftMemRaw
                        exact hleftMemRaw
                      have hrightMem :
                          head.incident.get rightSlot ∈ head.incident :=
                        List.get_mem head.incident rightSlot
                      exact False.elim
                        (nodup_append_disjoint head.incident
                          (tail.flatMap fun node => node.incident)
                          hflat hrightMem hleftMem)
                  | succ rightTailVal =>
                      let leftTail : Fin tail.length :=
                        ⟨leftTailVal, Nat.lt_of_succ_lt_succ leftLt⟩
                      let rightTail : Fin tail.length :=
                        ⟨rightTailVal, Nat.lt_of_succ_lt_succ rightLt⟩
                      let leftSlotTail :
                          Fin ((tail.get leftTail).incident.length) :=
                        Fin.cast (by simp [leftTail]) leftSlot
                      let rightSlotTail :
                          Fin ((tail.get rightTail).incident.length) :=
                        Fin.cast (by simp [rightTail]) rightSlot
                      have htail :
                          (tail.get leftTail).incident.get leftSlotTail =
                            (tail.get rightTail).incident.get rightSlotTail := by
                        simpa [leftTail, rightTail, leftSlotTail, rightSlotTail]
                          using h
                      have htailNodup :
                          (tail.flatMap fun node => node.incident).Nodup :=
                        nodup_append_right head.incident
                          (tail.flatMap fun node => node.incident) hflat
                      have hnodeTail :
                          leftTail = rightTail :=
                        nodeIncidentIds_get_node_eq_of_nodup tail htailNodup
                          htail
                      apply Fin.ext
                      have hval := congrArg (fun idx : Fin tail.length => idx.val)
                        hnodeTail
                      exact congrArg Nat.succ hval

theorem incidentOfValidIds_eq_node_eq {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (ho : st.OwnerIdPartition boundary)
    {leftNode rightNode : Fin st.nodes.length}
    {leftSlot : Fin (incidentOfValidIds hv leftNode).length}
    {rightSlot : Fin (incidentOfValidIds hv rightNode).length}
    (h :
      (incidentOfValidIds hv leftNode).get leftSlot =
        (incidentOfValidIds hv rightNode).get rightSlot) :
    leftNode = rightNode := by
  have hraw :
      (st.nodes.get leftNode).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) leftSlot) =
        (st.nodes.get rightNode).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) rightSlot) := by
    have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) h
    simpa [incidentOfValidIds] using hval
  exact nodeIncidentIds_get_node_eq_of_nodup st.nodes
    (by simpa [nodeIncidentIds] using ho.nodeIncidentIds_nodup) hraw

/--
Renderer-derived constructor incidence evidence.  It turns each rendered node's
ordered incident endpoint IDs into finite endpoint references and proves the
length, injectivity, and label laws required by `PortHypergraph`.
-/
structure IncidenceEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  incident : Fin st.nodes.length → List (Fin st.endpoints.length)
  incident_length :
    ∀ node : Fin st.nodes.length,
      (incident node).length = Sig.arity ((st.nodes.get node).label)
  incident_injective :
    ∀ node : Fin st.nodes.length,
      Function.Injective fun slot : Fin (incident node).length =>
        (incident node).get slot
  incidence_label :
    ∀ (node : Fin st.nodes.length) (slot : Fin (incident node).length),
      st.endpoints.get ((incident node).get slot) =
        Sig.port ((st.nodes.get node).label) (Fin.cast (incident_length node) slot)

def incidenceEvidenceOfValidIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (hn : st.NodeIncidentNodup) :
    IncidenceEvidence st where
  incident := incidentOfValidIds hv
  incident_length := incidentOfValidIds_length hv
  incident_injective := incidentOfValidIds_injective hv hn
  incidence_label := incidentOfValidIds_label hv

theorem ValidIds.frontier_head_label {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {st : RenderState Sig (active :: frontier)}
    (hv : st.ValidIds)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    st.endpoints.get
      ⟨activeId, hv.frontier_bound activeId (by rw [hids]; simp)⟩ =
      active := by
  have hlabel :=
    hv.frontier_label 0 (by rw [hids]; simp) (by simp)
  simpa [hids] using hlabel

theorem ValidIds.frontier_tail_label {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {st : RenderState Sig (active :: frontier)}
    (hv : st.ValidIds)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (hrest : restIds.length = frontier.length)
    (i : Fin restIds.length) :
    st.endpoints.get
      ⟨restIds.get i,
        hv.frontier_bound (restIds.get i) (by rw [hids]; simp)⟩ =
      frontier.get (Fin.cast hrest i) := by
  have hlabel :=
    hv.frontier_label (i.val + 1)
      (by rw [hids]; simp [i.isLt])
      (by
        have hi : i.val < frontier.length := by
          simp [← hrest, i.isLt]
        simpa using Nat.succ_lt_succ hi)
  simpa [hids] using hlabel

/--
Raw endpoint-ID reachability for intermediate renderer states.  This relation
is defined before the semantic `PortHypergraph` exists, so it can be preserved
through render steps that still have pending frontier endpoints.
-/
inductive RawReachesBoundary {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundaryLength : Nat) :
    Nat → Prop
  | boundary {id : Nat} (hboundary : id ∈ List.range boundaryLength) :
      RawReachesBoundary st boundaryLength id
  | throughEdgeLeft (edge : RenderEdge Sig) (hmem : edge ∈ st.edges)
      (reach : RawReachesBoundary st boundaryLength edge.left) :
      RawReachesBoundary st boundaryLength edge.right
  | throughEdgeRight (edge : RenderEdge Sig) (hmem : edge ∈ st.edges)
      (reach : RawReachesBoundary st boundaryLength edge.right) :
      RawReachesBoundary st boundaryLength edge.left
  | throughConstructor (node : RenderNode Sig) (hmem : node ∈ st.nodes)
      (fromSlot toSlot : Fin node.incident.length)
      (reach :
        RawReachesBoundary st boundaryLength
          (node.incident.get fromSlot)) :
      RawReachesBoundary st boundaryLength (node.incident.get toSlot)

theorem RawReachesBoundary.mono
    {Sig : Signature} {frontier frontier' : List Sig.Port}
    {st : RenderState Sig frontier} {st' : RenderState Sig frontier'}
    {boundaryLength id : Nat}
    (hedges : ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge ∈ st'.edges)
    (hnodes : ∀ node : RenderNode Sig, node ∈ st.nodes → node ∈ st'.nodes)
    (reach : st.RawReachesBoundary boundaryLength id) :
    st'.RawReachesBoundary boundaryLength id := by
  induction reach with
  | boundary hboundary =>
      exact RawReachesBoundary.boundary hboundary
  | throughEdgeLeft edge hmem _reach ih =>
      exact RawReachesBoundary.throughEdgeLeft edge (hedges edge hmem) ih
  | throughEdgeRight edge hmem _reach ih =>
      exact RawReachesBoundary.throughEdgeRight edge (hedges edge hmem) ih
  | throughConstructor node hmem fromSlot toSlot _reach ih =>
      exact RawReachesBoundary.throughConstructor node (hnodes node hmem)
        fromSlot toSlot ih

/--
Reachability invariant for intermediate renderer states.  Every pending
endpoint is already in the boundary-connected component, and every rendered
constructor has at least one incident endpoint in that component.
-/
structure Reachability {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : Prop where
  frontier_reaches :
    ∀ id : Nat, id ∈ st.frontierIds →
      st.RawReachesBoundary boundary.length id
  node_reaches :
    ∀ node : RenderNode Sig, node ∈ st.nodes →
      ∃ slot : Fin node.incident.length,
        st.RawReachesBoundary boundary.length (node.incident.get slot)

theorem initial_reachability {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).Reachability boundary where
  frontier_reaches := by
    intro id hid
    exact RawReachesBoundary.boundary (by
      simpa [initial] using hid)
  node_reaches := by
    intro node hmem
    simp [initial] at hmem

end RenderState

namespace Diag

variable {Sig : Signature}

def freshNodeEndpoints (start arity : Nat) : List Nat :=
  (List.range arity).map fun offset => start + offset

@[simp]
theorem freshNodeEndpoints_length (start arity : Nat) :
    (freshNodeEndpoints start arity).length = arity := by
  simp [freshNodeEndpoints]

theorem freshNodeEndpoints_get (start arity : Nat)
    (i : Fin (freshNodeEndpoints start arity).length) :
    (freshNodeEndpoints start arity).get i = start + i.val := by
  simp [freshNodeEndpoints]

theorem freshNodeEndpoints_mem_lt {start arity id : Nat}
    (hmem : id ∈ freshNodeEndpoints start arity) :
    id < start + arity := by
  rcases list_exists_get_of_mem (freshNodeEndpoints start arity) hmem with
    ⟨i, hi⟩
  rw [← hi, freshNodeEndpoints_get]
  have hiLt : i.val < arity := by
    simpa using i.isLt
  omega

theorem freshNodeEndpoints_mem_ge {start arity id : Nat}
    (hmem : id ∈ freshNodeEndpoints start arity) :
    start ≤ id := by
  rcases list_exists_get_of_mem (freshNodeEndpoints start arity) hmem with
    ⟨i, hi⟩
  rw [← hi, freshNodeEndpoints_get]
  exact Nat.le_add_right start i.val

theorem freshNodeEndpoints_mem_of_bounds {start arity id : Nat}
    (hge : start ≤ id) (hlt : id < start + arity) :
    id ∈ freshNodeEndpoints start arity := by
  simp [freshNodeEndpoints]
  refine ⟨id - start, ?_, ?_⟩
  · omega
  · omega

theorem freshNodeEndpoints_nodup (start arity : Nat) :
    (freshNodeEndpoints start arity).Nodup := by
  apply list_nodup_of_get_injective
  intro i j hget
  change (freshNodeEndpoints start arity).get i =
    (freshNodeEndpoints start arity).get j at hget
  rw [freshNodeEndpoints_get, freshNodeEndpoints_get] at hget
  apply Fin.ext
  omega

theorem freshNodeEndpoints_label_append
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (hv : st.ValidIds) (node : Sig.Node)
    (i : Fin (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).length)
    (hbound :
      (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i <
        (st.endpoints ++ Sig.nodePorts node).length) :
    (st.endpoints ++ Sig.nodePorts node).get
        ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i,
          hbound⟩ =
      (Sig.nodePorts node).get
        (Fin.cast (by simp [freshNodeEndpoints, Signature.nodePorts]) i) := by
  have hget :=
    freshNodeEndpoints_get st.nextEndpoint (Sig.arity node) i
  have hbound' :
      st.nextEndpoint + i.val <
        (st.endpoints ++ Sig.nodePorts node).length := by
    simpa [← hget] using hbound
  have hright :
      st.endpoints.length ≤ st.nextEndpoint + i.val := by
    have hnext := hv.nextEndpoint_eq
    omega
  calc
    (st.endpoints ++ Sig.nodePorts node).get
        ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i,
          hbound⟩ =
        (st.endpoints ++ Sig.nodePorts node).get
          ⟨st.nextEndpoint + i.val, hbound'⟩ := by
          apply congrArg (fun idx =>
            (st.endpoints ++ Sig.nodePorts node).get idx)
          apply Fin.ext
          exact hget
    _ =
        (Sig.nodePorts node).get
          ⟨st.nextEndpoint + i.val - st.endpoints.length, by
            have hlen :
                (st.endpoints ++ Sig.nodePorts node).length =
                  st.endpoints.length + (Sig.nodePorts node).length := by
              simp
            omega⟩ := by
          exact list_get_append_right st.endpoints (Sig.nodePorts node)
            hright hbound'
    _ =
        (Sig.nodePorts node).get
          (Fin.cast (by simp [freshNodeEndpoints, Signature.nodePorts]) i) := by
          have hsub :
              st.nextEndpoint + i.val - st.endpoints.length = i.val := by
            have hnext := hv.nextEndpoint_eq
            omega
          apply congrArg (fun idx => (Sig.nodePorts node).get idx)
          apply Fin.ext
          simp [hsub]

/--
One `connect` rendering step.  The type records the frontier effect: the
active endpoint and selected mate are consumed, leaving `eraseFin frontier
mate`.
-/
def connectStep {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    RenderState Sig (eraseFin frontier mate) :=
  match hids : st.frontierIds with
  | [] =>
      False.elim (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen)
  | activeId :: restIds =>
      have hrest : restIds.length = frontier.length := by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simpa using Nat.succ.inj hlen
      let mateId := restIds.get (Fin.cast hrest.symm mate)
      let childIds := eraseFin restIds (Fin.cast hrest.symm mate)
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := frontier.get mate
             left := activeId
             right := mateId
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes
        frontierIds := childIds
        frontierIds_length := by
          dsimp [childIds]
          simp [eraseFin_length, hrest] }

/--
One `bud` rendering step.  The type records the frontier effect: the active
endpoint and selected constructor entry are consumed, and the remaining ordered
constructor endpoints are appended after the existing rest frontier.
-/
def budStep {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
  match hids : st.frontierIds with
  | [] =>
      False.elim (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen)
  | activeId :: restIds =>
      have hrest : restIds.length = frontier.length := by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simpa using Nat.succ.inj hlen
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let entryId := nodeEndpoints.get
        (Fin.cast (by simp [nodeEndpoints]) entry)
      let childIds := restIds ++
        eraseFin nodeEndpoints (Fin.cast (by simp [nodeEndpoints]) entry)
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := Sig.port node entry
             left := activeId
             right := entryId
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := childIds
        frontierIds_length := by
          dsimp [childIds]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            nodeEndpoints, eraseFin_length] }

theorem connectStep_edge_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {edge : RenderEdge Sig}
    (hmem : edge ∈ st.edges) :
    edge ∈ (connectStep mate ok st).edges := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem connectStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ st.nodes) :
    node ∈ (connectStep mate ok st).nodes := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simpa using hmem

theorem connectStep_node_mem_old_of_child
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ (connectStep mate ok st).nodes) :
    node ∈ st.nodes := by
  unfold connectStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simpa using hmem

/-- The concrete edge introduced by a `connect` render step is present in the
step result. -/
theorem connectStep_new_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := frontier.get mate
       left := activeId
       right :=
        restIds.get (Fin.cast (by
          have hlen := st.frontierIds_length
          rw [hids] at hlen
          exact (Nat.succ.inj hlen).symm) mate)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (connectStep mate ok st).edges := by
  unfold connectStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp

theorem connectStep_frontierIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (connectStep mate ok st).frontierIds =
      eraseFin restIds (Fin.cast (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        exact (Nat.succ.inj hlen).symm) mate) := by
  unfold connectStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp

theorem connectStep_frontier_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {id : Nat}
    (hmem : id ∈ (connectStep mate ok st).frontierIds) :
    id ∈ st.frontierIds := by
  unfold connectStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    rw [hids]
    right
    exact mem_of_mem_eraseFin restIds (Fin.cast hrest.symm mate) hmem

theorem connectStep_rawReachesBoundary_of_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port} {id : Nat}
    (reach : st.RawReachesBoundary boundary.length id) :
    (connectStep mate ok st).RawReachesBoundary boundary.length id :=
  RenderState.RawReachesBoundary.mono
    (st := st)
    (st' := connectStep mate ok st)
    (boundaryLength := boundary.length)
    (id := id)
    (fun _edge hmem => connectStep_edge_mem_old mate ok st hmem)
    (fun _node hmem => connectStep_node_mem_old mate ok st hmem)
    reach

theorem connectStep_reachability {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary) :
    (connectStep mate ok st).Reachability boundary where
  frontier_reaches := by
    intro id hmem
    exact connectStep_rawReachesBoundary_of_old mate ok st
      (hr.frontier_reaches id
        (connectStep_frontier_mem_old mate ok st hmem))
  node_reaches := by
    intro node hmem
    rcases hr.node_reaches node
        (connectStep_node_mem_old_of_child mate ok st hmem) with
      ⟨slot, reach⟩
    exact ⟨slot, connectStep_rawReachesBoundary_of_old mate ok st reach⟩

theorem budStep_edge_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {edge : RenderEdge Sig}
    (hmem : edge ∈ st.edges) :
    edge ∈ (budStep node entry ok st).edges := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem budStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {renderNode : RenderNode Sig}
    (hmem : renderNode ∈ st.nodes) :
    renderNode ∈ (budStep node entry ok st).nodes := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem budStep_rawReachesBoundary_of_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port} {id : Nat}
    (reach : st.RawReachesBoundary boundary.length id) :
    (budStep node entry ok st).RawReachesBoundary boundary.length id :=
  RenderState.RawReachesBoundary.mono
    (st := st)
    (st' := budStep node entry ok st)
    (boundaryLength := boundary.length)
    (id := id)
    (fun _edge hmem => budStep_edge_mem_old node entry ok st hmem)
    (fun _node hmem => budStep_node_mem_old node entry ok st hmem)
    reach

theorem budStep_node_mem_old_or_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {renderNode : RenderNode Sig}
    (hmem : renderNode ∈ (budStep node entry ok st).nodes) :
    renderNode ∈ st.nodes ∨
      renderNode =
        { label := node
          incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } := by
  unfold budStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [freshNodeEndpoints] at hmem
    exact hmem

theorem budStep_frontier_mem_old_or_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {id : Nat}
    (hmem : id ∈ (budStep node entry ok st).frontierIds) :
    id ∈ st.frontierIds ∨
      id ∈
        eraseFin (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
          (Fin.cast (by simp [freshNodeEndpoints]) entry) := by
  unfold budStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    simp [freshNodeEndpoints] at hmem
    rcases hmem with hold | hnew
    · left
      rw [hids]
      simp [hold]
    · right
      simpa [freshNodeEndpoints] using hnew

theorem budStep_new_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := Sig.port node entry
       left := activeId
       right :=
        (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
          (Fin.cast (by simp [freshNodeEndpoints]) entry)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (budStep node entry ok st).edges := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp [freshNodeEndpoints]

theorem budStep_frontierIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (budStep node entry ok st).frontierIds =
      restIds ++
        eraseFin (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
          (Fin.cast (by simp [freshNodeEndpoints]) entry) := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp [freshNodeEndpoints]

theorem budStep_new_node_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ({ label := node
       incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } :
        RenderNode Sig) ∈
      (budStep node entry ok st).nodes := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · simp [freshNodeEndpoints]

theorem budStep_entry_rawReachesBoundary
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (budStep node entry ok st).RawReachesBoundary boundary.length
      ((freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
        (Fin.cast (by simp [freshNodeEndpoints]) entry)) := by
  let entryIdx : Fin (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).length :=
    Fin.cast (by simp [freshNodeEndpoints]) entry
  let entryId := (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get entryIdx
  let newEdge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := entryId
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hactiveReach :
      st.RawReachesBoundary boundary.length activeId :=
    hr.frontier_reaches activeId (by
      rw [hids]
      simp)
  have hactiveReachChild :
      (budStep node entry ok st).RawReachesBoundary boundary.length activeId :=
    budStep_rawReachesBoundary_of_old node entry ok st hactiveReach
  change
    (budStep node entry ok st).RawReachesBoundary boundary.length entryId
  exact RenderState.RawReachesBoundary.throughEdgeLeft newEdge
    (by
      dsimp [newEdge, entryId, entryIdx]
      exact budStep_new_edge_mem node entry ok st hids)
    hactiveReachChild

theorem budStep_fresh_rawReachesBoundary
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    {id : Nat}
    (hfresh :
      id ∈ freshNodeEndpoints st.nextEndpoint (Sig.arity node)) :
    (budStep node entry ok st).RawReachesBoundary boundary.length id := by
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    Fin.cast (by simp [nodeEndpoints, freshNodeEndpoints]) entry
  rcases list_exists_get_of_mem nodeEndpoints hfresh with ⟨toSlot, hto⟩
  let newNode : RenderNode Sig := { label := node, incident := nodeEndpoints }
  have hentryReach :
      (budStep node entry ok st).RawReachesBoundary boundary.length
        (nodeEndpoints.get entryIdx) := by
    dsimp [nodeEndpoints, entryIdx]
    exact budStep_entry_rawReachesBoundary node entry ok st hr hids
  have htoReach :
      (budStep node entry ok st).RawReachesBoundary boundary.length
        (newNode.incident.get toSlot) :=
    RenderState.RawReachesBoundary.throughConstructor newNode
      (by
        dsimp [newNode, nodeEndpoints]
        exact budStep_new_node_mem node entry ok st)
      entryIdx toSlot hentryReach
  exact hto ▸ htoReach

theorem budStep_reachability {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary) :
    (budStep node entry ok st).Reachability boundary := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      refine
        { frontier_reaches := ?_
          node_reaches := ?_ }
      · intro id hmem
        rcases budStep_frontier_mem_old_or_new node entry ok st hmem with
          hold | hnew
        · exact budStep_rawReachesBoundary_of_old node entry ok st
            (hr.frontier_reaches id hold)
        · exact budStep_fresh_rawReachesBoundary node entry ok st hr hids
            (mem_of_mem_eraseFin
              (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
              (Fin.cast (by simp [freshNodeEndpoints]) entry)
              hnew)
      · intro renderNode hmem
        rcases budStep_node_mem_old_or_new node entry ok st hmem with
          hold | hnew
        · rcases hr.node_reaches renderNode hold with ⟨slot, reach⟩
          exact ⟨slot, budStep_rawReachesBoundary_of_old node entry ok st reach⟩
        · subst renderNode
          let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
          let entryIdx : Fin nodeEndpoints.length :=
            Fin.cast (by simp [nodeEndpoints, freshNodeEndpoints]) entry
          refine ⟨entryIdx, ?_⟩
          dsimp [nodeEndpoints, entryIdx]
          exact budStep_entry_rawReachesBoundary node entry ok st hr hids

theorem connectStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (connectStep mate ok st).ValidIds := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    dsimp
    refine
      { nextEndpoint_eq := hv.nextEndpoint_eq
        frontier_bound := ?_
        frontier_label := ?_
        edge_left_bound := ?_
        edge_right_bound := ?_
        edge_left_label := ?_
        edge_right_label := ?_
        node_incident_length := hv.node_incident_length
        node_incident_bound := hv.node_incident_bound
        node_incident_label := hv.node_incident_label }
    · intro id hid
      exact hv.frontier_bound id (by
        rw [hids]
        right
        exact mem_of_mem_eraseFin restIds
          (Fin.cast hrest.symm mate) hid)
    · intro n hid hfrontier
      let idx : Fin restIds.length := Fin.cast hrest.symm mate
      have hrel :
          ∀ (n : Nat) (hx : n < restIds.length)
            (hy : n < frontier.length),
            ∃ hbound : restIds.get ⟨n, hx⟩ < st.endpoints.length,
              st.endpoints.get ⟨restIds.get ⟨n, hx⟩, hbound⟩ =
                frontier.get ⟨n, hy⟩ := by
        intro n hx hy
        have hlabel :=
          hv.frontier_tail_label hids hrest ⟨n, hx⟩
        refine ⟨hv.frontier_bound (restIds.get ⟨n, hx⟩) ?_, ?_⟩
        · rw [hids]
          right
          exact List.get_mem restIds ⟨n, hx⟩
        · simpa using hlabel
      have haligned :=
        eraseFin_pointwise_relation
          (R := fun id label =>
            ∃ hbound : id < st.endpoints.length,
              st.endpoints.get ⟨id, hbound⟩ = label)
          hrest hrel idx mate (by simp [idx]) n hid hfrontier
      rcases haligned with ⟨hbound, hlabel⟩
      simpa using hlabel
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_left_bound edge hold
      · cases hnew
        exact hv.frontier_bound activeId (by rw [hids]; simp)
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_right_bound edge hold
      · cases hnew
        exact hv.frontier_bound
          (restIds.get (Fin.cast hrest.symm mate)) (by
            rw [hids]
            right
            exact List.get_mem restIds (Fin.cast hrest.symm mate))
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_left_label edge hold
      · cases hnew
        exact hv.frontier_head_label hids
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_right_label edge hold
      · cases hnew
        exact hv.frontier_tail_label hids hrest (Fin.cast hrest.symm mate)

theorem connectStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (connectStep mate ok st).EndpointPartition := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let idx : Fin restIds.length := Fin.cast hrest.symm mate
    have oldFrontierNodup : (activeId :: restIds).Nodup := by
      simpa [hids] using hp.frontier_nodup
    have active_not_rest : activeId ∉ restIds := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.1
    have rest_nodup : restIds.Nodup := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.2
    have active_ne_mate : activeId ≠ restIds.get idx := by
      intro hsame
      exact active_not_rest (by
        rw [hsame]
        exact List.get_mem restIds idx)
    have active_old_frontier : activeId ∈ st.frontierIds := by
      rw [hids]
      simp
    have mate_old_frontier : restIds.get idx ∈ st.frontierIds := by
      rw [hids]
      right
      exact List.get_mem restIds idx
    dsimp
    let newEdge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right := restIds.get idx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    let child : RenderState Sig (eraseFin frontier mate) :=
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges ++ [newEdge]
        nodes := st.nodes
        frontierIds := eraseFin restIds idx
        frontierIds_length := by
          dsimp [idx]
          simp [eraseFin_length, hrest] }
    change child.EndpointPartition
    have childConsumed_eq :
        child.edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, restIds.get idx] := by
      simp [child, newEdge, RenderState.edgeEndpointIds]
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · exact nodup_eraseFin restIds idx rest_nodup
    · have hnodup :
          (st.edgeEndpointIds ++ [activeId, restIds.get idx]).Nodup := by
        apply nodup_append_of_nodup_disjoint
        · exact hp.consumed_nodup
        · have hpair : ([activeId, restIds.get idx] : List Nat).Nodup := by
            simp
            exact active_ne_mate
          exact hpair
        · intro id hold hnew
          simp at hnew
          rcases hnew with hactive | hmate
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hactive] using active_old_frontier) hold
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hmate] using mate_old_frontier) hold
      rw [childConsumed_eq]
      exact hnodup
    · intro id hmem
      rw [childConsumed_eq] at hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hp.consumed_bound id hold
      · rcases hnew with hactive | hmate
        · have hbound := hv.frontier_bound activeId active_old_frontier
          simpa [hactive] using hbound
        · have hbound := hv.frontier_bound (restIds.get idx) mate_old_frontier
          simpa [hmate] using hbound
    · intro id hfrontier hconsumed
      rw [childConsumed_eq] at hconsumed
      simp at hconsumed
      rcases hconsumed with hold | hnew
      · have oldFrontier : id ∈ st.frontierIds := by
          rw [hids]
          right
          exact mem_of_mem_eraseFin restIds idx hfrontier
        exact hp.frontier_consumed_disjoint id oldFrontier hold
      · rcases hnew with hactive | hmate
        · have hrestMem : id ∈ restIds :=
            mem_of_mem_eraseFin restIds idx hfrontier
          exact active_not_rest (by simpa [hactive] using hrestMem)
        · have hnotMate :
            restIds.get idx ∉ eraseFin restIds idx :=
            get_not_mem_eraseFin_of_nodup restIds idx rest_nodup
          exact hnotMate (by simpa [hmate] using hfrontier)
    · intro id hid
      rcases hp.endpoint_covered id hid with holdFrontier | holdConsumed
      · rw [hids] at holdFrontier
        simp at holdFrontier
        rcases holdFrontier with hactive | hrestMem
        · right
          rw [childConsumed_eq]
          simp [hactive]
        · by_cases hmate : id = restIds.get idx
          · right
            rw [childConsumed_eq]
            simp [hmate]
          · left
            exact mem_eraseFin_of_mem_ne_get restIds idx hrestMem hmate
      · right
        rw [childConsumed_eq]
        simp [holdConsumed]

theorem connectStep_nodeIncidentNodup {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hn : st.NodeIncidentNodup) :
    (connectStep mate ok st).NodeIncidentNodup := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · constructor
    intro node hmem
    exact hn.node_incident_nodup node hmem

theorem connectStep_ownerIdPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (connectStep mate ok st).OwnerIdPartition boundary := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · constructor
    · simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
        using ho.owner_nodup
    · intro id hmem
      exact ho.owner_bound id (by
        simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using hmem)
    · intro id hid
      simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds] using
        ho.owner_covered id hid

theorem budStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (budStep node entry ok st).ValidIds := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    dsimp
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    have nodeEndpoints_length :
        nodeEndpoints.length = Sig.arity node := by
      simp [nodeEndpoints]
    have nodeEndpoints_labels :
        ∀ (n : Nat) (hid : n < nodeEndpoints.length)
          (hlabel : n < (Sig.nodePorts node).length),
          ∃ hbound : nodeEndpoints.get ⟨n, hid⟩ <
              (st.endpoints ++ Sig.nodePorts node).length,
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨nodeEndpoints.get ⟨n, hid⟩, hbound⟩ =
              (Sig.nodePorts node).get ⟨n, hlabel⟩ := by
      intro n hid hlabel
      have hbound :
          nodeEndpoints.get ⟨n, hid⟩ <
            (st.endpoints ++ Sig.nodePorts node).length := by
        have hlt := freshNodeEndpoints_mem_lt
          (start := st.nextEndpoint) (arity := Sig.arity node)
          (id := nodeEndpoints.get ⟨n, hid⟩)
          (by
            simp [nodeEndpoints])
        have hnext := hv.nextEndpoint_eq
        simp [Signature.nodePorts] at hlt ⊢
        omega
      refine ⟨hbound, ?_⟩
      have hlabel' :=
        freshNodeEndpoints_label_append st hv node ⟨n, hid⟩ hbound
      simpa [nodeEndpoints] using hlabel'
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      have hle :
          st.endpoints.length ≤
            (st.endpoints ++ Sig.nodePorts node).length := by
        simp
      exact Nat.lt_of_lt_of_le hbound hle
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      simp [Signature.nodePorts] at hlt ⊢
      omega
    refine
      { nextEndpoint_eq := ?_
        frontier_bound := ?_
        frontier_label := ?_
        edge_left_bound := ?_
        edge_right_bound := ?_
        edge_left_label := ?_
        edge_right_label := ?_
        node_incident_length := ?_
        node_incident_bound := ?_
        node_incident_label := ?_ }
    · simp [Signature.nodePorts, hv.nextEndpoint_eq]
    · intro id hid
      simp at hid
      rcases hid with hold | hnew
      · have holdBound := hv.frontier_bound id (by
          rw [hids]
          right
          exact hold)
        exact old_bound_lift holdBound
      · have hmem : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hnew
        exact fresh_bound_of_mem hmem
    · intro n hid hfrontier
      let portEntry : Fin (Sig.nodePorts node).length :=
        Fin.cast (by simp [Signature.nodePorts]) entry
      have hleft :
          ∀ (n : Nat) (hid : n < restIds.length)
            (hlabel : n < frontier.length),
            ∃ hbound : restIds.get ⟨n, hid⟩ <
                (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                  ⟨restIds.get ⟨n, hid⟩, hbound⟩ =
                frontier.get ⟨n, hlabel⟩ := by
        intro n hid hlabel
        have oldLabel :=
          hv.frontier_tail_label hids hrest ⟨n, hid⟩
        have oldBound :=
          hv.frontier_bound (restIds.get ⟨n, hid⟩) (by
            rw [hids]
            right
            exact List.get_mem restIds ⟨n, hid⟩)
        refine ⟨old_bound_lift oldBound, ?_⟩
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨restIds.get ⟨n, hid⟩, old_bound_lift oldBound⟩ =
              st.endpoints.get
                ⟨restIds.get ⟨n, hid⟩, oldBound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) oldBound (old_bound_lift oldBound)
          _ = frontier.get ⟨n, hlabel⟩ := by
              simpa using oldLabel
      have hright :
          ∀ (n : Nat)
            (hid : n < (eraseFin nodeEndpoints entryIdx).length)
            (hlabel : n < (Sig.nodePortsExcept node entry).length),
            ∃ hbound : (eraseFin nodeEndpoints entryIdx).get ⟨n, hid⟩ <
                (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                  ⟨(eraseFin nodeEndpoints entryIdx).get ⟨n, hid⟩,
                    hbound⟩ =
                (Sig.nodePortsExcept node entry).get ⟨n, hlabel⟩ := by
        intro n hid hlabel
        have hlabel' :
            n < (eraseFin (Sig.nodePorts node) portEntry).length := by
          simpa [Signature.nodePortsExcept, portEntry] using hlabel
        have haligned :=
          eraseFin_pointwise_relation
            (R := fun id label =>
              ∃ hbound : id <
                  (st.endpoints ++ Sig.nodePorts node).length,
                (st.endpoints ++ Sig.nodePorts node).get
                    ⟨id, hbound⟩ = label)
            (by simp [nodeEndpoints, Signature.nodePorts])
            nodeEndpoints_labels entryIdx portEntry
            (by simp [entryIdx, portEntry])
            n hid hlabel'
        rcases haligned with ⟨hbound, hlabelEq⟩
        refine ⟨hbound, ?_⟩
        simpa [Signature.nodePortsExcept, portEntry] using hlabelEq
      have haligned :=
        append_pointwise_relation
          (R := fun id label =>
            ∃ hbound : id < (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                ⟨id, hbound⟩ = label)
          hrest
          (by
            simp [Signature.nodePortsExcept, nodeEndpoints,
              Signature.nodePorts, eraseFin_length])
          hleft hright n hid hfrontier
      rcases haligned with ⟨hbound, hlabelEq⟩
      simpa using hlabelEq
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_left_bound edge hold
        exact old_bound_lift hbound
      · cases hnew
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        exact old_bound_lift hbound
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_right_bound edge hold
        exact old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints entryIdx
        exact fresh_bound_of_mem hmem
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_left_label edge hold
        have hbound := hv.edge_left_bound edge hold
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨edge.left, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨edge.left, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = edge.leftLabel := hlabel
      · cases hnew
        have hlabel := hv.frontier_head_label hids
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨activeId, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨activeId, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = active := hlabel
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_right_label edge hold
        have hbound := hv.edge_right_bound edge hold
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨edge.right, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨edge.right, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = edge.rightLabel := hlabel
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node entryIdx
            (fresh_bound_of_mem (List.get_mem nodeEndpoints entryIdx))
        simpa [nodeEndpoints, entryIdx, Signature.nodePorts] using hlabel
    · intro renderNode hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.node_incident_length renderNode hold
      · cases hnew
        simp
    · intro renderNode hmem slot
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.node_incident_bound renderNode hold slot
        exact old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get slot ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints slot
        exact fresh_bound_of_mem hmem
    · intro renderNode hmem slot
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.node_incident_label renderNode hold slot
        have hbound := hv.node_incident_bound renderNode hold slot
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨renderNode.incident.get slot, old_bound_lift hbound⟩ =
              st.endpoints.get
                ⟨renderNode.incident.get slot, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ =
              Sig.port renderNode.label
                (Fin.cast (hv.node_incident_length renderNode hold) slot) :=
                hlabel
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node slot
            (fresh_bound_of_mem (List.get_mem nodeEndpoints slot))
        simpa [nodeEndpoints, Signature.nodePorts] using hlabel

theorem budStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (budStep node entry ok st).EndpointPartition := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    have oldFrontierNodup : (activeId :: restIds).Nodup := by
      simpa [hids] using hp.frontier_nodup
    have active_not_rest : activeId ∉ restIds := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.1
    have rest_nodup : restIds.Nodup := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.2
    have active_old_frontier : activeId ∈ st.frontierIds := by
      rw [hids]
      simp
    have active_old_bound : activeId < st.endpoints.length :=
      hv.frontier_bound activeId active_old_frontier
    have entry_mem_fresh : nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
      List.get_mem nodeEndpoints entryIdx
    have entry_fresh_ge : st.nextEndpoint ≤ nodeEndpoints.get entryIdx :=
      freshNodeEndpoints_mem_ge entry_mem_fresh
    have active_ne_entry : activeId ≠ nodeEndpoints.get entryIdx := by
      intro hsame
      have hnext := hv.nextEndpoint_eq
      omega
    dsimp
    let newEdge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := Sig.port node entry
        left := activeId
        right := nodeEndpoints.get entryIdx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    let child : RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++ [newEdge]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := restIds ++ eraseFin nodeEndpoints entryIdx
        frontierIds_length := by
          dsimp [nodeEndpoints, entryIdx]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            eraseFin_length] }
    change child.EndpointPartition
    have childConsumed_eq :
        child.edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, nodeEndpoints.get entryIdx] := by
      simp [child, newEdge, RenderState.edgeEndpointIds]
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < child.endpoints.length := by
      simp [child, Signature.nodePorts]
      omega
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      simp [child, Signature.nodePorts] at hlt ⊢
      omega
    have old_fresh_disjoint
        {id : Nat} (hold : id < st.endpoints.length)
        (hfresh : id ∈ nodeEndpoints) : False := by
      have hge := freshNodeEndpoints_mem_ge
        (by simpa [nodeEndpoints] using hfresh)
      have hnext := hv.nextEndpoint_eq
      omega
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · apply nodup_append_of_nodup_disjoint
      · exact rest_nodup
      · exact nodup_eraseFin nodeEndpoints entryIdx
          (freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node))
      · intro id hrestMem hfreshExcept
        have hold := hv.frontier_bound id (by
          rw [hids]
          right
          exact hrestMem)
        have hfresh : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hfreshExcept
        exact old_fresh_disjoint hold hfresh
    · have hnodup :
          (st.edgeEndpointIds ++ [activeId, nodeEndpoints.get entryIdx]).Nodup := by
        apply nodup_append_of_nodup_disjoint
        · exact hp.consumed_nodup
        · have hpair :
            ([activeId, nodeEndpoints.get entryIdx] : List Nat).Nodup := by
            simp
            exact active_ne_entry
          exact hpair
        · intro id hold hnew
          simp at hnew
          rcases hnew with hactive | hentry
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hactive] using active_old_frontier) hold
          · have holdBound := hp.consumed_bound id hold
            have hfresh : id ∈ nodeEndpoints := by
              simp [hentry]
            exact old_fresh_disjoint holdBound hfresh
      rw [childConsumed_eq]
      exact hnodup
    · intro id hmem
      rw [childConsumed_eq] at hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact old_bound_lift (hp.consumed_bound id hold)
      · rcases hnew with hactive | hentry
        · simpa [hactive] using old_bound_lift active_old_bound
        · have hfresh : id ∈ nodeEndpoints := by
            simp [hentry]
          exact fresh_bound_of_mem hfresh
    · intro id hfrontier hconsumed
      rw [childConsumed_eq] at hconsumed
      change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx at hfrontier
      simp at hfrontier
      simp at hconsumed
      rcases hfrontier with hrestMem | hfreshExcept
      · rcases hconsumed with holdConsumed | hnew
        · have oldFrontier : id ∈ st.frontierIds := by
            rw [hids]
            right
            exact hrestMem
          exact hp.frontier_consumed_disjoint id oldFrontier holdConsumed
        · rcases hnew with hactive | hentry
          · exact active_not_rest (by simpa [hactive] using hrestMem)
          · have hold := hv.frontier_bound id (by
              rw [hids]
              right
              exact hrestMem)
            have hfresh : id ∈ nodeEndpoints := by
              simp [hentry]
            exact old_fresh_disjoint hold hfresh
      · have hfresh : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hfreshExcept
        rcases hconsumed with holdConsumed | hnew
        · have holdBound := hp.consumed_bound id holdConsumed
          exact old_fresh_disjoint holdBound hfresh
        · rcases hnew with hactive | hentry
          · have hold := active_old_bound
            have hactiveEq : id = activeId := hactive
            exact old_fresh_disjoint (by simpa [hactiveEq]) hfresh
          · have hentryNotMem :
              nodeEndpoints.get entryIdx ∉ eraseFin nodeEndpoints entryIdx :=
              get_not_mem_eraseFin_of_nodup nodeEndpoints entryIdx
                (freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node))
            exact hentryNotMem (by simpa [hentry] using hfreshExcept)
    · intro id hid
      by_cases hold : id < st.endpoints.length
      · rcases hp.endpoint_covered id hold with holdFrontier | holdConsumed
        · rw [hids] at holdFrontier
          simp at holdFrontier
          rcases holdFrontier with hactive | hrestMem
          · right
            rw [childConsumed_eq]
            simp [hactive]
          · left
            change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx
            simp [hrestMem]
        · right
          rw [childConsumed_eq]
          simp [holdConsumed]
      · have hge : st.endpoints.length ≤ id := Nat.le_of_not_gt hold
        have hnext := hv.nextEndpoint_eq
        have hfresh : id ∈ nodeEndpoints := by
          apply freshNodeEndpoints_mem_of_bounds
          · omega
          · have hchildLen :
                child.endpoints.length =
                  st.endpoints.length + Sig.arity node := by
              simp [child, Signature.nodePorts]
            have hid' := hid
            rw [hchildLen] at hid'
            omega
        by_cases hentry : id = nodeEndpoints.get entryIdx
        · right
          rw [childConsumed_eq]
          simp [hentry]
        · left
          change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx
          simp
          right
          exact mem_eraseFin_of_mem_ne_get nodeEndpoints entryIdx hfresh hentry

theorem budStep_nodeIncidentNodup {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hn : st.NodeIncidentNodup) :
    (budStep node entry ok st).NodeIncidentNodup := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i _activeId _restIds _hids
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    constructor
    intro renderNode hmem
    simp at hmem
    rcases hmem with hold | hnew
    · exact hn.node_incident_nodup renderNode hold
    · cases hnew
      exact freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node)

theorem budStep_ownerIdPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds)
    {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (budStep node entry ok st).OwnerIdPartition boundary := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    let child : RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := Sig.port node entry
             left := activeId
             right := nodeEndpoints.get entryIdx
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := restIds ++ eraseFin nodeEndpoints entryIdx
        frontierIds_length := by
          dsimp [nodeEndpoints, entryIdx]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            eraseFin_length] }
    change child.OwnerIdPartition boundary
    have childOwners_eq :
        child.ownerEndpointIds boundary =
          st.ownerEndpointIds boundary ++ nodeEndpoints := by
      simp [child, RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
    have childEndpoints_len :
        child.endpoints.length = st.endpoints.length + Sig.arity node := by
      simp [child, Signature.nodePorts]
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < child.endpoints.length := by
      rw [childEndpoints_len]
      omega
    have fresh_bound {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      rw [childEndpoints_len]
      simp at hlt
      omega
    have old_fresh_disjoint {id : Nat}
        (hold : id ∈ st.ownerEndpointIds boundary)
        (hfresh : id ∈ nodeEndpoints) : False := by
      have holdBound := ho.owner_bound id hold
      have hge := freshNodeEndpoints_mem_ge
        (by simpa [nodeEndpoints] using hfresh)
      have hnext := hv.nextEndpoint_eq
      omega
    refine
      { owner_nodup := ?_
        owner_bound := ?_
        owner_covered := ?_ }
    · rw [childOwners_eq]
      apply nodup_append_of_nodup_disjoint
      · exact ho.owner_nodup
      · exact freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node)
      · intro id hold hfresh
        exact old_fresh_disjoint hold hfresh
    · intro id hmem
      rw [childOwners_eq] at hmem
      simp at hmem
      rcases hmem with hold | hfresh
      · exact old_bound_lift (ho.owner_bound id hold)
      · exact fresh_bound hfresh
    · intro id hid
      by_cases hold : id < st.endpoints.length
      · have holdOwner := ho.owner_covered id hold
        rw [childOwners_eq]
        exact List.mem_append_left nodeEndpoints holdOwner
      · have hge : st.endpoints.length ≤ id := Nat.le_of_not_gt hold
        have hfresh : id ∈ nodeEndpoints := by
          apply freshNodeEndpoints_mem_of_bounds
          · have hnext := hv.nextEndpoint_eq
            simp
            omega
          · have hid' := hid
            rw [childEndpoints_len] at hid'
            have hnext := hv.nextEndpoint_eq
            simp
            omega
        rw [childOwners_eq]
        exact List.mem_append_right (st.ownerEndpointIds boundary) hfresh

/--
Execute traversal syntax into a construction trace.

This is not yet the final semantic quotient bridge: it is the concrete
frontier-processing pass that the bridge uses to build a finished
`PortHypergraph`.
-/
def renderTrace :
    ∀ {frontier : List Sig.Port}, Diag Sig frontier → RenderState Sig frontier →
      RenderState Sig []
  | [], finish, st =>
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges
        nodes := st.nodes
        frontierIds := []
        frontierIds_length := rfl }
  | _active :: _frontier, connect mate ok child, st =>
      renderTrace child (connectStep mate ok st)
  | _active :: _frontier, bud node entry ok child, st =>
      renderTrace child (budStep node entry ok st)

theorem renderTrace_validIds :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.ValidIds → (renderTrace d st).ValidIds
  | [], finish, st, hv => by
      dsimp [renderTrace]
      refine
        { nextEndpoint_eq := hv.nextEndpoint_eq
          frontier_bound := ?_
          frontier_label := ?_
          edge_left_bound := hv.edge_left_bound
          edge_right_bound := hv.edge_right_bound
          edge_left_label := hv.edge_left_label
          edge_right_label := hv.edge_right_label
          node_incident_length := hv.node_incident_length
          node_incident_bound := hv.node_incident_bound
          node_incident_label := hv.node_incident_label }
      · intro id hmem
        cases hmem
      · intro n hid _hfrontier
        cases hid
  | _active :: _frontier, connect mate ok child, st, hv =>
      renderTrace_validIds child (connectStep mate ok st)
        (connectStep_validIds mate ok st hv)
  | _active :: _frontier, bud node entry ok child, st, hv =>
      renderTrace_validIds child (budStep node entry ok st)
        (budStep_validIds node entry ok st hv)

theorem renderTrace_endpointPartition :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.ValidIds → st.EndpointPartition →
        (renderTrace d st).EndpointPartition
  | [], finish, st, _hv, hp => by
      dsimp [renderTrace]
      refine
        { frontier_nodup := ?_
          consumed_nodup := ?_
          consumed_bound := ?_
          frontier_consumed_disjoint := ?_
          endpoint_covered := ?_ }
      · simp
      · simpa [RenderState.edgeEndpointIds] using hp.consumed_nodup
      · intro id hmem
        exact hp.consumed_bound id (by
          simpa [RenderState.edgeEndpointIds] using hmem)
      · intro id hfrontier _hconsumed
        cases hfrontier
      · intro id hid
        right
        simpa [RenderState.edgeEndpointIds] using
          (RenderState.EndpointPartition.endpoint_consumed_of_frontier_empty
            hp ⟨id, hid⟩)
  | _active :: _frontier, connect mate ok child, st, hv, hp =>
      renderTrace_endpointPartition child (connectStep mate ok st)
        (connectStep_validIds mate ok st hv)
        (connectStep_endpointPartition mate ok st hv hp)
  | _active :: _frontier, bud node entry ok child, st, hv, hp =>
      renderTrace_endpointPartition child (budStep node entry ok st)
        (budStep_validIds node entry ok st hv)
        (budStep_endpointPartition node entry ok st hv hp)

theorem renderTrace_nodeIncidentNodup :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.NodeIncidentNodup → (renderTrace d st).NodeIncidentNodup
  | [], finish, st, hn => by
      dsimp [renderTrace]
      constructor
      intro node hmem
      exact hn.node_incident_nodup node hmem
  | _active :: _frontier, connect mate ok child, st, hn =>
      renderTrace_nodeIncidentNodup child (connectStep mate ok st)
        (connectStep_nodeIncidentNodup mate ok st hn)
  | _active :: _frontier, bud node entry ok child, st, hn =>
      renderTrace_nodeIncidentNodup child (budStep node entry ok st)
        (budStep_nodeIncidentNodup node entry ok st hn)

theorem renderTrace_ownerIdPartition :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) (boundary : List Sig.Port),
      st.ValidIds → st.OwnerIdPartition boundary →
        (renderTrace d st).OwnerIdPartition boundary
  | [], finish, st, boundary, _hv, ho => by
      dsimp [renderTrace]
      refine
        { owner_nodup := ?_
          owner_bound := ?_
          owner_covered := ?_ }
      · simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using ho.owner_nodup
      · intro id hmem
        exact ho.owner_bound id (by
          simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
            using hmem)
      · intro id hid
        simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using ho.owner_covered id hid
  | _active :: _frontier, connect mate ok child, st, boundary, hv, ho =>
      renderTrace_ownerIdPartition child (connectStep mate ok st) boundary
        (connectStep_validIds mate ok st hv)
        (connectStep_ownerIdPartition mate ok st ho)
  | _active :: _frontier, bud node entry ok child, st, boundary, hv, ho =>
      renderTrace_ownerIdPartition child (budStep node entry ok st) boundary
        (budStep_validIds node entry ok st hv)
        (budStep_ownerIdPartition node entry ok st hv ho)

theorem renderTrace_reachability :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {boundary : List Sig.Port},
      st.Reachability boundary → (renderTrace d st).Reachability boundary
  | [], finish, st, _boundary, hr => by
      dsimp [renderTrace]
      refine
        { frontier_reaches := ?_
          node_reaches := ?_ }
      · intro id hmem
        cases hmem
      · intro node hmem
        rcases hr.node_reaches node hmem with ⟨slot, reach⟩
        refine ⟨slot, ?_⟩
        exact RenderState.RawReachesBoundary.mono
          (st := st)
          (st' :=
            { nextEndpoint := st.nextEndpoint
              endpoints := st.endpoints
              edges := st.edges
              nodes := st.nodes
              frontierIds := []
              frontierIds_length := rfl })
          (fun _edge hmem => hmem)
          (fun _node hmem => hmem)
          reach
  | _active :: _frontier, connect mate ok child, st, _boundary, hr =>
      renderTrace_reachability child (connectStep mate ok st)
        (connectStep_reachability mate ok st hr)
  | _active :: _frontier, bud node entry ok child, st, _boundary, hr =>
      renderTrace_reachability child (budStep node entry ok st)
        (budStep_reachability node entry ok st hr)

theorem renderTrace_connect
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier)) :
    renderTrace (Diag.connect mate ok child) st =
      renderTrace child (connectStep mate ok st) :=
  rfl

theorem renderTrace_bud
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    renderTrace (Diag.bud node entry ok child) st =
      renderTrace child (budStep node entry ok st) :=
  rfl

/-- Edges already present before rendering a syntax subtree remain present in
the completed render trace. -/
theorem renderTrace_edge_mem_old :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {edge : RenderEdge Sig},
      edge ∈ st.edges → edge ∈ (renderTrace d st).edges
  | [], finish, st, edge, hmem => by
      simpa [renderTrace] using hmem
  | _active :: _frontier, connect mate ok child, st, edge, hmem => by
      rw [renderTrace_connect]
      exact renderTrace_edge_mem_old child (connectStep mate ok st)
        (connectStep_edge_mem_old mate ok st hmem)
  | _active :: _frontier, bud node entry ok child, st, edge, hmem => by
      rw [renderTrace_bud]
      exact renderTrace_edge_mem_old child (budStep node entry ok st)
        (budStep_edge_mem_old node entry ok st hmem)

/-- Constructor nodes already present before rendering a syntax subtree remain
present in the completed render trace. -/
theorem renderTrace_node_mem_old :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {node : RenderNode Sig},
      node ∈ st.nodes → node ∈ (renderTrace d st).nodes
  | [], finish, st, node, hmem => by
      simpa [renderTrace] using hmem
  | _active :: _frontier, connect mate ok child, st, node, hmem => by
      rw [renderTrace_connect]
      exact renderTrace_node_mem_old child (connectStep mate ok st)
        (connectStep_node_mem_old mate ok st hmem)
  | _active :: _frontier, bud ctor entry ok child, st, node, hmem => by
      rw [renderTrace_bud]
      exact renderTrace_node_mem_old child (budStep ctor entry ok st)
        (budStep_node_mem_old ctor entry ok st hmem)

/-- The concrete edge introduced by a top-level `connect` remains present after
rendering the child diagram. -/
theorem renderTrace_connect_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := frontier.get mate
       left := activeId
       right :=
        restIds.get (Fin.cast (by
          have hlen := st.frontierIds_length
          rw [hids] at hlen
          exact (Nat.succ.inj hlen).symm) mate)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (renderTrace (Diag.connect mate ok child) st).edges := by
  rw [renderTrace_connect]
  exact renderTrace_edge_mem_old child (connectStep mate ok st)
    (connectStep_new_edge_mem mate ok st hids)

/-- The concrete edge introduced by a top-level `bud` remains present after
rendering the child diagram. -/
theorem renderTrace_bud_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := Sig.port node entry
       left := activeId
       right :=
        (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
          (Fin.cast (by simp [freshNodeEndpoints]) entry)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (renderTrace (Diag.bud node entry ok child) st).edges := by
  rw [renderTrace_bud]
  exact renderTrace_edge_mem_old child (budStep node entry ok st)
    (budStep_new_edge_mem node entry ok st hids)

/-- The concrete constructor node introduced by a top-level `bud` remains
present after rendering the child diagram. -/
theorem renderTrace_bud_node_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    ({ label := node
       incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } :
        RenderNode Sig) ∈
      (renderTrace (Diag.bud node entry ok child) st).nodes := by
  rw [renderTrace_bud]
  exact renderTrace_node_mem_old child (budStep node entry ok st)
    (budStep_new_node_mem node entry ok st)

theorem connectStep_edgesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderEdge Sig),
      (connectStep mate ok st).edges = st.edges ++ suffix := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

theorem budStep_edgesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderEdge Sig),
      (budStep node entry ok st).edges = st.edges ++ suffix := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

/--
Edges already in a render state remain an ordered prefix of the completed
render trace.  The recursive bridge uses this stronger prefix fact, not just
membership, to identify processed edge indices after a render prefix.
-/
theorem renderTrace_edgesPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      ∃ suffix : List (RenderEdge Sig),
        (renderTrace d st).edges = st.edges ++ suffix
  | [], finish, st => by
      refine ⟨[], ?_⟩
      simp [renderTrace]
  | _active :: _frontier, connect mate ok child, st => by
      rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      rcases connectStep_edgesPrefix mate ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_connect, hsuffix, hstep, List.append_assoc]
  | _active :: _frontier, bud node entry ok child, st => by
      rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      rcases budStep_edgesPrefix node entry ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_bud, hsuffix, hstep, List.append_assoc]

/--
The edge introduced by a top-level rendered `connect` is at the first edge
index after the render prefix.  This deterministic index fact is needed to
relate renderer prefixes to traversal `processedEdges`.
-/
theorem renderTrace_connect_new_edge_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.connect mate ok child) st
    let mateId :=
      restIds.get (Fin.cast (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        exact (Nat.succ.inj hlen).symm) mate)
    let edge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right := mateId
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    final.edges.get ⟨st.edges.length, by
      dsimp [final]
      rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (connectStep mate ok st).edges = st.edges ++ [edge] := by
        unfold connectStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · rename_i activeId' restIds' hids'
          rw [hids] at hids'
          injection hids' with hactive hrest
          subst activeId'
          subst restIds'
          simp [edge, mateId]
      rw [renderTrace_connect, hsuffix, hstep]
      simp⟩ = edge := by
  intro final mateId edge
  rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (connectStep mate ok st).edges = st.edges ++ [edge] := by
    unfold connectStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · rename_i activeId' restIds' hids'
      rw [hids] at hids'
      injection hids' with hactive hrest
      subst activeId'
      subst restIds'
      simp [edge, mateId]
  have hfinal :
      final.edges = st.edges ++ edge :: suffix := by
    dsimp [final]
    rw [renderTrace_connect, hsuffix, hstep]
    simp
  have hbound : st.edges.length < final.edges.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.edges.length, by
        dsimp [final]
        rw [renderTrace_connect, hsuffix, hstep]
        simp⟩ : Fin final.edges.length) =
      ⟨st.edges.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.edges[st.edges.length]? = some edge := by
    rw [hfinal]
    simp
  have hsome :
      final.edges[st.edges.length]? =
        some (final.edges.get ⟨st.edges.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

/--
The edge introduced by a top-level rendered `bud` is at the first edge index
after the render prefix.  This is the bud analogue of
`renderTrace_connect_new_edge_get`.
-/
theorem renderTrace_bud_new_edge_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    let edge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := Sig.port node entry
        left := activeId
        right := nodeEndpoints.get entryIdx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    final.edges.get ⟨st.edges.length, by
      dsimp [final]
      rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (budStep node entry ok st).edges = st.edges ++ [edge] := by
        unfold budStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · rename_i activeId' restIds' hids'
          rw [hids] at hids'
          injection hids' with hactive hrest
          subst activeId'
          subst restIds'
          simp [edge, nodeEndpoints, entryIdx]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩ = edge := by
  intro final nodeEndpoints entryIdx edge
  rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (budStep node entry ok st).edges = st.edges ++ [edge] := by
    unfold budStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · rename_i activeId' restIds' hids'
      rw [hids] at hids'
      injection hids' with hactive hrest
      subst activeId'
      subst restIds'
      simp [edge, nodeEndpoints, entryIdx]
  have hfinal :
      final.edges = st.edges ++ edge :: suffix := by
    dsimp [final]
    rw [renderTrace_bud, hsuffix, hstep]
    simp
  have hbound : st.edges.length < final.edges.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.edges.length, by
        dsimp [final]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ : Fin final.edges.length) =
      ⟨st.edges.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.edges[st.edges.length]? = some edge := by
    rw [hfinal]
    simp
  have hsome :
      final.edges[st.edges.length]? =
        some (final.edges.get ⟨st.edges.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

theorem connectStep_nodesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderNode Sig),
      (connectStep mate ok st).nodes = st.nodes ++ suffix := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[], by simp⟩

theorem budStep_nodesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderNode Sig),
      (budStep node entry ok st).nodes = st.nodes ++ suffix := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

/--
Constructor nodes already in a render state remain an ordered prefix of the
completed render trace.  The recursive bridge uses this to identify seen-node
indices after a render prefix.
-/
theorem renderTrace_nodesPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      ∃ suffix : List (RenderNode Sig),
        (renderTrace d st).nodes = st.nodes ++ suffix
  | [], finish, st => by
      refine ⟨[], ?_⟩
      simp [renderTrace]
  | _active :: _frontier, connect mate ok child, st => by
      rcases renderTrace_nodesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      rcases connectStep_nodesPrefix mate ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_connect, hsuffix, hstep, List.append_assoc]
  | _active :: _frontier, bud node entry ok child, st => by
      rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      rcases budStep_nodesPrefix node entry ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_bud, hsuffix, hstep, List.append_assoc]

/--
The constructor node introduced by a top-level rendered `bud` is at the first
node index after the render prefix.  This deterministic index fact is needed
to relate renderer prefixes to traversal `seenNodes`.
-/
theorem renderTrace_bud_new_node_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let renderNode : RenderNode Sig :=
      { label := node
        incident := nodeEndpoints }
    final.nodes.get ⟨st.nodes.length, by
      dsimp [final]
      rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (budStep node entry ok st).nodes = st.nodes ++ [renderNode] := by
        unfold budStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · simp [renderNode, nodeEndpoints]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩ = renderNode := by
  intro final nodeEndpoints renderNode
  rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (budStep node entry ok st).nodes = st.nodes ++ [renderNode] := by
    unfold budStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · simp [renderNode, nodeEndpoints]
  have hfinal :
      final.nodes = st.nodes ++ renderNode :: suffix := by
    dsimp [final]
    rw [renderTrace_bud, hsuffix, hstep]
    simp
  have hbound : st.nodes.length < final.nodes.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.nodes.length, by
        dsimp [final]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ : Fin final.nodes.length) =
      ⟨st.nodes.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.nodes[st.nodes.length]? = some renderNode := by
    rw [hfinal]
    simp
  have hsome :
      final.nodes[st.nodes.length]? =
        some (final.nodes.get ⟨st.nodes.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

theorem connectStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).edges.length = st.edges.length + 1 := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem connectStep_nodes
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).nodes = st.nodes := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem connectStep_endpoints
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).endpoints = st.endpoints := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem budStep_endpoints
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).endpoints =
      st.endpoints ++ Sig.nodePorts node := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem budStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).edges.length = st.edges.length + 1 := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem budStep_nodes_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).nodes.length = st.nodes.length + 1 := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem budStep_endpoints_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).endpoints.length =
      st.endpoints.length + Sig.arity node := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [Signature.nodePorts]

def renderTrace_endpointPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      RenderState.EndpointPrefix (renderTrace d st) st.endpoints
  | [], finish, st =>
      { suffix := []
        endpoints_eq := by
          simp [renderTrace] }
  | _active :: _frontier, connect mate ok child, st =>
      let childPrefix :=
        renderTrace_endpointPrefix child (connectStep mate ok st)
      let suffix := childPrefix.suffix
      { suffix := suffix
        endpoints_eq := by
          rw [renderTrace_connect]
          have hchild :
              (renderTrace child (connectStep mate ok st)).endpoints =
                (connectStep mate ok st).endpoints ++ suffix := by
            simpa [suffix] using childPrefix.endpoints_eq
          calc
            (renderTrace child (connectStep mate ok st)).endpoints =
                (connectStep mate ok st).endpoints ++ suffix :=
              hchild
            _ = st.endpoints ++ suffix := by
              rw [connectStep_endpoints] }
  | _active :: _frontier, bud node entry ok child, st =>
      let childPrefix :=
        renderTrace_endpointPrefix child (budStep node entry ok st)
      let suffix := childPrefix.suffix
      { suffix := Sig.nodePorts node ++ suffix
        endpoints_eq := by
          rw [renderTrace_bud]
          have hchild :
              (renderTrace child (budStep node entry ok st)).endpoints =
                (budStep node entry ok st).endpoints ++ suffix := by
            simpa [suffix] using childPrefix.endpoints_eq
          calc
            (renderTrace child (budStep node entry ok st)).endpoints =
                (budStep node entry ok st).endpoints ++ suffix :=
              hchild
            _ =
                (st.endpoints ++ Sig.nodePorts node) ++ suffix := by
              rw [budStep_endpoints]
            _ =
                st.endpoints ++ (Sig.nodePorts node ++ suffix) := by
              rw [List.append_assoc] }

def renderTraceFromBoundary {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState Sig [] :=
  renderTrace d (RenderState.initial Sig boundary)

def renderTraceFromBoundary_endpointPrefix
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EndpointPrefix (renderTraceFromBoundary d) boundary :=
  let pref := renderTrace_endpointPrefix d (RenderState.initial Sig boundary)
  { suffix := pref.suffix
    endpoints_eq := by
      simpa [renderTraceFromBoundary, RenderState.initial] using
        pref.endpoints_eq }

theorem renderTraceFromBoundary_validIds
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).ValidIds :=
  renderTrace_validIds d (RenderState.initial Sig boundary)
    (RenderState.initial_validIds boundary)

theorem renderTraceFromBoundary_endpointPartition
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).EndpointPartition :=
  renderTrace_endpointPartition d (RenderState.initial Sig boundary)
    (RenderState.initial_validIds boundary)
    (RenderState.initial_endpointPartition boundary)

theorem renderTraceFromBoundary_nodeIncidentNodup
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).NodeIncidentNodup :=
  renderTrace_nodeIncidentNodup d (RenderState.initial Sig boundary)
    (RenderState.initial_nodeIncidentNodup boundary)

theorem renderTraceFromBoundary_ownerIdPartition
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).OwnerIdPartition boundary :=
  renderTrace_ownerIdPartition d (RenderState.initial Sig boundary) boundary
    (RenderState.initial_validIds boundary)
    (RenderState.initial_ownerIdPartition boundary)

theorem renderTraceFromBoundary_reachability
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).Reachability boundary :=
  renderTrace_reachability d (RenderState.initial Sig boundary)
    (RenderState.initial_reachability boundary)

def renderTraceFromBoundary_endpointEdgeEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EndpointEdgeEvidence (renderTraceFromBoundary d) :=
  RenderState.endpointEdgeEvidenceOfPartition
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)

def renderTraceFromBoundary_endpointEdge
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    Fin (renderTraceFromBoundary d).endpoints.length →
      Fin (renderTraceFromBoundary d).edges.length :=
  (renderTraceFromBoundary_endpointEdgeEvidence d).endpointEdge

theorem renderTraceFromBoundary_endpoint_edge_label
    {boundary : List Sig.Port} (d : Diag Sig boundary)
    (endpoint : Fin (renderTraceFromBoundary d).endpoints.length) :
    Sig.portEdge ((renderTraceFromBoundary d).endpoints.get endpoint) =
      ((renderTraceFromBoundary d).edges.get
        (renderTraceFromBoundary_endpointEdge d endpoint)).label :=
  (renderTraceFromBoundary_endpointEdgeEvidence d).endpoint_edge_label endpoint

def renderTraceFromBoundary_edgeEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EdgeEvidence (renderTraceFromBoundary d) :=
  RenderState.edgeEvidenceOfPartition
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)

def renderTraceFromBoundary_boundaryEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.BoundaryEvidence (renderTraceFromBoundary d) boundary :=
  RenderState.boundaryEvidenceOfPrefix
    (renderTraceFromBoundary_endpointPrefix d)

def renderTraceFromBoundary_incidenceEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.IncidenceEvidence (renderTraceFromBoundary d) :=
  RenderState.incidenceEvidenceOfValidIds
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_nodeIncidentNodup d)

theorem renderTraceFromBoundary_frontier_empty
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).frontierIds = [] := by
  have hlen := (renderTraceFromBoundary d).frontierIds_length
  cases hids : (renderTraceFromBoundary d).frontierIds with
  | nil => rfl
  | cons _head _tail =>
      rw [hids] at hlen
      simp at hlen

end Diag

end StringDiagram
end BijForm
