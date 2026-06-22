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

theorem frontierIds_cons_tail_length {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    restIds.length = frontier.length := by
  have hlen := st.frontierIds_length
  rw [hids] at hlen
  simpa using Nat.succ.inj hlen

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

structure EdgeEndpointBounds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  left :
    ∀ edge : Fin st.edges.length,
      (st.edges.get edge).left < st.endpoints.length
  right :
    ∀ edge : Fin st.edges.length,
      (st.edges.get edge).right < st.endpoints.length

def ValidIds.edgeEndpointBounds {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} (hv : st.ValidIds) :
    st.EdgeEndpointBounds where
  left edge := hv.edge_left_bound (st.edges.get edge) (List.get_mem st.edges edge)
  right edge := hv.edge_right_bound (st.edges.get edge) (List.get_mem st.edges edge)

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
  boundaryPort := fun b => listPrefixIndex pref.endpoints_eq b
  boundary_injective := by
    intro left right h
    exact fin_eq_of_val_eq (congrArg (fun x : Fin st.endpoints.length => x.val) h)
  boundary_label := by
    intro b
    exact listPrefixIndex_get pref.endpoints_eq b

theorem boundaryEvidenceOfPrefix_boundaryPort_val {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary) (b : Fin boundary.length) :
    ((boundaryEvidenceOfPrefix pref).boundaryPort b).val = b.val :=
  listPrefixIndex_val pref.endpoints_eq b

theorem boundaryEvidenceOfPrefix_exists_of_boundary_id {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary)
    (endpoint : Fin st.endpoints.length)
    (hboundary : endpoint.val ∈ List.range boundary.length) :
    ∃ b : Fin boundary.length,
      (boundaryEvidenceOfPrefix pref).boundaryPort b = endpoint := by
  let b : Fin boundary.length := ⟨endpoint.val, List.mem_range.mp hboundary⟩
  refine ⟨b, ?_⟩
  exact fin_eq_of_val_eq (by
    simp [b, boundaryEvidenceOfPrefix_boundaryPort_val pref b])

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

def initial_endpointPrefix {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).EndpointPrefix boundary where
  suffix := []
  endpoints_eq := by
    simp [initial]

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
      exact fin_zero_elim edgeIndex
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
      exact fin_zero_elim edgeIndex
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

def edgeLeftEndpointOfValidIds
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds) (edgeIndex : Fin st.edges.length) :
    Fin st.endpoints.length :=
  ⟨(st.edges.get edgeIndex).left,
    hv.edge_left_bound (st.edges.get edgeIndex)
      (List.get_mem st.edges edgeIndex)⟩

def edgeRightEndpointOfValidIds
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds) (edgeIndex : Fin st.edges.length) :
    Fin st.endpoints.length :=
  ⟨(st.edges.get edgeIndex).right,
    hv.edge_right_bound (st.edges.get edgeIndex)
      (List.get_mem st.edges edgeIndex)⟩

theorem edgeLeftEndpointOfValidIds_get
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds) (edgeIndex : Fin st.edges.length) :
    st.endpoints.get (edgeLeftEndpointOfValidIds hv edgeIndex) =
      (st.edges.get edgeIndex).leftLabel := by
  simpa [edgeLeftEndpointOfValidIds] using
    hv.edge_left_label (st.edges.get edgeIndex)
      (List.get_mem st.edges edgeIndex)

theorem edgeRightEndpointOfValidIds_get
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds) (edgeIndex : Fin st.edges.length) :
    st.endpoints.get (edgeRightEndpointOfValidIds hv edgeIndex) =
      (st.edges.get edgeIndex).rightLabel := by
  simpa [edgeRightEndpointOfValidIds] using
    hv.edge_right_label (st.edges.get edgeIndex)
      (List.get_mem st.edges edgeIndex)

theorem endpoint_eq_edgeLeftEndpointOfValidIds_of_val
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds)
    {endpoint : Fin st.endpoints.length}
    {edgeIndex : Fin st.edges.length}
    (h : endpoint.val = (st.edges.get edgeIndex).left) :
    endpoint = edgeLeftEndpointOfValidIds hv edgeIndex :=
  fin_eq_of_val_eq h

theorem endpoint_eq_edgeRightEndpointOfValidIds_of_val
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds)
    {endpoint : Fin st.endpoints.length}
    {edgeIndex : Fin st.edges.length}
    (h : endpoint.val = (st.edges.get edgeIndex).right) :
    endpoint = edgeRightEndpointOfValidIds hv edgeIndex :=
  fin_eq_of_val_eq h

theorem endpoint_get_eq_edgeLeftLabel_of_val
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds)
    {endpoint : Fin st.endpoints.length}
    {edgeIndex : Fin st.edges.length}
    (h : endpoint.val = (st.edges.get edgeIndex).left) :
    st.endpoints.get endpoint = (st.edges.get edgeIndex).leftLabel := by
  rw [endpoint_eq_edgeLeftEndpointOfValidIds_of_val hv h]
  exact edgeLeftEndpointOfValidIds_get hv edgeIndex

theorem endpoint_get_eq_edgeRightLabel_of_val
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier}
    (hv : st.ValidIds)
    {endpoint : Fin st.endpoints.length}
    {edgeIndex : Fin st.edges.length}
    (h : endpoint.val = (st.edges.get edgeIndex).right) :
    st.endpoints.get endpoint = (st.edges.get edgeIndex).rightLabel := by
  rw [endpoint_eq_edgeRightEndpointOfValidIds_of_val hv h]
  exact edgeRightEndpointOfValidIds_get hv edgeIndex

theorem endpointEdgeOfPartition_label
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    Sig.portEdge (st.endpoints.get endpoint) =
      (st.edges.get (endpointEdgeOfPartition hp endpoint)).label := by
  let edgeIndex := endpointEdgeOfPartition hp endpoint
  let edge := st.edges.get edgeIndex
  have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
    simpa [edgeIndex, edge] using
      endpointEdgeOfPartition_endpoint hp endpoint
  change Sig.portEdge (st.endpoints.get endpoint) = edge.label
  rcases hside with hleft | hright
  · rw [endpoint_get_eq_edgeLeftLabel_of_val hv
      (edgeIndex := edgeIndex) (by simpa [edge] using hleft)]
    exact edge.left_label
  · rw [endpoint_get_eq_edgeRightLabel_of_val hv
      (edgeIndex := edgeIndex) (by simpa [edge] using hright)]
    exact edge.right_label

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

theorem endpointEdgeOfPartition_edgeLeftEndpointOfValidIds
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        (edgeLeftEndpointOfValidIds hv edgeIndex) = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inl rfl

theorem endpointEdgeOfPartition_left
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).left,
          hv.edge_left_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  exact endpointEdgeOfPartition_edgeLeftEndpointOfValidIds hv hp edgeIndex

theorem endpointEdgeOfPartition_edgeRightEndpointOfValidIds
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        (edgeRightEndpointOfValidIds hv edgeIndex) = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inr rfl

theorem endpointEdgeOfPartition_right
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).right,
          hv.edge_right_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  exact endpointEdgeOfPartition_edgeRightEndpointOfValidIds hv hp edgeIndex

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
        exact fin_eq_of_val_eq (hleftL.trans hrightL.symm)
      exact False.elim (hne hfin)
    · rw [endpoint_get_eq_edgeLeftLabel_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hleftL)]
      rw [endpoint_get_eq_edgeRightLabel_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hrightR)]
      exact edge.compatible
  · rcases hrightSide with hrightL | hrightR
    · rw [endpoint_get_eq_edgeRightLabel_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hleftR)]
      rw [endpoint_get_eq_edgeLeftLabel_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hrightL)]
      exact Sig.compatible_symm edge.compatible
    · have hfin : left = right := by
        exact fin_eq_of_val_eq (hleftR.trans hrightR.symm)
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
  let leftEndpoint : Fin st.endpoints.length :=
    edgeLeftEndpointOfValidIds hv edgeIndex
  let rightEndpoint : Fin st.endpoints.length :=
    edgeRightEndpointOfValidIds hv edgeIndex
  refine ⟨leftEndpoint, rightEndpoint, ?_, ?_, ?_, ?_⟩
  · intro hsame
    have hval : edge.left = edge.right := by
      exact congrArg Fin.val hsame
    exact edge_left_ne_right_of_partition hp edgeIndex hval
  · exact endpointEdgeOfPartition_edgeLeftEndpointOfValidIds hv hp edgeIndex
  · exact endpointEdgeOfPartition_edgeRightEndpointOfValidIds hv hp edgeIndex
  · intro endpoint hendpointEdge
    have hsideRaw := endpointEdgeOfPartition_endpoint hp endpoint
    have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
      simpa [edge, hendpointEdge] using hsideRaw
    rcases hside with hleft | hright
    · left
      exact endpoint_eq_edgeLeftEndpointOfValidIds_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hleft)
    · right
      exact endpoint_eq_edgeRightEndpointOfValidIds_of_val hv
        (edgeIndex := edgeIndex) (by simpa [edge] using hright)

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
  exact fin_eq_of_val_eq (by
    simpa [incidentOfValidIds, slot] using hrawSlot)

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
  have hval := congrArg Fin.val horig
  exact fin_eq_of_val_eq (by
    simpa using hval)

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
      exact fin_zero_elim leftNode
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
                      have hval := congrArg (fun idx : Fin tail.length => idx.val)
                        hnodeTail
                      exact fin_eq_of_val_eq (congrArg Nat.succ hval)

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

end StringDiagram
end BijForm
