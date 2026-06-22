import BijForm.StringDiagram.Renderer

namespace BijForm
namespace StringDiagram

open DepPoly

/-!
## Semantic port-hypergraph representatives

The syntax layer uses a frontier of endpoint labels.  The semantic
representative separates those endpoint records from the edges/wires that
connect them: endpoints carry `Sig.Port`, edges carry `Sig.Edge`, and every
endpoint is incident to exactly one edge.  Every endpoint also has exactly one
semantic owner: either one ordered boundary position or one ordered
constructor port.
-/

/-- The unique semantic role played by a graph endpoint. -/
inductive EndpointOwner (boundaryLength nodeCount : Nat)
    (incidentLength : Fin nodeCount → Nat) where
  | boundary : Fin boundaryLength → EndpointOwner boundaryLength nodeCount incidentLength
  | constructor :
      (node : Fin nodeCount) →
      Fin (incidentLength node) →
      EndpointOwner boundaryLength nodeCount incidentLength

/--
A finite typed port-hypergraph representative with an ordered external
boundary.  Endpoints carry endpoint labels, edges carry wire labels, nodes
carry constructor labels, and every constructor incidence points to an ordered
constructor port.  The `endpoint_owner` field is the global monogamy condition
for endpoint ownership: local injectivity is not enough, so each endpoint must
have exactly one boundary-or-constructor owner.
-/
structure PortHypergraph (Sig : Signature) (boundary : List Sig.Port) where
  endpointCount : Nat
  edgeCount : Nat
  nodeCount : Nat
  endpointLabel : Fin endpointCount → Sig.Port
  edgeLabel : Fin edgeCount → Sig.Edge
  endpointEdge : Fin endpointCount → Fin edgeCount
  endpoint_edge_label :
    ∀ endpoint : Fin endpointCount,
      Sig.portEdge (endpointLabel endpoint) = edgeLabel (endpointEdge endpoint)
  edge_compatible :
    ∀ left right : Fin endpointCount,
      endpointEdge left = endpointEdge right →
        left ≠ right →
          Sig.compatible (endpointLabel left) (endpointLabel right)
  edge_two_endpoints :
    ∀ edge : Fin edgeCount,
      ∃ left right : Fin endpointCount,
        left ≠ right ∧
        endpointEdge left = edge ∧
        endpointEdge right = edge ∧
        ∀ endpoint : Fin endpointCount,
          endpointEdge endpoint = edge → endpoint = left ∨ endpoint = right
  boundaryPort : Fin boundary.length → Fin endpointCount
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length, endpointLabel (boundaryPort b) = boundary.get b
  nodeLabel : Fin nodeCount → Sig.Node
  incident : Fin nodeCount → List (Fin endpointCount)
  incident_length :
    ∀ node : Fin nodeCount, (incident node).length = Sig.arity (nodeLabel node)
  incident_injective :
    ∀ node : Fin nodeCount,
      Function.Injective fun slot : Fin (incident node).length =>
        (incident node).get slot
  incidence_label :
    ∀ (node : Fin nodeCount) (slot : Fin (incident node).length),
      endpointLabel ((incident node).get slot) =
        Sig.port (nodeLabel node) (Fin.cast (incident_length node) slot)
  endpoint_owner :
    ∀ endpoint : Fin endpointCount,
      ∃ owner : EndpointOwner boundary.length nodeCount
          (fun node => (incident node).length),
        (match owner with
          | .boundary boundaryIndex => boundaryPort boundaryIndex
          | .constructor node slot => (incident node).get slot) = endpoint ∧
        ∀ owner' : EndpointOwner boundary.length nodeCount
            (fun node => (incident node).length),
          (match owner' with
            | .boundary boundaryIndex => boundaryPort boundaryIndex
            | .constructor node slot => (incident node).get slot) = endpoint →
          owner' = owner

namespace PortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/-- Interpret an endpoint owner as the endpoint it owns in a concrete graph. -/
def endpointOwnerEndpoint (G : PortHypergraph Sig boundary) :
    EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length) →
      Fin G.endpointCount
  | .boundary boundaryIndex => G.boundaryPort boundaryIndex
  | .constructor node slot => (G.incident node).get slot

/-- The owners of a fixed endpoint.  Valid semantic representatives require
this subtype to have exactly one inhabitant for every endpoint. -/
def endpointOwnersOf (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) : Type :=
  { owner : EndpointOwner boundary.length G.nodeCount
      (fun node => (G.incident node).length) //
    endpointOwnerEndpoint G owner = endpoint }

/-- Every endpoint has exactly one boundary-or-constructor owner. -/
theorem endpointOwnersOf_existsUnique (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    ∃ owner : endpointOwnersOf G endpoint,
      ∀ owner' : endpointOwnersOf G endpoint, owner' = owner := by
  rcases G.endpoint_owner endpoint with ⟨owner, howner, huniq⟩
  have hownerEndpoint : endpointOwnerEndpoint G owner = endpoint := by
    cases owner <;> simpa [endpointOwnerEndpoint] using howner
  refine ⟨⟨owner, hownerEndpoint⟩, ?_⟩
  intro owner'
  rcases owner' with ⟨owner', howner'⟩
  apply Subtype.ext
  apply huniq
  revert howner'
  cases owner' <;> intro howner' <;> simpa [endpointOwnerEndpoint] using howner'

theorem endpointOwner_eq_of_endpoint (G : PortHypergraph Sig boundary)
    {endpoint : Fin G.endpointCount}
    {owner₁ owner₂ :
      EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length)}
    (howner₁ : endpointOwnerEndpoint G owner₁ = endpoint)
    (howner₂ : endpointOwnerEndpoint G owner₂ = endpoint) :
    owner₁ = owner₂ := by
  rcases G.endpoint_owner endpoint with ⟨owner, _howner, huniq⟩
  have hleft : owner₁ = owner := by
    apply huniq
    cases owner₁ <;> simpa [endpointOwnerEndpoint] using howner₁
  have hright : owner₂ = owner := by
    apply huniq
    cases owner₂ <;> simpa [endpointOwnerEndpoint] using howner₂
  exact hleft.trans hright.symm

/-- A mate of an endpoint is the other endpoint on the same edge. -/
def EdgeMate (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Prop :=
  endpoint ≠ mate ∧ G.endpointEdge endpoint = G.endpointEdge mate

theorem EdgeMate.symm {G : PortHypergraph Sig boundary}
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    EdgeMate G mate endpoint := by
  constructor
  · intro hsame
    exact hmate.1 hsame.symm
  · exact hmate.2.symm

/-- Type-level wrapper for executable edge-mate checks. -/
structure EdgeMateData (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Type where
  proof : EdgeMate G endpoint mate

/-- Check whether a concrete endpoint is the edge mate of another endpoint. -/
def edgeMateCandidate? (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) :
    Option (EdgeMateData G endpoint mate) :=
  if hsame : endpoint = mate then
    none
  else if hedge : G.endpointEdge endpoint = G.endpointEdge mate then
    some ⟨⟨hsame, hedge⟩⟩
  else
    none

theorem edgeMateCandidate?_isSome_of_edgeMate (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    (edgeMateCandidate? G endpoint mate).isSome := by
  simp [edgeMateCandidate?, hmate.1, hmate.2]

theorem edgeMateCandidate?_some_of_edgeMate (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    ∃ data : EdgeMateData G endpoint mate,
      edgeMateCandidate? G endpoint mate = some data := by
  cases hcase : edgeMateCandidate? G endpoint mate with
  | none =>
      have hsome := edgeMateCandidate?_isSome_of_edgeMate G hmate
      rw [hcase] at hsome
      simp at hsome
  | some data =>
      exact ⟨data, rfl⟩

/-- Search the finite endpoint set for the mate of a concrete endpoint. -/
def edgeMateSearch? (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    Option { mate : Fin G.endpointCount // EdgeMate G endpoint mate } :=
  (List.finRange G.endpointCount).findSome? fun mate =>
    match edgeMateCandidate? G endpoint mate with
    | some hmate => some ⟨mate, hmate.proof⟩
    | none => none

/-- Every endpoint has exactly one mate on its edge. -/
theorem edgeMate_existsUnique (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    ∃ mate : Fin G.endpointCount,
      EdgeMate G endpoint mate ∧
        ∀ mate' : Fin G.endpointCount, EdgeMate G endpoint mate' → mate' = mate := by
  rcases G.edge_two_endpoints (G.endpointEdge endpoint) with
    ⟨left, right, hdiff, hleft, hright, hall⟩
  have hendpoint : endpoint = left ∨ endpoint = right := hall endpoint rfl
  rcases hendpoint with hendpoint | hendpoint
  · refine ⟨right, ?_, ?_⟩
    · constructor
      · intro hsame
        exact hdiff (hendpoint.symm.trans hsame)
      · calc
          G.endpointEdge endpoint = G.endpointEdge left := by rw [hendpoint]
          _ = G.endpointEdge right := hleft.trans hright.symm
    · intro mate' hmate'
      rcases hall mate' hmate'.2.symm with hmateLeft | hmateRight
      · have hsame : endpoint = mate' := hendpoint.trans hmateLeft.symm
        exact False.elim (hmate'.1 hsame)
      · exact hmateRight
  · refine ⟨left, ?_, ?_⟩
    · constructor
      · intro hsame
        exact hdiff (hsame.symm.trans hendpoint)
      · calc
          G.endpointEdge endpoint = G.endpointEdge right := by rw [hendpoint]
          _ = G.endpointEdge left := hright.trans hleft.symm
    · intro mate' hmate'
      rcases hall mate' hmate'.2.symm with hmateLeft | hmateRight
      · exact hmateLeft
      · have hsame : endpoint = mate' := hendpoint.trans hmateRight.symm
        exact False.elim (hmate'.1 hsame)

theorem edgeMate_eq_of_same_endpoint (G : PortHypergraph Sig boundary)
    {endpoint mate₁ mate₂ : Fin G.endpointCount}
    (hmate₁ : EdgeMate G endpoint mate₁)
    (hmate₂ : EdgeMate G endpoint mate₂) :
    mate₁ = mate₂ := by
  rcases edgeMate_existsUnique G endpoint with
    ⟨mate, _hmate, huniq⟩
  exact (huniq mate₁ hmate₁).trans (huniq mate₂ hmate₂).symm

theorem edgeMate_compatible (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    Sig.compatible (G.endpointLabel endpoint) (G.endpointLabel mate) :=
  G.edge_compatible endpoint mate hmate.2 hmate.1

theorem incident_nodup (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).Nodup :=
  list_nodup_of_get_injective (G.incident node) (G.incident_injective node)

theorem incident_mem_node_eq (G : PortHypergraph Sig boundary)
    {leftNode rightNode : Fin G.nodeCount}
    {endpoint : Fin G.endpointCount}
    (hleft : endpoint ∈ G.incident leftNode)
    (hright : endpoint ∈ G.incident rightNode) :
    leftNode = rightNode := by
  rcases list_exists_get_of_mem (G.incident leftNode) hleft with
    ⟨leftSlot, hleftSlot⟩
  rcases list_exists_get_of_mem (G.incident rightNode) hright with
    ⟨rightSlot, hrightSlot⟩
  have hsame :
      (.constructor leftNode leftSlot :
        EndpointOwner boundary.length G.nodeCount
          (fun node => (G.incident node).length)) =
      .constructor rightNode rightSlot :=
    G.endpointOwner_eq_of_endpoint
      (owner₁ := .constructor leftNode leftSlot)
      (owner₂ := .constructor rightNode rightSlot)
      (by simpa [endpointOwnerEndpoint] using hleftSlot)
      (by simpa [endpointOwnerEndpoint] using hrightSlot)
  cases hsame
  rfl

theorem boundary_mem_not_incident_mem (G : PortHypergraph Sig boundary)
    {endpoint : Fin G.endpointCount}
    (hboundary : endpoint ∈ List.ofFn G.boundaryPort)
    {node : Fin G.nodeCount}
    (hincident : endpoint ∈ G.incident node) :
    False := by
  rcases (List.mem_ofFn.mp hboundary) with ⟨boundaryIndex, hboundaryEq⟩
  rcases list_exists_get_of_mem (G.incident node) hincident with
    ⟨slot, hslot⟩
  have hsame :
      (.boundary boundaryIndex :
        EndpointOwner boundary.length G.nodeCount
          (fun node => (G.incident node).length)) =
      .constructor node slot :=
    G.endpointOwner_eq_of_endpoint
      (owner₁ := .boundary boundaryIndex)
      (owner₂ := .constructor node slot)
      (by simpa [endpointOwnerEndpoint] using hboundaryEq)
      (by simpa [endpointOwnerEndpoint] using hslot)
  cases hsame

theorem incidentFlatMap_nodup_of_nodup (G : PortHypergraph Sig boundary) :
    ∀ (nodes : List (Fin G.nodeCount)),
      nodes.Nodup →
        (nodes.flatMap fun node => G.incident node).Nodup
  | [], _hnodup => by simp
  | node :: nodes, hnodup => by
      have hsplit : node ∉ nodes ∧ nodes.Nodup := by
        simpa using hnodup
      apply nodup_append_of_nodup_disjoint
      · exact G.incident_nodup node
      · exact G.incidentFlatMap_nodup_of_nodup nodes hsplit.2
      · intro endpoint hhead htail
        rw [← List.flatMap_def] at htail
        rw [List.mem_flatMap] at htail
        rcases htail with ⟨otherNode, hotherNode, hotherIncident⟩
        have hnodeEq :
            node = otherNode :=
          G.incident_mem_node_eq hhead hotherIncident
        exact hsplit.1 (by simpa [hnodeEq] using hotherNode)

theorem incident_labels (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).map G.endpointLabel =
      Sig.nodePorts (G.nodeLabel node) := by
  apply List.ext_getElem
  · simp [Signature.nodePorts, G.incident_length node]
  · intro i hleft hright
    rw [List.getElem_map]
    have hslot : i < (G.incident node).length := by
      simpa using hleft
    have hinc := G.incidence_label node ⟨i, hslot⟩
    simpa [Signature.nodePorts] using hinc

theorem incident_labels_except (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    (eraseFin (G.incident node) slot).map G.endpointLabel =
      Sig.nodePortsExcept (G.nodeLabel node)
        (Fin.cast (G.incident_length node) slot) := by
  calc
    (eraseFin (G.incident node) slot).map G.endpointLabel =
        eraseFin ((G.incident node).map G.endpointLabel)
          (Fin.cast (by simp) slot) :=
      map_eraseFin G.endpointLabel (G.incident node) slot
    _ = Sig.nodePortsExcept (G.nodeLabel node)
          (Fin.cast (G.incident_length node) slot) := by
      have hlabels := G.incident_labels node
      rw [eraseFin_eq_of_eq hlabels]
      simp [Signature.nodePortsExcept, Signature.nodePorts]

/--
A port endpoint has a path to the ordered boundary when it is a boundary
endpoint, can cross an edge to the other endpoint on that edge, or can move
across the ordered incidences of a constructor already in the same component.
-/
inductive PortReachesBoundary (G : PortHypergraph Sig boundary) :
    Fin G.endpointCount → Prop
  | boundary (b : Fin boundary.length) :
      PortReachesBoundary G (G.boundaryPort b)
  | throughEdge {p q : Fin G.endpointCount}
      (sameEdge : G.endpointEdge p = G.endpointEdge q)
      (different : p ≠ q)
      (reach : PortReachesBoundary G p) :
      PortReachesBoundary G q
  | throughConstructor {p q : Fin G.endpointCount}
      (node : Fin G.nodeCount)
      (fromSlot toSlot : Fin (G.incident node).length)
      (hp : (G.incident node).get fromSlot = p)
      (hq : (G.incident node).get toSlot = q)
      (reach : PortReachesBoundary G p) :
      PortReachesBoundary G q

theorem PortReachesBoundary.throughEdgeMate
    {G : PortHypergraph Sig boundary}
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate)
    (reach : PortReachesBoundary G endpoint) :
    PortReachesBoundary G mate :=
  PortReachesBoundary.throughEdge hmate.2 hmate.1 reach

/-- Every constructor is in some component connected to the external boundary. -/
def AllConstructorsReachBoundary (G : PortHypergraph Sig boundary) : Prop :=
  ∀ node : Fin G.nodeCount,
    ∃ slot : Fin (G.incident node).length,
      PortReachesBoundary G ((G.incident node).get slot)

end PortHypergraph

/--
The semantic representatives for final encoded diagrams: finite typed
port-hypergraphs with ordered external boundary and no constructor in a
component disconnected from that boundary.
-/
structure OpenPortHypergraph (Sig : Signature) (boundary : List Sig.Port) where
  raw : PortHypergraph Sig boundary
  allConstructorsReachBoundary :
    PortHypergraph.AllConstructorsReachBoundary raw

namespace RenderState

variable {Sig : Signature}

/--
Evidence that a completed render trace presents a semantic
`PortHypergraph`.  The trace lists are the storage; this structure supplies
the finite maps and proofs required by the semantic representative.
-/
structure PortHypergraphEvidence
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  edgeEvidence : EdgeEvidence st
  boundaryEvidence : BoundaryEvidence st boundary
  incidenceEvidence : IncidenceEvidence st
  endpoint_owner :
    ∀ endpoint : Fin st.endpoints.length,
      ∃ owner : EndpointOwner boundary.length st.nodes.length
          (fun node => (incidenceEvidence.incident node).length),
        (match owner with
          | .boundary boundaryIndex =>
              boundaryEvidence.boundaryPort boundaryIndex
          | .constructor node slot =>
              (incidenceEvidence.incident node).get slot) = endpoint ∧
        ∀ owner' : EndpointOwner boundary.length st.nodes.length
            (fun node => (incidenceEvidence.incident node).length),
          (match owner' with
            | .boundary boundaryIndex =>
                boundaryEvidence.boundaryPort boundaryIndex
            | .constructor node slot =>
                (incidenceEvidence.incident node).get slot) = endpoint →
          owner' = owner

def portHypergraphEvidenceOfInvariants
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary) :
    PortHypergraphEvidence st boundary where
  edgeEvidence := edgeEvidenceOfPartition hv hp
  boundaryEvidence := boundaryEvidenceOfPrefix pref
  incidenceEvidence := incidenceEvidenceOfValidIds hv hn
  endpoint_owner := by
    intro endpoint
    have hcovered :
        endpoint.val ∈ List.range boundary.length ∨
          endpoint.val ∈ st.nodeIncidentIds := by
      simpa [ownerEndpointIds] using ho.owner_covered endpoint.val endpoint.isLt
    rcases hcovered with hboundary | hnode
    · rcases boundaryEvidenceOfPrefix_exists_of_boundary_id pref endpoint
          hboundary with
        ⟨boundaryIndex, hboundaryOwner⟩
      refine ⟨.boundary boundaryIndex, by simpa using hboundaryOwner, ?_⟩
      intro owner' howner'
      cases owner' with
      | boundary boundaryIndex' =>
          have hownerBoundary' :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex' =
                endpoint := by
            simpa using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex' =
                (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex :=
            hownerBoundary'.trans hboundaryOwner.symm
          have hindex :
              boundaryIndex' = boundaryIndex :=
            (boundaryEvidenceOfPrefix pref).boundary_injective hsameEndpoint
          cases hindex
          rfl
      | constructor node slot =>
          have hownerConstructor' :
              (incidentOfValidIds hv node).get slot = endpoint := by
            simpa [incidenceEvidenceOfValidIds] using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                (incidentOfValidIds hv node).get slot :=
            hboundaryOwner.trans hownerConstructor'.symm
          exact False.elim
            (boundaryEvidenceOfPrefix_ne_incidentOfValidIds pref hv ho
              boundaryIndex node slot hsameEndpoint)
    · rcases incidentOfValidIds_exists_of_mem_nodeIncidentIds hv endpoint
          hnode with
        ⟨node, slot, hconstructorOwner⟩
      refine ⟨.constructor node slot, by
        simpa [incidenceEvidenceOfValidIds] using hconstructorOwner, ?_⟩
      intro owner' howner'
      cases owner' with
      | boundary boundaryIndex =>
          have hownerBoundary' :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                endpoint := by
            simpa using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                (incidentOfValidIds hv node).get slot :=
            hownerBoundary'.trans hconstructorOwner.symm
          exact False.elim
            (boundaryEvidenceOfPrefix_ne_incidentOfValidIds pref hv ho
              boundaryIndex node slot hsameEndpoint)
      | constructor node' slot' =>
          have hownerConstructor' :
              (incidentOfValidIds hv node').get slot' = endpoint := by
            simpa [incidenceEvidenceOfValidIds] using howner'
          have hsameEndpoint :
              (incidentOfValidIds hv node').get slot' =
                (incidentOfValidIds hv node).get slot :=
            hownerConstructor'.trans hconstructorOwner.symm
          have hnodeEq :
              node' = node :=
            incidentOfValidIds_eq_node_eq hv ho hsameEndpoint
          cases hnodeEq
          have hslotEq :
              slot' = slot :=
            incidentOfValidIds_injective hv hn node hsameEndpoint
          cases hslotEq
          rfl

namespace PortHypergraphEvidence

def toPortHypergraph {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : PortHypergraphEvidence st boundary) :
    PortHypergraph Sig boundary where
  endpointCount := st.endpoints.length
  edgeCount := st.edges.length
  nodeCount := st.nodes.length
  endpointLabel := st.endpoints.get
  edgeLabel := fun edge => (st.edges.get edge).label
  endpointEdge := ev.edgeEvidence.endpointEdgeEvidence.endpointEdge
  endpoint_edge_label := ev.edgeEvidence.endpointEdgeEvidence.endpoint_edge_label
  edge_compatible := ev.edgeEvidence.edge_compatible
  edge_two_endpoints := ev.edgeEvidence.edge_two_endpoints
  boundaryPort := ev.boundaryEvidence.boundaryPort
  boundary_injective := ev.boundaryEvidence.boundary_injective
  boundary_label := ev.boundaryEvidence.boundary_label
  nodeLabel := fun node => (st.nodes.get node).label
  incident := ev.incidenceEvidence.incident
  incident_length := ev.incidenceEvidence.incident_length
  incident_injective := ev.incidenceEvidence.incident_injective
  incidence_label := ev.incidenceEvidence.incidence_label
  endpoint_owner := by
    intro endpoint
    rcases ev.endpoint_owner endpoint with ⟨owner, howner, huniq⟩
    cases owner with
    | boundary boundaryIndex =>
        refine ⟨.boundary boundaryIndex, by simpa using howner, ?_⟩
        intro owner' howner'
        cases owner' with
        | boundary boundaryIndex' =>
            exact huniq (.boundary boundaryIndex') (by simpa using howner')
        | constructor node slot =>
            exact huniq (.constructor node slot) (by simpa using howner')
    | constructor node slot =>
        refine ⟨.constructor node slot, by simpa using howner, ?_⟩
        intro owner' howner'
        cases owner' with
        | boundary boundaryIndex =>
            exact huniq (.boundary boundaryIndex) (by simpa using howner')
        | constructor node' slot' =>
            exact huniq (.constructor node' slot') (by simpa using howner')

end PortHypergraphEvidence

theorem edgeMateOfInvariants_of_endpoint_sides
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (left right : Fin st.endpoints.length)
    (edgeIndex : Fin st.edges.length)
    (hleft : left.val = (st.edges.get edgeIndex).left)
    (hright : right.val = (st.edges.get edgeIndex).right) :
    PortHypergraph.EdgeMate
      (portHypergraphEvidenceOfInvariants hv hp hn pref ho).toPortHypergraph
      left right := by
  constructor
  · intro hsame
    have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) hsame
    have hne := edge_left_ne_right_of_partition hp edgeIndex
    exact hne (by
      calc
        (st.edges.get edgeIndex).left = left.val := hleft.symm
        _ = right.val := hval
        _ = (st.edges.get edgeIndex).right := hright)
  · have hleftEdge :=
      endpointEdgeOfPartition_eq_of_endpoint_side hp
        left edgeIndex (Or.inl hleft)
    have hrightEdge :=
      endpointEdgeOfPartition_eq_of_endpoint_side hp
        right edgeIndex (Or.inr hright)
    simpa [PortHypergraphEvidence.toPortHypergraph,
      portHypergraphEvidenceOfInvariants, edgeEvidenceOfPartition,
      endpointEdgeEvidenceOfPartition] using hleftEdge.trans hrightEdge.symm

theorem rawReachesBoundary_to_portReachesBoundaryOfInvariants
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    {id : Nat} (hbound : id < st.endpoints.length)
    (reach : st.RawReachesBoundary boundary.length id) :
    PortHypergraph.PortReachesBoundary
      (portHypergraphEvidenceOfInvariants hv hp hn pref ho).toPortHypergraph
      ⟨id, hbound⟩ := by
  let ev := portHypergraphEvidenceOfInvariants hv hp hn pref ho
  let G := ev.toPortHypergraph
  change PortHypergraph.PortReachesBoundary G ⟨id, hbound⟩
  induction reach with
  | boundary hboundary =>
      let boundaryIndex : Fin boundary.length :=
        ⟨_, List.mem_range.mp hboundary⟩
      have hendpoint :
          G.boundaryPort boundaryIndex = ⟨_, hbound⟩ := by
        exact fin_eq_of_val_eq rfl
      simpa [hendpoint] using
        (PortHypergraph.PortReachesBoundary.boundary
          (G := G) boundaryIndex)
  | throughEdgeLeft edge hmem _reach ih =>
      rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeEq⟩
      subst edge
      have hedgeMem : st.edges.get edgeIndex ∈ st.edges :=
        List.get_mem st.edges edgeIndex
      have hleftBound :=
        hv.edge_left_bound (st.edges.get edgeIndex) hedgeMem
      have hrightBound :=
        hv.edge_right_bound (st.edges.get edgeIndex) hedgeMem
      have hmate :
          PortHypergraph.EdgeMate G
            (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length)
            ⟨(st.edges.get edgeIndex).right, hrightBound⟩ := by
        simpa [G, ev] using
          edgeMateOfInvariants_of_endpoint_sides hv hp hn pref ho
            (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length)
            (⟨(st.edges.get edgeIndex).right, hrightBound⟩ :
              Fin st.endpoints.length)
            edgeIndex rfl rfl
      have hreachRight :
          PortHypergraph.PortReachesBoundary G
            ⟨(st.edges.get edgeIndex).right, hrightBound⟩ :=
        PortHypergraph.PortReachesBoundary.throughEdgeMate hmate (ih hleftBound)
      have htarget :
          (⟨(st.edges.get edgeIndex).right, hrightBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.edges.get edgeIndex).right, hbound⟩ := by
        exact fin_eq_of_val_eq rfl
      simpa [htarget] using hreachRight
  | throughEdgeRight edge hmem _reach ih =>
      rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeEq⟩
      subst edge
      have hedgeMem : st.edges.get edgeIndex ∈ st.edges :=
        List.get_mem st.edges edgeIndex
      have hleftBound :=
        hv.edge_left_bound (st.edges.get edgeIndex) hedgeMem
      have hrightBound :=
        hv.edge_right_bound (st.edges.get edgeIndex) hedgeMem
      have hmate :
          PortHypergraph.EdgeMate G
            (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length)
            ⟨(st.edges.get edgeIndex).right, hrightBound⟩ := by
        simpa [G, ev] using
          edgeMateOfInvariants_of_endpoint_sides hv hp hn pref ho
            (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length)
            (⟨(st.edges.get edgeIndex).right, hrightBound⟩ :
              Fin st.endpoints.length)
            edgeIndex rfl rfl
      have hreachLeft :
          PortHypergraph.PortReachesBoundary G
            ⟨(st.edges.get edgeIndex).left, hleftBound⟩ :=
        PortHypergraph.PortReachesBoundary.throughEdgeMate hmate.symm
          (ih hrightBound)
      have htarget :
          (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.edges.get edgeIndex).left, hbound⟩ := by
        exact fin_eq_of_val_eq rfl
      simpa [htarget] using hreachLeft
  | throughConstructor node hmem fromSlot toSlot _reach ih =>
      rcases list_exists_get_of_mem st.nodes hmem with ⟨nodeIndex, hnodeEq⟩
      subst node
      have hnodeMem : st.nodes.get nodeIndex ∈ st.nodes :=
        List.get_mem st.nodes nodeIndex
      let fromSlot' : Fin (incidentOfValidIds hv nodeIndex).length :=
        Fin.cast (by simp [incidentOfValidIds]) fromSlot
      let toSlot' : Fin (incidentOfValidIds hv nodeIndex).length :=
        Fin.cast (by simp [incidentOfValidIds]) toSlot
      have hfromBound :=
        hv.node_incident_bound (st.nodes.get nodeIndex) hnodeMem fromSlot
      have htoBound :=
        hv.node_incident_bound (st.nodes.get nodeIndex) hnodeMem toSlot
      have hfrom :
          (G.incident nodeIndex).get fromSlot' =
            (⟨(st.nodes.get nodeIndex).incident.get fromSlot, hfromBound⟩ :
              Fin st.endpoints.length) := by
        exact fin_eq_of_val_eq (by
          simp [G, ev, PortHypergraphEvidence.toPortHypergraph,
            portHypergraphEvidenceOfInvariants, incidenceEvidenceOfValidIds,
            incidentOfValidIds, fromSlot'])
      have hto :
          (G.incident nodeIndex).get toSlot' =
            (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) := by
        exact fin_eq_of_val_eq (by
          simp [G, ev, PortHypergraphEvidence.toPortHypergraph,
            portHypergraphEvidenceOfInvariants, incidenceEvidenceOfValidIds,
            incidentOfValidIds, toSlot'])
      have hreachTo :
          PortHypergraph.PortReachesBoundary G
            (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) :=
        PortHypergraph.PortReachesBoundary.throughConstructor
          nodeIndex fromSlot' toSlot' hfrom hto (ih hfromBound)
      have htarget :
          (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.nodes.get nodeIndex).incident.get toSlot, hbound⟩ := by
        exact fin_eq_of_val_eq rfl
      simpa [htarget] using hreachTo

/-- Evidence that a completed render trace presents an open semantic graph. -/
structure OpenPortHypergraphEvidence
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  graph : PortHypergraphEvidence st boundary
  allConstructorsReachBoundary :
    PortHypergraph.AllConstructorsReachBoundary graph.toPortHypergraph

def openEvidenceOfInvariants
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (hall :
      PortHypergraph.AllConstructorsReachBoundary
        (portHypergraphEvidenceOfInvariants hv hp hn pref ho).toPortHypergraph) :
    OpenPortHypergraphEvidence st boundary where
  graph := portHypergraphEvidenceOfInvariants hv hp hn pref ho
  allConstructorsReachBoundary := hall

namespace OpenPortHypergraphEvidence

def toOpenPortHypergraph {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : OpenPortHypergraphEvidence st boundary) :
    OpenPortHypergraph Sig boundary where
  raw := ev.graph.toPortHypergraph
  allConstructorsReachBoundary := ev.allConstructorsReachBoundary

end OpenPortHypergraphEvidence

end RenderState

namespace Diag

variable {Sig : Signature}

def renderTrace_endpointPrefixOfPrefix
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (pref : st.EndpointPrefix boundary) :
    (renderTrace d st).EndpointPrefix boundary :=
  pref.trans (renderTrace_endpointPrefix d st)

def renderTrace_graphEvidence
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary) :
    RenderState.PortHypergraphEvidence (renderTrace d st) boundary :=
  RenderState.portHypergraphEvidenceOfInvariants
    (renderTrace_validIds d st hv)
    (renderTrace_endpointPartition d st hv hp)
    (renderTrace_nodeIncidentNodup d st hn)
    (renderTrace_endpointPrefixOfPrefix d st pref)
    (renderTrace_ownerIdPartition d st boundary hv ho)

def renderTraceFromBoundary_graphEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.PortHypergraphEvidence (renderTraceFromBoundary d) boundary :=
  RenderState.portHypergraphEvidenceOfInvariants
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)
    (renderTraceFromBoundary_nodeIncidentNodup d)
    (renderTraceFromBoundary_endpointPrefix d)
    (renderTraceFromBoundary_ownerIdPartition d)

theorem renderTrace_allConstructorsReachBoundary
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (hr : st.Reachability boundary) :
    PortHypergraph.AllConstructorsReachBoundary
      (renderTrace_graphEvidence d st hv hp hn pref ho).toPortHypergraph := by
  let final := renderTrace d st
  let finalHv : final.ValidIds := renderTrace_validIds d st hv
  let finalHp : final.EndpointPartition :=
    renderTrace_endpointPartition d st hv hp
  let finalHn : final.NodeIncidentNodup :=
    renderTrace_nodeIncidentNodup d st hn
  let finalPref : final.EndpointPrefix boundary :=
    renderTrace_endpointPrefixOfPrefix d st pref
  let finalHo : final.OwnerIdPartition boundary :=
    renderTrace_ownerIdPartition d st boundary hv ho
  let finalHr : final.Reachability boundary :=
    renderTrace_reachability d st hr
  let ev : RenderState.PortHypergraphEvidence final boundary :=
    RenderState.portHypergraphEvidenceOfInvariants
      finalHv finalHp finalHn finalPref finalHo
  let G := ev.toPortHypergraph
  change PortHypergraph.AllConstructorsReachBoundary G
  intro node
  have hnodeMem : final.nodes.get node ∈ final.nodes :=
    List.get_mem final.nodes node
  rcases finalHr.node_reaches (final.nodes.get node) hnodeMem with
    ⟨rawSlot, rawReach⟩
  let slot : Fin (G.incident node).length :=
    Fin.cast
      (by
        simp [G, ev, RenderState.PortHypergraphEvidence.toPortHypergraph,
          RenderState.portHypergraphEvidenceOfInvariants,
          RenderState.incidenceEvidenceOfValidIds,
          RenderState.incidentOfValidIds])
      rawSlot
  refine ⟨slot, ?_⟩
  have hrawBound :
      (final.nodes.get node).incident.get rawSlot < final.endpoints.length :=
    finalHv.node_incident_bound (final.nodes.get node) hnodeMem rawSlot
  have hrawReach :
      PortHypergraph.PortReachesBoundary G
        (⟨(final.nodes.get node).incident.get rawSlot, hrawBound⟩ :
          Fin final.endpoints.length) :=
    RenderState.rawReachesBoundary_to_portReachesBoundaryOfInvariants
      finalHv finalHp finalHn finalPref finalHo hrawBound rawReach
  have hendpoint :
      (G.incident node).get slot =
        (⟨(final.nodes.get node).incident.get rawSlot, hrawBound⟩ :
          Fin final.endpoints.length) := by
    exact fin_eq_of_val_eq (by
      simp [G, ev, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.incidenceEvidenceOfValidIds,
        RenderState.incidentOfValidIds, slot])
  exact hendpoint.symm ▸ hrawReach

theorem renderTraceFromBoundary_allConstructorsReachBoundary
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    PortHypergraph.AllConstructorsReachBoundary
      (renderTraceFromBoundary_graphEvidence d).toPortHypergraph := by
  simpa [renderTraceFromBoundary_graphEvidence, renderTraceFromBoundary,
    renderTrace_graphEvidence, renderTrace_endpointPrefixOfPrefix,
    RenderState.EndpointPrefix.trans] using
    renderTrace_allConstructorsReachBoundary d
      (RenderState.initial Sig boundary)
      (RenderState.initial_validIds boundary)
      (RenderState.initial_endpointPartition boundary)
      (RenderState.initial_nodeIncidentNodup boundary)
      (RenderState.initial_endpointPrefix boundary)
      (RenderState.initial_ownerIdPartition boundary)
      (RenderState.initial_reachability boundary)

def renderTrace_openEvidence
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (hr : st.Reachability boundary) :
    RenderState.OpenPortHypergraphEvidence (renderTrace d st) boundary where
  graph := renderTrace_graphEvidence d st hv hp hn pref ho
  allConstructorsReachBoundary :=
    renderTrace_allConstructorsReachBoundary d st hv hp hn pref ho hr

/--
Renderer validity: the trace produced from traversal syntax carries exactly
the endpoint, edge, boundary, ordered-constructor incidence, endpoint-owner, and
boundary-reachability evidence required to be an open `PortHypergraph`.
-/
def renderTraceFromBoundary_openEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.OpenPortHypergraphEvidence
      (renderTraceFromBoundary d) boundary where
  graph := renderTraceFromBoundary_graphEvidence d
  allConstructorsReachBoundary :=
    renderTraceFromBoundary_allConstructorsReachBoundary d

/-- Semantic renderer obtained from `renderTraceFromBoundary_openEvidence`. -/
def toOpenPortHypergraph
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    OpenPortHypergraph Sig boundary :=
  (renderTraceFromBoundary_openEvidence d).toOpenPortHypergraph

/--
Bridge support for the syntax round-trip: a rendered top-level `connect`
really makes the first ordered boundary endpoint an edge mate of the selected
later boundary endpoint in the semantic graph.
-/
theorem toOpenPortHypergraph_connect_boundary_edgeMate
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate)) :
    let d : Diag Sig (active :: frontier) := Diag.connect mate ok child
    let G := Diag.toOpenPortHypergraph d
    PortHypergraph.EdgeMate G.raw
      (G.raw.boundaryPort ⟨0, by simp⟩)
      (G.raw.boundaryPort ⟨mate.val + 1, by
        simp⟩) := by
  intro d G
  let st := renderTraceFromBoundary d
  let hp : st.EndpointPartition := renderTraceFromBoundary_endpointPartition d
  let restIds : List Nat := List.map Nat.succ (List.range frontier.length)
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := 0
      right :=
        restIds.get (Fin.cast (by
          have hids :
              (RenderState.initial Sig (active :: frontier)).frontierIds =
                0 :: restIds := by
            simp [RenderState.initial, restIds]
            exact List.range_succ_eq_map
          exact (RenderState.frontierIds_cons_tail_length
            (RenderState.initial Sig (active :: frontier)) hids).symm) mate)
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hmem : edge ∈ st.edges := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, edge] using
      renderTrace_connect_edge_mem mate ok child
        (RenderState.initial Sig (active :: frontier))
        (activeId := 0) (restIds := restIds)
        (by
          simp [RenderState.initial, restIds]
          exact List.range_succ_eq_map)
  rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeIndex⟩
  have hactiveVal :
      (G.raw.boundaryPort ⟨0, by simp⟩).val =
        (st.edges.get edgeIndex).left := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.boundaryEvidenceOfPrefix, edge] at *
    rw [hedgeIndex]
    simpa [edge] using
      RenderState.boundaryEvidenceOfPrefix_boundaryPort_val
        (renderTraceFromBoundary_endpointPrefix d) ⟨0, by simp⟩
  have hmateVal :
      (G.raw.boundaryPort ⟨mate.val + 1, by
        simp⟩).val =
        (st.edges.get edgeIndex).right := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.boundaryEvidenceOfPrefix, edge] at *
    rw [hedgeIndex]
    have hboundaryVal :
        (listPrefixIndex (renderTraceFromBoundary_endpointPrefix d).endpoints_eq
            ⟨mate.val + 1, by simp⟩).val = mate.val + 1 :=
      listPrefixIndex_val (renderTraceFromBoundary_endpointPrefix d).endpoints_eq
        ⟨mate.val + 1, by simp⟩
    rw [hboundaryVal]
    simp [restIds]
  simpa [G, Diag.toOpenPortHypergraph,
    RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
    renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence] using
    RenderState.edgeMateOfInvariants_of_endpoint_sides
      (renderTraceFromBoundary_validIds d) hp
      (renderTraceFromBoundary_nodeIncidentNodup d)
      (renderTraceFromBoundary_endpointPrefix d)
      (renderTraceFromBoundary_ownerIdPartition d)
      (G.raw.boundaryPort ⟨0, by simp⟩)
      (G.raw.boundaryPort ⟨mate.val + 1, by simp⟩)
      edgeIndex hactiveVal hmateVal

/--
Bridge support for the syntax round-trip: a rendered top-level `bud` creates a
semantic constructor with the original label and entry position, and the first
ordered boundary endpoint is edge-mated to that constructor entry endpoint.
-/
theorem toOpenPortHypergraph_bud_boundary_entry_edgeMate
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
    let d : Diag Sig (active :: frontier) := Diag.bud node entry ok child
    let G := Diag.toOpenPortHypergraph d
    ∃ (nodeIndex : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident nodeIndex).length),
      G.raw.nodeLabel nodeIndex = node ∧
        slot.val = entry.val ∧
        PortHypergraph.EdgeMate G.raw
          (G.raw.boundaryPort ⟨0, by simp⟩)
          ((G.raw.incident nodeIndex).get slot) := by
  intro d G
  let st := renderTraceFromBoundary d
  let hv : st.ValidIds := renderTraceFromBoundary_validIds d
  let hp : st.EndpointPartition := renderTraceFromBoundary_endpointPartition d
  let nodeEndpoints :=
    freshNodeEndpoints (RenderState.initial Sig (active :: frontier)).nextEndpoint
      (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    Fin.cast (by simp [nodeEndpoints]) entry
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := 0
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  have hedgeMem : edge ∈ st.edges := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, edge,
      nodeEndpoints, entryIdx] using
      renderTrace_bud_edge_mem node entry ok child
        (RenderState.initial Sig (active :: frontier))
        (activeId := 0)
        (restIds := List.map Nat.succ (List.range frontier.length))
        (by
          simp [RenderState.initial]
          exact List.range_succ_eq_map)
  have hnodeMem : renderNode ∈ st.nodes := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, renderNode,
      nodeEndpoints] using
      renderTrace_bud_node_mem node entry ok child
        (RenderState.initial Sig (active :: frontier))
  rcases list_exists_get_of_mem st.edges hedgeMem with ⟨edgeIndex, hedgeIndex⟩
  rcases list_exists_get_of_mem st.nodes hnodeMem with ⟨nodeIndex, hnodeIndex⟩
  have hnodeLabel : G.raw.nodeLabel nodeIndex = node := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants, renderNode,
      nodeEndpoints] at *
    rw [hnodeIndex]
  let slot : Fin (G.raw.incident nodeIndex).length :=
    Fin.cast (by
      calc
        Sig.arity node = Sig.arity (G.raw.nodeLabel nodeIndex) := by
          rw [hnodeLabel]
        _ = (G.raw.incident nodeIndex).length :=
          (G.raw.incident_length nodeIndex).symm) entry
  refine ⟨nodeIndex, slot, hnodeLabel, ?_, ?_⟩
  · simp [slot]
  · have hactiveVal :
        (G.raw.boundaryPort ⟨0, by simp⟩).val =
          (st.edges.get edgeIndex).left := by
      dsimp [G, Diag.toOpenPortHypergraph,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.boundaryEvidenceOfPrefix, edge] at *
      rw [hedgeIndex]
      simpa [edge] using
        RenderState.boundaryEvidenceOfPrefix_boundaryPort_val
          (renderTraceFromBoundary_endpointPrefix d) ⟨0, by simp⟩
    have hincidentVal :
        ((G.raw.incident nodeIndex).get slot).val =
          (st.edges.get edgeIndex).right := by
      have hincidentList :
          (st.nodes.get nodeIndex).incident = nodeEndpoints := by
        simpa [renderNode] using congrArg RenderNode.incident hnodeIndex
      have hedgeRight :
          (st.edges.get edgeIndex).right = nodeEndpoints.get entryIdx := by
        simpa [edge] using congrArg RenderEdge.right hedgeIndex
      have hentryGet :
          (st.nodes.get nodeIndex).incident.get
              (Fin.cast (by
                rw [hincidentList]
                simp [nodeEndpoints]) entry) =
            nodeEndpoints.get entryIdx := by
        exact list_get_of_eq_of_val_eq hincidentList
          (Fin.cast (by
            rw [hincidentList]
            simp [nodeEndpoints]) entry)
          entryIdx
          (by simp [entryIdx])
      dsimp [G, Diag.toOpenPortHypergraph,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.incidenceEvidenceOfValidIds,
        RenderState.incidentOfValidIds, edge, slot, renderNode,
        nodeEndpoints, entryIdx]
      simpa [entryIdx] using hentryGet.trans hedgeRight.symm
    simpa [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence] using
      RenderState.edgeMateOfInvariants_of_endpoint_sides
        hv hp
        (renderTraceFromBoundary_nodeIncidentNodup d)
        (renderTraceFromBoundary_endpointPrefix d)
        (renderTraceFromBoundary_ownerIdPartition d)
        (G.raw.boundaryPort ⟨0, by simp⟩)
        ((G.raw.incident nodeIndex).get slot)
        edgeIndex hactiveVal hincidentVal

end Diag

/--
Boundary-preserving isomorphism of typed finite representatives.

The equivalences rename only the finite identifiers used for endpoints, edges,
and nodes.  The semantic data carried by those identifiers is preserved: the
ordered boundary is fixed pointwise, endpoint/edge/node labels agree after
transport, endpoint-to-edge incidence commutes with the edge transport, and
each ordered constructor-port incidence list is transported pointwise.
-/
structure PortHypergraphIso {Sig : Signature} {boundary : List Sig.Port}
    (G H : PortHypergraph Sig boundary) where
  endpointEquiv : Fin G.endpointCount ≃ᵢ Fin H.endpointCount
  edgeEquiv : Fin G.edgeCount ≃ᵢ Fin H.edgeCount
  nodeEquiv : Fin G.nodeCount ≃ᵢ Fin H.nodeCount
  boundary_preserved :
    ∀ b : Fin boundary.length,
      endpointEquiv.toFun (G.boundaryPort b) = H.boundaryPort b
  endpoint_label_preserved :
    ∀ endpoint : Fin G.endpointCount,
      G.endpointLabel endpoint =
        H.endpointLabel (endpointEquiv.toFun endpoint)
  edge_label_preserved :
    ∀ edge : Fin G.edgeCount,
      G.edgeLabel edge = H.edgeLabel (edgeEquiv.toFun edge)
  endpoint_edge_preserved :
    ∀ endpoint : Fin G.endpointCount,
      H.endpointEdge (endpointEquiv.toFun endpoint) =
        edgeEquiv.toFun (G.endpointEdge endpoint)
  node_label_preserved :
    ∀ node : Fin G.nodeCount,
      G.nodeLabel node = H.nodeLabel (nodeEquiv.toFun node)
  incidence_preserved :
    ∀ node : Fin G.nodeCount,
      (G.incident node).map endpointEquiv.toFun =
        H.incident (nodeEquiv.toFun node)

namespace PortHypergraphIso

variable {Sig : Signature} {boundary : List Sig.Port}

theorem boundary_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (b : Fin boundary.length) :
    e.endpointEquiv.invFun (H.boundaryPort b) = G.boundaryPort b := by
  have h := congrArg e.endpointEquiv.invFun (e.boundary_preserved b)
  simpa using h.symm

theorem endpoint_label_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (endpoint : Fin H.endpointCount) :
    H.endpointLabel endpoint =
      G.endpointLabel (e.endpointEquiv.invFun endpoint) := by
  have h := e.endpoint_label_preserved (e.endpointEquiv.invFun endpoint)
  rw [e.endpointEquiv.right_inv endpoint] at h
  exact h.symm

theorem edge_label_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (edge : Fin H.edgeCount) :
    H.edgeLabel edge = G.edgeLabel (e.edgeEquiv.invFun edge) := by
  have h := e.edge_label_preserved (e.edgeEquiv.invFun edge)
  rw [e.edgeEquiv.right_inv edge] at h
  exact h.symm

theorem endpoint_edge_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (endpoint : Fin H.endpointCount) :
    G.endpointEdge (e.endpointEquiv.invFun endpoint) =
      e.edgeEquiv.invFun (H.endpointEdge endpoint) := by
  have h := e.endpoint_edge_preserved (e.endpointEquiv.invFun endpoint)
  rw [e.endpointEquiv.right_inv endpoint] at h
  have h' := congrArg e.edgeEquiv.invFun h
  simpa using h'.symm

theorem node_label_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount) :
    H.nodeLabel node = G.nodeLabel (e.nodeEquiv.invFun node) := by
  have h := e.node_label_preserved (e.nodeEquiv.invFun node)
  rw [e.nodeEquiv.right_inv node] at h
  exact h.symm

theorem incidence_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount) :
    (H.incident node).map e.endpointEquiv.invFun =
      G.incident (e.nodeEquiv.invFun node) := by
  have h := e.incidence_preserved (e.nodeEquiv.invFun node)
  rw [e.nodeEquiv.right_inv node] at h
  have hmap := congrArg (List.map e.endpointEquiv.invFun) h
  have hleft :
      List.map e.endpointEquiv.invFun
          (List.map e.endpointEquiv.toFun
            (G.incident (e.nodeEquiv.invFun node))) =
        G.incident (e.nodeEquiv.invFun node) := by
    induction G.incident (e.nodeEquiv.invFun node) with
    | nil => rfl
    | cons endpoint endpoints ih =>
        simp [e.endpointEquiv.left_inv endpoint, ih]
  exact hmap.symm.trans hleft

def ofPreserved {G H : PortHypergraph Sig boundary}
    (endpointEquiv : Fin G.endpointCount ≃ᵢ Fin H.endpointCount)
    (edgeEquiv : Fin G.edgeCount ≃ᵢ Fin H.edgeCount)
    (nodeEquiv : Fin G.nodeCount ≃ᵢ Fin H.nodeCount)
    (boundary_preserved :
      ∀ b : Fin boundary.length,
        endpointEquiv.toFun (G.boundaryPort b) = H.boundaryPort b)
    (endpoint_label_preserved :
      ∀ endpoint : Fin G.endpointCount,
        G.endpointLabel endpoint =
          H.endpointLabel (endpointEquiv.toFun endpoint))
    (edge_label_preserved :
      ∀ edge : Fin G.edgeCount,
        G.edgeLabel edge = H.edgeLabel (edgeEquiv.toFun edge))
    (endpoint_edge_preserved :
      ∀ endpoint : Fin G.endpointCount,
        H.endpointEdge (endpointEquiv.toFun endpoint) =
          edgeEquiv.toFun (G.endpointEdge endpoint))
    (node_label_preserved :
      ∀ node : Fin G.nodeCount,
        G.nodeLabel node = H.nodeLabel (nodeEquiv.toFun node))
    (incidence_preserved :
      ∀ node : Fin G.nodeCount,
        (G.incident node).map endpointEquiv.toFun =
          H.incident (nodeEquiv.toFun node)) :
    PortHypergraphIso G H where
  endpointEquiv := endpointEquiv
  edgeEquiv := edgeEquiv
  nodeEquiv := nodeEquiv
  boundary_preserved := boundary_preserved
  endpoint_label_preserved := endpoint_label_preserved
  edge_label_preserved := edge_label_preserved
  endpoint_edge_preserved := endpoint_edge_preserved
  node_label_preserved := node_label_preserved
  incidence_preserved := incidence_preserved

def refl (G : PortHypergraph Sig boundary) : PortHypergraphIso G G where
  endpointEquiv := Iso.refl (Fin G.endpointCount)
  edgeEquiv := Iso.refl (Fin G.edgeCount)
  nodeEquiv := Iso.refl (Fin G.nodeCount)
  boundary_preserved := by
    intro _
    rfl
  endpoint_label_preserved := by
    intro _
    rfl
  edge_label_preserved := by
    intro _
    rfl
  endpoint_edge_preserved := by
    intro _
    rfl
  node_label_preserved := by
    intro _
    rfl
  incidence_preserved := by
    intro _
    simp [Iso.refl]

def symm {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) : PortHypergraphIso H G where
  endpointEquiv := Iso.symm e.endpointEquiv
  edgeEquiv := Iso.symm e.edgeEquiv
  nodeEquiv := Iso.symm e.nodeEquiv
  boundary_preserved := e.boundary_reflected
  endpoint_label_preserved := e.endpoint_label_reflected
  edge_label_preserved := e.edge_label_reflected
  endpoint_edge_preserved := e.endpoint_edge_reflected
  node_label_preserved := e.node_label_reflected
  incidence_preserved := e.incidence_reflected

def trans {G H K : PortHypergraph Sig boundary}
    (e₁ : PortHypergraphIso G H) (e₂ : PortHypergraphIso H K) :
    PortHypergraphIso G K where
  endpointEquiv := Iso.trans e₁.endpointEquiv e₂.endpointEquiv
  edgeEquiv := Iso.trans e₁.edgeEquiv e₂.edgeEquiv
  nodeEquiv := Iso.trans e₁.nodeEquiv e₂.nodeEquiv
  boundary_preserved := by
    intro b
    simp [Iso.trans, Function.comp, e₁.boundary_preserved b,
      e₂.boundary_preserved b]
  endpoint_label_preserved := by
    intro endpoint
    calc
      G.endpointLabel endpoint =
          H.endpointLabel (e₁.endpointEquiv.toFun endpoint) :=
        e₁.endpoint_label_preserved endpoint
      _ =
          K.endpointLabel
            (e₂.endpointEquiv.toFun (e₁.endpointEquiv.toFun endpoint)) :=
        e₂.endpoint_label_preserved (e₁.endpointEquiv.toFun endpoint)
  edge_label_preserved := by
    intro edge
    calc
      G.edgeLabel edge = H.edgeLabel (e₁.edgeEquiv.toFun edge) :=
        e₁.edge_label_preserved edge
      _ = K.edgeLabel (e₂.edgeEquiv.toFun (e₁.edgeEquiv.toFun edge)) :=
        e₂.edge_label_preserved (e₁.edgeEquiv.toFun edge)
  endpoint_edge_preserved := by
    intro endpoint
    calc
      K.endpointEdge
          (e₂.endpointEquiv.toFun (e₁.endpointEquiv.toFun endpoint)) =
          e₂.edgeEquiv.toFun
            (H.endpointEdge (e₁.endpointEquiv.toFun endpoint)) :=
        e₂.endpoint_edge_preserved (e₁.endpointEquiv.toFun endpoint)
      _ =
          e₂.edgeEquiv.toFun
            (e₁.edgeEquiv.toFun (G.endpointEdge endpoint)) := by
        rw [e₁.endpoint_edge_preserved endpoint]
  node_label_preserved := by
    intro node
    calc
      G.nodeLabel node = H.nodeLabel (e₁.nodeEquiv.toFun node) :=
        e₁.node_label_preserved node
      _ = K.nodeLabel (e₂.nodeEquiv.toFun (e₁.nodeEquiv.toFun node)) :=
        e₂.node_label_preserved (e₁.nodeEquiv.toFun node)
  incidence_preserved := by
    intro node
    calc
      (G.incident node).map (Iso.trans e₁.endpointEquiv e₂.endpointEquiv).toFun =
          ((G.incident node).map e₁.endpointEquiv.toFun).map
            e₂.endpointEquiv.toFun := by
        simp [Iso.trans, List.map_map]
      _ = (H.incident (e₁.nodeEquiv.toFun node)).map
            e₂.endpointEquiv.toFun := by
        rw [e₁.incidence_preserved node]
      _ = K.incident (e₂.nodeEquiv.toFun (e₁.nodeEquiv.toFun node)) := by
        rw [e₂.incidence_preserved (e₁.nodeEquiv.toFun node)]

theorem edgeMate_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin G.endpointCount}
    (hmate : PortHypergraph.EdgeMate G endpoint mate) :
    PortHypergraph.EdgeMate H
      (e.endpointEquiv.toFun endpoint) (e.endpointEquiv.toFun mate) := by
  constructor
  · intro hsame
    have hpre :
        endpoint = mate := by
      have h := congrArg e.endpointEquiv.invFun hsame
      simpa using h
    exact hmate.1 hpre
  · rw [e.endpoint_edge_preserved endpoint,
      e.endpoint_edge_preserved mate, hmate.2]

theorem edgeMate_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin H.endpointCount}
    (hmate : PortHypergraph.EdgeMate H endpoint mate) :
    PortHypergraph.EdgeMate G
      (e.endpointEquiv.invFun endpoint) (e.endpointEquiv.invFun mate) :=
  edgeMate_preserved (symm e) hmate

def incidenceSlotPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    Fin (H.incident (e.nodeEquiv.toFun node)).length :=
  Fin.cast
    (by
      have hlen := congrArg List.length (e.incidence_preserved node)
      simpa using hlen)
    slot

def incidenceSlotReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    Fin (G.incident (e.nodeEquiv.invFun node)).length :=
  Fin.cast
    (by
      have hlen := congrArg List.length (e.incidence_reflected node)
      simpa using hlen)
    slot

theorem incidence_get_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    (H.incident (e.nodeEquiv.toFun node)).get
        (incidenceSlotPreserved e node slot) =
      e.endpointEquiv.toFun ((G.incident node).get slot) := by
  have hlist := congrArg (fun xs : List (Fin H.endpointCount) =>
      xs[slot.val]?) (e.incidence_preserved node)
  have hleftBound :
      slot.val < ((G.incident node).map e.endpointEquiv.toFun).length := by
    simp [slot.isLt]
  have hleftSome :
      ((G.incident node).map e.endpointEquiv.toFun)[slot.val]? =
        some (e.endpointEquiv.toFun ((G.incident node).get slot)) := by
    rw [List.getElem?_eq_getElem hleftBound]
    simp
  have hslotVal : (incidenceSlotPreserved e node slot).val = slot.val := rfl
  have hrightSome :
      (H.incident (e.nodeEquiv.toFun node))[slot.val]? =
        some ((H.incident (e.nodeEquiv.toFun node)).get
          (incidenceSlotPreserved e node slot)) := by
    rw [← hslotVal]
    exact List.getElem?_eq_getElem
      (incidenceSlotPreserved e node slot).isLt
  have hlist' :
      ((G.incident node).map e.endpointEquiv.toFun)[slot.val]? =
        (H.incident (e.nodeEquiv.toFun node))[slot.val]? := by
    simpa using hlist
  rw [hleftSome, hrightSome] at hlist'
  exact Option.some.inj hlist'.symm

theorem incidence_get_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    (G.incident (e.nodeEquiv.invFun node)).get
        (incidenceSlotReflected e node slot) =
      e.endpointEquiv.invFun ((H.incident node).get slot) := by
  have hlist := congrArg (fun xs : List (Fin G.endpointCount) =>
      xs[slot.val]?) (e.incidence_reflected node)
  have hleftBound :
      slot.val < ((H.incident node).map e.endpointEquiv.invFun).length := by
    simp [slot.isLt]
  have hleftSome :
      ((H.incident node).map e.endpointEquiv.invFun)[slot.val]? =
        some (e.endpointEquiv.invFun ((H.incident node).get slot)) := by
    rw [List.getElem?_eq_getElem hleftBound]
    simp
  have hslotVal : (incidenceSlotReflected e node slot).val = slot.val := rfl
  have hrightSome :
      (G.incident (e.nodeEquiv.invFun node))[slot.val]? =
        some ((G.incident (e.nodeEquiv.invFun node)).get
          (incidenceSlotReflected e node slot)) := by
    rw [← hslotVal]
    exact List.getElem?_eq_getElem
      (incidenceSlotReflected e node slot).isLt
  have hlist' :
      ((H.incident node).map e.endpointEquiv.invFun)[slot.val]? =
        (G.incident (e.nodeEquiv.invFun node))[slot.val]? := by
    simpa using hlist
  rw [hleftSome, hrightSome] at hlist'
  exact Option.some.inj hlist'.symm

theorem boundary_owner_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (boundaryIndex : Fin boundary.length) :
    PortHypergraph.endpointOwnerEndpoint H (.boundary boundaryIndex) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G (.boundary boundaryIndex)) := by
  simp [PortHypergraph.endpointOwnerEndpoint, e.boundary_preserved]

theorem constructor_owner_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    PortHypergraph.endpointOwnerEndpoint H
        (.constructor (e.nodeEquiv.toFun node)
          (incidenceSlotPreserved e node slot)) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G (.constructor node slot)) := by
  simpa [PortHypergraph.endpointOwnerEndpoint] using
    incidence_get_preserved e node slot

theorem boundary_owner_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (boundaryIndex : Fin boundary.length) :
    PortHypergraph.endpointOwnerEndpoint G (.boundary boundaryIndex) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H (.boundary boundaryIndex)) := by
  simp [PortHypergraph.endpointOwnerEndpoint, e.boundary_reflected]

theorem constructor_owner_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    PortHypergraph.endpointOwnerEndpoint G
        (.constructor (e.nodeEquiv.invFun node)
          (incidenceSlotReflected e node slot)) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H (.constructor node slot)) := by
  simpa [PortHypergraph.endpointOwnerEndpoint] using
    incidence_get_reflected e node slot

def endpointOwnerPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) :
    EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length) →
      EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length)
  | .boundary boundaryIndex => .boundary boundaryIndex
  | .constructor node slot =>
      .constructor (e.nodeEquiv.toFun node)
        (incidenceSlotPreserved e node slot)

def endpointOwnerReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) :
    EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length) →
      EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length)
  | .boundary boundaryIndex => .boundary boundaryIndex
  | .constructor node slot =>
      .constructor (e.nodeEquiv.invFun node)
        (incidenceSlotReflected e node slot)

theorem endpointOwnerEndpoint_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    (owner : EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length)) :
    PortHypergraph.endpointOwnerEndpoint H
        (endpointOwnerPreserved e owner) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G owner) := by
  cases owner with
  | boundary boundaryIndex =>
      exact boundary_owner_preserved e boundaryIndex
  | constructor node slot =>
      exact constructor_owner_preserved e node slot

theorem endpointOwnerEndpoint_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    (owner : EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length)) :
    PortHypergraph.endpointOwnerEndpoint G
        (endpointOwnerReflected e owner) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H owner) := by
  cases owner with
  | boundary boundaryIndex =>
      exact boundary_owner_reflected e boundaryIndex
  | constructor node slot =>
      exact constructor_owner_reflected e node slot

def endpointOwnersOfPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint) :
    PortHypergraph.endpointOwnersOf H (e.endpointEquiv.toFun endpoint) :=
  ⟨endpointOwnerPreserved e owner.1, by
    rw [endpointOwnerEndpoint_preserved e owner.1, owner.2]⟩

def endpointOwnersOfReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint) :
    PortHypergraph.endpointOwnersOf G (e.endpointEquiv.invFun endpoint) :=
  ⟨endpointOwnerReflected e owner.1, by
    rw [endpointOwnerEndpoint_reflected e owner.1, owner.2]⟩

theorem endpointOwnersOfPreserved_unique
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint) :
    ∀ owner' : PortHypergraph.endpointOwnersOf H
        (e.endpointEquiv.toFun endpoint),
      owner' = endpointOwnersOfPreserved e owner := by
  rcases PortHypergraph.endpointOwnersOf_existsUnique H
      (e.endpointEquiv.toFun endpoint) with ⟨uniqueOwner, hunique⟩
  intro owner'
  exact (hunique owner').trans
    (hunique (endpointOwnersOfPreserved e owner)).symm

theorem endpointOwnersOfReflected_unique
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint) :
    ∀ owner' : PortHypergraph.endpointOwnersOf G
        (e.endpointEquiv.invFun endpoint),
      owner' = endpointOwnersOfReflected e owner := by
  rcases PortHypergraph.endpointOwnersOf_existsUnique G
      (e.endpointEquiv.invFun endpoint) with ⟨uniqueOwner, hunique⟩
  intro owner'
  exact (hunique owner').trans
    (hunique (endpointOwnersOfReflected e owner)).symm

theorem endpointOwnersOf_unique_transport_preserved
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint)
    (owner' : PortHypergraph.endpointOwnersOf H
        (e.endpointEquiv.toFun endpoint)) :
    owner' = endpointOwnersOfPreserved e owner :=
  endpointOwnersOfPreserved_unique e owner owner'

theorem endpointOwnersOf_unique_transport_reflected
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint)
    (owner' : PortHypergraph.endpointOwnersOf G
        (e.endpointEquiv.invFun endpoint)) :
    owner' = endpointOwnersOfReflected e owner :=
  endpointOwnersOfReflected_unique e owner owner'

end PortHypergraphIso

end StringDiagram
end BijForm
