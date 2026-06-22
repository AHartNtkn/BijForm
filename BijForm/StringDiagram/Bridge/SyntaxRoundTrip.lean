import BijForm.StringDiagram.Traversal

namespace BijForm
namespace StringDiagram

open DepPoly

namespace Diag

variable {Sig : Signature}

theorem openEvidence_endpointEdge_val_of_endpoint_eq
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : RenderState.OpenPortHypergraphEvidence st boundary)
    {left right : Fin st.endpoints.length} {edge : Nat}
    (h : left = right)
    (hedge : (ev.graph.toPortHypergraph.endpointEdge right).val = edge) :
    (ev.toOpenPortHypergraph.raw.endpointEdge left).val = edge := by
  change (ev.graph.toPortHypergraph.endpointEdge left).val = edge
  cases h
  exact hedge

/--
Bridge support for the syntax round-trip: in the semantic graph rendered from
a top-level `connect`, the executable first-pending search on the initial
ordered-boundary state returns the corresponding `connect` branch.
-/
theorem toOpenPortHypergraph_connect_initial_search
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate)) :
    let d : Diag Sig (active :: frontier) := Diag.connect mate ok child
    let G := Diag.toOpenPortHypergraph d
    let st := OpenPortHypergraph.SearchState.initial G
    let rest : List (Fin G.raw.endpointCount) :=
      List.ofFn fun i : Fin frontier.length =>
        G.raw.boundaryPort ⟨i.val + 1, by
          simp [i.isLt]⟩
    ∃ hmate : PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        (rest.get (listIndexCast rest (by dsimp [rest]; simp) mate)),
      st.firstPendingStepSearch?
          (G.raw.boundaryPort ⟨0, by simp⟩) rest =
        some (OpenPortHypergraph.FirstPendingStep.connect
          (listIndexCast rest (by dsimp [rest]; simp) mate) hmate) := by
  intro d G st rest
  let mateTail : Fin rest.length := listIndexCast rest (by simp [rest]) mate
  have hpending :
      st.pending = G.raw.boundaryPort ⟨0, by simp⟩ :: rest := by
    dsimp [st, OpenPortHypergraph.SearchState.initial, rest]
    rw [List.ofFn_succ]
    congr
  have hrestGet :
      rest.get mateTail =
        G.raw.boundaryPort ⟨mate.val + 1, by
          simp [mate.isLt]⟩ := by
    simp [rest, mateTail]
  have hmateBase :=
    Diag.toOpenPortHypergraph_connect_boundary_edgeMate mate ok child
  have hmate :
      PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        (rest.get mateTail) := by
    rw [hrestGet]
    simpa [d, G] using hmateBase
  have hrestNodup := st.rest_nodup hpending
  rcases st.firstPendingStepSearch?_some_connect_exact_of_witness
      hrestNodup mateTail hmate with ⟨hmate', hstep⟩
  refine ⟨hmate', ?_⟩
  simpa [mateTail] using hstep

/--
Bridge support for the syntax round-trip: in the semantic graph rendered from
a top-level `bud`, the executable first-pending search on the initial
ordered-boundary state returns the corresponding `bud` branch.  The proof also
shows that no pending-boundary `connect` mate can precede the constructor entry,
using endpoint-owner uniqueness to separate boundary endpoints from constructor
incidences.
-/
theorem toOpenPortHypergraph_bud_initial_search
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
    let d : Diag Sig (active :: frontier) := Diag.bud node entry ok child
    let G := Diag.toOpenPortHypergraph d
    let st := OpenPortHypergraph.SearchState.initial G
    let rest : List (Fin G.raw.endpointCount) :=
      List.ofFn fun i : Fin frontier.length =>
        G.raw.boundaryPort ⟨i.val + 1, by
          simp [i.isLt]⟩
    ∃ (nodeIndex : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident nodeIndex).length)
      (hmate : PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        ((G.raw.incident nodeIndex).get slot))
      (hunseen : ¬ st.seenNode nodeIndex),
      st.firstPendingStepSearch?
          (G.raw.boundaryPort ⟨0, by simp⟩) rest =
        some (OpenPortHypergraph.FirstPendingStep.bud
          nodeIndex slot hmate hunseen) := by
  intro d G st rest
  rcases Diag.toOpenPortHypergraph_bud_boundary_entry_edgeMate
      node entry ok child with
    ⟨nodeIndex, slot, _hnodeLabel, _hslotVal, hmate⟩
  have hunseen : ¬ st.seenNode nodeIndex := by
    simp [st, OpenPortHypergraph.SearchState.initial,
      OpenPortHypergraph.SearchState.seenNode]
  have hboundary_constructor_ne
      (b : Fin (active :: frontier).length) :
      G.raw.boundaryPort b ≠ (G.raw.incident nodeIndex).get slot := by
    intro hsame
    let endpoint := G.raw.boundaryPort b
    have himpossible :
        (.boundary b :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) =
        .constructor nodeIndex slot :=
      PortHypergraph.endpointOwner_eq_of_endpoint G.raw
        (owner₁ := .boundary b)
        (owner₂ := .constructor nodeIndex slot)
        rfl
        (by
          change (G.raw.incident nodeIndex).get slot = endpoint
          exact hsame.symm)
    cases himpossible
  have hconnect :
      OpenPortHypergraph.firstPendingConnectSearch? G st.seenNode
        (G.raw.boundaryPort ⟨0, by simp⟩) rest = none := by
    exact OpenPortHypergraph.firstPendingConnectSearch?_none_of_forall_not_edgeMate
      G st.seenNode (by
        intro tailMate htailMate
        have hsameMate :
            rest.get tailMate = (G.raw.incident nodeIndex).get slot := by
          exact PortHypergraph.edgeMate_eq_of_same_endpoint G.raw
            htailMate hmate
        let b : Fin (active :: frontier).length :=
          ⟨tailMate.val + 1, by
            have htail := tailMate.isLt
            simp [rest] at htail
            simp
            omega⟩
        have hrestBoundary :
            rest.get tailMate = G.raw.boundaryPort b := by
          simp [rest, b]
        exact hboundary_constructor_ne b (hrestBoundary.symm.trans hsameMate))
  rcases st.firstPendingStepSearch?_some_bud_exact_of_witness
      hconnect nodeIndex slot hmate hunseen with
    ⟨hmate', hunseen', hstep⟩
  exact ⟨nodeIndex, slot, hmate', hunseen', hstep⟩

/--
Arbitrary-prefix version of rendered `connect` recognition.  If a completed
render trace is viewed through semantic graph evidence, the edge introduced by
the current top-level `connect` makes the active frontier endpoint and selected
mate endpoint edge-mates in that semantic graph.
-/
theorem renderTrace_connect_edgeMate_of_invariants
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hv : (renderTrace (Diag.connect mate ok child) st).ValidIds)
    (hp : (renderTrace (Diag.connect mate ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.connect mate ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.connect mate ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.connect mate ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.connect mate ok child) st
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    let mateId :=
      restIds.get (listIndexCast restIds (by
        exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
    ∃ (hactive : activeId < final.endpoints.length)
      (hmateBound : mateId < final.endpoints.length),
      PortHypergraph.EdgeMate G
        ⟨activeId, hactive⟩ ⟨mateId, hmateBound⟩ := by
  intro final G mateId
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := mateId
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hedgeMem : edge ∈ final.edges := by
    simpa [final, edge, mateId] using
      renderTrace_connect_edge_mem mate ok child st hids
  rcases list_exists_get_of_mem final.edges hedgeMem with
    ⟨edgeIndex, hedgeIndex⟩
  have hleftEq : (final.edges.get edgeIndex).left = activeId := by
    have h := congrArg RenderEdge.left hedgeIndex
    simpa [edge] using h
  have hrightEq : (final.edges.get edgeIndex).right = mateId := by
    have h := congrArg RenderEdge.right hedgeIndex
    simpa [edge] using h
  have hleftEqRaw :
      (((renderTrace (Diag.connect mate ok child) st).edges.get edgeIndex).left) =
        activeId := by
    simpa [final] using hleftEq
  have hrightEqRaw :
      (((renderTrace (Diag.connect mate ok child) st).edges.get edgeIndex).right) =
        mateId := by
    simpa [final] using hrightEq
  have hactiveBound :
      activeId < final.endpoints.length := by
    have h := hv.edge_left_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hleftEqRaw] at h
    simpa [final] using h
  have hmateBound :
      mateId < final.endpoints.length := by
    have h := hv.edge_right_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hrightEqRaw] at h
    simpa [final] using h
  refine ⟨hactiveBound, hmateBound, ?_⟩
  have hactiveVal :
      (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).left :=
    hleftEq.symm
  have hmateVal :
      (⟨mateId, hmateBound⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).right :=
    hrightEq.symm
  simpa [G, final] using
    RenderState.edgeMateOfInvariants_of_endpoint_sides
      hv hp hn pref ho
      (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
      (⟨mateId, hmateBound⟩ : Fin final.endpoints.length)
      edgeIndex hactiveVal hmateVal

/--
In a completed render trace whose current step is `connect`, the active
frontier endpoint is assigned to the newly rendered edge index.
-/
theorem renderTrace_connect_active_endpointEdge_val
    {active : Sig.Port} {frontier boundary : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    (hv : (renderTrace (Diag.connect mate ok child) st).ValidIds)
    (hp : (renderTrace (Diag.connect mate ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.connect mate ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.connect mate ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.connect mate ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (hactive : activeId <
      (renderTrace (Diag.connect mate ok child) st).endpoints.length) :
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    (G.endpointEdge ⟨activeId, hactive⟩).val = st.edges.length := by
  intro G
  let final := renderTrace (Diag.connect mate ok child) st
  let mateId :=
    restIds.get (listIndexCast restIds (by
      exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := mateId
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let edgeIndex : Fin final.edges.length :=
    renderTrace_connect_new_edgeIndex mate ok child st hids
  have hedgeGet :
      final.edges.get edgeIndex = edge := by
    simpa [final, mateId, edge, edgeIndex] using
      renderTrace_connect_new_edge_get mate ok child st hids
  have hside :
      (⟨activeId, hactive⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).left := by
    exact (congrArg RenderEdge.left hedgeGet).symm
  have heq :=
    RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
      (⟨activeId, hactive⟩ : Fin final.endpoints.length)
      edgeIndex (Or.inl hside)
  have hraw :
      G.endpointEdge ⟨activeId, hactive⟩ =
        edgeIndex := by
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using heq
  exact (congrArg Fin.val hraw).trans (by
    simp [edgeIndex])

/--
In a completed render trace whose current step is `bud`, the active frontier
endpoint is assigned to the newly rendered edge index.
-/
theorem renderTrace_bud_active_endpointEdge_val
    {active : Sig.Port} {frontier boundary : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : (renderTrace (Diag.bud node entry ok child) st).ValidIds)
    (hp : (renderTrace (Diag.bud node entry ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.bud node entry ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.bud node entry ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.bud node entry ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (hactive : activeId <
      (renderTrace (Diag.bud node entry ok child) st).endpoints.length) :
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    (G.endpointEdge ⟨activeId, hactive⟩).val = st.edges.length := by
  intro G
  let final := renderTrace (Diag.bud node entry ok child) st
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let edgeIndex : Fin final.edges.length :=
    renderTrace_bud_new_edgeIndex node entry ok child st hids
  have hedgeGet :
      final.edges.get edgeIndex = edge := by
    simpa [final, edge, nodeEndpoints, entryIdx, edgeIndex] using
      renderTrace_bud_new_edge_get node entry ok child st hids
  have hside :
      (⟨activeId, hactive⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).left := by
    exact (congrArg RenderEdge.left hedgeGet).symm
  have heq :=
    RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
      (⟨activeId, hactive⟩ : Fin final.endpoints.length)
      edgeIndex (Or.inl hside)
  have hraw :
      G.endpointEdge ⟨activeId, hactive⟩ =
        edgeIndex := by
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using heq
  exact (congrArg Fin.val hraw).trans (by
    simp [edgeIndex])

/--
Exact arbitrary-prefix recognition for rendered `bud`.  The constructor found
by the first-pending search is the node allocated by the current render step,
with the original entry slot and ordered incident endpoint IDs.
-/
theorem renderTrace_bud_entry_edgeMate_exact_of_invariants
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hv : (renderTrace (Diag.bud node entry ok child) st).ValidIds)
    (hp : (renderTrace (Diag.bud node entry ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.bud node entry ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.bud node entry ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.bud node entry ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    ∃ (hactive : activeId < final.endpoints.length)
      (nodeIndex : Fin G.nodeCount)
      (slot : Fin (G.incident nodeIndex).length),
      nodeIndex.val = st.nodes.length ∧
        G.nodeLabel nodeIndex = node ∧
        slot.val = entry.val ∧
        (G.incident nodeIndex).map (fun endpoint => endpoint.val) =
          freshNodeEndpoints st.nextEndpoint (Sig.arity node) ∧
        PortHypergraph.EdgeMate G
          ⟨activeId, hactive⟩ ((G.incident nodeIndex).get slot) := by
  intro final G
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  let edgeIndex : Fin final.edges.length :=
    renderTrace_bud_new_edgeIndex node entry ok child st hids
  let nodeIndexRaw : Fin final.nodes.length :=
    renderTrace_bud_new_nodeIndex node entry ok child st
  have hedgeGet :
      final.edges.get edgeIndex = edge := by
    simpa [final, edge, nodeEndpoints, entryIdx, edgeIndex] using
      renderTrace_bud_new_edge_get node entry ok child st hids
  have hnodeGet :
      final.nodes.get nodeIndexRaw = renderNode := by
    simpa [final, renderNode, nodeEndpoints, nodeIndexRaw] using
      renderTrace_bud_new_node_get node entry ok child st
  let nodeIndex : Fin G.nodeCount :=
    by
      dsimp [G, final, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants]
      exact nodeIndexRaw
  have hleftEq :
      (final.edges.get edgeIndex).left = activeId := by
    have h := congrArg RenderEdge.left hedgeGet
    simpa [edge, edgeIndex] using h
  have hrightEq :
      (final.edges.get edgeIndex).right = nodeEndpoints.get entryIdx := by
    have h := congrArg RenderEdge.right hedgeGet
    simpa [edge, edgeIndex] using h
  have hleftEqRaw :
      (((renderTrace (Diag.bud node entry ok child) st).edges.get edgeIndex).left) =
        activeId := by
    simpa [final] using hleftEq
  have hactiveBound :
      activeId < final.endpoints.length := by
    have h := hv.edge_left_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hleftEqRaw] at h
    simpa [final] using h
  have hnodeLabel : G.nodeLabel nodeIndex = node := by
    have hlabel := congrArg RenderNode.label hnodeGet
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants, nodeIndex,
      renderNode, nodeEndpoints] using hlabel
  let slot : Fin (G.incident nodeIndex).length :=
    listIndexCast (G.incident nodeIndex) (by
      calc
        Sig.arity node = Sig.arity (G.nodeLabel nodeIndex) := by
          rw [hnodeLabel]
        _ = (G.incident nodeIndex).length :=
          (G.incident_length nodeIndex).symm) entry
  have hslotVal : slot.val = entry.val := by
    simp [slot]
  have hincidentVals :
      (G.incident nodeIndex).map (fun endpoint => endpoint.val) =
        nodeEndpoints := by
    have hmap :
        (RenderState.incidentOfValidIds hv
            (show Fin final.nodes.length from nodeIndex)).map
            (fun endpoint => endpoint.val) =
          (final.nodes.get (show Fin final.nodes.length from nodeIndex)).incident :=
      RenderState.incidentOfValidIds_map_val hv
        (show Fin final.nodes.length from nodeIndex)
    have hraw :
        (final.nodes.get (show Fin final.nodes.length from nodeIndex)).incident =
          nodeEndpoints := by
      simpa [nodeIndex, renderNode] using congrArg RenderNode.incident hnodeGet
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.incidenceEvidenceOfValidIds] using hmap.trans hraw
  have hincidentVal :
      ((G.incident nodeIndex).get slot).val =
        (final.edges.get edgeIndex).right := by
    have hget :
        ((G.incident nodeIndex).get slot).val =
          nodeEndpoints.get entryIdx := by
      exact list_get_map_eq_get_of_val_eq (fun endpoint => endpoint.val)
        hincidentVals slot entryIdx (by simpa [entryIdx] using hslotVal)
    exact hget.trans hrightEq.symm
  have hnodeIndexVal : nodeIndex.val = st.nodes.length := by
    simp [nodeIndex, nodeIndexRaw]
  refine ⟨hactiveBound, nodeIndex, slot, hnodeIndexVal, hnodeLabel, hslotVal,
    hincidentVals, ?_⟩
  simpa [G, final] using
    RenderState.edgeMateOfInvariants_of_endpoint_sides
      hv hp hn pref ho
      (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
      ((G.incident nodeIndex).get slot)
      edgeIndex hleftEqRaw.symm hincidentVal

/--
If a search state is related to a renderer prefix of a completed render trace,
then the owned first-pending traversal replays the remaining syntax exactly.
This is the recursive proof spine for the syntax-to-graph-to-syntax inverse.
-/
theorem toDiag_of_renderPrefixRelated :
    ∀ {frontier boundary : List Sig.Port}
      (d : Diag Sig frontier)
      (rst : RenderState Sig frontier)
      (_rhv : rst.ValidIds)
      (_rhp : rst.EndpointPartition)
      (_rhn : rst.NodeIncidentNodup)
      (_rpref : rst.EndpointPrefix boundary)
      (_rho : rst.OwnerIdPartition boundary)
      (_rhr : rst.Reachability boundary)
      (hv : (renderTrace d rst).ValidIds)
      (hp : (renderTrace d rst).EndpointPartition)
      (hn : (renderTrace d rst).NodeIncidentNodup)
      (pref : (renderTrace d rst).EndpointPrefix boundary)
      (ho : (renderTrace d rst).OwnerIdPartition boundary)
      (hall :
        PortHypergraph.AllConstructorsReachBoundary
          (RenderState.portHypergraphEvidenceOfInvariants hv hp hn pref ho).toPortHypergraph)
      (sst : OpenPortHypergraph.SearchState
        (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
        frontier)
      (_hrel : OpenPortHypergraph.SearchState.RenderPrefixRelated
        (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall) rst sst)
      (hcomplete : sst.FrontierComplete),
      sst.toDiag hcomplete = d := by
  intro frontier boundary d
  induction d with
  | finish =>
      intro rst _rhv _rhp _rhn _rpref _rho _rhr hv hp hn pref ho hall sst _hrel hcomplete
      rw [OpenPortHypergraph.SearchState.toDiag_empty]
  | connect mate ok child ih =>
      intro rst rhv rhp rhn rpref rho rhr hv hp hn pref ho hall sst hrel hcomplete
      rename_i activeLabel frontier
      cases hpendingCase : sst.pending with
      | nil =>
          have hlabels := sst.pending_labels
          rw [hpendingCase] at hlabels
          simp at hlabels
      | cons activeEndpoint rest =>
          cases hidsCase : rst.frontierIds with
          | nil =>
              exact False.elim
                (RenderState.frontierIds_ne_nil rst hidsCase)
          | cons activeId restIds =>
              have hpending :
                  sst.pending = activeEndpoint :: rest := hpendingCase
              have hids : rst.frontierIds = activeId :: restIds := hidsCase
              have hvals := hrel.pending_cons_values hpending hids
              have hrestIdsLen : restIds.length = frontier.length := by
                exact RenderState.frontierIds_cons_tail_length rst hids
              have hrestLenVals : rest.length = restIds.length := by
                have hlen := congrArg List.length hvals.2
                simpa using hlen
              have hrestLen : rest.length = frontier.length :=
                hrestLenVals.trans hrestIdsLen
              let searchMate : Fin rest.length := listIndexCast rest hrestLen.symm mate
              let renderMateInRestIds : Fin restIds.length :=
                listIndexCast restIds hrestIdsLen.symm mate
              have hmateVal :
                  (rest.get searchMate).val =
                    restIds.get renderMateInRestIds := by
                have hget :=
                  list_get_map_eq_get (fun endpoint =>
                    (endpoint : Fin (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointCount).val)
                    hvals.2 searchMate
                simpa [searchMate, renderMateInRestIds] using hget
              rcases renderTrace_connect_edgeMate_of_invariants
                  mate ok child rst hv hp hn pref ho hids with
                ⟨hactiveBound, hmateBound, hmateRendered⟩
              have hactiveEq :
                  activeEndpoint =
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length) := by
                exact fin_eq_of_val_eq hvals.1
              have hmateEq :
                  rest.get searchMate =
                    (⟨restIds.get renderMateInRestIds, hmateBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length) := by
                exact fin_eq_of_val_eq hmateVal
              have hmateSearch :
                  PortHypergraph.EdgeMate (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw
                    activeEndpoint (rest.get searchMate) := by
                rw [hactiveEq, hmateEq]
                change
                  PortHypergraph.EdgeMate (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).graph.toPortHypergraph
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length)
                    (⟨restIds.get renderMateInRestIds, hmateBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length)
                simpa [renderMateInRestIds] using hmateRendered
              rcases sst.firstPendingStepSearch?_some_connect_exact_of_witness
                  (sst.rest_nodup hpending) searchMate hmateSearch with
                ⟨hmateSearch', hstep⟩
              rw [OpenPortHypergraph.SearchState.toDiag_connect sst hcomplete
                hpending searchMate hmateSearch' hstep]
              have hidx :
                  sst.restLabelIndex hpending searchMate = mate := by
                exact fin_eq_of_val_eq (by
                  simp [OpenPortHypergraph.SearchState.restLabelIndex,
                    searchMate])
              have hactiveEdgeRaw :=
                renderTrace_connect_active_endpointEdge_val
                  mate ok child rst hv hp hn pref ho hids hactiveBound
              have hactiveEdge :
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointEdge activeEndpoint).val =
                    rst.edges.length := by
                exact openEvidence_endpointEdge_val_of_endpoint_eq
                  (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                  hactiveEq hactiveEdgeRaw
              have hchildComplete :
                  (sst.connectChild hpending searchMate hmateSearch').FrontierComplete :=
                sst.connectChild_frontierComplete hpending searchMate
                  hmateSearch' hcomplete
              have hchildRel :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall) (connectStep mate ok rst)
                    (sst.connectChild hpending searchMate hmateSearch') := by
                cases hidx
                exact hrel.connectChild_of_new_edge hpending searchMate
                  hmateSearch' ok hactiveEdge
                  (connectStep_edges_length mate ok rst)
                  (by
                    have hnodes := connectStep_nodes mate ok rst
                    exact congrArg List.length hnodes)
              have hchild :=
                ih (connectStep mate ok rst)
                  (connectStep_validIds mate ok rst rhv)
                  (connectStep_endpointPartition mate ok rst rhv rhp)
                  (connectStep_nodeIncidentNodup mate ok rst rhn)
                  (connectStep_endpointPrefix mate ok rst rpref)
                  (connectStep_ownerIdPartition mate ok rst rho)
                  (connectStep_reachability mate ok rst rhr)
                  hv hp hn pref ho hall
                  (sst.connectChild hpending searchMate hmateSearch')
                  hchildRel
                  hchildComplete
              have hok :
                  sst.connect_compatible hpending searchMate hmateSearch' = ok :=
                Subsingleton.elim _ _
              cases hok
              rw [hchild]
              cases hidx
              rfl
  | bud node entry ok child ih =>
      intro rst rhv rhp rhn rpref rho rhr hv hp hn pref ho hall sst hrel hcomplete
      rename_i activeLabel frontier
      cases hpendingCase : sst.pending with
      | nil =>
          have hlabels := sst.pending_labels
          rw [hpendingCase] at hlabels
          simp at hlabels
      | cons activeEndpoint rest =>
          cases hidsCase : rst.frontierIds with
          | nil =>
              exact False.elim
                (RenderState.frontierIds_ne_nil rst hidsCase)
          | cons activeId restIds =>
              have hpending :
                  sst.pending = activeEndpoint :: rest := hpendingCase
              have hids : rst.frontierIds = activeId :: restIds := hidsCase
              have hvals := hrel.pending_cons_values hpending hids
              have hrestIdsLen : restIds.length = frontier.length := by
                exact RenderState.frontierIds_cons_tail_length rst hids
              have hrestLenVals : rest.length = restIds.length := by
                have hlen := congrArg List.length hvals.2
                simpa using hlen
              rcases renderTrace_bud_entry_edgeMate_exact_of_invariants
                  node entry ok child rst hv hp hn pref ho hids with
                ⟨hactiveBound, nodeIndex, slot, hnewNode, hnodeLabel,
                  hslotVal, hincidentVals, hmateRendered⟩
              have hactiveEq :
                  activeEndpoint =
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.bud node entry ok child) rst).endpoints.length) := by
                exact fin_eq_of_val_eq hvals.1
              have hmateSearch :
                  PortHypergraph.EdgeMate (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw
                    activeEndpoint (((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.incident nodeIndex).get slot) := by
                rw [hactiveEq]
                change
                  PortHypergraph.EdgeMate (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).graph.toPortHypergraph
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.bud node entry ok child) rst).endpoints.length)
                    (((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).graph.toPortHypergraph.incident nodeIndex).get slot)
                simpa using hmateRendered
              have hunseen : ¬ sst.seenNode nodeIndex := by
                intro hseen
                have hlt := (hrel.seen_prefix nodeIndex).1 hseen
                omega
              have hentryFreshVal :
                  (((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.incident nodeIndex).get slot).val =
                    (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                      (listIndexCast
                        (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                        (by simp [freshNodeEndpoints]) entry) := by
                exact list_get_map_eq_get_of_val_eq (fun endpoint =>
                  (endpoint : Fin (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointCount).val)
                  hincidentVals slot
                  (listIndexCast
                    (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                    (by simp [freshNodeEndpoints]) entry)
                  hslotVal
              have hconnectNone :
                  OpenPortHypergraph.firstPendingConnectSearch? (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                    sst.seenNode activeEndpoint rest = none := by
                exact OpenPortHypergraph.firstPendingConnectSearch?_none_of_forall_not_edgeMate
                  (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                  sst.seenNode (by
                    intro tailMate htailMate
                    have htailEq :
                        rest.get tailMate =
                          ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.incident nodeIndex).get slot := by
                      exact PortHypergraph.edgeMate_eq_of_same_endpoint
                        (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw
                        htailMate hmateSearch
                    let tailRestIdx : Fin restIds.length :=
                      listIndexCast restIds hrestLenVals tailMate
                    have htailVal :
                        (rest.get tailMate).val =
                          restIds.get tailRestIdx := by
                      have hget :=
                        list_get_map_eq_get (fun endpoint =>
                          (endpoint : Fin (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointCount).val)
                          hvals.2 tailMate
                      simpa [tailRestIdx] using hget
                    have holdLt :
                        restIds.get tailRestIdx < rst.nextEndpoint := by
                      have hbound :=
                        rhv.frontier_bound (restIds.get tailRestIdx) (by
                          rw [hids]
                          right
                          exact List.get_mem restIds tailRestIdx)
                      rw [rhv.nextEndpoint_eq]
                      exact hbound
                    have hfreshMem :
                        (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                            (listIndexCast
                              (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                              (by simp [freshNodeEndpoints]) entry) ∈
                          freshNodeEndpoints rst.nextEndpoint (Sig.arity node) :=
                      List.get_mem
                        (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                        (listIndexCast
                          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                          (by simp [freshNodeEndpoints]) entry)
                    have hfreshGe :
                        rst.nextEndpoint ≤
                          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                            (listIndexCast
                              (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                              (by simp [freshNodeEndpoints]) entry) :=
                      freshNodeEndpoints_mem_ge hfreshMem
                    have heqVal :
                        restIds.get tailRestIdx =
                          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                            (listIndexCast
                              (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                              (by simp [freshNodeEndpoints]) entry) := by
                      exact htailVal.symm.trans
                        ((congrArg (fun endpoint => endpoint.val) htailEq).trans
                          hentryFreshVal)
                    omega)
              rcases sst.firstPendingStepSearch?_some_bud_exact_of_witness
                  hconnectNone nodeIndex slot hmateSearch hunseen with
                ⟨hmateSearch', hunseen', hstep⟩
              rw [OpenPortHypergraph.SearchState.toDiag_bud sst hcomplete
                hpending nodeIndex slot hmateSearch' hunseen' hstep]
              have hentryVal :
                  (OpenPortHypergraph.SearchState.budEntry
                    (G := (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph)
                    nodeIndex slot).val =
                    entry.val := by
                simpa [OpenPortHypergraph.SearchState.budEntry] using hslotVal
              have hfrontier :
                  frontier ++
                      Sig.nodePortsExcept
                        ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.nodeLabel
                          nodeIndex)
                        (OpenPortHypergraph.SearchState.budEntry
                          (G := (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph)
                          nodeIndex slot) =
                    frontier ++ Sig.nodePortsExcept node entry := by
                exact congrArg (fun tail => frontier ++ tail)
                  (Signature.nodePortsExcept_eq_of_val (Sig := Sig)
                    hnodeLabel hentryVal)
              let searchChildB :=
                sst.budChild hpending nodeIndex slot hmateSearch' hunseen'
              have hactiveEdgeRaw :=
                renderTrace_bud_active_endpointEdge_val
                  node entry ok child rst hv hp hn pref ho hids hactiveBound
              have hactiveEdge :
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointEdge
                      activeEndpoint).val = rst.edges.length := by
                exact openEvidence_endpointEdge_val_of_endpoint_eq
                  (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                  hactiveEq hactiveEdgeRaw
              have hchildRelB :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                    (hfrontier.symm ▸ budStep node entry ok rst) searchChildB := by
                exact hrel.budChild_of_new_edge_node hpending nodeIndex slot
                  hmateSearch' hunseen' node entry ok hfrontier hincidentVals hslotVal
                  hactiveEdge hnewNode
                  (by
                    have hcast :=
                      RenderState.cast_edges hfrontier.symm
                        (budStep node entry ok rst)
                    have hlen := congrArg List.length hcast
                    simpa [hlen] using
                      budStep_edges_length node entry ok rst)
                  (by
                    have hcast :=
                      RenderState.cast_nodes hfrontier.symm
                        (budStep node entry ok rst)
                    have hlen := congrArg List.length hcast
                    simpa [hlen] using
                      budStep_nodes_length node entry ok rst)
              let searchChildA : OpenPortHypergraph.SearchState
                  (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                  (frontier ++ Sig.nodePortsExcept node entry) :=
                hfrontier ▸ searchChildB
              have hchildRelA :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                    (budStep node entry ok rst) searchChildA := by
                simpa [searchChildA] using
                  OpenPortHypergraph.SearchState.RenderPrefixRelated.cast_cancel_left
                    hfrontier hchildRelB
              have hchildCompleteB : searchChildB.FrontierComplete :=
                sst.budChild_frontierComplete hpending nodeIndex slot
                  hmateSearch' hunseen' hcomplete
              have hchildCompleteA : searchChildA.FrontierComplete := by
                dsimp [searchChildA]
                exact OpenPortHypergraph.SearchState.frontierComplete_cast
                  hfrontier searchChildB hchildCompleteB
              have hchildA :=
                ih (budStep node entry ok rst)
                  (budStep_validIds node entry ok rst rhv)
                  (budStep_endpointPartition node entry ok rst rhv rhp)
                  (budStep_nodeIncidentNodup node entry ok rst rhn)
                  (budStep_endpointPrefix node entry ok rst rpref)
                  (budStep_ownerIdPartition node entry ok rst rhv rho)
                  (budStep_reachability node entry ok rst rhr)
                  hv hp hn pref ho hall searchChildA hchildRelA
                  hchildCompleteA
              have hdiagCast :
                  searchChildA.toDiag hchildCompleteA =
                    hfrontier ▸ searchChildB.toDiag hchildCompleteB := by
                dsimp [searchChildA, hchildCompleteA]
                exact OpenPortHypergraph.SearchState.toDiag_cast
                  hfrontier searchChildB hchildCompleteB
              have hchildForTransport :
                  child =
                    hfrontier ▸ searchChildB.toDiag hchildCompleteB :=
                hchildA.symm.trans hdiagCast
              exact (Diag.bud_transport
                (hnode := hnodeLabel)
                (hentryVal := hentryVal)
                (okA := ok)
                (okB := sst.bud_compatible hpending nodeIndex slot
                  hmateSearch')
                (childA := child)
                (childB := searchChildB.toDiag hchildCompleteB)
                hfrontier hchildForTransport).symm

end Diag

end StringDiagram
end BijForm
