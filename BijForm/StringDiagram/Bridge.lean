import BijForm.StringDiagram.Traversal

namespace BijForm
namespace StringDiagram

open DepPoly

namespace Diag

variable {Sig : Signature}

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
        (rest.get (Fin.cast (by dsimp [rest]; simp) mate)),
      st.firstPendingStepSearch?
          (G.raw.boundaryPort ⟨0, by simp⟩) rest =
        some (OpenPortHypergraph.FirstPendingStep.connect
          (Fin.cast (by dsimp [rest]; simp) mate) hmate) := by
  intro d G st rest
  let mateTail : Fin rest.length := Fin.cast (by simp [rest]) mate
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
    rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
    have hboundaryEq :
        (.boundary b :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      rfl
    have hconstructorEq :
        (.constructor nodeIndex slot :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      change (G.raw.incident nodeIndex).get slot = endpoint
      exact hsame.symm
    have himpossible :
        (.boundary b :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) =
        .constructor nodeIndex slot :=
      hboundaryEq.trans hconstructorEq.symm
    cases himpossible
  have hconnect :
      OpenPortHypergraph.firstPendingConnectSearch? G st.seenNode
        (G.raw.boundaryPort ⟨0, by simp⟩) rest = none := by
    cases hcase :
        OpenPortHypergraph.firstPendingConnectSearch? G st.seenNode
          (G.raw.boundaryPort ⟨0, by simp⟩) rest with
    | none => rfl
    | some step =>
        rcases OpenPortHypergraph.firstPendingConnectSearch?_some_connect
            G st.seenNode hcase with ⟨tailMate, htailMate, _hstep⟩
        have hsameMate :
            rest.get tailMate = (G.raw.incident nodeIndex).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw
              (G.raw.boundaryPort ⟨0, by simp⟩) with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          exact (huniq (rest.get tailMate) htailMate).trans
            (huniq ((G.raw.incident nodeIndex).get slot) hmate).symm
        let b : Fin (active :: frontier).length :=
          ⟨tailMate.val + 1, by
            have htail := tailMate.isLt
            simp [rest] at htail
            simp
            omega⟩
        have hrestBoundary :
            rest.get tailMate = G.raw.boundaryPort b := by
          simp [rest, b]
        exact False.elim
          (hboundary_constructor_ne b (hrestBoundary.symm.trans hsameMate))
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
      restIds.get (Fin.cast (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        exact (Nat.succ.inj hlen).symm) mate)
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
  constructor
  · intro hsame
    have hval := congrArg (fun endpoint => endpoint.val) hsame
    have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
    exact hne (by
      calc
        (final.edges.get edgeIndex).left =
            (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val :=
          hactiveVal.symm
        _ = (⟨mateId, hmateBound⟩ : Fin final.endpoints.length).val := hval
        _ = (final.edges.get edgeIndex).right := hmateVal)
  · have hleft :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
        edgeIndex (Or.inl hactiveVal)
    have hright :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (⟨mateId, hmateBound⟩ : Fin final.endpoints.length)
        edgeIndex (Or.inr hmateVal)
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

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
  have hedgeGet :
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
            injection hids' with hactiveEq hrestEq
            subst activeId'
            subst restIds'
            simp [edge, mateId]
        rw [renderTrace_connect, hsuffix, hstep]
        simp⟩ = edge := by
    simpa [final, mateId, edge] using
      renderTrace_connect_new_edge_get mate ok child st hids
  let edgeIndex : Fin final.edges.length :=
    ⟨st.edges.length, by
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
          injection hids' with hactiveEq hrestEq
          subst activeId'
          subst restIds'
          simp [edge, mateId]
      rw [renderTrace_connect, hsuffix, hstep]
      simp⟩
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
  rw [hraw]

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
  have hedgeGet :
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
            injection hids' with hactiveEq hrestEq
            subst activeId'
            subst restIds'
            simp [edge, nodeEndpoints, entryIdx]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ = edge := by
    simpa [final, edge, nodeEndpoints, entryIdx] using
      renderTrace_bud_new_edge_get node entry ok child st hids
  let edgeIndex : Fin final.edges.length :=
    ⟨st.edges.length, by
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
          injection hids' with hactiveEq hrestEq
          subst activeId'
          subst restIds'
          simp [edge, nodeEndpoints, entryIdx]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩
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
  rw [hraw]

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
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  have hedgeGet :
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
            injection hids' with hactiveEq hrestEq
            subst activeId'
            subst restIds'
            simp [edge, nodeEndpoints, entryIdx]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ = edge := by
    simpa [final, edge, nodeEndpoints, entryIdx] using
      renderTrace_bud_new_edge_get node entry ok child st hids
  have hnodeGet :
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
    simpa [final, renderNode, nodeEndpoints] using
      renderTrace_bud_new_node_get node entry ok child st
  let edgeIndex : Fin final.edges.length :=
    ⟨st.edges.length, by
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
          injection hids' with hactiveEq hrestEq
          subst activeId'
          subst restIds'
          simp [edge, nodeEndpoints, entryIdx]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩
  let nodeIndex : Fin G.nodeCount :=
    ⟨st.nodes.length, by
      dsimp [G, final, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants]
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
      simp⟩
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
    Fin.cast (by
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
      have hopt := congrArg (fun xs : List Nat => xs[entry.val]?) hincidentVals
      have hleftBound : entry.val < (G.incident nodeIndex).length := by
        have hlen := G.incident_length nodeIndex
        rw [hnodeLabel] at hlen
        simp [hlen]
      have hrightBound : entry.val < nodeEndpoints.length := by
        simp [nodeEndpoints]
      have hleftSome :
          ((G.incident nodeIndex).map
              (fun endpoint => endpoint.val))[entry.val]? =
            some (((G.incident nodeIndex).map
              (fun endpoint => endpoint.val)).get
                ⟨entry.val, by simpa using hleftBound⟩) :=
        List.getElem?_eq_getElem (by simpa using hleftBound)
      have hrightSome :
          nodeEndpoints[entry.val]? =
            some (nodeEndpoints.get ⟨entry.val, hrightBound⟩) :=
        List.getElem?_eq_getElem hrightBound
      change
        ((G.incident nodeIndex).map
            (fun endpoint => endpoint.val))[entry.val]? =
          nodeEndpoints[entry.val]? at hopt
      rw [hleftSome, hrightSome] at hopt
      injection hopt with hval
      have hval' :
          ((G.incident nodeIndex).get ⟨entry.val, hleftBound⟩).val =
            nodeEndpoints.get ⟨entry.val, hrightBound⟩ := by
        simpa using hval
      have hslotEq : slot = ⟨entry.val, hleftBound⟩ := by
        apply Fin.ext
        exact hslotVal
      have hentryIdxEq : entryIdx = ⟨entry.val, hrightBound⟩ := by
        apply Fin.ext
        rfl
      rw [hslotEq, hentryIdxEq]
      exact hval'
    exact hget.trans hrightEq.symm
  refine ⟨hactiveBound, nodeIndex, slot, rfl, hnodeLabel, hslotVal,
    hincidentVals, ?_⟩
  constructor
  · intro hsame
    have hval := congrArg (fun endpoint => endpoint.val) hsame
    have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
    exact hne (by
      calc
        (final.edges.get edgeIndex).left =
            (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val :=
          hleftEq
        _ = ((G.incident nodeIndex).get slot).val := hval
        _ = (final.edges.get edgeIndex).right := hincidentVal)
  · have hleft :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
        edgeIndex (Or.inl hleftEqRaw.symm)
    have hright :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        ((G.incident nodeIndex).get slot) edgeIndex (Or.inr hincidentVal)
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

/--
Arbitrary-prefix version of rendered `bud` recognition.  If a completed render
trace is viewed through semantic graph evidence, the constructor introduced by
the current top-level `bud` has the original label and entry position, and the
active frontier endpoint is edge-mated to that constructor entry endpoint.
-/
theorem renderTrace_bud_entry_edgeMate_of_invariants
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
      G.nodeLabel nodeIndex = node ∧
        slot.val = entry.val ∧
        PortHypergraph.EdgeMate G
          ⟨activeId, hactive⟩ ((G.incident nodeIndex).get slot) := by
  intro final G
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
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  have hedgeMem : edge ∈ final.edges := by
    simpa [final, edge, nodeEndpoints, entryIdx] using
      renderTrace_bud_edge_mem node entry ok child st hids
  have hnodeMem : renderNode ∈ final.nodes := by
    simpa [final, renderNode, nodeEndpoints] using
      renderTrace_bud_node_mem node entry ok child st
  rcases list_exists_get_of_mem final.edges hedgeMem with
    ⟨edgeIndex, hedgeIndex⟩
  rcases list_exists_get_of_mem final.nodes hnodeMem with
    ⟨nodeIndex, hnodeIndex⟩
  have hleftEq : (final.edges.get edgeIndex).left = activeId := by
    have h := congrArg RenderEdge.left hedgeIndex
    simpa [edge] using h
  have hrightEq :
      (final.edges.get edgeIndex).right = nodeEndpoints.get entryIdx := by
    have h := congrArg RenderEdge.right hedgeIndex
    simpa [edge] using h
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
    dsimp [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants, renderNode,
      nodeEndpoints] at *
    rw [hnodeIndex]
  let slot : Fin (G.incident nodeIndex).length :=
    Fin.cast (by
      calc
        Sig.arity node = Sig.arity (G.nodeLabel nodeIndex) := by
          rw [hnodeLabel]
        _ = (G.incident nodeIndex).length :=
          (G.incident_length nodeIndex).symm) entry
  refine ⟨hactiveBound, nodeIndex, slot, hnodeLabel, ?_, ?_⟩
  · simp [slot]
  · have hincidentVal :
        ((G.incident nodeIndex).get slot).val =
          (final.edges.get edgeIndex).right := by
      have hincidentList :
          (final.nodes.get nodeIndex).incident = nodeEndpoints := by
        simpa [renderNode] using congrArg RenderNode.incident hnodeIndex
      have hentryGet :
          (final.nodes.get nodeIndex).incident.get
              (Fin.cast (by
                rw [hincidentList]
                simp [nodeEndpoints]) entry) =
            nodeEndpoints.get entryIdx := by
        have hleftBound :
            entry.val < (final.nodes.get nodeIndex).incident.length := by
          rw [hincidentList]
          simp [nodeEndpoints]
        have hrightBound : entry.val < nodeEndpoints.length := by
          simp [nodeEndpoints]
        have hleftIdx :
            (Fin.cast (by
              rw [hincidentList]
              simp [nodeEndpoints]) entry :
                Fin (final.nodes.get nodeIndex).incident.length) =
              ⟨entry.val, hleftBound⟩ := by
          apply Fin.ext
          rfl
        have hrightIdx : entryIdx = ⟨entry.val, hrightBound⟩ := by
          apply Fin.ext
          rfl
        have hopt :
            (final.nodes.get nodeIndex).incident[entry.val]? =
              nodeEndpoints[entry.val]? := by
          rw [hincidentList]
        have hleftSome :
            (final.nodes.get nodeIndex).incident[entry.val]? =
              some ((final.nodes.get nodeIndex).incident.get
                ⟨entry.val, hleftBound⟩) :=
          List.getElem?_eq_getElem hleftBound
        have hrightSome :
            nodeEndpoints[entry.val]? =
              some (nodeEndpoints.get ⟨entry.val, hrightBound⟩) :=
          List.getElem?_eq_getElem hrightBound
        have hget :
            (final.nodes.get nodeIndex).incident.get ⟨entry.val, hleftBound⟩ =
              nodeEndpoints.get ⟨entry.val, hrightBound⟩ := by
          rw [hleftSome, hrightSome] at hopt
          injection hopt with hget
        rw [hleftIdx, hrightIdx]
        exact hget
      dsimp [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.incidenceEvidenceOfValidIds,
        RenderState.incidentOfValidIds, edge, slot, renderNode,
        nodeEndpoints, entryIdx]
      simpa [entryIdx] using hentryGet.trans hrightEq.symm
    constructor
    · intro hsame
      have hval := congrArg (fun endpoint => endpoint.val) hsame
      have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
      exact hne (by
        calc
          (final.edges.get edgeIndex).left =
              (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val :=
            hleftEq
          _ = ((G.incident nodeIndex).get slot).val := hval
          _ = (final.edges.get edgeIndex).right := hincidentVal)
    · have hleft :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
          edgeIndex (Or.inl hleftEqRaw.symm)
      have hright :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          ((G.incident nodeIndex).get slot) edgeIndex (Or.inr hincidentVal)
      simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.edgeEvidenceOfPartition,
        RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

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
                have hlen := rst.frontierIds_length
                rw [hids] at hlen
                exact Nat.succ.inj hlen
              have hrestLenVals : rest.length = restIds.length := by
                have hlen := congrArg List.length hvals.2
                simpa using hlen
              have hrestLen : rest.length = frontier.length :=
                hrestLenVals.trans hrestIdsLen
              let searchMate : Fin rest.length := Fin.cast hrestLen.symm mate
              let renderMateInRestIds : Fin restIds.length :=
                Fin.cast hrestIdsLen.symm mate
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
                apply Fin.ext
                exact hvals.1
              have hmateEq :
                  rest.get searchMate =
                    (⟨restIds.get renderMateInRestIds, hmateBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length) := by
                apply Fin.ext
                exact hmateVal
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
                apply Fin.ext
                simp [OpenPortHypergraph.SearchState.restLabelIndex,
                  searchMate]
              have hactiveEdgeRaw :=
                renderTrace_connect_active_endpointEdge_val
                  mate ok child rst hv hp hn pref ho hids hactiveBound
              have hactiveEdge :
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointEdge activeEndpoint).val =
                    rst.edges.length := by
                rw [hactiveEq]
                change
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).graph.toPortHypergraph.endpointEdge
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.connect mate ok child) rst).endpoints.length)).val =
                    rst.edges.length
                simpa using hactiveEdgeRaw
              have hpendingVals :
                  (sst.connectChild hpending searchMate hmateSearch').pending.map
                      (fun endpoint => endpoint.val) =
                    (connectStep mate ok rst).frontierIds := by
                have hvalsChild :=
                  hrel.connectChild_pending_vals hpending searchMate
                    hmateSearch' mate ok (by simp [searchMate])
                simpa using hvalsChild
              have hchildRelRaw :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall) (connectStep mate ok rst)
                    (by
                      cases hidx
                      exact sst.connectChild hpending searchMate hmateSearch') := by
                cases hidx
                exact hrel.connectChild_of_new_edge hpending searchMate
                  hmateSearch' (connectStep mate ok rst) hpendingVals
                  hactiveEdge
                  (connectStep_edges_length mate ok rst)
                  (by
                    have hnodes := connectStep_nodes mate ok rst
                    exact congrArg List.length hnodes)
              have hchildComplete :
                  (sst.connectChild hpending searchMate hmateSearch').FrontierComplete :=
                sst.connectChild_frontierComplete hpending searchMate
                  hmateSearch' hcomplete
              have hchildRel :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall) (connectStep mate ok rst)
                    (sst.connectChild hpending searchMate hmateSearch') := by
                cases hidx
                simpa using hchildRelRaw
              have hchild :=
                ih (connectStep mate ok rst)
                  (connectStep_validIds mate ok rst rhv)
                  (connectStep_endpointPartition mate ok rst rhv rhp)
                  (connectStep_nodeIncidentNodup mate ok rst rhn)
                  (by
                    refine
                      { suffix := rpref.suffix
                        endpoints_eq := ?_ }
                    rw [connectStep_endpoints]
                    exact rpref.endpoints_eq)
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
                have hlen := rst.frontierIds_length
                rw [hids] at hlen
                exact Nat.succ.inj hlen
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
                apply Fin.ext
                exact hvals.1
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
                      (Fin.cast (by simp [freshNodeEndpoints]) entry) := by
                have hget :=
                  list_get_map_eq_get (fun endpoint =>
                    (endpoint : Fin (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointCount).val)
                    hincidentVals slot
                have hidx :
                    (Fin.cast (by rw [← hincidentVals]; simp) slot :
                        Fin (freshNodeEndpoints rst.nextEndpoint
                          (Sig.arity node)).length) =
                      Fin.cast (by simp [freshNodeEndpoints]) entry := by
                  apply Fin.ext
                  exact hslotVal
                rw [hidx] at hget
                exact hget
              have hconnectNone :
                  OpenPortHypergraph.firstPendingConnectSearch? (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                    sst.seenNode activeEndpoint rest = none := by
                cases hconnect :
                    OpenPortHypergraph.firstPendingConnectSearch? (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                      sst.seenNode activeEndpoint rest with
                | none => rfl
                | some step =>
                    rcases OpenPortHypergraph.firstPendingConnectSearch?_some_connect
                       (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph sst.seenNode hconnect with
                      ⟨tailMate, htailMate, _hstepEq⟩
                    have htailEq :
                        rest.get tailMate =
                          ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.incident nodeIndex).get slot := by
                      rcases PortHypergraph.edgeMate_existsUnique
                         (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw activeEndpoint with
                        ⟨uniqueMate, _hunique, huniq⟩
                      exact (huniq (rest.get tailMate) htailMate).trans
                        (huniq
                          (((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.incident nodeIndex).get slot)
                          hmateSearch).symm
                    let tailRestIdx : Fin restIds.length :=
                      Fin.cast hrestLenVals tailMate
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
                            (Fin.cast (by simp [freshNodeEndpoints]) entry) ∈
                          freshNodeEndpoints rst.nextEndpoint (Sig.arity node) :=
                      List.get_mem
                        (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
                        (Fin.cast (by simp [freshNodeEndpoints]) entry)
                    have hfreshGe :
                        rst.nextEndpoint ≤
                          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                            (Fin.cast (by simp [freshNodeEndpoints]) entry) :=
                      freshNodeEndpoints_mem_ge hfreshMem
                    have heqVal :
                        restIds.get tailRestIdx =
                          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
                            (Fin.cast (by simp [freshNodeEndpoints]) entry) := by
                      exact htailVal.symm.trans
                        ((congrArg (fun endpoint => endpoint.val) htailEq).trans
                          hentryFreshVal)
                    omega
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
              let childRstB :
                  RenderState Sig
                    (frontier ++
                      Sig.nodePortsExcept
                        ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.nodeLabel
                          nodeIndex)
                        (OpenPortHypergraph.SearchState.budEntry
                          (G := (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph)
                          nodeIndex slot)) :=
                hfrontier.symm ▸ budStep node entry ok rst
              have hpendingVals :
                  searchChildB.pending.map (fun endpoint => endpoint.val) =
                    (budStep node entry ok rst).frontierIds := by
                exact hrel.budChild_pending_vals hpending nodeIndex slot
                  hmateSearch' hunseen' node entry ok hincidentVals hslotVal
              have hpendingValsB :
                  searchChildB.pending.map (fun endpoint => endpoint.val) =
                    childRstB.frontierIds := by
                simpa [childRstB] using
                  hpendingVals.trans
                    (RenderState.cast_frontierIds hfrontier.symm
                      (budStep node entry ok rst)).symm
              have hactiveEdgeRaw :=
                renderTrace_bud_active_endpointEdge_val
                  node entry ok child rst hv hp hn pref ho hids hactiveBound
              have hactiveEdge :
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph.raw.endpointEdge
                      activeEndpoint).val = rst.edges.length := by
                rw [hactiveEq]
                change
                  ((RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).graph.toPortHypergraph.endpointEdge
                    (⟨activeId, hactiveBound⟩ :
                      Fin (renderTrace (Diag.bud node entry ok child) rst).endpoints.length)).val =
                    rst.edges.length
                simpa using hactiveEdgeRaw
              have hchildRelB :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                    childRstB searchChildB := by
                exact hrel.budChild_of_new_edge_node hpending nodeIndex slot
                  hmateSearch' hunseen' childRstB hpendingValsB
                  hactiveEdge hnewNode
                  (by
                    have hcast :=
                      RenderState.cast_edges hfrontier.symm
                        (budStep node entry ok rst)
                    have hlen := congrArg List.length hcast
                    simpa [childRstB, hlen] using
                      budStep_edges_length node entry ok rst)
                  (by
                    have hcast :=
                      RenderState.cast_nodes hfrontier.symm
                        (budStep node entry ok rst)
                    have hlen := congrArg List.length hcast
                    simpa [childRstB, hlen] using
                      budStep_nodes_length node entry ok rst)
              let searchChildA : OpenPortHypergraph.SearchState
                  (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall).toOpenPortHypergraph
                  (frontier ++ Sig.nodePortsExcept node entry) :=
                hfrontier ▸ searchChildB
              have hchildRelA :
                  OpenPortHypergraph.SearchState.RenderPrefixRelated
                    (RenderState.openEvidenceOfInvariants hv hp hn pref ho hall)
                    (budStep node entry ok rst) searchChildA := by
                simpa [searchChildA, childRstB] using
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
                  (by
                    refine
                      { suffix := rpref.suffix ++ Sig.nodePorts node
                        endpoints_eq := ?_ }
                    rw [budStep_endpoints]
                    rw [rpref.endpoints_eq, List.append_assoc])
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
  rcases G.raw.endpoint_owner endpoint with ⟨owner, _howner, huniq⟩
  have hleftOwner :
      (.constructor leftNode leftSlot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) = owner := by
    apply huniq
    simpa [PortHypergraph.endpointOwnerEndpoint] using hleftSlot
  have hrightOwner :
      (.constructor rightNode rightSlot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) = owner := by
    apply huniq
    simpa [PortHypergraph.endpointOwnerEndpoint] using hrightSlot
  have hsame :
      (.constructor leftNode leftSlot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      .constructor rightNode rightSlot :=
    hleftOwner.trans hrightOwner.symm
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
  rcases G.raw.endpoint_owner endpoint with ⟨owner, _howner, huniq⟩
  have hboundaryOwner :
      (.boundary boundaryIndex :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) = owner := by
    apply huniq
    simpa [PortHypergraph.endpointOwnerEndpoint] using hboundaryEq
  have hconstructorOwner :
      (.constructor node slot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) = owner := by
    apply huniq
    simpa [PortHypergraph.endpointOwnerEndpoint] using hslot
  have hsame :
      (.boundary boundaryIndex :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      .constructor node slot :=
    hboundaryOwner.trans hconstructorOwner.symm
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
original graph.  It records the relabeling that sends rendered endpoint, edge,
and node indices to the original graph indices in traversal order.
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
    cases edge with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  edge_left_bound := by
    intro edge
    cases edge with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  edge_right_bound := by
    intro edge
    cases edge with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  edge_left := by
    intro edge
    cases edge with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  edge_right := by
    intro edge
    cases edge with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  node_label := by
    intro node
    cases node with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  node_incident_length := by
    intro node
    cases node with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  node_incident_bound := by
    intro node
    cases node with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  node_incident := by
    intro node
    cases node with
    | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)

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
      apply Fin.ext
      rfl
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
      apply Fin.ext
      rfl
    have htailCast :
        (⟨id.val, by simpa [htailLen] using id.isLt⟩ :
          Fin rest.length) =
        Fin.cast htailLen id := by
      apply Fin.ext
      rfl
    simpa [hids, hpending, hcast, htailCast] using h

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
    · have hendpoint :
          endpoint =
            (⟨(rst.edges.get edgeIndex).left,
              hrel.edge_left_bound edgeIndex⟩ : Fin rst.endpoints.length) := by
        apply Fin.ext
        exact hleft
      rw [hendpoint]
      have hedge :
          RenderState.endpointEdgeOfPartition hp
              (⟨(rst.edges.get edgeIndex).left,
                hrel.edge_left_bound edgeIndex⟩ :
                Fin rst.endpoints.length) = edgeIndex := by
        exact RenderState.endpointEdgeOfPartition_left hv hp edgeIndex
      rw [hedge]
      exact hrel.edge_left edgeIndex
    · have hendpoint :
          endpoint =
            (⟨(rst.edges.get edgeIndex).right,
              hrel.edge_right_bound edgeIndex⟩ : Fin rst.endpoints.length) := by
        apply Fin.ext
        exact hright
      rw [hendpoint]
      have hedge :
          RenderState.endpointEdgeOfPartition hp
              (⟨(rst.edges.get edgeIndex).right,
                hrel.edge_right_bound edgeIndex⟩ :
                Fin rst.endpoints.length) = edgeIndex := by
        exact RenderState.endpointEdgeOfPartition_right hv hp edgeIndex
      rw [hedge]
      exact hrel.edge_right edgeIndex
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
UNFINISHED inverse law: traversing an open graph to syntax and rendering that
syntax gives an ordered-boundary-preserving isomorphic semantic graph.
-/
theorem OpenPortHypergraph.toOpenPortHypergraph_fromGraph_iso
    {Sig : Signature} {boundary : List Sig.Port}
    (G : OpenPortHypergraph Sig boundary) :
    OpenPortHypergraph.isoRel
      (Diag.toOpenPortHypergraph (OpenPortHypergraph.fromGraph G)) G := by
  sorry

/--
UNFINISHED semantic bridge assembly.  The quotient maps are now wired through
the owned renderer and traversal, but this declaration still depends on the
unfinished graph inverse-law declaration above.
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
