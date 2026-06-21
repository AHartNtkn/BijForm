import BijForm.StringDiagram.Renderer.Steps

namespace BijForm
namespace StringDiagram

open DepPoly

namespace Diag


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

theorem connectStep_endpoints_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (endpoint : Fin (connectStep mate ok st).endpoints.length) :
    (connectStep mate ok st).endpoints.get endpoint =
      st.endpoints.get
        (Fin.cast
          (congrArg List.length (connectStep_endpoints mate ok st))
          endpoint) := by
  let oldEndpoint :=
    Fin.cast (congrArg List.length (connectStep_endpoints mate ok st))
      endpoint
  let i := endpoint.val
  have hchildSome :
      (connectStep mate ok st).endpoints[i]? =
        some ((connectStep mate ok st).endpoints.get endpoint) :=
    by simp [i]
  have holdSome :
      (connectStep mate ok st).endpoints[i]? =
        some (st.endpoints.get oldEndpoint) := by
    rw [connectStep_endpoints mate ok st]
    exact List.getElem?_eq_getElem oldEndpoint.isLt
  rw [hchildSome] at holdSome
  injection holdSome with hget

theorem connectStep_nodes_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (node : Fin (connectStep mate ok st).nodes.length) :
    (connectStep mate ok st).nodes.get node =
      st.nodes.get
        (Fin.cast
          (congrArg List.length (connectStep_nodes mate ok st))
          node) := by
  let oldNode :=
    Fin.cast (congrArg List.length (connectStep_nodes mate ok st))
      node
  let i := node.val
  have hchildSome :
      (connectStep mate ok st).nodes[i]? =
        some ((connectStep mate ok st).nodes.get node) :=
    by simp [i]
  have holdSome :
      (connectStep mate ok st).nodes[i]? =
        some (st.nodes.get oldNode) := by
    rw [connectStep_nodes mate ok st]
    exact List.getElem?_eq_getElem oldNode.isLt
  rw [hchildSome] at holdSome
  injection holdSome with hget

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
