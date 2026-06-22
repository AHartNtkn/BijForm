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
        restIds.get (listIndexCast restIds (by
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
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
          (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
            (by simp [freshNodeEndpoints]) entry)
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

/-- Endpoint lists grow by append through a completed render trace. -/
def renderTrace_endpointsAppend :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      AppendStep.Witness st.endpoints (renderTrace d st).endpoints
  | [], finish, st => by
      exact { suffix := [], step := ⟨by simp [renderTrace]⟩ }
  | _active :: _frontier, connect mate ok child, st => by
      let stepAppend := connectStep_endpointsAppend mate ok st
      let traceAppend :=
        renderTrace_endpointsAppend child (connectStep mate ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_connect] using fullAppend.step }
  | _active :: _frontier, bud node entry ok child, st => by
      let stepAppend := budStep_endpointsAppend node entry ok st
      let traceAppend :=
        renderTrace_endpointsAppend child (budStep node entry ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_bud] using fullAppend.step }

/--
Edges already in a render state remain an ordered prefix of the completed
render trace.  The recursive bridge uses this stronger prefix fact, not just
membership, to identify processed edge indices after a render prefix.
-/
def renderTrace_edgesAppend :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      AppendStep.Witness st.edges (renderTrace d st).edges
  | [], finish, st => by
      exact { suffix := [], step := ⟨by simp [renderTrace]⟩ }
  | _active :: _frontier, connect mate ok child, st => by
      let stepAppend := connectStep_edgesAppend mate ok st
      let traceAppend :=
        renderTrace_edgesAppend child (connectStep mate ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_connect] using fullAppend.step }
  | _active :: _frontier, bud node entry ok child, st => by
      let stepAppend := budStep_edgesAppend node entry ok st
      let traceAppend :=
        renderTrace_edgesAppend child (budStep node entry ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_bud] using fullAppend.step }

/-- The first edge index allocated by a top-level rendered `connect`. -/
def renderTrace_connect_new_edgeIndex
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    Fin (renderTrace (Diag.connect mate ok child) st).edges.length := by
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
  let traceAppend :=
    renderTrace_edgesAppend child (connectStep mate ok st)
  have hstep : AppendStep st.edges (connectStep mate ok st).edges [edge] :=
    ⟨by simpa [edge, mateId] using connectStep_edges mate ok st hids⟩
  exact AppendStep.firstSuffixIndex hstep traceAppend.step

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
    final.edges.get
      (renderTrace_connect_new_edgeIndex mate ok child st hids) = edge := by
  intro final mateId edge
  let traceAppend :=
    renderTrace_edgesAppend child (connectStep mate ok st)
  have hstep :
      AppendStep st.edges (connectStep mate ok st).edges [edge] :=
    ⟨by simpa [edge, mateId] using connectStep_edges mate ok st hids⟩
  have htrace :
      AppendStep (connectStep mate ok st).edges final.edges
        traceAppend.suffix :=
    ⟨by
      dsimp [final]
      rw [renderTrace_connect]
      exact traceAppend.step.eq_append⟩
  simpa [renderTrace_connect_new_edgeIndex, mateId, edge] using
    AppendStep.get_firstSuffixIndex hstep htrace

/-- The first edge index allocated by a top-level rendered `bud`. -/
def renderTrace_bud_new_edgeIndex
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    Fin (renderTrace (Diag.bud node entry ok child) st).edges.length := by
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
  let traceAppend :=
    renderTrace_edgesAppend child (budStep node entry ok st)
  have hstep : AppendStep st.edges (budStep node entry ok st).edges [edge] :=
    ⟨by
      simpa [edge, nodeEndpoints, entryIdx] using
        budStep_edges node entry ok st hids⟩
  exact AppendStep.firstSuffixIndex hstep traceAppend.step

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
    final.edges.get
      (renderTrace_bud_new_edgeIndex node entry ok child st hids) = edge := by
  intro final nodeEndpoints entryIdx edge
  let traceAppend :=
    renderTrace_edgesAppend child (budStep node entry ok st)
  have hstep :
      AppendStep st.edges (budStep node entry ok st).edges [edge] :=
    ⟨by
      simpa [edge, nodeEndpoints, entryIdx] using
        budStep_edges node entry ok st hids⟩
  have htrace :
      AppendStep (budStep node entry ok st).edges final.edges
        traceAppend.suffix :=
    ⟨by
      dsimp [final]
      rw [renderTrace_bud]
      exact traceAppend.step.eq_append⟩
  simpa [renderTrace_bud_new_edgeIndex, nodeEndpoints, entryIdx, edge] using
    AppendStep.get_firstSuffixIndex hstep htrace

/--
Constructor nodes already in a render state remain an ordered prefix of the
completed render trace.  The recursive bridge uses this to identify seen-node
indices after a render prefix.
-/
def renderTrace_nodesAppend :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      AppendStep.Witness st.nodes (renderTrace d st).nodes
  | [], finish, st => by
      exact { suffix := [], step := ⟨by simp [renderTrace]⟩ }
  | _active :: _frontier, connect mate ok child, st => by
      let stepAppend := connectStep_nodesAppend mate ok st
      let traceAppend :=
        renderTrace_nodesAppend child (connectStep mate ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_connect] using fullAppend.step }
  | _active :: _frontier, bud node entry ok child, st => by
      let stepAppend := budStep_nodesAppend node entry ok st
      let traceAppend :=
        renderTrace_nodesAppend child (budStep node entry ok st)
      let fullAppend := stepAppend.trans traceAppend
      exact
        { suffix := fullAppend.suffix
          step := by
            simpa [renderTrace_bud] using fullAppend.step }

/-- The first node index allocated by a top-level rendered `bud`. -/
def renderTrace_bud_new_nodeIndex
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    Fin (renderTrace (Diag.bud node entry ok child) st).nodes.length := by
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  let traceAppend :=
    renderTrace_nodesAppend child (budStep node entry ok st)
  have hstep : AppendStep st.nodes (budStep node entry ok st).nodes [renderNode] :=
    ⟨by
      simpa [renderNode, nodeEndpoints] using
        budStep_nodes node entry ok st⟩
  exact AppendStep.firstSuffixIndex hstep traceAppend.step

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
    final.nodes.get
      (renderTrace_bud_new_nodeIndex node entry ok child st) = renderNode := by
  intro final nodeEndpoints renderNode
  let traceAppend :=
    renderTrace_nodesAppend child (budStep node entry ok st)
  have hstep :
      AppendStep st.nodes (budStep node entry ok st).nodes [renderNode] :=
    ⟨by
      simpa [renderNode, nodeEndpoints] using
        budStep_nodes node entry ok st⟩
  have htrace :
      AppendStep (budStep node entry ok st).nodes final.nodes
        traceAppend.suffix :=
    ⟨by
      dsimp [final]
      rw [renderTrace_bud]
      exact traceAppend.step.eq_append⟩
  simpa [renderTrace_bud_new_nodeIndex, nodeEndpoints, renderNode] using
    AppendStep.get_firstSuffixIndex hstep htrace

def renderTrace_endpointPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      RenderState.EndpointPrefix (renderTrace d st) st.endpoints
  | _, d, st =>
      let append := renderTrace_endpointsAppend d st
      { suffix := append.suffix
        endpoints_eq := append.step.eq_append }

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
