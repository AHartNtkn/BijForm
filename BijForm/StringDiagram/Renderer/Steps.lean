import BijForm.StringDiagram.Renderer.Core

namespace BijForm
namespace StringDiagram

open DepPoly

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

theorem freshNodeEndpoints_get_sub_of_eq {start base arity : Nat}
    (hstart : start = base)
    (i : Fin (freshNodeEndpoints start arity).length) :
    (freshNodeEndpoints start arity).get i - base = i.val := by
  rw [← hstart, freshNodeEndpoints_get]
  omega

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

theorem oldEndpoint_lt_budEndpoints
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (node : Sig.Node) {id : Nat}
    (hbound : id < st.endpoints.length) :
    id < (st.endpoints ++ Sig.nodePorts node).length := by
  simp [Signature.nodePorts]
  omega

theorem oldEndpoint_get_budEndpoints
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (node : Sig.Node) {id : Nat}
    (hbound : id < st.endpoints.length)
    (hbud : id < (st.endpoints ++ Sig.nodePorts node).length) :
    (st.endpoints ++ Sig.nodePorts node).get ⟨id, hbud⟩ =
      st.endpoints.get ⟨id, hbound⟩ :=
  list_get_append_left st.endpoints (Sig.nodePorts node) hbound hbud

theorem freshNodeEndpoint_lt_budEndpoints
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (hv : st.ValidIds) (node : Sig.Node) {id : Nat}
    (hmem : id ∈ freshNodeEndpoints st.nextEndpoint (Sig.arity node)) :
    id < (st.endpoints ++ Sig.nodePorts node).length := by
  have hlt := freshNodeEndpoints_mem_lt hmem
  have hnext := hv.nextEndpoint_eq
  simp [Signature.nodePorts] at hlt ⊢
  omega

theorem oldEndpoint_not_mem_freshNodeEndpoints
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (hv : st.ValidIds) {arity id : Nat}
    (hbound : id < st.endpoints.length)
    (hfresh : id ∈ freshNodeEndpoints st.nextEndpoint arity) :
    False := by
  have hge := freshNodeEndpoints_mem_ge hfresh
  have hnext := hv.nextEndpoint_eq
  omega

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
  exact fin_eq_of_val_eq (by omega)

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
        (listIndexCast (Sig.nodePorts node)
          (by simp [freshNodeEndpoints, Signature.nodePorts]) i) := by
  let endpoint : Fin (st.endpoints ++ Sig.nodePorts node).length :=
    ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i, hbound⟩
  let nodePort : Fin (Sig.nodePorts node).length :=
    listIndexCast (Sig.nodePorts node)
      (by simp [freshNodeEndpoints, Signature.nodePorts]) i
  have hright :
      st.endpoints.length ≤ endpoint.val := by
    have hget :=
      freshNodeEndpoints_get st.nextEndpoint (Sig.arity node) i
    change st.endpoints.length ≤
      (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i
    rw [hget]
    have hnext := hv.nextEndpoint_eq
    omega
  have hval : endpoint.val - st.endpoints.length = nodePort.val := by
    have hget :=
      freshNodeEndpoints_get st.nextEndpoint (Sig.arity node) i
    change
      (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i -
        st.endpoints.length = nodePort.val
    rw [hget]
    have hnext := hv.nextEndpoint_eq
    simp [nodePort]
    omega
  exact list_get_of_eq_append_right_of_val_eq rfl endpoint nodePort
    hright hval

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
        exact RenderState.frontierIds_cons_tail_length st hids
      let mateId := restIds.get (listIndexCast restIds hrest.symm mate)
      let childIds := eraseFin restIds (listIndexCast restIds hrest.symm mate)
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
        exact RenderState.frontierIds_cons_tail_length st hids
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let entryId := nodeEndpoints.get
        (listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry)
      let childIds := restIds ++
        eraseFin nodeEndpoints (listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry)
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

/-- Declarative append/frontier effect of a single renderer step. -/
structure RenderDelta {source target : List Sig.Port}
    (st : RenderState Sig source) (child : RenderState Sig target)
    (endpointSuffix : List Sig.Port)
    (edgeSuffix : List (RenderEdge Sig))
    (nodeSuffix : List (RenderNode Sig))
    (frontierIds : List Nat) : Prop where
  endpoints : AppendStep st.endpoints child.endpoints endpointSuffix
  edges : AppendStep st.edges child.edges edgeSuffix
  nodes : AppendStep st.nodes child.nodes nodeSuffix
  nextEndpoint_eq : child.nextEndpoint = st.nextEndpoint + endpointSuffix.length
  frontierIds_eq : child.frontierIds = frontierIds

/-- `connectStep` exposes its append effects through `RenderDelta`. -/
theorem connectStep_delta
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let idx : Fin restIds.length :=
      listIndexCast restIds (by
        exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
    let edge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right := restIds.get idx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    RenderDelta st (connectStep mate ok st) [] [edge] []
      (eraseFin restIds idx) := by
  unfold connectStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    refine
      { endpoints := ?_
        edges := ?_
        nodes := ?_
        nextEndpoint_eq := ?_
        frontierIds_eq := ?_ }
    · exact ⟨by simp⟩
    · exact ⟨by simp [listIndexCast]⟩
    · exact ⟨by simp⟩
    · simp
    · simp [listIndexCast]

/-- `budStep` exposes its append effects through `RenderDelta`. -/
theorem budStep_delta
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
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
    RenderDelta st (budStep node entry ok st) (Sig.nodePorts node) [edge]
      [renderNode] (restIds ++ eraseFin nodeEndpoints entryIdx) := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    refine
      { endpoints := ?_
        edges := ?_
        nodes := ?_
        nextEndpoint_eq := ?_
        frontierIds_eq := ?_ }
    · exact ⟨by simp⟩
    · exact ⟨by simp [freshNodeEndpoints, listIndexCast]⟩
    · exact ⟨by simp [freshNodeEndpoints]⟩
    · simp [Signature.nodePorts]
    · simp [freshNodeEndpoints, listIndexCast]

theorem connectStep_edge_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {edge : RenderEdge Sig}
    (hmem : edge ∈ st.edges) :
    edge ∈ (connectStep mate ok st).edges := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      exact (connectStep_delta mate ok st hids).edges.mem_prefix hmem

theorem connectStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ st.nodes) :
    node ∈ (connectStep mate ok st).nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      exact (connectStep_delta mate ok st hids).nodes.mem_prefix hmem

theorem connectStep_node_mem_old_of_child
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ (connectStep mate ok st).nodes) :
    node ∈ st.nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      rcases (connectStep_delta mate ok st hids).nodes.mem_cases hmem with
        hold | hnew
      · exact hold
      · cases hnew

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
        restIds.get (listIndexCast restIds (by
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (connectStep mate ok st).edges := by
  let idx : Fin restIds.length :=
    listIndexCast restIds (by
      exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := restIds.get idx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hdelta := connectStep_delta mate ok st hids
  simpa [idx, edge] using hdelta.edges.mem_single

theorem connectStep_edges
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (connectStep mate ok st).edges =
      st.edges ++
        [{ label := Sig.portEdge active
           leftLabel := active
           rightLabel := frontier.get mate
           left := activeId
           right :=
            restIds.get (listIndexCast restIds (by
              exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
           left_label := rfl
           right_label := (Sig.compatible_edge ok).symm
           compatible := ok }] := by
  let idx : Fin restIds.length :=
    listIndexCast restIds (by
      exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := restIds.get idx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hdelta := connectStep_delta mate ok st hids
  simpa [idx, edge] using hdelta.edges.eq_append

theorem connectStep_edges_get_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (edge : Fin (connectStep mate ok st).edges.length)
    (hold : edge.val < st.edges.length) :
    (connectStep mate ok st).edges.get edge =
      st.edges.get ⟨edge.val, hold⟩ := by
  exact list_get_of_eq_append_left
    (connectStep_edges mate ok st hids) edge hold

theorem connectStep_edges_get_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (edge : Fin (connectStep mate ok st).edges.length)
    (hnew : edge.val = st.edges.length) :
    (connectStep mate ok st).edges.get edge =
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right :=
          restIds.get (listIndexCast restIds (by
            exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok } := by
  let idx : Fin restIds.length :=
    listIndexCast restIds (by
      exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
  let newEdge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := restIds.get idx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hdelta := connectStep_delta mate ok st hids
  simpa [idx, newEdge] using hdelta.edges.get_single_at_length edge hnew

theorem connectStep_frontierIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (connectStep mate ok st).frontierIds =
      eraseFin restIds (listIndexCast restIds (by
        exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate) := by
  let idx : Fin restIds.length :=
    listIndexCast restIds (by
      exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
  have hdelta := connectStep_delta mate ok st hids
  simpa [idx] using hdelta.frontierIds_eq

theorem connectStep_frontier_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {id : Nat}
    (hmem : id ∈ (connectStep mate ok st).frontierIds) :
    id ∈ st.frontierIds := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    let idx : Fin restIds.length :=
      listIndexCast restIds (by
        exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
    have hdelta := connectStep_delta mate ok st hids
    have hmemErase : id ∈ eraseFin restIds idx := by
      rw [hdelta.frontierIds_eq] at hmem
      simpa [idx] using hmem
    right
    exact mem_of_mem_eraseFin restIds idx hmemErase

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
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      exact (budStep_delta node entry ok st hids).edges.mem_prefix hmem

theorem budStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {renderNode : RenderNode Sig}
    (hmem : renderNode ∈ st.nodes) :
    renderNode ∈ (budStep node entry ok st).nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      exact (budStep_delta node entry ok st hids).nodes.mem_prefix hmem

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
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let newNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      have hdelta := budStep_delta node entry ok st hids
      rcases hdelta.nodes.mem_cases hmem with hold | hnew
      · exact Or.inl hold
      · right
        simpa [nodeEndpoints, newNode] using hnew

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
          (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
            (by simp [freshNodeEndpoints]) entry) := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
    have hdelta := budStep_delta node entry ok st hids
    have hmemFull : id ∈ restIds ++ eraseFin nodeEndpoints entryIdx := by
      rw [hdelta.frontierIds_eq] at hmem
      simpa [nodeEndpoints, entryIdx] using hmem
    rcases List.mem_append.mp hmemFull with hold | hnew
    · left
      simp [hold]
    · right
      simpa [nodeEndpoints, entryIdx] using hnew

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
          (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
            (by simp [freshNodeEndpoints]) entry)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (budStep node entry ok st).edges := by
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
  have hdelta := budStep_delta node entry ok st hids
  simpa [nodeEndpoints, entryIdx, edge] using hdelta.edges.mem_single

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
          (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
            (by simp [freshNodeEndpoints]) entry) := by
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
  have hdelta := budStep_delta node entry ok st hids
  simpa [nodeEndpoints, entryIdx] using hdelta.frontierIds_eq

def connectStep_edgesAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.edges (connectStep mate ok st).edges := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let idx : Fin restIds.length :=
        listIndexCast restIds (by
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
      let edge : RenderEdge Sig :=
        { label := Sig.portEdge active
          leftLabel := active
          rightLabel := frontier.get mate
          left := activeId
          right := restIds.get idx
          left_label := rfl
          right_label := (Sig.compatible_edge ok).symm
          compatible := ok }
      refine { suffix := [edge], step := ?_ }
      have hdelta := connectStep_delta mate ok st hids
      exact ⟨by simpa [idx, edge] using hdelta.edges.eq_append⟩

def budStep_edgesAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.edges (budStep node entry ok st).edges := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
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
      refine { suffix := [edge], step := ?_ }
      have hdelta := budStep_delta node entry ok st hids
      exact ⟨by
        simpa [nodeEndpoints, entryIdx, edge] using hdelta.edges.eq_append⟩

def connectStep_nodesAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.nodes (connectStep mate ok st).nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      refine { suffix := [], step := ?_ }
      have hdelta := connectStep_delta mate ok st hids
      exact ⟨by simpa using hdelta.nodes.eq_append⟩

def budStep_nodesAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.nodes (budStep node entry ok st).nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let renderNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      refine { suffix := [renderNode], step := ?_ }
      have hdelta := budStep_delta node entry ok st hids
      exact ⟨by simpa [nodeEndpoints, renderNode] using
        hdelta.nodes.eq_append⟩

theorem budStep_edges
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (budStep node entry ok st).edges =
      st.edges ++
        [{ label := Sig.portEdge active
           leftLabel := active
           rightLabel := Sig.port node entry
           left := activeId
           right :=
            (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
              (listIndexCast
                (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
                (by simp [freshNodeEndpoints]) entry)
           left_label := rfl
           right_label := (Sig.compatible_edge ok).symm
           compatible := ok }] := by
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
  have hdelta := budStep_delta node entry ok st hids
  simpa [nodeEndpoints, entryIdx, edge, listIndexCast] using
    hdelta.edges.eq_append

theorem budStep_nodes
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).nodes =
      st.nodes ++
        [{ label := node
           incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) }] := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let renderNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      have hdelta := budStep_delta node entry ok st hids
      simpa [nodeEndpoints, renderNode] using hdelta.nodes.eq_append

theorem connectStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).edges.length = st.edges.length + 1 := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let idx : Fin restIds.length :=
        listIndexCast restIds (by
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate
      let edge : RenderEdge Sig :=
        { label := Sig.portEdge active
          leftLabel := active
          rightLabel := frontier.get mate
          left := activeId
          right := restIds.get idx
          left_label := rfl
          right_label := (Sig.compatible_edge ok).symm
          compatible := ok }
      have hdelta := connectStep_delta mate ok st hids
      simpa [idx, edge] using hdelta.edges.length

theorem connectStep_nodes
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).nodes = st.nodes := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      have hdelta := connectStep_delta mate ok st hids
      simpa using hdelta.nodes.eq_append

theorem connectStep_endpoints
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).endpoints = st.endpoints := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons _activeId _restIds =>
      have hdelta := connectStep_delta mate ok st hids
      simpa using hdelta.endpoints.eq_append

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
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      have hdelta := budStep_delta node entry ok st hids
      simpa using hdelta.endpoints.eq_append

def connectStep_endpointsAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.endpoints (connectStep mate ok st).endpoints where
  suffix := []
  step := ⟨by simp [connectStep_endpoints mate ok st]⟩

def budStep_endpointsAppend
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    AppendStep.Witness st.endpoints (budStep node entry ok st).endpoints where
  suffix := Sig.nodePorts node
  step := ⟨by rw [budStep_endpoints node entry ok st]⟩

theorem budStep_edgeEndpointIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (budStep node entry ok st).edgeEndpointIds =
      st.edgeEndpointIds ++
        [activeId,
          (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
            (listIndexCast
              (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
              (by simp [freshNodeEndpoints]) entry)] := by
  simp [RenderState.edgeEndpointIds, budStep_edges node entry ok st hids,
    listIndexCast]

theorem budStep_ownerEndpointIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (boundary : List Sig.Port) :
    (budStep node entry ok st).ownerEndpointIds boundary =
      st.ownerEndpointIds boundary ++
        freshNodeEndpoints st.nextEndpoint (Sig.arity node) := by
  simp [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds,
    budStep_nodes node entry ok st]

def connectStep_endpointPrefix
    {active : Sig.Port} {frontier boundary : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (pref : st.EndpointPrefix boundary) :
    (connectStep mate ok st).EndpointPrefix boundary :=
  pref.trans
    { suffix := (connectStep_endpointsAppend mate ok st).suffix
      endpoints_eq := (connectStep_endpointsAppend mate ok st).step.eq_append }

def budStep_endpointPrefix
    {active : Sig.Port} {frontier boundary : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (pref : st.EndpointPrefix boundary) :
    (budStep node entry ok st).EndpointPrefix boundary :=
  pref.trans
    { suffix := (budStep_endpointsAppend node entry ok st).suffix
      endpoints_eq :=
        (budStep_endpointsAppend node entry ok st).step.eq_append }

theorem budStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).edges.length = st.edges.length + 1 := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
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
      have hdelta := budStep_delta node entry ok st hids
      simpa [nodeEndpoints, entryIdx, edge] using hdelta.edges.length

theorem budStep_nodes_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).nodes.length = st.nodes.length + 1 := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let renderNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      have hdelta := budStep_delta node entry ok st hids
      simpa [nodeEndpoints, renderNode] using hdelta.nodes.length

theorem budStep_endpoints_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).endpoints.length =
      st.endpoints.length + Sig.arity node := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      have hdelta := budStep_delta node entry ok st hids
      simpa [Signature.nodePorts] using hdelta.endpoints.length

theorem budStep_edges_get_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (edge : Fin (budStep node entry ok rst).edges.length)
    (hold : edge.val < rst.edges.length) :
    (budStep node entry ok rst).edges.get edge =
      rst.edges.get ⟨edge.val, hold⟩ := by
  exact list_get_of_eq_append_left
    (budStep_edges node entry ok rst hids) edge hold

theorem budStep_edges_get_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds)
    (edge : Fin (budStep node entry ok rst).edges.length)
    (hnew : edge.val = rst.edges.length) :
    (budStep node entry ok rst).edges.get edge =
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := Sig.port node entry
        left := activeId
        right :=
          (freshNodeEndpoints rst.nextEndpoint (Sig.arity node)).get
            (listIndexCast
              (freshNodeEndpoints rst.nextEndpoint (Sig.arity node))
              (by simp [freshNodeEndpoints]) entry)
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok } := by
  let nodeEndpoints := freshNodeEndpoints rst.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
  let newEdge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hdelta := budStep_delta node entry ok rst hids
  simpa [nodeEndpoints, entryIdx, newEdge, listIndexCast] using
    hdelta.edges.get_single_at_length edge hnew

theorem budStep_nodes_get_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    (renderNode : Fin (budStep node entry ok rst).nodes.length)
    (hold : renderNode.val < rst.nodes.length) :
    (budStep node entry ok rst).nodes.get renderNode =
      rst.nodes.get ⟨renderNode.val, hold⟩ := by
  exact list_get_of_eq_append_left
    (budStep_nodes node entry ok rst) renderNode hold

theorem budStep_nodes_get_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    (renderNode : Fin (budStep node entry ok rst).nodes.length)
    (hnew : renderNode.val = rst.nodes.length) :
    (budStep node entry ok rst).nodes.get renderNode =
      { label := node
        incident := freshNodeEndpoints rst.nextEndpoint (Sig.arity node) } := by
  cases hids : rst.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil rst hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints rst.nextEndpoint (Sig.arity node)
      let newNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      have hdelta := budStep_delta node entry ok rst hids
      simpa [nodeEndpoints, newNode] using
        hdelta.nodes.get_single_at_length renderNode hnew

theorem budStep_endpoints_get_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    (endpoint : Fin (budStep node entry ok rst).endpoints.length)
    (hold : endpoint.val < rst.endpoints.length) :
    (budStep node entry ok rst).endpoints.get endpoint =
      rst.endpoints.get ⟨endpoint.val, hold⟩ := by
  exact list_get_of_eq_append_left
    (budStep_endpoints node entry ok rst) endpoint hold

theorem budStep_endpoints_get_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (rst : RenderState Sig (active :: frontier))
    (endpoint : Fin (budStep node entry ok rst).endpoints.length)
    (hnew : rst.endpoints.length ≤ endpoint.val) :
    (budStep node entry ok rst).endpoints.get endpoint =
      (Sig.nodePorts node).get
        ⟨endpoint.val - rst.endpoints.length, by
          have hb :
              endpoint.val < rst.endpoints.length + Sig.arity node := by
            exact Nat.lt_of_lt_of_eq endpoint.isLt
              (budStep_endpoints_length node entry ok rst)
          simp [Signature.nodePorts]
          omega⟩ := by
  let i := endpoint.val
  have hiBound : i < rst.endpoints.length + Sig.arity node := by
    have hendpoint : i < (budStep node entry ok rst).endpoints.length := by
      dsimp [i]
      exact endpoint.isLt
    exact Nat.lt_of_lt_of_eq hendpoint
      (budStep_endpoints_length node entry ok rst)
  have hslotBound : i - rst.endpoints.length < (Sig.nodePorts node).length := by
    simpa [Signature.nodePorts] using
      (by omega : i - rst.endpoints.length < Sig.arity node)
  have hget :=
    list_get_of_eq_append_right
      (budStep_endpoints node entry ok rst)
      endpoint
      (by simpa [i] using hnew)
  simpa [i, hslotBound] using hget

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
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let renderNode : RenderNode Sig :=
        { label := node
          incident := nodeEndpoints }
      have hdelta := budStep_delta node entry ok st hids
      simpa [nodeEndpoints, renderNode] using hdelta.nodes.mem_single

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
        (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
          (by simp [freshNodeEndpoints]) entry)) := by
  let entryIdx : Fin (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).length :=
    listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
      (by simp [freshNodeEndpoints]) entry
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
    listIndexCast nodeEndpoints (by simp [nodeEndpoints, freshNodeEndpoints]) entry
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
              (listIndexCast (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
                (by simp [freshNodeEndpoints]) entry)
              hnew)
      · intro renderNode hmem
        rcases budStep_node_mem_old_or_new node entry ok st hmem with
          hold | hnew
        · rcases hr.node_reaches renderNode hold with ⟨slot, reach⟩
          exact ⟨slot, budStep_rawReachesBoundary_of_old node entry ok st reach⟩
        · subst renderNode
          let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
          let entryIdx : Fin nodeEndpoints.length :=
            listIndexCast nodeEndpoints (by simp [nodeEndpoints, freshNodeEndpoints]) entry
          refine ⟨entryIdx, ?_⟩
          dsimp [nodeEndpoints, entryIdx]
          exact budStep_entry_rawReachesBoundary node entry ok st hr hids

theorem connectStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (connectStep mate ok st).ValidIds := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    have hrest : restIds.length = frontier.length := by
      exact RenderState.frontierIds_cons_tail_length st hids
    let idx : Fin restIds.length := listIndexCast restIds hrest.symm mate
    have hdelta := connectStep_delta mate ok st hids
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
    · calc
        (connectStep mate ok st).nextEndpoint = st.nextEndpoint := by
          simpa using hdelta.nextEndpoint_eq
        _ = st.endpoints.length := hv.nextEndpoint_eq
        _ = (connectStep mate ok st).endpoints.length := by
          rw [connectStep_endpoints mate ok st]
    · intro id hid
      have hbound := hv.frontier_bound id
        (connectStep_frontier_mem_old mate ok st hid)
      simpa [connectStep_endpoints mate ok st] using hbound
    · intro n hid hfrontier
      have hfrontierIdsEq := connectStep_frontierIds mate ok st hids
      have hidErase : n < (eraseFin restIds idx).length := by
        exact Nat.lt_of_lt_of_eq hid
          (congrArg List.length hfrontierIdsEq)
      have hgetId :
          (connectStep mate ok st).frontierIds.get ⟨n, hid⟩ =
            (eraseFin restIds idx).get ⟨n, hidErase⟩ := by
        exact list_get_of_eq_of_val_eq hfrontierIdsEq
          ⟨n, hid⟩ ⟨n, hidErase⟩ rfl
      have hrel :
          IndexedListRel
            (fun id label =>
              ∃ hbound : id < st.endpoints.length,
                st.endpoints.get ⟨id, hbound⟩ = label)
            restIds frontier := by
        refine { length := hrest, get := ?_ }
        intro n hx hy
        have hlabel :=
          hv.frontier_tail_label hids hrest ⟨n, hx⟩
        refine ⟨hv.frontier_bound (restIds.get ⟨n, hx⟩) ?_, ?_⟩
        · rw [hids]
          right
          exact List.get_mem restIds ⟨n, hx⟩
        · simpa using hlabel
      have haligned := (hrel.erase idx mate (by simp [idx])).get
        n hidErase hfrontier
      rcases haligned with ⟨hbound, hlabel⟩
      have hchildBound :
          (connectStep mate ok st).frontierIds.get ⟨n, hid⟩ <
            (connectStep mate ok st).endpoints.length := by
        rw [hgetId]
        exact Nat.lt_of_lt_of_eq hbound
          (congrArg List.length (connectStep_endpoints mate ok st)).symm
      change
        (connectStep mate ok st).endpoints.get
            ⟨(connectStep mate ok st).frontierIds.get ⟨n, hid⟩,
              hchildBound⟩ =
          (eraseFin frontier mate).get ⟨n, hfrontier⟩
      exact
        (list_get_of_eq_of_val_eq
          (connectStep_endpoints mate ok st)
          ⟨(connectStep mate ok st).frontierIds.get ⟨n, hid⟩,
            hchildBound⟩
          ⟨(eraseFin restIds idx).get ⟨n, hidErase⟩, hbound⟩
          (by simpa using hgetId)).trans hlabel
    · intro edge hmem
      simp [connectStep_edges mate ok st hids] at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_left_bound edge hold
        simpa [connectStep_endpoints mate ok st] using hbound
      · cases hnew
        have hbound := hv.frontier_bound activeId (by simp [hids])
        simpa [connectStep_endpoints mate ok st] using hbound
    · intro edge hmem
      simp [connectStep_edges mate ok st hids] at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_right_bound edge hold
        simpa [connectStep_endpoints mate ok st] using hbound
      · cases hnew
        have hbound := hv.frontier_bound (restIds.get idx) (by
          rw [hids]
          right
          exact List.get_mem restIds idx)
        simpa [connectStep_endpoints mate ok st] using hbound
    · intro edge hmem
      simp [connectStep_edges mate ok st hids] at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_left_label edge hold
        simpa [connectStep_endpoints mate ok st] using hlabel
      · cases hnew
        have hlabel := hv.frontier_head_label hids
        simpa [connectStep_endpoints mate ok st] using hlabel
    · intro edge hmem
      simp [connectStep_edges mate ok st hids] at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_right_label edge hold
        simpa [connectStep_endpoints mate ok st] using hlabel
      · cases hnew
        have hlabel := hv.frontier_tail_label hids hrest idx
        simpa [idx, connectStep_endpoints mate ok st] using hlabel
    · intro node hmem
      exact hv.node_incident_length node
        (connectStep_node_mem_old_of_child mate ok st hmem)
    · intro node hmem slot
      have hold := connectStep_node_mem_old_of_child mate ok st hmem
      have hbound := hv.node_incident_bound node hold slot
      simpa [connectStep_endpoints mate ok st] using hbound
    · intro node hmem slot
      have hold := connectStep_node_mem_old_of_child mate ok st hmem
      have hlabel := hv.node_incident_label node hold slot
      simpa [connectStep_endpoints mate ok st] using hlabel

theorem connectStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (connectStep mate ok st).EndpointPartition := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    have hrest : restIds.length = frontier.length := by
      exact RenderState.frontierIds_cons_tail_length st hids
    let idx : Fin restIds.length := listIndexCast restIds hrest.symm mate
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
    have childConsumed_eq :
        (connectStep mate ok st).edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, restIds.get idx] := by
      simp [RenderState.edgeEndpointIds, connectStep_edges mate ok st hids, idx]
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · rw [connectStep_frontierIds mate ok st hids]
      exact nodup_eraseFin restIds idx rest_nodup
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
      · have hbound := hp.consumed_bound id hold
        simpa [connectStep_endpoints mate ok st] using hbound
      · rcases hnew with hactive | hmate
        · have hbound := hv.frontier_bound activeId active_old_frontier
          simpa [hactive, connectStep_endpoints mate ok st] using hbound
        · have hbound := hv.frontier_bound (restIds.get idx) mate_old_frontier
          simpa [hmate, connectStep_endpoints mate ok st] using hbound
    · intro id hfrontier hconsumed
      have hfrontierErase : id ∈ eraseFin restIds idx := by
        rw [connectStep_frontierIds mate ok st hids] at hfrontier
        simpa [idx] using hfrontier
      rw [childConsumed_eq] at hconsumed
      simp at hconsumed
      rcases hconsumed with hold | hnew
      · have oldFrontier : id ∈ st.frontierIds := by
          rw [hids]
          right
          exact mem_of_mem_eraseFin restIds idx hfrontierErase
        exact hp.frontier_consumed_disjoint id oldFrontier hold
      · rcases hnew with hactive | hmate
        · have hrestMem : id ∈ restIds :=
            mem_of_mem_eraseFin restIds idx hfrontierErase
          exact active_not_rest (by simpa [hactive] using hrestMem)
        · have hnotMate :
            restIds.get idx ∉ eraseFin restIds idx :=
            get_not_mem_eraseFin_of_nodup restIds idx rest_nodup
          exact hnotMate (by simpa [hmate] using hfrontierErase)
    · intro id hid
      have holdBound : id < st.endpoints.length := by
        simpa [connectStep_endpoints mate ok st] using hid
      rcases hp.endpoint_covered id holdBound with holdFrontier | holdConsumed
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
            rw [connectStep_frontierIds mate ok st hids]
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
  constructor
  intro node hmem
  exact hn.node_incident_nodup node
    (connectStep_node_mem_old_of_child mate ok st hmem)

theorem connectStep_ownerIdPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (connectStep mate ok st).OwnerIdPartition boundary := by
  have hnodes := connectStep_nodes mate ok st
  have hendpoints := connectStep_endpoints mate ok st
  constructor
  · simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds,
      hnodes] using ho.owner_nodup
  · intro id hmem
    have holdMem : id ∈ st.ownerEndpointIds boundary := by
      simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds,
        hnodes] using hmem
    have hbound := ho.owner_bound id holdMem
    simpa [hendpoints] using hbound
  · intro id hid
    have holdBound : id < st.endpoints.length := by
      simpa [hendpoints] using hid
    simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds,
      hnodes] using ho.owner_covered id holdBound

theorem budStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (budStep node entry ok st).ValidIds := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    have hrest : restIds.length = frontier.length := by
      exact RenderState.frontierIds_cons_tail_length st hids
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
    have childFrontierIds_eq :
        (budStep node entry ok st).frontierIds =
          restIds ++ eraseFin nodeEndpoints entryIdx := by
      simpa [nodeEndpoints, entryIdx] using
        budStep_frontierIds node entry ok st hids
    have childEdges_eq :
        (budStep node entry ok st).edges =
          st.edges ++
            [{ label := Sig.portEdge active
               leftLabel := active
               rightLabel := Sig.port node entry
               left := activeId
               right := nodeEndpoints.get entryIdx
               left_label := rfl
               right_label := (Sig.compatible_edge ok).symm
               compatible := ok }] := by
      simpa [nodeEndpoints, entryIdx, listIndexCast] using
        budStep_edges node entry ok st hids
    have childNodes_eq :=
      budStep_nodes node entry ok st
    have childEndpoints_eq :=
      budStep_endpoints node entry ok st
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
        exact freshNodeEndpoint_lt_budEndpoints st hv node
          (by simp [nodeEndpoints])
      refine ⟨hbound, ?_⟩
      have hlabel' :=
        freshNodeEndpoints_label_append st hv node ⟨n, hid⟩ hbound
      simpa [nodeEndpoints] using hlabel'
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      exact oldEndpoint_lt_budEndpoints st node hbound
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      exact freshNodeEndpoint_lt_budEndpoints st hv node
        (by simpa [nodeEndpoints] using hmem)
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
    · have hnext := (budStep_delta node entry ok st hids).nextEndpoint_eq
      simpa [childEndpoints_eq, Signature.nodePorts, hv.nextEndpoint_eq] using
        hnext
    · intro id hid
      rw [childFrontierIds_eq] at hid
      simp at hid
      rcases hid with hold | hnew
      · have holdBound := hv.frontier_bound id (by
          rw [hids]
          right
          exact hold)
        simpa [childEndpoints_eq] using old_bound_lift holdBound
      · have hmem : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hnew
        simpa [childEndpoints_eq] using fresh_bound_of_mem hmem
    · intro n hid hfrontier
      let portEntry : Fin (Sig.nodePorts node).length :=
        listIndexCast (Sig.nodePorts node) (by simp [Signature.nodePorts]) entry
      have hleft :
          IndexedListRel
            (fun id label =>
              ∃ hbound : id < (st.endpoints ++ Sig.nodePorts node).length,
                (st.endpoints ++ Sig.nodePorts node).get
                  ⟨id, hbound⟩ = label)
            restIds frontier := by
        refine { length := hrest, get := ?_ }
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
                exact oldEndpoint_get_budEndpoints st node oldBound
                  (old_bound_lift oldBound)
          _ = frontier.get ⟨n, hlabel⟩ := by
              simpa using oldLabel
      have hrightBase :
          IndexedListRel
            (fun id label =>
              ∃ hbound : id <
                  (st.endpoints ++ Sig.nodePorts node).length,
                (st.endpoints ++ Sig.nodePorts node).get
                    ⟨id, hbound⟩ = label)
            nodeEndpoints (Sig.nodePorts node) := by
        refine { length := by simp [nodeEndpoints, Signature.nodePorts], get := ?_ }
        exact nodeEndpoints_labels
      have hright := hrightBase.erase entryIdx portEntry (by simp [entryIdx, portEntry])
      have hfullRel :=
        hleft.append hright
      have hid' : n < (restIds ++ eraseFin nodeEndpoints entryIdx).length := by
        simpa [childFrontierIds_eq] using hid
      have hgetId :
          (budStep node entry ok st).frontierIds.get ⟨n, hid⟩ =
            (restIds ++ eraseFin nodeEndpoints entryIdx).get ⟨n, hid'⟩ := by
        exact list_get_of_eq_of_val_eq childFrontierIds_eq
          ⟨n, hid⟩ ⟨n, hid'⟩ rfl
      have haligned :=
        hfullRel.get n hid'
          (by
            simpa [Signature.nodePortsExcept, portEntry] using hfrontier)
      rcases haligned with ⟨hbound, hlabelEq⟩
      have hchildBound :
          (budStep node entry ok st).frontierIds.get ⟨n, hid⟩ <
            (budStep node entry ok st).endpoints.length := by
        rw [hgetId]
        exact Nat.lt_of_lt_of_eq hbound
          (congrArg List.length childEndpoints_eq).symm
      change
        (budStep node entry ok st).endpoints.get
            ⟨(budStep node entry ok st).frontierIds.get ⟨n, hid⟩,
              hchildBound⟩ =
          (frontier ++ Sig.nodePortsExcept node entry).get ⟨n, hfrontier⟩
      exact
        (list_get_of_eq_of_val_eq childEndpoints_eq
          ⟨(budStep node entry ok st).frontierIds.get ⟨n, hid⟩,
            hchildBound⟩
          ⟨(restIds ++ eraseFin nodeEndpoints entryIdx).get ⟨n, hid'⟩,
            hbound⟩
          (by simpa using hgetId)).trans
          (by
            simpa [Signature.nodePortsExcept, portEntry] using hlabelEq)
    · intro edge hmem
      simp [childEdges_eq] at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_left_bound edge hold
        simpa [childEndpoints_eq] using old_bound_lift hbound
      · cases hnew
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        simpa [childEndpoints_eq] using old_bound_lift hbound
    · intro edge hmem
      simp [childEdges_eq] at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_right_bound edge hold
        simpa [childEndpoints_eq] using old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints entryIdx
        simpa [childEndpoints_eq] using fresh_bound_of_mem hmem
    · intro edge hmem
      simp [childEdges_eq] at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_left_label edge hold
        have hbound := hv.edge_left_bound edge hold
        have hcalc :
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨edge.left, old_bound_lift hbound⟩ =
              edge.leftLabel := by
          calc
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨edge.left, old_bound_lift hbound⟩ =
                st.endpoints.get ⟨edge.left, hbound⟩ := by
                  exact oldEndpoint_get_budEndpoints st node hbound
                    (old_bound_lift hbound)
            _ = edge.leftLabel := hlabel
        simpa [childEndpoints_eq] using hcalc
      · cases hnew
        have hlabel := hv.frontier_head_label hids
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        have hcalc :
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨activeId, old_bound_lift hbound⟩ =
              active := by
          calc
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨activeId, old_bound_lift hbound⟩ =
                st.endpoints.get ⟨activeId, hbound⟩ := by
                  exact oldEndpoint_get_budEndpoints st node hbound
                    (old_bound_lift hbound)
            _ = active := hlabel
        simpa [childEndpoints_eq] using hcalc
    · intro edge hmem
      simp [childEdges_eq] at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_right_label edge hold
        have hbound := hv.edge_right_bound edge hold
        have hcalc :
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨edge.right, old_bound_lift hbound⟩ =
              edge.rightLabel := by
          calc
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨edge.right, old_bound_lift hbound⟩ =
                st.endpoints.get ⟨edge.right, hbound⟩ := by
                  exact oldEndpoint_get_budEndpoints st node hbound
                    (old_bound_lift hbound)
            _ = edge.rightLabel := hlabel
        simpa [childEndpoints_eq] using hcalc
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node entryIdx
            (fresh_bound_of_mem (List.get_mem nodeEndpoints entryIdx))
        simpa [childEndpoints_eq, nodeEndpoints, entryIdx, Signature.nodePorts] using
          hlabel
    · intro renderNode hmem
      simp [childNodes_eq] at hmem
      rcases hmem with hold | hnew
      · exact hv.node_incident_length renderNode hold
      · cases hnew
        simp
    · intro renderNode hmem slot
      simp [childNodes_eq] at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.node_incident_bound renderNode hold slot
        simpa [childEndpoints_eq] using old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get slot ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints slot
        simpa [childEndpoints_eq] using fresh_bound_of_mem hmem
    · intro renderNode hmem slot
      simp [childNodes_eq] at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.node_incident_label renderNode hold slot
        have hbound := hv.node_incident_bound renderNode hold slot
        have hcalc :
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨renderNode.incident.get slot, old_bound_lift hbound⟩ =
              Sig.port renderNode.label
                (Fin.cast (hv.node_incident_length renderNode hold) slot) := by
          calc
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨renderNode.incident.get slot, old_bound_lift hbound⟩ =
                st.endpoints.get
                  ⟨renderNode.incident.get slot, hbound⟩ := by
                  exact oldEndpoint_get_budEndpoints st node hbound
                    (old_bound_lift hbound)
            _ =
                Sig.port renderNode.label
                  (Fin.cast (hv.node_incident_length renderNode hold) slot) :=
                  hlabel
        simpa [childEndpoints_eq] using hcalc
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node slot
            (fresh_bound_of_mem (List.get_mem nodeEndpoints slot))
        simpa [childEndpoints_eq, nodeEndpoints, Signature.nodePorts] using hlabel

theorem budStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (budStep node entry ok st).EndpointPartition := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
    have hrest : restIds.length = frontier.length := by
      exact RenderState.frontierIds_cons_tail_length st hids
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      listIndexCast nodeEndpoints (by simp [nodeEndpoints]) entry
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
    have childFrontierIds_eq :
        (budStep node entry ok st).frontierIds =
          restIds ++ eraseFin nodeEndpoints entryIdx := by
      simpa [nodeEndpoints, entryIdx] using
        budStep_frontierIds node entry ok st hids
    have childConsumed_eq :
        (budStep node entry ok st).edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, nodeEndpoints.get entryIdx] := by
      simpa [nodeEndpoints, entryIdx] using
        budStep_edgeEndpointIds node entry ok st hids
    have childEndpoints_eq :=
      budStep_endpoints node entry ok st
    have childEndpoints_len :
        (budStep node entry ok st).endpoints.length =
          st.endpoints.length + Sig.arity node := by
      simp [childEndpoints_eq, Signature.nodePorts]
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < (budStep node entry ok st).endpoints.length := by
      simpa [childEndpoints_eq] using oldEndpoint_lt_budEndpoints st node hbound
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < (budStep node entry ok st).endpoints.length := by
      simpa [childEndpoints_eq, nodeEndpoints] using
        freshNodeEndpoint_lt_budEndpoints st hv node
          (by simpa [nodeEndpoints] using hmem)
    have old_fresh_disjoint
        {id : Nat} (hold : id < st.endpoints.length)
        (hfresh : id ∈ nodeEndpoints) : False := by
      exact oldEndpoint_not_mem_freshNodeEndpoints st hv hold
        (by simpa [nodeEndpoints] using hfresh)
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · rw [childFrontierIds_eq]
      apply nodup_append_of_nodup_disjoint
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
      rw [childFrontierIds_eq] at hfrontier
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
            rw [childFrontierIds_eq]
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
                (budStep node entry ok st).endpoints.length =
                  st.endpoints.length + Sig.arity node :=
              childEndpoints_len
            have hid' := hid
            rw [hchildLen] at hid'
            omega
        by_cases hentry : id = nodeEndpoints.get entryIdx
        · right
          rw [childConsumed_eq]
          simp [hentry]
        · left
          rw [childFrontierIds_eq]
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
  constructor
  intro renderNode hmem
  rcases budStep_node_mem_old_or_new node entry ok st hmem with hold | hnew
  · exact hn.node_incident_nodup renderNode hold
  · subst renderNode
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
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  have childOwners_eq :
      (budStep node entry ok st).ownerEndpointIds boundary =
        st.ownerEndpointIds boundary ++ nodeEndpoints := by
    simpa [nodeEndpoints] using
      budStep_ownerEndpointIds node entry ok st boundary
  have childEndpoints_eq :=
    budStep_endpoints node entry ok st
  have childEndpoints_len :
      (budStep node entry ok st).endpoints.length =
        st.endpoints.length + Sig.arity node := by
    simp [childEndpoints_eq, Signature.nodePorts]
  have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
      id < (budStep node entry ok st).endpoints.length := by
    simpa [childEndpoints_eq] using oldEndpoint_lt_budEndpoints st node hbound
  have fresh_bound {id : Nat} (hmem : id ∈ nodeEndpoints) :
      id < (budStep node entry ok st).endpoints.length := by
    simpa [childEndpoints_eq, nodeEndpoints] using
      freshNodeEndpoint_lt_budEndpoints st hv node
        (by simpa [nodeEndpoints] using hmem)
  have old_fresh_disjoint {id : Nat}
      (hold : id ∈ st.ownerEndpointIds boundary)
      (hfresh : id ∈ nodeEndpoints) : False := by
    have holdBound := ho.owner_bound id hold
    exact oldEndpoint_not_mem_freshNodeEndpoints st hv holdBound
      (by simpa [nodeEndpoints] using hfresh)
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


end Diag

end StringDiagram
end BijForm
