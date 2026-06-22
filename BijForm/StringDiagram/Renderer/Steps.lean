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
  let endpoint : Fin (st.endpoints ++ Sig.nodePorts node).length :=
    ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i, hbound⟩
  let nodePort : Fin (Sig.nodePorts node).length :=
    Fin.cast (by simp [freshNodeEndpoints, Signature.nodePorts]) i
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
        exact RenderState.frontierIds_cons_tail_length st hids
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
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
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
            restIds.get (Fin.cast (by
              exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
           left_label := rfl
           right_label := (Sig.compatible_edge ok).symm
           compatible := ok }] := by
  unfold connectStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    rfl

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
          restIds.get (Fin.cast (by
            exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok } := by
  let newEdge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right :=
        restIds.get (Fin.cast (by
          exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate)
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let i := edge.val
  have hchildSome :
      (connectStep mate ok st).edges[i]? =
        some ((connectStep mate ok st).edges.get edge) :=
    by simp [i]
  have hnewSome :
      (connectStep mate ok st).edges[i]? = some newEdge := by
    rw [connectStep_edges mate ok st hids]
    have hi : i = st.edges.length := by
      simpa [i] using hnew
    rw [hi]
    simp [newEdge]
  rw [hchildSome] at hnewSome
  injection hnewSome with hget

theorem connectStep_frontierIds
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (connectStep mate ok st).frontierIds =
      eraseFin restIds (Fin.cast (by
        exact (RenderState.frontierIds_cons_tail_length st hids).symm) mate) := by
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
                exact oldEndpoint_get_budEndpoints st node oldBound
                  (old_bound_lift oldBound)
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
                exact oldEndpoint_get_budEndpoints st node hbound
                  (old_bound_lift hbound)
          _ = edge.leftLabel := hlabel
      · cases hnew
        have hlabel := hv.frontier_head_label hids
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨activeId, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨activeId, hbound⟩ := by
                exact oldEndpoint_get_budEndpoints st node hbound
                  (old_bound_lift hbound)
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
                exact oldEndpoint_get_budEndpoints st node hbound
                  (old_bound_lift hbound)
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
                exact oldEndpoint_get_budEndpoints st node hbound
                  (old_bound_lift hbound)
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      simpa [child] using oldEndpoint_lt_budEndpoints st node hbound
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      simpa [child] using
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
      exact RenderState.frontierIds_cons_tail_length st hids
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
      simpa [child] using oldEndpoint_lt_budEndpoints st node hbound
    have fresh_bound {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      simpa [child] using
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
