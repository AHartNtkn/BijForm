import BijForm.StringDiagram.Traversal.State

namespace BijForm
namespace StringDiagram

open DepPoly

namespace OpenPortHypergraph

/--
Search the ordered pending tail for a `connect` step.  A successful result
carries the exact mate index and edge-mate proof consumed by `Diag.connect`.
-/
def firstPendingConnectSearch? (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G seenNode active rest) :=
  (List.finRange rest.length).findSome? fun mate =>
    match PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | some hmate => some (FirstPendingStep.connect mate hmate.proof)
    | none => none

theorem firstPendingConnectSearch?_exists_of_witness
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ step : FirstPendingStep G seenNode active rest,
      firstPendingConnectSearch? G seenNode active rest = some step := by
  unfold firstPendingConnectSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange mate
  · have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingConnectSearch?_some_connect
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G seenNode active rest}
    (hstep : firstPendingConnectSearch? G seenNode active rest = some step) :
    ∃ (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)),
      step = FirstPendingStep.connect mate hmate := by
  unfold firstPendingConnectSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨mate, _hmem, hcandidate⟩
  cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
      (rest.get mate) with
  | none =>
      rw [hcase] at hcandidate
      cases hcandidate
  | some data =>
      rw [hcase] at hcandidate
      injection hcandidate with hstepEq
      exact ⟨mate, data.proof, hstepEq.symm⟩

namespace SearchState

/--
Search unseen constructors in representative order for a `bud` step.  The
successful slot is the constructor port joined to the active endpoint.
-/
def firstPendingBudSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  (List.finRange G.raw.nodeCount).findSome? fun node =>
    if hseen : node ∈ st.seenNodes then
      none
    else
      (List.finRange (G.raw.incident node).length).findSome? fun slot =>
        match PortHypergraph.edgeMateCandidate? G.raw active
            ((G.raw.incident node).get slot) with
        | some hmate =>
            some (FirstPendingStep.bud node slot hmate.proof
              (by simpa [seenNode] using hseen))
        | none => none

theorem firstPendingBudSearch?_exists_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingBudSearch? active rest = some step := by
  unfold firstPendingBudSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange node
  · have hnodeUnseen : node ∉ st.seenNodes := by
      simpa [seenNode] using hunseen
    simp [hnodeUnseen]
    refine ⟨slot, ?_⟩
    have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingBudSearch?_some_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (hstep : st.firstPendingBudSearch? active rest = some step) :
    ∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen : ¬ st.seenNode node),
      step = FirstPendingStep.bud node slot hmate hunseen := by
  unfold firstPendingBudSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨node, _hnodeMem, hnodeCandidate⟩
  by_cases hseen : node ∈ st.seenNodes
  · simp [hseen] at hnodeCandidate
  · simp [hseen] at hnodeCandidate
    rcases List.exists_of_findSome?_eq_some hnodeCandidate with
      ⟨slot, _hslotMem, hslotCandidate⟩
    change
      (match PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
        | some hmate => some (FirstPendingStep.bud node slot
            hmate.proof (by simpa [seenNode] using hseen))
        | none => none) = some step at hslotCandidate
    cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
        ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hslotCandidate
        cases hslotCandidate
    | some data =>
        rw [hcase] at hslotCandidate
        injection hslotCandidate with hstepEq
        exact ⟨node, slot, data.proof, by simpa [seenNode] using hseen,
          hstepEq.symm⟩

/--
Executable first-pending search.  It tries the remaining pending frontier
first, then unseen constructor ports.  The returned value is constructor data,
not an eliminated `Prop` witness.
-/
def firstPendingStepSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  match firstPendingConnectSearch? G st.seenNode active rest with
  | some step => some step
  | none => st.firstPendingBudSearch? active rest

/-- A successful bud result from the executable first-pending search certifies
that the pending-tail connect search failed. -/
theorem firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    {hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)}
    {hunseen : ¬ st.seenNode node}
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    firstPendingConnectSearch? G st.seenNode active rest = none := by
  unfold firstPendingStepSearch? at hstep
  cases hconnect :
      firstPendingConnectSearch? G st.seenNode active rest with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          G st.seenNode hconnect with
        ⟨mate, hmate, hstepEq⟩
      rw [hconnect, hstepEq] at hstep
      cases hstep

theorem firstPendingStepSearch?_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (_hstep : st.firstPendingStepSearch? active rest = some step) :
    FirstPendingStepReady G st.seenNode active rest :=
  step.ready

theorem firstPendingStepSearch?_exists_of_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hready : FirstPendingStepReady G st.seenNode active rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step := by
  rcases hready with hconnect | hbud
  · rcases hconnect with ⟨mate, hmate⟩
    rcases firstPendingConnectSearch?_exists_of_witness
        G st.seenNode mate hmate with ⟨step, hstep⟩
    unfold firstPendingStepSearch?
    rw [hstep]
    exact ⟨step, rfl⟩
  · rcases hbud with ⟨node, slot, hmate, hunseen⟩
    unfold firstPendingStepSearch?
    cases hconnect :
        firstPendingConnectSearch? G st.seenNode active rest with
    | some step =>
        exact ⟨step, rfl⟩
    | none =>
        rcases st.firstPendingBudSearch?_exists_of_witness
            node slot hmate hunseen with ⟨step, hstep⟩
        exact ⟨step, by simp [hstep]⟩

theorem firstPendingStepSearch?_some_connect_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ (mate' : Fin rest.length)
      (hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate')),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate' hmate') := by
  rcases firstPendingConnectSearch?_exists_of_witness
      G st.seenNode mate hmate with ⟨step, hstep⟩
  rcases firstPendingConnectSearch?_some_connect
      G st.seenNode hstep with ⟨mate', hmate', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hstep]
  exact ⟨mate', hmate', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_connect_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hrestNodup : rest.Nodup)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate') := by
  rcases st.firstPendingStepSearch?_some_connect_of_witness mate hmate with
    ⟨mate', hmate', hstep⟩
  have hget : rest.get mate' = rest.get mate := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq (rest.get mate') hmate').trans
      (huniq (rest.get mate) hmate).symm
  have hmateEq : mate' = mate :=
    list_get_injective_of_nodup rest hrestNodup hget
  subst mate'
  exact ⟨hmate', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_connect
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
      Fin.cast (by simp) mate
    ∃ rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((rest.map e.endpointEquiv.toFun).get rightMate),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.connect rightMate rightMateEdge) := by
  dsimp
  let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
    Fin.cast (by simp) mate
  have hget :
      (rest.map e.endpointEquiv.toFun).get rightMate =
        e.endpointEquiv.toFun (rest.get mate) := by
    simp [rightMate]
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((rest.map e.endpointEquiv.toFun).get rightMate) := by
    rw [hget]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have hrightPending := hr.pending_cons hpending
  have hrightNodup :
      (rest.map e.endpointEquiv.toFun).Nodup :=
    right.rest_nodup hrightPending
  rcases right.firstPendingStepSearch?_some_connect_exact_of_witness
      hrightNodup rightMate rightMateEdge with
    ⟨rightMateEdge', hstep⟩
  exact ⟨rightMateEdge', hstep⟩

theorem IsoRelated.firstPendingConnectSearch?_none
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (_hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (_hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none) :
    firstPendingConnectSearch? H right.seenNode (e.endpointEquiv.toFun active)
        (rest.map e.endpointEquiv.toFun) = none := by
  cases hright :
      firstPendingConnectSearch? H right.seenNode
        (e.endpointEquiv.toFun active) (rest.map e.endpointEquiv.toFun) with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          H right.seenNode hright with
        ⟨rightMate, hmateRight, _hstepEq⟩
      let leftMate : Fin rest.length :=
        Fin.cast (by simp) rightMate
      have hget :
          (rest.map e.endpointEquiv.toFun).get rightMate =
            e.endpointEquiv.toFun (rest.get leftMate) := by
        simp [leftMate]
      have hmateRight' :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            (e.endpointEquiv.toFun (rest.get leftMate)) := by
        simpa [hget] using hmateRight
      have hmateLeft :
          PortHypergraph.EdgeMate G.raw active (rest.get leftMate) := by
        have hreflected := PortHypergraphIso.edgeMate_reflected e hmateRight'
        simpa using hreflected
      rcases firstPendingConnectSearch?_exists_of_witness
          G left.seenNode leftMate hmateLeft with
        ⟨leftStep, hleftStep⟩
      rw [hconnect] at hleftStep
      cases hleftStep

theorem firstPendingStepSearch?_some_bud_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (node' : Fin G.raw.nodeCount)
      (slot' : Fin (G.raw.incident node').length)
      (hmate' :
        PortHypergraph.EdgeMate G.raw active
          ((G.raw.incident node').get slot'))
      (hunseen' : ¬ st.seenNode node'),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node' slot' hmate' hunseen') := by
  rcases st.firstPendingBudSearch?_exists_of_witness
      node slot hmate hunseen with ⟨step, hstep⟩
  rcases st.firstPendingBudSearch?_some_bud hstep with
    ⟨node', slot', hmate', hunseen', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hconnect, hstep]
  exact ⟨node', slot', hmate', hunseen', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_bud_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (hmate' :
          PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen' : ¬ st.seenNode node),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate' hunseen') := by
  rcases st.firstPendingStepSearch?_some_bud_of_witness
      hconnect node slot hmate hunseen with
    ⟨node', slot', hmate', hunseen', hstep⟩
  have hendpointEq :
      (G.raw.incident node').get slot' = (G.raw.incident node).get slot := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq ((G.raw.incident node').get slot') hmate').trans
      (huniq ((G.raw.incident node).get slot) hmate).symm
  have hownerEq :
      (.constructor node' slot' :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      (.constructor node slot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) := by
    let endpoint := (G.raw.incident node).get slot
    rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
    have hleft :
        (.constructor node' slot' :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      exact hendpointEq
    have hright :
        (.constructor node slot :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      rfl
    exact hleft.trans hright.symm
  cases hownerEq
  exact ⟨hmate', hunseen', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_bud
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ left.seenNode node) :
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    ∃ (rightMateEdge :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            ((H.raw.incident rightNode).get rightSlot))
      (rightUnseen : ¬ right.seenNode rightNode),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.bud rightNode rightSlot rightMateEdge
          rightUnseen) := by
  dsimp
  let rightNode := e.nodeEquiv.toFun node
  let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((H.raw.incident rightNode).get rightSlot) := by
    have hslot :
        (H.raw.incident rightNode).get rightSlot =
          e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
      PortHypergraphIso.incidence_get_preserved e node slot
    rw [hslot]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have rightUnseen : ¬ right.seenNode rightNode := by
    intro hseen
    have hpre := hr.seen_mem_reflected hseen
    exact hunseen (by simpa [rightNode, seenNode] using hpre)
  have hconnectRight :=
    hr.firstPendingConnectSearch?_none hpending hconnect
  rcases right.firstPendingStepSearch?_some_bud_exact_of_witness
      hconnectRight rightNode rightSlot rightMateEdge rightUnseen with
    ⟨rightMateEdge', rightUnseen', hstep⟩
  exact ⟨rightMateEdge', rightUnseen', hstep⟩

end SearchState

/--
The global traversal-readiness invariant for an open representative.  It is
the totality statement for the owned graph-to-`Diag` search: every
nonempty ordered pending state has the constructor choice required by the
syntax.
-/
def FirstPendingTraversalReady (G : OpenPortHypergraph Sig boundary) : Prop :=
  ∀ {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : TraversalState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)},
    st.FrontierComplete →
    st.pending = active :: rest →
      FirstPendingStepReady G st.seenNode active rest

/--
Frontier completeness makes the first-pending traversal step locally total.
Initial completeness and step preservation supply the state-invariant
obligations for the owned graph-to-`Diag` traversal.
-/
theorem firstPendingTraversalReady_of_frontierComplete
    (G : OpenPortHypergraph Sig boundary) :
    FirstPendingTraversalReady G := by
  intro activeLabel restLabels st active rest hcomplete hpending
  rcases PortHypergraph.edgeMate_existsUnique G.raw active with
    ⟨mate, hmate, _hmateUniq⟩
  have hactiveMem : active ∈ st.pending := by
    rw [hpending]
    simp
  have hactiveUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge active) :=
    st.pending_unprocessed active hactiveMem
  have hmateUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge mate) := by
    intro hprocessed
    exact hactiveUnprocessed (by simpa [hmate.2] using hprocessed)
  have mate_pending_tail
      (hmatePending : mate ∈ st.pending) : mate ∈ rest := by
    rw [hpending] at hmatePending
    exact list_mem_tail_of_mem_cons_ne hmatePending (by
      intro hactiveMate
      exact hmate.1 hactiveMate)
  have connect_of_pending (hmatePending : mate ∈ st.pending) :
      FirstPendingStepReady G st.seenNode active rest := by
    have hrest : mate ∈ rest := mate_pending_tail hmatePending
    rcases list_exists_get_of_mem rest hrest with ⟨mateIndex, hget⟩
    refine Or.inl ⟨mateIndex, ?_⟩
    rw [hget]
    exact hmate
  rcases G.raw.endpoint_owner mate with ⟨owner, howner, _huniq⟩
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.boundary boundaryIndex) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      exact connect_of_pending
        (hcomplete mate hmateUnprocessed (.boundary boundaryIndex)
          hownerEndpoint)
  | constructor node slot =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      by_cases hseen : st.seenNode node
      · exact connect_of_pending
          (hcomplete mate hmateUnprocessed (.constructor node slot)
            hownerEndpoint hseen)
      · refine Or.inr ⟨node, slot, ?_, hseen⟩
        rw [show (G.raw.incident node).get slot = mate by
          simpa [PortHypergraph.endpointOwnerEndpoint] using hownerEndpoint]
        exact hmate

/--
A finite search state inherits first-pending step readiness from its projected
proof-level traversal state.  This still returns a `Prop`; the data-producing
search must construct `FirstPendingStep` directly.
-/
theorem SearchState.firstPendingStepReady_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
      FirstPendingStepReady G st.seenNode active rest :=
  (firstPendingTraversalReady_of_frontierComplete G)
    st.toTraversalState hcomplete hpending

theorem SearchState.firstPendingStepSearch?_exists_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step :=
  st.firstPendingStepSearch?_exists_of_ready
    (st.firstPendingStepReady_of_frontierComplete hcomplete hpending)

namespace SearchState

/--
Owned graph-to-syntax traversal from a finite search state.  The recursion
always processes the first pending endpoint.  The `none` search branch is
impossible by `firstPendingStepSearch?_exists_of_frontierComplete`, and child
recursion decreases the finite count of unprocessed edges.
-/
def toDiag {G : OpenPortHypergraph Sig boundary} :
    ∀ {frontier : List Sig.Port},
      (st : SearchState G frontier) → st.FrontierComplete → Diag Sig frontier
  | [], _st, _hcomplete => Diag.finish
  | activeLabel :: restLabels, st, hcomplete =>
      match hpending : st.pending with
      | [] =>
          False.elim (by
            have hlabels := st.pending_labels
            rw [hpending] at hlabels
            simp at hlabels)
      | active :: rest =>
          match hstep : st.firstPendingStepSearch? active rest with
          | none =>
              False.elim (by
                rcases st.firstPendingStepSearch?_exists_of_frontierComplete
                    hcomplete hpending with ⟨step, hsome⟩
                rw [hstep] at hsome
                cases hsome)
          | some step =>
              match step with
              | FirstPendingStep.connect mate hmate =>
                  Diag.connect
                    (st.restLabelIndex hpending mate)
                    (st.connect_compatible hpending mate hmate)
                    (toDiag
                      (st.connectChild hpending mate hmate)
                      (st.connectChild_frontierComplete hpending mate hmate
                        hcomplete))
              | FirstPendingStep.bud node slot hmate hunseen =>
                  Diag.bud
                    (G.raw.nodeLabel node)
                    (budEntry node slot)
                    (st.bud_compatible hpending node slot hmate)
                    (toDiag
                      (st.budChild hpending node slot hmate
                        (by simpa [seenNode] using hunseen))
                      (st.budChild_frontierComplete hpending node slot hmate
                        (by simpa [seenNode] using hunseen) hcomplete))
termination_by frontier st _hcomplete => st.remainingEdges
decreasing_by
  · exact st.connectChild_remainingEdges_lt hpending mate hmate
  · exact st.budChild_remainingEdges_lt hpending node slot hmate
      (by simpa [seenNode] using hunseen)

/-- The owned traversal result is independent of the proof of frontier
completeness supplied to it. -/
theorem toDiag_frontierComplete_irrel {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    (h₁ h₂ : st.FrontierComplete) :
    st.toDiag h₁ = st.toDiag h₂ := by
  have hproof : h₁ = h₂ := Subsingleton.elim _ _
  cases hproof
  rfl

/-- Traversal commutes with casting the frontier index of a search state. -/
theorem toDiag_cast {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier)
    (hc : st.FrontierComplete) :
    (h ▸ st).toDiag (frontierComplete_cast h st hc) =
      h ▸ st.toDiag hc := by
  cases h
  rfl

/-- Empty-frontier traversal computes to `finish`. -/
theorem toDiag_empty {G : OpenPortHypergraph Sig boundary}
    (st : SearchState G []) (hcomplete : st.FrontierComplete) :
    st.toDiag hcomplete = Diag.finish := by
  rw [SearchState.toDiag.eq_def]

/-- Connect-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_connect {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate)) :
    st.toDiag hcomplete =
      Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate)
        ((st.connectChild hpending mate hmate).toDiag
          (st.connectChild_frontierComplete hpending mate hmate hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect mate' hmate' =>
          rw [hstep] at hstep'
          injection hstep' with hconnect
          cases hconnect
          simp
      | bud _node _slot _hmate' _hunseen =>
          rw [hstep] at hstep'
          cases hstep'

/-- Bud-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_bud {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node)
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    st.toDiag hcomplete =
      Diag.bud
        (G.raw.nodeLabel node)
        (budEntry node slot)
        (st.bud_compatible hpending node slot hmate)
        ((st.budChild hpending node slot hmate
            (by simpa [seenNode] using hunseen)).toDiag
          (st.budChild_frontierComplete hpending node slot hmate
            (by simpa [seenNode] using hunseen) hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect _mate' _hmate' =>
          rw [hstep] at hstep'
          cases hstep'
      | bud _node' _slot' _hmate' _hunseen' =>
          rw [hstep] at hstep'
          injection hstep' with hbud
          cases hbud
          simp

/-- The owned graph-to-syntax traversal is invariant under related
ordered-boundary-preserving isomorphic search states. -/
theorem toDiag_isoRelated
    {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    {frontier : List Sig.Port}
    (left : SearchState G frontier) (right : SearchState H frontier)
    (hrel : IsoRelated e left right)
    (hleft : left.FrontierComplete) (hright : right.FrontierComplete) :
    left.toDiag hleft = right.toDiag hright := by
  induction frontier, left, hleft using SearchState.toDiag.induct with
  | case1 st hcomplete _hcomplete =>
      rw [toDiag_empty]
      rw [toDiag_empty]
  | case2 activeLabel restLabels active rest mate hmate st _hcomplete
      hcomplete hpending hstep _hstep ih =>
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_connect hpending mate hmate with
        ⟨rightMateEdge, hrightStep⟩
      have hchildRel :=
        hrel.connectChild_with hpending mate hmate rightMateEdge
      have hchild :=
        ih (right.connectChild hrightPending (Fin.cast (by simp) mate)
              rightMateEdge) hchildRel
          (right.connectChild_frontierComplete hrightPending
            (Fin.cast (by simp) mate) rightMateEdge hright)
      rw [toDiag_connect st hcomplete hpending mate hmate hstep]
      rw [toDiag_connect right hright hrightPending
        (Fin.cast (by simp) mate) rightMateEdge hrightStep]
      have hidx := hrel.restLabelIndex hpending mate
      cases hidx
      have hok :
          right.connect_compatible hrightPending (Fin.cast (by simp) mate)
              rightMateEdge =
            st.connect_compatible hpending mate hmate := Subsingleton.elim _ _
      cases hok
      exact congrArg (fun child => Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) child) hchild
  | case3 activeLabel restLabels active rest node slot hmate st _hcomplete
      hcomplete hpending hunseen hstep _hstep ih =>
      have hconnect :=
        st.firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud hstep
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_bud hpending hconnect node slot
          hmate hunseen with
        ⟨rightMateEdge, rightUnseen, hrightStep⟩
      let rightNode := e.nodeEquiv.toFun node
      let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
      have rightUnseenMem : rightNode ∉ right.seenNodes := by
        simpa [rightNode, seenNode] using rightUnseen
      have leftUnseenMem : node ∉ st.seenNodes := by
        simpa [seenNode] using hunseen
      have hfrontier :
          restLabels ++
              Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
                (budEntry (G := H) rightNode rightSlot) =
            restLabels ++
              Sig.nodePortsExcept (G.raw.nodeLabel node)
                (budEntry (G := G) node slot) := by
        have hentryVal := budEntry_val_preserved e node slot
        exact congrArg (fun tail => restLabels ++ tail)
          (Signature.nodePortsExcept_eq_of_val (Sig := Sig)
            (e.node_label_preserved node).symm hentryVal)
      let rightChild :=
        hfrontier ▸
          right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem
      have hchildRel :
          IsoRelated e
            (st.budChild hpending node slot hmate leftUnseenMem)
            rightChild := by
        dsimp [rightChild, rightNode, rightSlot, hfrontier]
        exact hrel.budChild_with hpending node slot hmate leftUnseenMem
          rightMateEdge rightUnseenMem
      have hrightChildCompleteUncast :
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).FrontierComplete :=
        right.budChild_frontierComplete hrightPending rightNode rightSlot
          rightMateEdge rightUnseenMem hright
      have hrightChildComplete : rightChild.FrontierComplete := by
        dsimp [rightChild]
        exact frontierComplete_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchild := ih rightChild hchildRel hrightChildComplete
      rw [toDiag_bud st hcomplete hpending node slot hmate hunseen hstep]
      rw [toDiag_bud right hright hrightPending rightNode rightSlot
        rightMateEdge rightUnseen hrightStep]
      have hrightChildDiagCast :
          rightChild.toDiag hrightChildComplete =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        dsimp [rightChild, hrightChildComplete]
        exact toDiag_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchildCast :
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
              (st.budChild_frontierComplete hpending node slot hmate
                leftUnseenMem hcomplete) =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        exact hchild.trans hrightChildDiagCast
      exact Diag.bud_transport
        (hnode := (e.node_label_preserved node).symm)
        (hentryVal := budEntry_val_preserved e node slot)
        (okA := st.bud_compatible hpending node slot hmate)
        (okB := right.bud_compatible hrightPending rightNode rightSlot
          rightMateEdge)
        (childA :=
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
            (st.budChild_frontierComplete hpending node slot hmate
              leftUnseenMem hcomplete))
        (childB :=
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).toDiag hrightChildCompleteUncast)
        hfrontier hchildCast

end SearchState

def fromGraph (G : OpenPortHypergraph Sig boundary) : Diag Sig boundary :=
  (SearchState.initial G).toDiag (SearchState.initial_frontierComplete G)

namespace SearchState

/-- Semantic exhaustion for a finite search state: all constructors have been
seen and all edges have been consumed by traversal steps. -/
structure GraphExhausted {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop where
  allNodesSeen : ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes
  allEdgesProcessed : ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges

theorem pending_ne_nil_of_reachable_unprocessed
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    {endpoint : Fin G.raw.endpointCount}
    (hreach : PortHypergraph.PortReachesBoundary G.raw endpoint)
    (hunprocessed : G.raw.endpointEdge endpoint ∉ st.processedEdges) :
    st.pending ≠ [] := by
  induction hreach with
  | boundary b =>
      intro hpendingNil
      have hmem :
          G.raw.boundaryPort b ∈ st.pending :=
        hcomplete (G.raw.boundaryPort b) hunprocessed (.boundary b) rfl
      rw [hpendingNil] at hmem
      cases hmem
  | throughEdge sameEdge _different _reach ih =>
      apply ih
      intro hprocessed
      exact hunprocessed (by
        rw [← sameEdge]
        exact hprocessed)
  | throughConstructor node fromSlot toSlot hp hq _reach ih =>
      by_cases hseen : node ∈ st.seenNodes
      · intro hpendingNil
        have htoUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get toSlot) ∉
              st.processedEdges := by
          rw [hq]
          exact hunprocessed
        have hmem :
            (G.raw.incident node).get toSlot ∈ st.pending :=
          hcomplete ((G.raw.incident node).get toSlot) htoUnprocessed
            (.constructor node toSlot) rfl hseen
        rw [hpendingNil] at hmem
        cases hmem
      · have hfromUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get fromSlot) ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hseen fromSlot
        apply ih
        rw [← hp]
        exact hfromUnprocessed

theorem allNodesSeen_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes := by
  intro node
  by_cases hseen : node ∈ st.seenNodes
  · exact hseen
  · rcases G.allConstructorsReachBoundary node with ⟨slot, hreach⟩
    have hunprocessed :
        G.raw.endpointEdge ((G.raw.incident node).get slot) ∉
          st.processedEdges :=
      st.unseen_incident_unprocessed node hseen slot
    have hnonempty :=
      st.pending_ne_nil_of_reachable_unprocessed hcomplete hreach hunprocessed
    exact False.elim (hnonempty hpendingNil)

theorem allEdgesProcessed_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges := by
  intro edge
  by_cases hprocessed : edge ∈ st.processedEdges
  · exact hprocessed
  · rcases G.raw.edge_two_endpoints edge with
      ⟨left, _right, _hdiff, hleft, _hright, _hall⟩
    have hleftUnprocessed :
        G.raw.endpointEdge left ∉ st.processedEdges := by
      intro hleftProcessed
      exact hprocessed (by simpa [hleft] using hleftProcessed)
    rcases G.raw.endpoint_owner left with ⟨owner, howner, _huniq⟩
    cases owner with
    | boundary boundaryIndex =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.boundary boundaryIndex)
            hownerEndpoint
        rw [hpendingNil] at hmem
        cases hmem
    | constructor node slot =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hseen : node ∈ st.seenNodes :=
          st.allNodesSeen_of_pending_nil hcomplete hpendingNil node
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.constructor node slot)
            hownerEndpoint hseen
        rw [hpendingNil] at hmem
        cases hmem

theorem graphExhausted_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    st.GraphExhausted where
  allNodesSeen := st.allNodesSeen_of_pending_nil hcomplete hpendingNil
  allEdgesProcessed := st.allEdgesProcessed_of_pending_nil hcomplete hpendingNil

theorem pending_eq_nil_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G []) :
    st.pending = [] := by
  cases hpending : st.pending with
  | nil => rfl
  | cons active rest =>
      have hlabels := st.pending_labels
      rw [hpending] at hlabels
      simp at hlabels

theorem graphExhausted_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G [])
    (hcomplete : st.FrontierComplete) :
    st.GraphExhausted :=
  st.graphExhausted_of_pending_nil hcomplete
    st.pending_eq_nil_of_empty_frontier

end SearchState

def isoRel (G H : OpenPortHypergraph Sig boundary) : Prop :=
  Nonempty (PortHypergraphIso G.raw H.raw)

def isoSetoid (Sig : Signature) (boundary : List Sig.Port) :
    Setoid (OpenPortHypergraph Sig boundary) where
  r := isoRel
  iseqv := by
    constructor
    · intro G
      exact ⟨PortHypergraphIso.refl G.raw⟩
    · intro G H h
      rcases h with ⟨e⟩
      exact ⟨PortHypergraphIso.symm e⟩
    · intro G H K hGH hHK
      rcases hGH with ⟨eGH⟩
      rcases hHK with ⟨eHK⟩
      exact ⟨PortHypergraphIso.trans eGH eHK⟩

end OpenPortHypergraph

end StringDiagram
end BijForm
