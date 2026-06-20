import BijForm.DependentPolynomial

namespace BijForm
namespace StringDiagram

open DepPoly

/-- Remove the element at a proof-carrying index. -/
def eraseFin {α : Type} : (xs : List α) → Fin xs.length → List α
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => xs
  | x :: xs, ⟨n + 1, h⟩ =>
      x :: eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩

@[simp]
theorem eraseFin_length {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      (eraseFin xs i).length = xs.length - 1
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => by simp [eraseFin]
  | x :: xs, ⟨n + 1, h⟩ => by
      have ih := eraseFin_length xs ⟨n, Nat.lt_of_succ_lt_succ h⟩
      have htail : n < xs.length := Nat.lt_of_succ_lt_succ h
      have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le n) htail
      simp [eraseFin, ih]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)

/--
A typed ordered-port string-diagram signature.

`Edge` is the label carried by wires/edges.  `Port` is the label carried by
open frontier endpoints.  Unoriented signatures usually take `Port` to be the
same type as `Edge`.  Oriented signatures usually take `Port` to be a direction
paired with an edge type.  `portEdge` forgets endpoint-only data,
`compatible` states when two frontier endpoints may be joined, and
`compatible_edge` and `compatible_symm` ensure such a connection has one edge
label and can be viewed from either endpoint.

Each node label has a finite ordered list of ports, represented by `arity` and
`port`.  The order is part of the formal data because the canonical traversal
and linear isomorphism test depend on it.
-/
structure Signature where
  Edge : Type
  Port : Type
  Node : Type
  portEdge : Port → Edge
  arity : Node → Nat
  port : (node : Node) → Fin (arity node) → Port
  compatible : Port → Port → Prop
  compatible_edge :
    ∀ {left right : Port}, compatible left right → portEdge left = portEdge right
  compatible_symm :
    ∀ {left right : Port}, compatible left right → compatible right left

namespace Unoriented

/-- Build an unoriented signature: endpoint compatibility is equality of wire
types, while every constructor still has an ordered list of typed ports. -/
def signature (Ty Node : Type)
    (arity : Node → Nat)
    (portTy : (node : Node) → Fin (arity node) → Ty) :
    Signature where
  Edge := Ty
  Port := Ty
  Node := Node
  portEdge := id
  arity := arity
  port := portTy
  compatible := Eq
  compatible_edge := by
    intro left right h
    exact h
  compatible_symm := by
    intro left right h
    exact h.symm

end Unoriented

/-- Endpoint polarity for oriented string diagrams. -/
inductive Direction where
  | input
  | output
deriving DecidableEq, Repr

namespace Direction

def opposite : Direction → Direction
  | .input => .output
  | .output => .input

@[simp]
theorem opposite_opposite (d : Direction) : opposite (opposite d) = d := by
  cases d <;> rfl

end Direction

namespace Oriented

/-- A typed oriented endpoint. -/
structure Endpoint (Ty : Type) where
  direction : Direction
  ty : Ty
deriving Repr

/-- Build an oriented signature.  Two endpoints are compatible when their wire
types agree and their directions are opposite. -/
def signature (Ty Node : Type)
    (arity : Node → Nat)
    (portSpec : (node : Node) → Fin (arity node) → Endpoint Ty) :
    Signature where
  Edge := Ty
  Port := Endpoint Ty
  Node := Node
  portEdge := fun p => p.ty
  arity := arity
  port := portSpec
  compatible := fun p q =>
    p.ty = q.ty ∧ Direction.opposite p.direction = q.direction
  compatible_edge := by
    intro left right h
    exact h.1
  compatible_symm := by
    intro left right h
    constructor
    · exact h.1.symm
    · rw [← h.2]
      exact Direction.opposite_opposite left.direction

end Oriented

/-- Constructor tags for the traversal grammar. -/
inductive Ctor where
  | finish
  | connect
  | bud
deriving DecidableEq, Repr

namespace Signature

variable (Sig : Signature)

theorem edge_eq_of_compatible {left right : Sig.Port}
    (ok : Sig.compatible left right) :
    Sig.portEdge left = Sig.portEdge right :=
  Sig.compatible_edge ok

theorem compatible_comm {left right : Sig.Port}
    (ok : Sig.compatible left right) :
    Sig.compatible right left :=
  Sig.compatible_symm ok

def nodePorts (node : Sig.Node) : List Sig.Port :=
  List.ofFn fun slot : Fin (Sig.arity node) => Sig.port node slot

def nodePortsExcept (node : Sig.Node) (entry : Fin (Sig.arity node)) :
    List Sig.Port :=
  eraseFin (Sig.nodePorts node) (Fin.cast (by simp [nodePorts]) entry)

end Signature

/--
Canonical traversal syntax for typed open string diagrams.

The index is the ordered frontier boundary.  `connect` always processes the
first frontier port and connects it to one later frontier port.  `bud` processes
the first frontier port by entering an ordered constructor port and appending
the remaining constructor ports, in constructor order, to the frontier.
-/
inductive Diag (Sig : Signature) : List Sig.Port → Type
  | finish : Diag Sig []
  | connect {active : Sig.Port} {frontier : List Sig.Port}
      (mate : Fin frontier.length)
      (ok : Sig.compatible active (frontier.get mate))
      (child : Diag Sig (eraseFin frontier mate)) :
      Diag Sig (active :: frontier)
  | bud {active : Sig.Port} {frontier : List Sig.Port}
      (node : Sig.Node)
      (entry : Fin (Sig.arity node))
      (ok : Sig.compatible active (Sig.port node entry))
      (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
      Diag Sig (active :: frontier)

namespace Diag

variable {Sig : Signature}

/-- Structural rank used for the generated syntax coding. -/
def rank : ∀ {boundary : List Sig.Port}, Diag Sig boundary → Nat
  | _, finish => 0
  | _, connect _ _ child => rank child + 1
  | _, bud _ _ _ child => rank child + 1

end Diag

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

end RenderState

namespace Diag

variable {Sig : Signature}

def freshNodeEndpoints (start arity : Nat) : List Nat :=
  (List.range arity).map fun offset => start + offset

@[simp]
theorem freshNodeEndpoints_length (start arity : Nat) :
    (freshNodeEndpoints start arity).length = arity := by
  simp [freshNodeEndpoints]

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

def renderTraceFromBoundary {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState Sig [] :=
  renderTrace d (RenderState.initial Sig boundary)

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

structure ConnectParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  mate : Fin frontier.length
  ok : Sig.compatible active (frontier.get mate)

structure BudParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  node : Sig.Node
  entry : Fin (Sig.arity node)
  ok : Sig.compatible active (Sig.port node entry)

def Param (Sig : Signature) : Ctor → Type
  | .finish => Unit
  | .connect => ConnectParam Sig
  | .bud => BudParam Sig

def out (Sig : Signature) : (c : Ctor) → Param Sig c → List Sig.Port
  | .finish, _ => []
  | .connect, p => p.active :: p.frontier
  | .bud, p => p.active :: p.frontier

def Pos (_Sig : Signature) : (c : Ctor) → Param _Sig c → Type
  | .finish, _ => Empty
  | .connect, _ => Unit
  | .bud, _ => Unit

def input (Sig : Signature) :
    {c : Ctor} → (p : Param Sig c) → Pos Sig c p → List Sig.Port
  | .finish, _, q => nomatch q
  | .connect, p, _ => eraseFin p.frontier p.mate
  | .bud, p, _ => p.frontier ++ Sig.nodePortsExcept p.node p.entry

/-- Dependent polynomial for typed ordered-frontier traversal syntax. -/
def poly (Sig : Signature) : DepPoly (List Sig.Port) where
  Ctor := Ctor
  Param := Param Sig
  out := out Sig
  Pos := Pos Sig
  input := input Sig

/-- Same-fiber constructor data for typed string diagrams. -/
def inversion (Sig : Signature) : OutputIndexInversion (poly Sig) :=
  OutputIndexInversion.canonical (poly Sig)

def layerToSyntax (Sig : Signature) (boundary : List Sig.Port) :
    CodeLayer (poly Sig) (inversion Sig) (Diag Sig) boundary → Diag Sig boundary
  | ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
      exact .finish
  | ⟨⟨.connect, p, h⟩, child⟩ => by
      cases p with
      | mk active frontier mate ok =>
          cases h
          exact .connect mate ok (child ())
  | ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk active frontier node entry ok =>
          cases h
          exact .bud node entry ok (child ())

def syntaxToLayer (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary → CodeLayer (poly Sig) (inversion Sig) (Diag Sig) boundary
  | .finish =>
      ⟨⟨Ctor.finish, (), rfl⟩, fun q => nomatch q⟩
  | @Diag.connect _ active frontier mate ok child =>
      ⟨⟨Ctor.connect, ⟨active, frontier, mate, ok⟩, rfl⟩, fun _ => child⟩
  | @Diag.bud _ active frontier node entry ok child =>
      ⟨⟨Ctor.bud, ⟨active, frontier, node, entry, ok⟩, rfl⟩, fun _ => child⟩

def syntaxLayerPresentation (Sig : Signature) :
    CodeLayerPresentation (poly Sig) (inversion Sig) (Diag Sig) (Diag Sig) :=
  CodeLayerPresentation.ofMaps
    (layerToSyntax Sig)
    (syntaxToLayer Sig)
    (by
      intro boundary layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | finish =>
              cases param
              cases out_eq
              have hchild : (fun q => nomatch q) = child := by
                child_eta_empty
              cases hchild
              rfl
          | connect =>
              cases param with
              | mk active frontier mate ok =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl
          | bud =>
              cases param with
              | mk active frontier node entry ok =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl)
    (by
      intro boundary t
      cases t with
      | finish => rfl
      | connect mate ok child => rfl
      | bud node entry ok child => rfl)

theorem layer_child_rank_lt (Sig : Signature) :
    ∀ {boundary : List Sig.Port} (z : Diag Sig boundary)
      (q : (poly Sig).Pos
          ((inversion Sig).decode boundary
            (((syntaxLayerPresentation Sig).iso boundary).invFun z).1).ctor
          ((inversion Sig).decode boundary
            (((syntaxLayerPresentation Sig).iso boundary).invFun z).1).param),
      Diag.rank ((((syntaxLayerPresentation Sig).iso boundary).invFun z).2 q) <
        Diag.rank z := by
  intro boundary z q
  cases z with
  | finish =>
      cases q
  | connect mate ok child =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]
  | bud node entry ok child =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]

/-- Presentation of typed rooted open diagram syntax as generated code data. -/
def syntaxPresentation (Sig : Signature) :
    SyntaxPresentation (poly Sig) (inversion Sig) (Diag Sig) :=
  SyntaxPresentation.ofLayer
    (syntaxLayerPresentation Sig)
    (fun _ t => Diag.rank t)
    (layer_child_rank_lt Sig)

/-- Generated coding data for typed rooted open diagram syntax. -/
def generatedCode (Sig : Signature) : GeneratedCode (poly Sig) (Diag Sig) :=
  (syntaxPresentation Sig).generatedCode

/--
Typed rooted open diagrams are bijective with the initial algebra of their
dependent polynomial presentation through the generic generated-code
construction.
-/
def syntaxIso (Sig : Signature) (boundary : List Sig.Port) :
    Mu (poly Sig) boundary ≃ᵢ Diag Sig boundary :=
  (generatedCode Sig).iso boundary

/-!
## Semantic port-hypergraph representatives

The syntax above uses a frontier of endpoint labels.  The semantic
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

/-- A mate of an endpoint is the other endpoint on the same edge. -/
def EdgeMate (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Prop :=
  endpoint ≠ mate ∧ G.endpointEdge endpoint = G.endpointEdge mate

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

theorem edgeMate_compatible (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    Sig.compatible (G.endpointLabel endpoint) (G.endpointLabel mate) :=
  G.edge_compatible endpoint mate hmate.2 hmate.1

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
  endpointEdge : Fin st.endpoints.length → Fin st.edges.length
  endpoint_edge_label :
    ∀ endpoint : Fin st.endpoints.length,
      Sig.portEdge (st.endpoints.get endpoint) =
        (st.edges.get (endpointEdge endpoint)).label
  edge_compatible :
    ∀ left right : Fin st.endpoints.length,
      endpointEdge left = endpointEdge right →
        left ≠ right →
          Sig.compatible (st.endpoints.get left) (st.endpoints.get right)
  edge_two_endpoints :
    ∀ edge : Fin st.edges.length,
      ∃ left right : Fin st.endpoints.length,
        left ≠ right ∧
        endpointEdge left = edge ∧
        endpointEdge right = edge ∧
        ∀ endpoint : Fin st.endpoints.length,
          endpointEdge endpoint = edge → endpoint = left ∨ endpoint = right
  boundaryPort : Fin boundary.length → Fin st.endpoints.length
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length,
      st.endpoints.get (boundaryPort b) = boundary.get b
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
  endpoint_owner :
    ∀ endpoint : Fin st.endpoints.length,
      ∃ owner : EndpointOwner boundary.length st.nodes.length
          (fun node => (incident node).length),
        (match owner with
          | .boundary boundaryIndex => boundaryPort boundaryIndex
          | .constructor node slot => (incident node).get slot) = endpoint ∧
        ∀ owner' : EndpointOwner boundary.length st.nodes.length
            (fun node => (incident node).length),
          (match owner' with
            | .boundary boundaryIndex => boundaryPort boundaryIndex
            | .constructor node slot => (incident node).get slot) = endpoint →
          owner' = owner

namespace PortHypergraphEvidence

def toPortHypergraph {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : PortHypergraphEvidence st boundary) :
    PortHypergraph Sig boundary := by
  cases ev with
  | mk endpointEdge endpoint_edge_label edge_compatible edge_two_endpoints
      boundaryPort boundary_injective boundary_label incident incident_length
      incident_injective incidence_label endpoint_owner =>
    exact
      { endpointCount := st.endpoints.length
        edgeCount := st.edges.length
        nodeCount := st.nodes.length
        endpointLabel := st.endpoints.get
        edgeLabel := fun edge => (st.edges.get edge).label
        endpointEdge := endpointEdge
        endpoint_edge_label := endpoint_edge_label
        edge_compatible := edge_compatible
        edge_two_endpoints := edge_two_endpoints
        boundaryPort := boundaryPort
        boundary_injective := boundary_injective
        boundary_label := boundary_label
        nodeLabel := fun node => (st.nodes.get node).label
        incident := incident
        incident_length := incident_length
        incident_injective := incident_injective
        incidence_label := incidence_label
        endpoint_owner := by
          intro endpoint
          rcases endpoint_owner endpoint with ⟨owner, howner, huniq⟩
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
                  exact huniq (.constructor node' slot') (by simpa using howner') }

end PortHypergraphEvidence

/-- Evidence that a completed render trace presents an open semantic graph. -/
structure OpenPortHypergraphEvidence
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  graph : PortHypergraphEvidence st boundary
  allConstructorsReachBoundary :
    PortHypergraph.AllConstructorsReachBoundary graph.toPortHypergraph

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

/--
UNFINISHED renderer validity: the trace produced from traversal syntax carries
exactly the endpoint, edge, boundary, and ordered-constructor incidence
evidence required to be an open `PortHypergraph`.
-/
def renderTraceFromBoundary_openEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.OpenPortHypergraphEvidence
      (renderTraceFromBoundary d) boundary := by
  sorry

/--
UNFINISHED semantic renderer obtained from
`renderTraceFromBoundary_openEvidence`.  This declaration records the intended
renderer target and depends on the unfinished renderer-validity proof above.
-/
def toOpenPortHypergraph_unfinished
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    OpenPortHypergraph Sig boundary :=
  (renderTraceFromBoundary_openEvidence d).toOpenPortHypergraph

end Diag

/--
Boundary-preserving isomorphism of typed finite representatives.  It relabels
endpoints, edges, and nodes, preserves the ordered boundary pointwise,
preserves endpoint/edge/node labels, preserves endpoint-to-edge incidence, and
preserves every ordered constructor-port incidence.
-/
structure PortHypergraphIso {Sig : Signature} {boundary : List Sig.Port}
    (G H : PortHypergraph Sig boundary) where
  endpointEquiv : Fin G.endpointCount ≃ᵢ Fin H.endpointCount
  edgeEquiv : Fin G.edgeCount ≃ᵢ Fin H.edgeCount
  nodeEquiv : Fin G.nodeCount ≃ᵢ Fin H.nodeCount
  boundary_preserved :
    ∀ b : Fin boundary.length,
      endpointEquiv.toFun (G.boundaryPort b) = H.boundaryPort b
  boundary_reflected :
    ∀ b : Fin boundary.length,
      endpointEquiv.invFun (H.boundaryPort b) = G.boundaryPort b
  endpoint_label_preserved :
    ∀ endpoint : Fin G.endpointCount,
      G.endpointLabel endpoint =
        H.endpointLabel (endpointEquiv.toFun endpoint)
  endpoint_label_reflected :
    ∀ endpoint : Fin H.endpointCount,
      H.endpointLabel endpoint =
        G.endpointLabel (endpointEquiv.invFun endpoint)
  edge_label_preserved :
    ∀ edge : Fin G.edgeCount,
      G.edgeLabel edge = H.edgeLabel (edgeEquiv.toFun edge)
  edge_label_reflected :
    ∀ edge : Fin H.edgeCount,
      H.edgeLabel edge = G.edgeLabel (edgeEquiv.invFun edge)
  endpoint_edge_preserved :
    ∀ endpoint : Fin G.endpointCount,
      H.endpointEdge (endpointEquiv.toFun endpoint) =
        edgeEquiv.toFun (G.endpointEdge endpoint)
  endpoint_edge_reflected :
    ∀ endpoint : Fin H.endpointCount,
      G.endpointEdge (endpointEquiv.invFun endpoint) =
        edgeEquiv.invFun (H.endpointEdge endpoint)
  node_label_preserved :
    ∀ node : Fin G.nodeCount,
      G.nodeLabel node = H.nodeLabel (nodeEquiv.toFun node)
  node_label_reflected :
    ∀ node : Fin H.nodeCount,
      H.nodeLabel node = G.nodeLabel (nodeEquiv.invFun node)
  incidence_preserved :
    ∀ node : Fin G.nodeCount,
      (G.incident node).map endpointEquiv.toFun =
        H.incident (nodeEquiv.toFun node)
  incidence_reflected :
    ∀ node : Fin H.nodeCount,
      (H.incident node).map endpointEquiv.invFun =
        G.incident (nodeEquiv.invFun node)

namespace PortHypergraphIso

variable {Sig : Signature} {boundary : List Sig.Port}

def refl (G : PortHypergraph Sig boundary) : PortHypergraphIso G G where
  endpointEquiv := Iso.refl (Fin G.endpointCount)
  edgeEquiv := Iso.refl (Fin G.edgeCount)
  nodeEquiv := Iso.refl (Fin G.nodeCount)
  boundary_preserved := by
    intro _
    rfl
  boundary_reflected := by
    intro _
    rfl
  endpoint_label_preserved := by
    intro _
    rfl
  endpoint_label_reflected := by
    intro _
    rfl
  edge_label_preserved := by
    intro _
    rfl
  edge_label_reflected := by
    intro _
    rfl
  endpoint_edge_preserved := by
    intro _
    rfl
  endpoint_edge_reflected := by
    intro _
    rfl
  node_label_preserved := by
    intro _
    rfl
  node_label_reflected := by
    intro _
    rfl
  incidence_preserved := by
    intro _
    simp [Iso.refl]
  incidence_reflected := by
    intro _
    simp [Iso.refl]

def symm {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) : PortHypergraphIso H G where
  endpointEquiv := Iso.symm e.endpointEquiv
  edgeEquiv := Iso.symm e.edgeEquiv
  nodeEquiv := Iso.symm e.nodeEquiv
  boundary_preserved := e.boundary_reflected
  boundary_reflected := e.boundary_preserved
  endpoint_label_preserved := e.endpoint_label_reflected
  endpoint_label_reflected := e.endpoint_label_preserved
  edge_label_preserved := e.edge_label_reflected
  edge_label_reflected := e.edge_label_preserved
  endpoint_edge_preserved := e.endpoint_edge_reflected
  endpoint_edge_reflected := e.endpoint_edge_preserved
  node_label_preserved := e.node_label_reflected
  node_label_reflected := e.node_label_preserved
  incidence_preserved := e.incidence_reflected
  incidence_reflected := e.incidence_preserved

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
  boundary_reflected := by
    intro b
    simp [Iso.trans, Function.comp, e₂.boundary_reflected b,
      e₁.boundary_reflected b]
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
  endpoint_label_reflected := by
    intro endpoint
    calc
      K.endpointLabel endpoint =
          H.endpointLabel (e₂.endpointEquiv.invFun endpoint) :=
        e₂.endpoint_label_reflected endpoint
      _ =
          G.endpointLabel
            (e₁.endpointEquiv.invFun (e₂.endpointEquiv.invFun endpoint)) :=
        e₁.endpoint_label_reflected (e₂.endpointEquiv.invFun endpoint)
  edge_label_preserved := by
    intro edge
    calc
      G.edgeLabel edge = H.edgeLabel (e₁.edgeEquiv.toFun edge) :=
        e₁.edge_label_preserved edge
      _ = K.edgeLabel (e₂.edgeEquiv.toFun (e₁.edgeEquiv.toFun edge)) :=
        e₂.edge_label_preserved (e₁.edgeEquiv.toFun edge)
  edge_label_reflected := by
    intro edge
    calc
      K.edgeLabel edge = H.edgeLabel (e₂.edgeEquiv.invFun edge) :=
        e₂.edge_label_reflected edge
      _ = G.edgeLabel (e₁.edgeEquiv.invFun (e₂.edgeEquiv.invFun edge)) :=
        e₁.edge_label_reflected (e₂.edgeEquiv.invFun edge)
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
  endpoint_edge_reflected := by
    intro endpoint
    calc
      G.endpointEdge
          (e₁.endpointEquiv.invFun (e₂.endpointEquiv.invFun endpoint)) =
          e₁.edgeEquiv.invFun
            (H.endpointEdge (e₂.endpointEquiv.invFun endpoint)) :=
        e₁.endpoint_edge_reflected (e₂.endpointEquiv.invFun endpoint)
      _ =
          e₁.edgeEquiv.invFun
            (e₂.edgeEquiv.invFun (K.endpointEdge endpoint)) := by
        rw [e₂.endpoint_edge_reflected endpoint]
  node_label_preserved := by
    intro node
    calc
      G.nodeLabel node = H.nodeLabel (e₁.nodeEquiv.toFun node) :=
        e₁.node_label_preserved node
      _ = K.nodeLabel (e₂.nodeEquiv.toFun (e₁.nodeEquiv.toFun node)) :=
        e₂.node_label_preserved (e₁.nodeEquiv.toFun node)
  node_label_reflected := by
    intro node
    calc
      K.nodeLabel node = H.nodeLabel (e₂.nodeEquiv.invFun node) :=
        e₂.node_label_reflected node
      _ = G.nodeLabel (e₁.nodeEquiv.invFun (e₂.nodeEquiv.invFun node)) :=
        e₁.node_label_reflected (e₂.nodeEquiv.invFun node)
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
  incidence_reflected := by
    intro node
    calc
      (K.incident node).map (Iso.trans e₁.endpointEquiv e₂.endpointEquiv).invFun =
          ((K.incident node).map e₂.endpointEquiv.invFun).map
            e₁.endpointEquiv.invFun := by
        simp [Iso.trans, List.map_map]
      _ = (H.incident (e₂.nodeEquiv.invFun node)).map
            e₁.endpointEquiv.invFun := by
        rw [e₂.incidence_reflected node]
      _ = G.incident (e₁.nodeEquiv.invFun (e₂.nodeEquiv.invFun node)) := by
        rw [e₁.incidence_reflected (e₂.nodeEquiv.invFun node)]

end PortHypergraphIso

namespace OpenPortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/--
State for the boundary-rooted graph-to-syntax traversal.  The pending endpoint
list is ordered, and its labels are exactly the `Diag` frontier index.
-/
structure TraversalState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  seenNode : Fin G.raw.nodeCount → Prop
  processedEdge : Fin G.raw.edgeCount → Prop
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → ¬ processedEdge (G.raw.endpointEdge endpoint)

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

/-- Typed open boundary-connected port-hypergraphs quotiented by ordered
boundary-preserving isomorphism. -/
def OpenPortHypergraphUpToIso (Sig : Signature) (boundary : List Sig.Port) :
    Type :=
  Quotient (OpenPortHypergraph.isoSetoid Sig boundary)

/--
Blueprint for the canonical search procedure.  This structure records the
data that a completed owned traversal must provide; it is not the completed
semantic bridge.
-/
structure CanonicalTraversalBlueprint (Sig : Signature) where
  toGraph :
    ∀ {boundary : List Sig.Port}, Diag Sig boundary → OpenPortHypergraph Sig boundary
  fromGraph :
    ∀ {boundary : List Sig.Port}, OpenPortHypergraph Sig boundary → Diag Sig boundary
  from_to :
    ∀ {boundary : List Sig.Port} (d : Diag Sig boundary),
      fromGraph (toGraph d) = d
  to_from :
    ∀ {boundary : List Sig.Port} (G : OpenPortHypergraph Sig boundary),
      OpenPortHypergraph.isoRel (toGraph (fromGraph G)) G
  from_isoRel :
    ∀ {boundary : List Sig.Port} {G H : OpenPortHypergraph Sig boundary},
      OpenPortHypergraph.isoRel G H → fromGraph G = fromGraph H

/-- A completed traversal blueprint induces the quotient semantic isomorphism. -/
def CanonicalTraversalBlueprint.iso (T : CanonicalTraversalBlueprint Sig)
    (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary where
  toFun d := Quotient.mk (OpenPortHypergraph.isoSetoid Sig boundary) (T.toGraph d)
  invFun q :=
    Quotient.liftOn q
      (fun G => T.fromGraph G)
      (by
        intro G H h
        exact T.from_isoRel h)
  left_inv := by
    intro d
    exact T.from_to d
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro G
    apply Quotient.sound
    exact T.to_from G

/--
Transport the semantic quotient to the generated traversal-code family.  This
is blueprint-level: constructing the required traversal data is the remaining
semantic bridge obligation below.
-/
def CanonicalTraversalBlueprint.semanticCodeIso (T : CanonicalTraversalBlueprint Sig)
    (boundary : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig boundary ≃ᵢ Diag Sig boundary :=
  Iso.symm (T.iso boundary)

/--
Transport the semantic quotient to the dependent-polynomial initial algebra.
This is blueprint-level and depends on completed canonical traversal data.
-/
def CanonicalTraversalBlueprint.semanticMuIso (T : CanonicalTraversalBlueprint Sig)
    (boundary : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig boundary ≃ᵢ Mu (poly Sig) boundary :=
  Iso.trans (T.semanticCodeIso boundary) (Iso.symm (syntaxIso Sig boundary))

/--
UNFINISHED semantic bridge: typed rooted open diagrams should present exactly
the finite typed open endpoint/edge/node port-hypergraphs whose edges and
nodes are labeled, whose external boundary endpoints are ordered, and whose
constructors lie in components connected to that ordered boundary, up to
ordered boundary-preserving isomorphism.  The proof must instantiate a
canonical search procedure whose unique traversal order supplies the canonical
edge and node labels used for linear isomorphism testing.
-/
def diagOpenPortHypergraphIso (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary := by
  sorry

end StringDiagram
end BijForm
