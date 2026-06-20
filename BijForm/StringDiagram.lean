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

/--
A typed ordered-port string-diagram signature.

`Edge` is the label carried by wires/edges.  `Port` is the label carried by
open frontier endpoints.  Unoriented signatures usually take `Port` to be the
same type as `Edge`.  Oriented signatures usually take `Port` to be a direction
paired with an edge type.  `portEdge` forgets endpoint-only data,
`compatible` states when two frontier endpoints may be joined, and
`compatible_edge` ensures such a connection has one edge label.

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
endpoint is incident to exactly one edge.
-/

/--
A finite typed port-hypergraph representative with an ordered external
boundary.  Endpoints carry endpoint labels, edges carry wire labels, nodes
carry constructor labels, and every constructor incidence points to an ordered
constructor port.
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
  endpoint_covered :
    ∀ endpoint : Fin endpointCount,
      (∃ boundaryIndex : Fin boundary.length,
        boundaryPort boundaryIndex = endpoint) ∨
      ∃ (node : Fin nodeCount) (slot : Fin (incident node).length),
        (incident node).get slot = endpoint

namespace PortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

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
The formal boundary for the canonical search procedure.  A full procedure
must choose the unique boundary-rooted traversal order for each open
port-hypergraph and render syntax back to representatives, with inverse laws
modulo ordered boundary-preserving isomorphism.
-/
structure CanonicalTraversal (Sig : Signature) where
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

/-- A canonical traversal procedure induces the quotient semantic isomorphism. -/
def CanonicalTraversal.iso (T : CanonicalTraversal Sig)
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
is conditional on supplied canonical traversal data; constructing such data is
the remaining semantic bridge obligation below.
-/
def CanonicalTraversal.semanticCodeIso (T : CanonicalTraversal Sig)
    (boundary : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig boundary ≃ᵢ Diag Sig boundary :=
  Iso.symm (T.iso boundary)

/--
Transport the semantic quotient to the dependent-polynomial initial algebra.
This is the semantic quotient's initial-algebra presentation, conditional on a
canonical traversal.
-/
def CanonicalTraversal.semanticMuIso (T : CanonicalTraversal Sig)
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
