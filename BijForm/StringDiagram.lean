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

`Port` is the label carried by open frontier endpoints.  Unoriented signatures
usually take `Port` to be a wire type.  Oriented signatures usually take `Port`
to be a direction paired with a wire type.  `compatible` states when two
frontier endpoints may be joined.

Each node label has a finite ordered list of ports, represented by `arity` and
`port`.  The order is part of the formal data because the canonical traversal
and linear isomorphism test depend on it.
-/
structure Signature where
  Port : Type
  Node : Type
  arity : Node → Nat
  port : (node : Node) → Fin (arity node) → Port
  compatible : Port → Port → Prop

namespace Unoriented

/-- Build an unoriented signature: endpoint compatibility is equality of wire
types, while every constructor still has an ordered list of typed ports. -/
def signature (Ty Node : Type)
    (arity : Node → Nat)
    (portTy : (node : Node) → Fin (arity node) → Ty) :
    Signature where
  Port := Ty
  Node := Node
  arity := arity
  port := portTy
  compatible := Eq

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
  Port := Endpoint Ty
  Node := Node
  arity := arity
  port := portSpec
  compatible := fun p q =>
    p.ty = q.ty ∧ Direction.opposite p.direction = q.direction

end Oriented

/-- Constructor tags for the traversal grammar. -/
inductive Ctor where
  | finish
  | connect
  | bud
deriving DecidableEq, Repr

namespace Signature

variable (Sig : Signature)

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

/--
A finite typed port-hypergraph representative with an ordered external
boundary.  The finite ports carry endpoint labels, nodes carry constructor
labels, and every constructor incidence points to an ordered constructor port.
-/
structure PortHypergraph (Sig : Signature) (boundary : List Sig.Port) where
  portCount : Nat
  nodeCount : Nat
  portLabel : Fin portCount → Sig.Port
  boundaryPort : Fin boundary.length → Fin portCount
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length, portLabel (boundaryPort b) = boundary.get b
  nodeLabel : Fin nodeCount → Sig.Node
  incident :
    (node : Fin nodeCount) →
      Fin (Sig.arity (nodeLabel node)) → Fin portCount
  incidence_compatible :
    ∀ (node : Fin nodeCount) (slot : Fin (Sig.arity (nodeLabel node))),
      Sig.compatible (portLabel (incident node slot)) (Sig.port (nodeLabel node) slot)

namespace PortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/--
A port has a path to the ordered boundary when it is a boundary port or can be
reached by moving across the ordered incidences of a constructor already in the
same component.
-/
inductive PortReachesBoundary (G : PortHypergraph Sig boundary) :
    Fin G.portCount → Prop
  | boundary (b : Fin boundary.length) :
      PortReachesBoundary G (G.boundaryPort b)
  | throughConstructor {p q : Fin G.portCount}
      (node : Fin G.nodeCount)
      (fromSlot toSlot : Fin (Sig.arity (G.nodeLabel node)))
      (hp : G.incident node fromSlot = p)
      (hq : G.incident node toSlot = q)
      (reach : PortReachesBoundary G p) :
      PortReachesBoundary G q

/-- Every constructor is in some component connected to the external boundary. -/
def AllConstructorsReachBoundary (G : PortHypergraph Sig boundary) : Prop :=
  ∀ node : Fin G.nodeCount,
    ∃ slot : Fin (Sig.arity (G.nodeLabel node)),
      PortReachesBoundary G (G.incident node slot)

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
ports and nodes, preserves the ordered boundary pointwise, preserves port and
node labels, and preserves every ordered constructor-port incidence.
-/
structure PortHypergraphIso {Sig : Signature} {boundary : List Sig.Port}
    (G H : PortHypergraph Sig boundary) where
  portEquiv : Fin G.portCount ≃ᵢ Fin H.portCount
  nodeEquiv : Fin G.nodeCount ≃ᵢ Fin H.nodeCount
  boundary_preserved :
    ∀ b : Fin boundary.length, portEquiv.toFun (G.boundaryPort b) = H.boundaryPort b
  port_label_preserved :
    ∀ p : Fin G.portCount, G.portLabel p = H.portLabel (portEquiv.toFun p)
  node_label_preserved :
    ∀ node : Fin G.nodeCount,
      G.nodeLabel node = H.nodeLabel (nodeEquiv.toFun node)
  incidence_preserved :
    ∀ node : Fin G.nodeCount,
      ∀ slot : Fin (Sig.arity (G.nodeLabel node)),
        portEquiv.toFun (G.incident node slot) =
          H.incident (nodeEquiv.toFun node)
            (Fin.cast (by rw [node_label_preserved node]) slot)

namespace PortHypergraphIso

variable {Sig : Signature} {boundary : List Sig.Port}

def refl (G : PortHypergraph Sig boundary) : PortHypergraphIso G G where
  portEquiv := Iso.refl (Fin G.portCount)
  nodeEquiv := Iso.refl (Fin G.nodeCount)
  boundary_preserved := by
    intro _
    rfl
  port_label_preserved := by
    intro _
    rfl
  node_label_preserved := by
    intro _
    rfl
  incidence_preserved := by
    intro _ _
    rfl

/--
UNFINISHED: inverse finite relabelings should witness symmetry of typed
boundary-preserving port-hypergraph isomorphism.
-/
def symm {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) : PortHypergraphIso H G := by
  sorry

/--
UNFINISHED: composed finite relabelings should witness transitivity of typed
boundary-preserving port-hypergraph isomorphism.
-/
def trans {G H K : PortHypergraph Sig boundary}
    (e₁ : PortHypergraphIso G H) (e₂ : PortHypergraphIso H K) :
    PortHypergraphIso G K := by
  sorry

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
The formal boundary for the canonical search procedure.  A completed procedure
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

/--
UNFINISHED: a canonical traversal procedure should induce the quotient semantic
isomorphism.  The remaining obligation is that boundary-preserving isomorphic
representatives decode to the same canonical traversal syntax.
-/
def CanonicalTraversal.iso (T : CanonicalTraversal Sig)
    (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary where
  toFun d := Quotient.mk (OpenPortHypergraph.isoSetoid Sig boundary) (T.toGraph d)
  invFun q :=
    Quotient.liftOn q
      (fun G => T.fromGraph G)
      (by
        intro G H h
        /-
        UNFINISHED: canonical traversal uniqueness should prove that
        isomorphic representatives decode to the same traversal syntax.
        -/
        sorry)
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
UNFINISHED semantic bridge: typed rooted open diagrams should present exactly
the finite typed open port-hypergraphs whose constructors lie in components
connected to the ordered external boundary, up to ordered boundary-preserving
isomorphism.  The proof must instantiate a canonical search procedure whose
unique traversal order supplies the canonical labels used for linear
isomorphism testing.
-/
def diagOpenPortHypergraphIso (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary := by
  sorry

end StringDiagram
end BijForm
