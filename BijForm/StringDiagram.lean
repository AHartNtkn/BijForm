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

theorem map_eraseFin {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Fin xs.length),
      (eraseFin xs i).map f =
        eraseFin (xs.map f) (Fin.cast (by simp) i)
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => by
      change xs.map f = xs.map f
      rfl
  | x :: xs, ⟨n + 1, h⟩ => by
      have ih := map_eraseFin f xs ⟨n, Nat.lt_of_succ_lt_succ h⟩
      simp [eraseFin, ih]

theorem mem_of_mem_eraseFin {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length) {x : α},
      x ∈ eraseFin xs i → x ∈ xs
  | [], i, _x, _hmem => nomatch i
  | y :: _ys, ⟨0, _⟩, x, hmem => by
      right
      simpa [eraseFin] using hmem
  | y :: ys, ⟨n + 1, h⟩, x, hmem => by
      simp [eraseFin] at hmem
      rcases hmem with hxy | htail
      · simp [hxy]
      · have htailOrig :
            x ∈ ys :=
          mem_of_mem_eraseFin ys ⟨n, Nat.lt_of_succ_lt_succ h⟩ htail
        simp [htailOrig]

theorem get_not_mem_eraseFin_of_nodup {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      xs.Nodup → xs.get i ∉ eraseFin xs i
  | [], i, _hnodup => nomatch i
  | head :: xs, ⟨0, _⟩, hnodup => by
      have hsplit : head ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simpa [eraseFin] using hsplit.1
  | x :: xs, ⟨n + 1, h⟩, hnodup => by
      intro hmem
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simp [eraseFin] at hmem
      rcases hmem with hhead | htail
      · exact hsplit.1 (by
          rw [← hhead]
          exact List.get_mem xs ⟨n, Nat.lt_of_succ_lt_succ h⟩)
      · exact get_not_mem_eraseFin_of_nodup xs
          ⟨n, Nat.lt_of_succ_lt_succ h⟩ hsplit.2 htail

theorem nodup_eraseFin {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      xs.Nodup → (eraseFin xs i).Nodup
  | [], i, _hnodup => nomatch i
  | head :: xs, ⟨0, _⟩, hnodup => by
      have hsplit : head ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simpa [eraseFin] using hsplit.2
  | x :: xs, ⟨n + 1, h⟩, hnodup => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      have htail :
          (eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩).Nodup :=
        nodup_eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ hsplit.2
      have hnot :
          x ∉ eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ := by
        intro hmem
        exact hsplit.1
          (mem_of_mem_eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ hmem)
      simp [eraseFin, hnot, htail]

theorem eraseFin_eq_of_eq {α : Type} {xs ys : List α}
    (hxy : xs = ys) (i : Fin xs.length) :
    eraseFin xs i =
      eraseFin ys (Fin.cast (by rw [← hxy]) i) := by
  cases hxy
  simp

theorem nodup_append_of_nodup_disjoint {α : Type} :
    ∀ (xs ys : List α),
      xs.Nodup →
      ys.Nodup →
      (∀ x : α, x ∈ xs → x ∈ ys → False) →
        (xs ++ ys).Nodup
  | [], ys, _hxs, hys, _hdisjoint => by
      simpa
  | x :: xs, ys, hxs, hys, hdisjoint => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hxs
      constructor
      · intro a hmem heq
        simp at hmem
        rcases hmem with hmemXs | hmemYs
        · exact hsplit.1 (by simpa [heq] using hmemXs)
        · exact hdisjoint x (by simp) (by simpa [heq] using hmemYs)
      · exact nodup_append_of_nodup_disjoint xs ys hsplit.2 hys
          (by
            intro a hmemXs hmemYs
            exact hdisjoint a (by simp [hmemXs]) hmemYs)

theorem list_exists_get_of_mem {α : Type} {x : α} :
    ∀ (xs : List α), x ∈ xs → ∃ i : Fin xs.length, xs.get i = x
  | [], h => by cases h
  | y :: ys, h => by
      simp at h
      rcases h with h | h
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simp [h]
      · rcases list_exists_get_of_mem ys h with ⟨i, hi⟩
        refine ⟨⟨i.val + 1, by simp [i.isLt]⟩, ?_⟩
        exact hi

theorem findSome?_exists_of_mem_isSome {α β : Type}
    (xs : List α) (f : α → Option β) {x : α}
    (hmem : x ∈ xs) (hxs : (f x).isSome) :
    ∃ y : β, xs.findSome? f = some y := by
  cases hfind : xs.findSome? f with
  | some y =>
      exact ⟨y, rfl⟩
  | none =>
      have hall := (List.findSome?_eq_none_iff).mp hfind
      have hxnone := hall x hmem
      rw [hxnone] at hxs
      simp at hxs

theorem list_mem_tail_of_mem_cons_ne {α : Type} {head x : α} {tail : List α}
    (hmem : x ∈ head :: tail) (hne : head ≠ x) : x ∈ tail := by
  simp at hmem
  rcases hmem with h | h
  · exact False.elim (hne h.symm)
  · exact h

theorem list_nodup_ofFn_injective {α : Type} {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ]
      constructor
      · intro a hmem heq
        rw [List.mem_ofFn] at hmem
        rcases hmem with ⟨i, hi⟩
        have hidx : i.succ = (0 : Fin (n + 1)) :=
          hf (hi.trans heq.symm)
        exact False.elim ((Fin.succ_ne_zero i) hidx)
      · apply ih
        intro i j hij
        have hidx : i.succ = j.succ := hf hij
        exact (Fin.succ_inj.mp hidx)

theorem list_ofFn_get {α : Type} (xs : List α) :
    List.ofFn (fun i : Fin xs.length => xs.get i) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.getElem_ofFn]

theorem list_nodup_of_get_injective {α : Type} (xs : List α)
    (hf : Function.Injective fun i : Fin xs.length => xs.get i) :
    xs.Nodup := by
  have hnodup :
      (List.ofFn (fun i : Fin xs.length => xs.get i)).Nodup :=
    list_nodup_ofFn_injective
      (fun i : Fin xs.length => xs.get i) hf
  rw [list_ofFn_get xs] at hnodup
  exact hnodup

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

/-- Type-level wrapper for executable edge-mate checks. -/
structure EdgeMateData (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Type where
  proof : EdgeMate G endpoint mate

/-- Check whether a concrete endpoint is the edge mate of another endpoint. -/
def edgeMateCandidate? (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) :
    Option (EdgeMateData G endpoint mate) :=
  if hsame : endpoint = mate then
    none
  else if hedge : G.endpointEdge endpoint = G.endpointEdge mate then
    some ⟨⟨hsame, hedge⟩⟩
  else
    none

theorem edgeMateCandidate?_isSome_of_edgeMate (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    (edgeMateCandidate? G endpoint mate).isSome := by
  simp [edgeMateCandidate?, hmate.1, hmate.2]

/-- Search the finite endpoint set for the mate of a concrete endpoint. -/
def edgeMateSearch? (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    Option { mate : Fin G.endpointCount // EdgeMate G endpoint mate } :=
  (List.finRange G.endpointCount).findSome? fun mate =>
    match edgeMateCandidate? G endpoint mate with
    | some hmate => some ⟨mate, hmate.proof⟩
    | none => none

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

theorem incident_nodup (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).Nodup :=
  list_nodup_of_get_injective (G.incident node) (G.incident_injective node)

theorem incident_labels (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).map G.endpointLabel =
      Sig.nodePorts (G.nodeLabel node) := by
  apply List.ext_getElem
  · simp [Signature.nodePorts, G.incident_length node]
  · intro i hleft hright
    rw [List.getElem_map]
    have hslot : i < (G.incident node).length := by
      simpa using hleft
    have hinc := G.incidence_label node ⟨i, hslot⟩
    simpa [Signature.nodePorts] using hinc

theorem incident_labels_except (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    (eraseFin (G.incident node) slot).map G.endpointLabel =
      Sig.nodePortsExcept (G.nodeLabel node)
        (Fin.cast (G.incident_length node) slot) := by
  calc
    (eraseFin (G.incident node) slot).map G.endpointLabel =
        eraseFin ((G.incident node).map G.endpointLabel)
          (Fin.cast (by simp) slot) :=
      map_eraseFin G.endpointLabel (G.incident node) slot
    _ = Sig.nodePortsExcept (G.nodeLabel node)
          (Fin.cast (G.incident_length node) slot) := by
      have hlabels := G.incident_labels node
      rw [eraseFin_eq_of_eq hlabels]
      simp [Signature.nodePortsExcept, Signature.nodePorts]

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

namespace TraversalState

/--
The completeness invariant missing from the current traversal proof.  Every
unprocessed boundary endpoint, and every unprocessed endpoint of an already
seen constructor, must occur in the ordered pending frontier.
-/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : TraversalState G frontier) : Prop :=
  ∀ endpoint : Fin G.raw.endpointCount,
    ¬ st.processedEdge (G.raw.endpointEdge endpoint) →
      ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length),
        PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
          match owner with
          | .boundary _ => endpoint ∈ st.pending
          | .constructor node _ => st.seenNode node → endpoint ∈ st.pending

end TraversalState

/--
Finite, data-carrying state for the owned graph-to-syntax search.

`TraversalState` is the proof-level invariant surface.  `SearchState` keeps the
same pending frontier together with finite lists of seen constructors and
processed edges, so a later traversal implementation can make constructor
choices as data and then project those choices back to the proof-level
invariants.
-/
structure SearchState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  pending_nodup : pending.Nodup
  seenNodes : List (Fin G.raw.nodeCount)
  processedEdges : List (Fin G.raw.edgeCount)
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → G.raw.endpointEdge endpoint ∉ processedEdges
  pending_owner_seen :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending →
        ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length),
          PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
            match owner with
            | .boundary _ => True
            | .constructor node _ => node ∈ seenNodes
  unseen_incident_unprocessed :
    ∀ node : Fin G.raw.nodeCount,
      node ∉ seenNodes →
        ∀ slot : Fin (G.raw.incident node).length,
          G.raw.endpointEdge ((G.raw.incident node).get slot) ∉ processedEdges

namespace SearchState

def seenNode {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (node : Fin G.raw.nodeCount) : Prop :=
  node ∈ st.seenNodes

def processedEdge {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (edge : Fin G.raw.edgeCount) : Prop :=
  edge ∈ st.processedEdges

def toTraversalState {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    TraversalState G frontier where
  pending := st.pending
  pending_labels := st.pending_labels
  seenNode := st.seenNode
  processedEdge := st.processedEdge
  pending_unprocessed := by
    intro endpoint hpending hprocessed
    exact st.pending_unprocessed endpoint hpending hprocessed

/-- Proof-level frontier completeness for a finite search state. -/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop :=
  st.toTraversalState.FrontierComplete

/-- Initial finite search state: the ordered boundary endpoints are pending. -/
def initial (G : OpenPortHypergraph Sig boundary) : SearchState G boundary where
  pending := List.ofFn G.raw.boundaryPort
  pending_labels := by
    apply List.ext_getElem
    · simp [List.length_ofFn]
    · intro i hleft hright
      rw [List.getElem_map]
      rw [List.getElem_ofFn]
      exact G.raw.boundary_label ⟨i, hright⟩
  pending_nodup :=
    list_nodup_ofFn_injective G.raw.boundaryPort G.raw.boundary_injective
  seenNodes := []
  processedEdges := []
  pending_unprocessed := by
    intro _endpoint _hpending
    simp
  pending_owner_seen := by
    intro endpoint hpending owner howner
    rw [List.mem_ofFn] at hpending
    rcases hpending with ⟨boundaryIndex, hboundary⟩
    cases owner with
    | boundary _ =>
        trivial
    | constructor node slot =>
        have hboundaryOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = endpoint := by
          exact hboundary
        have hconstructorOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = endpoint := howner
        rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
        have hboundaryEq :
            (.boundary boundaryIndex :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hboundaryOwner
        have hconstructorEq :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
        have himpossible :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) =
              .boundary boundaryIndex := by
          exact hconstructorEq.trans hboundaryEq.symm
        cases himpossible
  unseen_incident_unprocessed := by
    intro _node _hunseen _slot
    simp

theorem initial_frontierComplete (G : OpenPortHypergraph Sig boundary) :
    (initial G).FrontierComplete := by
  intro endpoint _hunprocessed owner howner
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          G.raw.boundaryPort boundaryIndex = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      have hmem :
          G.raw.boundaryPort boundaryIndex ∈ List.ofFn G.raw.boundaryPort :=
        (List.mem_ofFn).mpr ⟨boundaryIndex, rfl⟩
      rw [hownerEndpoint] at hmem
      simpa [FrontierComplete, toTraversalState, initial] using hmem
  | constructor node _slot =>
      intro hseen
      simp [toTraversalState, initial, seenNode] at hseen

theorem pending_cons_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    (active :: rest).Nodup := by
  simpa [hpending] using st.pending_nodup

theorem active_not_mem_rest {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    active ∉ rest := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.1

theorem rest_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.Nodup := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.2

theorem pending_labels_cons {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel ∧
      rest.map G.raw.endpointLabel = restLabels := by
  have hlabels :
      (active :: rest).map G.raw.endpointLabel =
        activeLabel :: restLabels := by
    simpa [hpending] using st.pending_labels
  simpa using hlabels

theorem active_label_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel :=
  (st.pending_labels_cons hpending).1

theorem rest_labels_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.map G.raw.endpointLabel = restLabels :=
  (st.pending_labels_cons hpending).2

def restLabelIndex {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) : Fin restLabels.length :=
  let hrest := st.rest_labels_eq hpending
  Fin.cast (by
    rw [← hrest]
    simp) mate

theorem restLabelIndex_get {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) :
    restLabels.get (st.restLabelIndex hpending mate) =
      G.raw.endpointLabel (rest.get mate) := by
  have hrest := st.rest_labels_eq hpending
  cases hrest
  simp [restLabelIndex]

theorem constructor_seen_of_pending {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    {endpoint : Fin G.raw.endpointCount}
    (hpending : endpoint ∈ st.pending)
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    (howner :
      PortHypergraph.endpointOwnerEndpoint G.raw (.constructor node slot) =
        endpoint) :
    node ∈ st.seenNodes :=
  st.pending_owner_seen endpoint hpending (.constructor node slot) howner

end SearchState

/--
The local step condition needed by the first-pending traversal.  For the
active endpoint and the remaining ordered pending endpoints, the edge mate must
either already be in the remaining pending list, giving a `connect`, or be an
ordered port of an unseen constructor, giving a `bud`.
-/
def FirstPendingStepReady (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Prop :=
  (∃ mate : Fin rest.length,
    PortHypergraph.EdgeMate G.raw active (rest.get mate)) ∨
  (∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length),
    PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot) ∧
      ¬ seenNode node)

/--
Data for one first-pending traversal step.  This is the constructor-level
choice object that `Diag` construction needs: either the active endpoint
connects to a later pending endpoint, or it enters an unseen constructor at an
ordered slot.
-/
inductive FirstPendingStep (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Type where
  | connect
      (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
      FirstPendingStep G seenNode active rest
  | bud
      (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (unseen : ¬ seenNode node) :
      FirstPendingStep G seenNode active rest

namespace FirstPendingStep

theorem ready {G : OpenPortHypergraph Sig boundary}
    {seenNode : Fin G.raw.nodeCount → Prop}
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (step : FirstPendingStep G seenNode active rest) :
    FirstPendingStepReady G seenNode active rest := by
  cases step with
  | connect mate hmate =>
      exact Or.inl ⟨mate, hmate⟩
  | bud node slot hmate unseen =>
      exact Or.inr ⟨node, slot, hmate, unseen⟩

end FirstPendingStep

namespace SearchState

theorem connect_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    Sig.compatible activeLabel
      (restLabels.get (st.restLabelIndex hpending mate)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hmateLabel := st.restLabelIndex_get hpending mate
  rw [hactive] at hcompat
  rw [← hmateLabel] at hcompat
  exact hcompat

def budEntry {G : OpenPortHypergraph Sig boundary}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length) :
    Fin (Sig.arity (G.raw.nodeLabel node)) :=
  Fin.cast (G.raw.incident_length node) slot

theorem bud_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)) :
    Sig.compatible activeLabel
      (Sig.port (G.raw.nodeLabel node) (budEntry node slot)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hslot := G.raw.incidence_label node slot
  rw [hactive] at hcompat
  rw [hslot] at hcompat
  exact hcompat

def connectChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    SearchState G (eraseFin restLabels (st.restLabelIndex hpending mate)) where
  pending := eraseFin rest mate
  pending_labels := by
    calc
      (eraseFin rest mate).map G.raw.endpointLabel =
          eraseFin (rest.map G.raw.endpointLabel) (Fin.cast (by simp) mate) :=
        map_eraseFin G.raw.endpointLabel rest mate
      _ = eraseFin restLabels (st.restLabelIndex hpending mate) := by
        have hrest := st.rest_labels_eq hpending
        cases hrest
        simp [restLabelIndex]
  pending_nodup :=
    nodup_eraseFin rest mate (st.rest_nodup hpending)
  seenNodes := st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        exact st.active_not_mem_rest hpending (by
          simpa [hactiveEndpoint] using hrestMem)
      have hendpointMate : endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmateNotMem :
          rest.get mate ∉ eraseFin rest mate :=
        get_not_mem_eraseFin_of_nodup rest mate (st.rest_nodup hpending)
      exact hmateNotMem (by simpa [hendpointMate] using hmem)
    · exact st.pending_unprocessed endpoint hstPending hold
  pending_owner_seen := by
    intro endpoint hmem owner howner
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    exact st.pending_owner_seen endpoint hstPending owner howner
  unseen_incident_unprocessed := by
    intro node hunseen slot hprocessed
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · let endpoint := (G.raw.incident node).get slot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hownerActive :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = active := by
          change (G.raw.incident node).get slot = active
          exact hactiveEndpoint.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending hownerActive
        exact hunseen hseen
      have hendpointMate :
          endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmatePending : rest.get mate ∈ st.pending := by
        rw [hpending]
        right
        exact List.get_mem rest mate
      have hownerMate :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = rest.get mate := by
        change (G.raw.incident node).get slot = rest.get mate
        exact hendpointMate
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hmatePending hownerMate
      exact hunseen hseen
    · exact st.unseen_incident_unprocessed node hunseen slot hold

def budChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    SearchState G
      (restLabels ++
        Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot)) where
  pending := rest ++ eraseFin (G.raw.incident node) slot
  pending_labels := by
    calc
      (rest ++ eraseFin (G.raw.incident node) slot).map
          G.raw.endpointLabel =
          rest.map G.raw.endpointLabel ++
            (eraseFin (G.raw.incident node) slot).map G.raw.endpointLabel := by
        simp
      _ = restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot) := by
        rw [st.rest_labels_eq hpending,
          G.raw.incident_labels_except node slot]
        rfl
  pending_nodup := by
    apply nodup_append_of_nodup_disjoint
    · exact st.rest_nodup hpending
    · exact nodup_eraseFin (G.raw.incident node) slot
        (G.raw.incident_nodup node)
    · intro endpoint hrest hnew
      have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnew
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      have howner :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot') = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hstPending howner
      exact hunseen hseen
  seenNodes := node :: st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    simp at hmem
    simp at hprocessed
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          exact st.active_not_mem_rest hpending (by
            simpa [hactiveEndpoint] using hrest)
        have hendpointMate :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hstPending (by
            change (G.raw.incident node).get slot = endpoint
            exact hendpointMate.symm)
        exact hunseen hseen
      · exact st.pending_unprocessed endpoint hstPending hold
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          have hactivePending : active ∈ st.pending := by
            rw [hpending]
            simp
          have hseen : node ∈ st.seenNodes :=
            st.constructor_seen_of_pending hactivePending (by
              change (G.raw.incident node).get slot' = active
              exact hslot'.trans hactiveEndpoint.symm)
          exact hunseen hseen
        have hendpointEntry :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hentryNotMem :
            (G.raw.incident node).get slot ∉
              eraseFin (G.raw.incident node) slot :=
          get_not_mem_eraseFin_of_nodup (G.raw.incident node) slot
            (G.raw.incident_nodup node)
        exact hentryNotMem (by simpa [hendpointEntry] using hnewEndpoint)
      · have holdSlot :
            G.raw.endpointEdge ((G.raw.incident node).get slot') ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hunseen slot'
        exact holdSlot (by
          rw [hslot']
          exact hold)
  pending_owner_seen := by
    intro endpoint hmem owner howner
    simp at hmem
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hseen : ownerNode ∈ st.seenNodes :=
            st.constructor_seen_of_pending hstPending howner
          simp [hseen]
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hconstructorOwner :
              PortHypergraph.endpointOwnerEndpoint G.raw
                  (.constructor node slot') = endpoint := by
            simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
          rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
          have hnewEq :
              (.constructor node slot' :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
          have hownerEq :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using howner
          have hsame :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) =
                .constructor node slot' := hownerEq.trans hnewEq.symm
          cases hsame
          simp
  unseen_incident_unprocessed := by
    intro otherNode hotherUnseen otherSlot hprocessed
    have hotherNotSeen : otherNode ∉ st.seenNodes := by
      intro hseen
      exact hotherUnseen (by simp [hseen])
    simp at hprocessed
    rcases hprocessed with hnewProcessed | hold
    · let endpoint := (G.raw.incident otherNode).get otherSlot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hseen : otherNode ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending (by
            change (G.raw.incident otherNode).get otherSlot = active
            exact hactiveEndpoint.symm)
        exact hotherNotSeen hseen
      have hendpointEntry :
          endpoint = (G.raw.incident node).get slot := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
          huniq ((G.raw.incident node).get slot) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hownerOther :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor otherNode otherSlot) =
            endpoint := rfl
      have hownerNode :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) =
            endpoint := by
        change (G.raw.incident node).get slot = endpoint
        exact hendpointEntry.symm
      rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
      have hotherEq :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerOther
      have hnodeEq :
          (.constructor node slot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerNode
      have hsame :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) =
            .constructor node slot := hotherEq.trans hnodeEq.symm
      cases hsame
      exact hotherUnseen (by simp)
    · exact st.unseen_incident_unprocessed otherNode hotherNotSeen otherSlot hold

end SearchState

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

end SearchState

/--
The global traversal-readiness invariant for an open representative.  It is
the missing totality statement for the owned graph-to-`Diag` search: every
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
Initial completeness and step preservation are the remaining state-invariant
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
UNFINISHED semantic bridge: typed rooted open diagrams should present exactly
the finite typed open endpoint/edge/node port-hypergraphs whose edges and
nodes are labeled, whose external boundary endpoints are ordered, and whose
constructors lie in components connected to that ordered boundary, up to
ordered boundary-preserving isomorphism.  The proof must instantiate a
canonical search procedure whose unique traversal order supplies the canonical
edge and node labels used for linear isomorphism testing.  The immediate
blockers are initial/step preservation of
`OpenPortHypergraph.TraversalState.FrontierComplete`, renderer validity, and
the renderer/traversal inverse laws.
-/
def diagOpenPortHypergraphIso (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary := by
  sorry

end StringDiagram
end BijForm
