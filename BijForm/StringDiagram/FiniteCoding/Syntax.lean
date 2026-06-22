import BijForm.CodeAlgebra
import BijForm.FiniteSubtypeTable
import BijForm.StringDiagram.Polynomial

namespace BijForm
namespace StringDiagram

open DepPoly

/-- Constructor entry of a string-diagram signature: a node and one ordered port. -/
abbrev Signature.Entry (Sig : Signature) : Type :=
  Σ node : Sig.Node, Fin (Sig.arity node)

/-- Entries whose constructor has exactly one port. These are base branches from
a one-port frontier because budding them leaves the empty frontier. -/
abbrev Signature.UnaryEntry (Sig : Signature) : Type :=
  { entry : Sig.Entry // Sig.arity entry.1 = 1 }

/-- Entries whose constructor has more than one port. These are recursive
branches from a one-port frontier. -/
abbrev Signature.NonUnaryEntry (Sig : Signature) : Type :=
  { entry : Sig.Entry // Sig.arity entry.1 ≠ 1 }

def Signature.entryValues (Sig : Signature) (nodes : List Sig.Node) :
    List Sig.Entry :=
  nodes.flatMap fun node =>
    List.ofFn fun slot : Fin (Sig.arity node) => ⟨node, slot⟩

theorem Signature.mem_entryValues {Sig : Signature}
    {nodes : List Sig.Node} {entry : Sig.Entry} :
    entry ∈ Sig.entryValues nodes ↔ entry.1 ∈ nodes := by
  rw [Signature.entryValues, List.mem_flatMap]
  constructor
  · intro h
    rcases h with ⟨node, hnode, hentry⟩
    rcases List.mem_ofFn.mp hentry with ⟨slot, hslot⟩
    cases hslot
    exact hnode
  · intro h
    exact ⟨entry.1, h, by
      rw [List.mem_ofFn]
      exact ⟨entry.2, rfl⟩⟩

theorem Signature.entryValues_nodup {Sig : Signature} :
    ∀ nodes : List Sig.Node, nodes.Nodup → (Sig.entryValues nodes).Nodup
  | [], _hnodup => by
      simp [Signature.entryValues]
  | node :: nodes, hnodup => by
      have hsplit : node ∉ nodes ∧ nodes.Nodup := by
        simpa using hnodup
      change
        ((List.ofFn fun slot : Fin (Sig.arity node) =>
              (⟨node, slot⟩ : Sig.Entry)) ++ Sig.entryValues nodes).Nodup
      rw [List.nodup_append]
      refine ⟨?_, Signature.entryValues_nodup nodes hsplit.2, ?_⟩
      · apply list_nodup_ofFn_injective
        intro left right h
        cases h
        rfl
      · intro entry hentry rest hrest heq
        rcases List.mem_ofFn.mp hentry with ⟨slot, hslot⟩
        cases hslot
        cases heq
        exact hsplit.1 (Signature.mem_entryValues.mp hrest)

def Signature.entryDecidableEq {Sig : Signature} [DecidableEq Sig.Node] :
    DecidableEq Sig.Entry
  | ⟨leftNode, leftSlot⟩, ⟨rightNode, rightSlot⟩ =>
      if hnode : leftNode = rightNode then
        by
          cases hnode
          exact if hslot : leftSlot = rightSlot then
            isTrue (by cases hslot; rfl)
          else
            isFalse (by
              intro h
              cases h
              exact hslot rfl)
      else
        isFalse (by
          intro h
          cases h
          exact hnode rfl)

def Signature.entryTable {Sig : Signature} [DecidableEq Sig.Node]
    (nodes : FiniteSubtypeTable Sig.Node (fun _ => True)) :
    FiniteSubtypeTable Sig.Entry (fun _ => True) where
  values := Sig.entryValues nodes.values
  nodup := Signature.entryValues_nodup nodes.values nodes.nodup
  sound := by
    intro _i
    trivial
  complete := by
    intro entry _h
    have hnodeMem : entry.1 ∈ nodes.values := by
      cases hcomplete : nodes.complete entry.1 True.intro with
      | mk i hi =>
          exact hi ▸ List.get_mem nodes.values i
    have hentryMem : entry ∈ Sig.entryValues nodes.values :=
      Signature.mem_entryValues.mpr hnodeMem
    exact @FiniteSubtypeTable.indexOfMem Sig.Entry
      (Signature.entryDecidableEq (Sig := Sig))
      (Sig.entryValues nodes.values) entry hentryMem

def Signature.unaryEntryTable {Sig : Signature} [DecidableEq Sig.Node]
    (entries : FiniteSubtypeTable Sig.Entry (fun _ => True)) :
    FiniteSubtypeTable Sig.Entry (fun entry => Sig.arity entry.1 = 1) :=
  @FiniteSubtypeTable.filterAll Sig.Entry
    (Signature.entryDecidableEq (Sig := Sig)) entries
    (fun entry => Sig.arity entry.1 = 1) _

def Signature.nonUnaryEntryTable {Sig : Signature} [DecidableEq Sig.Node]
    (entries : FiniteSubtypeTable Sig.Entry (fun _ => True)) :
    FiniteSubtypeTable Sig.Entry (fun entry => Sig.arity entry.1 ≠ 1) :=
  @FiniteSubtypeTable.filterAll Sig.Entry
    (Signature.entryDecidableEq (Sig := Sig)) entries
    (fun entry => Sig.arity entry.1 ≠ 1) _

/--
Finite/infinite carrier shape for open frontier diagrams: the empty frontier has
only `finish`, while every nonempty frontier is assigned a natural-number code.
-/
def openFrontierShape (Sig : Signature) :
    List Sig.Port → CodeShape
  | [] => .finite 1
  | _ :: _ => .infinite

def openFrontierEmptyCarrier {Sig : Signature}
    {boundary : List Sig.Port} (h : boundary = []) :
    (openFrontierShape Sig boundary).Carrier := by
  cases h
  exact ⟨0, by decide⟩

theorem openFrontierEmptyCarrier_unique {Sig : Signature}
    {boundary : List Sig.Port} (h : boundary = [])
    (z : (openFrontierShape Sig boundary).Carrier) :
    openFrontierEmptyCarrier (Sig := Sig) h = z := by
  cases h
  exact fin_one_eq _ _

def openFrontierNonemptyIso {Sig : Signature}
    {boundary : List Sig.Port} (h : boundary ≠ []) :
    (openFrontierShape Sig boundary).Carrier ≃ᵢ Nat := by
  cases boundary with
  | nil => exact False.elim (h rfl)
  | cons _ _ => exact CodeShape.infiniteIso rfl

theorem Signature.nodePortsExcept_length
    {Sig : Signature} (node : Sig.Node) (entry : Fin (Sig.arity node)) :
    (Sig.nodePortsExcept node entry).length = Sig.arity node - 1 := by
  simp [Signature.nodePortsExcept, Signature.nodePorts]

theorem Signature.nodePortsExcept_eq_nil_of_arity_one
    {Sig : Signature} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    (h : Sig.arity node = 1) :
    Sig.nodePortsExcept node entry = [] := by
  have hlen : (Sig.nodePortsExcept node entry).length = 0 := by
    simp [Signature.nodePortsExcept_length, h]
  cases hports : Sig.nodePortsExcept node entry with
  | nil => rfl
  | cons _ _ =>
      simp [hports] at hlen

theorem Signature.nodePortsExcept_ne_nil_of_arity_ne_one
    {Sig : Signature} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    (hpos : 0 < Sig.arity node) (hne : Sig.arity node ≠ 1) :
    Sig.nodePortsExcept node entry ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [Signature.nodePortsExcept_length] at hlen
  omega

theorem eraseFin_ne_nil_of_length_gt_one
    {α : Type} {xs : List α} (i : Fin xs.length)
    (h : 1 < xs.length) :
    eraseFin xs i ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [eraseFin_length] at hlen
  omega

/--
Reusable finite data for single-sorted string-diagram coding.

The equivalences are the branch tables the compiler needs: all constructor
entries, one-port/base entries, and one-port/recursive entries. The arity bound
is used by the generic rank measure for bud branches.
-/
structure SingleSortedFiniteCodingData (Sig : Signature) where
  compatibleAll : ∀ left right : Sig.Port, Sig.compatible left right
  rankScale : Nat
  arity_lt_rankScale : ∀ node : Sig.Node, Sig.arity node < rankScale
  unaryCount : Nat
  unaryCount_pos : 0 < unaryCount
  unaryIso : Sig.UnaryEntry ≃ᵢ Fin unaryCount
  nonUnaryCount : Nat
  nonUnaryCount_pos : 0 < nonUnaryCount
  nonUnaryIso : Sig.NonUnaryEntry ≃ᵢ Fin nonUnaryCount

namespace SingleSortedFiniteCodingData

def ofEntryTable {Sig : Signature} [DecidableEq Sig.Node]
    (entries : FiniteSubtypeTable Sig.Entry (fun _ => True))
    (compatibleAll : ∀ left right : Sig.Port, Sig.compatible left right)
    (rankScale : Nat)
    (arity_lt_rankScale : ∀ node : Sig.Node, Sig.arity node < rankScale)
    (unaryCount_pos :
      0 < (Signature.unaryEntryTable (Sig := Sig) entries).values.length)
    (nonUnaryCount_pos :
      0 < (Signature.nonUnaryEntryTable (Sig := Sig) entries).values.length) :
    SingleSortedFiniteCodingData Sig where
  compatibleAll := compatibleAll
  rankScale := rankScale
  arity_lt_rankScale := arity_lt_rankScale
  unaryCount := (Signature.unaryEntryTable (Sig := Sig) entries).values.length
  unaryCount_pos := unaryCount_pos
  unaryIso := (Signature.unaryEntryTable (Sig := Sig) entries).iso
  nonUnaryCount := (Signature.nonUnaryEntryTable (Sig := Sig) entries).values.length
  nonUnaryCount_pos := nonUnaryCount_pos
  nonUnaryIso := (Signature.nonUnaryEntryTable (Sig := Sig) entries).iso

def ofNodeTable {Sig : Signature} [DecidableEq Sig.Node]
    (nodes : FiniteSubtypeTable Sig.Node (fun _ => True))
    (compatibleAll : ∀ left right : Sig.Port, Sig.compatible left right)
    (rankScale : Nat)
    (arity_lt_rankScale : ∀ node : Sig.Node, Sig.arity node < rankScale)
    (unaryCount_pos :
      0 < (Signature.unaryEntryTable (Sig := Sig)
        (Signature.entryTable (Sig := Sig) nodes)).values.length)
    (nonUnaryCount_pos :
      0 < (Signature.nonUnaryEntryTable (Sig := Sig)
        (Signature.entryTable (Sig := Sig) nodes)).values.length) :
    SingleSortedFiniteCodingData Sig :=
  ofEntryTable
    (Sig := Sig)
    (Signature.entryTable (Sig := Sig) nodes)
    compatibleAll
    rankScale
    arity_lt_rankScale
    unaryCount_pos
    nonUnaryCount_pos

variable {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)

def entryTag : Type :=
  Fin (data.unaryCount + data.nonUnaryCount)

def entryPartitionIso :
    Sig.Entry ≃ᵢ (Fin data.unaryCount ⊕ Fin data.nonUnaryCount) :=
  Iso.subtypePartition
    (fun entry : Sig.Entry => Sig.arity entry.1 = 1)
    data.unaryIso
    data.nonUnaryIso

def entryIso : Sig.Entry ≃ᵢ data.entryTag :=
  Iso.trans data.entryPartitionIso
    (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount)

end SingleSortedFiniteCodingData

@[simp] private def openBoundaryCases {Sig : Signature}
    {motive : List Sig.Port → Sort _}
    (empty : motive [])
    (one : ∀ active, motive [active])
    (two : ∀ active first, motive [active, first])
    (many : ∀ active first second rest,
      motive (active :: first :: second :: rest)) :
    ∀ boundary, motive boundary
  | [] => empty
  | active :: [] => one active
  | active :: first :: [] => two active first
  | active :: first :: second :: rest => many active first second rest

/-- The one-step branch shape generated from finite single-sorted signature data. -/
def singleSortedFiniteLayerShape
    {Sig : Signature} (_data : SingleSortedFiniteCodingData Sig) :
    List Sig.Port → Type :=
  openBoundaryCases
    (motive := fun _ => Type)
    (Fin 1)
    (fun _active =>
      Sig.UnaryEntry ⊕ (Sig.NonUnaryEntry × Nat))
    (fun _active _first =>
      Fin 1 ⊕ (Sig.Entry × Nat))
    (fun _active first second rest =>
      (Fin (first :: second :: rest).length × Nat) ⊕
        (Sig.Entry × Nat))

/-- Carrier isomorphism for the generated one-step branch shape. -/
def singleSortedFiniteLayerShapeCarrierIso
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary ≃ᵢ
        (openFrontierShape Sig boundary).Carrier :=
  openBoundaryCases
    (motive := fun boundary =>
      singleSortedFiniteLayerShape data boundary ≃ᵢ
        (openFrontierShape Sig boundary).Carrier)
    (Iso.refl (Fin 1))
    (fun _active =>
      Iso.trans
        (Iso.sum data.unaryIso
          (Iso.prod data.nonUnaryIso (Iso.refl Nat)))
        (CodeAlgebra.finiteRecursiveNat
          data.unaryCount data.nonUnaryCount data.nonUnaryCount_pos))
    (fun _active _first =>
      Iso.trans
        (Iso.sum (Iso.refl (Fin 1))
          (Iso.prod data.entryIso (Iso.refl Nat)))
        (CodeAlgebra.finiteRecursiveNat 1
          (data.unaryCount + data.nonUnaryCount)
          (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)))
    (fun _active first second rest =>
      Iso.trans
        (Iso.sum (Iso.refl (Fin (first :: second :: rest).length × Nat))
          (Iso.prod data.entryIso (Iso.refl Nat)))
        (CodeAlgebra.finSumProdNat
          (first :: second :: rest).length
          (data.unaryCount + data.nonUnaryCount)
          (by simp)
          (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)))

/-- Rank used by the finite single-sorted frontier compiler. -/
def singleSortedFiniteRank
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary, (openFrontierShape Sig boundary).Carrier → Nat :=
  fun boundary code => by
    cases boundary with
    | nil => exact 0
    | cons _ frontier =>
        exact frontier.length + 1 + data.rankScale * (show Nat from code)

@[simp] private theorem singleSortedFiniteRank_nil
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    (code : (openFrontierShape Sig []).Carrier) :
    singleSortedFiniteRank data [] code = 0 := by
  rfl

@[simp] private theorem singleSortedFiniteRank_cons
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port)
    (code : (openFrontierShape Sig (active :: frontier)).Carrier) :
    singleSortedFiniteRank data (active :: frontier) code =
      frontier.length + 1 + data.rankScale * (show Nat from code) := by
  rfl

@[simp] private theorem singleSortedFiniteRank_openFrontierEmptyCarrier
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    {boundary : List Sig.Port} (h : boundary = []) :
    singleSortedFiniteRank data boundary
        (openFrontierEmptyCarrier (Sig := Sig) h) = 0 := by
  cases h
  rfl

@[simp] private theorem singleSortedFiniteRank_openFrontierNonemptyIso
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    {boundary : List Sig.Port} (h : boundary ≠ []) (code : Nat) :
    singleSortedFiniteRank data boundary
        ((openFrontierNonemptyIso (Sig := Sig) h).invFun code) =
      boundary.length + data.rankScale * code := by
  cases boundary with
  | nil => exact False.elim (h rfl)
  | cons _ _ =>
      simp [singleSortedFiniteRank, openFrontierNonemptyIso,
        CodeShape.infiniteIso, Iso.refl]

private def singleSortedFiniteOneFrontierBudShape
    {Sig : Signature} {node : Sig.Node} (entry : Fin (Sig.arity node))
    (child :
      Unit → (openFrontierShape Sig (Sig.nodePortsExcept node entry)).Carrier) :
    Sig.UnaryEntry ⊕ (Sig.NonUnaryEntry × Nat) :=
  if hentry : Sig.arity node = 1 then
    Sum.inl ⟨⟨node, entry⟩, hentry⟩
  else
    have hne : Sig.nodePortsExcept node entry ≠ [] :=
      Signature.nodePortsExcept_ne_nil_of_arity_ne_one
        (Nat.lt_of_le_of_lt (Nat.zero_le entry.val) entry.isLt) hentry
    Sum.inr
      (⟨⟨node, entry⟩, hentry⟩,
        (openFrontierNonemptyIso (Sig := Sig) hne).toFun (child ()))

@[simp] private theorem singleSortedFiniteOneFrontierBudShape_unary
    {Sig : Signature} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    (hentry : Sig.arity node = 1) :
    singleSortedFiniteOneFrontierBudShape entry
        (fun _ =>
          openFrontierEmptyCarrier (Sig := Sig)
            (Signature.nodePortsExcept_eq_nil_of_arity_one hentry)) =
      Sum.inl ⟨⟨node, entry⟩, hentry⟩ := by
  simp [singleSortedFiniteOneFrontierBudShape, hentry]

@[simp] private theorem singleSortedFiniteOneFrontierBudShape_nonunary
    {Sig : Signature} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    (hentry : Sig.arity node ≠ 1) (payload : Nat) :
    singleSortedFiniteOneFrontierBudShape entry
        (fun _ =>
          (openFrontierNonemptyIso (Sig := Sig)
            (Signature.nodePortsExcept_ne_nil_of_arity_ne_one
              (Nat.lt_of_le_of_lt (Nat.zero_le entry.val) entry.isLt)
              hentry)).invFun payload) =
      Sum.inr (⟨⟨node, entry⟩, hentry⟩, payload) := by
  simp [singleSortedFiniteOneFrontierBudShape, hentry, openFrontierNonemptyIso]

def singleSortedFiniteLayerToShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary →
      singleSortedFiniteLayerShape data boundary :=
  openBoundaryCases
    (motive := fun boundary =>
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary →
      singleSortedFiniteLayerShape data boundary)
    (by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  exact ⟨0, by decide⟩
              | connect =>
                  cases param
                  cases out_eq
              | bud =>
                  cases param
                  cases out_eq)
    (fun active => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param with
                  | mk _ frontier mate _ =>
                      cases out_eq
                      exact fin_zero_elim mate
              | bud =>
                  cases param with
                  | mk _ frontier node entry _ =>
                      cases out_eq
                      exact singleSortedFiniteOneFrontierBudShape entry child)
    (fun active first => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param
                  cases out_eq
                  exact Sum.inl ⟨0, by decide⟩
              | bud =>
                  cases param with
                  | mk _ frontier node entry _ =>
                      cases out_eq
                      exact Sum.inr (⟨node, entry⟩, child ()))
    (fun active first second rest => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param with
                  | mk _ frontier mate _ =>
                      cases out_eq
                      have hne :
                          eraseFin (first :: second :: rest) mate ≠ [] :=
                        eraseFin_ne_nil_of_length_gt_one mate (by simp)
                      exact Sum.inl
                        (mate,
                          (openFrontierNonemptyIso (Sig := Sig) hne).toFun
                            (child ()))
              | bud =>
                  cases param with
                  | mk _ frontier node entry _ =>
                      cases out_eq
                      exact Sum.inr (⟨node, entry⟩, child ()))

def singleSortedFiniteLayerFromShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary →
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary :=
  openBoundaryCases
    (motive := fun boundary =>
      singleSortedFiniteLayerShape data boundary →
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary)
    (fun _tag =>
      ⟨⟨.finish, (), rfl⟩, fun q => nomatch q⟩)
    (fun active shape =>
      match shape with
      | Sum.inl unary =>
          let entry := unary.val
          have hnil : Sig.nodePortsExcept entry.1 entry.2 = [] :=
            Signature.nodePortsExcept_eq_nil_of_arity_one
              unary.property
          ⟨⟨.bud,
              ⟨active, [], entry.1, entry.2,
                data.compatibleAll active _⟩,
              rfl⟩,
            fun _ => openFrontierEmptyCarrier (Sig := Sig) hnil⟩
      | Sum.inr tagged =>
          let entry := tagged.1.val
          have hne : Sig.nodePortsExcept entry.1 entry.2 ≠ [] :=
            Signature.nodePortsExcept_ne_nil_of_arity_ne_one
              (Nat.lt_of_le_of_lt (Nat.zero_le entry.2.val) entry.2.isLt)
              tagged.1.property
          ⟨⟨.bud,
              ⟨active, [], entry.1, entry.2,
                data.compatibleAll active _⟩,
              rfl⟩,
            fun _ =>
              (openFrontierNonemptyIso (Sig := Sig) hne).invFun tagged.2⟩)
    (fun active first shape =>
      match shape with
      | Sum.inl _connect =>
          ⟨⟨.connect,
              ⟨active, [first], ⟨0, by simp⟩,
                data.compatibleAll active first⟩,
              rfl⟩,
            fun _ => ⟨0, by decide⟩⟩
      | Sum.inr tagged =>
          let entry := tagged.1
          ⟨⟨.bud,
              ⟨active, [first], entry.1, entry.2,
                data.compatibleAll active _⟩,
              rfl⟩,
            fun _ => tagged.2⟩)
    (fun active first second rest shape =>
      match shape with
      | Sum.inl tagged =>
          have hne :
              eraseFin (first :: second :: rest) tagged.1 ≠ [] :=
            eraseFin_ne_nil_of_length_gt_one tagged.1 (by simp)
          ⟨⟨.connect,
              ⟨active, first :: second :: rest, tagged.1,
                data.compatibleAll active
                  ((first :: second :: rest).get tagged.1)⟩,
              rfl⟩,
            fun _ =>
              (openFrontierNonemptyIso (Sig := Sig) hne).invFun tagged.2⟩
      | Sum.inr tagged =>
          let entry := tagged.1
          ⟨⟨.bud,
              ⟨active, first :: second :: rest, entry.1, entry.2,
                data.compatibleAll active _⟩,
              rfl⟩,
            fun _ => tagged.2⟩)

private def singleSortedFiniteConnectLayer
    {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {mate : Fin frontier.length}
    (ok : Sig.compatible active (frontier.get mate))
    (out_eq :
      (poly Sig).out Ctor.connect
        (⟨active, frontier, mate, ok⟩ : ConnectParam Sig) = active :: frontier)
    (child :
      Unit → (openFrontierShape Sig (eraseFin frontier mate)).Carrier) :
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier)
        (active :: frontier) :=
  ⟨{ ctor := Ctor.connect,
      param := (⟨active, frontier, mate, ok⟩ : ConnectParam Sig),
      out_eq := out_eq }, child⟩

private theorem singleSortedFiniteLayer_ext_connect_ok
    {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {mate : Fin frontier.length}
    {ok ok' : Sig.compatible active (frontier.get mate)}
    {out_eq :
      (poly Sig).out Ctor.connect
        (⟨active, frontier, mate, ok⟩ : ConnectParam Sig) = active :: frontier}
    {out_eq' :
      (poly Sig).out Ctor.connect
        (⟨active, frontier, mate, ok'⟩ : ConnectParam Sig) = active :: frontier}
    {childf childg :
      Unit → (openFrontierShape Sig (eraseFin frontier mate)).Carrier}
    (hchild : childf = childg) :
    singleSortedFiniteConnectLayer ok out_eq childf =
      singleSortedFiniteConnectLayer ok' out_eq' childg := by
  unfold singleSortedFiniteConnectLayer
  refine CodeLayer.canonical_ext_param
    (P := poly Sig)
    (Code := fun boundary => (openFrontierShape Sig boundary).Carrier)
    (i := active :: frontier)
    (ctor := Ctor.connect)
    (ConnectParam.eq_of_ok) ?_
  exact heq_of_eq hchild

private def singleSortedFiniteBudLayer
    {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {node : Sig.Node} {entry : Fin (Sig.arity node)}
    (ok : Sig.compatible active (Sig.port node entry))
    (out_eq :
      (poly Sig).out Ctor.bud
        (⟨active, frontier, node, entry, ok⟩ : BudParam Sig) =
          active :: frontier)
    (child :
      Unit →
        (openFrontierShape Sig (frontier ++ Sig.nodePortsExcept node entry)).Carrier) :
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier)
        (active :: frontier) :=
  ⟨{ ctor := Ctor.bud,
      param := (⟨active, frontier, node, entry, ok⟩ : BudParam Sig),
      out_eq := out_eq }, child⟩

private theorem singleSortedFiniteLayer_ext_bud_ok
    {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {node : Sig.Node} {entry : Fin (Sig.arity node)}
    {ok ok' : Sig.compatible active (Sig.port node entry)}
    {out_eq :
      (poly Sig).out Ctor.bud
        (⟨active, frontier, node, entry, ok⟩ : BudParam Sig) =
          active :: frontier}
    {out_eq' :
      (poly Sig).out Ctor.bud
        (⟨active, frontier, node, entry, ok'⟩ : BudParam Sig) =
          active :: frontier}
    {childf childg :
      Unit →
        (openFrontierShape Sig (frontier ++ Sig.nodePortsExcept node entry)).Carrier}
    (hchild : childf = childg) :
    singleSortedFiniteBudLayer ok out_eq childf =
      singleSortedFiniteBudLayer ok' out_eq' childg := by
  unfold singleSortedFiniteBudLayer
  refine CodeLayer.canonical_ext_param
    (P := poly Sig)
    (Code := fun boundary => (openFrontierShape Sig boundary).Carrier)
    (i := active :: frontier)
    (ctor := Ctor.bud)
    (BudParam.eq_of_ok) ?_
  exact heq_of_eq hchild

@[simp] private theorem singleSortedFiniteLayerToShape_one_bud
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    {active : Sig.Port} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    {ok : Sig.compatible active (Sig.port node entry)}
    {out_eq :
      (poly Sig).out Ctor.bud
        (⟨active, [], node, entry, ok⟩ : BudParam Sig) = [active]}
    {child :
      Unit → (openFrontierShape Sig (Sig.nodePortsExcept node entry)).Carrier} :
    singleSortedFiniteLayerToShape data [active]
        (singleSortedFiniteBudLayer
          (frontier := []) ok out_eq child) =
      singleSortedFiniteOneFrontierBudShape entry child := by
  cases out_eq
  rfl

private theorem singleSortedFiniteOneFrontierBudLayer_left_inv
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    {active : Sig.Port} {node : Sig.Node} {entry : Fin (Sig.arity node)}
    {ok : Sig.compatible active (Sig.port node entry)}
    {out_eq :
      (poly Sig).out Ctor.bud
        (⟨active, [], node, entry, ok⟩ : BudParam Sig) = [active]}
    {child :
      Unit → (openFrontierShape Sig (Sig.nodePortsExcept node entry)).Carrier} :
    singleSortedFiniteLayerFromShape data [active]
        (singleSortedFiniteLayerToShape data [active]
          (singleSortedFiniteBudLayer
            (frontier := []) ok out_eq child)) =
      singleSortedFiniteBudLayer (frontier := []) ok out_eq child := by
  cases out_eq
  by_cases harity : Sig.arity node = 1
  · rw [singleSortedFiniteLayerToShape_one_bud (data := data)]
    dsimp [singleSortedFiniteLayerFromShape,
      singleSortedFiniteOneFrontierBudShape, harity]
    have hchild :
        (fun _ =>
          openFrontierEmptyCarrier (Sig := Sig)
            (Signature.nodePortsExcept_eq_nil_of_arity_one harity)) = child := by
      funext q
      cases q
      exact openFrontierEmptyCarrier_unique
        (Sig := Sig)
        (Signature.nodePortsExcept_eq_nil_of_arity_one harity)
        (child ())
    simpa [singleSortedFiniteLayerFromShape, singleSortedFiniteOneFrontierBudShape,
      harity, singleSortedFiniteBudLayer] using
      (singleSortedFiniteLayer_ext_bud_ok
        (Sig := Sig) (active := active) (frontier := [])
        (node := node) (entry := entry)
        (ok := data.compatibleAll active (Sig.port node entry))
        (ok' := ok) (out_eq := rfl) (out_eq' := rfl)
        (childf := fun _ =>
          openFrontierEmptyCarrier (Sig := Sig)
            (Signature.nodePortsExcept_eq_nil_of_arity_one harity))
        (childg := child) hchild)
  · rw [singleSortedFiniteLayerToShape_one_bud (data := data)]
    dsimp [singleSortedFiniteLayerFromShape,
      singleSortedFiniteOneFrontierBudShape, harity]
    have hne : Sig.nodePortsExcept node entry ≠ [] :=
      Signature.nodePortsExcept_ne_nil_of_arity_ne_one
        (Nat.lt_of_le_of_lt (Nat.zero_le entry.val) entry.isLt) harity
    simp [harity]
    change
      singleSortedFiniteBudLayer
          (frontier := [])
          (data.compatibleAll active (Sig.port node entry)) rfl
          (fun _ : Unit => child ()) =
        singleSortedFiniteBudLayer (frontier := []) ok rfl child
    have hchild :
        (fun _ : Unit => child ()) = child := by
      funext q
      cases q
      rfl
    exact singleSortedFiniteLayer_ext_bud_ok
      (Sig := Sig) (active := active) (frontier := [])
      (node := node) (entry := entry)
      (ok := data.compatibleAll active (Sig.port node entry))
      (ok' := ok) (out_eq := rfl) (out_eq' := rfl)
      (childf := fun _ : Unit => child ())
      (childg := child) hchild

private theorem singleSortedFiniteOneFrontierShape_right_inv
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port)
    (shape : Sig.UnaryEntry ⊕ (Sig.NonUnaryEntry × Nat)) :
    singleSortedFiniteLayerToShape data [active]
        (singleSortedFiniteLayerFromShape data [active] shape) = shape := by
  cases shape with
  | inl unary =>
      cases unary with
      | mk entry hentry =>
          cases entry with
          | mk node entry =>
              change
                singleSortedFiniteOneFrontierBudShape entry
                    (fun _ =>
                      openFrontierEmptyCarrier (Sig := Sig)
                        (Signature.nodePortsExcept_eq_nil_of_arity_one hentry)) =
                  Sum.inl ⟨⟨node, entry⟩, hentry⟩
              exact singleSortedFiniteOneFrontierBudShape_unary hentry
  | inr tagged =>
      cases tagged with
      | mk nonUnary payload =>
          cases nonUnary with
          | mk entry hentry =>
              cases entry with
              | mk node entry =>
                  change
                    singleSortedFiniteOneFrontierBudShape entry
                        (fun _ =>
                          (openFrontierNonemptyIso (Sig := Sig)
                            (Signature.nodePortsExcept_ne_nil_of_arity_ne_one
                              (Nat.lt_of_le_of_lt
                                (Nat.zero_le entry.val) entry.isLt)
                              hentry)).invFun payload) =
                      Sum.inr (⟨⟨node, entry⟩, hentry⟩, payload)
                  exact singleSortedFiniteOneFrontierBudShape_nonunary
                    hentry payload

private theorem singleSortedFiniteLayer_left_inv
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      Function.LeftInverse
        (singleSortedFiniteLayerFromShape data boundary)
        (singleSortedFiniteLayerToShape data boundary) :=
  openBoundaryCases
    (motive := fun boundary =>
      Function.LeftInverse
        (singleSortedFiniteLayerFromShape data boundary)
        (singleSortedFiniteLayerToShape data boundary))
    (by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  finish_code_layer_left_inv out_eq child
              | connect =>
                  cases param with
                  | mk active frontier mate ok =>
                      cases out_eq
              | bud =>
                  cases param with
                  | mk active frontier node entry ok =>
                      cases out_eq)
    (fun active => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param with
                  | mk active' frontier mate ok =>
                      cases out_eq
                      exact fin_zero_elim mate
              | bud =>
                  cases param with
                  | mk active' frontier node entry ok =>
                      cases out_eq
                      exact singleSortedFiniteOneFrontierBudLayer_left_inv
                        (data := data))
    (fun active first => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param with
                  | mk active' frontier mate ok =>
                      cases out_eq
                      cases mate with
                      | mk val isLt =>
                          cases val with
                          | zero =>
                              have hchild :
                                  (fun _ => ⟨0, by decide⟩) = child := by
                                funext q
                                cases q
                                exact fin_one_eq _ _
                              cases hchild
                              rfl
                          | succ val =>
                              simp at isLt
              | bud =>
                  cases param with
                  | mk active' frontier node entry ok =>
                      cases out_eq
                      simp [singleSortedFiniteLayerToShape,
                        singleSortedFiniteLayerFromShape]
                      exact singleSortedFiniteLayer_ext_bud_ok (by
                        child_eta_cases))
    (fun active first second rest => by
      intro layer
      cases layer with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
              cases ctor with
              | finish =>
                  cases param
                  cases out_eq
              | connect =>
                  cases param with
                  | mk active' frontier mate ok =>
                      cases out_eq
                      have hne :
                          eraseFin (first :: second :: rest) mate ≠ [] :=
                        eraseFin_ne_nil_of_length_gt_one mate (by simp)
                      simp [singleSortedFiniteLayerToShape,
                        singleSortedFiniteLayerFromShape]
                      exact singleSortedFiniteLayer_ext_connect_ok (by
                        child_eta_cases)
              | bud =>
                  cases param with
                  | mk active' frontier node entry ok =>
                      cases out_eq
                      simp [singleSortedFiniteLayerToShape,
                        singleSortedFiniteLayerFromShape]
                      exact singleSortedFiniteLayer_ext_bud_ok (by
                        child_eta_cases))

private theorem singleSortedFiniteLayer_right_inv
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      Function.RightInverse
        (singleSortedFiniteLayerFromShape data boundary)
        (singleSortedFiniteLayerToShape data boundary) :=
  openBoundaryCases
    (motive := fun boundary =>
      Function.RightInverse
        (singleSortedFiniteLayerFromShape data boundary)
        (singleSortedFiniteLayerToShape data boundary))
    (by
      intro shape
      exact fin_one_eq _ _)
    (fun active => by
      intro shape
      exact singleSortedFiniteOneFrontierShape_right_inv data active shape)
    (fun active first => by
      intro shape
      cases shape with
      | inl connect =>
          cases connect with
          | mk val isLt =>
              have hval : val = 0 := by omega
              subst val
              simp [singleSortedFiniteLayerToShape,
                singleSortedFiniteLayerFromShape]
      | inr tagged =>
          simp [singleSortedFiniteLayerToShape,
            singleSortedFiniteLayerFromShape])
    (fun active first second rest => by
      intro shape
      cases shape with
      | inl tagged =>
          cases tagged with
          | mk mate payload =>
              simp [singleSortedFiniteLayerToShape,
                singleSortedFiniteLayerFromShape,
                openFrontierNonemptyIso]
      | inr tagged =>
          simp [singleSortedFiniteLayerToShape,
            singleSortedFiniteLayerFromShape])

/--
Generic finite single-sorted layer presentation.

The compiler directions are data-driven and reusable; finite branch tables are
applied only by `singleSortedFiniteLayerShapeCarrierIso`.
-/
def singleSortedFiniteLayerPresentation
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    CodeLayerPresentation (poly Sig) (inversion Sig)
      (fun boundary => (openFrontierShape Sig boundary).Carrier)
      (singleSortedFiniteLayerShape data) :=
  CodeLayerPresentation.ofMaps
    (singleSortedFiniteLayerToShape data)
    (singleSortedFiniteLayerFromShape data)
    (singleSortedFiniteLayer_left_inv data)
    (singleSortedFiniteLayer_right_inv data)

private theorem singleSortedFiniteLayer_shape_child_rank_lt
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ {boundary : List Sig.Port}
      (shape : singleSortedFiniteLayerShape data boundary)
      (q : (poly Sig).Pos
          ((inversion Sig).decode boundary
            ((singleSortedFiniteLayerFromShape data boundary shape).1)).ctor
          ((inversion Sig).decode boundary
            ((singleSortedFiniteLayerFromShape data boundary shape).1)).param),
      singleSortedFiniteRank data
          ((poly Sig).input
            ((inversion Sig).decode boundary
              ((singleSortedFiniteLayerFromShape data boundary shape).1)).param q)
          ((singleSortedFiniteLayerFromShape data boundary shape).2 q) <
        singleSortedFiniteRank data boundary
          ((singleSortedFiniteLayerShapeCarrierIso data boundary).toFun shape) := by
  intro boundary
  exact
    openBoundaryCases
      (motive := fun boundary =>
        ∀ (shape : singleSortedFiniteLayerShape data boundary)
          (q : (poly Sig).Pos
              ((inversion Sig).decode boundary
                ((singleSortedFiniteLayerFromShape data boundary shape).1)).ctor
              ((inversion Sig).decode boundary
                ((singleSortedFiniteLayerFromShape data boundary shape).1)).param),
          singleSortedFiniteRank data
              ((poly Sig).input
                ((inversion Sig).decode boundary
                  ((singleSortedFiniteLayerFromShape data boundary shape).1)).param q)
              ((singleSortedFiniteLayerFromShape data boundary shape).2 q) <
            singleSortedFiniteRank data boundary
              ((singleSortedFiniteLayerShapeCarrierIso data boundary).toFun shape))
      (by
        intro shape q
        cases q)
      (fun active => by
        intro shape q
        cases shape with
        | inl unary =>
            cases q
            simp [singleSortedFiniteLayerFromShape, inversion,
              OutputIndexInversion.canonical, poly, input]
            omega
        | inr tagged =>
            cases tagged with
            | mk nonUnary payload =>
                cases q
                have hz :
                    payload <
                      (singleSortedFiniteLayerShapeCarrierIso data [active]).toFun
                        (Sum.inr (nonUnary, payload)) := by
                  dsimp [singleSortedFiniteLayerShapeCarrierIso]
                  exact CodeAlgebra.finiteRecursiveNat_payload_lt_of_prefix_or_tag
                    data.unaryCount data.nonUnaryCount data.nonUnaryCount_pos
                    (data.nonUnaryIso.toFun nonUnary, payload)
                    (Or.inl data.unaryCount_pos)
                have harity := data.arity_lt_rankScale nonUnary.val.1
                have hlen :
                    (Sig.nodePortsExcept nonUnary.val.1 nonUnary.val.2).length =
                      Sig.arity nonUnary.val.1 - 1 :=
                  Signature.nodePortsExcept_length nonUnary.val.1 nonUnary.val.2
                simp [singleSortedFiniteLayerFromShape, inversion,
                  OutputIndexInversion.canonical, poly, input, hlen]
                exact CodeAlgebra.rank_scaled_payload_lt
                  (scale := data.rankScale)
                  (childBase := Sig.arity nonUnary.val.1 - 1)
                  (parentBase := 1)
                  (payload := payload)
                  (code :=
                    (singleSortedFiniteLayerShapeCarrierIso data [active]).toFun
                      (Sum.inr (nonUnary, payload)))
                  (by omega) hz)
      (fun active first => by
        intro shape q
        cases shape with
        | inl connect =>
            cases q
            simp [singleSortedFiniteLayerFromShape, inversion,
              OutputIndexInversion.canonical, poly, input, eraseFin]
            omega
        | inr tagged =>
            cases tagged with
            | mk entry payload =>
                cases q
                have hz :
                    payload <
                      (singleSortedFiniteLayerShapeCarrierIso data [active, first]).toFun
                        (Sum.inr (entry, payload)) := by
                  dsimp [singleSortedFiniteLayerShapeCarrierIso]
                  exact CodeAlgebra.finiteRecursiveNat_payload_lt_of_prefix_or_tag
                    1 (data.unaryCount + data.nonUnaryCount)
                    (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)
                    (data.entryIso.toFun entry, payload)
                    (Or.inl (by decide))
                have harity := data.arity_lt_rankScale entry.1
                have hlenExcept :
                    (Sig.nodePortsExcept entry.1 entry.2).length =
                      Sig.arity entry.1 - 1 :=
                  Signature.nodePortsExcept_length entry.1 entry.2
                simp [singleSortedFiniteLayerFromShape, inversion,
                  OutputIndexInversion.canonical, poly, input]
                exact CodeAlgebra.rank_scaled_payload_lt
                  (scale := data.rankScale)
                  (childBase :=
                    (Sig.nodePortsExcept entry.1 entry.2).length + 1)
                  (parentBase := 2)
                  (payload := payload)
                  (code :=
                    (singleSortedFiniteLayerShapeCarrierIso data [active, first]).toFun
                      (Sum.inr (entry, payload)))
                  (by rw [hlenExcept]; omega) hz)
      (fun active first second rest => by
        intro shape q
        cases shape with
        | inl tagged =>
            cases tagged with
            | mk mate payload =>
                cases q
                have hz :
                    payload ≤
                      (singleSortedFiniteLayerShapeCarrierIso data
                          (active :: first :: second :: rest)).toFun
                        (Sum.inl (mate, payload)) := by
                  dsimp [singleSortedFiniteLayerShapeCarrierIso]
                  exact CodeAlgebra.finSumProdNat_toFun_inl_snd_le
                    (first :: second :: rest).length
                    (data.unaryCount + data.nonUnaryCount)
                    (by simp)
                    (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)
                    (mate, payload)
                have hlen :
                    (eraseFin (first :: second :: rest) mate).length =
                      (first :: second :: rest).length - 1 :=
                  eraseFin_length (first :: second :: rest) mate
                simp [singleSortedFiniteLayerFromShape, inversion,
                  OutputIndexInversion.canonical, poly, input, hlen]
                exact CodeAlgebra.rank_scaled_payload_le_with_gap
                  (scale := data.rankScale)
                  (childBase := (first :: second :: rest).length - 1)
                  (parentBase := (first :: second :: rest).length + 1)
                  (payload := payload)
                  (code :=
                    (singleSortedFiniteLayerShapeCarrierIso data
                      (active :: first :: second :: rest)).toFun
                        (Sum.inl (mate, payload)))
                  (by omega) hz
        | inr tagged =>
            cases tagged with
            | mk entry payload =>
                cases q
                have hz :
                    payload <
                      (singleSortedFiniteLayerShapeCarrierIso data
                          (active :: first :: second :: rest)).toFun
                        (Sum.inr (entry, payload)) := by
                  dsimp [singleSortedFiniteLayerShapeCarrierIso]
                  exact CodeAlgebra.finSumProdNat_toFun_inr_snd_lt
                    (first :: second :: rest).length
                    (data.unaryCount + data.nonUnaryCount)
                    (by simp)
                    (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)
                    (data.entryIso.toFun entry, payload)
                have harity := data.arity_lt_rankScale entry.1
                have hlenExcept :
                    (Sig.nodePortsExcept entry.1 entry.2).length =
                      Sig.arity entry.1 - 1 :=
                  Signature.nodePortsExcept_length entry.1 entry.2
                simp [singleSortedFiniteLayerFromShape, inversion,
                  OutputIndexInversion.canonical, poly, input]
                exact CodeAlgebra.rank_scaled_payload_lt
                  (scale := data.rankScale)
                  (childBase :=
                    rest.length +
                      (Sig.nodePortsExcept entry.1 entry.2).length + 1 + 1)
                  (parentBase := rest.length + 1 + 1 + 1)
                  (payload := payload)
                  (code :=
                    (singleSortedFiniteLayerShapeCarrierIso data
                      (active :: first :: second :: rest)).toFun
                        (Sum.inr (entry, payload)))
                  (by rw [hlenExcept]; omega) hz)
      boundary

/-- Generic generated shape-code data for finite single-sorted string diagrams. -/
def singleSortedFiniteGeneratedShapeCode
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    GeneratedShapeCode (poly Sig) :=
  ShapeLayerPresentation.generatedCode
    { shape := openFrontierShape Sig
      presentation :=
        LayerPresentation.ofShapeChildRank
          (singleSortedFiniteLayerPresentation data)
          (singleSortedFiniteLayerShapeCarrierIso data)
          (singleSortedFiniteRank data)
          (by
            intro boundary shape q
            exact singleSortedFiniteLayer_shape_child_rank_lt
              (data := data) (boundary := boundary) shape q) }

/-- Syntax for any open frontier is coded by the generated open-frontier shape. -/
def singleSortedFiniteSyntaxShapeIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ (openFrontierShape Sig boundary).Carrier :=
  GeneratedCode.shapeCodeIso
    (generatedCode Sig)
    (singleSortedFiniteGeneratedShapeCode Sig data)
    boundary

/-- Empty-frontier syntax is generated as the singleton finite carrier. -/
def singleSortedFiniteSyntaxEmptyFinOneIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    Diag Sig [] ≃ᵢ Fin 1 :=
  GeneratedCode.shapeFinIso
    (generatedCode Sig)
    (singleSortedFiniteGeneratedShapeCode Sig data)
    [] rfl

/-- Nonempty-frontier syntax is generated as a natural-number carrier. -/
def singleSortedFiniteSyntaxNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    Diag Sig (active :: frontier) ≃ᵢ Nat :=
  GeneratedCode.shapeNatIso
    (generatedCode Sig)
    (singleSortedFiniteGeneratedShapeCode Sig data)
    (active :: frontier) rfl

end StringDiagram
end BijForm
