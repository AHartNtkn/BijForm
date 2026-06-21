import BijForm.CodeAlgebra
import BijForm.StringDiagram.Polynomial
import BijForm.StringDiagram.Bridge

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

def openFrontierNatCarrier {Sig : Signature}
    {boundary : List Sig.Port} (h : boundary ≠ []) :
    Nat → (openFrontierShape Sig boundary).Carrier := by
  cases boundary with
  | nil => exact False.elim (h rfl)
  | cons _ _ => exact id

def openFrontierCarrierNat {Sig : Signature}
    {boundary : List Sig.Port} (h : boundary ≠ []) :
    (openFrontierShape Sig boundary).Carrier → Nat := by
  cases boundary with
  | nil => exact False.elim (h rfl)
  | cons _ _ => exact id

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
  arity_pos : ∀ node : Sig.Node, 0 < Sig.arity node
  rankScale : Nat
  rankScale_pos : 0 < rankScale
  arity_lt_rankScale : ∀ node : Sig.Node, Sig.arity node < rankScale
  unaryCount : Nat
  unaryCount_pos : 0 < unaryCount
  unaryIso : Sig.UnaryEntry ≃ᵢ Fin unaryCount
  nonUnaryCount : Nat
  nonUnaryCount_pos : 0 < nonUnaryCount
  nonUnaryIso : Sig.NonUnaryEntry ≃ᵢ Fin nonUnaryCount

namespace SingleSortedFiniteCodingData

variable {Sig : Signature} (data : SingleSortedFiniteCodingData Sig)

def entryTag : Type :=
  Fin (data.unaryCount + data.nonUnaryCount)

def entryToTag (entry : Sig.Entry) : data.entryTag :=
  if h : Sig.arity entry.1 = 1 then
    (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).toFun
      (Sum.inl (data.unaryIso.toFun ⟨entry, h⟩))
  else
    (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).toFun
      (Sum.inr (data.nonUnaryIso.toFun ⟨entry, h⟩))

def tagToEntry (tag : data.entryTag) : Sig.Entry :=
  match (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).invFun tag with
  | Sum.inl unary => (data.unaryIso.invFun unary).val
  | Sum.inr nonUnary => (data.nonUnaryIso.invFun nonUnary).val

def tagToEntryOk (active : Sig.Port) (tag : data.entryTag) :
    Sig.compatible active (Sig.port (data.tagToEntry tag).1 (data.tagToEntry tag).2) :=
  data.compatibleAll active _

def unaryTagToEntry (tag : Fin data.unaryCount) : Sig.Entry :=
  (data.unaryIso.invFun tag).val

def unaryTagArity (tag : Fin data.unaryCount) :
    Sig.arity (data.unaryTagToEntry tag).1 = 1 :=
  (data.unaryIso.invFun tag).property

def nonUnaryTagToEntry (tag : Fin data.nonUnaryCount) : Sig.Entry :=
  (data.nonUnaryIso.invFun tag).val

def nonUnaryTagArity (tag : Fin data.nonUnaryCount) :
    Sig.arity (data.nonUnaryTagToEntry tag).1 ≠ 1 :=
  (data.nonUnaryIso.invFun tag).property

theorem tagToEntry_entryToTag (entry : Sig.Entry) :
    data.tagToEntry (data.entryToTag entry) = entry := by
  by_cases hentry : Sig.arity entry.1 = 1
  · simp [entryToTag, tagToEntry, hentry]
  · simp [entryToTag, tagToEntry, hentry]

theorem entryToTag_tagToEntry (tag : data.entryTag) :
    data.entryToTag (data.tagToEntry tag) = tag := by
  cases htag :
      (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).invFun tag with
  | inl unary =>
      have hright :
          (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).toFun
              (Sum.inl unary) = tag := by
        simpa [htag] using
          (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).right_inv tag
      unfold entryToTag tagToEntry
      rw [htag]
      rw [dif_pos (data.unaryIso.invFun unary).property]
      have hunary :
          (⟨(data.unaryIso.invFun unary).val,
            (data.unaryIso.invFun unary).property⟩ : Sig.UnaryEntry) =
            data.unaryIso.invFun unary := by
        apply Subtype.ext
        rfl
      rw [hunary]
      rw [data.unaryIso.right_inv unary]
      exact hright
  | inr nonUnary =>
      have hright :
          (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).toFun
              (Sum.inr nonUnary) = tag := by
        simpa [htag] using
          (CodeAlgebra.finSum data.unaryCount data.nonUnaryCount).right_inv tag
      unfold entryToTag tagToEntry
      rw [htag]
      rw [dif_neg (data.nonUnaryIso.invFun nonUnary).property]
      have hnonUnary :
          (⟨(data.nonUnaryIso.invFun nonUnary).val,
            (data.nonUnaryIso.invFun nonUnary).property⟩ :
              Sig.NonUnaryEntry) =
            data.nonUnaryIso.invFun nonUnary := by
        apply Subtype.ext
        rfl
      rw [hnonUnary]
      rw [data.nonUnaryIso.right_inv nonUnary]
      exact hright

def entryIso : Sig.Entry ≃ᵢ data.entryTag where
  toFun := data.entryToTag
  invFun := data.tagToEntry
  left_inv := data.tagToEntry_entryToTag
  right_inv := data.entryToTag_tagToEntry

end SingleSortedFiniteCodingData

/-- The one-step branch shape generated from finite single-sorted signature data. -/
def singleSortedFiniteLayerShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    List Sig.Port → Type
  | [] => Fin 1
  | _active :: [] =>
      Fin data.unaryCount ⊕ (Fin data.nonUnaryCount × Nat)
  | _active :: _first :: [] =>
      Fin 1 ⊕ (Fin (data.unaryCount + data.nonUnaryCount) × Nat)
  | _active :: first :: second :: rest =>
      (Fin (first :: second :: rest).length × Nat) ⊕
        (Fin (data.unaryCount + data.nonUnaryCount) × Nat)

/-- Carrier isomorphism for the generated one-step branch shape. -/
def singleSortedFiniteLayerShapeCarrierIso
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary ≃ᵢ
        (openFrontierShape Sig boundary).Carrier
  | [] => Iso.refl (Fin 1)
  | _active :: [] =>
      CodeAlgebra.finiteRecursiveNat
        data.unaryCount data.nonUnaryCount data.nonUnaryCount_pos
  | _active :: _first :: [] =>
      CodeAlgebra.finiteRecursiveNat 1
        (data.unaryCount + data.nonUnaryCount)
        (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)
  | _active :: first :: second :: rest =>
      CodeAlgebra.finSumProdNat
        (first :: second :: rest).length
        (data.unaryCount + data.nonUnaryCount)
        (by simp)
        (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos)

/-- Rank used by the finite single-sorted frontier compiler. -/
def singleSortedFiniteRank
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary, (openFrontierShape Sig boundary).Carrier → Nat :=
  fun boundary code => by
    cases boundary with
    | nil => exact 0
    | cons _ frontier =>
        exact frontier.length + 1 + data.rankScale * (show Nat from code)

def singleSortedFiniteLayerToShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary →
      singleSortedFiniteLayerShape data boundary
  | [], ⟨⟨.finish, (), _h⟩, _child⟩ => ⟨0, by decide⟩
  | [], ⟨⟨.connect, p, h⟩, _child⟩ => by
      cases p
      cases h
  | [], ⟨⟨.bud, p, h⟩, _child⟩ => by
      cases p
      cases h
  | active :: [], ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
  | active :: [], ⟨⟨.connect, p, h⟩, _child⟩ => by
      cases p with
      | mk _ frontier mate _ =>
          cases h
          cases mate with
          | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | active :: [], ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk _ frontier node entry _ =>
          cases h
          by_cases hentry : Sig.arity node = 1
          · exact Sum.inl (data.unaryIso.toFun ⟨⟨node, entry⟩, hentry⟩)
          · have hne : Sig.nodePortsExcept node entry ≠ [] :=
              Signature.nodePortsExcept_ne_nil_of_arity_ne_one
                (data.arity_pos node) hentry
            exact Sum.inr
              (data.nonUnaryIso.toFun ⟨⟨node, entry⟩, hentry⟩,
                openFrontierCarrierNat (Sig := Sig) hne (child ()))
  | active :: first :: [], ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
  | active :: first :: [], ⟨⟨.connect, p, h⟩, _child⟩ => by
      cases p
      cases h
      exact Sum.inl ⟨0, by decide⟩
  | active :: first :: [], ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk _ frontier node entry _ =>
          cases h
          exact Sum.inr (data.entryToTag ⟨node, entry⟩, child ())
  | active :: first :: second :: rest, ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
  | active :: first :: second :: rest, ⟨⟨.connect, p, h⟩, child⟩ => by
      cases p with
      | mk _ frontier mate _ =>
          cases h
          have hne :
              eraseFin (first :: second :: rest) mate ≠ [] :=
            eraseFin_ne_nil_of_length_gt_one mate (by simp)
          exact Sum.inl
            (mate, openFrontierCarrierNat (Sig := Sig) hne (child ()))
  | active :: first :: second :: rest, ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk _ frontier node entry _ =>
          cases h
          exact Sum.inr (data.entryToTag ⟨node, entry⟩, child ())

def singleSortedFiniteLayerFromShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary →
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary
  | [], _tag =>
      ⟨⟨.finish, (), rfl⟩, fun q => nomatch q⟩
  | active :: [], Sum.inl unary =>
      let entry := data.unaryTagToEntry unary
      have hnil : Sig.nodePortsExcept entry.1 entry.2 = [] :=
        Signature.nodePortsExcept_eq_nil_of_arity_one
          (data.unaryTagArity unary)
      ⟨⟨.bud,
          ⟨active, [], entry.1, entry.2, data.compatibleAll active _⟩,
          rfl⟩,
        fun _ => openFrontierEmptyCarrier (Sig := Sig) hnil⟩
  | active :: [], Sum.inr tagged =>
      let entry := data.nonUnaryTagToEntry tagged.1
      have hne : Sig.nodePortsExcept entry.1 entry.2 ≠ [] :=
        Signature.nodePortsExcept_ne_nil_of_arity_ne_one
          (data.arity_pos entry.1) (data.nonUnaryTagArity tagged.1)
      ⟨⟨.bud,
          ⟨active, [], entry.1, entry.2, data.compatibleAll active _⟩,
          rfl⟩,
        fun _ => openFrontierNatCarrier (Sig := Sig) hne tagged.2⟩
  | active :: first :: [], Sum.inl _connect =>
      ⟨⟨.connect,
          ⟨active, [first], ⟨0, by simp⟩, data.compatibleAll active first⟩,
          rfl⟩,
        fun _ => ⟨0, by decide⟩⟩
  | active :: first :: [], Sum.inr tagged =>
      let entry := data.tagToEntry tagged.1
      ⟨⟨.bud,
          ⟨active, [first], entry.1, entry.2, data.tagToEntryOk active tagged.1⟩,
          rfl⟩,
        fun _ => tagged.2⟩
  | active :: first :: second :: rest, Sum.inl tagged =>
      have hne :
          eraseFin (first :: second :: rest) tagged.1 ≠ [] :=
        eraseFin_ne_nil_of_length_gt_one tagged.1 (by simp)
      ⟨⟨.connect,
          ⟨active, first :: second :: rest, tagged.1,
            data.compatibleAll active ((first :: second :: rest).get tagged.1)⟩,
          rfl⟩,
        fun _ => openFrontierNatCarrier (Sig := Sig) hne tagged.2⟩
  | active :: first :: second :: rest, Sum.inr tagged =>
      let entry := data.tagToEntry tagged.1
      ⟨⟨.bud,
          ⟨active, first :: second :: rest, entry.1, entry.2,
            data.tagToEntryOk active tagged.1⟩,
          rfl⟩,
        fun _ => tagged.2⟩

/--
Generic finite single-sorted layer presentation.

Unfinished proof boundary: the two compiler directions above are data-driven
and reusable, but their dependent inverse proofs still need to be closed.
-/
def singleSortedFiniteLayerPresentation
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    CodeLayerPresentation (poly Sig) (inversion Sig)
      (fun boundary => (openFrontierShape Sig boundary).Carrier)
      (singleSortedFiniteLayerShape data) :=
  CodeLayerPresentation.ofMaps
    (singleSortedFiniteLayerToShape data)
    (singleSortedFiniteLayerFromShape data)
    (by
      -- Unfinished: dependent inverse proof for the generic branch compiler.
      sorry)
    (by
      -- Unfinished: dependent inverse proof for the generic branch compiler.
      sorry)

def singleSortedFiniteCarrierLayer
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    CodeLayerPresentation (poly Sig) (inversion Sig)
      (fun boundary => (openFrontierShape Sig boundary).Carrier)
      (fun boundary => (openFrontierShape Sig boundary).Carrier) :=
  (singleSortedFiniteLayerPresentation data).transCarrier
    (singleSortedFiniteLayerShapeCarrierIso data)

/--
Rank descent for the generic finite single-sorted layer compiler.

Unfinished: the proof uses `rankScale`, `arity_lt_rankScale`, and the finite
recursive carrier inequalities to show every decoded child is smaller.
-/
theorem singleSortedFiniteLayer_child_rank_lt
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ {boundary : List Sig.Port}
      (z : (openFrontierShape Sig boundary).Carrier)
      (q : (poly Sig).Pos
          ((inversion Sig).decode boundary
            (((singleSortedFiniteCarrierLayer data).iso boundary).invFun z).1).ctor
          ((inversion Sig).decode boundary
            (((singleSortedFiniteCarrierLayer data).iso boundary).invFun z).1).param),
      singleSortedFiniteRank data
          ((poly Sig).input
            ((inversion Sig).decode boundary
              (((singleSortedFiniteCarrierLayer data).iso boundary).invFun z).1).param q)
          ((((singleSortedFiniteCarrierLayer data).iso boundary).invFun z).2 q) <
        singleSortedFiniteRank data boundary z := by
  -- Unfinished: generic rank descent for the finite branch-table compiler.
  sorry

/-- Generic generated shape-code data for finite single-sorted string diagrams. -/
def singleSortedFiniteGeneratedShapeCode
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    GeneratedShapeCode (poly Sig) :=
  ((LayerShapePresentation.ofComponents
    (singleSortedFiniteLayerPresentation data)
    (singleSortedFiniteLayerShapeCarrierIso data)
    (singleSortedFiniteRank data)
    (by
      intro boundary z q
      exact singleSortedFiniteLayer_child_rank_lt data z q)).toShapeLayerPresentation
        (openFrontierShape Sig)).generatedCode

/-- Generated-code equivalence for finite single-sorted string-diagram syntax. -/
def singleSortedFiniteSyntaxIso
    (Sig : Signature) (_data : SingleSortedFiniteCodingData Sig)
    (boundary : List Sig.Port) :
    Mu (poly Sig) boundary ≃ᵢ Diag Sig boundary :=
  syntaxIso Sig boundary

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

/-- Empty-frontier open graphs inherit the singleton finite syntax carrier. -/
def singleSortedFiniteOpenGraphEmptyFinOneIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    OpenPortHypergraphUpToIso Sig [] ≃ᵢ Fin 1 :=
  Iso.trans (Iso.symm (diagOpenPortHypergraphIso Sig []))
    (singleSortedFiniteSyntaxEmptyFinOneIso Sig data)

/-- Nonempty-frontier open graphs inherit the natural-number syntax carrier. -/
def singleSortedFiniteOpenGraphNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    OpenPortHypergraphUpToIso Sig (active :: frontier) ≃ᵢ Nat :=
  Iso.trans (Iso.symm (diagOpenPortHypergraphIso Sig (active :: frontier)))
    (singleSortedFiniteSyntaxNonemptyNatIso Sig data active frontier)

end StringDiagram
end BijForm
