import BijForm.CodeAlgebra
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

/-- The one-step branch shape generated from finite single-sorted signature data. -/
def singleSortedFiniteLayerShape
    {Sig : Signature} (_data : SingleSortedFiniteCodingData Sig) :
    List Sig.Port → Type
  | [] => Fin 1
  | _active :: [] =>
      Sig.UnaryEntry ⊕ (Sig.NonUnaryEntry × Nat)
  | _active :: _first :: [] =>
      Fin 1 ⊕ (Sig.Entry × Nat)
  | _active :: first :: second :: rest =>
      (Fin (first :: second :: rest).length × Nat) ⊕
        (Sig.Entry × Nat)

/-- Carrier isomorphism for the generated one-step branch shape. -/
def singleSortedFiniteLayerShapeCarrierIso
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary ≃ᵢ
        (openFrontierShape Sig boundary).Carrier
  | [] => Iso.refl (Fin 1)
  | _active :: [] =>
      Iso.trans
        (Iso.sum data.unaryIso
          (Iso.prod data.nonUnaryIso (Iso.refl Nat)))
        (CodeAlgebra.finiteRecursiveNat
          data.unaryCount data.nonUnaryCount data.nonUnaryCount_pos)
  | _active :: _first :: [] =>
      Iso.trans
        (Iso.sum (Iso.refl (Fin 1))
          (Iso.prod data.entryIso (Iso.refl Nat)))
        (CodeAlgebra.finiteRecursiveNat 1
          (data.unaryCount + data.nonUnaryCount)
          (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos))
  | _active :: first :: second :: rest =>
      Iso.trans
        (Iso.sum (Iso.refl (Fin (first :: second :: rest).length × Nat))
          (Iso.prod data.entryIso (Iso.refl Nat)))
        (CodeAlgebra.finSumProdNat
          (first :: second :: rest).length
          (data.unaryCount + data.nonUnaryCount)
          (by simp)
          (Nat.lt_add_right data.nonUnaryCount data.unaryCount_pos))

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

private theorem rank_scaled_payload_lt
    {scale childBase parentBase payload code : Nat}
    (hbase : childBase < parentBase + scale)
    (hz : payload < code) :
    childBase + scale * payload < parentBase + scale * code := by
  have hsucc : payload + 1 ≤ code := Nat.succ_le_of_lt hz
  have hmul : scale * (payload + 1) ≤ scale * code :=
    Nat.mul_le_mul_left scale hsucc
  have hstep : childBase + scale * payload <
      parentBase + scale * (payload + 1) := by
    rw [Nat.mul_succ]
    omega
  exact Nat.lt_of_lt_of_le hstep (Nat.add_le_add_left hmul parentBase)

private theorem rank_scaled_payload_le_with_gap
    {scale childBase parentBase payload code : Nat}
    (hbase : childBase < parentBase)
    (hz : payload ≤ code) :
    childBase + scale * payload < parentBase + scale * code := by
  have hmul : scale * payload ≤ scale * code :=
    Nat.mul_le_mul_left scale hz
  omega

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
          · exact Sum.inl ⟨⟨node, entry⟩, hentry⟩
          · have hne : Sig.nodePortsExcept node entry ≠ [] :=
              Signature.nodePortsExcept_ne_nil_of_arity_ne_one
                (Nat.lt_of_le_of_lt (Nat.zero_le entry.val) entry.isLt) hentry
            exact Sum.inr
              (⟨⟨node, entry⟩, hentry⟩,
                (openFrontierNonemptyIso (Sig := Sig) hne).toFun (child ()))
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
          exact Sum.inr (⟨node, entry⟩, child ())
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
            (mate, (openFrontierNonemptyIso (Sig := Sig) hne).toFun (child ()))
  | active :: first :: second :: rest, ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk _ frontier node entry _ =>
          cases h
          exact Sum.inr (⟨node, entry⟩, child ())

def singleSortedFiniteLayerFromShape
    {Sig : Signature} (data : SingleSortedFiniteCodingData Sig) :
    ∀ boundary,
      singleSortedFiniteLayerShape data boundary →
      CodeLayer (poly Sig) (inversion Sig)
        (fun boundary => (openFrontierShape Sig boundary).Carrier) boundary
  | [], _tag =>
      ⟨⟨.finish, (), rfl⟩, fun q => nomatch q⟩
  | active :: [], Sum.inl unary =>
      let entry := unary.val
      have hnil : Sig.nodePortsExcept entry.1 entry.2 = [] :=
        Signature.nodePortsExcept_eq_nil_of_arity_one
          unary.property
      ⟨⟨.bud,
          ⟨active, [], entry.1, entry.2, data.compatibleAll active _⟩,
          rfl⟩,
        fun _ => openFrontierEmptyCarrier (Sig := Sig) hnil⟩
  | active :: [], Sum.inr tagged =>
      let entry := tagged.1.val
      have hne : Sig.nodePortsExcept entry.1 entry.2 ≠ [] :=
        Signature.nodePortsExcept_ne_nil_of_arity_ne_one
          (Nat.lt_of_le_of_lt (Nat.zero_le entry.2.val) entry.2.isLt)
          tagged.1.property
      ⟨⟨.bud,
          ⟨active, [], entry.1, entry.2, data.compatibleAll active _⟩,
          rfl⟩,
        fun _ => (openFrontierNonemptyIso (Sig := Sig) hne).invFun tagged.2⟩
  | active :: first :: [], Sum.inl _connect =>
      ⟨⟨.connect,
          ⟨active, [first], ⟨0, by simp⟩, data.compatibleAll active first⟩,
          rfl⟩,
        fun _ => ⟨0, by decide⟩⟩
  | active :: first :: [], Sum.inr tagged =>
      let entry := tagged.1
      ⟨⟨.bud,
          ⟨active, [first], entry.1, entry.2, data.compatibleAll active _⟩,
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
        fun _ => (openFrontierNonemptyIso (Sig := Sig) hne).invFun tagged.2⟩
  | active :: first :: second :: rest, Sum.inr tagged =>
      let entry := tagged.1
      ⟨⟨.bud,
          ⟨active, first :: second :: rest, entry.1, entry.2,
            data.compatibleAll active _⟩,
          rfl⟩,
        fun _ => tagged.2⟩

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
    (by
      intro boundary layer
      cases boundary with
      | nil =>
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
                  | bud =>
                      cases param with
                      | mk active frontier node entry ok =>
                          cases out_eq
      | cons active frontier =>
          cases frontier with
          | nil =>
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
                                  exact False.elim (Nat.not_lt_zero val isLt)
                      | bud =>
                          cases param with
                          | mk active' frontier node entry ok =>
                              cases out_eq
                              by_cases hentry : Sig.arity node = 1
                              · have hchild :
                                    (fun _ =>
                                      openFrontierEmptyCarrier
                                        (Sig := Sig)
                                        (Signature.nodePortsExcept_eq_nil_of_arity_one hentry)) =
                                      child := by
                                  funext q
                                  cases q
                                  exact openFrontierEmptyCarrier_unique
                                    (Sig := Sig)
                                    (Signature.nodePortsExcept_eq_nil_of_arity_one hentry)
                                    (child ())
                                simp [singleSortedFiniteLayerToShape,
                                  singleSortedFiniteLayerFromShape, hentry]
                                exact singleSortedFiniteLayer_ext_bud_ok hchild
                              · have hchild :
                                    (fun _ => child ()) = child := by
                                  child_eta_unit
                                simp [singleSortedFiniteLayerToShape,
                                  singleSortedFiniteLayerFromShape, hentry]
                                exact singleSortedFiniteLayer_ext_bud_ok hchild
          | cons first rest =>
              cases rest with
              | nil =>
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
                                  have hchild : (fun _ => child ()) = child := by
                                    child_eta_unit
                                  simp [singleSortedFiniteLayerToShape,
                                    singleSortedFiniteLayerFromShape]
                                  exact singleSortedFiniteLayer_ext_bud_ok hchild
              | cons second rest =>
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
                                  have hchild :
                                      (fun _ => child ()) = child := by
                                    child_eta_unit
                                  simp [singleSortedFiniteLayerToShape,
                                    singleSortedFiniteLayerFromShape]
                                  exact singleSortedFiniteLayer_ext_connect_ok hchild
                          | bud =>
                              cases param with
                              | mk active' frontier node entry ok =>
                                  cases out_eq
                                  have hchild : (fun _ => child ()) = child := by
                                    child_eta_unit
                                  simp [singleSortedFiniteLayerToShape,
                                    singleSortedFiniteLayerFromShape]
                                  exact singleSortedFiniteLayer_ext_bud_ok hchild)
    (by
      intro boundary shape
      cases boundary with
      | nil =>
          exact fin_one_eq _ _
      | cons active frontier =>
          cases frontier with
          | nil =>
              cases shape with
              | inl unary =>
                  cases unary with
                  | mk entry hentry =>
                      simp [singleSortedFiniteLayerToShape,
                        singleSortedFiniteLayerFromShape, hentry]
              | inr tagged =>
                  cases tagged with
                  | mk nonUnary payload =>
                    cases nonUnary with
                    | mk entry hentry =>
                        simp [singleSortedFiniteLayerToShape,
                          singleSortedFiniteLayerFromShape, hentry,
                          openFrontierNonemptyIso]
          | cons first rest =>
              cases rest with
              | nil =>
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
                        singleSortedFiniteLayerFromShape]
              | cons second rest =>
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
  intro boundary shape q
  cases boundary with
  | nil =>
      cases q
  | cons active frontier =>
      cases frontier with
      | nil =>
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
                  exact rank_scaled_payload_lt
                    (scale := data.rankScale)
                    (childBase := Sig.arity nonUnary.val.1 - 1)
                    (parentBase := 1)
                    (payload := payload)
                    (code :=
                      (singleSortedFiniteLayerShapeCarrierIso data [active]).toFun
                        (Sum.inr (nonUnary, payload)))
                    (by omega) hz
      | cons first rest =>
          cases rest with
          | nil =>
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
                      exact rank_scaled_payload_lt
                        (scale := data.rankScale)
                        (childBase :=
                          (Sig.nodePortsExcept entry.1 entry.2).length + 1)
                        (parentBase := 2)
                        (payload := payload)
                        (code :=
                          (singleSortedFiniteLayerShapeCarrierIso data [active, first]).toFun
                            (Sum.inr (entry, payload)))
                        (by rw [hlenExcept]; omega) hz
          | cons second rest =>
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
                      exact rank_scaled_payload_le_with_gap
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
                      exact rank_scaled_payload_lt
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
                        (by rw [hlenExcept]; omega) hz

/-- Generic generated shape-code data for finite single-sorted string diagrams. -/
def singleSortedFiniteGeneratedShapeCode
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig) :
    GeneratedShapeCode (poly Sig) :=
  ((LayerShapePresentation.ofShapeChildRank
    (singleSortedFiniteLayerPresentation data)
    (singleSortedFiniteLayerShapeCarrierIso data)
    (singleSortedFiniteRank data)
    (by
      intro boundary shape q
      exact singleSortedFiniteLayer_shape_child_rank_lt
        (data := data) (boundary := boundary) shape q)).toShapeLayerPresentation
        (openFrontierShape Sig)).generatedCode

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
  CodeShape.sourceFinIso (singleSortedFiniteSyntaxShapeIso Sig data []) rfl

/-- Nonempty-frontier syntax is generated as a natural-number carrier. -/
def singleSortedFiniteSyntaxNonemptyNatIso
    (Sig : Signature) (data : SingleSortedFiniteCodingData Sig)
    (active : Sig.Port) (frontier : List Sig.Port) :
    Diag Sig (active :: frontier) ≃ᵢ Nat :=
  CodeShape.sourceNatIso
    (singleSortedFiniteSyntaxShapeIso Sig data (active :: frontier)) rfl

end StringDiagram
end BijForm
