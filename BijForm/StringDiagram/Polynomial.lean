import BijForm.StringDiagram.Basic
import BijForm.InitialAlgebra

namespace BijForm
namespace StringDiagram

open DepPoly

structure ConnectParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  mate : Fin frontier.length
  ok : Sig.compatible active (frontier.get mate)

namespace ConnectParam

theorem eq_of_ok {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {mate : Fin frontier.length}
    {ok ok' : Sig.compatible active (frontier.get mate)} :
    ({ active := active, frontier := frontier, mate := mate, ok := ok } :
      ConnectParam Sig) =
      { active := active, frontier := frontier, mate := mate, ok := ok' } := by
  cases Subsingleton.elim ok ok'
  rfl

end ConnectParam

structure BudParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  node : Sig.Node
  entry : Fin (Sig.arity node)
  ok : Sig.compatible active (Sig.port node entry)

namespace BudParam

theorem eq_of_ok {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {node : Sig.Node} {entry : Fin (Sig.arity node)}
    {ok ok' : Sig.compatible active (Sig.port node entry)} :
    ({ active := active, frontier := frontier, node := node, entry := entry, ok := ok } :
      BudParam Sig) =
      { active := active, frontier := frontier, node := node, entry := entry, ok := ok' } := by
  cases Subsingleton.elim ok ok'
  rfl

end BudParam

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

/-- Presentation of typed rooted open diagram syntax as generated code data. -/
def syntaxPresentation (Sig : Signature) :
    SyntaxPresentation (poly Sig) (inversion Sig) (Diag Sig) :=
  SyntaxPresentation.ofLayerIsoChildRank
    (fun boundary =>
      { toFun := layerToSyntax Sig boundary
        invFun := syntaxToLayer Sig boundary
        left_inv :=
          CodeLayer.canonical_left_inv_by_fiber
            (toCarrier := layerToSyntax Sig)
            (fromCarrier := syntaxToLayer Sig) (by
              intro boundary ctor param out_eq child
              cases ctor with
              | finish =>
                  cases param
                  finish_code_layer_left_inv out_eq child
              | connect =>
                  cases param with
                  | mk active frontier mate ok =>
                    finish_code_layer_left_inv out_eq child
              | bud =>
                  cases param with
                  | mk active frontier node entry ok =>
                    finish_code_layer_left_inv out_eq child) boundary
        right_inv := by
          intro t
          cases t with
          | finish => rfl
          | connect mate ok child => rfl
          | bud node entry ok child => rfl })
    (fun _ t => Diag.rank t)
    (by
      intro boundary layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | finish =>
          cases param
          cases out_eq
          cases q
      | connect =>
          cases param with
          | mk active frontier mate ok =>
              cases out_eq
              cases q
              simp [layerToSyntax]
      | bud =>
          cases param with
          | mk active frontier node entry ok =>
              cases out_eq
              cases q
              simp [layerToSyntax])

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

end StringDiagram
end BijForm
