import BijForm.DependentPolynomial

namespace BijForm
namespace StringDiagram

open DepPoly

/--
A single-typed string-diagram signature.

`portsMinusOne a = m` means constructor `a` has `m + 1` ports, so every
constructor has at least one port.
-/
structure Signature where
  ctorCount : Nat
  portsMinusOne : Fin ctorCount → Nat

/--
Rooted open diagram syntax for a single-typed signature.

`Diag Sig n` describes a diagram with `n` currently open frontier ports.  The
constructors mirror the boundary-rooted traversal:

* `finish` closes the empty frontier;
* `connect` connects two frontier ports and continues with two fewer ports;
* `bud` enters one constructor port from the frontier and exposes the remaining
  constructor ports on the frontier.

This syntax is the local canonical presentation used for generated coding in
this module.  The semantic theorem identifying it with concrete finite open
port-hypergraphs up to boundary-preserving isomorphism is still an unfinished
graph-model obligation; this module deliberately avoids replacing that theorem
with an opaque graph quotient.
-/
inductive Diag (Sig : Signature) : Nat → Type
  | finish : Diag Sig 0
  | connect {n : Nat} (frontier : 1 < n) :
      Diag Sig (n - 2) → Fin (n - 1) → Diag Sig n
  | bud {n : Nat} (a : Fin Sig.ctorCount) :
      Fin (Sig.portsMinusOne a + 1) → 0 < n →
        Diag Sig (n - 1 + Sig.portsMinusOne a) → Diag Sig n

namespace Diag

variable {Sig : Signature}

/-- Structural rank used for the generated syntax coding. -/
def rank : ∀ {n : Nat}, Diag Sig n → Nat
  | _, finish => 0
  | _, connect _ child _ => rank child + 1
  | _, bud _ _ _ child => rank child + 1

end Diag

/-- Polynomial constructors for the rooted open syntax. -/
inductive Ctor where
  | finish
  | connect
  | bud
deriving DecidableEq, Repr

structure ConnectParam where
  n : Nat
  frontier : 1 < n
  port : Fin (n - 1)

structure BudParam (Sig : Signature) where
  n : Nat
  node : Fin Sig.ctorCount
  entry : Fin (Sig.portsMinusOne node + 1)
  frontier : 0 < n

def Param (Sig : Signature) : Ctor → Type
  | .finish => Unit
  | .connect => ConnectParam
  | .bud => BudParam Sig

def out (Sig : Signature) : (c : Ctor) → Param Sig c → Nat
  | .finish, _ => 0
  | .connect, p => p.n
  | .bud, p => p.n

def Pos (Sig : Signature) : (c : Ctor) → Param Sig c → Type
  | .finish, _ => Empty
  | .connect, _ => Unit
  | .bud, _ => Unit

def input (Sig : Signature) :
    {c : Ctor} → (p : Param Sig c) → Pos Sig c p → Nat
  | .finish, _, q => nomatch q
  | .connect, p, _ => p.n - 2
  | .bud, p, _ => p.n - 1 + Sig.portsMinusOne p.node

/-- Dependent polynomial for the rooted open string-diagram syntax. -/
def poly (Sig : Signature) : DepPoly Nat where
  Ctor := Ctor
  Param := Param Sig
  out := out Sig
  Pos := Pos Sig
  input := input Sig

/--
The constructor output index is exposed directly as a same-fiber constructor
parameter.  This keeps the constructor-fiber data visible to the generic
generated-code layer.
-/
def inversion (Sig : Signature) : OutputIndexInversion (poly Sig) :=
  OutputIndexInversion.canonical (poly Sig)

def layerToSyntax (Sig : Signature) (n : Nat) :
    CodeLayer (poly Sig) (inversion Sig) (Diag Sig) n → Diag Sig n
  | ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
      exact .finish
  | ⟨⟨.connect, p, h⟩, child⟩ => by
      cases p with
      | mk m hm port =>
          cases h
          exact .connect hm (child ()) port
  | ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk m a entry hm =>
          cases h
          exact .bud a entry hm (child ())

def syntaxToLayer (Sig : Signature) (n : Nat) :
    Diag Sig n → CodeLayer (poly Sig) (inversion Sig) (Diag Sig) n
  | .finish =>
      ⟨⟨Ctor.finish, (), rfl⟩, fun q => nomatch q⟩
  | @Diag.connect _ m hm child port =>
      ⟨⟨Ctor.connect, ⟨m, hm, port⟩, rfl⟩, fun _ => child⟩
  | @Diag.bud _ m a entry hm child =>
      ⟨⟨Ctor.bud, ⟨m, a, entry, hm⟩, rfl⟩, fun _ => child⟩

def syntaxLayerPresentation (Sig : Signature) :
    CodeLayerPresentation (poly Sig) (inversion Sig) (Diag Sig) (Diag Sig) :=
  CodeLayerPresentation.ofMaps
    (layerToSyntax Sig)
    (syntaxToLayer Sig)
    (by
      intro n layer
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
              | mk m hm port =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl
          | bud =>
              cases param with
              | mk m a entry hm =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl)
    (by
      intro n t
      cases t with
      | finish => rfl
      | connect hm child port => rfl
      | bud a entry hm child => rfl)

theorem layer_child_rank_lt (Sig : Signature) :
    ∀ {n : Nat} (z : Diag Sig n)
      (q : (poly Sig).Pos
          ((inversion Sig).decode n
            (((syntaxLayerPresentation Sig).iso n).invFun z).1).ctor
          ((inversion Sig).decode n
            (((syntaxLayerPresentation Sig).iso n).invFun z).1).param),
      Diag.rank ((((syntaxLayerPresentation Sig).iso n).invFun z).2 q) <
        Diag.rank z := by
  intro n z q
  cases z with
  | finish =>
      cases q
  | connect hm child port =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]
  | bud a entry hm child =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]

/-- Presentation of rooted open diagram syntax as generated code data. -/
def syntaxPresentation (Sig : Signature) :
    SyntaxPresentation (poly Sig) (inversion Sig) (Diag Sig) :=
  SyntaxPresentation.ofLayer
    (syntaxLayerPresentation Sig)
    (fun _ t => Diag.rank t)
    (layer_child_rank_lt Sig)

/-- Generated coding data for the rooted open diagram syntax. -/
def generatedCode (Sig : Signature) : GeneratedCode (poly Sig) (Diag Sig) :=
  (syntaxPresentation Sig).generatedCode

/--
Rooted open diagrams are bijective with the initial algebra of their dependent
polynomial presentation through the generic generated-code construction.
-/
def syntaxIso (Sig : Signature) (n : Nat) : Mu (poly Sig) n ≃ᵢ Diag Sig n :=
  (generatedCode Sig).iso n

end StringDiagram
end BijForm
