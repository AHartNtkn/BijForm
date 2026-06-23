import BijForm.InitialAlgebra
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly

/-- Reference syntax for bounded tagged chains.  At bound `n + 1`, a chain may
stop immediately or choose one of `n + 2` tags and continue at bound `n`. -/
inductive FinChainSyntax : Nat → Type
  | done {n : Nat} : FinChainSyntax n
  | step {n : Nat} (tag : Fin (n + 2)) : FinChainSyntax n → FinChainSyntax (n + 1)

namespace FinChainSyntax

@[simp]
def rank : ∀ {i : Nat}, FinChainSyntax i → Nat
  | _, done => 0
  | _, step _ child => rank child + 1

end FinChainSyntax

/-- Polynomial constructors for bounded tagged chains. -/
inductive FinChainCtor where
  | done
  | step
deriving DecidableEq, Repr

def FinChainParam : FinChainCtor → Type
  | .done => Nat
  | .step => Σ n : Nat, Fin (n + 2)

def FinChainOut : (c : FinChainCtor) → FinChainParam c → Nat
  | .done, (n : Nat) => n
  | .step, p => p.1 + 1

def FinChainPos : (c : FinChainCtor) → FinChainParam c → Type
  | .done, _ => Empty
  | .step, _ => Unit

def FinChainInput : {c : FinChainCtor} → (p : FinChainParam c) → FinChainPos c p → Nat
  | .done, _, q => nomatch q
  | .step, p, _ => p.1

/-- Dependent polynomial for bounded tagged chains. -/
def FinChainPoly : DepPoly Nat where
  Ctor := FinChainCtor
  Param := FinChainParam
  out := FinChainOut
  Pos := FinChainPos
  input := FinChainInput

def FinChainInversion : OutputIndexInversion FinChainPoly :=
  OutputIndexInversion.canonical FinChainPoly

def FinChainLayerToSyntax (i : Nat) :
    CodeLayer FinChainPoly FinChainInversion FinChainSyntax i → FinChainSyntax i
  | ⟨⟨.done, _n, h⟩, _child⟩ => by
      cases h
      exact .done
  | ⟨⟨.step, p, h⟩, child⟩ => by
      cases p with
      | mk n tag =>
          cases h
          exact .step tag (child ())

def FinChainSyntaxToLayer (i : Nat) :
    FinChainSyntax i → CodeLayer FinChainPoly FinChainInversion FinChainSyntax i
  | .done => ⟨⟨FinChainCtor.done, (i : Nat), rfl⟩, fun q => nomatch q⟩
  | @FinChainSyntax.step n tag child =>
      ⟨⟨FinChainCtor.step, ⟨n, tag⟩, rfl⟩, fun _ => child⟩

def FinChainSyntaxPresentation :
    SyntaxPresentation FinChainPoly FinChainInversion FinChainSyntax :=
  SyntaxPresentation.ofLayerIsoChildRank
    (fun i =>
      { toFun := FinChainLayerToSyntax i
        invFun := FinChainSyntaxToLayer i
        left_inv :=
          CodeLayer.canonical_left_inv_by_fiber
            (toCarrier := FinChainLayerToSyntax)
            (fromCarrier := FinChainSyntaxToLayer) (by
              intro i ctor param out_eq child
              cases ctor with
              | done =>
                  finish_code_layer_left_inv out_eq child
              | step =>
                  cases param with
                  | mk n tag =>
                    finish_code_layer_left_inv out_eq child) i
        right_inv := by
          intro t
          cases t with
          | done => rfl
          | step tag child => rfl })
    (fun _ t => FinChainSyntax.rank t)
    (by
      intro i layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | done =>
          cases out_eq
          cases q
      | step =>
          cases param with
          | mk n tag =>
              cases out_eq
              cases q
              simp [FinChainLayerToSyntax])

def FinChainGeneratedCode : GeneratedCode FinChainPoly FinChainSyntax :=
  FinChainSyntaxPresentation.generatedCode

/-- Bounded tagged chains as the generic initial algebra are bijective with
readable syntax through generated layer coding. -/
def FinChainSyntaxIso (i : Nat) : Mu FinChainPoly i ≃ᵢ FinChainSyntax i :=
  FinChainGeneratedCode.iso i

def FinChainSize : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + (n + 2) * FinChainSize n

theorem FinChainSize_pos : ∀ n : Nat, 0 < FinChainSize n
  | 0 => by decide
  | n + 1 => by
      dsimp [FinChainSize]
      exact Nat.add_pos_left (by decide : 0 < 1) ((n + 2) * FinChainSize n)

def FinChainShape (i : Nat) : CodeShape :=
  .finite (FinChainSize i)

abbrev FinChainCarrier (i : Nat) : Type :=
  (FinChainShape i).Carrier

def FinChainLayerShape : Nat → Type
  | 0 => Fin 1
  | n + 1 => Fin 1 ⊕ (Fin (n + 2) × FinChainCarrier n)

def FinChainLayerCarrierIso : ∀ i, FinChainLayerShape i ≃ᵢ FinChainCarrier i
  | 0 => Iso.refl (Fin 1)
  | n + 1 =>
      Iso.trans
        (Iso.sum (Iso.refl (Fin 1))
          (CodeAlgebra.finProdPos (n + 2) (FinChainSize n) (FinChainSize_pos n)))
        (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n))

def FinChainLayerShapeLayerPresentation :
    CodeLayerPresentation FinChainPoly FinChainInversion FinChainCarrier FinChainLayerShape :=
  CodeLayerPresentation.ofMaps
    (fun
      | 0, ⟨⟨.done, _n, h⟩, _child⟩ => by
          cases h
          exact ⟨0, by decide⟩
      | 0, ⟨⟨.step, p, h⟩, _child⟩ => by
          cases p with
          | mk _m _tag => cases h
      | n + 1, ⟨⟨.done, _m, h⟩, _child⟩ => by
          cases h
          exact Sum.inl ⟨0, by decide⟩
      | n + 1, ⟨⟨.step, p, h⟩, child⟩ => by
          cases p with
          | mk m tag =>
              have hmn : m = n := Nat.succ.inj h
              cases hmn
              exact Sum.inr (tag, child ()))
    (fun
      | 0, _ => ⟨⟨FinChainCtor.done, (0 : Nat), rfl⟩, fun q => nomatch q⟩
      | n + 1, shape =>
          match shape with
          | Sum.inl _ => ⟨⟨FinChainCtor.done, (n + 1 : Nat), rfl⟩, fun q => nomatch q⟩
          | Sum.inr pair =>
              ⟨⟨FinChainCtor.step, ⟨n, pair.1⟩, rfl⟩, fun _ => pair.2⟩)
    (CodeLayer.canonical_left_inv_by_fiber (by
      intro i ctor param out_eq child
      cases i with
      | zero =>
          cases ctor with
          | done =>
              finish_code_layer_left_inv out_eq child
          | step =>
              cases param with
              | mk _m _tag => cases out_eq
      | succ n =>
          cases ctor with
          | done =>
              finish_code_layer_left_inv out_eq child
          | step =>
              cases param with
              | mk m tag =>
                  have hmn : m = n := Nat.succ.inj out_eq
                  cases hmn
                  finish_code_layer_left_inv out_eq child))
    (by
      intro i shape
      cases i with
      | zero =>
          have hcode : shape = ⟨0, by decide⟩ := by
            apply fin_eq_of_val_eq
            have hlt : shape.val < 1 := by
              exact shape.isLt
            exact Nat.lt_one_iff.mp hlt
          rw [hcode]
      | succ n =>
          cases shape with
          | inl tag =>
              have htag : tag = ⟨0, by decide⟩ := by
                exact fin_one_eq tag ⟨0, by decide⟩
              cases htag
              rfl
          | inr pair =>
              cases pair
              rfl)

def FinChainLayerPresentation :
    LayerPresentation FinChainPoly FinChainInversion FinChainCarrier :=
  LayerPresentation.ofLayerChildRank
    (FinChainLayerShapeLayerPresentation.transCarrier FinChainLayerCarrierIso)
    (fun i _ => i)
    (LayerPresentation.layerChildRankOfShapeChildRank
      FinChainLayerShapeLayerPresentation
      FinChainLayerCarrierIso
      (fun i _ => i)
      (by
        intro i shape q
        cases i with
        | zero =>
            cases q
        | succ n =>
            cases shape with
            | inl done =>
                cases q
            | inr pair =>
                cases q
                simp [FinChainLayerShapeLayerPresentation, FinChainLayerShape,
                  FinChainCarrier, FinChainShape, FinChainPos, FinChainInput,
                  FinChainPoly, FinChainOut, FinChainInversion,
                  OutputIndexInversion.canonical]))

def FinChainShapeLayerPresentation :
    ShapeLayerPresentation FinChainPoly FinChainInversion :=
  { shape := FinChainShape
    presentation := FinChainLayerPresentation }

def FinChainGeneratedShapeCode : GeneratedShapeCode FinChainPoly :=
  FinChainShapeLayerPresentation.generatedCode

def FinChainShapeIso (i : Nat) : Mu FinChainPoly i ≃ᵢ FinChainCarrier i :=
  FinChainGeneratedShapeCode.iso i

def FinChainSyntaxShapeIso (i : Nat) : FinChainSyntax i ≃ᵢ FinChainCarrier i :=
  GeneratedCode.shapeCodeIso FinChainGeneratedCode FinChainGeneratedShapeCode i

/-- Every bounded tagged-chain index is finite, with cardinality given by
`FinChainSize`. This theorem exercises generated finite carriers with many
different `Fin k` values rather than only a singleton finite case. -/
def FinChainSyntaxFinIso (i : Nat) : FinChainSyntax i ≃ᵢ Fin (FinChainSize i) :=
  GeneratedCode.shapeFinIso
    FinChainGeneratedCode FinChainGeneratedShapeCode i rfl

def FinChainSyntaxFinOneIso : FinChainSyntax 0 ≃ᵢ Fin 1 :=
  FinChainSyntaxFinIso 0

def FinChainSyntaxFinThreeIso : FinChainSyntax 1 ≃ᵢ Fin 3 :=
  FinChainSyntaxFinIso 1

def FinChainSyntaxFinTenIso : FinChainSyntax 2 ≃ᵢ Fin 10 :=
  FinChainSyntaxFinIso 2

end Examples
end BijForm
