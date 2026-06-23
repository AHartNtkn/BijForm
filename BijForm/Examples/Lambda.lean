import BijForm.InitialAlgebra
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly

/-- De Bruijn lambda terms indexed by context size. Variables are unavailable
at context `0`, while abstraction moves the recursive child to context
`k + 1`. -/
inductive LamSyntax : Nat → Type
  | var {k : Nat} (v : Fin k) : LamSyntax k
  | lam {k : Nat} : LamSyntax (k + 1) → LamSyntax k
  | app {k : Nat} : LamSyntax k → LamSyntax k → LamSyntax k

namespace LamSyntax

@[simp]
def rank : ∀ {k : Nat}, LamSyntax k → Nat
  | _, var _ => 0
  | _, lam body => rank body + 1
  | _, app fn arg => Nat.max (rank fn) (rank arg) + 1

end LamSyntax

/-- Polynomial constructors for de Bruijn lambda terms. -/
inductive LamCtor where
  | var
  | lam
  | app
deriving DecidableEq, Repr

def LamParam : LamCtor → Type
  | .var => Σ k : Nat, Fin k
  | .lam => Nat
  | .app => Nat

def LamOut : (c : LamCtor) → LamParam c → Nat
  | LamCtor.var, p => p.1
  | LamCtor.lam, (k : Nat) => k
  | LamCtor.app, (k : Nat) => k

def LamPos : (c : LamCtor) → LamParam c → Type
  | LamCtor.var, _ => Empty
  | LamCtor.lam, _ => Unit
  | LamCtor.app, _ => Bool

def LamInput : {c : LamCtor} → (p : LamParam c) → LamPos c p → Nat
  | LamCtor.var, _, q => nomatch q
  | LamCtor.lam, (k : Nat), _ => k + 1
  | LamCtor.app, (k : Nat), _ => k

/-- Dependent polynomial for de Bruijn lambda terms. -/
def LamPoly : DepPoly Nat where
  Ctor := LamCtor
  Param := LamParam
  out := LamOut
  Pos := LamPos
  input := LamInput

def LamInversion : OutputIndexInversion LamPoly :=
  OutputIndexInversion.canonical LamPoly

def LamLayerToSyntax (k : Nat) :
    CodeLayer LamPoly LamInversion LamSyntax k → LamSyntax k
  | ⟨⟨.var, p, h⟩, _child⟩ => by
      cases p with
      | mk k' v =>
        cases h
        exact .var v
  | ⟨⟨.lam, _k, h⟩, child⟩ => by
      cases h
      exact .lam (child ())
  | ⟨⟨.app, _k, h⟩, child⟩ => by
      cases h
      exact .app (child false) (child true)

def LamSyntaxToLayer (k : Nat) :
    LamSyntax k → CodeLayer LamPoly LamInversion LamSyntax k
  | .var v => ⟨⟨LamCtor.var, ⟨k, v⟩, rfl⟩, fun q => nomatch q⟩
  | .lam body => ⟨⟨LamCtor.lam, (k : Nat), rfl⟩, fun _ => body⟩
  | .app fn arg => ⟨⟨LamCtor.app, (k : Nat), rfl⟩, fun
      | false => fn
      | true => arg⟩

def LamSyntaxPresentation : LayerPresentation LamPoly LamInversion LamSyntax :=
  LayerPresentation.ofLayerChildRank
    (CodeLayerPresentation.ofMapsExt
      LamLayerToSyntax
      LamSyntaxToLayer
      (by
        intro k layer
        rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
        cases ctor with
        | var =>
            cases param with
            | mk k' v =>
                cases out_eq
                rfl
        | lam =>
            cases out_eq
            rfl
        | app =>
            cases out_eq
            rfl)
      (by
        intro k layer
        rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
        cases ctor with
        | var =>
            cases param with
            | mk k' v =>
                cases out_eq
                exact heq_of_eq (by funext q; cases q)
        | lam =>
            cases out_eq
            exact heq_of_eq (by funext q; cases q; rfl)
        | app =>
            cases out_eq
            exact heq_of_eq (by funext q; cases q <;> rfl))
      (by
        intro k t
        cases t <;> simp [LamLayerToSyntax, LamSyntaxToLayer]))
    (fun _ t => LamSyntax.rank t)
    (by
      intro k layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | var =>
          cases param with
          | mk k' v =>
              cases out_eq
              cases q
      | lam =>
          cases out_eq
          cases q
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMapsExt,
            LamLayerToSyntax]
      | app =>
          cases out_eq
          cases q <;>
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMapsExt,
              LamLayerToSyntax])

def LamGeneratedCode : GeneratedCode LamPoly LamSyntax :=
  LamSyntaxPresentation.generatedCode

/-- Lambda terms as the generic initial algebra are bijective with readable
syntax through generated layer coding. -/
def LamSyntaxIso (k : Nat) : Mu LamPoly k ≃ᵢ LamSyntax k :=
  LamGeneratedCode.iso k

abbrev LamNatLayerShape (k : Nat) :=
  Fin k ⊕ (Nat ⊕ (Nat × Nat))

def LamNatLayerShapeTo (k : Nat) :
    CodeLayer LamPoly LamInversion (fun _ => Nat) k → LamNatLayerShape k
  | ⟨⟨.var, p, h⟩, _child⟩ => by
      cases p with
      | mk k' v =>
        cases h
        exact Sum.inl v
  | ⟨⟨.lam, _k, h⟩, child⟩ => by
      cases h
      exact Sum.inr (Sum.inl (child ()))
  | ⟨⟨.app, _k, h⟩, child⟩ => by
      cases h
      exact Sum.inr (Sum.inr (child false, child true))

def LamNatLayerShapeInv (k : Nat) :
    LamNatLayerShape k → CodeLayer LamPoly LamInversion (fun _ => Nat) k
  | Sum.inl v => ⟨⟨LamCtor.var, ⟨k, v⟩, rfl⟩, fun q => nomatch q⟩
  | Sum.inr (Sum.inl body) => ⟨⟨LamCtor.lam, (k : Nat), rfl⟩, fun _ => body⟩
  | Sum.inr (Sum.inr pair) => ⟨⟨LamCtor.app, (k : Nat), rfl⟩, fun
      | false => pair.1
      | true => pair.2⟩

def LamNatLayerShapeLayerPresentation :
    CodeLayerPresentation LamPoly LamInversion (fun _ => Nat) LamNatLayerShape :=
  CodeLayerPresentation.ofMapsExt
    LamNatLayerShapeTo
    LamNatLayerShapeInv
    (by
      intro k layer
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | var =>
          cases param with
          | mk k' v =>
              cases out_eq
              rfl
      | lam =>
          cases out_eq
          rfl
      | app =>
          cases out_eq
          rfl)
    (by
      intro k layer
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | var =>
          cases param with
          | mk k' v =>
              cases out_eq
              exact heq_of_eq (by funext q; cases q)
      | lam =>
          cases out_eq
          exact heq_of_eq (by funext q; cases q; rfl)
      | app =>
          cases out_eq
          exact heq_of_eq (by funext q; cases q <;> rfl))
    (by
      intro k shape
      cases shape with
      | inl v => rfl
      | inr tail =>
          cases tail with
          | inl body => rfl
          | inr pair =>
              cases pair
              rfl)

def LamNatRank (k n : Nat) : Nat :=
  n + if k = 0 then 1 else 0

/-- The closed code `0` descends through `lam` to context `1` with the same
numeric code, so identity rank on `Nat` would not be enough. -/
theorem LamNatRank_closed_zero_child :
    LamNatRank 1 0 < LamNatRank 0 0 := by
  decide

/-- At the empty context, code `0` selects `lam`, not `app`; otherwise the
decoder would recurse at the same index and code. -/
theorem LamNatLayer_zero_invFun_zero :
    ((LamNatLayerShapeLayerPresentation.transCarrier
      (fun k => CodeAlgebra.finPrefixNat k CodeAlgebra.sumProdNat)).iso 0).invFun 0 =
      ⟨⟨LamCtor.lam, (0 : Nat), rfl⟩, fun _ => 0⟩ := by
  rfl

def LamNatLayerPresentation :
    LayerPresentation LamPoly LamInversion (fun _ => Nat) :=
  LayerPresentation.ofLayerChildRank
    (LamNatLayerShapeLayerPresentation.transCarrier
      (fun k => CodeAlgebra.finPrefixNat k CodeAlgebra.sumProdNat))
    LamNatRank
    (by
      intro k layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | var =>
          cases param with
          | mk k' v =>
              cases out_eq
              cases q
      | lam =>
          cases out_eq
          cases q
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
            LamNatLayerShapeLayerPresentation, CodeLayerPresentation.ofMapsExt,
            LamNatLayerShapeTo, LamNatRank, LamPoly, LamOut, LamInput, LamInversion,
            OutputIndexInversion.canonical]
      | app =>
          cases out_eq
          cases q
          · have h :=
              CodeAlgebra.finPrefixNat_sumProdNat_toFun_inr_inr_fst_pair_lt
                param (child false) (child true)
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
              LamNatLayerShapeLayerPresentation, CodeLayerPresentation.ofMapsExt,
              LamNatLayerShapeTo, LamNatRank, LamPoly, LamOut, LamInput, LamInversion,
              OutputIndexInversion.canonical] at h ⊢
          · have h :=
              CodeAlgebra.finPrefixNat_sumProdNat_toFun_inr_inr_snd_pair_lt
                param (child false) (child true)
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
              LamNatLayerShapeLayerPresentation, CodeLayerPresentation.ofMapsExt,
              LamNatLayerShapeTo, LamNatRank, LamPoly, LamOut, LamInput, LamInversion,
              OutputIndexInversion.canonical] at h ⊢)

def LamNatGeneratedCode : GeneratedNatCode LamPoly :=
  LayerPresentation.generatedCode LamNatLayerPresentation

def LamNatIso (k : Nat) : Mu LamPoly k ≃ᵢ Nat :=
  LamNatGeneratedCode.iso k

def LamSyntaxNatIso (k : Nat) : LamSyntax k ≃ᵢ Nat :=
  GeneratedCode.codeIso LamGeneratedCode LamNatGeneratedCode k

def ClosedLamSyntaxNatIso : LamSyntax 0 ≃ᵢ Nat :=
  LamSyntaxNatIso 0

end Examples
end BijForm
