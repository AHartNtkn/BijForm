import BijForm.DependentPolynomial
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

theorem Lam_layer_child_rank_lt :
    ∀ {k : Nat} (z : LamSyntax k)
      (q : LamPoly.Pos
          (LamInversion.decode k (LamSyntaxToLayer k z).1).ctor
          (LamInversion.decode k (LamSyntaxToLayer k z).1).param),
      LamSyntax.rank ((LamSyntaxToLayer k z).2 q) <
        LamSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | lam body =>
      cases q
      simp [LamSyntaxToLayer, LamInversion,
        OutputIndexInversion.canonical, LamSyntax.rank]
  | app fn arg =>
      cases q
      · simpa [LamSyntaxToLayer, LamInversion,
          OutputIndexInversion.canonical, LamSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (LamSyntax.rank fn) (LamSyntax.rank arg))
      · simpa [LamSyntaxToLayer, LamInversion,
          OutputIndexInversion.canonical, LamSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (LamSyntax.rank fn) (LamSyntax.rank arg))

def LamSyntaxPresentation : SyntaxPresentation LamPoly LamInversion LamSyntax :=
  SyntaxPresentation.ofLayerMaps
    LamLayerToSyntax
    LamSyntaxToLayer
    (by
      intro k layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | var =>
            cases param with
            | mk k' v =>
              cases out_eq
              child_eta_empty_rfl child
          | lam =>
            change LamParam LamCtor.lam at param
            change Nat at param
            cases out_eq
            child_eta_unit_rfl child
          | app =>
            change LamParam LamCtor.app at param
            change Nat at param
            cases out_eq
            child_eta_bool_rfl child)
    (by
      intro k t
      cases t <;> simp [LamLayerToSyntax, LamSyntaxToLayer])
    (fun _ t => LamSyntax.rank t)
    Lam_layer_child_rank_lt

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
  CodeLayerPresentation.ofMaps
    LamNatLayerShapeTo
    LamNatLayerShapeInv
    (by
      intro k layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | var =>
            cases param with
            | mk k' v =>
              cases out_eq
              child_eta_empty_rfl child
          | lam =>
            change LamParam LamCtor.lam at param
            change Nat at param
            cases out_eq
            child_eta_unit_rfl child
          | app =>
            change LamParam LamCtor.app at param
            change Nat at param
            cases out_eq
            child_eta_bool_rfl child)
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

theorem LamNat_layer_child_rank_lt :
    ∀ {k : Nat} (layer : CodeLayer LamPoly LamInversion (fun _ => Nat) k)
      (q : LamPoly.Pos
          (LamInversion.decode k layer.1).ctor
          (LamInversion.decode k layer.1).param),
      LamNatRank
          (LamPoly.input (LamInversion.decode k layer.1).param q)
          (layer.2 q) <
        LamNatRank k
          ((CodeAlgebra.finPrefixNat k CodeAlgebra.sumProdNat).toFun
            (LamNatLayerShapeTo k layer)) := by
  intro k layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | var =>
        intro q
        cases q
      | lam =>
        dsimp [LamPoly, LamParam] at param
        cases out_eq
        intro q
        cases q
        let bodyCode := child ()
        have hparent :
            (CodeAlgebra.finPrefixNat param CodeAlgebra.sumProdNat).toFun
                (LamNatLayerShapeTo param
                  ⟨⟨LamCtor.lam, (param : Nat), rfl⟩, child⟩) =
              param + 2 * bodyCode := by
          simp [bodyCode, LamNatLayerShapeTo,
            CodeAlgebra.finPrefixNat, CodeAlgebra.sumProdNat, CodeAlgebra.toNatSum,
            Iso.trans, Iso.sum, CodeAlgebra.finPlusNat, CodeAlgebra.sumNat, Iso.refl]
        change LamNatRank (param + 1) bodyCode <
          LamNatRank param
            ((CodeAlgebra.finPrefixNat param CodeAlgebra.sumProdNat).toFun
              (LamNatLayerShapeTo param
                ⟨⟨LamCtor.lam, (param : Nat), rfl⟩, child⟩))
        rw [hparent]
        dsimp [LamNatRank]
        by_cases hk : param = 0
        · subst param
          simp
          omega
        · have hkpos : 0 < param := Nat.pos_of_ne_zero hk
          simp [hk]
          omega
      | app =>
        dsimp [LamPoly, LamParam] at param
        cases out_eq
        intro q
        cases q
        · change LamNatRank param (child false) <
            LamNatRank param
              ((CodeAlgebra.finPrefixNat param CodeAlgebra.sumProdNat).toFun
                (LamNatLayerShapeTo param
                  ⟨⟨LamCtor.app, (param : Nat), rfl⟩, child⟩))
          have hchild_lt_parent :=
            CodeAlgebra.finPrefixNat_toFun_inr_lt_of_lt param CodeAlgebra.sumProdNat
              (a := Sum.inr (child false, child true))
              (CodeAlgebra.sumProdNat_toFun_inr_fst_lt (child false, child true))
          dsimp [LamNatRank]
          by_cases hk : param = 0
          · simpa [hk, LamNatLayerShapeTo] using hchild_lt_parent
          · simpa [hk, LamNatLayerShapeTo] using hchild_lt_parent
        · change LamNatRank param (child true) <
            LamNatRank param
              ((CodeAlgebra.finPrefixNat param CodeAlgebra.sumProdNat).toFun
                (LamNatLayerShapeTo param
                  ⟨⟨LamCtor.app, (param : Nat), rfl⟩, child⟩))
          have hchild_lt_parent :=
            CodeAlgebra.finPrefixNat_toFun_inr_lt_of_lt param CodeAlgebra.sumProdNat
              (a := Sum.inr (child false, child true))
              (CodeAlgebra.sumProdNat_toFun_inr_snd_lt (child false, child true))
          dsimp [LamNatRank]
          by_cases hk : param = 0
          · simpa [hk, LamNatLayerShapeTo] using hchild_lt_parent
          · simpa [hk, LamNatLayerShapeTo] using hchild_lt_parent

def LamNatLayerShapePresentation :
    LayerShapePresentation LamPoly LamInversion (fun _ => Nat) LamNatLayerShape :=
  LayerShapePresentation.ofLayerChildRank
    LamNatLayerShapeLayerPresentation
    (fun k => CodeAlgebra.finPrefixNat k CodeAlgebra.sumProdNat)
    LamNatRank
    (by
    intro k layer q
    exact LamNat_layer_child_rank_lt layer q)

def LamNatLayerPresentation : RankedNatLayerPresentation LamPoly LamInversion :=
  LamNatLayerShapePresentation.toRankedNatLayerPresentationSelf

def LamNatGeneratedCode : GeneratedRankedNatCode LamPoly :=
  LamNatLayerPresentation.generatedCode

def LamNatIso (k : Nat) : Mu LamPoly k ≃ᵢ Nat :=
  LamNatGeneratedCode.iso k

def LamSyntaxNatIso (k : Nat) : LamSyntax k ≃ᵢ Nat :=
  GeneratedCode.rankedNatCodeIso LamGeneratedCode LamNatGeneratedCode k

def ClosedLamSyntaxNatIso : LamSyntax 0 ≃ᵢ Nat :=
  LamSyntaxNatIso 0

end Examples
end BijForm
