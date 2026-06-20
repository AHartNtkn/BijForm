import BijForm.DependentPolynomial
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

theorem FinChainLayer_left_inv (i : Nat) :
    Function.LeftInverse (FinChainSyntaxToLayer i) (FinChainLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | done =>
          cases out_eq
          have hchild : (fun q => nomatch q) = child := by
            child_eta_empty
          cases hchild
          rfl
      | step =>
          cases param with
          | mk n tag =>
            cases out_eq
            have hchild : (fun _ => child ()) = child := by
              child_eta_unit
            cases hchild
            rfl

theorem FinChainLayer_right_inv (i : Nat) :
    Function.RightInverse (FinChainSyntaxToLayer i) (FinChainLayerToSyntax i) := by
  intro t
  cases t with
  | done => rfl
  | step tag child => rfl

def FinChainSyntaxLayerPresentation :
    CodeLayerPresentation FinChainPoly FinChainInversion FinChainSyntax FinChainSyntax where
  toCarrier := FinChainLayerToSyntax
  fromCarrier := FinChainSyntaxToLayer
  left_inv := FinChainLayer_left_inv
  right_inv := FinChainLayer_right_inv

theorem FinChain_layer_child_rank_lt :
    ∀ {i : Nat} (z : FinChainSyntax i)
      (q : FinChainPoly.Pos
          (FinChainInversion.decode i
            ((FinChainSyntaxLayerPresentation.iso i).invFun z).1).ctor
          (FinChainInversion.decode i
            ((FinChainSyntaxLayerPresentation.iso i).invFun z).1).param),
      FinChainSyntax.rank (((FinChainSyntaxLayerPresentation.iso i).invFun z).2 q) <
        FinChainSyntax.rank z := by
  intro i z q
  cases z with
  | done => cases q
  | step tag child =>
      cases q
      simp [CodeLayerPresentation.iso, FinChainSyntaxLayerPresentation,
        FinChainSyntaxToLayer, FinChainInversion,
        OutputIndexInversion.canonical, FinChainSyntax.rank]

def FinChainSyntaxPresentation :
    SyntaxPresentation FinChainPoly FinChainInversion FinChainSyntax where
  layer := FinChainSyntaxLayerPresentation
  rank := fun _ t => FinChainSyntax.rank t
  child_rank_lt := FinChain_layer_child_rank_lt

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

def FinChainShapeLayerPresentation :
    ShapeLayerPresentation FinChainPoly FinChainInversion where
  shape := FinChainShape
  layer := {
    toCarrier
      | 0, ⟨⟨.done, _n, h⟩, _child⟩ => by
          cases h
          exact ⟨0, by decide⟩
      | 0, ⟨⟨.step, p, h⟩, _child⟩ => by
          cases p with
          | mk _m _tag => cases h
      | n + 1, ⟨⟨.done, _m, h⟩, _child⟩ => by
          cases h
          exact (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).toFun
            (Sum.inl ⟨0, by decide⟩)
      | n + 1, ⟨⟨.step, p, h⟩, child⟩ => by
          cases p with
          | mk m tag =>
              have hmn : m = n := Nat.succ.inj h
              cases hmn
              exact (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).toFun
                (Sum.inr
                  ((CodeAlgebra.finProdPos (n + 2) (FinChainSize n) (FinChainSize_pos n)).toFun
                    (tag, child ())))
    fromCarrier
      | 0, _ => ⟨⟨FinChainCtor.done, (0 : Nat), rfl⟩, fun q => nomatch q⟩
      | n + 1, code =>
          match (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).invFun code with
          | Sum.inl _ => ⟨⟨FinChainCtor.done, (n + 1 : Nat), rfl⟩, fun q => nomatch q⟩
          | Sum.inr payload =>
              let pair :=
                (CodeAlgebra.finProdPos (n + 2) (FinChainSize n) (FinChainSize_pos n)).invFun
                  payload
              ⟨⟨FinChainCtor.step, ⟨n, pair.1⟩, rfl⟩, fun _ => pair.2⟩
    left_inv := by
      intro i layer
      cases i with
      | zero =>
          cases layer with
          | mk code child =>
            cases code with
            | mk ctor param out_eq =>
              cases ctor with
              | done =>
                  cases out_eq
                  have hchild : (fun q => nomatch q) = child := by
                    child_eta_empty
                  cases hchild
                  rfl
              | step =>
                  cases param with
                  | mk _m _tag => cases out_eq
      | succ n =>
          cases layer with
          | mk code child =>
            cases code with
            | mk ctor param out_eq =>
              cases ctor with
              | done =>
                  cases out_eq
                  have hsum :
                      (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).invFun
                          ((CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).toFun
                            (Sum.inl (0 : Fin 1))) =
                        Sum.inl (0 : Fin 1) :=
                    (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).left_inv
                      (Sum.inl (0 : Fin 1))
                  have hchild : (fun q => nomatch q) = child := by
                    child_eta_empty
                  dsimp
                  rw [hsum]
                  cases hchild
                  rfl
              | step =>
                  cases param with
                  | mk m tag =>
                      have hmn : m = n := Nat.succ.inj out_eq
                      cases hmn
                      cases out_eq
                      have hprod :
                          (CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                              (FinChainSize_pos n)).invFun
                              ((CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                                (FinChainSize_pos n)).toFun (tag, child ())) =
                            (tag, child ()) :=
                        (CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                          (FinChainSize_pos n)).left_inv (tag, child ())
                      have hsum :
                          (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).invFun
                              ((CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).toFun
                                (Sum.inr
                                  ((CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                                    (FinChainSize_pos n)).toFun (tag, child ())))) =
                            Sum.inr
                              ((CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                                (FinChainSize_pos n)).toFun (tag, child ())) :=
                        (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).left_inv
                          (Sum.inr
                            ((CodeAlgebra.finProdPos (n + 2) (FinChainSize n)
                              (FinChainSize_pos n)).toFun (tag, child ())))
                      have hchild : (fun _ => child ()) = child := by
                        child_eta_unit
                      dsimp
                      rw [hsum]
                      dsimp
                      rw [hprod]
                      cases hchild
                      rfl
    right_inv := by
      intro i code
      cases i with
      | zero =>
          have hcode : code = ⟨0, by decide⟩ := by
            apply Fin.ext
            have hlt : code.val < 1 := by
              simpa only [FinChainCarrier, FinChainShape, FinChainSize] using code.isLt
            exact Nat.lt_one_iff.mp hlt
          rw [hcode]
      | succ n =>
          dsimp
          generalize hsum :
              (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).invFun code = shape at *
          have hright := (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).right_inv code
          rw [hsum] at hright
          cases shape with
          | inl tag =>
              have htag : tag = ⟨0, by decide⟩ := by
                apply Fin.ext
                omega
              cases htag
              exact hright
          | inr payload =>
              have hprod :=
                (CodeAlgebra.finProdPos (n + 2) (FinChainSize n) (FinChainSize_pos n)).right_inv
                  payload
              dsimp
              rw [hprod]
              exact hright
  }
  rank := fun i _ => i
  child_rank_lt := by
    intro i z q
    cases i with
    | zero =>
        dsimp [CodeLayerPresentation.iso] at q
        cases q
    | succ n =>
        dsimp [CodeLayerPresentation.iso] at q ⊢
        generalize hshape :
            (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)).invFun z = shape at q ⊢
        cases shape with
        | inl _ => cases q
        | inr _ =>
            cases q
            exact Nat.lt_succ_self n

theorem FinChainShape_child_rank_lt :
    ∀ {i : Nat} (z : FinChainCarrier i)
      (q : FinChainPoly.Pos
          (FinChainInversion.decode i
            ((FinChainShapeLayerPresentation.layer.iso i).invFun z).1).ctor
          (FinChainInversion.decode i
            ((FinChainShapeLayerPresentation.layer.iso i).invFun z).1).param),
      FinChainPoly.input
          (FinChainInversion.decode i
            ((FinChainShapeLayerPresentation.layer.iso i).invFun z).1).param q < i := by
  intro i z q
  simpa [FinChainShapeLayerPresentation, FinChainCarrier] using
    FinChainShapeLayerPresentation.child_rank_lt z q

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
  GeneratedCode.shapeFinIso FinChainGeneratedCode FinChainGeneratedShapeCode i rfl

def FinChainSyntaxFinOneIso : FinChainSyntax 0 ≃ᵢ Fin 1 :=
  FinChainSyntaxFinIso 0

def FinChainSyntaxFinThreeIso : FinChainSyntax 1 ≃ᵢ Fin 3 :=
  FinChainSyntaxFinIso 1

def FinChainSyntaxFinTenIso : FinChainSyntax 2 ≃ᵢ Fin 10 :=
  FinChainSyntaxFinIso 2

end Examples
end BijForm
