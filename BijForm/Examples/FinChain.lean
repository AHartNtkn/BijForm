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

def FinChainLayerIso (i : Nat) :
    CodeLayer FinChainPoly FinChainInversion FinChainSyntax i ≃ᵢ FinChainSyntax i where
  toFun := FinChainLayerToSyntax i
  invFun := FinChainSyntaxToLayer i
  left_inv := FinChainLayer_left_inv i
  right_inv := FinChainLayer_right_inv i

theorem FinChain_layer_child_rank_lt :
    ∀ {i : Nat} (z : FinChainSyntax i)
      (q : FinChainPoly.Pos
          (FinChainInversion.decode i ((FinChainLayerIso i).invFun z).1).ctor
          (FinChainInversion.decode i ((FinChainLayerIso i).invFun z).1).param),
      FinChainSyntax.rank (((FinChainLayerIso i).invFun z).2 q) < FinChainSyntax.rank z := by
  intro i z q
  cases z with
  | done => cases q
  | step tag child =>
      cases q
      simp [FinChainLayerIso, FinChainSyntaxToLayer, FinChainInversion,
        OutputIndexInversion.canonical, FinChainSyntax.rank]

def FinChainGeneratedCode : GeneratedCode FinChainPoly FinChainSyntax where
  inversion := FinChainInversion
  layer := FinChainLayerIso
  rank := fun _ t => FinChainSyntax.rank t
  child_rank_lt := FinChain_layer_child_rank_lt

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

def FinChainZeroLayerIso :
    CodeLayer FinChainPoly FinChainInversion FinChainCarrier 0 ≃ᵢ FinChainCarrier 0 where
  toFun
    | ⟨⟨.done, _n, h⟩, _child⟩ => by
        cases h
        exact ⟨0, by decide⟩
    | ⟨⟨.step, p, h⟩, _child⟩ => by
        cases p with
        | mk _m _tag => cases h
  invFun := fun _ => ⟨⟨FinChainCtor.done, (0 : Nat), rfl⟩, fun q => nomatch q⟩
  left_inv := by
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
            | mk _m _tag => cases out_eq
  right_inv := by
    intro code
    have hcode : code = ⟨0, by decide⟩ := by
      apply Fin.ext
      have hlt : code.val < 1 := by
        simpa only [FinChainCarrier, FinChainShape, FinChainSize] using code.isLt
      exact Nat.lt_one_iff.mp hlt
    rw [hcode]

abbrev FinChainSuccLayerShape (n : Nat) :=
  Fin 1 ⊕ (Fin (n + 2) × FinChainCarrier n)

def FinChainSuccLayerShapeIso (n : Nat) :
    CodeLayer FinChainPoly FinChainInversion FinChainCarrier (n + 1) ≃ᵢ
      FinChainSuccLayerShape n where
  toFun
    | ⟨⟨.done, _m, h⟩, _child⟩ => by
        cases h
        exact Sum.inl ⟨0, by decide⟩
    | ⟨⟨.step, p, h⟩, child⟩ => by
        cases p with
        | mk m tag =>
          cases h
          exact Sum.inr (tag, child ())
  invFun
    | Sum.inl _ => ⟨⟨FinChainCtor.done, (n + 1 : Nat), rfl⟩, fun q => nomatch q⟩
    | Sum.inr payload =>
        ⟨⟨FinChainCtor.step, ⟨n, payload.1⟩, rfl⟩, fun _ => payload.2⟩
  left_inv := by
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
            | mk m tag =>
              cases out_eq
              have hchild : (fun _ => child ()) = child := by
                child_eta_unit
              cases hchild
              rfl
  right_inv := by
    intro shape
    cases shape with
    | inl tag =>
        apply congrArg Sum.inl
        apply Fin.ext
        omega
    | inr payload =>
        cases payload
        rfl

def FinChainSuccLayerIso (n : Nat) :
    CodeLayer FinChainPoly FinChainInversion FinChainCarrier (n + 1) ≃ᵢ
      FinChainCarrier (n + 1) :=
  Iso.trans (FinChainSuccLayerShapeIso n)
    (Iso.trans
      (Iso.sum (Iso.refl (Fin 1))
        (CodeAlgebra.finProdPos (n + 2) (FinChainSize n) (FinChainSize_pos n)))
      (CodeAlgebra.finSum 1 ((n + 2) * FinChainSize n)))

def FinChainShapeLayerIso :
    ∀ i, CodeLayer FinChainPoly FinChainInversion FinChainCarrier i ≃ᵢ FinChainCarrier i
  | 0 => FinChainZeroLayerIso
  | n + 1 => FinChainSuccLayerIso n

theorem FinChainShape_child_rank_lt :
    ∀ {i : Nat} (z : FinChainCarrier i)
      (q : FinChainPoly.Pos
          (FinChainInversion.decode i ((FinChainShapeLayerIso i).invFun z).1).ctor
          (FinChainInversion.decode i ((FinChainShapeLayerIso i).invFun z).1).param),
      FinChainPoly.input
          (FinChainInversion.decode i ((FinChainShapeLayerIso i).invFun z).1).param q < i := by
  intro i z
  generalize hlayer : (FinChainShapeLayerIso i).invFun z = layer
  intro q
  change FinChainPoly.input (FinChainInversion.decode i layer.1).param q < i
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | done => cases q
      | step =>
          cases param with
          | mk n tag =>
            cases out_eq
            cases q
            change n < n + 1
            exact Nat.lt_succ_self n

def FinChainGeneratedShapeCode : GeneratedShapeCode FinChainPoly where
  shape := FinChainShape
  inversion := FinChainInversion
  layer := FinChainShapeLayerIso
  rank := fun i _ => i
  child_rank_lt := by
    intro i z q
    exact FinChainShape_child_rank_lt z q

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
