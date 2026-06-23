import BijForm.RankDescent

namespace BijForm
namespace Examples

open DepPoly

/-- Reference syntax family for numeric expressions indexed by the number of
available variables. -/
inductive NumSyntax : Nat → Type
  | var {k : Nat} (v : Fin (k + 1)) : NumSyntax k
  | zero {k : Nat} : NumSyntax k
  | succ {k : Nat} : NumSyntax k → NumSyntax k
  | plus {k : Nat} : NumSyntax k → NumSyntax k → NumSyntax k
  | times {k : Nat} : NumSyntax k → NumSyntax k → NumSyntax k

namespace NumSyntax

@[simp]
def rank : ∀ {k : Nat}, NumSyntax k → Nat
  | _, var _ => 0
  | _, zero => 0
  | _, succ e => rank e + 1
  | _, plus lhs rhs => Nat.max (rank lhs) (rank rhs) + 1
  | _, times lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end NumSyntax

/-- Polynomial constructors for numeric expressions: variables, zero,
successor, addition, and multiplication. -/
inductive NumCtor where
  | var
  | zero
  | succ
  | plus
  | times
deriving DecidableEq, Repr

def NumParam : NumCtor → Type
  | .var => Σ k : Nat, Fin (k + 1)
  | .zero => Nat
  | .succ => Nat
  | .plus => Nat
  | .times => Nat

def NumOut : (c : NumCtor) → NumParam c → Nat
  | .var, p => p.1
  | .zero, k => k
  | .succ, k => k
  | .plus, k => k
  | .times, k => k

def NumPos : (c : NumCtor) → NumParam c → Type
  | .var, _ => Empty
  | .zero, _ => Empty
  | .succ, _ => Unit
  | .plus, _ => Bool
  | .times, _ => Bool

def NumInput : {c : NumCtor} → (p : NumParam c) → NumPos c p → Nat
  | .var, _, q => nomatch q
  | .zero, _, q => nomatch q
  | .succ, k, _ => k
  | .plus, k, _ => k
  | .times, k, _ => k

/-- Dependent polynomial for numeric expressions indexed by available variables. -/
def NumPoly : DepPoly Nat where
  Ctor := NumCtor
  Param := NumParam
  out := NumOut
  Pos := NumPos
  input := NumInput

/-- Output-index inversion for numeric expressions.  This is the same-fiber
case: the output index is simply exposed as the local context size `k`. -/
def NumInversion : OutputIndexInversion NumPoly :=
  OutputIndexInversion.canonical NumPoly

def NumLayerToSyntax (k : Nat) :
    CodeLayer NumPoly NumInversion NumSyntax k → NumSyntax k
  | ⟨⟨.var, p, h⟩, _child⟩ => by
      cases p with
      | mk k' v =>
        dsimp [NumPoly, NumOut] at h
        cases h.symm
        exact .var v
  | ⟨⟨.zero, k0, h⟩, _child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact .zero
  | ⟨⟨.succ, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact .succ (child ())
  | ⟨⟨.plus, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact .plus (child false) (child true)
  | ⟨⟨.times, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact .times (child false) (child true)

def NumSyntaxToLayer (k : Nat) :
    NumSyntax k → CodeLayer NumPoly NumInversion NumSyntax k
  | .var v => ⟨⟨NumCtor.var, ⟨k, v⟩, rfl⟩, fun q => nomatch q⟩
  | .zero => ⟨⟨NumCtor.zero, (k : Nat), rfl⟩, fun q => nomatch q⟩
  | .succ e => ⟨⟨NumCtor.succ, (k : Nat), rfl⟩, fun _ => e⟩
  | .plus lhs rhs => ⟨⟨NumCtor.plus, (k : Nat), rfl⟩, fun
      | false => lhs
      | true => rhs⟩
  | .times lhs rhs => ⟨⟨NumCtor.times, (k : Nat), rfl⟩, fun
      | false => lhs
      | true => rhs⟩

theorem Num_layer_child_rank_lt :
    ∀ {k : Nat} (z : NumSyntax k)
      (q : NumPoly.Pos
          (NumInversion.decode k (NumSyntaxToLayer k z).1).ctor
          (NumInversion.decode k (NumSyntaxToLayer k z).1).param),
      NumSyntax.rank ((NumSyntaxToLayer k z).2 q) <
        NumSyntax.rank z := by
  rank_descent

def NumSyntaxPresentation : SyntaxPresentation NumPoly NumInversion NumSyntax :=
  SyntaxPresentation.ofLayerIso
    (fun k =>
      { toFun := NumLayerToSyntax k
        invFun := NumSyntaxToLayer k
        left_inv :=
          CodeLayer.canonical_left_inv_by_fiber
            (toCarrier := NumLayerToSyntax)
            (fromCarrier := NumSyntaxToLayer) (by
              intro k ctor param out_eq child
              cases ctor with
              | var =>
                  cases param with
                  | mk k' v =>
                    finish_code_layer_left_inv out_eq child
              | zero =>
                  finish_code_layer_left_inv out_eq child
              | succ =>
                  finish_code_layer_left_inv out_eq child
              | plus =>
                  finish_code_layer_left_inv out_eq child
              | times =>
                  finish_code_layer_left_inv out_eq child) k
        right_inv := by
          intro e
          cases e <;> simp [NumLayerToSyntax, NumSyntaxToLayer] })
    (fun _ e => NumSyntax.rank e)
    Num_layer_child_rank_lt

def NumGeneratedCode : GeneratedCode NumPoly NumSyntax :=
  NumSyntaxPresentation.generatedCode

/-- Numeric expressions as the generic initial algebra are bijective with the
readable recursive syntax family through generated layer coding. -/
def NumSyntaxIso (k : Nat) : Mu NumPoly k ≃ᵢ NumSyntax k :=
  NumGeneratedCode.iso k

abbrev NumNatLayerShape (k : Nat) :=
  Fin (k + 2) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)))

def NumNatLayerShapeTo (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k → NumNatLayerShape k
  | ⟨⟨.var, p, h⟩, _child⟩ => by
      cases p with
      | mk k' v =>
        dsimp [NumPoly, NumOut] at h
        cases h.symm
        exact Sum.inl ⟨v.val, Nat.lt_succ_of_lt v.isLt⟩
  | ⟨⟨.zero, k0, h⟩, _child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact Sum.inl ⟨k + 1, by omega⟩
  | ⟨⟨.succ, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact Sum.inr (Sum.inl (child ()))
  | ⟨⟨.plus, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨⟨.times, k0, h⟩, child⟩ => by
      dsimp [NumPoly, NumOut] at h
      cases h.symm
      exact Sum.inr (Sum.inr (Sum.inr (child false, child true)))

def NumNatLayerShapeInv (k : Nat) :
    NumNatLayerShape k → CodeLayer NumPoly NumInversion (fun _ => Nat) k
  | Sum.inl tag =>
      if h : tag.val < k + 1 then
        ⟨⟨NumCtor.var, ⟨k, ⟨tag.val, h⟩⟩, rfl⟩, fun q => nomatch q⟩
      else
        ⟨⟨NumCtor.zero, (k : Nat), rfl⟩, fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨⟨NumCtor.succ, (k : Nat), rfl⟩, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨⟨NumCtor.plus, (k : Nat), rfl⟩, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr p)) => ⟨⟨NumCtor.times, (k : Nat), rfl⟩, fun
      | false => p.1
      | true => p.2⟩

def NumNatLayerShapeLayerPresentation :
    CodeLayerPresentation NumPoly NumInversion (fun _ => Nat) NumNatLayerShape :=
  CodeLayerPresentation.ofMaps
    NumNatLayerShapeTo
    NumNatLayerShapeInv
    (CodeLayer.canonical_left_inv_by_fiber (by
      intro k ctor param out_eq child
      cases ctor with
      | var =>
        cases param with
        | mk k' v =>
          simp [NumPoly, NumOut] at out_eq
          cases out_eq
          cases v with
          | mk val isLt =>
            dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
            rw [dif_pos isLt]
            exact CodeLayer.ext_rfl
              (P := NumPoly) (H := NumInversion) (Code := fun _ => Nat) (i := k)
              (by child_eta_cases)
      | zero =>
        simp [NumPoly, NumOut] at out_eq
        cases out_eq
        dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
        have hnot : ¬k + 1 < k + 1 := by omega
        rw [dif_neg hnot]
        exact CodeLayer.ext_rfl
          (P := NumPoly) (H := NumInversion) (Code := fun _ => Nat) (i := k)
          (by child_eta_cases)
      | succ =>
        simp [NumPoly, NumOut] at out_eq
        cases out_eq
        dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
        exact CodeLayer.ext_rfl
          (P := NumPoly) (H := NumInversion) (Code := fun _ => Nat) (i := k)
          (by child_eta_cases)
      | plus =>
        simp [NumPoly, NumOut] at out_eq
        cases out_eq
        dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
        exact CodeLayer.ext_rfl
          (P := NumPoly) (H := NumInversion) (Code := fun _ => Nat) (i := k)
          (by child_eta_cases)
      | times =>
        simp [NumPoly, NumOut] at out_eq
        cases out_eq
        dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
        exact CodeLayer.ext_rfl
          (P := NumPoly) (H := NumInversion) (Code := fun _ => Nat) (i := k)
          (by child_eta_cases)))
    (by
    intro k x
    have hshape :
        Function.RightInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
      intro x
      cases x with
      | inl tag =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          by_cases h : tag.val < k + 1
          · rw [dif_pos h]
          · rw [dif_neg h]
            exact congrArg Sum.inl (fin_eq_of_val_eq (by
              have hlt := tag.isLt
              change k + 1 = tag.val
              omega))
      | inr tail =>
          rcases tail with child | (⟨_plusLeft, _plusRight⟩ | ⟨_timesLeft, _timesRight⟩) <;>
            rfl
    exact hshape x)

theorem NumNat_layer_child_lt :
    ∀ {k : Nat} (layer : CodeLayer NumPoly NumInversion (fun _ => Nat) k)
      (q : NumPoly.Pos
          (NumInversion.decode k layer.1).ctor
          (NumInversion.decode k layer.1).param),
      layer.2 q <
        (CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).toFun
          (NumNatLayerShapeTo k layer) := by
  rank_descent [NumNatLayerShapeTo, NumPoly, NumOut, NumPos, NumInput,
    NumInversion]

def NumNatLayerPresentation : NatLayerPresentation NumPoly NumInversion :=
  LayerPresentation.ofLayerShapeChildRank
    NumNatLayerShapeLayerPresentation
    (fun k => CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat)
    (fun _ n => n)
    (by
    intro k layer q
    exact NumNat_layer_child_lt layer q)

def NumNatGeneratedCode : GeneratedNatCode NumPoly :=
  LayerPresentation.generatedCode NumNatLayerPresentation

def NumNatIso (k : Nat) : Mu NumPoly k ≃ᵢ Nat :=
  NumNatGeneratedCode.iso k

def NumSyntaxNatIso (k : Nat) : NumSyntax k ≃ᵢ Nat :=
  GeneratedCode.codeIso NumGeneratedCode NumNatGeneratedCode k

end Examples
end BijForm
