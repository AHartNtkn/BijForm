import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

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

theorem NumLayer_left_inv (k : Nat) :
    Function.LeftInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | var =>
          cases param with
          | mk k' v =>
            dsimp [NumPoly, NumOut] at out_eq
            cases out_eq.symm
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              child_eta_empty
            cases hchild
            rfl
      | zero =>
          change NumParam NumCtor.zero at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          have hchild : (fun q => nomatch q) = child := by
            child_eta_empty
          cases hchild
          rfl
      | succ =>
          change NumParam NumCtor.succ at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          have hchild : (fun _ => child ()) = child := by
            child_eta_unit
          cases hchild
          rfl
      | plus =>
          change NumParam NumCtor.plus at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            child_eta_bool
          rw [hchild]
          rfl
      | times =>
          change NumParam NumCtor.times at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            child_eta_bool
          rw [hchild]
          rfl

theorem NumLayer_right_inv (k : Nat) :
    Function.RightInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro e
  cases e <;> simp [NumLayerToSyntax, NumSyntaxToLayer]

def NumSyntaxLayerPresentation :
    CodeLayerPresentation NumPoly NumInversion NumSyntax NumSyntax where
  toCarrier := NumLayerToSyntax
  fromCarrier := NumSyntaxToLayer
  left_inv := NumLayer_left_inv
  right_inv := NumLayer_right_inv

theorem Num_layer_child_rank_lt :
    ∀ {k : Nat} (z : NumSyntax k)
      (q : NumPoly.Pos
          (NumInversion.decode k ((NumSyntaxLayerPresentation.iso k).invFun z).1).ctor
          (NumInversion.decode k ((NumSyntaxLayerPresentation.iso k).invFun z).1).param),
      NumSyntax.rank (((NumSyntaxLayerPresentation.iso k).invFun z).2 q) <
        NumSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | zero => cases q
  | succ e =>
      cases q
      simp [CodeLayerPresentation.iso, NumSyntaxLayerPresentation, NumSyntaxToLayer,
        NumInversion,
        OutputIndexInversion.canonical, NumSyntax.rank]
  | plus lhs rhs =>
      cases q
      · simpa [CodeLayerPresentation.iso, NumSyntaxLayerPresentation, NumSyntaxToLayer,
          NumInversion,
          OutputIndexInversion.canonical,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [CodeLayerPresentation.iso, NumSyntaxLayerPresentation, NumSyntaxToLayer,
          NumInversion,
          OutputIndexInversion.canonical,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))
  | times lhs rhs =>
      cases q
      · simpa [CodeLayerPresentation.iso, NumSyntaxLayerPresentation, NumSyntaxToLayer,
          NumInversion,
          OutputIndexInversion.canonical,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [CodeLayerPresentation.iso, NumSyntaxLayerPresentation, NumSyntaxToLayer,
          NumInversion,
          OutputIndexInversion.canonical,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))

def NumSyntaxPresentation : SyntaxPresentation NumPoly NumInversion NumSyntax where
  layer := NumSyntaxLayerPresentation
  rank := fun _ e => NumSyntax.rank e
  child_rank_lt := Num_layer_child_rank_lt

def NumGeneratedCode : GeneratedCode NumPoly NumSyntax :=
  NumSyntaxPresentation.generatedCode

def NumWellFoundedCode : WellFoundedCode NumPoly NumSyntax :=
  NumGeneratedCode.toWellFoundedCode

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

def NumNatCodeLayerPresentation :
    CodeLayerPresentation NumPoly NumInversion (fun _ => Nat) (fun _ => Nat) where
  toCarrier k layer :=
    (CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).toFun
      (NumNatLayerShapeTo k layer)
  fromCarrier k n :=
    NumNatLayerShapeInv k
      ((CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).invFun n)
  left_inv := by
    intro k x
    have hshape :
        Function.LeftInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
      intro x
      cases x with
      | mk code child =>
          cases code with
          | mk ctor param out_eq =>
            cases ctor with
            | var =>
              cases param with
              | mk k' v =>
                dsimp [NumPoly, NumOut] at out_eq
                cases out_eq.symm
                cases out_eq
                cases v with
                | mk val isLt =>
                  dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
                  rw [dif_pos isLt]
                  have hchild : (fun q => nomatch q) = child := by
                    child_eta_empty
                  cases hchild
                  refine Sigma.ext rfl ?_
                  apply heq_of_eq
                  child_eta_empty
            | zero =>
              change NumParam NumCtor.zero at param
              change Nat at param
              dsimp [NumPoly, NumOut] at out_eq
              cases out_eq.symm
              cases out_eq
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              have hnot : ¬k + 1 < k + 1 := by omega
              rw [dif_neg hnot]
              have hchild : (fun q => nomatch q) = child := by
                child_eta_empty
              cases hchild
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              child_eta_empty
            | succ =>
              change NumParam NumCtor.succ at param
              change Nat at param
              dsimp [NumPoly, NumOut] at out_eq
              cases out_eq.symm
              cases out_eq
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              have hchild : (fun _ => child ()) = child := by
                child_eta_unit
              cases hchild
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              child_eta_unit
            | plus =>
              change NumParam NumCtor.plus at param
              change Nat at param
              dsimp [NumPoly, NumOut] at out_eq
              cases out_eq.symm
              cases out_eq
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              have hchild : child = (fun
                  | false => child false
                  | true => child true) := by
                child_eta_bool
              rw [hchild]
              rfl
            | times =>
              change NumParam NumCtor.times at param
              change Nat at param
              dsimp [NumPoly, NumOut] at out_eq
              cases out_eq.symm
              cases out_eq
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              have hchild : child = (fun
                  | false => child false
                  | true => child true) := by
                child_eta_bool
              rw [hchild]
              rfl
    change
      NumNatLayerShapeInv k
        ((CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).invFun
          ((CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).toFun
            (NumNatLayerShapeTo k x))) = x
    rw [(CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).left_inv
      (NumNatLayerShapeTo k x)]
    exact hshape x
  right_inv := by
    intro k n
    have hshape :
        Function.RightInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
      intro x
      cases x with
      | inl tag =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          by_cases h : tag.val < k + 1
          · rw [dif_pos h]
          · rw [dif_neg h]
            exact congrArg Sum.inl (Fin.ext (by
              have hlt := tag.isLt
              change k + 1 = tag.val
              omega))
      | inr tail =>
          cases tail with
          | inl child => rfl
          | inr rest =>
              cases rest with
              | inl p =>
                  cases p
                  rfl
              | inr p =>
                  cases p
                  rfl
    change
      (CodeAlgebra.finPrefixNat (k + 2) CodeAlgebra.natOrProdOrProdNat).toFun
        (NumNatLayerShapeTo k
          (NumNatLayerShapeInv k
            ((CodeAlgebra.finPrefixNat (k + 2)
              CodeAlgebra.natOrProdOrProdNat).invFun n))) = n
    rw [hshape ((CodeAlgebra.finPrefixNat (k + 2)
      CodeAlgebra.natOrProdOrProdNat).invFun n)]
    exact (CodeAlgebra.finPrefixNat (k + 2)
      CodeAlgebra.natOrProdOrProdNat).right_inv n

theorem NumNat_layer_child_lt :
    ∀ {k : Nat} (layer : CodeLayer NumPoly NumInversion (fun _ => Nat) k)
      (q : NumPoly.Pos
          (NumInversion.decode k layer.1).ctor
          (NumInversion.decode k layer.1).param),
      layer.2 q < (NumNatCodeLayerPresentation.iso k).toFun layer := by
  intro k layer
  cases layer with
  | mk code child =>
      cases code with
      | mk ctor param out_eq =>
        cases ctor with
        | var =>
          cases param with
          | mk k' v =>
            intro q
            cases q
        | zero =>
          intro q
          cases q
        | succ =>
          change NumParam NumCtor.succ at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          intro q
          cases q
          let c := child ()
          have htail := CodeAlgebra.natOrProdOrProdNat_toFun_inl_le c
          have hlt := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
            (k + 2) (by omega) CodeAlgebra.natOrProdOrProdNat
            (a := Sum.inl c) htail
          simpa [c, CodeLayerPresentation.iso, NumNatCodeLayerPresentation,
            NumNatLayerShapeTo] using hlt
        | plus =>
          change NumParam NumCtor.plus at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          intro q
          cases q
          · have htail :=
              CodeAlgebra.natOrProdOrProdNat_toFun_inr_inl_fst_le
                (child false, child true)
            have hlt := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
              (k + 2) (by omega) CodeAlgebra.natOrProdOrProdNat
              (a := Sum.inr (Sum.inl (child false, child true))) htail
            simpa [CodeLayerPresentation.iso, NumNatCodeLayerPresentation,
              NumNatLayerShapeTo] using hlt
          · have htail :=
              CodeAlgebra.natOrProdOrProdNat_toFun_inr_inl_snd_le
                (child false, child true)
            have hlt := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
              (k + 2) (by omega) CodeAlgebra.natOrProdOrProdNat
              (a := Sum.inr (Sum.inl (child false, child true))) htail
            simpa [CodeLayerPresentation.iso, NumNatCodeLayerPresentation,
              NumNatLayerShapeTo] using hlt
        | times =>
          change NumParam NumCtor.times at param
          change Nat at param
          dsimp [NumPoly, NumOut] at out_eq
          cases out_eq.symm
          cases out_eq
          intro q
          cases q
          · have htail :=
              CodeAlgebra.natOrProdOrProdNat_toFun_inr_inr_fst_le
                (child false, child true)
            have hlt := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
              (k + 2) (by omega) CodeAlgebra.natOrProdOrProdNat
              (a := Sum.inr (Sum.inr (child false, child true))) htail
            simpa [CodeLayerPresentation.iso, NumNatCodeLayerPresentation,
              NumNatLayerShapeTo] using hlt
          · have htail :=
              CodeAlgebra.natOrProdOrProdNat_toFun_inr_inr_snd_le
                (child false, child true)
            have hlt := CodeAlgebra.finPrefixNat_toFun_inr_lt_of_le
              (k + 2) (by omega) CodeAlgebra.natOrProdOrProdNat
              (a := Sum.inr (Sum.inr (child false, child true))) htail
            simpa [CodeLayerPresentation.iso, NumNatCodeLayerPresentation,
              NumNatLayerShapeTo] using hlt

def NumNatLayerPresentation : NatLayerPresentation NumPoly NumInversion where
  layer := NumNatCodeLayerPresentation
  child_lt := by
    intro k n q
    have h :=
      NumNat_layer_child_lt ((NumNatCodeLayerPresentation.iso k).invFun n) q
    rw [(NumNatCodeLayerPresentation.iso k).right_inv n] at h
    exact h

def NumNatGeneratedCode : GeneratedNatCode NumPoly :=
  NumNatLayerPresentation.generatedCode

def NumNatIso (k : Nat) : Mu NumPoly k ≃ᵢ Nat :=
  NumNatGeneratedCode.iso k

def NumSyntaxNatIso (k : Nat) : NumSyntax k ≃ᵢ Nat :=
  GeneratedCode.natCodeIso NumGeneratedCode NumNatGeneratedCode k

end Examples
end BijForm
