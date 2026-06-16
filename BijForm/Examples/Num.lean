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

inductive NumCode (k : Nat) where
  | var (v : Fin (k + 1))
  | zero
  | succ
  | plus
  | times

def NumDecode (k : Nat) : NumCode k → Fiber NumPoly k
  | .var v => ⟨.var, ⟨k, v⟩, rfl⟩
  | .zero => ⟨.zero, k, rfl⟩
  | .succ => ⟨.succ, k, rfl⟩
  | .plus => ⟨.plus, k, rfl⟩
  | .times => ⟨.times, k, rfl⟩

def NumEncode (k : Nat) : Fiber NumPoly k → NumCode k
  | ⟨.var, p, h⟩ =>
      have _ : NumPoly.out NumCtor.var p = k := h
      .var (k := k) (h ▸ p.2)
  | ⟨.zero, _, _⟩ => .zero
  | ⟨.succ, _, _⟩ => .succ
  | ⟨.plus, _, _⟩ => .plus
  | ⟨.times, _, _⟩ => .times

theorem Num_decode_encode (k : Nat) (f : Fiber NumPoly k) :
    NumDecode k (NumEncode k f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | var =>
        cases param with
        | mk k' v =>
          cases out_eq
          rfl
    | zero =>
        cases out_eq
        rfl
    | succ =>
        cases out_eq
        rfl
    | plus =>
        cases out_eq
        rfl
    | times =>
        cases out_eq
        rfl

theorem Num_encode_decode (k : Nat) (c : NumCode k) :
    NumEncode k (NumDecode k c) = c := by
  cases c <;> rfl

/-- Output-index inversion for numeric expressions.  This is the same-fiber
case: the output index is simply exposed as the local context size `k`. -/
def NumInversion : OutputIndexInversion NumPoly where
  Code := NumCode
  decode := NumDecode
  encode := NumEncode
  decode_encode := Num_decode_encode
  encode_decode := Num_encode_decode

def NumLayerToSyntax (k : Nat) :
    CodeLayer NumPoly NumInversion NumSyntax k → NumSyntax k
  | ⟨.var v, _child⟩ =>
      .var v
  | ⟨.zero, _child⟩ =>
      .zero
  | ⟨.succ, child⟩ =>
      .succ (child ())
  | ⟨.plus, child⟩ =>
      .plus (child false) (child true)
  | ⟨.times, child⟩ =>
      .times (child false) (child true)

def NumSyntaxToLayer (k : Nat) :
    NumSyntax k → CodeLayer NumPoly NumInversion NumSyntax k
  | .var v => ⟨.var v, fun q => nomatch q⟩
  | .zero => ⟨.zero, fun q => nomatch q⟩
  | .succ e => ⟨.succ, fun _ => e⟩
  | .plus lhs rhs => ⟨.plus, fun (b : Bool) => if b then rhs else lhs⟩
  | .times lhs rhs => ⟨.times, fun (b : Bool) => if b then rhs else lhs⟩

theorem NumLayer_left_inv (k : Nat) :
    Function.LeftInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
      | var v =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | zero =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rfl
      | succ =>
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          rfl
      | plus =>
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl
      | times =>
          have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
            funext q
            cases q <;> rfl
          rw [hchild]
          rfl

theorem NumLayer_right_inv (k : Nat) :
    Function.RightInverse (NumSyntaxToLayer k) (NumLayerToSyntax k) := by
  intro e
  cases e <;> simp [NumLayerToSyntax, NumSyntaxToLayer]

def NumLayerIso (k : Nat) :
    CodeLayer NumPoly NumInversion NumSyntax k ≃ᵢ NumSyntax k where
  toFun := NumLayerToSyntax k
  invFun := NumSyntaxToLayer k
  left_inv := NumLayer_left_inv k
  right_inv := NumLayer_right_inv k

theorem Num_layer_child_rank_lt :
    ∀ {k : Nat} (z : NumSyntax k)
      (q : NumPoly.Pos
          (NumInversion.decode k ((NumLayerIso k).invFun z).1).ctor
          (NumInversion.decode k ((NumLayerIso k).invFun z).1).param),
      NumSyntax.rank (((NumLayerIso k).invFun z).2 q) < NumSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | zero => cases q
  | succ e =>
      cases q
      simp [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode, NumSyntax.rank]
  | plus lhs rhs =>
      cases q
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))
  | times lhs rhs =>
      cases q
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (NumSyntax.rank lhs) (NumSyntax.rank rhs))
      · simpa [NumLayerIso, NumSyntaxToLayer, NumInversion, NumDecode,
          NumSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (NumSyntax.rank lhs) (NumSyntax.rank rhs))

def NumGeneratedCode : GeneratedCode NumPoly NumSyntax where
  inversion := NumInversion
  layer := NumLayerIso
  rank := fun _ e => NumSyntax.rank e
  child_rank_lt := Num_layer_child_rank_lt

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
  | ⟨.var v, _child⟩ => Sum.inl ⟨v.val, by omega⟩
  | ⟨.zero, _child⟩ => Sum.inl ⟨k + 1, by omega⟩
  | ⟨.succ, child⟩ => Sum.inr (Sum.inl (child ()))
  | ⟨.plus, child⟩ => Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨.times, child⟩ => Sum.inr (Sum.inr (Sum.inr (child false, child true)))

def NumNatLayerShapeInv (k : Nat) :
    NumNatLayerShape k → CodeLayer NumPoly NumInversion (fun _ => Nat) k
  | Sum.inl tag =>
      if h : tag.val < k + 1 then
        ⟨.var ⟨tag.val, h⟩, fun q => nomatch q⟩
      else
        ⟨.zero, fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨.succ, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨.plus, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr p)) => ⟨.times, fun
      | false => p.1
      | true => p.2⟩

theorem NumNatLayerShape_left_inv (k : Nat) :
    Function.LeftInverse (NumNatLayerShapeInv k) (NumNatLayerShapeTo k) := by
  intro x
  cases x with
  | mk code child =>
      cases code with
      | var v =>
          cases v with
          | mk val isLt =>
              dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
              rw [dif_pos isLt]
              have hchild : (fun q => nomatch q) = child := by
                funext q
                cases q
              cases hchild
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              funext q
              cases q
      | zero =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hnot : ¬k + 1 < k + 1 := by omega
          rw [dif_neg hnot]
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | succ =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : (fun _ => child ()) = child := by
            funext q
            cases q
            rfl
          cases hchild
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
          rfl
      | plus =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]
      | times =>
          dsimp [NumNatLayerShapeTo, NumNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]

theorem NumNatLayerShape_right_inv (k : Nat) :
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

def NumNatLayerShapeIso (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k ≃ᵢ NumNatLayerShape k where
  toFun := NumNatLayerShapeTo k
  invFun := NumNatLayerShapeInv k
  left_inv := NumNatLayerShape_left_inv k
  right_inv := NumNatLayerShape_right_inv k

def NumNatTailIso : (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat))) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) (Iso.sum CodeAlgebra.prodNat CodeAlgebra.prodNat))
    CodeAlgebra.sum3Nat

def NumNatLayerIso (k : Nat) :
    CodeLayer NumPoly NumInversion (fun _ => Nat) k ≃ᵢ Nat :=
  Iso.trans (NumNatLayerShapeIso k)
    (Iso.trans (Iso.sum (Iso.refl (Fin (k + 2))) NumNatTailIso)
      (CodeAlgebra.finPlusNat (k + 2)))

theorem NumNat_child_lt :
    ∀ {k : Nat} (n : Nat)
      (q : NumPoly.Pos
          (NumInversion.decode k ((NumNatLayerIso k).invFun n).1).ctor
          (NumInversion.decode k ((NumNatLayerIso k).invFun n).1).param),
      (((NumNatLayerIso k).invFun n).2 q) < n := by
  intro k n
  generalize hz : (NumNatLayerIso k).invFun n = z
  have hn : (NumNatLayerIso k).toFun z = n := by
    rw [← hz]
    exact (NumNatLayerIso k).right_inv n
  change ∀ q : NumPoly.Pos (NumInversion.decode k z.1).ctor
      (NumInversion.decode k z.1).param,
    z.2 q < n
  cases z with
  | mk code child =>
      cases code with
      | var v =>
          intro q
          cases q
      | zero =>
          intro q
          cases q
      | succ =>
          intro q
          cases q
          let c := child ()
          have hn' : k + 2 + 2 * c = n := by
            simpa [c, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, CodeAlgebra.sum3Nat, Iso.trans, Iso.sum,
              CodeAlgebra.finPlusNat, CodeAlgebra.sumNat] using hn
          change c < n
          rw [← hn']
          have heq : c + (k + 2 + c) = k + 2 + 2 * c := by
            rw [Nat.two_mul]
            ac_rfl
          have hlt : c < c + (k + 2 + c) :=
            Nat.lt_add_of_pos_right (by omega : 0 < k + 2 + c)
          rw [← heq]
          exact hlt
      | plus =>
          intro q
          let pcode := CodeAlgebra.prodNat.toFun (child false, child true)
          have hn' : k + 2 + (2 * (2 * pcode) + 1) = n := by
            simpa [pcode, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, CodeAlgebra.sum3Nat, Iso.trans, Iso.sum,
              CodeAlgebra.finPlusNat, CodeAlgebra.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_fst_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 3 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 3 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 3 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_snd_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 3 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 3 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 3 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
      | times =>
          intro q
          let pcode := CodeAlgebra.prodNat.toFun (child false, child true)
          have hn' : k + 2 + (2 * (2 * pcode + 1) + 1) = n := by
            simpa [pcode, NumNatLayerIso, NumNatLayerShapeIso, NumNatLayerShapeTo,
              NumNatTailIso, CodeAlgebra.sum3Nat, Iso.trans, Iso.sum,
              CodeAlgebra.finPlusNat, CodeAlgebra.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_fst_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 5 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode + 1) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 5 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 5 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_snd_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have heq : pcode + (k + 5 + 3 * pcode) =
                k + 2 + (2 * (2 * pcode + 1) + 1) := by
              omega
            have hpair_lt : pcode < pcode + (k + 5 + 3 * pcode) :=
              Nat.lt_add_of_pos_right (by omega : 0 < k + 5 + 3 * pcode)
            rw [← heq]
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt

def NumNatGeneratedCode : GeneratedNatCode NumPoly where
  inversion := NumInversion
  layer := NumNatLayerIso
  child_lt := NumNat_child_lt

def NumNatIso (k : Nat) : Mu NumPoly k ≃ᵢ Nat :=
  NumNatGeneratedCode.iso k

def NumSyntaxNatIso (k : Nat) : NumSyntax k ≃ᵢ Nat :=
  Iso.trans (Iso.symm (NumSyntaxIso k)) (NumNatIso k)

end Examples
end BijForm
