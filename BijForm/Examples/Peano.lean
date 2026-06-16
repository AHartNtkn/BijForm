import BijForm.Examples.Num
import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly

/-- Reference syntax family for Peano formulas indexed by context size.
Equality compares already-coded numeric terms in the same context. -/
inductive PeanoSyntax : Nat → Type
  | eq {k : Nat} (lhs rhs : Mu NumPoly k) : PeanoSyntax k
  | not {k : Nat} : PeanoSyntax k → PeanoSyntax k
  | implies {k : Nat} : PeanoSyntax k → PeanoSyntax k → PeanoSyntax k
  | forallE {k : Nat} : PeanoSyntax (k + 1) → PeanoSyntax k

namespace PeanoSyntax

def rank : ∀ {k : Nat}, PeanoSyntax k → Nat
  | _, eq _ _ => 0
  | _, not e => rank e + 1
  | _, implies lhs rhs => Nat.max (rank lhs) (rank rhs) + 1
  | _, forallE e => rank e + 1

end PeanoSyntax

/-- Polynomial constructors for Peano formulas indexed by context size. -/
inductive PeanoCtor where
  | eq
  | not
  | implies
  | forallE
deriving DecidableEq, Repr

def PeanoParam : PeanoCtor → Type
  | .eq => Σ k : Nat, Mu NumPoly k × Mu NumPoly k
  | .not => Nat
  | .implies => Nat
  | .forallE => Nat

def PeanoOut : (c : PeanoCtor) → PeanoParam c → Nat
  | .eq, p => p.1
  | .not, k => k
  | .implies, k => k
  | .forallE, k => k

def PeanoPos : (c : PeanoCtor) → PeanoParam c → Type
  | .eq, _ => Empty
  | .not, _ => Unit
  | .implies, _ => Bool
  | .forallE, _ => Unit

def PeanoInput : {c : PeanoCtor} → (p : PeanoParam c) → PeanoPos c p → Nat
  | PeanoCtor.eq, _, q => nomatch q
  | PeanoCtor.not, (k : Nat), _ => k
  | PeanoCtor.implies, (k : Nat), _ => k
  | PeanoCtor.forallE, (k : Nat), _ => k + 1

/-- Dependent polynomial for Peano formulas. -/
def PeanoPoly : DepPoly Nat where
  Ctor := PeanoCtor
  Param := PeanoParam
  out := PeanoOut
  Pos := PeanoPos
  input := PeanoInput

inductive PeanoCode (k : Nat) where
  | eq (lhs rhs : Mu NumPoly k)
  | not
  | implies
  | forallE

def PeanoDecode (k : Nat) : PeanoCode k → Fiber PeanoPoly k
  | .eq lhs rhs => ⟨.eq, ⟨k, (lhs, rhs)⟩, rfl⟩
  | .not => ⟨.not, k, rfl⟩
  | .implies => ⟨.implies, k, rfl⟩
  | .forallE => ⟨.forallE, k, rfl⟩

def PeanoEncode (k : Nat) : Fiber PeanoPoly k → PeanoCode k
  | ⟨.eq, p, h⟩ =>
      have _ : PeanoPoly.out PeanoCtor.eq p = k := h
      .eq (k := k) (h ▸ p.2.1) (h ▸ p.2.2)
  | ⟨.not, _, _⟩ => .not
  | ⟨.implies, _, _⟩ => .implies
  | ⟨.forallE, _, _⟩ => .forallE

theorem Peano_decode_encode (k : Nat) (f : Fiber PeanoPoly k) :
    PeanoDecode k (PeanoEncode k f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | eq =>
        cases param with
        | mk k' pair =>
          cases pair with
          | mk lhs rhs =>
            cases out_eq
            rfl
    | not =>
        cases out_eq
        rfl
    | implies =>
        cases out_eq
        rfl
    | forallE =>
        cases out_eq
        rfl

theorem Peano_encode_decode (k : Nat) (c : PeanoCode k) :
    PeanoEncode k (PeanoDecode k c) = c := by
  cases c <;> rfl

/-- Output-index inversion for Peano formulas.  The `forallE` constructor keeps
the output context at `k` while its recursive child lives at `k+1`. -/
def PeanoInversion : OutputIndexInversion PeanoPoly where
  Code := PeanoCode
  decode := PeanoDecode
  encode := PeanoEncode
  decode_encode := Peano_decode_encode
  encode_decode := Peano_encode_decode

def PeanoLayerToSyntax (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion PeanoSyntax k → PeanoSyntax k
  | ⟨.eq lhs rhs, _child⟩ =>
      .eq lhs rhs
  | ⟨.not, child⟩ =>
      .not (child ())
  | ⟨.implies, child⟩ =>
      .implies (child false) (child true)
  | ⟨.forallE, child⟩ =>
      .forallE (child ())

def PeanoSyntaxToLayer (k : Nat) :
    PeanoSyntax k → CodeLayer PeanoPoly PeanoInversion PeanoSyntax k
  | .eq lhs rhs => ⟨.eq lhs rhs, fun q => nomatch q⟩
  | .not e => ⟨.not, fun _ => e⟩
  | .implies lhs rhs => ⟨.implies, fun (b : Bool) => if b then rhs else lhs⟩
  | .forallE e => ⟨.forallE, fun _ => e⟩

theorem PeanoLayer_left_inv (k : Nat) :
    Function.LeftInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | eq lhs rhs =>
        have hchild : (fun q => nomatch q) = child := by
          funext q
          cases q
        cases hchild
        rfl
    | not =>
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl
    | implies =>
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
        rw [hchild]
        rfl
    | forallE =>
        have hchild : (fun _ => child ()) = child := by
          funext q
          cases q
          rfl
        cases hchild
        rfl

theorem PeanoLayer_right_inv (k : Nat) :
    Function.RightInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro e
  cases e <;> simp [PeanoLayerToSyntax, PeanoSyntaxToLayer]

def PeanoLayerIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion PeanoSyntax k ≃ᵢ PeanoSyntax k where
  toFun := PeanoLayerToSyntax k
  invFun := PeanoSyntaxToLayer k
  left_inv := PeanoLayer_left_inv k
  right_inv := PeanoLayer_right_inv k

theorem Peano_layer_child_rank_lt :
    ∀ {k : Nat} (z : PeanoSyntax k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k ((PeanoLayerIso k).invFun z).1).ctor
          (PeanoInversion.decode k ((PeanoLayerIso k).invFun z).1).param),
      PeanoSyntax.rank (((PeanoLayerIso k).invFun z).2 q) < PeanoSyntax.rank z := by
  intro k z q
  cases z with
  | eq lhs rhs => cases q
  | not e =>
      cases q
      simp [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
        PeanoSyntax.rank]
  | implies lhs rhs =>
      cases q
      · simpa [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
      · simpa [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
  | forallE e =>
      cases q
      simp [PeanoLayerIso, PeanoSyntaxToLayer, PeanoInversion, PeanoDecode,
        PeanoSyntax.rank]

def PeanoGeneratedCode : GeneratedCode PeanoPoly PeanoSyntax where
  inversion := PeanoInversion
  layer := PeanoLayerIso
  rank := fun _ e => PeanoSyntax.rank e
  child_rank_lt := Peano_layer_child_rank_lt

def PeanoWellFoundedCode : WellFoundedCode PeanoPoly PeanoSyntax :=
  PeanoGeneratedCode.toWellFoundedCode

/-- Peano formulas as the generic initial algebra are bijective with readable
syntax through generated layer coding, including the `forall` branch whose
child is in context `k + 1`. -/
def PeanoSyntaxIso (k : Nat) : Mu PeanoPoly k ≃ᵢ PeanoSyntax k :=
  PeanoGeneratedCode.iso k

abbrev PeanoNatLayerShape :=
  (Nat × Nat) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ Nat))

def PeanoNatLayerShapeTo (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k → PeanoNatLayerShape
  | ⟨.eq lhs rhs, _child⟩ => Sum.inl ((NumNatIso k).toFun lhs, (NumNatIso k).toFun rhs)
  | ⟨.not, child⟩ => Sum.inr (Sum.inl (child ()))
  | ⟨.implies, child⟩ => Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨.forallE, child⟩ => Sum.inr (Sum.inr (Sum.inr (child ())))

def PeanoNatLayerShapeInv (k : Nat) :
    PeanoNatLayerShape → CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k
  | Sum.inl p =>
      ⟨.eq ((NumNatIso k).invFun p.1) ((NumNatIso k).invFun p.2),
        fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨.not, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨.implies, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr child)) => ⟨.forallE, fun _ => child⟩

theorem PeanoNatLayerShape_left_inv (k : Nat) :
    Function.LeftInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
  intro x
  cases x with
  | mk code child =>
      cases code with
      | eq lhs rhs =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          rw [(NumNatIso k).left_inv lhs, (NumNatIso k).left_inv rhs]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | not =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
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
      | implies =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            funext q
            cases q <;> rfl
          rw [hchild]
      | forallE =>
          dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
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

theorem PeanoNatLayerShape_right_inv (k : Nat) :
    Function.RightInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
  intro x
  cases x with
  | inl p =>
      cases p
      simp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
  | inr tail =>
      cases tail with
      | inl child => rfl
      | inr rest =>
          cases rest with
          | inl p =>
              cases p
              rfl
          | inr child => rfl

def PeanoNatLayerShapeIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k ≃ᵢ PeanoNatLayerShape where
  toFun := PeanoNatLayerShapeTo k
  invFun := PeanoNatLayerShapeInv k
  left_inv := PeanoNatLayerShape_left_inv k
  right_inv := PeanoNatLayerShape_right_inv k

def PeanoNatLayerIso (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k ≃ᵢ Nat :=
  Iso.trans (PeanoNatLayerShapeIso k)
    (Iso.trans (Iso.sum CodeAlgebra.prodNat
      (Iso.sum (Iso.refl Nat) (Iso.sum CodeAlgebra.prodNat (Iso.refl Nat))))
      CodeAlgebra.sum4Nat)

theorem PeanoNat_child_lt :
    ∀ {k : Nat} (n : Nat)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k ((PeanoNatLayerIso k).invFun n).1).ctor
          (PeanoInversion.decode k ((PeanoNatLayerIso k).invFun n).1).param),
      (((PeanoNatLayerIso k).invFun n).2 q) < n := by
  intro k n
  generalize hz : (PeanoNatLayerIso k).invFun n = z
  have hn : (PeanoNatLayerIso k).toFun z = n := by
    rw [← hz]
    exact (PeanoNatLayerIso k).right_inv n
  change ∀ q : PeanoPoly.Pos (PeanoInversion.decode k z.1).ctor
      (PeanoInversion.decode k z.1).param,
    z.2 q < n
  cases z with
  | mk code child =>
      cases code with
      | eq lhs rhs =>
          intro q
          cases q
      | not =>
          intro q
          cases q
          let c := child ()
          have hn' : 2 * (2 * c) + 1 = n := by
            simpa [c, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              CodeAlgebra.sum4Nat, Iso.trans, Iso.sum, CodeAlgebra.sum3Nat,
              CodeAlgebra.sumNat] using hn
          change c < n
          rw [← hn']
          exact Nat.lt_succ_of_le (by
            rw [Nat.two_mul, Nat.two_mul]
            simp [Nat.add_assoc])
      | implies =>
          intro q
          let pcode := CodeAlgebra.prodNat.toFun (child false, child true)
          have hn' : 2 * (2 * (2 * pcode) + 1) + 1 = n := by
            simpa [pcode, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              CodeAlgebra.sum4Nat, Iso.trans, Iso.sum, CodeAlgebra.sum3Nat,
              CodeAlgebra.sumNat] using hn
          cases q
          · change child false < n
            rw [← hn']
            have hchild_le : child false ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_fst_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have hpair_lt : pcode < 2 * (2 * (2 * pcode) + 1) + 1 :=
              Nat.lt_succ_of_le (by
                rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
                simp [Nat.add_assoc])
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
          · change child true < n
            rw [← hn']
            have hchild_le : child true ≤ pcode := by
              simpa [pcode, CodeAlgebra.prodNat] using
                CodeAlgebra.prodNat_snd_le (CodeAlgebra.prodNat.toFun (child false, child true))
            have hpair_lt : pcode < 2 * (2 * (2 * pcode) + 1) + 1 :=
              Nat.lt_succ_of_le (by
                rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
                simp [Nat.add_assoc])
            exact Nat.lt_of_le_of_lt hchild_le hpair_lt
      | forallE =>
          intro q
          cases q
          let c := child ()
          have hn' : 2 * (2 * (2 * c + 1) + 1) + 1 = n := by
            simpa [c, PeanoNatLayerIso, PeanoNatLayerShapeIso, PeanoNatLayerShapeTo,
              CodeAlgebra.sum4Nat, Iso.trans, Iso.sum, CodeAlgebra.sum3Nat,
              CodeAlgebra.sumNat] using hn
          change c < n
          rw [← hn']
          exact Nat.lt_succ_of_le (by
            rw [Nat.two_mul, Nat.two_mul, Nat.two_mul]
            simp [Nat.add_assoc])

def PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly where
  inversion := PeanoInversion
  layer := PeanoNatLayerIso
  child_lt := PeanoNat_child_lt

def PeanoNatIso (k : Nat) : Mu PeanoPoly k ≃ᵢ Nat :=
  PeanoNatGeneratedCode.iso k

def PeanoSyntaxNatIso (k : Nat) : PeanoSyntax k ≃ᵢ Nat :=
  Iso.trans (Iso.symm (PeanoSyntaxIso k)) (PeanoNatIso k)

end Examples
end BijForm
