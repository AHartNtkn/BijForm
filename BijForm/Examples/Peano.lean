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

/-- Output-index inversion for Peano formulas.  The `forallE` constructor keeps
the output context at `k` while its recursive child lives at `k+1`. -/
def PeanoInversion : OutputIndexInversion PeanoPoly :=
  OutputIndexInversion.canonical PeanoPoly

def PeanoLayerToSyntax (k : Nat) :
    CodeLayer PeanoPoly PeanoInversion PeanoSyntax k → PeanoSyntax k
  | ⟨⟨.eq, p, h⟩, _child⟩ => by
      cases p with
      | mk k' pair =>
        cases pair with
        | mk lhs rhs =>
          dsimp [PeanoPoly, PeanoOut] at h
          cases h
          exact .eq lhs rhs
  | ⟨⟨.not, _k, h⟩, child⟩ => by
      cases h
      exact .not (child ())
  | ⟨⟨.implies, _k, h⟩, child⟩ => by
      cases h
      exact .implies (child false) (child true)
  | ⟨⟨.forallE, _k, h⟩, child⟩ => by
      cases h
      exact .forallE (child ())

def PeanoSyntaxToLayer (k : Nat) :
    PeanoSyntax k → CodeLayer PeanoPoly PeanoInversion PeanoSyntax k
  | .eq lhs rhs => ⟨⟨PeanoCtor.eq, ⟨k, (lhs, rhs)⟩, rfl⟩, fun q => nomatch q⟩
  | .not e => ⟨⟨PeanoCtor.not, (k : Nat), rfl⟩, fun _ => e⟩
  | .implies lhs rhs => ⟨⟨PeanoCtor.implies, (k : Nat), rfl⟩, fun
      | false => lhs
      | true => rhs⟩
  | .forallE e => ⟨⟨PeanoCtor.forallE, (k : Nat), rfl⟩, fun _ => e⟩

theorem PeanoLayer_left_inv (k : Nat) :
    Function.LeftInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | eq =>
        cases param with
        | mk k' pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp [PeanoPoly, PeanoOut] at out_eq
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              child_eta_empty
            cases hchild
            rfl
      | not =>
        change PeanoParam PeanoCtor.not at param
        change Nat at param
        cases out_eq
        have hchild : (fun _ => child ()) = child := by
          child_eta_unit
        cases hchild
        rfl
      | implies =>
        change PeanoParam PeanoCtor.implies at param
        change Nat at param
        cases out_eq
        have hchild : child = (fun
            | false => child false
            | true => child true) := by
          child_eta_bool
        rw [hchild]
        rfl
      | forallE =>
        change PeanoParam PeanoCtor.forallE at param
        change Nat at param
        cases out_eq
        have hchild : (fun _ => child ()) = child := by
          child_eta_unit
        cases hchild
        rfl

theorem PeanoLayer_right_inv (k : Nat) :
    Function.RightInverse (PeanoSyntaxToLayer k) (PeanoLayerToSyntax k) := by
  intro e
  cases e <;> simp [PeanoLayerToSyntax, PeanoSyntaxToLayer]

def PeanoSyntaxLayerPresentation :
    CodeLayerPresentation PeanoPoly PeanoInversion PeanoSyntax PeanoSyntax where
  toCarrier := PeanoLayerToSyntax
  fromCarrier := PeanoSyntaxToLayer
  left_inv := PeanoLayer_left_inv
  right_inv := PeanoLayer_right_inv

theorem Peano_layer_child_rank_lt :
    ∀ {k : Nat} (z : PeanoSyntax k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k
            ((PeanoSyntaxLayerPresentation.iso k).invFun z).1).ctor
          (PeanoInversion.decode k
            ((PeanoSyntaxLayerPresentation.iso k).invFun z).1).param),
      PeanoSyntax.rank (((PeanoSyntaxLayerPresentation.iso k).invFun z).2 q) <
        PeanoSyntax.rank z := by
  intro k z q
  cases z with
  | eq lhs rhs => cases q
  | not e =>
      cases q
      simp [CodeLayerPresentation.iso, PeanoSyntaxLayerPresentation, PeanoSyntaxToLayer,
        PeanoInversion,
        OutputIndexInversion.canonical,
        PeanoSyntax.rank]
  | implies lhs rhs =>
      cases q
      · simpa [CodeLayerPresentation.iso, PeanoSyntaxLayerPresentation,
          PeanoSyntaxToLayer, PeanoInversion,
          OutputIndexInversion.canonical,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
      · simpa [CodeLayerPresentation.iso, PeanoSyntaxLayerPresentation,
          PeanoSyntaxToLayer, PeanoInversion,
          OutputIndexInversion.canonical,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
  | forallE e =>
      cases q
      simp [CodeLayerPresentation.iso, PeanoSyntaxLayerPresentation, PeanoSyntaxToLayer,
        PeanoInversion,
        OutputIndexInversion.canonical,
        PeanoSyntax.rank]

def PeanoSyntaxPresentation : SyntaxPresentation PeanoPoly PeanoInversion PeanoSyntax where
  layer := PeanoSyntaxLayerPresentation
  rank := fun _ e => PeanoSyntax.rank e
  child_rank_lt := Peano_layer_child_rank_lt

def PeanoGeneratedCode : GeneratedCode PeanoPoly PeanoSyntax :=
  PeanoSyntaxPresentation.generatedCode

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
  | ⟨⟨.eq, p, h⟩, _child⟩ => by
      cases p with
      | mk k' pair =>
        cases pair with
        | mk lhs rhs =>
          dsimp [PeanoPoly, PeanoOut] at h
          cases h
          exact Sum.inl ((NumNatIso k).toFun lhs, (NumNatIso k).toFun rhs)
  | ⟨⟨.not, _k, h⟩, child⟩ => by
      cases h
      exact Sum.inr (Sum.inl (child ()))
  | ⟨⟨.implies, _k, h⟩, child⟩ => by
      cases h
      exact Sum.inr (Sum.inr (Sum.inl (child false, child true)))
  | ⟨⟨.forallE, _k, h⟩, child⟩ => by
      cases h
      exact Sum.inr (Sum.inr (Sum.inr (child ())))

def PeanoNatLayerShapeInv (k : Nat) :
    PeanoNatLayerShape → CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k
  | Sum.inl p =>
      ⟨⟨PeanoCtor.eq, ⟨k, ((NumNatIso k).invFun p.1, (NumNatIso k).invFun p.2)⟩, rfl⟩,
        fun q => nomatch q⟩
  | Sum.inr (Sum.inl child) => ⟨⟨PeanoCtor.not, (k : Nat), rfl⟩, fun _ => child⟩
  | Sum.inr (Sum.inr (Sum.inl p)) => ⟨⟨PeanoCtor.implies, (k : Nat), rfl⟩, fun
      | false => p.1
      | true => p.2⟩
  | Sum.inr (Sum.inr (Sum.inr child)) =>
      ⟨⟨PeanoCtor.forallE, (k : Nat), rfl⟩, fun _ => child⟩

def PeanoNatCodeLayerPresentation :
    CodeLayerPresentation PeanoPoly PeanoInversion (fun _ => Nat) (fun _ => Nat) where
  toCarrier k layer :=
    CodeAlgebra.prodOrNatOrProdOrNat.toFun (PeanoNatLayerShapeTo k layer)
  fromCarrier k n :=
    PeanoNatLayerShapeInv k (CodeAlgebra.prodOrNatOrProdOrNat.invFun n)
  left_inv := by
    intro k x
    have hshape :
        Function.LeftInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
      intro x
      cases x with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | eq =>
            cases param with
            | mk k' pair =>
              cases pair with
              | mk lhs rhs =>
                dsimp [PeanoPoly, PeanoOut] at out_eq
                cases out_eq
                dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
                rw [(NumNatIso k).left_inv lhs, (NumNatIso k).left_inv rhs]
                have hchild : (fun q => nomatch q) = child := by
                  child_eta_empty
                cases hchild
                refine Sigma.ext ?_ ?_
                · apply congrArg
                    (fun h =>
                      (⟨PeanoCtor.eq, ⟨k, (lhs, rhs)⟩, h⟩ : Fiber PeanoPoly k))
                  apply Subsingleton.elim
                · apply heq_of_eq
                  child_eta_empty
          | not =>
              change PeanoParam PeanoCtor.not at param
              change Nat at param
              cases out_eq
              dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
              have hchild : (fun _ => child ()) = child := by
                child_eta_unit
              cases hchild
              rfl
          | implies =>
              change PeanoParam PeanoCtor.implies at param
              change Nat at param
              cases out_eq
              dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
              have hchild : child = (fun
                  | false => child false
                  | true => child true) := by
                child_eta_bool
              rw [hchild]
              rfl
          | forallE =>
              change PeanoParam PeanoCtor.forallE at param
              change Nat at param
              cases out_eq
              dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
              have hchild : (fun _ => child ()) = child := by
                child_eta_unit
              cases hchild
              rfl
    change
      PeanoNatLayerShapeInv k
        (CodeAlgebra.prodOrNatOrProdOrNat.invFun
          (CodeAlgebra.prodOrNatOrProdOrNat.toFun
            (PeanoNatLayerShapeTo k x))) = x
    rw [CodeAlgebra.prodOrNatOrProdOrNat.left_inv (PeanoNatLayerShapeTo k x)]
    exact hshape x
  right_inv := by
    intro k n
    have hshape :
        Function.RightInverse (PeanoNatLayerShapeInv k) (PeanoNatLayerShapeTo k) := by
      intro x
      cases x with
      | inl p =>
          cases p with
          | mk lhs rhs =>
            dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
            rw [(NumNatIso k).right_inv lhs, (NumNatIso k).right_inv rhs]
      | inr tail =>
          cases tail with
          | inl child => rfl
          | inr rest =>
              cases rest with
              | inl p =>
                  cases p
                  rfl
              | inr child => rfl
    change
      CodeAlgebra.prodOrNatOrProdOrNat.toFun
        (PeanoNatLayerShapeTo k
          (PeanoNatLayerShapeInv k
            (CodeAlgebra.prodOrNatOrProdOrNat.invFun n))) = n
    rw [hshape (CodeAlgebra.prodOrNatOrProdOrNat.invFun n)]
    exact CodeAlgebra.prodOrNatOrProdOrNat.right_inv n

theorem PeanoNat_layer_child_lt :
    ∀ {k : Nat} (layer : CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k layer.1).ctor
          (PeanoInversion.decode k layer.1).param),
      layer.2 q < (PeanoNatCodeLayerPresentation.iso k).toFun layer := by
  intro k layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | eq =>
        cases param with
        | mk k' pair =>
          cases pair with
          | mk lhs rhs =>
            dsimp [PeanoPoly, PeanoOut] at out_eq
            cases out_eq
            intro q
            cases q
      | not =>
          change PeanoParam PeanoCtor.not at param
          change Nat at param
          cases out_eq
          intro q
          cases q
          let c := child ()
          simpa [c, CodeLayerPresentation.iso, PeanoNatCodeLayerPresentation,
            PeanoNatLayerShapeTo] using
            CodeAlgebra.prodOrNatOrProdOrNat_toFun_inr_inl_lt c
      | implies =>
          change PeanoParam PeanoCtor.implies at param
          change Nat at param
          cases out_eq
          intro q
          cases q
          · simpa [CodeLayerPresentation.iso, PeanoNatCodeLayerPresentation,
              PeanoNatLayerShapeTo] using
              CodeAlgebra.prodOrNatOrProdOrNat_toFun_inr_inr_inl_fst_lt
                (child false, child true)
          · simpa [CodeLayerPresentation.iso, PeanoNatCodeLayerPresentation,
              PeanoNatLayerShapeTo] using
              CodeAlgebra.prodOrNatOrProdOrNat_toFun_inr_inr_inl_snd_lt
                (child false, child true)
      | forallE =>
          change PeanoParam PeanoCtor.forallE at param
          change Nat at param
          cases out_eq
          intro q
          cases q
          let c := child ()
          simpa [c, CodeLayerPresentation.iso, PeanoNatCodeLayerPresentation,
            PeanoNatLayerShapeTo] using
            CodeAlgebra.prodOrNatOrProdOrNat_toFun_inr_inr_inr_lt c

def PeanoNatLayerPresentation : NatLayerPresentation PeanoPoly PeanoInversion where
  layer := PeanoNatCodeLayerPresentation
  child_lt := by
    intro k n q
    have h :=
      PeanoNat_layer_child_lt ((PeanoNatCodeLayerPresentation.iso k).invFun n) q
    rw [(PeanoNatCodeLayerPresentation.iso k).right_inv n] at h
    exact h

def PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly :=
  PeanoNatLayerPresentation.generatedCode

def PeanoNatIso (k : Nat) : Mu PeanoPoly k ≃ᵢ Nat :=
  PeanoNatGeneratedCode.iso k

def PeanoSyntaxNatIso (k : Nat) : PeanoSyntax k ≃ᵢ Nat :=
  GeneratedCode.natCodeIso PeanoGeneratedCode PeanoNatGeneratedCode k

end Examples
end BijForm
