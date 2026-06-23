import BijForm.Examples.Num
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

@[simp]
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

def PeanoSyntaxPresentation : LayerPresentation PeanoPoly PeanoInversion PeanoSyntax :=
  LayerPresentation.ofLayerChildRank
    (CodeLayerPresentation.ofMapsExt
      PeanoLayerToSyntax
      PeanoSyntaxToLayer
      (by
        intro k layer
        rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
        cases ctor with
        | eq =>
            cases param with
            | mk k' pair =>
                cases pair with
                | mk lhs rhs =>
                    dsimp [PeanoPoly, PeanoOut] at out_eq
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
            rfl)
      (by
        intro k layer
        rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
        cases ctor with
        | eq =>
            cases param with
            | mk k' pair =>
                cases pair with
                | mk lhs rhs =>
                    dsimp [PeanoPoly, PeanoOut] at out_eq
                    cases out_eq
                    exact heq_of_eq (by funext q; cases q)
        | not =>
            cases out_eq
            exact heq_of_eq (by funext q; cases q; rfl)
        | implies =>
            cases out_eq
            exact heq_of_eq (by funext q <;> cases q <;> rfl)
        | forallE =>
            cases out_eq
            exact heq_of_eq (by funext q; cases q; rfl))
      (by
        intro k e
        cases e <;> simp [PeanoLayerToSyntax, PeanoSyntaxToLayer]))
    (fun _ e => PeanoSyntax.rank e)
    (by
      intro k layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | eq =>
          cases param with
          | mk k' pair =>
              cases pair with
              | mk lhs rhs =>
                  dsimp [PeanoPoly, PeanoOut] at out_eq
                  cases out_eq
                  cases q
      | not =>
          cases out_eq
          cases q
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMapsExt,
            PeanoLayerToSyntax]
      | implies =>
          cases out_eq
          cases q <;>
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMapsExt,
              PeanoLayerToSyntax]
      | forallE =>
          cases out_eq
          cases q
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMapsExt,
            PeanoLayerToSyntax])

def PeanoGeneratedCode : GeneratedCode PeanoPoly PeanoSyntax :=
  PeanoSyntaxPresentation.generatedCode

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

def PeanoNatLayerShapeLayerPresentation :
    CodeLayerPresentation PeanoPoly PeanoInversion (fun _ => Nat)
      (fun _ => PeanoNatLayerShape) :=
  CodeLayerPresentation.ofMapsExt
    PeanoNatLayerShapeTo
    PeanoNatLayerShapeInv
    (by
      intro k layer
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | eq =>
          cases param with
          | mk k' pair =>
              cases pair with
              | mk lhs rhs =>
                  simp [PeanoPoly, PeanoOut] at out_eq
                  cases out_eq
                  dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
                  rw [(NumNatIso k).left_inv lhs, (NumNatIso k).left_inv rhs]
      | not =>
          cases out_eq
          rfl
      | implies =>
          cases out_eq
          rfl
      | forallE =>
          cases out_eq
          rfl)
    (by
      intro k layer
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | eq =>
          cases param with
          | mk k' pair =>
              cases pair with
              | mk lhs rhs =>
                  simp [PeanoPoly, PeanoOut] at out_eq
                  cases out_eq
                  dsimp [PeanoNatLayerShapeTo, PeanoNatLayerShapeInv]
                  rw [(NumNatIso k).left_inv lhs, (NumNatIso k).left_inv rhs]
                  exact heq_of_eq (by funext q; cases q)
      | not =>
          cases out_eq
          exact heq_of_eq (by funext q; cases q; rfl)
      | implies =>
          cases out_eq
          exact heq_of_eq (by funext q <;> cases q <;> rfl)
      | forallE =>
          cases out_eq
          exact heq_of_eq (by funext q; cases q; rfl))
    (by
    intro k x
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
          rcases tail with child | (⟨_lhs, _rhs⟩ | child) <;> rfl
    exact hshape x)

def PeanoNatLayerPresentation :
    LayerPresentation PeanoPoly PeanoInversion (fun _ => Nat) :=
  LayerPresentation.ofLayerChildRank
    (PeanoNatLayerShapeLayerPresentation.transCarrier
      (fun _ => CodeAlgebra.prodOrNatOrProdOrNat))
    (fun _ n => n)
    (by
      intro k layer q
      rcases layer with ⟨⟨ctor, param, out_eq⟩, child⟩
      cases ctor with
      | eq =>
          cases param with
          | mk k' pair =>
              cases pair with
              | mk lhs rhs =>
                  dsimp [PeanoPoly, PeanoOut] at out_eq
                  cases out_eq
                  cases q
      | not =>
          cases out_eq
          cases q
          have hsub :
              CodeAlgebra.SubcodeLt
                CodeAlgebra.prodOrNatOrProdOrNat
                (fun n : Nat => Sum.inr (Sum.inl n))
                id :=
            CodeAlgebra.SubcodeLe.toNatSum_inr_lt
              (h := CodeAlgebra.SubcodeLe.toNatSum_inl
                (h := CodeAlgebra.subcode_nat_id))
          have h := hsub (child ())
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
            PeanoNatLayerShapeLayerPresentation, PeanoNatLayerShapeTo,
            PeanoPoly, PeanoOut, PeanoInput, PeanoInversion,
            OutputIndexInversion.canonical] at h ⊢
          have hsame : child PUnit.unit = child () := rfl
          rw [hsame]
          exact h
      | implies =>
          cases out_eq
          cases q
          · have hsub :
                CodeAlgebra.SubcodeLt
                  CodeAlgebra.prodOrNatOrProdOrNat
                  (fun p : Nat × Nat => Sum.inr (Sum.inr (Sum.inl p)))
                  (fun p : Nat × Nat => p.1) :=
              CodeAlgebra.SubcodeLt.toNatSum_inr
                (h := CodeAlgebra.SubcodeLe.toNatSum_inr_lt
                  (h := CodeAlgebra.SubcodeLe.toNatSum_inl
                    (h := CodeAlgebra.subcode_prodNat_fst)))
            have h := hsub (child false, child true)
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
              PeanoNatLayerShapeLayerPresentation, PeanoNatLayerShapeTo,
              PeanoPoly, PeanoOut, PeanoInput, PeanoInversion,
              OutputIndexInversion.canonical] at h ⊢
            exact h
          · have hsub :
                CodeAlgebra.SubcodeLt
                  CodeAlgebra.prodOrNatOrProdOrNat
                  (fun p : Nat × Nat => Sum.inr (Sum.inr (Sum.inl p)))
                  (fun p : Nat × Nat => p.2) :=
              CodeAlgebra.SubcodeLt.toNatSum_inr
                (h := CodeAlgebra.SubcodeLe.toNatSum_inr_lt
                  (h := CodeAlgebra.SubcodeLe.toNatSum_inl
                    (h := CodeAlgebra.subcode_prodNat_snd)))
            have h := hsub (child false, child true)
            simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
              PeanoNatLayerShapeLayerPresentation, PeanoNatLayerShapeTo,
              PeanoPoly, PeanoOut, PeanoInput, PeanoInversion,
              OutputIndexInversion.canonical] at h ⊢
            exact h
      | forallE =>
          cases out_eq
          cases q
          have hsub :
              CodeAlgebra.SubcodeLt
                CodeAlgebra.prodOrNatOrProdOrNat
                (fun n : Nat => Sum.inr (Sum.inr (Sum.inr n)))
                id :=
            CodeAlgebra.SubcodeLt.toNatSum_inr
              (h := CodeAlgebra.SubcodeLt.toNatSum_inr
                (h := CodeAlgebra.SubcodeLe.toNatSum_inr_lt
                  (h := CodeAlgebra.subcode_nat_id)))
          have h := hsub (child ())
          simp [CodeLayerPresentation.iso, CodeLayerPresentation.transCarrier,
            PeanoNatLayerShapeLayerPresentation, PeanoNatLayerShapeTo,
            PeanoPoly, PeanoOut, PeanoInput, PeanoInversion,
            OutputIndexInversion.canonical] at h ⊢
          have hsame : child PUnit.unit = child () := rfl
          rw [hsame]
          exact h)

def PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly :=
  LayerPresentation.generatedCode PeanoNatLayerPresentation

def PeanoNatIso (k : Nat) : Mu PeanoPoly k ≃ᵢ Nat :=
  PeanoNatGeneratedCode.iso k

def PeanoSyntaxNatIso (k : Nat) : PeanoSyntax k ≃ᵢ Nat :=
  GeneratedCode.codeIso PeanoGeneratedCode PeanoNatGeneratedCode k

end Examples
end BijForm
