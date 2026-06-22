import BijForm.Examples.Num
import BijForm.InitialAlgebra
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

theorem Peano_layer_child_rank_lt :
    ∀ {k : Nat} (z : PeanoSyntax k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k (PeanoSyntaxToLayer k z).1).ctor
          (PeanoInversion.decode k (PeanoSyntaxToLayer k z).1).param),
      PeanoSyntax.rank ((PeanoSyntaxToLayer k z).2 q) <
        PeanoSyntax.rank z := by
  intro k z q
  cases z with
  | eq lhs rhs => cases q
  | not e =>
      cases q
      simp [PeanoSyntaxToLayer, PeanoInversion,
        OutputIndexInversion.canonical,
        PeanoSyntax.rank]
  | implies lhs rhs =>
      cases q
      · simpa [PeanoSyntaxToLayer, PeanoInversion,
          OutputIndexInversion.canonical,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
      · simpa [PeanoSyntaxToLayer, PeanoInversion,
          OutputIndexInversion.canonical,
          PeanoSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (PeanoSyntax.rank lhs) (PeanoSyntax.rank rhs))
  | forallE e =>
      cases q
      simp [PeanoSyntaxToLayer, PeanoInversion,
        OutputIndexInversion.canonical,
        PeanoSyntax.rank]

def PeanoSyntaxPresentation : SyntaxPresentation PeanoPoly PeanoInversion PeanoSyntax :=
  SyntaxPresentation.ofLayerIso
    (fun k =>
      { toFun := PeanoLayerToSyntax k
        invFun := PeanoSyntaxToLayer k
        left_inv :=
          CodeLayer.canonical_left_inv_by_fiber
            (toCarrier := PeanoLayerToSyntax)
            (fromCarrier := PeanoSyntaxToLayer) (by
              intro k ctor param out_eq child
              cases ctor with
              | eq =>
                cases param with
                | mk k' pair =>
                  cases pair with
                  | mk lhs rhs =>
                    finish_code_layer_left_inv out_eq child
              | not =>
                finish_code_layer_left_inv out_eq child
              | implies =>
                finish_code_layer_left_inv out_eq child
              | forallE =>
                finish_code_layer_left_inv out_eq child) k
        right_inv := by
          intro e
          cases e <;> simp [PeanoLayerToSyntax, PeanoSyntaxToLayer] })
    (fun _ e => PeanoSyntax.rank e)
    Peano_layer_child_rank_lt

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
  CodeLayerPresentation.ofMaps
    PeanoNatLayerShapeTo
    PeanoNatLayerShapeInv
    (CodeLayer.canonical_left_inv_by_fiber (by
      intro k ctor param out_eq child
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
            have hchild : (fun q => nomatch q) = child := by
              child_eta_cases
            cases hchild
            refine CodeLayer.ext_layer
              (P := PeanoPoly) (H := PeanoInversion) (Code := fun _ => Nat)
              (i := k) ?_ ?_
            · apply congrArg
                (fun h =>
                  (⟨PeanoCtor.eq, ⟨k, (lhs, rhs)⟩, h⟩ : Fiber PeanoPoly k))
              apply Subsingleton.elim
            · apply heq_of_eq
              child_eta_cases
      | not =>
          finish_code_layer_left_inv out_eq child
      | implies =>
          finish_code_layer_left_inv out_eq child
      | forallE =>
          finish_code_layer_left_inv out_eq child))
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
          cases tail with
          | inl child => rfl
          | inr rest =>
              cases rest with
              | inl p =>
                  cases p
                  rfl
              | inr child => rfl
    exact hshape x)

theorem PeanoNat_layer_child_lt :
    ∀ {k : Nat} (layer : CodeLayer PeanoPoly PeanoInversion (fun _ => Nat) k)
      (q : PeanoPoly.Pos
          (PeanoInversion.decode k layer.1).ctor
          (PeanoInversion.decode k layer.1).param),
      layer.2 q <
        CodeAlgebra.prodOrNatOrProdOrNat.toFun (PeanoNatLayerShapeTo k layer) := by
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
          have hpath :
              CodeAlgebra.SubcodeLt CodeAlgebra.prodOrNatOrProdOrNat
                (fun c : Nat => Sum.inr (Sum.inl c)) id := by
            exact CodeAlgebra.SubcodeLe.toNatSum4_inr_inl_lt
              (first := CodeAlgebra.prodNat) (third := CodeAlgebra.prodNat)
              (fourth := Iso.refl Nat) CodeAlgebra.subcode_nat_id
          simpa [c, PeanoNatLayerShapeTo] using
            hpath c
      | implies =>
          change PeanoParam PeanoCtor.implies at param
          change Nat at param
          cases out_eq
          intro q
          cases q
          · have hpath :
                CodeAlgebra.SubcodeLt CodeAlgebra.prodOrNatOrProdOrNat
                  (fun p : Nat × Nat => Sum.inr (Sum.inr (Sum.inl p)))
                  Prod.fst := by
              exact CodeAlgebra.SubcodeLe.toNatSum4_inr_inr_inl_lt
                (first := CodeAlgebra.prodNat) (second := Iso.refl Nat)
                (fourth := Iso.refl Nat) CodeAlgebra.subcode_prodNat_fst
            simpa [PeanoNatLayerShapeTo] using
              hpath (child false, child true)
          · have hpath :
                CodeAlgebra.SubcodeLt CodeAlgebra.prodOrNatOrProdOrNat
                  (fun p : Nat × Nat => Sum.inr (Sum.inr (Sum.inl p)))
                  Prod.snd := by
              exact CodeAlgebra.SubcodeLe.toNatSum4_inr_inr_inl_lt
                (first := CodeAlgebra.prodNat) (second := Iso.refl Nat)
                (fourth := Iso.refl Nat) CodeAlgebra.subcode_prodNat_snd
            simpa [PeanoNatLayerShapeTo] using
              hpath (child false, child true)
      | forallE =>
          change PeanoParam PeanoCtor.forallE at param
          change Nat at param
          cases out_eq
          intro q
          cases q
          let c := child ()
          have hpath :
              CodeAlgebra.SubcodeLt CodeAlgebra.prodOrNatOrProdOrNat
                (fun c : Nat => Sum.inr (Sum.inr (Sum.inr c))) id := by
            exact CodeAlgebra.SubcodeLe.toNatSum4_inr_inr_inr_lt
              (first := CodeAlgebra.prodNat) (second := Iso.refl Nat)
              (third := CodeAlgebra.prodNat) CodeAlgebra.subcode_nat_id
          simpa [c, PeanoNatLayerShapeTo] using
            hpath c

def PeanoNatLayerPresentation : NatLayerPresentation PeanoPoly PeanoInversion :=
  LayerPresentation.ofLayerShapeChildRank
    PeanoNatLayerShapeLayerPresentation
    (fun _ => CodeAlgebra.prodOrNatOrProdOrNat)
    (fun _ n => n)
    (by
    intro k layer q
    exact PeanoNat_layer_child_lt layer q)

def PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly :=
  LayerPresentation.generatedCode PeanoNatLayerPresentation

def PeanoNatIso (k : Nat) : Mu PeanoPoly k ≃ᵢ Nat :=
  PeanoNatGeneratedCode.iso k

def PeanoSyntaxNatIso (k : Nat) : PeanoSyntax k ≃ᵢ Nat :=
  GeneratedCode.codeIso PeanoGeneratedCode PeanoNatGeneratedCode k

end Examples
end BijForm
