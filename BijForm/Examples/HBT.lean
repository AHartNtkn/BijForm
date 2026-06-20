import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly


/-- Reference syntax family for height-bounded trees: leaves may appear at any
height, while branches increase the height bound by one. -/
inductive HBTSyntax : Nat → Type
  | leaf {i : Nat} (label : Nat) : HBTSyntax i
  | branch {m : Nat} : HBTSyntax m → HBTSyntax m → HBTSyntax (m + 1)

namespace HBTSyntax

def rank : ∀ {i : Nat}, HBTSyntax i → Nat
  | _, leaf _ => 0
  | _, branch lhs rhs => Nat.max (rank lhs) (rank rhs) + 1

end HBTSyntax

/-- Polynomial constructors for height-bounded trees: leaves carry a natural
label, branches have two children. -/
inductive HBTCtor where
  | leaf
  | branch
deriving DecidableEq, Repr

def HBTParam : HBTCtor → Type
  | .leaf => Nat × Nat
  | .branch => Nat

def HBTOut : (c : HBTCtor) → HBTParam c → Nat
  | HBTCtor.leaf, p => p.1
  | HBTCtor.branch, (n : Nat) => n + 1

def HBTPos : (c : HBTCtor) → HBTParam c → Type
  | HBTCtor.leaf, _ => Empty
  | HBTCtor.branch, _ => Bool

def HBTInput : {c : HBTCtor} → (p : HBTParam c) → HBTPos c p → Nat
  | HBTCtor.leaf, _, q => nomatch q
  | HBTCtor.branch, (n : Nat), _ => n

/-- Raw height-bounded-tree polynomial.  The branch constructor outputs `n+1`;
`HBTInversion` below is the same-fiber inversion of that output index. -/
def HBTPoly : DepPoly Nat where
  Ctor := HBTCtor
  Param := HBTParam
  out := HBTOut
  Pos := HBTPos
  input := HBTInput

/-- The non-opaque output-index inversion for the height-bounded-tree example. -/
def HBTInversion : OutputIndexInversion HBTPoly :=
  OutputIndexInversion.canonical HBTPoly

/-- The fiber of branch constructors at height zero is empty. -/
theorem no_zero_height_branch (f : Fiber HBTPoly 0) (hctor : f.ctor = .branch) :
    False := by
  cases f with
  | mk ctor param out_eq =>
    cases hctor
    cases out_eq

/-- The fiber of branch constructors at `m+1` contains the predecessor `m`. -/
def branchAtSucc (m : Nat) : Fiber HBTPoly (m + 1) :=
  ⟨HBTCtor.branch, (m : Nat), rfl⟩

def HBTLayerToSyntax (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i → HBTSyntax i
  | ⟨⟨.leaf, p, h⟩, _child⟩ => by
      cases p with
      | mk height label =>
        cases h
        exact .leaf label
  | ⟨⟨.branch, m, h⟩, child⟩ => by
      cases h
      exact .branch (child false) (child true)

def HBTSyntaxToLayer (i : Nat) :
    HBTSyntax i → CodeLayer HBTPoly HBTInversion HBTSyntax i
  | .leaf label =>
      ⟨⟨HBTCtor.leaf, ((i, label) : Nat × Nat), rfl⟩, fun q => nomatch q⟩
  | @HBTSyntax.branch m lhs rhs =>
      ⟨⟨HBTCtor.branch, (m : Nat), rfl⟩, fun
        | false => lhs
        | true => rhs⟩

theorem HBTLayer_left_inv (i : Nat) :
    Function.LeftInverse (HBTSyntaxToLayer i) (HBTLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | mk ctor param out_eq =>
      cases ctor with
      | leaf =>
          cases param with
          | mk height label =>
            cases out_eq
            have hchild : (fun q => nomatch q) = child := by
              child_eta_empty
            cases hchild
            rfl
      | branch =>
          cases out_eq
          have hchild : child = (fun
              | false => child false
              | true => child true) := by
            child_eta_bool
          rw [hchild]
          rfl

theorem HBTLayer_right_inv (i : Nat) :
    Function.RightInverse (HBTSyntaxToLayer i) (HBTLayerToSyntax i) := by
  intro t
  cases t <;> simp [HBTLayerToSyntax, HBTSyntaxToLayer]

def HBTLayerIso (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i ≃ᵢ HBTSyntax i where
  toFun := HBTLayerToSyntax i
  invFun := HBTSyntaxToLayer i
  left_inv := HBTLayer_left_inv i
  right_inv := HBTLayer_right_inv i

theorem HBT_layer_child_rank_lt :
    ∀ {i : Nat} (z : HBTSyntax i)
      (q : HBTPoly.Pos
          (HBTInversion.decode i ((HBTLayerIso i).invFun z).1).ctor
          (HBTInversion.decode i ((HBTLayerIso i).invFun z).1).param),
      HBTSyntax.rank (((HBTLayerIso i).invFun z).2 q) < HBTSyntax.rank z := by
  intro i z q
  cases z with
  | leaf label => cases q
  | branch lhs rhs =>
      cases q
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion,
          OutputIndexInversion.canonical, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion,
          OutputIndexInversion.canonical, HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))

/--
Generated coding data for height-bounded trees. The example supplies only
the local layer coding over `HBTInversion`; the full object-layer step is
produced by `GeneratedCode.toWellFoundedCode`.
-/
def HBTGeneratedCode : GeneratedCode HBTPoly HBTSyntax where
  inversion := HBTInversion
  layer := HBTLayerIso
  rank := fun _ t => HBTSyntax.rank t
  child_rank_lt := HBT_layer_child_rank_lt

def HBTWellFoundedCode : WellFoundedCode HBTPoly HBTSyntax :=
  HBTGeneratedCode.toWellFoundedCode

/-- Height-bounded trees as the generic initial algebra are bijective with
readable syntax through generated layer coding. -/
def HBTSyntaxIso (i : Nat) : Mu HBTPoly i ≃ᵢ HBTSyntax i :=
  HBTGeneratedCode.iso i

def HBTNatZeroLayerIso :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) 0 ≃ᵢ Nat where
  toFun
    | ⟨⟨.leaf, p, h⟩, _child⟩ => by
        cases p with
        | mk height label =>
          cases h
          exact label
    | ⟨⟨.branch, m, h⟩, _child⟩ => by cases h
  invFun n := ⟨⟨HBTCtor.leaf, ((0, n) : Nat × Nat), rfl⟩, fun q => nomatch q⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                cases out_eq
                have hchild : (fun q => nomatch q) = child := by
                  child_eta_empty
                cases hchild
                rfl
          | branch => cases out_eq
  right_inv := by
    intro n
    rfl

def HBTNatSuccLayerSumIso (m : Nat) :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) (m + 1) ≃ᵢ
      (Nat ⊕ (Nat × Nat)) where
  toFun
    | ⟨⟨.leaf, p, h⟩, _child⟩ => by
        cases p with
        | mk height label =>
          cases h
          exact Sum.inl label
    | ⟨⟨.branch, _k, _h⟩, child⟩ => Sum.inr (child false, child true)
  invFun
    | Sum.inl label =>
        ⟨⟨HBTCtor.leaf, ((m + 1, label) : Nat × Nat), rfl⟩, fun q => nomatch q⟩
    | Sum.inr p => ⟨⟨HBTCtor.branch, (m : Nat), rfl⟩, fun
        | false => p.1
        | true => p.2⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                cases out_eq
                have hchild : (fun q => nomatch q) = child := by
                  child_eta_empty
                cases hchild
                rfl
          | branch =>
              cases out_eq
              have hchild : child = (fun
                  | false => child false
                  | true => child true) := by
                child_eta_bool
              rw [hchild]
              rfl
  right_inv := by
    intro x
    cases x with
    | inl label => rfl
    | inr p =>
        cases p
        rfl

def HBTNatSuccLayerIso (m : Nat) :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) (m + 1) ≃ᵢ Nat :=
  Iso.trans (HBTNatSuccLayerSumIso m) CodeAlgebra.sumProdNat

def HBTNatLayerIso :
    ∀ i, CodeLayer HBTPoly HBTInversion (fun _ => Nat) i ≃ᵢ Nat
  | 0 => HBTNatZeroLayerIso
  | m + 1 => HBTNatSuccLayerIso m

theorem HBTNat_child_lt :
    ∀ {i : Nat} (n : Nat)
      (q : HBTPoly.Pos
          (HBTInversion.decode i ((HBTNatLayerIso i).invFun n).1).ctor
          (HBTInversion.decode i ((HBTNatLayerIso i).invFun n).1).param),
      (((HBTNatLayerIso i).invFun n).2 q) < n := by
  intro i n
  cases i with
  | zero =>
      intro q
      cases q
  | succ m =>
      dsimp [HBTNatLayerIso, HBTNatSuccLayerIso, Iso.trans]
      generalize hsum : CodeAlgebra.sumProdNat.invFun n = s
      cases s with
      | inl label =>
          intro q
          cases q
      | inr pair =>
          intro q
          cases q
          · change pair.1 < n
            exact CodeAlgebra.sumProdNat_invFun_inr_fst_lt hsum
          · change pair.2 < n
            exact CodeAlgebra.sumProdNat_invFun_inr_snd_lt hsum

/-- Generated Nat coding data for height-bounded trees. The recursive encoder
and decoder are produced by `GeneratedNatCode`, not by an example-specific
recursive function. -/
def HBTNatGeneratedCode : GeneratedNatCode HBTPoly where
  inversion := HBTInversion
  layer := HBTNatLayerIso
  child_lt := HBTNat_child_lt

def HBTNatIso (i : Nat) : Mu HBTPoly i ≃ᵢ Nat :=
  HBTNatGeneratedCode.iso i

def HBTSyntaxNatIso (i : Nat) : HBTSyntax i ≃ᵢ Nat :=
  GeneratedCode.natCodeIso HBTGeneratedCode HBTNatGeneratedCode i

end Examples
end BijForm
