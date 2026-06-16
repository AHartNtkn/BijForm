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

/-- Index-local constructor codes for height-bounded trees. At target height
`i`, a branch code must include an explicit predecessor `m` with `m + 1 = i`. -/
inductive HBTCode (i : Nat) where
  | leaf (label : Nat)
  | branch (m : Nat) (out_eq : m + 1 = i)

def HBTDecode (i : Nat) : HBTCode i → Fiber HBTPoly i
  | .leaf label => ⟨.leaf, (i, label), rfl⟩
  | .branch m h => ⟨.branch, m, h⟩

def HBTEncode (i : Nat) : Fiber HBTPoly i → HBTCode i
  | ⟨.leaf, p, h⟩ =>
      have _ : HBTPoly.out HBTCtor.leaf p = i := h
      .leaf (i := i) p.2
  | ⟨.branch, m, h⟩ => .branch (i := i) m h

theorem HBT_decode_encode (i : Nat) (f : Fiber HBTPoly i) :
    HBTDecode i (HBTEncode i f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | leaf =>
        cases param with
        | mk n label =>
          cases out_eq
          rfl
    | branch =>
        rfl

theorem HBT_encode_decode (i : Nat) (c : HBTCode i) :
    HBTEncode i (HBTDecode i c) = c := by
  cases c with
  | leaf label => rfl
  | branch m h => rfl

/-- The non-opaque output-index inversion for the height-bounded-tree example. -/
def HBTInversion : OutputIndexInversion HBTPoly where
  Code := HBTCode
  decode := HBTDecode
  encode := HBTEncode
  decode_encode := HBT_decode_encode
  encode_decode := HBT_encode_decode

/-- The fiber of branch constructors at height zero is empty. -/
theorem no_zero_height_branch (f : Fiber HBTPoly 0) (hctor : f.ctor = .branch) :
    False := by
  cases f with
  | mk ctor param out_eq =>
    cases hctor
    cases out_eq

/-- The fiber of branch constructors at `m+1` contains the predecessor `m`. -/
def branchAtSucc (m : Nat) : Fiber HBTPoly (m + 1) :=
  HBTDecode (m + 1) (.branch m rfl)

def HBTLayerToSyntax (i : Nat) :
    CodeLayer HBTPoly HBTInversion HBTSyntax i → HBTSyntax i
  | ⟨.leaf label, _child⟩ =>
      .leaf label
  | ⟨.branch _m h, child⟩ =>
      h ▸ (.branch (child false) (child true))

def HBTSyntaxToLayer (i : Nat) :
    HBTSyntax i → CodeLayer HBTPoly HBTInversion HBTSyntax i
  | .leaf label =>
      ⟨.leaf label, fun q => nomatch q⟩
  | @HBTSyntax.branch m lhs rhs =>
      ⟨.branch m rfl, fun (b : Bool) => if b then rhs else lhs⟩

theorem HBTLayer_left_inv (i : Nat) :
    Function.LeftInverse (HBTSyntaxToLayer i) (HBTLayerToSyntax i) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | leaf label =>
        have hchild : (fun q => nomatch q) = child := by
          funext q
          cases q
        cases hchild
        rfl
    | branch m h =>
        cases h
        have hchild : child = (fun (b : Bool) => if b then child true else child false) := by
          funext q
          cases q <;> rfl
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
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion, HBTDecode,
          HBTSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (HBTSyntax.rank lhs) (HBTSyntax.rank rhs))
      · simpa [HBTLayerIso, HBTSyntaxToLayer, HBTInversion, HBTDecode,
          HBTSyntax.rank] using
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
    | ⟨.leaf label, _child⟩ => label
    | ⟨.branch _ h, _child⟩ => by cases h
  invFun n := ⟨.leaf n, fun q => nomatch q⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | leaf label =>
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
        | branch m h => cases h
  right_inv := by
    intro n
    rfl

def HBTNatSuccLayerSumIso (m : Nat) :
    CodeLayer HBTPoly HBTInversion (fun _ => Nat) (m + 1) ≃ᵢ
      (Nat ⊕ (Nat × Nat)) where
  toFun
    | ⟨.leaf label, _child⟩ => Sum.inl label
    | ⟨.branch _ _h, child⟩ => Sum.inr (child false, child true)
  invFun
    | Sum.inl label => ⟨.leaf label, fun q => nomatch q⟩
    | Sum.inr p => ⟨.branch m rfl, fun
        | false => p.1
        | true => p.2⟩
  left_inv := by
    intro x
    cases x with
    | mk code child =>
        cases code with
        | leaf label =>
            have hchild : (fun q => nomatch q) = child := by
              funext q
              cases q
            cases hchild
            rfl
        | branch k h =>
            cases h
            have hchild : child = (fun
                | false => child false
                | true => child true) := by
              funext q
              cases q <;> rfl
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
  Iso.trans (HBTNatSuccLayerSumIso m)
    (Iso.trans (Iso.sum (Iso.refl Nat) CodeAlgebra.prodNat) CodeAlgebra.sumNat)

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
      dsimp [HBTNatLayerIso, HBTNatSuccLayerIso, Iso.trans, Iso.sum]
      generalize hsum : CodeAlgebra.sumNat.invFun n = s
      cases s with
      | inl label =>
          intro q
          cases q
      | inr pairCode =>
          intro q
          have hright := CodeAlgebra.sumNat.right_inv n
          rw [hsum] at hright
          simp [CodeAlgebra.sumNat] at hright
          cases q
          · change (CodeAlgebra.prodNat.invFun pairCode).1 < n
            have hle := CodeAlgebra.prodNat_fst_le pairCode
            omega
          · change (CodeAlgebra.prodNat.invFun pairCode).2 < n
            have hle := CodeAlgebra.prodNat_snd_le pairCode
            omega

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
  Iso.trans (Iso.symm (HBTSyntaxIso i)) (HBTNatIso i)

end Examples
end BijForm
