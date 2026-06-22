import BijForm.QuotientPolynomial
import BijForm.Examples.HBT

namespace BijForm
namespace Examples

open DepPoly

/-
Concrete quotient example: a constructor-layer branch-swap quotient descends
the generated height-bounded-tree Nat code to a canonical Nat normal form.
-/

/-- One-step quotient relation for height-bounded trees modulo swapping the
two children of a branch node. -/
inductive HBTSwapLayerRel :
    ∀ i, Obj HBTPoly (Mu HBTPoly) i → Obj HBTPoly (Mu HBTPoly) i → Prop
  | branch {m : Nat} (lhs rhs : Mu HBTPoly m) :
      HBTSwapLayerRel (m + 1)
        { ctor := .branch
          param := m
          out_eq := rfl
          child := fun
            | false => lhs
            | true => rhs }
        { ctor := .branch
          param := m
          out_eq := rfl
          child := fun
            | false => rhs
            | true => lhs }

/-- Quotient presentation for height-bounded trees where branch children are
unordered. -/
def HBTChildSwapQuotient : QuotientPresentation HBTPoly where
  LayerRel := HBTSwapLayerRel

/-- Height-bounded trees modulo branch-child swapping, generated from the
dependent-polynomial quotient presentation. -/
abbrev HBTChildSwap (i : Nat) : Type :=
  HBTChildSwapQuotient.Carrier i

/-- The quotient equates a branch with the same branch whose two children are
swapped. -/
theorem HBTChildSwap_branch_sound {m : Nat} (lhs rhs : Mu HBTPoly m) :
    HBTChildSwapQuotient.ofMu
        (Mu.sup (P := HBTPoly) .branch m rfl
          (fun
            | false => lhs
            | true => rhs))
      =
      HBTChildSwapQuotient.ofMu
        (Mu.sup (P := HBTPoly) .branch m rfl
          (fun
            | false => rhs
            | true => lhs)) := by
  apply QuotientPresentation.sound
  exact QuotientPresentation.Rel.layer (HBTSwapLayerRel.branch lhs rhs)

/-- Raw branch layer used to state constructor-surface quotient equations. -/
def HBTRawBranchObj {m : Nat} (lhs rhs : Mu HBTPoly m) :
    Obj HBTPoly (Mu HBTPoly) (m + 1) where
  ctor := HBTCtor.branch
  param := m
  out_eq := rfl
  child := fun
    | false => lhs
    | true => rhs

/-- The branch-swap layer relation is respected by raw quotient introduction. -/
theorem HBTChildSwap_innRaw_branch_sound {m : Nat} (lhs rhs : Mu HBTPoly m) :
    HBTChildSwapQuotient.innRaw (HBTRawBranchObj lhs rhs)
      =
      HBTChildSwapQuotient.innRaw (HBTRawBranchObj rhs lhs) := by
  exact HBTChildSwapQuotient.innRaw_layer_sound
    (HBTSwapLayerRel.branch lhs rhs)

/-- The Nat-code relation induced by the branch-swap quotient and the existing
generated Nat coding for height-bounded trees. -/
abbrev HBTChildSwapNatCodeRel (i : Nat) (a b : Nat) : Prop :=
  HBTChildSwapQuotient.GeneratedCodeRel HBTNatGeneratedCode i a b

/-- Canonical code carrier for branch-swap quotient trees: quotient the
generated Nat code by the transported branch-swap relation. -/
abbrev HBTChildSwapNatCode (i : Nat) : Type :=
  HBTChildSwapQuotient.GeneratedCodeCarrier HBTNatGeneratedCode i

/-- The generic quotient-polynomial theorem specializes to a coding of
height-bounded branch-swap quotient trees by a quotient of the generated Nat
code. -/
def HBTChildSwapNatCodeIso (i : Nat) :
    HBTChildSwap i ≃ᵢ HBTChildSwapNatCode i :=
  HBTChildSwapQuotient.generatedCodeIso HBTNatGeneratedCode i

def HBTQuotLeaf (i label : Nat) : Mu HBTPoly i :=
  Mu.sup (P := HBTPoly) .leaf (i, label) rfl (fun q => nomatch q)

def HBTQuotBranch (m : Nat) (lhs rhs : Mu HBTPoly m) :
    Mu HBTPoly (m + 1) :=
  Mu.sup (P := HBTPoly) .branch m rfl (fun
    | false => lhs
    | true => rhs)

theorem HBTChildSwap_branch_congr {m : Nat}
    {lhs lhs' rhs rhs' : Mu HBTPoly m}
    (hlhs : QuotientPresentation.Rel HBTChildSwapQuotient m lhs lhs')
    (hrhs : QuotientPresentation.Rel HBTChildSwapQuotient m rhs rhs') :
    QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
      (HBTQuotBranch m lhs rhs) (HBTQuotBranch m lhs' rhs') := by
  apply QuotientPresentation.Rel.congr
  intro q
  cases q
  · exact hlhs
  · exact hrhs

theorem HBTChildSwap_branch_eta {m : Nat}
    (child : Bool → Mu HBTPoly m) :
    QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
      (HBTQuotBranch m (child false) (child true))
      (Mu.sup (P := HBTPoly) .branch m rfl child) := by
  apply QuotientPresentation.Rel.congr
  intro q
  cases q <;> exact QuotientPresentation.Rel.refl _

theorem HBTChildSwap_branch_swap_rel {m : Nat}
    (lhs rhs : Mu HBTPoly m) :
    QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
      (HBTQuotBranch m lhs rhs) (HBTQuotBranch m rhs lhs) :=
  QuotientPresentation.Rel.layer (HBTSwapLayerRel.branch lhs rhs)

/-- Canonical Nat normal form for height-bounded trees modulo branch-child
swapping. -/
def HBTChildSwapNorm : ∀ i, Mu HBTPoly i → Nat
  | 0, Mu.sup .leaf p _h _child => p.2
  | 0, Mu.sup .branch _m h _child => by cases h
  | _m + 1, Mu.sup .leaf p _h _child =>
      CodeAlgebra.sumNat.toFun (Sum.inl p.2)
  | _m + 1, Mu.sup .branch k _h child =>
      CodeAlgebra.sumNat.toFun
        (Sum.inr
          (CodeAlgebra.unorderedPairCode
            (HBTChildSwapNorm k (child false))
            (HBTChildSwapNorm k (child true))))

/-- Decode a concrete Nat normal form into a representative tree. -/
def HBTChildSwapDenorm : ∀ i, Nat → Mu HBTPoly i
  | 0, n => HBTQuotLeaf 0 n
  | m + 1, n =>
      match CodeAlgebra.sumNat.invFun n with
      | Sum.inl label => HBTQuotLeaf (m + 1) label
      | Sum.inr pairCode =>
          let pair := (CodeAlgebra.unorderedPairNat.invFun pairCode).val
          HBTQuotBranch m
            (HBTChildSwapDenorm m pair.1)
            (HBTChildSwapDenorm m pair.2)

theorem HBTChildSwap_norm_denorm :
    ∀ i (n : Nat), HBTChildSwapNorm i (HBTChildSwapDenorm i n) = n
  | 0, _n => rfl
  | m + 1, n => by
      dsimp [HBTChildSwapDenorm]
      generalize hsum : CodeAlgebra.sumNat.invFun n = s
      have hright := CodeAlgebra.sumNat.right_inv n
      rw [hsum] at hright
      cases s with
      | inl label =>
          simpa [HBTChildSwapNorm, HBTQuotLeaf] using hright
      | inr pairCode =>
          let pair := (CodeAlgebra.unorderedPairNat.invFun pairCode).val
          have hleft :=
            HBTChildSwap_norm_denorm m pair.1
          have hright_child :=
            HBTChildSwap_norm_denorm m pair.2
          have hpair :
              CodeAlgebra.unorderedPairCode
                (HBTChildSwapNorm m (HBTChildSwapDenorm m pair.1))
                (HBTChildSwapNorm m (HBTChildSwapDenorm m pair.2)) =
                pairCode := by
            rw [hleft, hright_child]
            exact CodeAlgebra.unorderedPairCode_invFun pairCode
          simpa [HBTChildSwapNorm, HBTQuotBranch, pair, hpair] using hright

theorem HBTChildSwap_denorm_norm_rel :
    ∀ i (x : Mu HBTPoly i),
      QuotientPresentation.Rel HBTChildSwapQuotient i
        (HBTChildSwapDenorm i (HBTChildSwapNorm i x)) x
  | 0, Mu.sup .leaf p h child => by
      cases p with
      | mk height label =>
        cases h
        apply QuotientPresentation.Rel.congr
        intro q
        cases q
  | 0, Mu.sup .branch _m h _child => by
      cases h
  | m + 1, Mu.sup .leaf p h child => by
      cases p with
      | mk height label =>
        cases h
        dsimp [HBTChildSwapNorm, HBTChildSwapDenorm]
        rw [CodeAlgebra.sumNat.left_inv (Sum.inl label)]
        apply QuotientPresentation.Rel.congr
        intro q
        cases q
  | m + 1, Mu.sup .branch k h child => by
      cases h
      dsimp [HBTChildSwapNorm, HBTChildSwapDenorm]
      rw [CodeAlgebra.sumNat.left_inv
        (Sum.inr
          (CodeAlgebra.unorderedPairCode
            (HBTChildSwapNorm m (child false))
            (HBTChildSwapNorm m (child true))))]
      exact QuotientPresentation.Rel.unorderedPair_decode_encode_repair
        HBTChildSwapQuotient
        (HBTChildSwapNorm m)
        (HBTChildSwapDenorm m)
        (HBTQuotBranch m)
        (child false)
        (child true)
        (HBTChildSwap_denorm_norm_rel m (child false))
        (HBTChildSwap_denorm_norm_rel m (child true))
        (fun hlhs hrhs => HBTChildSwap_branch_congr hlhs hrhs)
        HBTChildSwap_branch_swap_rel
        (HBTChildSwap_branch_eta child)

theorem HBTChildSwap_norm_respects :
    ∀ {i : Nat} {x y : Mu HBTPoly i},
      QuotientPresentation.Rel HBTChildSwapQuotient i x y →
        HBTChildSwapNorm i x = HBTChildSwapNorm i y := by
  exact QuotientPresentation.Rel.respects_of_layer_congr
    HBTChildSwapQuotient HBTChildSwapNorm
    (by
      intro i x y h
      cases h with
      | branch lhs rhs =>
          simp [Mu.inn, HBTChildSwapNorm,
            CodeAlgebra.unorderedPairCode_comm])
    (by
      intro i c p h child child' ih
      cases c with
      | leaf =>
          cases i <;> rfl
      | branch =>
          cases i with
          | zero => cases h
          | succ m =>
              dsimp [HBTChildSwapNorm]
              have hfalse :
                  HBTChildSwapNorm p (child false) =
                    HBTChildSwapNorm p (child' false) := by
                simpa [HBTPoly, HBTInput] using ih false
              have htrue :
                  HBTChildSwapNorm p (child true) =
                    HBTChildSwapNorm p (child' true) := by
                simpa [HBTPoly, HBTInput] using ih true
              rw [hfalse, htrue])

/-- Concrete descent of the generated HBT Nat code through the branch-swap
quotient relation. -/
def HBTChildSwapDescendedNatCode :
    QuotientPresentation.DescendedGeneratedCode HBTChildSwapQuotient
      HBTNatGeneratedCode (fun _ => Nat) :=
  QuotientPresentation.DescendedGeneratedCode.ofMuNormalizer
    (C := HBTNatGeneratedCode)
    HBTChildSwapNorm
    HBTChildSwapDenorm
    (by
      intro i x y hxy
      exact HBTChildSwap_norm_respects hxy)
    HBTChildSwap_denorm_norm_rel
    HBTChildSwap_norm_denorm

/-- Height-bounded trees modulo branch-child swapping are concretely coded by
`Nat`. The coding is obtained by descending the generated HBT Nat code through
the quotient relation. -/
def HBTChildSwapNatIso (i : Nat) : HBTChildSwap i ≃ᵢ Nat :=
  QuotientPresentation.DescendedGeneratedCode.carrierIso
    HBTChildSwapDescendedNatCode i

/-- Readable height-bounded syntax transported to the generated branch-swap
quotient relation through `HBTSyntaxIso`. -/
def HBTSyntaxSwapRel (i : Nat) (x y : HBTSyntax i) : Prop :=
  QuotientPresentation.SyntaxRel HBTChildSwapQuotient HBTSyntaxIso i x y

/-- The readable syntax branch-swap relation as an explicit setoid. -/
def HBTSyntaxSwapSetoid (i : Nat) : Setoid (HBTSyntax i) :=
  QuotientPresentation.syntaxSetoid HBTChildSwapQuotient HBTSyntaxIso i

/-- Readable height-bounded syntax modulo branch-child swapping. -/
abbrev HBTSyntaxChildSwap (i : Nat) : Type :=
  QuotientPresentation.SyntaxCarrier HBTChildSwapQuotient HBTSyntaxIso i

/-- The readable syntax quotient is the generated quotient-polynomial carrier. -/
def HBTSyntaxChildSwapIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwap i :=
  QuotientPresentation.syntaxCarrierIso HBTChildSwapQuotient HBTSyntaxIso i

/-- Intermediate encoding theorem for readable branch-swap quotient syntax into
the quotient of generated Nat codes. -/
def HBTSyntaxChildSwapNatCodeIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ HBTChildSwapNatCode i :=
  Iso.trans (HBTSyntaxChildSwapIso i) (HBTChildSwapNatCodeIso i)

/-- Readable height-bounded syntax modulo branch-child swapping is concretely
coded by `Nat`. -/
def HBTSyntaxChildSwapNatIso (i : Nat) :
    HBTSyntaxChildSwap i ≃ᵢ Nat :=
  Iso.trans (HBTSyntaxChildSwapIso i) (HBTChildSwapNatIso i)

end Examples
end BijForm
