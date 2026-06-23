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

/-- One-layer canonical Nat normal-form encoder for height-bounded trees modulo
branch-child swapping. -/
def HBTChildSwapLayerEncode :
    ∀ i, Obj HBTPoly (fun _ => Nat) i → Nat
  | 0, ⟨.leaf, p, h, _child⟩ => by
      cases p with
      | mk height label =>
        cases h
        exact label
  | 0, ⟨.branch, _m, h, _child⟩ => by
      cases h
  | _m + 1, ⟨.leaf, p, h, _child⟩ => by
      cases p with
      | mk height label =>
        cases h
        exact CodeAlgebra.sumNat.toFun (Sum.inl label)
  | _m + 1, ⟨.branch, _k, _h, child⟩ =>
      CodeAlgebra.sumNat.toFun
        (Sum.inr
          (CodeAlgebra.unorderedPairCode (child false) (child true)))

def HBTChildSwapLayerDecodeSucc (m n : Nat) :
    Obj HBTPoly (fun _ => Nat) (m + 1) :=
  match CodeAlgebra.sumNatDecode n with
  | Sum.inl label =>
      ⟨HBTCtor.leaf, ((m + 1, label) : Nat × Nat), rfl,
        fun q => nomatch q⟩
  | Sum.inr pairCode =>
      let pair := (CodeAlgebra.unorderedPairNat.invFun pairCode).val
      ⟨HBTCtor.branch, (m : Nat), rfl, fun
        | false => pair.1
        | true => pair.2⟩

/-- One-layer decoder for canonical HBT branch-swap Nat normal forms. -/
def HBTChildSwapLayerDecode :
    ∀ i, Nat → Obj HBTPoly (fun _ => Nat) i
  | 0, n =>
      ⟨HBTCtor.leaf, ((0, n) : Nat × Nat), rfl, fun q => nomatch q⟩
  | m + 1, n => HBTChildSwapLayerDecodeSucc m n

theorem HBTChildSwapDecodedChildRank :
    ∀ i z,
      (q : HBTPoly.Pos (HBTChildSwapLayerDecode i z).ctor
        (HBTChildSwapLayerDecode i z).param) →
        (HBTChildSwapLayerDecode i z).child q < z := by
  intro i z
  cases i with
  | zero =>
      intro q
      dsimp [HBTChildSwapLayerDecode]
      cases q
  | succ m =>
      dsimp [HBTChildSwapLayerDecode, HBTChildSwapLayerDecodeSucc]
      exact
        match hdecode : CodeAlgebra.sumNatDecode z with
        | Sum.inl _label => by
            intro q
            cases q
        | Sum.inr pairCode => by
            intro q
            have hz := CodeAlgebra.sumNat_encode_decode z
            rw [hdecode] at hz
            cases q
            · exact Nat.lt_of_lt_of_eq
                (CodeAlgebra.unorderedPairNat_invFun_fst_lt_sumNat_inr pairCode)
                hz
            · exact Nat.lt_of_lt_of_eq
                (CodeAlgebra.unorderedPairNat_invFun_snd_lt_sumNat_inr pairCode)
                hz

/-- Layer-local data from which the quotient framework derives the recursive
normalizer, denormalizer, and descended concrete Nat coding. -/
def HBTChildSwapLayerNormalForm :
    QuotientPresentation.LayerNormalForm HBTChildSwapQuotient (fun _ => Nat) where
  encodeLayer := HBTChildSwapLayerEncode
  decodeLayer := HBTChildSwapLayerDecode
  rank := fun _ n => n
  decoded_child_rank_lt := by
    intro i z q
    exact HBTChildSwapDecodedChildRank i z q
  encode_decode_layer := by
    intro i z
    cases i with
    | zero =>
        rfl
    | succ m =>
        dsimp [HBTChildSwapLayerEncode, HBTChildSwapLayerDecode,
          HBTChildSwapLayerDecodeSucc]
        generalize hdecode : CodeAlgebra.sumNatDecode z = s
        have hright := CodeAlgebra.sumNat_encode_decode z
        rw [hdecode] at hright
        cases s with
        | inl label =>
            simpa [HBTChildSwapLayerEncode] using hright
        | inr pairCode =>
            have hpair := CodeAlgebra.unorderedPairCode_invFun pairCode
            simpa [HBTChildSwapLayerEncode, hpair] using hright
  layer_rel_respects := by
    intro i x y encodeChild h
    cases h with
    | branch lhs rhs =>
        simpa [HBTChildSwapLayerEncode, Obj.map, HBTPoly, HBTInput] using
          CodeAlgebra.sumNat_unorderedPairCode_swap
            (encodeChild _ lhs) (encodeChild _ rhs)
  decode_encode_layer_rel := by
    intro i realize layer
    cases layer with
    | mk ctor param out_eq child =>
      cases i with
      | zero =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                cases out_eq
                simp [HBTChildSwapLayerEncode, HBTChildSwapLayerDecode,
                  Obj.map, Mu.inn]
                apply QuotientPresentation.Rel.congr
                intro q
                cases q
          | branch =>
              cases out_eq
      | succ m =>
          cases ctor with
          | leaf =>
              cases param with
              | mk height label =>
                cases out_eq
                dsimp [HBTChildSwapLayerEncode, HBTChildSwapLayerDecode,
                  HBTChildSwapLayerDecodeSucc, Obj.map, Mu.inn]
                rw [show
                  CodeAlgebra.sumNatDecode
                    (CodeAlgebra.sumNat.toFun (Sum.inl label)) =
                      Sum.inl label by
                  exact CodeAlgebra.sumNatDecode_encode (Sum.inl label)]
                simp
                apply QuotientPresentation.Rel.congr
                intro q
                cases q
          | branch =>
              cases out_eq
              dsimp [HBTChildSwapLayerEncode, HBTChildSwapLayerDecode,
                HBTChildSwapLayerDecodeSucc, Obj.map, Mu.inn]
              rw [show
                CodeAlgebra.sumNatDecode
                  (CodeAlgebra.sumNat.toFun
                    (Sum.inr
                      (CodeAlgebra.unorderedPairCode
                        (child false) (child true)))) =
                    Sum.inr
                      (CodeAlgebra.unorderedPairCode
                        (child false) (child true)) by
                exact CodeAlgebra.sumNatDecode_encode
                  (Sum.inr
                    (CodeAlgebra.unorderedPairCode
                      (child false) (child true)))]
              simp
              have hrepair :
                  QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
                    (Mu.sup (P := HBTPoly) .branch m rfl
                      (fun q => realize m (match q with
                        | false =>
                            (CodeAlgebra.unorderedPairNat.invFun
                              (CodeAlgebra.unorderedPairCode
                                (child false) (child true))).val.1
                        | true =>
                            (CodeAlgebra.unorderedPairNat.invFun
                              (CodeAlgebra.unorderedPairCode
                                (child false) (child true))).val.2)))
                    (Mu.sup (P := HBTPoly) .branch m rfl
                      (fun q => realize m (match q with
                        | false => child false
                        | true => child true))) :=
                QuotientPresentation.Rel.unorderedPair_code_decode_encode_repair
                  HBTChildSwapQuotient
                  (fun lhs rhs =>
                    Mu.sup (P := HBTPoly) .branch m rfl
                      (fun q => realize m (match q with
                        | false => lhs
                        | true => rhs)))
                  (child false)
                  (child true)
                  (fun lhs rhs => by
                    have hleft :
                        QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
                          (Mu.sup (P := HBTPoly) .branch m rfl
                            (fun q => realize m (match q with
                              | false => lhs
                              | true => rhs)))
                          (Mu.sup (P := HBTPoly) .branch m rfl (fun
                            | false => realize m lhs
                            | true => realize m rhs)) := by
                      apply QuotientPresentation.Rel.congr
                      intro q
                      cases q <;> exact QuotientPresentation.Rel.refl _
                    have hswap :
                        QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
                          (Mu.sup (P := HBTPoly) .branch m rfl (fun
                            | false => realize m lhs
                            | true => realize m rhs))
                          (Mu.sup (P := HBTPoly) .branch m rfl (fun
                            | false => realize m rhs
                            | true => realize m lhs)) :=
                      QuotientPresentation.Rel.layer
                        (HBTSwapLayerRel.branch (realize m lhs) (realize m rhs))
                    have hright :
                        QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
                          (Mu.sup (P := HBTPoly) .branch m rfl (fun
                            | false => realize m rhs
                            | true => realize m lhs))
                          (Mu.sup (P := HBTPoly) .branch m rfl
                            (fun q => realize m (match q with
                              | false => rhs
                              | true => lhs))) := by
                      apply QuotientPresentation.Rel.congr
                      intro q
                      cases q <;> exact QuotientPresentation.Rel.refl _
                    exact QuotientPresentation.Rel.trans hleft
                      (QuotientPresentation.Rel.trans hswap hright))
              have htarget :
                  QuotientPresentation.Rel HBTChildSwapQuotient (m + 1)
                    (Mu.sup (P := HBTPoly) .branch m rfl
                      (fun q => realize m (match q with
                        | false => child false
                        | true => child true)))
                    (Mu.sup (P := HBTPoly) .branch m rfl
                      (fun q => realize m (child q))) := by
                apply QuotientPresentation.Rel.congr
                intro q
                cases q <;> exact QuotientPresentation.Rel.refl _
              exact QuotientPresentation.Rel.trans hrepair htarget

/-- Concrete descent of the generated HBT Nat code through the branch-swap
quotient relation. -/
def HBTChildSwapDescendedNatCode :
    QuotientPresentation.DescendedGeneratedCode HBTChildSwapQuotient
      HBTNatGeneratedCode (fun _ => Nat) :=
  HBTChildSwapLayerNormalForm.descendedGeneratedCode HBTNatGeneratedCode

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
