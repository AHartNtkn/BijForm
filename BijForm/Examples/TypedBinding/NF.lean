import BijForm.TypedBinding

namespace BijForm
namespace Examples
namespace TypedBinding

open DepPoly
open BijForm.TypedBinding

/-!
## Normal-form lambda expressions

The blog-post normal-form syntax has two mutually recursive sorts.  Variables
belong to the application-term sort.  The lambda constructor binds one
application-term variable in its body, while the other recursive arguments use empty
binder lists.
-/

inductive NFSort where
  | normalExp
  | appTerm
deriving DecidableEq, Repr

inductive NFCtor where
  | dum
  | lam
  | app
deriving DecidableEq, Repr

def NFArgs : NFCtor → List (Arg NFSort)
  | .dum => [{ binders := [], sort := .appTerm }]
  | .lam => [{ binders := [.appTerm], sort := .normalExp }]
  | .app =>
      [{ binders := [], sort := .appTerm },
       { binders := [], sort := .normalExp }]

def NFRet : NFCtor → NFSort
  | .dum => .normalExp
  | .lam => .normalExp
  | .app => .appTerm

def NFSignature : Signature NFSort where
  Ctor := NFCtor
  args := NFArgs
  ret := NFRet

abbrev NFTerm (Γ : List NFSort) (t : NFSort) : Type :=
  Term NFSignature Γ t

abbrev NFPoly : DepPoly (Poly.Ix NFSignature) :=
  PolyOf NFSignature

def NormalExp (Γ : List NFSort) : Type :=
  NFTerm Γ .normalExp

def AppTerm (Γ : List NFSort) : Type :=
  NFTerm Γ .appTerm

def NFClosed : Type :=
  NormalExp []

def NFVar {Γ : List NFSort} (v : Var Γ .appTerm) : AppTerm Γ :=
  Term.var v

def NFDum {Γ : List NFSort} (e : AppTerm Γ) : NormalExp Γ :=
  Term.op (S := NFSignature) NFCtor.dum (fun
    | ⟨0, _⟩ => e
    | ⟨n + 1, h⟩ => by
        simp [NFSignature, NFArgs] at h)

def NFLam {Γ : List NFSort} (body : NormalExp (.appTerm :: Γ)) :
    NormalExp Γ :=
  Term.op (S := NFSignature) NFCtor.lam (fun
    | ⟨0, _⟩ => body
    | ⟨n + 1, h⟩ => by
        simp [NFSignature, NFArgs] at h)

def NFApp {Γ : List NFSort} (fn : AppTerm Γ) (arg : NormalExp Γ) :
    AppTerm Γ :=
  Term.op (S := NFSignature) NFCtor.app (fun
    | ⟨0, _⟩ => fn
    | ⟨1, _⟩ => arg
    | ⟨n + 2, h⟩ => by
        simp [NFSignature, NFArgs] at h
        omega)

def NFInversion : OutputIndexInversion NFPoly :=
  inversion NFSignature

def NFSyntaxIso (Γ : List NFSort) (t : NFSort) :
    Mu NFPoly (Γ, t) ≃ᵢ NFTerm Γ t :=
  syntaxIso NFSignature Γ t

abbrev appTermCount (Γ : List NFSort) : Nat :=
  Var.count NFSort.appTerm Γ

abbrev normalExpCount (Γ : List NFSort) : Nat :=
  Var.count NFSort.normalExp Γ

def NFCode : Poly.Ix NFSignature → Type
  | (_, .normalExp) => Nat
  | (Γ, .appTerm) => Fin (appTermCount Γ) × Nat

theorem NFCode_normalExp_carrier (Γ : List NFSort) :
    NFCode (Γ, .normalExp) = Nat :=
  rfl

theorem NFCode_appTerm_carrier (Γ : List NFSort) :
    NFCode (Γ, .appTerm) = (Fin (appTermCount Γ) × Nat) :=
  rfl

def NFCodeRank : ∀ i, NFCode i → Nat
  | (Γ, .normalExp), n => by
      change Nat at n
      exact if appTermCount Γ = 0 then 2 * n + 2 else 2 * n + 1
  | (_, .appTerm), p => 2 * p.2

abbrev NFNormalCtorCarrier (Γ : List NFSort) : Type :=
  NFCode (Γ, .appTerm) ⊕ Nat

abbrev NFAppCtorCarrier (Γ : List NFSort) : Type :=
  NFCode (Γ, .appTerm) × Nat

def NFNormalFamilyToCarrier (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .normalExp → NFNormalCtorCarrier Γ
  | ⟨.dum, h, args⟩ => by
      cases h
      exact Sum.inl args.1
  | ⟨.lam, h, args⟩ => by
      cases h
      exact Sum.inr args.1
  | ⟨.app, h, _args⟩ => by
      cases h

def NFNormalFamilyOfCarrier (Γ : List NFSort) :
    NFNormalCtorCarrier Γ → CtorFamily NFSignature NFCode Γ .normalExp
  | Sum.inl e =>
      ⟨.dum, rfl, (e, PUnit.unit)⟩
  | Sum.inr body =>
      ⟨.lam, rfl, (body, PUnit.unit)⟩

def NFNormalFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .normalExp ≃ᵢ NFNormalCtorCarrier Γ where
  toFun := NFNormalFamilyToCarrier Γ
  invFun := NFNormalFamilyOfCarrier Γ
  left_inv := by
    intro family
    cases family with
    | mk c h args =>
        cases c with
        | dum =>
            cases h
            cases args with
            | mk e rest =>
                cases rest
                rfl
        | lam =>
            cases h
            cases args with
            | mk body rest =>
                cases rest
                rfl
        | app =>
            cases h
  right_inv := by
    intro x
    cases x with
    | inl e => rfl
    | inr body => rfl

def NFAppFamilyToCarrier (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .appTerm → NFAppCtorCarrier Γ
  | ⟨.app, h, args⟩ => by
      cases h
      exact (args.1, args.2.1)
  | ⟨.dum, h, _args⟩ => by
      cases h
  | ⟨.lam, h, _args⟩ => by
      cases h

def NFAppFamilyOfCarrier (Γ : List NFSort) :
    NFAppCtorCarrier Γ → CtorFamily NFSignature NFCode Γ .appTerm
  | pair =>
      ⟨.app, rfl, (pair.1, (pair.2, PUnit.unit))⟩

def NFAppFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .appTerm ≃ᵢ NFAppCtorCarrier Γ where
  toFun := NFAppFamilyToCarrier Γ
  invFun := NFAppFamilyOfCarrier Γ
  left_inv := by
    intro family
    cases family with
    | mk c h args =>
        cases c with
        | dum =>
            cases h
        | lam =>
            cases h
        | app =>
            cases h
            cases args with
            | mk fn rest =>
                cases rest with
                | mk arg restDone =>
                    cases restDone
                    rfl
  right_inv := by
    intro pair
    cases pair
    rfl

def NFNormalGeneratedShapeIso (Γ : List NFSort) :
    LayerShape NFSignature NFCode Γ .normalExp ≃ᵢ NFCode (Γ, .normalExp) :=
  Iso.trans
    (LayerShape.familyCarrierIso (S := NFSignature) (Code := NFCode)
      Γ .normalExp (Var.finIso Γ .normalExp) (NFNormalFamilyCarrierIso Γ))
    (Iso.trans
      (Iso.sum (Iso.refl (Fin (normalExpCount Γ)))
        (CodeAlgebra.finProdNatOrNat (appTermCount Γ)))
      (CodeAlgebra.finPlusNat (normalExpCount Γ)))

def NFAppGeneratedShapeIso (Γ : List NFSort) :
    LayerShape NFSignature NFCode Γ .appTerm ≃ᵢ NFCode (Γ, .appTerm) :=
  Iso.trans
    (LayerShape.familyCarrierIso (S := NFSignature) (Code := NFCode)
      Γ .appTerm (Var.finIso Γ .appTerm) (NFAppFamilyCarrierIso Γ))
    (CodeAlgebra.finTaggedProdNat (appTermCount Γ))

def NFGeneratedShapeIso :
    ∀ Γ t, LayerShape NFSignature NFCode Γ t ≃ᵢ NFCode (Γ, t)
  | Γ, .normalExp => NFNormalGeneratedShapeIso Γ
  | Γ, .appTerm => NFAppGeneratedShapeIso Γ

theorem NFGeneratedLayer_child_rank_lt :
    LayerShapeRankProof NFSignature NFCode NFGeneratedShapeIso NFCodeRank := by
  intro Γ t layer
  cases t with
    | normalExp =>
        cases layer with
        | mk code child =>
          cases code with
          | var v =>
              intro q
              cases q
          | op c h =>
              cases c with
              | dum =>
                  cases h
                  intro q
                  cases q using Fin.cases with
                  | zero =>
                      let app : Fin (appTermCount Γ) × Nat := child ⟨0, by decide⟩
                      have hcount : 0 < appTermCount Γ :=
                        Nat.lt_of_le_of_lt (Nat.zero_le app.1.val) app.1.isLt
                      have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
                      let tail :=
                        (CodeAlgebra.finProdNatOrNat (appTermCount Γ)).toFun
                          (Sum.inl app)
                      have hparent :
                          (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                              ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                Γ NFSort.normalExp).toFun
                                ⟨FiberCode.op NFCtor.dum rfl, child⟩) =
                            normalExpCount Γ + tail := by
                        simp [app, tail, hcount, NFGeneratedShapeIso,
                          NFNormalGeneratedShapeIso, NFNormalFamilyCarrierIso,
                          NFNormalFamilyToCarrier, LayerShape.iso,
                          LayerShape.layerToShape, LayerShape.familyCarrierIso,
                          LayerShape.familyIso,
                          CtorLayer.familyIso, CtorLayer.toFamily,
                          ArgTuple.ofChild, ListPiTuple.ofPi, Iso.trans, Iso.sum,
                          CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
                      change NFCodeRank (Γ, NFSort.appTerm) app <
                        NFCodeRank (Γ, NFSort.normalExp)
                          ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                            ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                              Γ NFSort.normalExp).toFun
                              ⟨FiberCode.op NFCtor.dum rfl, child⟩))
                      rw [hparent]
                      simp [NFCodeRank, hcne]
                      have happ_le : app.2 ≤ tail := by
                        simpa [tail] using
                          CodeAlgebra.finProdNatOrNat_inl_snd_le
                            (appTermCount Γ) app
                      omega
                  | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)
              | lam =>
                  cases h
                  intro q
                  cases q using Fin.cases with
                  | zero =>
                      let body : Nat := child ⟨0, by decide⟩
                      let tail :=
                        (CodeAlgebra.finProdNatOrNat (appTermCount Γ)).toFun
                          (Sum.inr body)
                      have hbody_le : body ≤ tail := by
                        simpa [tail] using
                          CodeAlgebra.finProdNatOrNat_inr_le
                            (appTermCount Γ) body
                      by_cases hc : appTermCount Γ = 0
                      · have hparent :
                            (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                                ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                  Γ NFSort.normalExp).toFun
                                  ⟨FiberCode.op NFCtor.lam rfl, child⟩) =
                              normalExpCount Γ + tail := by
                          simp [body, tail, hc, NFGeneratedShapeIso,
                            NFNormalGeneratedShapeIso, NFNormalFamilyCarrierIso,
                            NFNormalFamilyToCarrier, LayerShape.iso,
                            LayerShape.layerToShape, LayerShape.familyCarrierIso,
                            LayerShape.familyIso,
                            CtorLayer.familyIso, CtorLayer.toFamily,
                            ArgTuple.ofChild, ListPiTuple.ofPi, Iso.trans, Iso.sum,
                            CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
                        change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                          NFCodeRank (Γ, NFSort.normalExp)
                            ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                              ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                Γ NFSort.normalExp).toFun
                                ⟨FiberCode.op NFCtor.lam rfl, child⟩))
                        rw [hparent]
                        simp [NFCodeRank, appTermCount, Var.count, hc]
                        omega
                      · have hpos : 0 < appTermCount Γ := Nat.pos_of_ne_zero hc
                        have hbody_lt : body < tail := by
                          simpa [tail] using
                            CodeAlgebra.finProdNatOrNat_inr_lt_of_pos
                              (k := appTermCount Γ) (n := body) hpos
                        have hparent :
                            (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                                ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                  Γ NFSort.normalExp).toFun
                                  ⟨FiberCode.op NFCtor.lam rfl, child⟩) =
                              normalExpCount Γ + tail := by
                          simp [body, tail, hpos, NFGeneratedShapeIso,
                            NFNormalGeneratedShapeIso, NFNormalFamilyCarrierIso,
                            NFNormalFamilyToCarrier, LayerShape.iso,
                            LayerShape.layerToShape, LayerShape.familyCarrierIso,
                            LayerShape.familyIso,
                            CtorLayer.familyIso, CtorLayer.toFamily,
                            ArgTuple.ofChild, ListPiTuple.ofPi, Iso.trans, Iso.sum,
                            CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
                        change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                          NFCodeRank (Γ, NFSort.normalExp)
                            ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                              ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                Γ NFSort.normalExp).toFun
                                ⟨FiberCode.op NFCtor.lam rfl, child⟩))
                        rw [hparent]
                        simp [NFCodeRank, appTermCount, Var.count, hc]
                        omega
                  | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)
              | app =>
                  cases h
    | appTerm =>
        cases layer with
        | mk code child =>
          cases code with
          | var v =>
              intro q
              cases q
          | op c h =>
              cases c with
              | dum =>
                  cases h
              | lam =>
                  cases h
              | app =>
                  cases h
                  intro q
                  let fn : Fin (appTermCount Γ) × Nat := child ⟨0, by decide⟩
                  let arg : Nat := child ⟨1, by decide⟩
                  have hcount : 0 < appTermCount Γ :=
                    Nat.lt_of_le_of_lt (Nat.zero_le fn.1.val) fn.1.isLt
                  have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
                  let pair := (fn, arg)
                  have hparent :
                      (NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                          ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                            Γ NFSort.appTerm).toFun
                            ⟨FiberCode.op NFCtor.app rfl, child⟩) =
                        (CodeAlgebra.finTaggedProdNat (appTermCount Γ)).toFun
                          (Sum.inr pair) := by
                    simp [fn, arg, pair, NFGeneratedShapeIso,
                      NFAppGeneratedShapeIso, NFAppFamilyCarrierIso,
                      NFAppFamilyToCarrier, LayerShape.iso, LayerShape.layerToShape,
                      LayerShape.familyCarrierIso, LayerShape.familyIso,
                      CtorLayer.familyIso, CtorLayer.toFamily,
                      ArgTuple.ofChild, ListPiTuple.ofPi, Iso.trans, Iso.sum]
                  cases q using Fin.cases with
                  | zero =>
                      change NFCodeRank (Γ, NFSort.appTerm) fn <
                        NFCodeRank (Γ, NFSort.appTerm)
                          ((NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                            ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                              Γ NFSort.appTerm).toFun
                              ⟨FiberCode.op NFCtor.app rfl, child⟩))
                      rw [hparent]
                      simp [NFCodeRank]
                      have hfn_lt :
                          fn.2 <
                            ((CodeAlgebra.finTaggedProdNat
                              (appTermCount Γ)).toFun (Sum.inr pair)).2 := by
                        simpa [pair] using
                          CodeAlgebra.finTaggedProdNat_inr_fst_payload_lt
                            (appTermCount Γ) pair
                      omega
                  | succ q =>
                      cases q using Fin.cases with
                      | zero =>
                          change NFCodeRank (Γ, NFSort.normalExp) arg <
                            NFCodeRank (Γ, NFSort.appTerm)
                              ((NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                                ((LayerShape.iso (S := NFSignature) (Code := NFCode)
                                  Γ NFSort.appTerm).toFun
                                  ⟨FiberCode.op NFCtor.app rfl, child⟩))
                          rw [hparent]
                          simp [NFCodeRank, hcne]
                          have harg_lt :
                              arg <
                                ((CodeAlgebra.finTaggedProdNat
                                  (appTermCount Γ)).toFun (Sum.inr pair)).2 := by
                            simpa [pair] using
                              CodeAlgebra.finTaggedProdNat_inr_snd_lt
                                (appTermCount Γ) pair
                          omega
                      | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)

def NFLayerShapeCodingData : LayerShapeCodingData NFSignature where
  Code := NFCode
  layerShape := NFGeneratedShapeIso
  rank := NFCodeRank
  shape_child_rank_lt := by
    intro Γ t layer q
    exact NFGeneratedLayer_child_rank_lt layer q

def NFSyntaxCodeIso (Γ : List NFSort) (t : NFSort) :
    NFTerm Γ t ≃ᵢ NFCode (Γ, t) :=
  NFLayerShapeCodingData.syntaxCodeIso Γ t

def NormalExpNatIso (Γ : List NFSort) : NormalExp Γ ≃ᵢ Nat :=
  NFSyntaxCodeIso Γ .normalExp

def AppTermCodeIso (Γ : List NFSort) :
    AppTerm Γ ≃ᵢ (Fin (appTermCount Γ) × Nat) :=
  NFSyntaxCodeIso Γ .appTerm

def NFClosedNatIso : NFClosed ≃ᵢ Nat :=
  NormalExpNatIso []

theorem NFCode_closedNormal_carrier : NFCode ([], .normalExp) = Nat :=
  rfl

theorem NFCode_closedApp_carrier :
    NFCode ([], .appTerm) = (Fin 0 × Nat) :=
  rfl

def ClosedAppTermEmptyIso : AppTerm [] ≃ᵢ Empty where
  toFun := fun x =>
    let code := (AppTermCodeIso []).toFun x
    False.elim (Nat.not_lt_zero code.1.val code.1.isLt)
  invFun := fun e => nomatch e
  left_inv := by
    intro x
    let code := (AppTermCodeIso []).toFun x
    exact False.elim (Nat.not_lt_zero code.1.val code.1.isLt)
  right_inv := by
    intro e
    cases e

end TypedBinding
end Examples
end BijForm
