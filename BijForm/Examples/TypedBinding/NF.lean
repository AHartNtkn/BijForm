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

def NFNormalDumArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.dum) ≃ᵢ
      NFCode (Γ, .appTerm) :=
  ArgTuple.singleIso (S := NFSignature) (Code := NFCode) Γ
    { binders := [], sort := .appTerm }

def NFNormalLamArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.lam) ≃ᵢ Nat :=
  ArgTuple.singleIso (S := NFSignature) (Code := NFCode) Γ
    { binders := [.appTerm], sort := .normalExp }

def NFNormalFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .normalExp ≃ᵢ NFNormalCtorCarrier Γ :=
  CtorFamily.sumIso (S := NFSignature) (Code := NFCode) Γ
    NFCtor.dum NFCtor.lam rfl rfl
    (by intro h; cases h)
    (fun
      | NFCtor.dum => isTrue rfl
      | NFCtor.lam => isFalse (by intro h; cases h)
      | NFCtor.app => isFalse (by intro h; cases h))
    (by
      intro c h hne
      cases c with
      | dum => exact False.elim (hne rfl)
      | lam => rfl
      | app => cases h)
    (NFNormalDumArgsIso Γ)
    (NFNormalLamArgsIso Γ)

def NFAppArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.app) ≃ᵢ NFAppCtorCarrier Γ :=
  ArgTuple.pairIso (S := NFSignature) (Code := NFCode) Γ
    { binders := [], sort := .appTerm }
    { binders := [], sort := .normalExp }

def NFAppFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .appTerm ≃ᵢ NFAppCtorCarrier Γ :=
  CtorFamily.singleIso (S := NFSignature) (Code := NFCode) Γ
    NFCtor.app rfl
    (by
      intro c h
      cases c <;> cases h
      rfl)
    (NFAppArgsIso Γ)

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

def NFNormalGeneratedLayerIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .normalExp) ≃ᵢ
      NFCode (Γ, .normalExp) :=
  Iso.trans
    (LayerShape.layerCarrierCoding (S := NFSignature) (Code := NFCode)
      Γ .normalExp (Var.finIso Γ .normalExp) (NFNormalFamilyCarrierIso Γ))
    (Iso.trans
      (Iso.sum (Iso.refl (Fin (normalExpCount Γ)))
        (CodeAlgebra.finProdNatOrNat (appTermCount Γ)))
      (CodeAlgebra.finPlusNat (normalExpCount Γ)))

def NFAppGeneratedLayerIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm) ≃ᵢ
      NFCode (Γ, .appTerm) :=
  Iso.trans
    (LayerShape.layerCarrierCoding (S := NFSignature) (Code := NFCode)
      Γ .appTerm (Var.finIso Γ .appTerm) (NFAppFamilyCarrierIso Γ))
    (CodeAlgebra.finTaggedProdNat (appTermCount Γ))

def NFGeneratedLayerIso :
    ∀ Γ t, CodeLayer NFPoly NFInversion NFCode (Γ, t) ≃ᵢ NFCode (Γ, t)
  | Γ, .normalExp => NFNormalGeneratedLayerIso Γ
  | Γ, .appTerm => NFAppGeneratedLayerIso Γ

theorem NFGeneratedLayer_dum_child_rank_lt (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.dum) →
        NFCode ((NFSignature.arg NFCtor.dum q).binders ++ Γ,
          (NFSignature.arg NFCtor.dum q).sort)) :
    NFCodeRank (Γ, NFSort.appTerm) (child ⟨0, by decide⟩) <
      NFCodeRank (Γ, NFSort.normalExp)
        ((NFGeneratedLayerIso Γ NFSort.normalExp).toFun
          ⟨FiberCode.op NFCtor.dum rfl, child⟩) := by
  let app : Fin (appTermCount Γ) × Nat := child ⟨0, by decide⟩
  have hcount : 0 < appTermCount Γ :=
    Nat.lt_of_le_of_lt (Nat.zero_le app.1.val) app.1.isLt
  have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
  let tail :=
    (CodeAlgebra.finProdNatOrNat (appTermCount Γ)).toFun
      (Sum.inl app)
  have hparent :
      (NFGeneratedLayerIso Γ NFSort.normalExp).toFun
          ⟨FiberCode.op NFCtor.dum rfl, child⟩ =
        normalExpCount Γ + tail := by
    dsimp [NFGeneratedLayerIso, NFNormalGeneratedLayerIso, Iso.trans]
    rw [show
      (LayerShape.layerCarrierCoding (S := NFSignature)
          (Code := NFCode) Γ NFSort.normalExp
          (Var.finIso Γ NFSort.normalExp)
          (NFNormalFamilyCarrierIso Γ)).toFun
          ⟨FiberCode.op NFCtor.dum rfl, child⟩ = _ by
        simpa [NFSignature, NFRet] using
          (LayerShape.layerCarrierCoding_op_toFun
            (S := NFSignature) (Code := NFCode) (Γ := Γ)
            (c := NFCtor.dum)
            (varIso := Var.finIso Γ NFSort.normalExp)
            (ctorIso := NFNormalFamilyCarrierIso Γ)
            (child := child))]
    simp [app, tail, hcount, NFNormalFamilyCarrierIso,
      NFNormalDumArgsIso, NFNormalLamArgsIso,
      CtorFamily.sumIso, Iso.sum,
      CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
  rw [hparent]
  change NFCodeRank (Γ, NFSort.appTerm) app <
    NFCodeRank (Γ, NFSort.normalExp) (normalExpCount Γ + tail)
  simp [NFCodeRank, hcne]
  have happ_le : app.2 ≤ tail := by
    simpa [tail] using
      CodeAlgebra.finProdNatOrNat_inl_snd_le
        (appTermCount Γ) app
  omega

theorem NFGeneratedLayer_lam_child_rank_lt (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.lam) →
        NFCode ((NFSignature.arg NFCtor.lam q).binders ++ Γ,
          (NFSignature.arg NFCtor.lam q).sort)) :
    NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp)
        (child ⟨0, by decide⟩) <
      NFCodeRank (Γ, NFSort.normalExp)
        ((NFGeneratedLayerIso Γ NFSort.normalExp).toFun
          ⟨FiberCode.op NFCtor.lam rfl, child⟩) := by
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
        (NFGeneratedLayerIso Γ NFSort.normalExp).toFun
            ⟨FiberCode.op NFCtor.lam rfl, child⟩ =
          normalExpCount Γ + tail := by
      dsimp [NFGeneratedLayerIso, NFNormalGeneratedLayerIso, Iso.trans]
      rw [show
        (LayerShape.layerCarrierCoding (S := NFSignature)
            (Code := NFCode) Γ NFSort.normalExp
            (Var.finIso Γ NFSort.normalExp)
            (NFNormalFamilyCarrierIso Γ)).toFun
            ⟨FiberCode.op NFCtor.lam rfl, child⟩ = _ by
          simpa [NFSignature, NFRet] using
            (LayerShape.layerCarrierCoding_op_toFun
              (S := NFSignature) (Code := NFCode) (Γ := Γ)
              (c := NFCtor.lam)
              (varIso := Var.finIso Γ NFSort.normalExp)
              (ctorIso := NFNormalFamilyCarrierIso Γ)
              (child := child))]
      simp [body, tail, hc, NFNormalFamilyCarrierIso,
        NFNormalDumArgsIso, NFNormalLamArgsIso,
        CtorFamily.sumIso, Iso.sum,
        CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
    rw [hparent]
    change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
      NFCodeRank (Γ, NFSort.normalExp) (normalExpCount Γ + tail)
    simp [NFCodeRank, appTermCount, Var.count, hc]
    omega
  · have hpos : 0 < appTermCount Γ := Nat.pos_of_ne_zero hc
    have hbody_lt : body < tail := by
      simpa [tail] using
        CodeAlgebra.finProdNatOrNat_inr_lt_of_pos
          (k := appTermCount Γ) (n := body) hpos
    have hparent :
        (NFGeneratedLayerIso Γ NFSort.normalExp).toFun
            ⟨FiberCode.op NFCtor.lam rfl, child⟩ =
          normalExpCount Γ + tail := by
      dsimp [NFGeneratedLayerIso, NFNormalGeneratedLayerIso, Iso.trans]
      rw [show
        (LayerShape.layerCarrierCoding (S := NFSignature)
            (Code := NFCode) Γ NFSort.normalExp
            (Var.finIso Γ NFSort.normalExp)
            (NFNormalFamilyCarrierIso Γ)).toFun
            ⟨FiberCode.op NFCtor.lam rfl, child⟩ = _ by
          simpa [NFSignature, NFRet] using
            (LayerShape.layerCarrierCoding_op_toFun
              (S := NFSignature) (Code := NFCode) (Γ := Γ)
              (c := NFCtor.lam)
              (varIso := Var.finIso Γ NFSort.normalExp)
              (ctorIso := NFNormalFamilyCarrierIso Γ)
              (child := child))]
      simp [body, tail, hpos, NFNormalFamilyCarrierIso,
        NFNormalDumArgsIso, NFNormalLamArgsIso,
        CtorFamily.sumIso, Iso.sum,
        CodeAlgebra.finPlusNat, CodeAlgebra.finProdNatOrNat]
    rw [hparent]
    change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
      NFCodeRank (Γ, NFSort.normalExp) (normalExpCount Γ + tail)
    simp [NFCodeRank, appTermCount, Var.count, hc]
    omega

theorem NFGeneratedLayer_app_fn_child_rank_lt (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.app) →
        NFCode ((NFSignature.arg NFCtor.app q).binders ++ Γ,
          (NFSignature.arg NFCtor.app q).sort)) :
    NFCodeRank (Γ, NFSort.appTerm) (child ⟨0, by decide⟩) <
      NFCodeRank (Γ, NFSort.appTerm)
        ((NFGeneratedLayerIso Γ NFSort.appTerm).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩) := by
  let fn : Fin (appTermCount Γ) × Nat := child ⟨0, by decide⟩
  let arg : Nat := child ⟨1, by decide⟩
  let pair := (fn, arg)
  have hparent :
      (NFGeneratedLayerIso Γ NFSort.appTerm).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩ =
        (CodeAlgebra.finTaggedProdNat (appTermCount Γ)).toFun
          (Sum.inr pair) := by
    dsimp [NFGeneratedLayerIso, NFAppGeneratedLayerIso, Iso.trans]
    rw [show
      (LayerShape.layerCarrierCoding (S := NFSignature)
          (Code := NFCode) Γ NFSort.appTerm
          (Var.finIso Γ NFSort.appTerm)
          (NFAppFamilyCarrierIso Γ)).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩ = _ by
        simpa [NFSignature, NFRet] using
          (LayerShape.layerCarrierCoding_op_toFun
            (S := NFSignature) (Code := NFCode) (Γ := Γ)
            (c := NFCtor.app)
            (varIso := Var.finIso Γ NFSort.appTerm)
            (ctorIso := NFAppFamilyCarrierIso Γ)
            (child := child))]
    simp [fn, arg, pair, NFAppFamilyCarrierIso,
      NFAppArgsIso, CtorFamily.singleIso]
  rw [hparent]
  change NFCodeRank (Γ, NFSort.appTerm) fn <
    NFCodeRank (Γ, NFSort.appTerm)
      ((CodeAlgebra.finTaggedProdNat (appTermCount Γ)).toFun (Sum.inr pair))
  simp [NFCodeRank]
  have hfn_lt :
      fn.2 <
        ((CodeAlgebra.finTaggedProdNat
          (appTermCount Γ)).toFun (Sum.inr pair)).2 := by
    simpa [pair] using
      CodeAlgebra.finTaggedProdNat_inr_fst_payload_lt
        (appTermCount Γ) pair
  omega

theorem NFGeneratedLayer_app_arg_child_rank_lt (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.app) →
        NFCode ((NFSignature.arg NFCtor.app q).binders ++ Γ,
          (NFSignature.arg NFCtor.app q).sort)) :
    NFCodeRank (Γ, NFSort.normalExp) (child ⟨1, by decide⟩) <
      NFCodeRank (Γ, NFSort.appTerm)
        ((NFGeneratedLayerIso Γ NFSort.appTerm).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩) := by
  let fn : Fin (appTermCount Γ) × Nat := child ⟨0, by decide⟩
  let arg : Nat := child ⟨1, by decide⟩
  have hcount : 0 < appTermCount Γ :=
    Nat.lt_of_le_of_lt (Nat.zero_le fn.1.val) fn.1.isLt
  have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
  let pair := (fn, arg)
  have hparent :
      (NFGeneratedLayerIso Γ NFSort.appTerm).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩ =
        (CodeAlgebra.finTaggedProdNat (appTermCount Γ)).toFun
          (Sum.inr pair) := by
    dsimp [NFGeneratedLayerIso, NFAppGeneratedLayerIso, Iso.trans]
    rw [show
      (LayerShape.layerCarrierCoding (S := NFSignature)
          (Code := NFCode) Γ NFSort.appTerm
          (Var.finIso Γ NFSort.appTerm)
          (NFAppFamilyCarrierIso Γ)).toFun
          ⟨FiberCode.op NFCtor.app rfl, child⟩ = _ by
        simpa [NFSignature, NFRet] using
          (LayerShape.layerCarrierCoding_op_toFun
            (S := NFSignature) (Code := NFCode) (Γ := Γ)
            (c := NFCtor.app)
            (varIso := Var.finIso Γ NFSort.appTerm)
            (ctorIso := NFAppFamilyCarrierIso Γ)
            (child := child))]
    simp [fn, arg, pair, NFAppFamilyCarrierIso,
      NFAppArgsIso, CtorFamily.singleIso]
  rw [hparent]
  change NFCodeRank (Γ, NFSort.normalExp) arg <
    NFCodeRank (Γ, NFSort.appTerm)
      ((CodeAlgebra.finTaggedProdNat (appTermCount Γ)).toFun (Sum.inr pair))
  simp [NFCodeRank, hcne]
  have harg_lt :
      arg <
        ((CodeAlgebra.finTaggedProdNat
          (appTermCount Γ)).toFun (Sum.inr pair)).2 := by
    simpa [pair] using
      CodeAlgebra.finTaggedProdNat_inr_snd_lt
        (appTermCount Γ) pair
  omega

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
                      simpa [NFSignature, NFArgs] using
                        NFGeneratedLayer_dum_child_rank_lt Γ child
                  | succ q => exact fin_zero_elim q
              | lam =>
                  cases h
                  intro q
                  cases q using Fin.cases with
                  | zero =>
                      simpa [NFSignature, NFArgs] using
                        NFGeneratedLayer_lam_child_rank_lt Γ child
                  | succ q => exact fin_zero_elim q
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
                  cases q using Fin.cases with
                  | zero =>
                      simpa [NFSignature, NFArgs] using
                        NFGeneratedLayer_app_fn_child_rank_lt Γ child
                  | succ q =>
                      cases q using Fin.cases with
                      | zero =>
                          simpa [NFSignature, NFArgs] using
                            NFGeneratedLayer_app_arg_child_rank_lt Γ child
                      | succ q => exact fin_zero_elim q

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

def ClosedAppTermEmptyIso : AppTerm [] ≃ᵢ Empty :=
  Iso.trans (AppTermCodeIso []) (fin_zero_prod_empty_iso Nat)

end TypedBinding
end Examples
end BijForm
