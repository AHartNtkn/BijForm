import BijForm.TypedBinding

namespace BijForm
namespace Examples
namespace TypedBinding

open DepPoly
open BijForm.TypedBinding
open BijForm.TypedBinding.LayerShape

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

def NFNormalCtorCases : List (CtorFamily.Case NFSignature .normalExp) :=
  [⟨NFCtor.dum, rfl⟩, ⟨NFCtor.lam, rfl⟩]

def NFAppCtorCases : List (CtorFamily.Case NFSignature .appTerm) :=
  [⟨NFCtor.app, rfl⟩]

def NFNormalCtorIndex (c : NFCtor) (h : NFRet c = .normalExp) :
    Fin NFNormalCtorCases.length :=
  match c with
  | .dum => ⟨0, by decide⟩
  | .lam => ⟨1, by decide⟩
  | .app => by cases h

theorem NFNormalCtorIndex_spec (c : NFCtor) (h : NFRet c = .normalExp) :
    (NFNormalCtorCases.get (NFNormalCtorIndex c h)).ctor = c := by
  cases c with
  | dum => rfl
  | lam => rfl
  | app => cases h

theorem NFNormalCtorIndex_get (q : Fin NFNormalCtorCases.length) :
    NFNormalCtorIndex (NFNormalCtorCases.get q).ctor
      (NFNormalCtorCases.get q).ret_eq = q := by
  cases q with
  | mk n hn =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              exact False.elim (by
                simp [NFNormalCtorCases] at hn
                omega)

def NFAppCtorIndex (c : NFCtor) (h : NFRet c = .appTerm) :
    Fin NFAppCtorCases.length :=
  match c with
  | .dum => by cases h
  | .lam => by cases h
  | .app => ⟨0, by decide⟩

theorem NFAppCtorIndex_spec (c : NFCtor) (h : NFRet c = .appTerm) :
    (NFAppCtorCases.get (NFAppCtorIndex c h)).ctor = c := by
  cases c with
  | dum => cases h
  | lam => cases h
  | app => rfl

theorem NFAppCtorIndex_get (q : Fin NFAppCtorCases.length) :
    NFAppCtorIndex (NFAppCtorCases.get q).ctor
      (NFAppCtorCases.get q).ret_eq = q := by
  cases q with
  | mk n hn =>
      cases n with
      | zero => rfl
      | succ n =>
          exact False.elim (by
            simp [NFAppCtorCases] at hn)

def NFNormalDumArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.dum) ≃ᵢ
      NFCode (Γ, .appTerm) :=
  { toFun := fun args =>
      ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.dum) args ⟨0, by decide⟩
    invFun := fun z =>
      ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.dum) (fun
          | ⟨0, _⟩ => z
          | ⟨n + 1, h⟩ => by
              simp [NFArgs] at h)
    left_inv := by
      intro args
      simpa [NFArgs] using
        (ArgTuple.ofChild_toChild (S := NFSignature) (Code := NFCode) Γ
          (args := NFArgs NFCtor.dum) args)
    right_inv := by
      intro z
      rfl }

def NFNormalLamArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.lam) ≃ᵢ Nat :=
  { toFun := fun args =>
      ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.lam) args ⟨0, by decide⟩
    invFun := fun z =>
      ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.lam) (fun
          | ⟨0, _⟩ => z
          | ⟨n + 1, h⟩ => by
              simp [NFArgs] at h)
    left_inv := by
      intro args
      simpa [NFArgs] using
        (ArgTuple.ofChild_toChild (S := NFSignature) (Code := NFCode) Γ
          (args := NFArgs NFCtor.lam) args)
    right_inv := by
      intro z
      rfl }

def NFNormalCaseCarrierIso (Γ : List NFSort) :
    CtorFamily.CaseCarrier (S := NFSignature) (Code := NFCode)
      Γ NFNormalCtorCases ≃ᵢ NFNormalCtorCarrier Γ where
  toFun
    | ⟨⟨0, _⟩, args⟩ => Sum.inl ((NFNormalDumArgsIso Γ).toFun args)
    | ⟨⟨1, _⟩, args⟩ => Sum.inr ((NFNormalLamArgsIso Γ).toFun args)
    | ⟨⟨n + 2, hn⟩, _args⟩ => False.elim (by
        simp [NFNormalCtorCases] at hn
        omega)
  invFun
    | Sum.inl z => ⟨⟨0, by decide⟩, (NFNormalDumArgsIso Γ).invFun z⟩
    | Sum.inr z => ⟨⟨1, by decide⟩, (NFNormalLamArgsIso Γ).invFun z⟩
  left_inv := by
    intro entry
    cases entry with
    | mk q args =>
        cases q with
        | mk n hn =>
            cases n with
            | zero =>
                exact Sigma.ext rfl (heq_of_eq ((NFNormalDumArgsIso Γ).left_inv args))
            | succ n =>
                cases n with
                | zero =>
                    exact Sigma.ext rfl (heq_of_eq ((NFNormalLamArgsIso Γ).left_inv args))
                | succ n =>
                    exact False.elim (by
                      simp [NFNormalCtorCases] at hn
                      omega)
  right_inv := by
    intro z
    cases z with
    | inl z => exact congrArg Sum.inl ((NFNormalDumArgsIso Γ).right_inv z)
    | inr z => exact congrArg Sum.inr ((NFNormalLamArgsIso Γ).right_inv z)

def NFNormalFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .normalExp ≃ᵢ NFNormalCtorCarrier Γ where
  toFun family := by
    cases family with
    | mk c h args =>
        cases c with
        | dum => exact Sum.inl ((NFNormalDumArgsIso Γ).toFun args)
        | lam => exact Sum.inr ((NFNormalLamArgsIso Γ).toFun args)
        | app => cases h
  invFun
    | Sum.inl z => ⟨NFCtor.dum, rfl, (NFNormalDumArgsIso Γ).invFun z⟩
    | Sum.inr z => ⟨NFCtor.lam, rfl, (NFNormalLamArgsIso Γ).invFun z⟩
  left_inv := by
    intro family
    cases family with
    | mk c h args =>
        cases c with
        | dum =>
            cases h
            dsimp
            rw [(NFNormalDumArgsIso Γ).left_inv args]
        | lam =>
            cases h
            dsimp
            rw [(NFNormalLamArgsIso Γ).left_inv args]
        | app => cases h
  right_inv := by
    intro z
    cases z with
    | inl z =>
        dsimp
        exact congrArg Sum.inl ((NFNormalDumArgsIso Γ).right_inv z)
    | inr z =>
        dsimp
        exact congrArg Sum.inr ((NFNormalLamArgsIso Γ).right_inv z)

def NFAppArgsIso (Γ : List NFSort) :
    ArgTuple NFSignature NFCode Γ (NFArgs NFCtor.app) ≃ᵢ NFAppCtorCarrier Γ :=
  { toFun := fun args =>
      (ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.app) args ⟨0, by decide⟩,
       ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.app) args ⟨1, by decide⟩)
    invFun := fun pair =>
      ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
        (args := NFArgs NFCtor.app) (fun
          | ⟨0, _⟩ => pair.1
          | ⟨1, _⟩ => pair.2
          | ⟨n + 2, h⟩ => by
              simp [NFArgs] at h
              omega)
    left_inv := by
      intro args
      simpa [NFArgs] using
        (ArgTuple.ofChild_toChild (S := NFSignature) (Code := NFCode) Γ
          (args := NFArgs NFCtor.app) args)
    right_inv := by
      intro pair
      cases pair
      rfl }

def NFAppCaseCarrierIso (Γ : List NFSort) :
    CtorFamily.CaseCarrier (S := NFSignature) (Code := NFCode)
      Γ NFAppCtorCases ≃ᵢ NFAppCtorCarrier Γ where
  toFun
    | ⟨⟨0, _⟩, args⟩ => (NFAppArgsIso Γ).toFun args
    | ⟨⟨n + 1, hn⟩, _args⟩ => False.elim (by
        simp [NFAppCtorCases] at hn)
  invFun z := ⟨⟨0, by decide⟩, (NFAppArgsIso Γ).invFun z⟩
  left_inv := by
    intro entry
    cases entry with
    | mk q args =>
        cases q with
        | mk n hn =>
            cases n with
            | zero =>
                exact Sigma.ext rfl (heq_of_eq ((NFAppArgsIso Γ).left_inv args))
            | succ n =>
                exact False.elim (by
                  simp [NFAppCtorCases] at hn)
  right_inv := by
    intro z
    exact (NFAppArgsIso Γ).right_inv z

def NFAppFamilyCarrierIso (Γ : List NFSort) :
    CtorFamily NFSignature NFCode Γ .appTerm ≃ᵢ NFAppCtorCarrier Γ where
  toFun family := by
    cases family with
    | mk c h args =>
        cases c with
        | dum => cases h
        | lam => cases h
        | app => exact (NFAppArgsIso Γ).toFun args
  invFun z := ⟨NFCtor.app, rfl, (NFAppArgsIso Γ).invFun z⟩
  left_inv := by
    intro family
    cases family with
    | mk c h args =>
        cases c with
        | dum => cases h
        | lam => cases h
        | app =>
            cases h
            dsimp
            rw [(NFAppArgsIso Γ).left_inv args]
  right_inv := by
    intro z
    exact (NFAppArgsIso Γ).right_inv z

@[simp]
theorem NFNormalFamilyCarrierIso_dum_toFun (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.dum) →
        NFCode ((NFSignature.arg NFCtor.dum q).binders ++ Γ,
          (NFSignature.arg NFCtor.dum q).sort)) :
    (NFNormalFamilyCarrierIso Γ).toFun
        ⟨NFCtor.dum, rfl,
          ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
            (args := NFArgs NFCtor.dum) child⟩ =
      Sum.inl (child ⟨0, by decide⟩) := by
  simp [NFNormalFamilyCarrierIso, NFNormalDumArgsIso]

@[simp]
theorem NFNormalFamilyCarrierIso_lam_toFun (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.lam) →
        NFCode ((NFSignature.arg NFCtor.lam q).binders ++ Γ,
          (NFSignature.arg NFCtor.lam q).sort)) :
    (NFNormalFamilyCarrierIso Γ).toFun
        ⟨NFCtor.lam, rfl,
          ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
            (args := NFArgs NFCtor.lam) child⟩ =
      Sum.inr (child ⟨0, by decide⟩) := by
  simp [NFNormalFamilyCarrierIso, NFNormalLamArgsIso]

@[simp]
theorem NFAppFamilyCarrierIso_app_toFun (Γ : List NFSort)
    (child :
      (q : NFSignature.ArgPos NFCtor.app) →
        NFCode ((NFSignature.arg NFCtor.app q).binders ++ Γ,
          (NFSignature.arg NFCtor.app q).sort)) :
    (NFAppFamilyCarrierIso Γ).toFun
        ⟨NFCtor.app, rfl,
          ArgTuple.ofChild (S := NFSignature) (Code := NFCode) Γ
            (args := NFArgs NFCtor.app) child⟩ =
      (child ⟨0, by decide⟩, child ⟨1, by decide⟩) := by
  simp [NFAppFamilyCarrierIso, NFAppArgsIso]

def NFNormalGeneratedShapeIso (Γ : List NFSort) :
    LayerShape NFSignature NFCode Γ .normalExp ≃ᵢ NFCode (Γ, .normalExp) :=
  Iso.trans
    (LayerShape.carrierCoding (S := NFSignature) (Code := NFCode)
      Γ .normalExp (Var.finIso Γ .normalExp) (NFNormalFamilyCarrierIso Γ))
    (Iso.trans
      (Iso.sum (Iso.refl (Fin (normalExpCount Γ)))
        (CodeAlgebra.optionalFinitePayloadNat (appTermCount Γ)))
      (CodeAlgebra.finPlusNat (normalExpCount Γ)))

def NFAppGeneratedShapeIso (Γ : List NFSort) :
    LayerShape NFSignature NFCode Γ .appTerm ≃ᵢ NFCode (Γ, .appTerm) :=
  Iso.trans
    (LayerShape.carrierCoding (S := NFSignature) (Code := NFCode)
      Γ .appTerm (Var.finIso Γ .appTerm) (NFAppFamilyCarrierIso Γ))
    (CodeAlgebra.taggedPairPayload (appTermCount Γ))

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
        (CodeAlgebra.optionalFinitePayloadNat (appTermCount Γ)))
      (CodeAlgebra.finPlusNat (normalExpCount Γ)))

def NFAppGeneratedLayerIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm) ≃ᵢ
      NFCode (Γ, .appTerm) :=
  Iso.trans
    (LayerShape.layerCarrierCoding (S := NFSignature) (Code := NFCode)
      Γ .appTerm (Var.finIso Γ .appTerm) (NFAppFamilyCarrierIso Γ))
    (CodeAlgebra.taggedPairPayload (appTermCount Γ))

def NFGeneratedLayerIso :
    ∀ Γ t, CodeLayer NFPoly NFInversion NFCode (Γ, t) ≃ᵢ NFCode (Γ, t)
  | Γ, .normalExp => NFNormalGeneratedLayerIso Γ
  | Γ, .appTerm => NFAppGeneratedLayerIso Γ

theorem NFCtorFamilyRankBound :
    LayerShapeRankProof.CtorFamilyRankBound
      (S := NFSignature) (Code := NFCode)
      (layerShape := NFGeneratedShapeIso) (rank := NFCodeRank) := by
  intro Γ t family q
  cases family with
  | mk c h args =>
      cases c with
      | dum =>
          cases h
          cases q with
          | mk n hn =>
              cases n with
              | zero =>
                  let app : Fin (appTermCount Γ) × Nat :=
                    ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                      args ⟨0, hn⟩
                  have hcount : 0 < appTermCount Γ :=
                    Nat.lt_of_le_of_lt (Nat.zero_le app.1.val) app.1.isLt
                  have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
                  let tail :=
                    (CodeAlgebra.optionalFinitePayloadNat
                      (appTermCount Γ)).toFun (Sum.inl app)
                  change NFCodeRank (Γ, NFSort.appTerm) app <
                    NFCodeRank (Γ, NFSort.normalExp)
                      ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                        (Sum.inr
                          (CtorLayer.ofFamily
                            (S := NFSignature) (Code := NFCode)
                            Γ NFSort.normalExp
                            (⟨NFCtor.dum, rfl, args⟩ :
                              CtorFamily NFSignature NFCode Γ
                                NFSort.normalExp))))
                  rw [show
                    (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                        (Sum.inr
                          (CtorLayer.ofFamily
                            (S := NFSignature) (Code := NFCode)
                            Γ NFSort.normalExp
                            (⟨NFCtor.dum, rfl, args⟩ :
                              CtorFamily NFSignature NFCode Γ
                                NFSort.normalExp))) =
                      normalExpCount Γ + tail by
                    simp [NFGeneratedShapeIso, NFNormalGeneratedShapeIso,
                      LayerShape.carrierCoding, LayerShape.familyIso,
                      CtorLayer.ofFamily, CtorLayer.toFamily,
                      CtorLayer.familyIso, ArgTuple.ofChild_toChild,
                      NFNormalFamilyCarrierIso, NFNormalDumArgsIso, app, tail,
                      Iso.trans, Iso.sum, CodeAlgebra.finPlusNat]]
                  change NFCodeRank (Γ, NFSort.appTerm) app <
                    NFCodeRank (Γ, NFSort.normalExp)
                      (normalExpCount Γ + tail)
                  simp [NFCodeRank, hcne]
                  have happ_le : app.2 ≤ tail := by
                    simpa [tail] using
                      CodeAlgebra.optionalFinitePayloadNat_left_payload_le
                        (appTermCount Γ) app
                  omega
              | succ n =>
                  exact False.elim (by
                    simp [NFSignature, NFArgs] at hn)
      | lam =>
          cases h
          cases q with
          | mk n hn =>
              cases n with
              | zero =>
                  let body : Nat :=
                    ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                      args ⟨0, hn⟩
                  let tail :=
                    (CodeAlgebra.optionalFinitePayloadNat
                      (appTermCount Γ)).toFun (Sum.inr body)
                  have hbody_le : body ≤ tail := by
                    simpa [tail] using
                      CodeAlgebra.optionalFinitePayloadNat_right_payload_le
                        (appTermCount Γ) body
                  by_cases hc : appTermCount Γ = 0
                  · change NFCodeRank
                        (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                      NFCodeRank (Γ, NFSort.normalExp)
                        ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                          (Sum.inr
                            (CtorLayer.ofFamily
                              (S := NFSignature) (Code := NFCode)
                              Γ NFSort.normalExp
                              (⟨NFCtor.lam, rfl, args⟩ :
                                CtorFamily NFSignature NFCode Γ
                                  NFSort.normalExp))))
                    rw [show
                      (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                          (Sum.inr
                            (CtorLayer.ofFamily
                              (S := NFSignature) (Code := NFCode)
                              Γ NFSort.normalExp
                              (⟨NFCtor.lam, rfl, args⟩ :
                                CtorFamily NFSignature NFCode Γ
                                  NFSort.normalExp))) =
                        normalExpCount Γ + tail by
                      simp [NFGeneratedShapeIso, NFNormalGeneratedShapeIso,
                        LayerShape.carrierCoding, LayerShape.familyIso,
                        CtorLayer.ofFamily, CtorLayer.toFamily,
                        CtorLayer.familyIso, ArgTuple.ofChild_toChild,
                        NFNormalFamilyCarrierIso, NFNormalLamArgsIso, body, tail,
                        Iso.trans, Iso.sum, CodeAlgebra.finPlusNat]]
                    change NFCodeRank
                        (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                      NFCodeRank (Γ, NFSort.normalExp)
                        (normalExpCount Γ + tail)
                    simp [NFCodeRank, appTermCount, Var.count, hc]
                    omega
                  · have hpos : 0 < appTermCount Γ := Nat.pos_of_ne_zero hc
                    have hbody_lt : body < tail := by
                      simpa [tail] using
                        CodeAlgebra.optionalFinitePayloadNat_right_payload_lt_of_pos
                          (k := appTermCount Γ) (n := body) hpos
                    change NFCodeRank
                        (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                      NFCodeRank (Γ, NFSort.normalExp)
                        ((NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                          (Sum.inr
                            (CtorLayer.ofFamily
                              (S := NFSignature) (Code := NFCode)
                              Γ NFSort.normalExp
                              (⟨NFCtor.lam, rfl, args⟩ :
                                CtorFamily NFSignature NFCode Γ
                                  NFSort.normalExp))))
                    rw [show
                      (NFGeneratedShapeIso Γ NFSort.normalExp).toFun
                          (Sum.inr
                            (CtorLayer.ofFamily
                              (S := NFSignature) (Code := NFCode)
                              Γ NFSort.normalExp
                              (⟨NFCtor.lam, rfl, args⟩ :
                                CtorFamily NFSignature NFCode Γ
                                  NFSort.normalExp))) =
                        normalExpCount Γ + tail by
                      simp [NFGeneratedShapeIso, NFNormalGeneratedShapeIso,
                        LayerShape.carrierCoding, LayerShape.familyIso,
                        CtorLayer.ofFamily, CtorLayer.toFamily,
                        CtorLayer.familyIso, ArgTuple.ofChild_toChild,
                        NFNormalFamilyCarrierIso, NFNormalLamArgsIso, body, tail,
                        Iso.trans, Iso.sum, CodeAlgebra.finPlusNat]]
                    change NFCodeRank
                        (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                      NFCodeRank (Γ, NFSort.normalExp)
                        (normalExpCount Γ + tail)
                    simp [NFCodeRank, appTermCount, Var.count, hc]
                    omega
              | succ n =>
                  exact False.elim (by
                    simp [NFSignature, NFArgs] at hn)
      | app =>
          cases h
          cases q with
          | mk n hn =>
              cases n with
              | zero =>
                  let fn : Fin (appTermCount Γ) × Nat :=
                    ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                      args ⟨0, hn⟩
                  let arg : Nat :=
                    ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                      args ⟨1, by decide⟩
                  let pair := (fn, arg)
                  change NFCodeRank (Γ, NFSort.appTerm) fn <
                    NFCodeRank (Γ, NFSort.appTerm)
                      ((NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                        (Sum.inr
                          (CtorLayer.ofFamily
                            (S := NFSignature) (Code := NFCode)
                            Γ NFSort.appTerm
                            (⟨NFCtor.app, rfl, args⟩ :
                              CtorFamily NFSignature NFCode Γ
                                NFSort.appTerm))))
                  rw [show
                    (NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                        (Sum.inr
                          (CtorLayer.ofFamily
                            (S := NFSignature) (Code := NFCode)
                            Γ NFSort.appTerm
                            (⟨NFCtor.app, rfl, args⟩ :
                              CtorFamily NFSignature NFCode Γ
                                NFSort.appTerm))) =
                      (CodeAlgebra.taggedPairPayload
                        (appTermCount Γ)).toFun (Sum.inr pair) by
                    simp [NFGeneratedShapeIso, NFAppGeneratedShapeIso,
                      LayerShape.carrierCoding, LayerShape.familyIso,
                      CtorLayer.ofFamily, CtorLayer.toFamily,
                      CtorLayer.familyIso, ArgTuple.ofChild_toChild,
                      NFAppFamilyCarrierIso, NFAppArgsIso, fn, arg, pair,
                      Iso.trans, Iso.sum]]
                  change NFCodeRank (Γ, NFSort.appTerm) fn <
                    NFCodeRank (Γ, NFSort.appTerm)
                      ((CodeAlgebra.taggedPairPayload
                        (appTermCount Γ)).toFun (Sum.inr pair))
                  simp [NFCodeRank]
                  have hfn_lt :
                      fn.2 <
                        ((CodeAlgebra.taggedPairPayload
                          (appTermCount Γ)).toFun (Sum.inr pair)).2 :=
                    CodeAlgebra.taggedPairPayload_left_payload_lt
                      (appTermCount Γ) pair
                  omega
              | succ n =>
                  cases n with
                  | zero =>
                      let fn : Fin (appTermCount Γ) × Nat :=
                        ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                          args ⟨0, by decide⟩
                      let arg : Nat :=
                        ArgTuple.toChild (S := NFSignature) (Code := NFCode) Γ
                          args ⟨0 + 1, hn⟩
                      have hcount : 0 < appTermCount Γ :=
                        Nat.lt_of_le_of_lt (Nat.zero_le fn.1.val) fn.1.isLt
                      have hcne : ¬appTermCount Γ = 0 := Nat.ne_of_gt hcount
                      let pair := (fn, arg)
                      change NFCodeRank (Γ, NFSort.normalExp) arg <
                        NFCodeRank (Γ, NFSort.appTerm)
                          ((NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                            (Sum.inr
                              (CtorLayer.ofFamily
                                (S := NFSignature) (Code := NFCode)
                                Γ NFSort.appTerm
                                (⟨NFCtor.app, rfl, args⟩ :
                                  CtorFamily NFSignature NFCode Γ
                                    NFSort.appTerm))))
                      rw [show
                        (NFGeneratedShapeIso Γ NFSort.appTerm).toFun
                            (Sum.inr
                              (CtorLayer.ofFamily
                                (S := NFSignature) (Code := NFCode)
                                Γ NFSort.appTerm
                                (⟨NFCtor.app, rfl, args⟩ :
                                  CtorFamily NFSignature NFCode Γ
                                    NFSort.appTerm))) =
                          (CodeAlgebra.taggedPairPayload
                            (appTermCount Γ)).toFun (Sum.inr pair) by
                        simp [NFGeneratedShapeIso, NFAppGeneratedShapeIso,
                          LayerShape.carrierCoding, LayerShape.familyIso,
                          CtorLayer.ofFamily, CtorLayer.toFamily,
                          CtorLayer.familyIso, ArgTuple.ofChild_toChild,
                          NFAppFamilyCarrierIso, NFAppArgsIso, fn, arg, pair,
                          Iso.trans, Iso.sum]]
                      change NFCodeRank (Γ, NFSort.normalExp) arg <
                        NFCodeRank (Γ, NFSort.appTerm)
                          ((CodeAlgebra.taggedPairPayload
                            (appTermCount Γ)).toFun (Sum.inr pair))
                      simp [NFCodeRank, hcne]
                      have harg_lt :
                          arg <
                            ((CodeAlgebra.taggedPairPayload
                              (appTermCount Γ)).toFun (Sum.inr pair)).2 :=
                        CodeAlgebra.taggedPairPayload_right_payload_lt
                          (appTermCount Γ) pair
                      omega
                  | succ n =>
                      exact False.elim (by
                        simp [NFSignature, NFArgs] at hn
                        omega)

def NFLayerShapeCodingData : LayerShapeCodingData NFSignature where
  Code := NFCode
  layerShape := NFGeneratedShapeIso
  rank := NFCodeRank
  shape_child_rank_lt :=
    LayerShapeRankProof.ofCtorFamilyRankBound
      (S := NFSignature) (Code := NFCode)
      (layerShape := NFGeneratedShapeIso) (rank := NFCodeRank)
      NFCtorFamilyRankBound

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
