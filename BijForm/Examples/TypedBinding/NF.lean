import BijForm.Examples.TypedBinding

namespace BijForm
namespace Examples
namespace TypedBinding

open DepPoly

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

namespace NFSort

def isAppTerm : NFSort → Bool
  | .normalExp => false
  | .appTerm => true

end NFSort

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

abbrev appTermVarToFin {Γ : List NFSort} :
    Var Γ .appTerm → Fin (appTermCount Γ) :=
  Var.toFin

abbrev appTermFinToVar {Γ : List NFSort} :
    Fin (appTermCount Γ) → Var Γ .appTerm :=
  Var.ofFin NFSort.appTerm

theorem appTermFinToVar_toFin {Γ : List NFSort} (i : Fin (appTermCount Γ)) :
    appTermVarToFin (appTermFinToVar i) = i :=
  Var.ofFin_toFin NFSort.appTerm i

theorem appTermVarToFin_toVar {Γ : List NFSort} (v : Var Γ .appTerm) :
    appTermFinToVar (appTermVarToFin v) = v :=
  Var.toFin_ofFin v

abbrev normalExpVarToFin {Γ : List NFSort} :
    Var Γ .normalExp → Fin (normalExpCount Γ) :=
  Var.toFin

abbrev normalExpFinToVar {Γ : List NFSort} :
    Fin (normalExpCount Γ) → Var Γ .normalExp :=
  Var.ofFin NFSort.normalExp

theorem normalExpFinToVar_toFin {Γ : List NFSort} (i : Fin (normalExpCount Γ)) :
    normalExpVarToFin (normalExpFinToVar i) = i :=
  Var.ofFin_toFin NFSort.normalExp i

theorem normalExpVarToFin_toVar {Γ : List NFSort} (v : Var Γ .normalExp) :
    normalExpFinToVar (normalExpVarToFin v) = v :=
  Var.toFin_ofFin v

def NFCode : Poly.Ix NFSignature → Type
  | (_, .normalExp) => Nat
  | (Γ, .appTerm) => Fin (appTermCount Γ) × Nat

abbrev NFNormalLayerShape (Γ : List NFSort) : Type :=
  Fin (normalExpCount Γ) ⊕ (NFCode (Γ, .appTerm) ⊕ Nat)

abbrev NFAppTermLayerShape (Γ : List NFSort) : Type :=
  Fin (appTermCount Γ) ⊕ (NFCode (Γ, .appTerm) × Nat)

def NFCodeRank : ∀ i, NFCode i → Nat
  | (Γ, .normalExp), n => by
      change Nat at n
      exact if appTermCount Γ = 0 then 2 * n + 2 else 2 * n + 1
  | (_, .appTerm), p => 2 * p.2

def NFNormalLayerToShape (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .normalExp) → NFNormalLayerShape Γ
  | ⟨.var v, _child⟩ => Sum.inl (normalExpVarToFin v)
  | ⟨.op .dum h, child⟩ => by
      cases h
      exact Sum.inr (Sum.inl (child ⟨0, by decide⟩))
  | ⟨.op .lam h, child⟩ => by
      cases h
      exact Sum.inr (Sum.inr (child ⟨0, by decide⟩))
  | ⟨.op .app h, _child⟩ => by
      cases h

def NFNormalLayerOfShape (Γ : List NFSort) :
    NFNormalLayerShape Γ → CodeLayer NFPoly NFInversion NFCode (Γ, .normalExp)
  | Sum.inl v => ⟨.var (normalExpFinToVar v), fun q => nomatch q⟩
  | Sum.inr (Sum.inl e) =>
      ⟨.op NFCtor.dum rfl, fun
        | ⟨0, _⟩ => e
        | ⟨n + 1, h⟩ => by
            simp [NFSignature, NFArgs] at h⟩
  | Sum.inr (Sum.inr body) =>
      ⟨.op NFCtor.lam rfl, fun
        | ⟨0, _⟩ => body
        | ⟨n + 1, h⟩ => by
            simp [NFSignature, NFArgs] at h⟩

theorem NFNormalLayerShape_left_inv (Γ : List NFSort) :
    Function.LeftInverse (NFNormalLayerOfShape Γ) (NFNormalLayerToShape Γ) := by
  intro layer
  cases layer with
  | mk code child =>
      cases code with
      | var v =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          change NFNormalLayerOfShape Γ (Sum.inl (normalExpVarToFin v)) =
            ⟨FiberCode.var v, (fun q => nomatch q)⟩
          dsimp [NFNormalLayerOfShape]
          rw [normalExpVarToFin_toVar v]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | op c h =>
          cases c with
          | dum =>
              cases h
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              funext q
              cases q using Fin.cases with
              | zero => rfl
              | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)
          | lam =>
              cases h
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              funext q
              cases q using Fin.cases with
              | zero => rfl
              | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)
          | app =>
              cases h

theorem NFNormalLayerShape_right_inv (Γ : List NFSort) :
    Function.RightInverse (NFNormalLayerOfShape Γ) (NFNormalLayerToShape Γ) := by
  intro shape
  cases shape with
  | inl v =>
      simp [NFNormalLayerToShape, NFNormalLayerOfShape, normalExpFinToVar_toFin]
  | inr rest =>
      cases rest with
      | inl e => rfl
      | inr body => rfl

def NFNormalLayerShapeIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .normalExp) ≃ᵢ NFNormalLayerShape Γ where
  toFun := NFNormalLayerToShape Γ
  invFun := NFNormalLayerOfShape Γ
  left_inv := NFNormalLayerShape_left_inv Γ
  right_inv := NFNormalLayerShape_right_inv Γ

def NFAppTermLayerToShape (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm) → NFAppTermLayerShape Γ
  | ⟨.var v, _child⟩ => Sum.inl (appTermVarToFin v)
  | ⟨.op .app h, child⟩ => by
      cases h
      exact Sum.inr (child ⟨0, by decide⟩, child ⟨1, by decide⟩)
  | ⟨.op .dum h, _child⟩ => by
      cases h
  | ⟨.op .lam h, _child⟩ => by
      cases h

def NFAppTermLayerOfShape (Γ : List NFSort) :
    NFAppTermLayerShape Γ → CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm)
  | Sum.inl v => ⟨.var (appTermFinToVar v), fun q => nomatch q⟩
  | Sum.inr pair =>
      ⟨.op NFCtor.app rfl, fun
        | ⟨0, _⟩ => pair.1
        | ⟨1, _⟩ => pair.2
        | ⟨n + 2, h⟩ => by
            simp [NFSignature, NFArgs] at h
            omega⟩

theorem NFAppTermLayerShape_left_inv (Γ : List NFSort) :
    Function.LeftInverse (NFAppTermLayerOfShape Γ) (NFAppTermLayerToShape Γ) := by
  intro layer
  cases layer with
  | mk code child =>
      cases code with
      | var v =>
          have hchild : (fun q => nomatch q) = child := by
            funext q
            cases q
          cases hchild
          change NFAppTermLayerOfShape Γ (Sum.inl (appTermVarToFin v)) =
            ⟨FiberCode.var v, (fun q => nomatch q)⟩
          dsimp [NFAppTermLayerOfShape]
          rw [appTermVarToFin_toVar v]
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          funext q
          cases q
      | op c h =>
          cases c with
          | dum =>
              cases h
          | lam =>
              cases h
          | app =>
              cases h
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              funext q
              cases q using Fin.cases with
              | zero => rfl
              | succ q =>
                  cases q using Fin.cases with
                  | zero => rfl
                  | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)

theorem NFAppTermLayerShape_right_inv (Γ : List NFSort) :
    Function.RightInverse (NFAppTermLayerOfShape Γ) (NFAppTermLayerToShape Γ) := by
  intro shape
  cases shape with
  | inl v =>
      simp [NFAppTermLayerToShape, NFAppTermLayerOfShape, appTermFinToVar_toFin]
  | inr pair =>
      cases pair
      rfl

def NFAppTermLayerShapeIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm) ≃ᵢ NFAppTermLayerShape Γ where
  toFun := NFAppTermLayerToShape Γ
  invFun := NFAppTermLayerOfShape Γ
  left_inv := NFAppTermLayerShape_left_inv Γ
  right_inv := NFAppTermLayerShape_right_inv Γ

def NFNormalTailToNat (Γ : List NFSort) :
    NFCode (Γ, .appTerm) ⊕ Nat → Nat
  | Sum.inl app =>
      if h : 0 < appTermCount Γ then
        2 * (CodeAlgebra.finProdNat (appTermCount Γ) h).toFun app
      else
        False.elim (Nat.not_lt_zero app.1.val (by
          have hzero : appTermCount Γ = 0 := Nat.eq_zero_of_not_pos h
          simpa [hzero] using app.1.isLt))
  | Sum.inr body =>
      if appTermCount Γ = 0 then body else 2 * body + 1

def NFNormalTailOfNat (Γ : List NFSort) (n : Nat) :
    NFCode (Γ, .appTerm) ⊕ Nat :=
  if h : 0 < appTermCount Γ then
    if _hp : n % 2 = 0 then
      Sum.inl ((CodeAlgebra.finProdNat (appTermCount Γ) h).invFun (n / 2))
    else
      Sum.inr (n / 2)
  else
    Sum.inr n

theorem NFNormalTail_left_inv (Γ : List NFSort) :
    Function.LeftInverse (NFNormalTailOfNat Γ) (NFNormalTailToNat Γ) := by
  intro x
  cases x with
  | inl app =>
      dsimp [NFNormalTailToNat, NFNormalTailOfNat]
      by_cases h : 0 < appTermCount Γ
      · let code := (CodeAlgebra.finProdNat (appTermCount Γ) h).toFun app
        have hmod : (2 * code) % 2 = 0 := Nat.mul_mod_right 2 code
        have hdiv : (2 * code) / 2 = code :=
          Nat.mul_div_right code (by decide : 0 < 2)
        simp [h, hmod, hdiv, code]
      · exact False.elim (Nat.not_lt_zero app.1.val (by
          have hzero : appTermCount Γ = 0 := Nat.eq_zero_of_not_pos h
          simpa [hzero] using app.1.isLt))
  | inr body =>
      dsimp [NFNormalTailToNat, NFNormalTailOfNat]
      by_cases h : appTermCount Γ = 0
      · simp [h, Nat.lt_irrefl]
      · have hpos : 0 < appTermCount Γ := Nat.pos_of_ne_zero h
        have hmod : (2 * body + 1) % 2 ≠ 0 := by
          have hcalc : (2 * body + 1) % 2 = 1 := by
            calc
              (2 * body + 1) % 2 = (1 + 2 * body) % 2 := by rw [Nat.add_comm]
              _ = 1 % 2 := Nat.add_mul_mod_self_left 1 2 body
              _ = 1 := Nat.mod_eq_of_lt (by decide : 1 < 2)
          omega
        have hdiv : (2 * body + 1) / 2 = body := by
          calc
            (2 * body + 1) / 2 = (1 + body * 2) / 2 := by
              rw [Nat.add_comm, Nat.mul_comm 2 body]
            _ = 1 / 2 + body := Nat.add_mul_div_right 1 body (by decide : 0 < 2)
            _ = body := by
              rw [Nat.div_eq_of_lt (by decide : 1 < 2)]
              exact Nat.zero_add body
        simp [hpos, h, hdiv]

theorem NFNormalTail_right_inv (Γ : List NFSort) :
    Function.RightInverse (NFNormalTailOfNat Γ) (NFNormalTailToNat Γ) := by
  intro n
  dsimp [NFNormalTailToNat, NFNormalTailOfNat]
  by_cases h : 0 < appTermCount Γ
  · by_cases hp : n % 2 = 0
    · simp [h, hp]
      have hsplit := Nat.div_add_mod n 2
      omega
    · simp [h, hp]
      have hne : ¬appTermCount Γ = 0 := Nat.ne_of_gt h
      have hsplit := Nat.div_add_mod n 2
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · exact False.elim (hp h0)
      · simp [hne]
        omega
  · have hzero : appTermCount Γ = 0 := Nat.eq_zero_of_not_pos h
    simp [hzero]

def NFNormalTailIso (Γ : List NFSort) :
    (NFCode (Γ, .appTerm) ⊕ Nat) ≃ᵢ Nat where
  toFun := NFNormalTailToNat Γ
  invFun := NFNormalTailOfNat Γ
  left_inv := NFNormalTail_left_inv Γ
  right_inv := NFNormalTail_right_inv Γ

def NFNormalLayerIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .normalExp) ≃ᵢ Nat :=
  Iso.trans (NFNormalLayerShapeIso Γ)
    (Iso.trans (Iso.sum (Iso.refl (Fin (normalExpCount Γ))) (NFNormalTailIso Γ))
      (CodeAlgebra.finPlusNat (normalExpCount Γ)))

def NFAppTermShapeToCode (Γ : List NFSort) :
    NFAppTermLayerShape Γ → NFCode (Γ, .appTerm)
  | Sum.inl v => (v, 0)
  | Sum.inr pair =>
      (pair.1.1, CodeAlgebra.prodNat.toFun (pair.1.2, pair.2) + 1)

def NFAppTermCodeToShape (Γ : List NFSort) :
    NFCode (Γ, .appTerm) → NFAppTermLayerShape Γ
  | (tag, 0) => Sum.inl tag
  | (tag, n + 1) =>
      let p := CodeAlgebra.prodNat.invFun n
      Sum.inr ((tag, p.1), p.2)

theorem NFAppTermShape_left_inv (Γ : List NFSort) :
    Function.LeftInverse (NFAppTermCodeToShape Γ) (NFAppTermShapeToCode Γ) := by
  intro x
  cases x with
  | inl v => rfl
  | inr pair =>
      cases pair with
      | mk fn arg =>
        cases fn with
        | mk tag payload =>
          dsimp [NFAppTermShapeToCode, NFAppTermCodeToShape]
          rw [CodeAlgebra.prodNat.left_inv (payload, arg)]

theorem NFAppTermShape_right_inv (Γ : List NFSort) :
    Function.RightInverse (NFAppTermCodeToShape Γ) (NFAppTermShapeToCode Γ) := by
  intro code
  cases code with
  | mk tag n =>
    cases n with
    | zero => rfl
    | succ n =>
        dsimp [NFAppTermShapeToCode, NFAppTermCodeToShape]
        rw [CodeAlgebra.prodNat.right_inv n]

def NFAppTermShapeIso (Γ : List NFSort) :
    NFAppTermLayerShape Γ ≃ᵢ NFCode (Γ, .appTerm) where
  toFun := NFAppTermShapeToCode Γ
  invFun := NFAppTermCodeToShape Γ
  left_inv := NFAppTermShape_left_inv Γ
  right_inv := NFAppTermShape_right_inv Γ

def NFAppTermLayerIso (Γ : List NFSort) :
    CodeLayer NFPoly NFInversion NFCode (Γ, .appTerm) ≃ᵢ NFCode (Γ, .appTerm) :=
  Iso.trans (NFAppTermLayerShapeIso Γ) (NFAppTermShapeIso Γ)

def NFCodeLayerIso :
    ∀ i, CodeLayer NFPoly NFInversion NFCode i ≃ᵢ NFCode i
  | (Γ, .normalExp) => NFNormalLayerIso Γ
  | (Γ, .appTerm) => NFAppTermLayerIso Γ

theorem NFCode_layer_child_rank_lt :
    ∀ {i : Poly.Ix NFSignature}
      (layer : CodeLayer NFPoly NFInversion NFCode i)
      (q : NFPoly.Pos
          (NFInversion.decode i layer.1).ctor
          (NFInversion.decode i layer.1).param),
      NFCodeRank
          (NFPoly.input (NFInversion.decode i layer.1).param q)
          (layer.2 q) < NFCodeRank i ((NFCodeLayerIso i).toFun layer) := by
  intro i layer
  cases i with
  | mk Γ t =>
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
                      let payload :=
                        (CodeAlgebra.finProdNat (appTermCount Γ) hcount).toFun app
                      have hparent :
                          (NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                              ⟨FiberCode.op NFCtor.dum rfl, child⟩ =
                            normalExpCount Γ + 2 * payload := by
                        simp [app, payload, hcount, NFCodeLayerIso, NFNormalLayerIso,
                          NFNormalLayerShapeIso, NFNormalLayerToShape,
                          NFNormalTailIso, NFNormalTailToNat, Iso.trans, Iso.sum,
                          CodeAlgebra.finPlusNat]
                      change NFCodeRank (Γ, NFSort.appTerm) app <
                        NFCodeRank (Γ, NFSort.normalExp)
                          ((NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                            ⟨FiberCode.op NFCtor.dum rfl, child⟩)
                      rw [hparent]
                      simp [NFCodeRank, hcne]
                      have happ_le : app.2 ≤ payload := by
                        simpa [payload] using
                          CodeAlgebra.finProdNat_toFun_snd_le
                            (appTermCount Γ) hcount app
                      omega
                  | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)
              | lam =>
                  cases h
                  intro q
                  cases q using Fin.cases with
                  | zero =>
                      let body : Nat := child ⟨0, by decide⟩
                      by_cases hc : appTermCount Γ = 0
                      · have hparent :
                            (NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                                ⟨FiberCode.op NFCtor.lam rfl, child⟩ =
                              normalExpCount Γ + body := by
                          simp [body, hc, NFCodeLayerIso, NFNormalLayerIso,
                            NFNormalLayerShapeIso, NFNormalLayerToShape,
                            NFNormalTailIso, NFNormalTailToNat, Iso.trans, Iso.sum,
                            CodeAlgebra.finPlusNat]
                        change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                          NFCodeRank (Γ, NFSort.normalExp)
                            ((NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                              ⟨FiberCode.op NFCtor.lam rfl, child⟩)
                        rw [hparent]
                        simp [NFCodeRank, appTermCount, Var.count, hc]
                        omega
                      · have hpos : 0 < appTermCount Γ := Nat.pos_of_ne_zero hc
                        have hparent :
                            (NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                                ⟨FiberCode.op NFCtor.lam rfl, child⟩ =
                              normalExpCount Γ + (2 * body + 1) := by
                          simp [body, hpos, hc, NFCodeLayerIso, NFNormalLayerIso,
                            NFNormalLayerShapeIso, NFNormalLayerToShape,
                            NFNormalTailIso, NFNormalTailToNat, Iso.trans, Iso.sum,
                            CodeAlgebra.finPlusNat]
                        change NFCodeRank (NFSort.appTerm :: Γ, NFSort.normalExp) body <
                          NFCodeRank (Γ, NFSort.normalExp)
                            ((NFCodeLayerIso (Γ, NFSort.normalExp)).toFun
                              ⟨FiberCode.op NFCtor.lam rfl, child⟩)
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
                  let pairCode := CodeAlgebra.prodNat.toFun (fn.2, arg)
                  have hparent :
                      (NFCodeLayerIso (Γ, NFSort.appTerm)).toFun
                          ⟨FiberCode.op NFCtor.app rfl, child⟩ =
                        (fn.1, pairCode + 1) := by
                    simp [fn, arg, pairCode, NFCodeLayerIso, NFAppTermLayerIso,
                      NFAppTermLayerShapeIso, NFAppTermLayerToShape, NFAppTermShapeIso,
                      NFAppTermShapeToCode, Iso.trans]
                  cases q using Fin.cases with
                  | zero =>
                      change NFCodeRank (Γ, NFSort.appTerm) fn <
                        NFCodeRank (Γ, NFSort.appTerm)
                          ((NFCodeLayerIso (Γ, NFSort.appTerm)).toFun
                            ⟨FiberCode.op NFCtor.app rfl, child⟩)
                      rw [hparent]
                      simp [NFCodeRank]
                      have hfn_le : fn.2 ≤ pairCode := by
                        simpa [pairCode, CodeAlgebra.prodNat] using
                          CodeAlgebra.prodNat_fst_le
                            (CodeAlgebra.prodNat.toFun (fn.2, arg))
                      omega
                  | succ q =>
                      cases q using Fin.cases with
                      | zero =>
                          change NFCodeRank (Γ, NFSort.normalExp) arg <
                            NFCodeRank (Γ, NFSort.appTerm)
                              ((NFCodeLayerIso (Γ, NFSort.appTerm)).toFun
                                ⟨FiberCode.op NFCtor.app rfl, child⟩)
                          rw [hparent]
                          simp [NFCodeRank, hcne]
                          have harg_le : arg ≤ pairCode := by
                            simpa [pairCode, CodeAlgebra.prodNat] using
                              CodeAlgebra.prodNat_snd_le
                                (CodeAlgebra.prodNat.toFun (fn.2, arg))
                          omega
                      | succ q => exact False.elim (Nat.not_lt_zero q.val q.isLt)

def NFCodeCodingData : CodeCodingData NFSignature where
  Code := NFCode
  layer := NFCodeLayerIso
  rank := NFCodeRank
  layer_child_rank_lt := by
    intro i layer q
    exact NFCode_layer_child_rank_lt layer q

def NFSyntaxCodeIso (Γ : List NFSort) (t : NFSort) :
    NFTerm Γ t ≃ᵢ NFCode (Γ, t) :=
  NFCodeCodingData.syntaxCodeIso Γ t

def NormalExpNatIso (Γ : List NFSort) : NormalExp Γ ≃ᵢ Nat :=
  NFSyntaxCodeIso Γ .normalExp

def AppTermCodeIso (Γ : List NFSort) :
    AppTerm Γ ≃ᵢ (Fin (appTermCount Γ) × Nat) :=
  NFSyntaxCodeIso Γ .appTerm

def NFClosedNatIso : NFClosed ≃ᵢ Nat :=
  NormalExpNatIso []

end TypedBinding
end Examples
end BijForm
