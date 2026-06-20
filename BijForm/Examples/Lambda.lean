import BijForm.DependentPolynomial
import BijForm.CodeAlgebra

namespace BijForm
namespace Examples

open DepPoly

/-- De Bruijn lambda terms indexed by context size. Variables are unavailable
at context `0`, while abstraction moves the recursive child to context
`k + 1`. -/
inductive LamSyntax : Nat → Type
  | var {k : Nat} (v : Fin k) : LamSyntax k
  | lam {k : Nat} : LamSyntax (k + 1) → LamSyntax k
  | app {k : Nat} : LamSyntax k → LamSyntax k → LamSyntax k

namespace LamSyntax

def rank : ∀ {k : Nat}, LamSyntax k → Nat
  | _, var _ => 0
  | _, lam body => rank body + 1
  | _, app fn arg => Nat.max (rank fn) (rank arg) + 1

end LamSyntax

/-- Polynomial constructors for de Bruijn lambda terms. -/
inductive LamCtor where
  | var
  | lam
  | app
deriving DecidableEq, Repr

def LamParam : LamCtor → Type
  | .var => Σ k : Nat, Fin k
  | .lam => Nat
  | .app => Nat

def LamOut : (c : LamCtor) → LamParam c → Nat
  | LamCtor.var, p => p.1
  | LamCtor.lam, (k : Nat) => k
  | LamCtor.app, (k : Nat) => k

def LamPos : (c : LamCtor) → LamParam c → Type
  | LamCtor.var, _ => Empty
  | LamCtor.lam, _ => Unit
  | LamCtor.app, _ => Bool

def LamInput : {c : LamCtor} → (p : LamParam c) → LamPos c p → Nat
  | LamCtor.var, _, q => nomatch q
  | LamCtor.lam, (k : Nat), _ => k + 1
  | LamCtor.app, (k : Nat), _ => k

/-- Dependent polynomial for de Bruijn lambda terms. -/
def LamPoly : DepPoly Nat where
  Ctor := LamCtor
  Param := LamParam
  out := LamOut
  Pos := LamPos
  input := LamInput

inductive LamCode (k : Nat) where
  | var (v : Fin k)
  | lam
  | app

def LamDecode (k : Nat) : LamCode k → Fiber LamPoly k
  | .var v => ⟨.var, ⟨k, v⟩, rfl⟩
  | .lam => ⟨.lam, k, rfl⟩
  | .app => ⟨.app, k, rfl⟩

def LamEncode (k : Nat) : Fiber LamPoly k → LamCode k
  | ⟨.var, p, h⟩ =>
      have _ : LamPoly.out LamCtor.var p = k := h
      .var (k := k) (h ▸ p.2)
  | ⟨.lam, _, _⟩ => .lam
  | ⟨.app, _, _⟩ => .app

theorem Lam_decode_encode (k : Nat) (f : Fiber LamPoly k) :
    LamDecode k (LamEncode k f) = f := by
  cases f with
  | mk ctor param out_eq =>
    cases ctor with
    | var =>
        cases param with
        | mk k' v =>
          cases out_eq
          rfl
    | lam =>
        cases out_eq
        rfl
    | app =>
        cases out_eq
        rfl

theorem Lam_encode_decode (k : Nat) (c : LamCode k) :
    LamEncode k (LamDecode k c) = c := by
  cases c <;> rfl

def LamInversion : OutputIndexInversion LamPoly where
  Code := LamCode
  decode := LamDecode
  encode := LamEncode
  decode_encode := Lam_decode_encode
  encode_decode := Lam_encode_decode

def LamLayerToSyntax (k : Nat) :
    CodeLayer LamPoly LamInversion LamSyntax k → LamSyntax k
  | ⟨.var v, _child⟩ => .var v
  | ⟨.lam, child⟩ => .lam (child ())
  | ⟨.app, child⟩ => .app (child false) (child true)

def LamSyntaxToLayer (k : Nat) :
    LamSyntax k → CodeLayer LamPoly LamInversion LamSyntax k
  | .var v => ⟨.var v, fun q => nomatch q⟩
  | .lam body => ⟨.lam, fun _ => body⟩
  | .app fn arg => ⟨.app, fun
      | false => fn
      | true => arg⟩

theorem LamLayer_left_inv (k : Nat) :
    Function.LeftInverse (LamSyntaxToLayer k) (LamLayerToSyntax k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | var v =>
      have hchild : (fun q => nomatch q) = child := by
        child_eta_empty
      cases hchild
      rfl
    | lam =>
      have hchild : (fun _ => child ()) = child := by
        child_eta_unit
      cases hchild
      rfl
    | app =>
      have hchild : child = (fun
          | false => child false
          | true => child true) := by
        child_eta_bool
      rw [hchild]
      rfl

theorem LamLayer_right_inv (k : Nat) :
    Function.RightInverse (LamSyntaxToLayer k) (LamLayerToSyntax k) := by
  intro t
  cases t <;> simp [LamLayerToSyntax, LamSyntaxToLayer]

def LamLayerIso (k : Nat) :
    CodeLayer LamPoly LamInversion LamSyntax k ≃ᵢ LamSyntax k where
  toFun := LamLayerToSyntax k
  invFun := LamSyntaxToLayer k
  left_inv := LamLayer_left_inv k
  right_inv := LamLayer_right_inv k

theorem Lam_layer_child_rank_lt :
    ∀ {k : Nat} (z : LamSyntax k)
      (q : LamPoly.Pos
          (LamInversion.decode k ((LamLayerIso k).invFun z).1).ctor
          (LamInversion.decode k ((LamLayerIso k).invFun z).1).param),
      LamSyntax.rank (((LamLayerIso k).invFun z).2 q) < LamSyntax.rank z := by
  intro k z q
  cases z with
  | var v => cases q
  | lam body =>
      cases q
      simp [LamLayerIso, LamSyntaxToLayer, LamInversion, LamDecode, LamSyntax.rank]
  | app fn arg =>
      cases q
      · simpa [LamLayerIso, LamSyntaxToLayer, LamInversion, LamDecode,
          LamSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_left (LamSyntax.rank fn) (LamSyntax.rank arg))
      · simpa [LamLayerIso, LamSyntaxToLayer, LamInversion, LamDecode,
          LamSyntax.rank] using
          Nat.lt_succ_of_le (Nat.le_max_right (LamSyntax.rank fn) (LamSyntax.rank arg))

def LamGeneratedCode : GeneratedCode LamPoly LamSyntax where
  inversion := LamInversion
  layer := LamLayerIso
  rank := fun _ t => LamSyntax.rank t
  child_rank_lt := Lam_layer_child_rank_lt

/-- Lambda terms as the generic initial algebra are bijective with readable
syntax through generated layer coding. -/
def LamSyntaxIso (k : Nat) : Mu LamPoly k ≃ᵢ LamSyntax k :=
  LamGeneratedCode.iso k

abbrev LamNatLayerShape (k : Nat) :=
  Fin k ⊕ (Nat ⊕ (Nat × Nat))

def LamNatLayerShapeTo (k : Nat) :
    CodeLayer LamPoly LamInversion (fun _ => Nat) k → LamNatLayerShape k
  | ⟨.var v, _child⟩ => Sum.inl v
  | ⟨.lam, child⟩ => Sum.inr (Sum.inl (child ()))
  | ⟨.app, child⟩ => Sum.inr (Sum.inr (child false, child true))

def LamNatLayerShapeInv (k : Nat) :
    LamNatLayerShape k → CodeLayer LamPoly LamInversion (fun _ => Nat) k
  | Sum.inl v => ⟨.var v, fun q => nomatch q⟩
  | Sum.inr (Sum.inl body) => ⟨.lam, fun _ => body⟩
  | Sum.inr (Sum.inr pair) => ⟨.app, fun
      | false => pair.1
      | true => pair.2⟩

theorem LamNatLayerShape_left_inv (k : Nat) :
    Function.LeftInverse (LamNatLayerShapeInv k) (LamNatLayerShapeTo k) := by
  intro layer
  cases layer with
  | mk code child =>
    cases code with
    | var v =>
      have hchild : (fun q => nomatch q) = child := by
        child_eta_empty
      cases hchild
      rfl
    | lam =>
      have hchild : (fun _ => child ()) = child := by
        child_eta_unit
      cases hchild
      rfl
    | app =>
      have hchild : child = (fun
          | false => child false
          | true => child true) := by
        child_eta_bool
      rw [hchild]
      rfl

theorem LamNatLayerShape_right_inv (k : Nat) :
    Function.RightInverse (LamNatLayerShapeInv k) (LamNatLayerShapeTo k) := by
  intro shape
  cases shape with
  | inl v => rfl
  | inr tail =>
      cases tail with
      | inl body => rfl
      | inr pair =>
          cases pair
          rfl

def LamNatLayerShapeIso (k : Nat) :
    CodeLayer LamPoly LamInversion (fun _ => Nat) k ≃ᵢ LamNatLayerShape k where
  toFun := LamNatLayerShapeTo k
  invFun := LamNatLayerShapeInv k
  left_inv := LamNatLayerShape_left_inv k
  right_inv := LamNatLayerShape_right_inv k

def LamNatLayerIso (k : Nat) :
    CodeLayer LamPoly LamInversion (fun _ => Nat) k ≃ᵢ Nat :=
  Iso.trans (LamNatLayerShapeIso k)
    (CodeAlgebra.finPrefixNat k CodeAlgebra.sumProdNat)

def LamNatRank (k n : Nat) : Nat :=
  n + if k = 0 then 1 else 0

/-- The closed code `0` descends through `lam` to context `1` with the same
numeric code, so identity rank on `Nat` would not be enough. -/
theorem LamNatRank_closed_zero_child :
    LamNatRank 1 0 < LamNatRank 0 0 := by
  decide

/-- At the empty context, code `0` selects `lam`, not `app`; otherwise the
decoder would recurse at the same index and code. -/
theorem LamNatLayer_zero_invFun_zero :
    (LamNatLayerIso 0).invFun 0 = ⟨LamCode.lam, fun _ => 0⟩ := by
  rfl

theorem LamNat_layer_child_rank_lt :
    ∀ {k : Nat} (layer : CodeLayer LamPoly LamInversion (fun _ => Nat) k)
      (q : LamPoly.Pos
          (LamInversion.decode k layer.1).ctor
          (LamInversion.decode k layer.1).param),
      LamNatRank
          (LamPoly.input (LamInversion.decode k layer.1).param q)
          (layer.2 q) < LamNatRank k ((LamNatLayerIso k).toFun layer) := by
  intro k layer
  cases layer with
  | mk code child =>
    cases code with
    | var v =>
        intro q
        cases q
    | lam =>
        intro q
        cases q
        let bodyCode := child ()
        have hparent :
            (LamNatLayerIso k).toFun ⟨LamCode.lam, child⟩ = k + 2 * bodyCode := by
          simp [bodyCode, LamNatLayerIso, LamNatLayerShapeIso, LamNatLayerShapeTo,
            CodeAlgebra.finPrefixNat, CodeAlgebra.sumProdNat, Iso.trans, Iso.sum,
            CodeAlgebra.finPlusNat,
            CodeAlgebra.sumNat, Iso.refl]
        change LamNatRank (k + 1) bodyCode <
          LamNatRank k ((LamNatLayerIso k).toFun ⟨LamCode.lam, child⟩)
        rw [hparent]
        dsimp [LamNatRank]
        by_cases hk : k = 0
        · subst k
          simp
          omega
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          simp [hk]
          omega
    | app =>
        intro q
        let pairCode := CodeAlgebra.prodNat.toFun (child false, child true)
        have hparent :
            (LamNatLayerIso k).toFun ⟨LamCode.app, child⟩ =
              k + (2 * pairCode + 1) := by
          simp [pairCode, LamNatLayerIso, LamNatLayerShapeIso, LamNatLayerShapeTo,
            CodeAlgebra.finPrefixNat, CodeAlgebra.sumProdNat, Iso.trans, Iso.sum,
            CodeAlgebra.finPlusNat,
            CodeAlgebra.sumNat, Iso.refl]
        cases q
        · change LamNatRank k (child false) <
            LamNatRank k ((LamNatLayerIso k).toFun ⟨LamCode.app, child⟩)
          rw [hparent]
          have hchild_le : child false ≤ pairCode := by
            simpa [pairCode] using
              CodeAlgebra.prodNat_toFun_fst_le (child false, child true)
          have hpair_lt : pairCode < k + (2 * pairCode + 1) := by
            omega
          have hchild_lt_parent : child false < k + (2 * pairCode + 1) :=
            Nat.lt_of_le_of_lt hchild_le hpair_lt
          dsimp [LamNatRank]
          by_cases hk : k = 0
          · simpa [hk] using hchild_lt_parent
          · simpa [hk] using hchild_lt_parent
        · change LamNatRank k (child true) <
            LamNatRank k ((LamNatLayerIso k).toFun ⟨LamCode.app, child⟩)
          rw [hparent]
          have hchild_le : child true ≤ pairCode := by
            simpa [pairCode] using
              CodeAlgebra.prodNat_toFun_snd_le (child false, child true)
          have hpair_lt : pairCode < k + (2 * pairCode + 1) := by
            omega
          have hchild_lt_parent : child true < k + (2 * pairCode + 1) :=
            Nat.lt_of_le_of_lt hchild_le hpair_lt
          dsimp [LamNatRank]
          by_cases hk : k = 0
          · simpa [hk] using hchild_lt_parent
          · simpa [hk] using hchild_lt_parent

def LamNatGeneratedCode : GeneratedRankedNatCode LamPoly :=
  GeneratedRankedNatCode.ofLayerChildRank LamInversion LamNatLayerIso LamNatRank
    (by
      intro k layer q
      exact LamNat_layer_child_rank_lt layer q)

def LamNatIso (k : Nat) : Mu LamPoly k ≃ᵢ Nat :=
  LamNatGeneratedCode.iso k

def LamSyntaxNatIso (k : Nat) : LamSyntax k ≃ᵢ Nat :=
  Iso.trans (Iso.symm (LamSyntaxIso k)) (LamNatIso k)

def ClosedLamSyntaxNatIso : LamSyntax 0 ≃ᵢ Nat :=
  LamSyntaxNatIso 0

end Examples
end BijForm
