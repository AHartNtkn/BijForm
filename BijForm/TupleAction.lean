import BijForm.CodeAlgebra

namespace BijForm
namespace TupleAction

/--
Concrete coding data for a quotient of a raw carrier.  The quotient relation is
explicit, while `normalize` and `denormalize` provide a computable normal form
and concrete code for the quotient.
-/
structure ConcreteQuotientCode (Raw : Type u) where
  Rel : Raw → Raw → Prop
  rel_refl : ∀ x, Rel x x
  rel_symm : ∀ {x y}, Rel x y → Rel y x
  rel_trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z
  Canon : Type v
  code : Canon ≃ᵢ Nat
  normalize : Raw → Canon
  denormalize : Canon → Raw
  normalize_respects : ∀ {x y}, Rel x y → normalize x = normalize y
  denormalize_normalize_rel : ∀ x, Rel (denormalize (normalize x)) x
  normalize_denormalize : ∀ c, normalize (denormalize c) = c

namespace ConcreteQuotientCode

def setoid {Raw : Type u} (C : ConcreteQuotientCode Raw) : Setoid Raw where
  r := C.Rel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact C.rel_refl x
    · intro x y hxy
      exact C.rel_symm hxy
    · intro x y z hxy hyz
      exact C.rel_trans hxy hyz

abbrev Carrier {Raw : Type u} (C : ConcreteQuotientCode Raw) : Type u :=
  Quotient C.setoid

def ofRaw {Raw : Type u} (C : ConcreteQuotientCode Raw) (x : Raw) :
    C.Carrier :=
  Quotient.mk C.setoid x

def iso {Raw : Type u} (C : ConcreteQuotientCode Raw) : C.Carrier ≃ᵢ Nat where
  toFun :=
    Quotient.lift (fun x => C.code.toFun (C.normalize x))
      (by
        intro x y hxy
        change C.code.toFun (C.normalize x) = C.code.toFun (C.normalize y)
        rw [C.normalize_respects hxy])
  invFun := fun n => C.ofRaw (C.denormalize (C.code.invFun n))
  left_inv := by
    intro q
    exact Quotient.ind (s := C.setoid)
      (motive := fun q =>
        C.ofRaw (C.denormalize
          (C.code.invFun
            (Quotient.lift (fun x => C.code.toFun (C.normalize x))
              (by
                intro x y hxy
                change C.code.toFun (C.normalize x) = C.code.toFun (C.normalize y)
                rw [C.normalize_respects hxy]) q))) = q)
      (fun x => by
        change C.ofRaw
            (C.denormalize (C.code.invFun (C.code.toFun (C.normalize x)))) =
          C.ofRaw x
        rw [C.code.left_inv]
        exact Quotient.sound (C.denormalize_normalize_rel x))
      q
  right_inv := by
    intro n
    change C.code.toFun
        (C.normalize (C.denormalize (C.code.invFun n))) = n
    rw [C.normalize_denormalize, C.code.right_inv]

end ConcreteQuotientCode

/-- A finite action surface.  The `Elem` code makes the acting family concrete;
the quotient relation and canonicalization live in `ConcreteActionCode`. -/
structure FiniteAction (Raw : Type u) where
  Elem : Type v
  size : Nat
  elemCode : Elem ≃ᵢ Fin size
  act : Elem → Raw → Raw

namespace FiniteAction

def orbitStep {Raw : Type u} (A : FiniteAction Raw) (x y : Raw) : Prop :=
  ∃ g : A.Elem, A.act g x = y

end FiniteAction

/-- Concrete quotient coding for a finite action. `action_sound` records that
every action step is included in the quotient relation being normalized. -/
structure ConcreteActionCode {Raw : Type u} (A : FiniteAction Raw) extends
    ConcreteQuotientCode Raw where
  action_sound : ∀ g x, Rel (A.act g x) x

namespace BinarySwap

inductive Elem where
  | id
  | swap
deriving DecidableEq

def elemCode : Elem ≃ᵢ Fin 2 where
  toFun
    | .id => ⟨0, by decide⟩
    | .swap => ⟨1, by decide⟩
  invFun i :=
    if h : i.val = 0 then .id else .swap
  left_inv := by
    intro g
    cases g <;> simp
  right_inv := by
    intro i
    apply Fin.ext
    by_cases h : i.val = 0
    · simp [h]
    · have hi : i.val = 1 := by omega
      simp [hi]

def act : Elem → Nat × Nat → Nat × Nat
  | .id, p => p
  | .swap, p => (p.2, p.1)

def action : FiniteAction (Nat × Nat) where
  Elem := Elem
  size := 2
  elemCode := elemCode
  act := act

def Rel (p q : Nat × Nat) : Prop :=
  CodeAlgebra.sortNatPair p.1 p.2 = CodeAlgebra.sortNatPair q.1 q.2

theorem rel_refl (p : Nat × Nat) : Rel p p :=
  rfl

theorem rel_symm {p q : Nat × Nat} (h : Rel p q) : Rel q p :=
  h.symm

theorem rel_trans {p q r : Nat × Nat} (hpq : Rel p q) (hqr : Rel q r) :
    Rel p r :=
  hpq.trans hqr

theorem action_sound (g : Elem) (p : Nat × Nat) : Rel (act g p) p := by
  cases g with
  | id => rfl
  | swap =>
      exact CodeAlgebra.sortNatPair_comm p.2 p.1

abbrev Canon : Type :=
  {p : Nat × Nat // p.1 ≤ p.2}

def normalize (p : Nat × Nat) : Canon :=
  CodeAlgebra.sortNatPair p.1 p.2

def denormalize (p : Canon) : Nat × Nat :=
  p.val

theorem normalize_respects {p q : Nat × Nat} (h : Rel p q) :
    normalize p = normalize q :=
  h

theorem denormalize_normalize_rel (p : Nat × Nat) :
    Rel (denormalize (normalize p)) p := by
  cases p with
  | mk a b =>
    dsimp [Rel, normalize, denormalize]
    rw [CodeAlgebra.sortNatPair_of_le (CodeAlgebra.sortNatPair a b).property]

theorem normalize_denormalize (p : Canon) :
    normalize (denormalize p) = p := by
  exact CodeAlgebra.sortNatPair_of_le p.property

def concreteCode : ConcreteActionCode action where
  Rel := Rel
  rel_refl := rel_refl
  rel_symm := @rel_symm
  rel_trans := @rel_trans
  Canon := Canon
  code := CodeAlgebra.unorderedPairNat
  normalize := normalize
  denormalize := denormalize
  normalize_respects := @normalize_respects
  denormalize_normalize_rel := denormalize_normalize_rel
  normalize_denormalize := normalize_denormalize
  action_sound := action_sound

def encode (a b : Nat) : Nat :=
  concreteCode.code.toFun (concreteCode.normalize (a, b))

def decode (n : Nat) : Nat × Nat :=
  concreteCode.denormalize (concreteCode.code.invFun n)

theorem encode_eq_unorderedPairCode (a b : Nat) :
    encode a b = CodeAlgebra.unorderedPairCode a b :=
  rfl

theorem encode_comm (a b : Nat) :
    encode a b = encode b a := by
  exact CodeAlgebra.unorderedPairCode_comm a b

theorem encode_decode (n : Nat) :
    encode (decode n).1 (decode n).2 = n := by
  exact CodeAlgebra.unorderedPairCode_invFun n

theorem decode_encode_of_le {a b : Nat} (h : a ≤ b) :
    decode (encode a b) = (a, b) := by
  exact congrArg Subtype.val
    (CodeAlgebra.unorderedPairNat_inv_unorderedPairCode_of_le h)

theorem decode_encode_of_not_le {a b : Nat} (h : ¬a ≤ b) :
    decode (encode a b) = (b, a) := by
  exact congrArg Subtype.val
    (CodeAlgebra.unorderedPairNat_inv_unorderedPairCode_of_not_le h)

end BinarySwap

end TupleAction
end BijForm
