import BijForm.TupleAction

namespace BijForm
namespace Examples
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
    exact fin_eq_of_val_eq (by
      by_cases h : i.val = 0
      · simp [h]
      · have hi : i.val = 1 := by omega
        simp [hi])

def act : Elem → Nat × Nat → Nat × Nat
  | .id, p => p
  | .swap, p => (p.2, p.1)

def action : TupleAction.FiniteAction (Nat × Nat) where
  Elem := Elem
  size := 2
  elemCode := elemCode
  act := act

abbrev Canon : Type :=
  {p : Nat × Nat // p.1 ≤ p.2}

def normalize (p : Nat × Nat) : Canon :=
  CodeAlgebra.sortNatPair p.1 p.2

def denormalize (p : Canon) : Nat × Nat :=
  p.val

theorem normalize_denormalize (p : Canon) :
    normalize (denormalize p) = p := by
  exact CodeAlgebra.sortNatPair_of_le p.property

theorem action_sound (g : Elem) (p : Nat × Nat) :
    normalize (act g p) = normalize p := by
  cases g with
  | id => rfl
  | swap =>
      exact CodeAlgebra.sortNatPair_comm p.2 p.1

def quotientCode : TupleAction.ConcreteQuotientCode (Nat × Nat) :=
  TupleAction.ConcreteQuotientCode.ofNormalizer
    CodeAlgebra.unorderedPairNat normalize denormalize normalize_denormalize

def concreteCode : TupleAction.ConcreteActionCode action where
  toConcreteQuotientCode := quotientCode
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
end Examples
end BijForm
