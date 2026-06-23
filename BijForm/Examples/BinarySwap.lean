import BijForm.TupleAction

namespace BijForm
namespace Examples
namespace BinarySwap

abbrev Tuple2 : Type :=
  TupleAction.FixedTuple.Tuple 2

abbrev SortedTuple2 : Type :=
  TupleAction.FixedTuple.SortedTuple 2

def leftIx : Fin 2 :=
  ⟨0, by decide⟩

def rightIx : Fin 2 :=
  ⟨1, by decide⟩

theorem fin2_eq_left_or_right (i : Fin 2) :
    i = leftIx ∨ i = rightIx := by
  have hval : i.val = 0 ∨ i.val = 1 := by omega
  cases hval with
  | inl h =>
      exact Or.inl (fin_eq_of_val_eq h)
  | inr h =>
      exact Or.inr (fin_eq_of_val_eq h)

theorem tuple2_ext {t u : Tuple2}
    (hleft : t leftIx = u leftIx)
    (hright : t rightIx = u rightIx) :
    t = u := by
  funext i
  rcases fin2_eq_left_or_right i with hi | hi
  · rw [hi]
    exact hleft
  · rw [hi]
    exact hright

def tupleOfPair (p : Nat × Nat) : Tuple2 :=
  fun i => if i = leftIx then p.1 else p.2

def pairOfTuple (t : Tuple2) : Nat × Nat :=
  (t leftIx, t rightIx)

def pairTupleIso : (Nat × Nat) ≃ᵢ Tuple2 where
  toFun := tupleOfPair
  invFun := pairOfTuple
  left_inv := by
    intro p
    cases p
    simp [tupleOfPair, pairOfTuple, leftIx, rightIx]
  right_inv := by
    intro t
    apply tuple2_ext
    · simp [tupleOfPair, pairOfTuple]
    · simp [tupleOfPair, pairOfTuple, leftIx, rightIx]

abbrev Canon : Type :=
  {p : Nat × Nat // p.1 ≤ p.2}

def canonOfSortedTuple2 (s : SortedTuple2) : Canon :=
  ⟨pairOfTuple s.val, s.property leftIx rightIx (by decide)⟩

def sortedTuple2OfCanon (p : Canon) : SortedTuple2 where
  val := tupleOfPair p.val
  property := by
    intro i j hij
    rcases fin2_eq_left_or_right i with hi | hi <;>
      rcases fin2_eq_left_or_right j with hj | hj
    · rw [hi, hj]
      exact Nat.le_refl _
    · rw [hi, hj]
      simpa [tupleOfPair, leftIx, rightIx] using p.property
    · rw [hi, hj] at hij
      simp [leftIx, rightIx] at hij
    · rw [hi, hj]
      exact Nat.le_refl _

def sortedTuple2CanonIso : SortedTuple2 ≃ᵢ Canon where
  toFun := canonOfSortedTuple2
  invFun := sortedTuple2OfCanon
  left_inv := by
    intro s
    apply Subtype.ext
    apply tuple2_ext
    · rfl
    · rfl
  right_inv := by
    intro p
    apply Subtype.ext
    cases p with
    | mk p hp =>
        cases p
        simp [canonOfSortedTuple2, sortedTuple2OfCanon, pairOfTuple,
          tupleOfPair, leftIx, rightIx]

def sortedTuple2Code : SortedTuple2 ≃ᵢ Nat :=
  Iso.trans sortedTuple2CanonIso CodeAlgebra.unorderedPairNat

def unitFinOneIso : Unit ≃ᵢ Fin 1 where
  toFun := fun _ => ⟨0, by decide⟩
  invFun := fun _ => ()
  left_inv := by
    intro u
    cases u
    rfl
  right_inv := by
    intro i
    exact fin_one_eq _ _

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

def swapFin2 (i : Fin 2) : Fin 2 :=
  if i = leftIx then rightIx else leftIx

@[simp]
theorem swapFin2_left :
    swapFin2 leftIx = rightIx := by
  simp [swapFin2]

@[simp]
theorem swapFin2_right :
    swapFin2 rightIx = leftIx := by
  simp [swapFin2, leftIx, rightIx]

theorem swapFin2_involutive (i : Fin 2) :
    swapFin2 (swapFin2 i) = i := by
  rcases fin2_eq_left_or_right i with hi | hi
  · rw [hi]
    simp
  · rw [hi]
    simp

def idPerm : TupleAction.FixedTuple.Perm 2 where
  toFun := id
  invFun := id
  left_inv := by
    intro i
    rfl
  right_inv := by
    intro i
    rfl

def swapPerm : TupleAction.FixedTuple.Perm 2 where
  toFun := swapFin2
  invFun := swapFin2
  left_inv := by
    intro i
    exact swapFin2_involutive i
  right_inv := by
    intro i
    exact swapFin2_involutive i

def perm : Elem → TupleAction.FixedTuple.Perm 2
  | .id => idPerm
  | .swap => swapPerm

def inv : Elem → Elem
  | .id => .id
  | .swap => .swap

def mul : Elem → Elem → Elem
  | .id, g => g
  | .swap, .id => .swap
  | .swap, .swap => .id

def permFamily : TupleAction.FixedTuple.PermFamily 2 where
  Elem := Elem
  size := 2
  elemCode := elemCode
  perm := perm
  id := .id
  inv := inv
  mul := mul
  act_id := by
    intro t
    apply tuple2_ext <;> rfl
  act_inv := by
    intro g t
    cases g <;>
      apply tuple2_ext <;>
      simp [TupleAction.FixedTuple.Perm.actTuple, perm, inv, idPerm,
        swapPerm]
  act_mul := by
    intro g h t
    cases g <;> cases h <;>
      apply tuple2_ext <;>
      simp [TupleAction.FixedTuple.Perm.actTuple, perm, mul, idPerm,
        swapPerm]

def tupleAction : TupleAction.FiniteAction Tuple2 :=
  permFamily.action

def action : TupleAction.FiniteAction (Nat × Nat) :=
  tupleAction.reindex pairTupleIso

def act : Elem → Nat × Nat → Nat × Nat
  | .id, p => p
  | .swap, p => (p.2, p.1)

theorem action_act_eq (g : Elem) (p : Nat × Nat) :
    action.act g p = act g p := by
  cases g <;> cases p <;>
    simp [action, tupleAction, TupleAction.FiniteAction.reindex,
      TupleAction.FixedTuple.PermFamily.action, permFamily,
      TupleAction.FixedTuple.Perm.actTuple, perm, idPerm, swapPerm,
      swapFin2, pairTupleIso, tupleOfPair, pairOfTuple, act, leftIx,
      rightIx]

def residual (s : SortedTuple2) :
    TupleAction.FixedTuple.ResidualImageData permFamily s where
  Image := Unit
  imageSize := 1
  imageCode := unitFinOneIso
  tupleOf := fun _ => s.val

def residualSigmaCode :
    (Σ s : SortedTuple2, (residual s).Image) ≃ᵢ Nat :=
  Iso.trans
    ({ toFun := fun c => c.1
       invFun := fun s => ⟨s, ()⟩
       left_inv := by
        intro c
        cases c with
        | mk s r =>
            cases r
            rfl
       right_inv := by
        intro s
        rfl } :
      (Σ s : SortedTuple2, (residual s).Image) ≃ᵢ SortedTuple2)
    sortedTuple2Code

def tupleSortCanon (t : Tuple2) : Canon :=
  CodeAlgebra.sortNatPair (t leftIx) (t rightIx)

def tupleNormalize :
    Tuple2 → Σ s : SortedTuple2, (residual s).Image :=
  fun t => ⟨sortedTuple2OfCanon (tupleSortCanon t), ()⟩

theorem tupleNormalize_swap (t : Tuple2) :
    tupleNormalize ((perm .swap).actTuple t) = tupleNormalize t := by
  apply Sigma.ext
  · apply Subtype.ext
    change
      tupleOfPair
          (CodeAlgebra.sortNatPair (t rightIx) (t leftIx)).val =
        tupleOfPair
          (CodeAlgebra.sortNatPair (t leftIx) (t rightIx)).val
    rw [CodeAlgebra.sortNatPair_comm (t rightIx) (t leftIx)]
  · exact heq_of_eq rfl

theorem tupleNormalize_respects
    {t u : Tuple2} (h : TupleAction.FixedTuple.PermFamily.OrbitRel permFamily t u) :
    tupleNormalize t = tupleNormalize u := by
  rcases h with ⟨g, hg⟩
  rw [← hg]
  cases g with
  | id =>
      rfl
  | swap =>
      exact (tupleNormalize_swap t).symm

theorem tupleNormalize_denormalize (c :
    Σ s : SortedTuple2, (residual s).Image) :
    tupleNormalize ((residual c.1).tupleOf c.2) = c := by
  cases c with
  | mk s r =>
      cases r
      apply Sigma.ext
      · change sortedTuple2OfCanon
          (CodeAlgebra.sortNatPair (s.val leftIx) (s.val rightIx)) = s
        rw [CodeAlgebra.sortNatPair_of_le
          (s.property leftIx rightIx (by decide))]
        exact sortedTuple2CanonIso.left_inv s
      · exact heq_of_eq rfl

theorem denormalize_tupleNormalize_rel (t : Tuple2) :
    TupleAction.FixedTuple.PermFamily.OrbitRel permFamily
      ((residual (tupleNormalize t).1).tupleOf (tupleNormalize t).2) t := by
  by_cases h : t leftIx ≤ t rightIx
  · refine ⟨.id, ?_⟩
    have hsort :
        CodeAlgebra.sortNatPair (t leftIx) (t rightIx) =
          ⟨(t leftIx, t rightIx), h⟩ :=
      CodeAlgebra.sortNatPair_of_le h
    change idPerm.actTuple
      ((residual (tupleNormalize t).1).tupleOf (tupleNormalize t).2) = t
    apply tuple2_ext
    · change (CodeAlgebra.sortNatPair (t leftIx) (t rightIx)).val.1 =
        t leftIx
      rw [hsort]
    · change (CodeAlgebra.sortNatPair (t leftIx) (t rightIx)).val.2 =
        t rightIx
      rw [hsort]
  · refine ⟨.swap, ?_⟩
    have hsort :
        CodeAlgebra.sortNatPair (t leftIx) (t rightIx) =
          ⟨(t rightIx, t leftIx), Nat.le_of_not_ge h⟩ := by
      simp [CodeAlgebra.sortNatPair, h]
    change swapPerm.actTuple
      ((residual (tupleNormalize t).1).tupleOf (tupleNormalize t).2) = t
    apply tuple2_ext
    · change (CodeAlgebra.sortNatPair (t leftIx) (t rightIx)).val.2 =
        t leftIx
      rw [hsort]
    · change (CodeAlgebra.sortNatPair (t leftIx) (t rightIx)).val.1 =
        t rightIx
      rw [hsort]

def orbitCodingData : TupleAction.FixedTuple.OrbitCodingData 2 permFamily where
  sortedCode := sortedTuple2Code
  residual := residual
  residualSigmaCode := residualSigmaCode
  normalize := tupleNormalize
  normalize_respects := by
    intro t u h
    exact tupleNormalize_respects h
  denormalize_normalize_rel := denormalize_tupleNormalize_rel
  normalize_denormalize := tupleNormalize_denormalize

def tupleConcreteCode : TupleAction.ConcreteActionCode tupleAction :=
  TupleAction.FixedTuple.orbitCodingData_toConcreteActionCode orbitCodingData

def concreteCode : TupleAction.ConcreteActionCode action :=
  tupleConcreteCode.reindex pairTupleIso

def normalize (p : Nat × Nat) : Canon :=
  CodeAlgebra.sortNatPair p.1 p.2

def denormalize (p : Canon) : Nat × Nat :=
  p.val

theorem normalize_denormalize (p : Canon) :
    normalize (denormalize p) = p := by
  exact CodeAlgebra.sortNatPair_of_le p.property

def encode (a b : Nat) : Nat :=
  concreteCode.code.toFun (concreteCode.normalize (a, b))

def decode (n : Nat) : Nat × Nat :=
  concreteCode.denormalize (concreteCode.code.invFun n)

theorem encode_eq_unorderedPairCode (a b : Nat) :
    encode a b = CodeAlgebra.unorderedPairCode a b := by
  rfl

theorem concreteCode_normalize_eq (p : Nat × Nat) :
    concreteCode.code.toFun (concreteCode.normalize p) =
      CodeAlgebra.unorderedPairNat.toFun (normalize p) := by
  cases p
  rfl

theorem decode_eq_unorderedPairNat_invFun (n : Nat) :
    decode n = (CodeAlgebra.unorderedPairNat.invFun n).val := by
  rfl

theorem action_sound (g : Elem) (p : Nat × Nat) :
    concreteCode.normalize (action.act g p) = concreteCode.normalize p := by
  exact concreteCode.normalize_respects (concreteCode.action_sound g p)

theorem encode_comm (a b : Nat) :
    encode a b = encode b a := by
  rw [encode_eq_unorderedPairCode, encode_eq_unorderedPairCode]
  exact CodeAlgebra.unorderedPairCode_comm a b

theorem encode_decode (n : Nat) :
    encode (decode n).1 (decode n).2 = n := by
  rw [decode_eq_unorderedPairNat_invFun]
  exact CodeAlgebra.unorderedPairCode_invFun n

theorem decode_encode_of_le {a b : Nat} (h : a ≤ b) :
    decode (encode a b) = (a, b) := by
  rw [encode_eq_unorderedPairCode, decode_eq_unorderedPairNat_invFun]
  exact congrArg Subtype.val
    (CodeAlgebra.unorderedPairNat_inv_unorderedPairCode_of_le h)

theorem decode_encode_of_not_le {a b : Nat} (h : ¬a ≤ b) :
    decode (encode a b) = (b, a) := by
  rw [encode_eq_unorderedPairCode, decode_eq_unorderedPairNat_invFun]
  exact congrArg Subtype.val
    (CodeAlgebra.unorderedPairNat_inv_unorderedPairCode_of_not_le h)

end BinarySwap
end Examples
end BijForm
