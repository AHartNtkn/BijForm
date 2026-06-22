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

def ofNormalizer {Raw : Type u} {Canon : Type v}
    (code : Canon ≃ᵢ Nat)
    (normalize : Raw → Canon)
    (denormalize : Canon → Raw)
    (normalize_denormalize : ∀ c, normalize (denormalize c) = c) :
    ConcreteQuotientCode Raw where
  Rel x y := normalize x = normalize y
  rel_refl := by
    intro x
    rfl
  rel_symm := by
    intro x y hxy
    exact hxy.symm
  rel_trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz
  Canon := Canon
  code := code
  normalize := normalize
  denormalize := denormalize
  normalize_respects := by
    intro x y hxy
    exact hxy
  denormalize_normalize_rel := by
    intro x
    exact normalize_denormalize (normalize x)
  normalize_denormalize := normalize_denormalize

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

def normalForm {Raw : Type u} (C : ConcreteQuotientCode Raw) :
    QuotientNormalForm C.setoid Nat where
  encode x := C.code.toFun (C.normalize x)
  decode n := C.denormalize (C.code.invFun n)
  encode_respects := by
    intro x y hxy
    change C.code.toFun (C.normalize x) = C.code.toFun (C.normalize y)
    rw [C.normalize_respects hxy]
  decode_encode_rel := by
    intro x
    change C.Rel
      (C.denormalize (C.code.invFun (C.code.toFun (C.normalize x)))) x
    rw [C.code.left_inv]
    exact C.denormalize_normalize_rel x
  encode_decode := by
    intro n
    change C.code.toFun
      (C.normalize (C.denormalize (C.code.invFun n))) = n
    rw [C.normalize_denormalize, C.code.right_inv]

def iso {Raw : Type u} (C : ConcreteQuotientCode Raw) : C.Carrier ≃ᵢ Nat :=
  C.normalForm.quotientIso

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

namespace FixedTuple

/-- Fixed-length tuples of natural-number codes. -/
abbrev Tuple (n : Nat) : Type :=
  Fin n → Nat

/-- A tuple is sorted when entries are nondecreasing in the `Fin` index. -/
def Sorted {n : Nat} (t : Tuple n) : Prop :=
  ∀ i j, i.val ≤ j.val → t i ≤ t j

/-- Sorted fixed-length tuples, intended as the structural carrier for
duplicate-aware orbit representatives. -/
abbrev SortedTuple (n : Nat) : Type :=
  {t : Tuple n // Sorted t}

/-- A concrete permutation of `Fin n`, kept project-local rather than importing
mathlib's permutation hierarchy. -/
structure Perm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

namespace Perm

def actTuple {n : Nat} (p : Perm n) (t : Tuple n) : Tuple n :=
  fun i => t (p.invFun i)

end Perm

/-- A finite permutation group action on fixed-length tuples. The group laws
are stated in terms of the induced tuple action, which is the exact structure
needed to make the orbit relation a setoid. -/
structure PermFamily (n : Nat) where
  Elem : Type u
  size : Nat
  elemCode : Elem ≃ᵢ Fin size
  perm : Elem → Perm n
  id : Elem
  inv : Elem → Elem
  mul : Elem → Elem → Elem
  act_id : ∀ t : Tuple n, (perm id).actTuple t = t
  act_inv :
    ∀ (g : Elem) (t : Tuple n),
      (perm (inv g)).actTuple ((perm g).actTuple t) = t
  act_mul :
    ∀ (g h : Elem) (t : Tuple n),
      (perm (mul h g)).actTuple t =
        (perm h).actTuple ((perm g).actTuple t)

namespace PermFamily

def action {n : Nat} (G : PermFamily n) : FiniteAction (Tuple n) where
  Elem := G.Elem
  size := G.size
  elemCode := G.elemCode
  act := fun g t => (G.perm g).actTuple t

def OrbitRel {n : Nat} (G : PermFamily n) (t u : Tuple n) : Prop :=
  ∃ g : G.Elem, (G.perm g).actTuple t = u

end PermFamily

/--
Duplicate-aware residual image data for a sorted tuple. `Image` is the
concrete finite residual index type: it must index distinct images after
identifying group elements that act the same because tuple entries are equal.
-/
structure ResidualImageData {n : Nat} (G : PermFamily n)
    (s : SortedTuple n) where
  Image : Type u
  imageSize : Nat
  imageCode : Image ≃ᵢ Fin imageSize
  tupleOf : Image → Tuple n
  tupleOf_mem :
    ∀ r, ∃ g : G.Elem, tupleOf r = (G.perm g).actTuple s.val
  tupleOf_complete :
    ∀ g : G.Elem, ∃ r, tupleOf r = (G.perm g).actTuple s.val
  tupleOf_injective :
    ∀ {r r'}, tupleOf r = tupleOf r' → r = r'

/--
Data required to turn finite permutation orbits on fixed-length tuples into a
concrete code.  The residual image data is where duplicate-sensitive stabilizer
handling lives: for each sorted tuple, it indexes distinct images, not raw
group elements.
-/
structure OrbitCodingData (n : Nat) (G : PermFamily n) where
  sortedCode : SortedTuple n ≃ᵢ Nat
  residual : (s : SortedTuple n) → ResidualImageData G s
  residualSigmaCode :
    (Σ s : SortedTuple n, (residual s).Image) ≃ᵢ Nat
  normalize : Tuple n → Σ s : SortedTuple n, (residual s).Image
  denormalize : (Σ s : SortedTuple n, (residual s).Image) → Tuple n
  normalize_respects :
    ∀ {t u : Tuple n}, PermFamily.OrbitRel G t u → normalize t = normalize u
  denormalize_normalize_rel :
    ∀ t, PermFamily.OrbitRel G (denormalize (normalize t)) t
  normalize_denormalize :
    ∀ c, normalize (denormalize c) = c

/-- Orbit coding data for a finite permutation group action produces a concrete
code for the quotient by that action. -/
def orbitCodingData_toConcreteActionCode
    {n : Nat} {G : PermFamily n} (D : OrbitCodingData n G) :
    ConcreteActionCode G.action where
  Rel := PermFamily.OrbitRel G
  rel_refl := by
    intro t
    exact ⟨G.id, G.act_id t⟩
  rel_symm := by
    intro t u htu
    rcases htu with ⟨g, hg⟩
    refine ⟨G.inv g, ?_⟩
    rw [← hg]
    exact G.act_inv g t
  rel_trans := by
    intro t u v htu huv
    rcases htu with ⟨g, hg⟩
    rcases huv with ⟨h, hh⟩
    refine ⟨G.mul h g, ?_⟩
    calc
      (G.perm (G.mul h g)).actTuple t
          = (G.perm h).actTuple ((G.perm g).actTuple t) := G.act_mul g h t
      _ = (G.perm h).actTuple u := by rw [hg]
      _ = v := hh
  Canon := Σ s : SortedTuple n, (D.residual s).Image
  code := D.residualSigmaCode
  normalize := D.normalize
  denormalize := D.denormalize
  normalize_respects := D.normalize_respects
  denormalize_normalize_rel := D.denormalize_normalize_rel
  normalize_denormalize := D.normalize_denormalize
  action_sound := by
    intro g t
    exact ⟨G.inv g, G.act_inv g t⟩

end FixedTuple

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

def action : FiniteAction (Nat × Nat) where
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

def quotientCode : ConcreteQuotientCode (Nat × Nat) :=
  ConcreteQuotientCode.ofNormalizer
    CodeAlgebra.unorderedPairNat normalize denormalize normalize_denormalize

def concreteCode : ConcreteActionCode action where
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

end TupleAction
end BijForm
