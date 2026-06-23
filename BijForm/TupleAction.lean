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

def reindex {Raw : Type u} {Raw' : Type w} (A : FiniteAction Raw)
    (e : Raw' ≃ᵢ Raw) : FiniteAction Raw' where
  Elem := A.Elem
  size := A.size
  elemCode := A.elemCode
  act := fun g x => e.invFun (A.act g (e.toFun x))

end FiniteAction

/-- Concrete quotient coding for a finite action. `action_sound` records that
every action step is included in the quotient relation being normalized. -/
structure ConcreteActionCode {Raw : Type u} (A : FiniteAction Raw) extends
    ConcreteQuotientCode Raw where
  action_sound : ∀ g x, Rel (A.act g x) x

namespace ConcreteQuotientCode

def reindex {Raw : Type u} {Raw' : Type w} (C : ConcreteQuotientCode Raw)
    (e : Raw' ≃ᵢ Raw) : ConcreteQuotientCode Raw' where
  Rel x y := C.Rel (e.toFun x) (e.toFun y)
  rel_refl := by
    intro x
    exact C.rel_refl (e.toFun x)
  rel_symm := by
    intro x y hxy
    exact C.rel_symm hxy
  rel_trans := by
    intro x y z hxy hyz
    exact C.rel_trans hxy hyz
  Canon := C.Canon
  code := C.code
  normalize := fun x => C.normalize (e.toFun x)
  denormalize := fun c => e.invFun (C.denormalize c)
  normalize_respects := by
    intro x y hxy
    exact C.normalize_respects hxy
  denormalize_normalize_rel := by
    intro x
    change C.Rel
      (e.toFun (e.invFun (C.denormalize (C.normalize (e.toFun x)))))
      (e.toFun x)
    rw [e.right_inv]
    exact C.denormalize_normalize_rel (e.toFun x)
  normalize_denormalize := by
    intro c
    change C.normalize (e.toFun (e.invFun (C.denormalize c))) = c
    rw [e.right_inv]
    exact C.normalize_denormalize c

end ConcreteQuotientCode

namespace ConcreteActionCode

def reindex {Raw : Type u} {Raw' : Type w} {A : FiniteAction Raw}
    (C : ConcreteActionCode A) (e : Raw' ≃ᵢ Raw) :
    ConcreteActionCode (A.reindex e) where
  toConcreteQuotientCode := C.toConcreteQuotientCode.reindex e
  action_sound := by
    intro g x
    change C.Rel
      (e.toFun (e.invFun (A.act g (e.toFun x))))
      (e.toFun x)
    rw [e.right_inv]
    exact C.action_sound g (e.toFun x)

end ConcreteActionCode

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
Duplicate-aware residual representative data for a sorted tuple. `Image` is
the concrete finite residual index type for canonical quotient representatives
inside the sorted fiber; it is not a list of all raw group images, because raw
images in the same action orbit must normalize to the same quotient code.
-/
structure ResidualImageData {n : Nat} (G : PermFamily n)
    (s : SortedTuple n) where
  Image : Type u
  imageSize : Nat
  imageCode : Image ≃ᵢ Fin imageSize
  tupleOf : Image → Tuple n

/--
Data required to turn finite permutation orbits on fixed-length tuples into a
concrete code.  The residual image data is where duplicate-sensitive stabilizer
handling lives: for each sorted tuple, it indexes canonical residual
representatives, not raw group elements or all raw group images.
-/
structure OrbitCodingData (n : Nat) (G : PermFamily n) where
  sortedCode : SortedTuple n ≃ᵢ Nat
  residual : (s : SortedTuple n) → ResidualImageData G s
  residualSigmaCode :
    (Σ s : SortedTuple n, (residual s).Image) ≃ᵢ Nat
  normalize : Tuple n → Σ s : SortedTuple n, (residual s).Image
  normalize_respects :
    ∀ {t u : Tuple n}, PermFamily.OrbitRel G t u → normalize t = normalize u
  denormalize_normalize_rel :
    ∀ t, PermFamily.OrbitRel G
      ((residual (normalize t).1).tupleOf (normalize t).2) t
  normalize_denormalize :
    ∀ c, normalize ((residual c.1).tupleOf c.2) = c

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
  denormalize := fun c => (D.residual c.1).tupleOf c.2
  normalize_respects := D.normalize_respects
  denormalize_normalize_rel := D.denormalize_normalize_rel
  normalize_denormalize := D.normalize_denormalize
  action_sound := by
    intro g t
    exact ⟨G.inv g, G.act_inv g t⟩

end FixedTuple

end TupleAction
end BijForm
