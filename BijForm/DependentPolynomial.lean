import BijForm.Coding

namespace BijForm

/-
This file develops the dependent-polynomial container layer used by the coding
framework. The key design requirement is to make constructor-fiber data explicit
rather than hide the hard part behind an opaque constructor isomorphism:

* constructors are presented as dependent polynomial containers over an index
  type `ι`;
* a constructor may compute its output index by a map `out`;
* `OutputIndexInversion` supplies, for each target index, a fiberwise inverse
  description of the parameters whose `out` lands there.

Initial algebra and generated-coding constructions over these containers live in
`BijForm.InitialAlgebra`.
-/

universe u v

/-- A dependent polynomial signature whose recursive positions may point at
indices computed from the constructor parameter. -/
structure DepPoly (ι : Type u) where
  Ctor : Type u
  Param : Ctor → Type u
  out : (c : Ctor) → Param c → ι
  Pos : (c : Ctor) → Param c → Type u
  input : {c : Ctor} → (p : Param c) → Pos c p → ι

namespace DepPoly

variable {ι : Type u}

/-- One layer of constructor data over a family `X`. -/
structure Obj (P : DepPoly ι) (X : ι → Type v) (i : ι) where
  ctor : P.Ctor
  param : P.Param ctor
  out_eq : P.out ctor param = i
  child : (q : P.Pos ctor param) → X (P.input param q)

/-- A same-fiber polynomial presentation: constructors for index `i` already
include the evidence that their output is `i`. -/
structure Fiber (P : DepPoly ι) (i : ι) where
  ctor : P.Ctor
  param : P.Param ctor
  out_eq : P.out ctor param = i

namespace Fiber

/--
Two same-fiber constructor records with the same constructor are equal once
their parameters are equal; the output-index proofs are proposition fields.
-/
theorem eq_mk_of_param_eq {P : DepPoly ι} {i : ι} {ctor : P.Ctor}
    {param param' : P.Param ctor}
    {out_eq : P.out ctor param = i} {out_eq' : P.out ctor param' = i}
    (hparam : param = param') :
    ({ ctor := ctor, param := param, out_eq := out_eq } : Fiber P i) =
      { ctor := ctor, param := param', out_eq := out_eq' } := by
  rw [Fiber.mk.injEq]
  constructor
  · rfl
  · cases hparam
    rfl

end Fiber

/--
Index-local constructor data for each output fiber. This structure records the
same-fiber representation used by later layer-coding definitions; by itself it
is not a completed solution to constructor-code generation.
-/
structure OutputIndexInversion (P : DepPoly ι) where
  Code : ι → Type u
  decode : (i : ι) → Code i → Fiber P i
  encode : (i : ι) → Fiber P i → Code i
  decode_encode : ∀ i f, decode i (encode i f) = f
  encode_decode : ∀ i c, encode i (decode i c) = c

namespace OutputIndexInversion

/-- The canonical same-fiber inversion: the code for each output index is the
fiber itself.  This is the generated default when no smaller constructor-code
presentation is needed. -/
def canonical (P : DepPoly ι) : OutputIndexInversion P where
  Code := Fiber P
  decode := fun _ f => f
  encode := fun _ f => f
  decode_encode := by
    intro _ _
    rfl
  encode_decode := by
    intro _ _
    rfl

/--
Low-level constructor for output-index inversion from caller-supplied fiber
equivalences.  Examples should prefer concrete generated inversion data, such
as `canonical` or reusable index-change constructors, so the construction of
same-fiber data remains visible.
-/
def ofIso {P : DepPoly ι} (Code : ι → Type u)
    (e : ∀ i, Code i ≃ᵢ Fiber P i) : OutputIndexInversion P where
  Code := Code
  decode := fun i c => (e i).toFun c
  encode := fun i f => (e i).invFun f
  decode_encode := by
    intro i f
    exact (e i).right_inv f
  encode_decode := by
    intro i c
    exact (e i).left_inv c

def fiberIso {P : DepPoly ι} (H : OutputIndexInversion P) (i : ι) :
    H.Code i ≃ᵢ Fiber P i where
  toFun := H.decode i
  invFun := H.encode i
  left_inv := H.encode_decode i
  right_inv := H.decode_encode i

end OutputIndexInversion

end DepPoly

end BijForm
