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
Build an output-index inversion from constructor-local parameter codes.

For each constructor `ctor` and target output index `i`, `ParamCode ctor i`
codes exactly the parameters whose output is `i`.  This constructor owns the
assembly of those local preimages into full `Fiber` decode/encode laws.
-/
def ofConstructorParamCodes {P : DepPoly ι}
    (ParamCode : P.Ctor → ι → Type u)
    (decodeParam :
      ∀ {ctor : P.Ctor} {i : ι},
        ParamCode ctor i → { param : P.Param ctor // P.out ctor param = i })
    (encodeParam :
      ∀ {ctor : P.Ctor} {i : ι},
        { param : P.Param ctor // P.out ctor param = i } → ParamCode ctor i)
    (decodeParam_encodeParam :
      ∀ {ctor : P.Ctor} {i : ι}
        (param : { param : P.Param ctor // P.out ctor param = i }),
        decodeParam (encodeParam param) = param)
    (encodeParam_decodeParam :
      ∀ {ctor : P.Ctor} {i : ι} (code : ParamCode ctor i),
        encodeParam (decodeParam code) = code) :
    OutputIndexInversion P where
  Code := fun i => Σ ctor : P.Ctor, ParamCode ctor i
  decode := fun i code =>
    let decoded := decodeParam (ctor := code.1) (i := i) code.2
    ⟨code.1, decoded.1, decoded.2⟩
  encode := fun i f =>
    ⟨f.ctor, encodeParam (ctor := f.ctor) (i := i) ⟨f.param, f.out_eq⟩⟩
  decode_encode := by
    intro i f
    cases f with
    | mk ctor param out_eq =>
        dsimp
        have h :
            decodeParam
              (ctor := ctor) (i := i)
              (encodeParam (ctor := ctor) (i := i) ⟨param, out_eq⟩) =
                ⟨param, out_eq⟩ :=
          decodeParam_encodeParam (ctor := ctor) (i := i) ⟨param, out_eq⟩
        rw [h]
  encode_decode := by
    intro i c
    cases c with
    | mk ctor code =>
        dsimp
        change
          (⟨ctor, encodeParam (decodeParam code)⟩ :
            Σ ctor : P.Ctor, ParamCode ctor i) = ⟨ctor, code⟩
        rw [encodeParam_decodeParam (ctor := ctor) (i := i) code]

def fiberIso {P : DepPoly ι} (H : OutputIndexInversion P) (i : ι) :
    H.Code i ≃ᵢ Fiber P i where
  toFun := H.decode i
  invFun := H.encode i
  left_inv := H.encode_decode i
  right_inv := H.decode_encode i

end OutputIndexInversion

end DepPoly

end BijForm
