# BijForm

BijForm is a Lean 4 formalization of bijective encodings for indexed
inductive data. The repository has two main parts:

- a proved natural-number pairing function, including an optimized closed-form
  decoder proved equivalent to the shell-scanning decoder;
- a small framework for deriving bijections for dependent-polynomial initial
  algebras from explicit one-layer coding data and a well-founded decoding
  measure;
- a quotient-polynomial layer that characterizes encodings of quotient
  datatypes as quotients of generated code families.

The examples are organized to start from readable reference syntax families,
then define the dependent-polynomial presentation, prove the syntax isomorphic
to the polynomial initial algebra, and finally instantiate generated coding
machinery with either `Nat` codings or index-dependent finite/infinite code
families.

## Build

This project uses Lean 4 through Lake.

```sh
lake build
```

The Lean toolchain is pinned in `lean-toolchain`:

```text
leanprover/lean4:v4.28.0
```

The default executable is only a small smoke-test-style program:

```sh
lake exe bijform
```

## Module Map

- `BijForm.Coding`
  Defines the project-local `Iso` structure and basic iso combinators for
  reflexivity, symmetry, transitivity, products, and sums.

- `BijForm.Pairing`
  Defines and proves the shell-based pairing function on `Nat x Nat`.
  The main declarations are:
  - `Pairing.iso`
  - `Pairing.isoFast`
  - `Pairing.encodeFast_eq_encode`
  - `Pairing.decodeFast_eq_decode`

- `BijForm.CodeAlgebra`
  Provides small reusable bijections for code carriers, including finite sums,
  finite products, finite-prefix sums into `Nat`, binary and nested `Nat`
  sums, unordered pairs of natural numbers, and products via the proved
  pairing function.

- `BijForm.TupleAction`
  Provides the explicit coding surface for quotienting finite action orbits:
  - `TupleAction.ConcreteQuotientCode`
  - `TupleAction.FiniteAction`
  - `TupleAction.ConcreteActionCode`
  - `TupleAction.FixedTuple.Tuple`
  - `TupleAction.FixedTuple.SortedTuple`
  - `TupleAction.FixedTuple.Perm`
  - `TupleAction.FixedTuple.PermFamily`
  - `TupleAction.FixedTuple.ResidualImageData`
  - `TupleAction.FixedTuple.OrbitCodingData`
  - `TupleAction.FixedTuple.orbitCodingData_toConcreteActionCode`
  - `TupleAction.BinarySwap.concreteCode`
  - `TupleAction.BinarySwap.encode`
  - `TupleAction.BinarySwap.decode`

- `BijForm.DependentPolynomial`
  Defines dependent polynomial signatures, their initial algebras, and the
  generic coding framework:
  - `DepPoly`
  - `Mu`
  - `OutputIndexInversion`
  - `WellFoundedCode`
  - `GeneratedCode`
  - `GeneratedShapeCode`
  - `GeneratedRankedNatCode`
  - `GeneratedNatCode`
  - `initialAlgebraCoding`

- `BijForm.QuotientPolynomial`
  Defines quotient presentations for dependent-polynomial initial algebras and
  their algebra/coding surface:
  - `QuotientPresentation`
  - `QuotientPresentation.Rel`
  - `QuotientPresentation.setoid`
  - `QuotientPresentation.Carrier`
  - `QuotientPresentation.inn`
  - `QuotientPresentation.inn_layer_sound`
  - `QuotientPresentation.recCarrier`
  - `QuotientPresentation.ind`
  - `QuotientPresentation.CodeRel`
  - `QuotientPresentation.CodeCarrier`
  - `QuotientPresentation.codeIso`
  - `QuotientPresentation.DescendedCode`

- `BijForm.Examples`
  Imports the worked example modules:
  - `BijForm.Examples.HBT`
  - `BijForm.Examples.HBTQuotient`
  - `BijForm.Examples.Sorted`
  - `BijForm.Examples.FinChain`
  - `BijForm.Examples.Lambda`
  - `BijForm.Examples.TypedBinding`
  - `BijForm.Examples.TypedBinding.NF`
  - `BijForm.Examples.Num`
  - `BijForm.Examples.Peano`

## Generic Coding Framework

The central construction is `WellFoundedCode`. It packages:

- a one-step isomorphism `Obj P Code i` to `Code i`;
- a `rank : forall i, Code i -> Nat`;
- a proof that every child code produced by one-step decoding has smaller
  rank than the parent code.

This rank is a termination measure for generic decoding. It is not a Goedel
code and does not need to be injective.

`GeneratedCode` factors the one-step isomorphism through explicit
same-fiber constructor data:

```lean
OutputIndexInversion P
CodeLayer P inversion Code i
```

This is the reusable point where output-index inversion is exposed instead of
hidden behind an opaque constructor isomorphism.

`GeneratedNatCode` specializes the framework to the constant code family
`fun _ => Nat`; its termination measure is the identity rank on `Nat`, so it
requires recursive child codes to be numerically smaller than the parent code.

`GeneratedRankedNatCode` specializes the framework to the same `Nat` carrier
while allowing an index-sensitive rank `i -> Nat -> Nat`.

`GeneratedShapeCode` specializes the same generic layer construction to
carrier families whose fibers are explicitly shaped as either `Nat` or `Fin k`.

## Quotient-Polynomial Coding

`QuotientPresentation` records a constructor-layer quotient relation for a
dependent polynomial `P`. The generated relation `QuotientPresentation.Rel`
closes that layer relation under recursive congruence, symmetry, and
transitivity on `Mu P i`, and `QuotientPresentation.Carrier` is the resulting
quotient datatype.

`QuotientPresentation.inn` is the quotient-algebra constructor from a layer of
already quotiented children. `QuotientPresentation.recCarrier` descends a fold
out of `Mu P` when the fold respects the generated quotient relation, and
`QuotientPresentation.ind` provides quotient induction.

For any existing `WellFoundedCode P Code`, `QuotientPresentation.codeIso`
characterizes the quotient datatype's encoding as the quotient of `Code i` by
the transported relation `QuotientPresentation.CodeRel`. This gives quotient
examples a generic path from the polynomial presentation to a code carrier
without hand-writing a final encoder for the quotient.

`QuotientPresentation.DescendedCode` records the extra criterion needed to
replace that quotient code carrier by a concrete carrier: the concrete encoder
must respect the transported relation, and its decoder must be inverse up to
that relation.

`BijForm.TupleAction` supplies reusable finite-action coding data used to prove
those descent criteria. The completed binary-swap instance codes unordered
pairs by a sorted representative and handles duplicate entries without storing
a raw group element.

The fixed-length tuple-action API applies this to quotients of `Fin n -> Nat`
tuples by a finite permutation group action. `TupleAction.FixedTuple.PermFamily`
packages the finite action and the identity, inverse, and composition laws that
make the orbit relation a setoid. A concrete quotient code is then described by
`TupleAction.FixedTuple.OrbitCodingData`: each tuple is normalized to a sorted
representative together with a residual image index for that representative,
and `TupleAction.FixedTuple.ResidualImageData` requires that this residual type
enumerates the distinct group images of the sorted tuple. From that data,
`TupleAction.FixedTuple.orbitCodingData_toConcreteActionCode` constructs the
generic `ConcreteActionCode`. The current generic theorem consumes these
normalization and residual-indexing functions as explicit data. The repository
does not currently provide a practical non-enumerative synthesizer for arbitrary
finite permutation groups; broader automation should come from structured
classes of actions with their own canonicalization data.

## Examples

### Height-Bounded Trees

Reference syntax:

```lean
HBTSyntax : Nat -> Type
```

Polynomial presentation:

```lean
HBTPoly : DepPoly Nat
```

Main results:

- `HBTSyntaxIso (i) : Iso (Mu HBTPoly i) (HBTSyntax i)`
- `HBTNatGeneratedCode : GeneratedNatCode HBTPoly`
- `HBTSyntaxNatIso (i) : Iso (HBTSyntax i) Nat`

Branch-swap quotient example:

- `HBTChildSwapQuotient : QuotientPresentation HBTPoly`
- `HBTChildSwap_inn_branch_sound`
- `TupleAction.BinarySwap.concreteCode`
- `HBTChildSwapNatCodeIso (i) : Iso (HBTChildSwap i) (HBTChildSwapNatCode i)`
- `HBTChildSwapDescendedNatCode : QuotientPresentation.DescendedCode HBTChildSwapQuotient HBTNatGeneratedCode.toWellFoundedCode (fun _ => Nat)`
- `HBTChildSwapNatIso (i) : Iso (HBTChildSwap i) Nat`
- `HBTSyntaxChildSwapNatCodeIso (i) : Iso (HBTSyntaxChildSwap i) (HBTChildSwapNatCode i)`
- `HBTSyntaxChildSwapNatIso (i) : Iso (HBTSyntaxChildSwap i) Nat`

In source, the precise theorem type uses the local `Iso` notation.

### Sorted Trees

Reference syntax:

```lean
SortedSyntax : SortedIx -> Type
```

Sorted trees are indexed by lower and upper bounds. Branches carry an in-bounds
pivot and narrow the child bounds.

Main results:

- `SortedSyntaxIso (i) : Iso (Mu SortedPoly i) (SortedSyntax i)`
- `SortedGeneratedShapeCode : GeneratedShapeCode SortedPoly`
- `SortedSyntaxShapeIso (i) : Iso (SortedSyntax i) (SortedCarrier i)`
- `SortedSyntaxNatIsoOfBound (i) : Bound.le i.1 i.2 -> Iso (SortedSyntax i) Nat`
- `SortedSyntaxFinOneIsoOfNotBound (i) : not Bound.le i.1 i.2 -> Iso (SortedSyntax i) (Fin 1)`
- `SortedSyntaxInfiniteNatIso (lower) : Iso (SortedSyntax (lower, none)) Nat`
- `SortedSyntaxFiniteNatIso (lower upper) : lower <= upper -> Iso (SortedSyntax (lower, some upper)) Nat`
- `SortedSyntaxInvalidFiniteIso (lower upper) : not lower <= upper -> Iso (SortedSyntax (lower, some upper)) (Fin 1)`
- `SortedEmptySyntaxFinOneIso : Iso (SortedSyntax (1, some 0)) (Fin 1)`

The sorted carrier family uses `Nat` for valid intervals and `Fin 1` for the
empty invalid interval shown above.

### Bounded Tagged Chains

Reference syntax:

```lean
FinChainSyntax : Nat -> Type
```

Main results:

- `FinChainSyntaxIso (i) : Iso (Mu FinChainPoly i) (FinChainSyntax i)`
- `FinChainGeneratedShapeCode : GeneratedShapeCode FinChainPoly`
- `FinChainSyntaxFinIso (i) : Iso (FinChainSyntax i) (Fin (FinChainSize i))`

The first concrete cases are `Fin 1`, `Fin 3`, and `Fin 10`.

### Lambda Terms

Reference syntax:

```lean
LamSyntax : Nat -> Type
```

Lambda terms use de Bruijn contexts. At context `0`, variables are unavailable,
so the Nat layer decodes code `0` as `lam`, not `app`.

Main results:

- `LamSyntaxIso (k) : Iso (Mu LamPoly k) (LamSyntax k)`
- `LamNatGeneratedCode : GeneratedRankedNatCode LamPoly`
- `LamNatLayer_zero_invFun_zero`
- `LamSyntaxNatIso (k) : Iso (LamSyntax k) Nat`
- `ClosedLamSyntaxNatIso : Iso (LamSyntax 0) Nat`

### Typed Binding Signatures

Module: `BijForm.Examples.TypedBinding`

Generic syntax:

```lean
TypedBinding.Signature
TypedBinding.Term
```

Typed binding signatures describe constructor arguments by a list of newly
bound types and a recursive result type. Empty binder lists represent ordinary
nonbinding recursive arguments.

Main results:

- `TypedBinding.PolyOf (S) : DepPoly (List Ty x Ty)`
- `TypedBinding.inversion (S) : OutputIndexInversion (TypedBinding.PolyOf S)`
- `TypedBinding.syntaxIso (S) (Γ) (t) : Iso (Mu (TypedBinding.PolyOf S) (Γ, t)) (TypedBinding.Term S Γ t)`
- `TypedBinding.CodeCodingData` packages arbitrary index-dependent concrete
  carrier codings and layer-local rank proofs.
- `TypedBinding.LayerShape` and `TypedBinding.CtorLayer` generate the
  one-step variable/constructor layer shape from the signature.
- `TypedBinding.LayerShapeCodingData` packages carrier codings from that
  generated layer shape, so instances do not supply a raw `CodeLayer`
  equivalence.
- `TypedBinding.ShapeCodingData` packages the concrete one-step carrier coding
  and layer-local rank proof needed to obtain generated shape encodings.

### Typed Binding Normal Forms

Module: `BijForm.Examples.TypedBinding.NF`

The normal-form lambda signature is instantiated with normal-expression and
application-term indices. Its generated code family uses `Nat` for normal
expressions and `Fin (appTermCount Γ) × Nat` for application terms in context
`Γ`, so the closed application-term fiber is empty while closed normal
expressions still code to `Nat`.

Main results for this instance:

- `TypedBinding.NFCodeCodingData : TypedBinding.CodeCodingData TypedBinding.NFSignature`
- `TypedBinding.NFSyntaxCodeIso (Γ) (t) : Iso (TypedBinding.NFTerm Γ t) (TypedBinding.NFCode (Γ, t))`
- `TypedBinding.NormalExpNatIso (Γ) : Iso (TypedBinding.NormalExp Γ) Nat`
- `TypedBinding.AppTermCodeIso (Γ) : Iso (TypedBinding.AppTerm Γ) (Fin (TypedBinding.appTermCount Γ) x Nat)`
- `TypedBinding.NFClosedNatIso : Iso TypedBinding.NFClosed Nat`
- `TypedBinding.NFCode_normalExp_carrier (Γ) : TypedBinding.NFCode (Γ, normalExp) = Nat`
- `TypedBinding.NFCode_appTerm_carrier (Γ) : TypedBinding.NFCode (Γ, appTerm) = Fin (TypedBinding.appTermCount Γ) x Nat`
- `TypedBinding.ClosedAppTermEmptyIso : Iso (TypedBinding.AppTerm []) Empty`

### Numeric Expressions

Reference syntax:

```lean
NumSyntax : Nat -> Type
```

Main results:

- `NumSyntaxIso (k) : Iso (Mu NumPoly k) (NumSyntax k)`
- `NumNatGeneratedCode : GeneratedNatCode NumPoly`
- `NumSyntaxNatIso (k) : Iso (NumSyntax k) Nat`

### Peano Formulas

Reference syntax:

```lean
PeanoSyntax : Nat -> Type
```

Peano formulas are indexed by context size. Equality compares numeric terms in
the same context, negation and implication preserve context, and universal
quantification decodes a child formula in context `k + 1`.

Main results:

- `PeanoSyntaxIso (k) : Iso (Mu PeanoPoly k) (PeanoSyntax k)`
- `PeanoNatGeneratedCode : GeneratedNatCode PeanoPoly`
- `PeanoSyntaxNatIso (k) : Iso (PeanoSyntax k) Nat`
