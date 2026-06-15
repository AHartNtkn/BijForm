# BijForm

BijForm is a Lean 4 formalization of bijective encodings for indexed
inductive data. The repository has two main parts:

- a proved natural-number pairing function, including an optimized closed-form
  decoder proved equivalent to the shell-scanning decoder;
- a small framework for deriving bijections for dependent-polynomial initial
  algebras from explicit one-layer coding data and a well-founded decoding
  measure.

The examples are organized to start from readable reference syntax families,
then define the dependent-polynomial presentation, prove the syntax isomorphic
to the polynomial initial algebra, and finally instantiate generated coding
machinery where a `Nat` coding is valid.

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

- `BijForm.NatCoding`
  Provides small reusable bijections into `Nat`, including finite-prefix sums,
  binary and nested sums, and products via the proved pairing function.

- `BijForm.DependentPolynomial`
  Defines dependent polynomial signatures, their initial algebras, and the
  generic coding framework:
  - `DepPoly`
  - `Mu`
  - `OutputIndexInversion`
  - `WellFoundedCode`
  - `GeneratedLayerCode`
  - `GeneratedNatCode`
  - `initialAlgebraCoding`

- `BijForm.Examples`
  Contains the worked examples. Each example begins with the reference syntax
  family before the polynomial encoding.

## Generic Coding Framework

The central construction is `WellFoundedCode`. It packages:

- a one-step isomorphism `Obj P Code i` to `Code i`;
- a `rank : forall i, Code i -> Nat`;
- a proof that every child code produced by one-step decoding has smaller
  rank than the parent code.

This rank is a termination measure for generic decoding. It is not a Goedel
code and does not need to be injective.

`GeneratedLayerCode` factors the one-step isomorphism through explicit
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
- `noSortedNatGeneratedCode : GeneratedNatCode SortedPoly -> False`

The negative result is intentional. A global constant-`Nat` generated code for
all sorted-tree indices is impossible because some bounded intervals have only
one tree. The framework records this obstruction rather than pretending the
example has the same shape as the infinite-fiber examples.

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
