# BijForm

BijForm is a Lean 4 development of bijective encodings for indexed inductive
data. The repository has three main themes:

- a proved natural-number pairing function, including a faster closed-form
  decoder proved equivalent to the original shell-scanning decoder;
- a framework for deriving bijections for dependent-polynomial initial
  algebras from explicit one-layer coding data and a well-founded decoding
  measure;
- quotient and string-diagram examples that compose the generic coding
  framework instead of hand-writing final encoders.

The examples are meant to start from readable reference syntax, identify the
dependent-polynomial presentation, prove the syntax isomorphic to the initial
algebra, instantiate generated coding data, and then compose those pieces into
actual encodings.

## Build

This project uses Lean 4 through Lake.

```sh
lake build
```

Repository policy checks are bundled with the audit executable:

```sh
lake --dir "$(git rev-parse --show-toplevel)" exe audit
```

The Lean toolchain is pinned in `lean-toolchain`:

```text
leanprover/lean4:v4.28.0
```

The default executable is a small smoke-test-style program:

```sh
lake exe bijform
```

## Repository Layout

Core coding utilities live in BijForm.Coding, BijForm.FiniteSubtypeTable,
BijForm.Pairing, BijForm.CodeAlgebra, and BijForm.DependentTuple. These modules
define the project-local isomorphism type, finite carrier tables, pairing and
sum/product encodings, and tuple helpers used by generated code.

Dependent-polynomial and initial-algebra infrastructure lives in
BijForm.DependentPolynomial and BijForm.InitialAlgebra. These modules define
polynomial signatures, fibers, output-index inversions, initial algebras,
layer presentations, generated code, generated Nat code, ranked Nat code, and
shape code.

Quotient infrastructure lives in BijForm.QuotientPolynomial and
BijForm.TupleAction. The quotient-polynomial layer presents quotient datatypes
as quotients of generated code families, while the tuple-action layer provides
normal-form and finite-action coding data used by quotient examples.

String-diagram infrastructure is split under BijForm.StringDiagram. Basic
syntax and signatures live in the basic and polynomial modules; rendering,
hypergraph semantics, traversal, bridge proofs, and finite coding live in the
Renderer, Hypergraph, Traversal, Bridge, and FiniteCoding subtrees. The
aggregate BijForm.StringDiagram module re-exports the intended public surface.

Worked examples live under BijForm.Examples. The examples currently cover
height-bounded trees, branch-swap quotients, sorted trees, bounded finite
chains, lambda terms, numeric expressions, Peano formulas, typed-binding normal
forms, and finite string-diagram encodings for symmetric interaction nets.

## Generated Coding

The reusable coding path starts with a same-fiber one-layer coding. A
well-founded code supplies a rank showing that every child decoded from one
layer is smaller than its parent. Generated code factors this through explicit
output-index inversion and a code layer, so constructor-level fiber changes are
visible rather than hidden behind an opaque equivalence.

Layer presentations are the canonical owner for generated layer coding data.
Syntax, Nat, ranked-Nat, and shape presentations are views over that same
layer/rank/descent structure. Shape code records visible carrier shapes such as
Nat, Fin k, or index-dependent products, while still storing generated-code
evidence in the canonical generated-code record.

## Quotient Coding

A quotient presentation gives constructor-layer equations for a dependent
polynomial. The generated quotient relation closes those equations under
recursive congruence, symmetry, and transitivity on the initial algebra.

Existing generated code can be transported across that quotient relation. The
code-side carrier is the quotient of the generated code family by the
transported relation. A descended code criterion then replaces that quotient
carrier with a concrete carrier when a normalizer and denormalizer respect the
relation and are inverse in the quotient sense.

Tuple-action code supplies reusable normal-form data for finite action orbits.
The binary-swap instance codes unordered pairs by sorted representatives and
is used by the height-bounded-tree branch-swap quotient.

## String Diagrams

String-diagram syntax is represented as ordered-frontier traversal syntax over
typed signatures. The semantic bridge renders syntax to open port-hypergraphs
and reconstructs syntax from ordered boundary-preserving hypergraphs. Finite
single-sorted coding derives branch tables from finite node data and produces
the empty-frontier Fin 1 case and nonempty-frontier Nat case generically.

The symmetric interaction-net example instantiates this finite string-diagram
coding path with erasure, duplication, and cons nodes, then composes the syntax
coding with the semantic open-graph quotient bridge.

## Examples

Height-bounded trees demonstrate ordinary generated Nat coding and a
branch-swap quotient whose quotient carrier descends to Nat through a
normalizer.

Sorted trees demonstrate index-dependent carrier shapes: valid intervals code
to Nat, while invalid finite intervals collapse to a singleton finite carrier.

Bounded tagged chains demonstrate finite shape carriers whose size depends on
the index.

Lambda terms demonstrate ranked Nat coding where decoding at an empty context
must avoid unavailable variable constructors.

Numeric expressions and Peano formulas demonstrate dependent examples where
Peano formulas reuse the generated numeric encoding inside a larger indexed
language.

Typed-binding normal forms demonstrate generated coding for a reusable
typed-binding signature framework. Normal expressions code to Nat, while
application terms use an index-dependent product whose closed application-term
fiber is empty.

Symmetric interaction nets demonstrate finite string-diagram coding and its
composition with the open-graph semantic quotient.

## Validation Policy

Lean source is the authoritative formalization surface. README prose is only
orientation; exact declaration inventories should be read from the source with
Lean or source-search tooling.

Committed `sorry` declarations are allowed only as honest unfinished
blueprinting, pending proof work, or proof-gap markers. They must not be
reported as completed proofs. The audit command checks for forbidden proof
substitutes, unclassified `sorry`, ignored reference material, and repository
specific policy invariants.
