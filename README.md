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

- `BijForm.StringDiagram`
  Defines typed ordered-port rooted open string-diagram syntax, unoriented and
  oriented signature builders, its dependent polynomial presentation, the
  generated-code isomorphism, and the unfinished semantic bridge to open
  endpoint/edge/node port-hypergraphs up to ordered-boundary-preserving
  isomorphism:
  - `StringDiagram.Signature`
  - `StringDiagram.Unoriented.signature`
  - `StringDiagram.Oriented.signature`
  - `StringDiagram.Diag`
  - `StringDiagram.poly`
  - `StringDiagram.generatedCode`
  - `StringDiagram.syntaxIso`
  - `StringDiagram.RenderState`
  - `StringDiagram.Diag.connectStep`
  - `StringDiagram.Diag.budStep`
  - `StringDiagram.Diag.freshNodeEndpoints_get`
  - `StringDiagram.Diag.freshNodeEndpoints_mem_lt`
  - `StringDiagram.Diag.freshNodeEndpoints_mem_ge`
  - `StringDiagram.Diag.freshNodeEndpoints_mem_of_bounds`
  - `StringDiagram.Diag.freshNodeEndpoints_nodup`
  - `StringDiagram.Diag.freshNodeEndpoints_label_append`
  - `StringDiagram.Diag.connectStep_validIds`
  - `StringDiagram.Diag.connectStep_endpointPartition`
  - `StringDiagram.Diag.connectStep_nodeIncidentNodup`
  - `StringDiagram.Diag.connectStep_ownerIdPartition`
  - `StringDiagram.Diag.connectStep_edge_mem_old`
  - `StringDiagram.Diag.connectStep_node_mem_old`
  - `StringDiagram.Diag.connectStep_node_mem_old_of_child`
  - `StringDiagram.Diag.connectStep_frontier_mem_old`
  - `StringDiagram.Diag.connectStep_rawReachesBoundary_of_old`
  - `StringDiagram.Diag.connectStep_reachability`
  - `StringDiagram.Diag.budStep_validIds`
  - `StringDiagram.Diag.budStep_endpointPartition`
  - `StringDiagram.Diag.budStep_nodeIncidentNodup`
  - `StringDiagram.Diag.budStep_ownerIdPartition`
  - `StringDiagram.Diag.budStep_endpoints`
  - `StringDiagram.Diag.renderTraceFromBoundary`
  - `StringDiagram.Diag.renderTrace_endpointPrefix`
  - `StringDiagram.Diag.renderTraceFromBoundary_endpointPrefix`
  - `StringDiagram.Diag.renderTrace_validIds`
  - `StringDiagram.Diag.renderTrace_endpointPartition`
  - `StringDiagram.Diag.renderTrace_nodeIncidentNodup`
  - `StringDiagram.Diag.renderTrace_ownerIdPartition`
  - `StringDiagram.Diag.renderTraceFromBoundary_validIds`
  - `StringDiagram.Diag.renderTraceFromBoundary_endpointPartition`
  - `StringDiagram.Diag.renderTraceFromBoundary_nodeIncidentNodup`
  - `StringDiagram.Diag.renderTraceFromBoundary_ownerIdPartition`
  - `StringDiagram.Diag.renderTraceFromBoundary_endpointEdgeEvidence`
  - `StringDiagram.Diag.renderTraceFromBoundary_endpointEdge`
  - `StringDiagram.Diag.renderTraceFromBoundary_endpoint_edge_label`
  - `StringDiagram.Diag.renderTraceFromBoundary_edgeEvidence`
  - `StringDiagram.Diag.renderTraceFromBoundary_boundaryEvidence`
  - `StringDiagram.Diag.renderTraceFromBoundary_incidenceEvidence`
  - `StringDiagram.Diag.renderTraceFromBoundary_graphEvidence`
  - `StringDiagram.nodup_append_left`
  - `StringDiagram.nodup_append_right`
  - `StringDiagram.nodup_append_disjoint`
  - `StringDiagram.RenderState.ValidIds`
  - `StringDiagram.RenderState.edgeEndpointIds`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_tail_nodup`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_left_not_tail`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_right_not_tail`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_mem_left`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_mem_right`
  - `StringDiagram.RenderState.edgeEndpointIdsOfEdges_get_left_ne_right`
  - `StringDiagram.RenderState.edgeEndpointRefOfEndpointId`
  - `StringDiagram.RenderState.edgeEndpointRefOfEndpointId_unique`
  - `StringDiagram.RenderState.EndpointPartition`
  - `StringDiagram.RenderState.NodeIncidentNodup`
  - `StringDiagram.RenderState.nodeIncidentIds`
  - `StringDiagram.RenderState.ownerEndpointIds`
  - `StringDiagram.RenderState.OwnerIdPartition`
  - `StringDiagram.RenderState.OwnerIdPartition.boundaryIds_nodup`
  - `StringDiagram.RenderState.OwnerIdPartition.nodeIncidentIds_nodup`
  - `StringDiagram.RenderState.OwnerIdPartition.boundary_nodeIncidentIds_disjoint`
  - `StringDiagram.RenderState.EndpointPrefix`
  - `StringDiagram.RenderState.BoundaryEvidence`
  - `StringDiagram.RenderState.boundaryEvidenceOfPrefix`
  - `StringDiagram.RenderState.boundaryEvidenceOfPrefix_boundaryPort_val`
  - `StringDiagram.RenderState.boundaryEvidenceOfPrefix_exists_of_boundary_id`
  - `StringDiagram.RenderState.initial_validIds`
  - `StringDiagram.RenderState.initial_endpointPartition`
  - `StringDiagram.RenderState.initial_nodeIncidentNodup`
  - `StringDiagram.RenderState.initial_ownerIdPartition`
  - `StringDiagram.RenderState.EndpointPartition.endpoint_consumed_of_frontier_empty`
  - `StringDiagram.RenderState.endpointEdgeOfPartition`
  - `StringDiagram.RenderState.endpointEdgeOfPartition_endpoint`
  - `StringDiagram.RenderState.endpointEdgeOfPartition_label`
  - `StringDiagram.RenderState.endpointEdgeOfPartition_eq_of_endpoint_side`
  - `StringDiagram.RenderState.endpointEdgeOfPartition_left`
  - `StringDiagram.RenderState.endpointEdgeOfPartition_right`
  - `StringDiagram.RenderState.edge_left_ne_right_of_partition`
  - `StringDiagram.RenderState.edgeCompatibleOfPartition`
  - `StringDiagram.RenderState.edgeTwoEndpointsOfPartition`
  - `StringDiagram.RenderState.EndpointEdgeEvidence`
  - `StringDiagram.RenderState.endpointEdgeEvidenceOfPartition`
  - `StringDiagram.RenderState.EdgeEvidence`
  - `StringDiagram.RenderState.edgeEvidenceOfPartition`
  - `StringDiagram.RenderState.incidentOfValidIds`
  - `StringDiagram.RenderState.incidentOfValidIds_val_mem_nodeIncidentIds`
  - `StringDiagram.RenderState.incidentOfValidIds_exists_of_mem_nodeIncidentIds`
  - `StringDiagram.RenderState.incidentOfValidIds_length`
  - `StringDiagram.RenderState.incidentOfValidIds_injective`
  - `StringDiagram.RenderState.incidentOfValidIds_label`
  - `StringDiagram.RenderState.boundaryEvidenceOfPrefix_ne_incidentOfValidIds`
  - `StringDiagram.RenderState.nodeIncidentIds_get_node_eq_of_nodup`
  - `StringDiagram.RenderState.incidentOfValidIds_eq_node_eq`
  - `StringDiagram.RenderState.IncidenceEvidence`
  - `StringDiagram.RenderState.incidenceEvidenceOfValidIds`
  - `StringDiagram.RenderState.ValidIds.frontier_head_label`
  - `StringDiagram.RenderState.ValidIds.frontier_tail_label`
  - `StringDiagram.RenderState.RawReachesBoundary`
  - `StringDiagram.RenderState.RawReachesBoundary.mono`
  - `StringDiagram.RenderState.Reachability`
  - `StringDiagram.RenderState.initial_reachability`
  - `StringDiagram.RenderState.PortHypergraphEvidence`
  - `StringDiagram.RenderState.portHypergraphEvidenceOfInvariants`
  - `StringDiagram.RenderState.OpenPortHypergraphEvidence`
  - `StringDiagram.Diag.renderTraceFromBoundary_openEvidence` (unfinished proof gap)
  - `StringDiagram.Diag.toOpenPortHypergraph_unfinished` (depends on unfinished renderer validity)
  - `StringDiagram.EndpointOwner`
  - `StringDiagram.PortHypergraph`
  - `StringDiagram.PortHypergraph.endpointOwnersOf`
  - `StringDiagram.PortHypergraph.endpointOwnersOf_existsUnique`
  - `StringDiagram.PortHypergraph.EdgeMate`
  - `StringDiagram.PortHypergraph.EdgeMateData`
  - `StringDiagram.PortHypergraph.edgeMateCandidate?`
  - `StringDiagram.PortHypergraph.edgeMateSearch?`
  - `StringDiagram.PortHypergraph.edgeMate_existsUnique`
  - `StringDiagram.PortHypergraph.incident_nodup`
  - `StringDiagram.PortHypergraph.incident_labels`
  - `StringDiagram.PortHypergraph.incident_labels_except`
  - `StringDiagram.PortHypergraph.PortReachesBoundary`
  - `StringDiagram.OpenPortHypergraph`
  - `StringDiagram.OpenPortHypergraph.TraversalState`
  - `StringDiagram.OpenPortHypergraph.TraversalState.FrontierComplete`
  - `StringDiagram.OpenPortHypergraph.SearchState`
  - `StringDiagram.OpenPortHypergraph.SearchState.initial`
  - `StringDiagram.OpenPortHypergraph.SearchState.initial_frontierComplete`
  - `StringDiagram.OpenPortHypergraph.SearchState.processedEdges_length_le`
  - `StringDiagram.OpenPortHypergraph.SearchState.remainingEdges`
  - `StringDiagram.OpenPortHypergraph.SearchState.processedEdges_length_lt_of_pending`
  - `StringDiagram.OpenPortHypergraph.SearchState.connectChild`
  - `StringDiagram.OpenPortHypergraph.SearchState.connectChild_frontierComplete`
  - `StringDiagram.OpenPortHypergraph.SearchState.connectChild_remainingEdges_lt`
  - `StringDiagram.OpenPortHypergraph.SearchState.budChild`
  - `StringDiagram.OpenPortHypergraph.SearchState.budChild_frontierComplete`
  - `StringDiagram.OpenPortHypergraph.SearchState.budChild_remainingEdges_lt`
  - `StringDiagram.PortHypergraphIso`
  - `StringDiagram.OpenPortHypergraphUpToIso`
  - `StringDiagram.OpenPortHypergraph.FirstPendingStep`
  - `StringDiagram.OpenPortHypergraph.FirstPendingTraversalReady`
  - `StringDiagram.OpenPortHypergraph.firstPendingConnectSearch?`
  - `StringDiagram.OpenPortHypergraph.SearchState.firstPendingStepSearch?`
  - `StringDiagram.OpenPortHypergraph.SearchState.firstPendingStepSearch?_exists_of_frontierComplete`
  - `StringDiagram.OpenPortHypergraph.SearchState.toDiag`
  - `StringDiagram.OpenPortHypergraph.fromGraph`
  - `StringDiagram.OpenPortHypergraph.SearchState.GraphExhausted`
  - `StringDiagram.OpenPortHypergraph.SearchState.pending_ne_nil_of_reachable_unprocessed`
  - `StringDiagram.OpenPortHypergraph.SearchState.allNodesSeen_of_pending_nil`
  - `StringDiagram.OpenPortHypergraph.SearchState.allEdgesProcessed_of_pending_nil`
  - `StringDiagram.OpenPortHypergraph.SearchState.graphExhausted_of_pending_nil`
  - `StringDiagram.OpenPortHypergraph.SearchState.pending_eq_nil_of_empty_frontier`
  - `StringDiagram.OpenPortHypergraph.SearchState.graphExhausted_of_empty_frontier`
  - `StringDiagram.OpenPortHypergraph.firstPendingTraversalReady_of_frontierComplete`
  - `StringDiagram.diagOpenPortHypergraphIso` (unfinished proof gap)

- `BijForm.Examples`
  Imports the worked example modules:
  - `BijForm.Examples.HBT`
  - `BijForm.Examples.HBTQuotient`
  - `BijForm.Examples.Sorted`
  - `BijForm.Examples.FinChain`
  - `BijForm.Examples.Lambda`
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

Module: `BijForm.TypedBinding`

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
- `TypedBinding.LayerShape` and `TypedBinding.CtorLayer` generate the
  one-step variable/constructor layer shape from the signature.
- `TypedBinding.LayerShapeCodingData` packages carrier codings from that
  generated layer shape, so instances do not supply a raw `CodeLayer`
  equivalence.

### Typed Binding Normal Forms

Module: `BijForm.Examples.TypedBinding.NF`

The normal-form lambda signature is instantiated with normal-expression and
application-term indices. Its generated code family uses `Nat` for normal
expressions and `Fin (appTermCount Γ) × Nat` for application terms in context
`Γ`, so the closed application-term fiber is empty while closed normal
expressions still code to `Nat`.

Main results for this instance:

- `BijForm.Examples.TypedBinding.NFLayerShapeCodingData : BijForm.TypedBinding.LayerShapeCodingData BijForm.Examples.TypedBinding.NFSignature`
- `BijForm.Examples.TypedBinding.NFSyntaxCodeIso (Γ) (t) : Iso (BijForm.Examples.TypedBinding.NFTerm Γ t) (BijForm.Examples.TypedBinding.NFCode (Γ, t))`
- `BijForm.Examples.TypedBinding.NormalExpNatIso (Γ) : Iso (BijForm.Examples.TypedBinding.NormalExp Γ) Nat`
- `BijForm.Examples.TypedBinding.AppTermCodeIso (Γ) : Iso (BijForm.Examples.TypedBinding.AppTerm Γ) (Fin (BijForm.Examples.TypedBinding.appTermCount Γ) x Nat)`
- `BijForm.Examples.TypedBinding.NFClosedNatIso : Iso BijForm.Examples.TypedBinding.NFClosed Nat`
- `BijForm.Examples.TypedBinding.NFCode_normalExp_carrier (Γ) : BijForm.Examples.TypedBinding.NFCode (Γ, normalExp) = Nat`
- `BijForm.Examples.TypedBinding.NFCode_appTerm_carrier (Γ) : BijForm.Examples.TypedBinding.NFCode (Γ, appTerm) = Fin (BijForm.Examples.TypedBinding.appTermCount Γ) x Nat`
- `BijForm.Examples.TypedBinding.ClosedAppTermEmptyIso : Iso (BijForm.Examples.TypedBinding.AppTerm []) Empty`

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
