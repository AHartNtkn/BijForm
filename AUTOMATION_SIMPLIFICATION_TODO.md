# Automation Simplification TODO

This tracks remaining places where proof facts, wrapper constructors, or
branch-specific theorem stacks should be replaced by stronger generic automation
or reusable schemas. Items are not complete when proof work is merely moved to a
new helper name. An item is complete only when the listed deletion targets are
gone or are replaced by a clearly broader owner-level schema.

## Global Validation

Run after any implementation slice that closes items here:

```bash
lake build
rg -n '\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b' BijForm
rg -n 'rank_descent|typed_binding_rank_descent|quotient_rank_descent|theorem .*child_rank_lt|private theorem .*child_rank_lt|LayerShapeRankProof' BijForm README.md
rg -n 'LayerPresentation\.ofCarrierLayerIso|LayerPresentation\.ofLayerMaps|SyntaxPresentation\.ofLayerMaps|CodeLayerPresentation\.ofIso|GeneratedCode where|GeneratedShapeCode where|WellFoundedCode' BijForm/Examples
```

For every closed item, add a source scan that would fail if the old proof-owner
model reappears under a renamed theorem, wrapper, or compatibility alias.

## Required Proof-Debt Item Shape

Every proof-debt item below must keep these fields visible:

- Evidence: current source symbols or proof patterns preserving the wrong model.
- Owner: generic proof/schema boundary that should discharge the class.
- Delete or replace: concrete symbols, wrappers, or proof bodies that should
  disappear when the item is done.
- Validation: scan or command that would fail if the old model remains.

## Rank Descent And Layer Presentations

- [x] Replace the current `rank_descent` macro model with real structural rank
  schemas.
  Evidence: `BijForm/RankDescent.lean` has macros that destruct `idx`, `z`,
  `layer`, `ctor`, and `out_eq`, then rely on `simp_all!` and `omega`.
  Current consumers include `HBT_layer_child_rank_lt`,
  `Num_layer_child_rank_lt`, `Lam_layer_child_rank_lt`,
  `Peano_layer_child_rank_lt`, `FinChain_layer_child_rank_lt`,
  `Sorted_layer_child_rank_lt`, and `StringDiagram.Polynomial.layer_child_rank_lt`.
  Owner: `LayerPresentation` / structural syntax-rank schema.
  Delete or replace: current case-bash macro bodies and named example
  `*_layer_child_rank_lt` wrappers whose bodies are only `rank_descent`.
  Validation:
  ```bash
  rg -n 'theorem .*_layer_child_rank_lt|\brank_descent\b' BijForm/Examples BijForm/StringDiagram/Polynomial.lean
  ```

- [x] Collapse thin `LayerPresentation` transport constructors into one
  canonical decoded-layer descent interface.
  Evidence: `LayerPresentation.ofLayer`, `ofLayerMaps`,
  `ofLayerChildRank`, `ofLayerShapeChildRank`, `ofShapeChildRank`, and
  `ofCarrierLayerIso` mostly forward `child_rank_lt` through `exact` or
  `simpa`.
  Owner: `LayerPresentation` with transport lemmas for carrier isomorphisms.
  Delete or replace: forwarding constructors that only move proof ownership
  between equivalent parent coordinates.
  Validation:
  ```bash
  rg -n 'LayerPresentation\.ofLayerMaps|LayerPresentation\.ofCarrierLayerIso|LayerPresentation\.ofLayerShapeChildRank|LayerPresentation\.ofShapeChildRank' BijForm
  ```

- [x] Remove syntax/Nat presentation aliases that only restate
  `LayerPresentation`.
  Evidence: `SyntaxPresentation`, `NatLayerPresentation`, and
  `RankedNatLayerPresentation` forward to the same layer-presentation data.
  Owner: `LayerPresentation`; syntax/Nat APIs should remain only where they add
  data or a final user-facing route.
  Delete or replace: forwarding constructors such as
  `SyntaxPresentation.ofLayerIso`, `SyntaxPresentation.ofLayerMaps`,
  `NatLayerPresentation.ofLayerChildLt`, and
  `RankedNatLayerPresentation.ofLayerChildRank`.
  Validation:
  ```bash
  rg -n '\bSyntaxPresentation\b|\bNatLayerPresentation\b|\bRankedNatLayerPresentation\b|SyntaxPresentation\.of|NatLayerPresentation\.of|RankedNatLayerPresentation\.of' BijForm
  ```

- [x] Replace CodeLayer inverse proof tactics and eta helper stacks with a
  generated layer-presentation constructor.
  Evidence: `canonical_left_inv_at_by_fiber`,
  `canonical_left_inv_by_fiber`, `child_eta_cases`, `child_eta_rfl`, and
  `finish_code_layer_left_inv` support per-example inverse scripts.
  Owner: `CodeLayerPresentation.ofConstructors` or an equivalent
  `ofReadableSyntax` schema.
  Delete or replace: eta tactics and per-example left-inverse branch scripts.
  Validation:
  ```bash
  rg -n 'canonical_left_inv|child_eta|finish_code_layer_left_inv|layer_left_inv|codeLayer_left_inv|codeLayer_eta|CodeLayer\.ext_rfl|\bext_rfl\b' BijForm
  ```

- [x] Add reusable output-index inversion constructors instead of manual
  decode/encode proof blocks.
  Evidence: `OutputIndexInversion.ofIso` is opaque; comments say examples
  should prefer concrete generated inversion data. Typed-binding still has
  manual `FiberCode.decode_encode` / `encode_decode` style proofs.
  Owner: `DepPoly.OutputIndexInversion`.
  Delete or replace: manual inversion round-trip blocks that only decompose
  output-index changes and constructor parameters.
  Validation:
  ```bash
  rg -n 'OutputIndexInversion\.ofIso|FiberCode\.(decode|encode|decode_encode|encode_decode)|def decode \(i : Poly\.Ix S\)|def encode \(i : Poly\.Ix S\)|theorem decode_encode \(i : Poly\.Ix S\)|theorem encode_decode \(i : Poly\.Ix S\)' BijForm/DependentPolynomial.lean BijForm/TypedBinding.lean
  ```

## Codec Bounds And Carrier Ranks

- [x] Turn `SubcodeLe` / `SubcodeLt` bound propagation into a codec-path
  synthesis schema.
  Evidence: `CodeAlgebra.lean` has arity-specific and path-specific facts for
  `toNatSum3`, `toNatSum4`, finite prefixes, finite products, tagged products,
  and scaled payloads.
  Owner: `CodeAlgebra`, with compositional path bounds over `Iso` expressions.
  Delete or replace: arity-specific theorem stacks whose only content is
  "this child projection is below this composed codec".
  Validation:
  ```bash
  rg -n 'toNatSum3|toNatSum4|finPrefixNat_.*lt|finTaggedProdNat_.*_lt|ScaledPayloadBound|scaled_payload_child_lt' BijForm/CodeAlgebra.lean BijForm/Examples BijForm/StringDiagram
  ```

- [x] Replace Sorted carrier payload descent with a generic prefixed-tail
  constructor payload schema.
  Evidence: `sortedConstructorPayload_child_rank_lt`,
  `SortedFiniteConstructorPayload_child_rank_lt`,
  `SortedInfiniteConstructorPayload_child_rank_lt`, and the
  `SortedLayerPresentation` proof manually split branch positions, use
  `finPrefixNat_toFun_inr_lt_of_le`, and repair parent code through
  `SortedCarrierLayerIso.right_inv`.
  Owner: `CodeAlgebra` plus `LayerPresentation` carrier-iso transport.
  Delete or replace: the private payload theorem, finite/infinite public
  wrappers, and manual `SortedLayerPresentation` branches.
  Validation:
  ```bash
  rg -n 'sortedConstructorPayload_child_rank_lt|Sorted(Finite|Infinite)ConstructorPayload_child_rank_lt|LayerPresentation\.ofCarrierLayerIso SortedCarrierLayerIso|finPrefixNat_toFun_inr_lt_of_le' BijForm/Examples/Sorted.lean
  ```

## Typed Binding

- [x] Replace one/two-argument and one/two-constructor typed-binding carrier
  helpers with finite-list constructor-family schemas.
  Evidence: `ArgTuple.singleIso`, `ArgTuple.pairIso`,
  `CtorFamily.singleIso`, `CtorFamily.sumIso`, and `LayerShape.*_op_toFun`
  are special cases despite generic dependent tuple support in
  `DependentTuple.lean`.
  Owner: `ArgTuple` / `CtorFamily` finite-list schema with projection/path
  lemmas.
  Delete or replace: single/pair and sum/single helpers plus branch-specific
  carrier-coding simp facts.
  Validation:
  ```bash
  rg -n 'ArgTuple\.(singleIso|pairIso)|CtorFamily\.(singleIso|sumIso)|LayerShape\..*_op_toFun' BijForm/TypedBinding.lean BijForm/Examples/TypedBinding
  ```

- [x] Replace typed-binding rank dispatch with table-driven argument descent.
  Evidence: `LayerShapeRankProof.of_op` and `typed_binding_rank_descent` still
  perform constructor/`Fin` dispatch; `NFGeneratedLayer_child_rank_lt` passes
  four explicit helper facts.
  Owner: `ArgTuple` / `List.Forall` traversal over `S.args ctor`, consumed by
  `LayerShapeRankProof`.
  Delete or replace: `typed_binding_rank_descent`,
  `LayerShapeRankProof.of_op`, and aggregate facts like
  `NFGeneratedLayer_child_rank_lt` once the argument-bound table owns dispatch.
  Validation:
  ```bash
  rg -n 'typed_binding_rank_descent|LayerShapeRankProof\.of_op|NFGeneratedLayer_child_rank_lt|cases q using Fin\.cases' BijForm/TypedBinding.lean BijForm/Examples/TypedBinding
  ```

- [x] Delete NF-specific generated-layer `toFun` exposure facts by making
  constructor-family carrier codings simplify generically.
  Evidence: `NFGeneratedLayerIso_dum_toFun`,
  `NFGeneratedLayerIso_lam_toFun`, and `NFGeneratedLayerIso_app_toFun` only
  expose `LayerShape.trans_layerCarrierCoding_op_toFun` through NF-specific
  names.
  Owner: `TypedBinding.LayerShape` / `CtorFamily`.
  Delete or replace: all `NFGeneratedLayerIso_*_toFun` facts.
  Validation:
  ```bash
  rg -n 'NFGeneratedLayerIso_.*_toFun|trans_layerCarrierCoding_op_toFun' BijForm/Examples/TypedBinding BijForm/TypedBinding.lean
  ```

- [x] Replace NF per-position rank facts with declarative carrier/rank bound
  data.
  Evidence: `NFGeneratedLayer_dum_child_rank_lt`,
  `NFGeneratedLayer_lam_child_rank_lt`,
  `NFGeneratedLayer_app_fn_child_rank_lt`, and
  `NFGeneratedLayer_app_arg_child_rank_lt` manually use
  `finProdNatOrNat_*`, `finTaggedProdNat_*`, positivity from `Fin`, and
  `omega`.
  Owner: `LayerShapeRankProof` generated from constructor-family carrier/rank
  bound data.
  Delete or replace: the four local rank lemmas and the `using [...]` proof
  list.
  Validation:
  ```bash
  rg -n 'NFGeneratedLayer_.*child_rank_lt|finProdNatOrNat|finTaggedProdNat|typed_binding_rank_descent.*using' BijForm/Examples/TypedBinding/NF.lean
  ```

## Quotient Normal Forms

- [x] Replace quotient decoder-rank equality plumbing with a decoded-layer
  child-rank constructor.
  Evidence: `LayerNormalForm.child_rank_lt` requires an explicit
  `decodeLayer i z = <...>`; `quotient_rank_descent` only forwards that
  equality to an external fact. `HBTChildSwapLayerDecode_child_rank_lt`
  still owns decoder inversion over `sumNat.invFun` and unordered-pair child
  bounds.
  Owner: `QuotientPolynomial.LayerNormalForm`, analogous to generated-code
  layer child-rank constructors.
  Delete or replace: `quotient_rank_descent` and local
  `HBTChildSwapLayerDecode_child_rank_lt` once the decoded-layer schema owns
  the proof.
  Validation:
  ```bash
  rg -n 'quotient_rank_descent|HBTChildSwapLayerDecode_child_rank_lt|cases hsum|match hsum|sumNat\.invFun' BijForm/QuotientPolynomial.lean BijForm/Examples/HBTQuotient.lean
  ```

- [x] Generalize unordered-pair quotient repair or move it out of shared
  quotient support.
  Evidence: `Rel.unorderedPair_decode_encode_repair` and
  `Rel.unorderedPair_code_decode_encode_repair` live in
  `QuotientPolynomial.lean` but are HBT branch-swap shaped.
  Owner: either a generic commutative-binary normal-form repair schema or the
  HBT quotient example.
  Delete or replace: shared `unorderedPair*` facts that are not generic
  quotient infrastructure.
  Validation:
  ```bash
  rg -n 'unorderedPair.*repair|unorderedPair' BijForm/QuotientPolynomial.lean BijForm/Examples/HBTQuotient.lean
  ```

- [x] Collapse HBT quotient relation repair dispatch into quotient normal-form
  support.
  Evidence: `decode_encode_layer_rel` still has local position dispatch and
  hand-built branch repair around unordered-pair decode/encode.
  Owner: `QuotientPresentation.Rel`, with a branch-swap unordered-pair
  normal-form constructor if that quotient remains as an example.
  Delete or replace: local `hrepair` / `htarget` position-dispatch proof
  blocks.
  Validation:
  ```bash
  rg -n 'decode_encode_layer_rel|hrepair|htarget|cases q <;> exact Rel\.refl' BijForm/Examples/HBTQuotient.lean
  ```

## String Diagram Rank And Finite Coding

- [x] Replace finite single-sorted scaled-payload rank facts with a generic
  open-frontier rank descent schema.
  Evidence: `SingleSortedFinitePayloadBound` rewraps
  `CodeAlgebra.ScaledPayloadBound`; six
  `singleSortedFiniteLayer_*_child_rank_lt` lemmas repeat base-length,
  payload-bound, and scaled-rank proofs.
  Owner: `CodeAlgebra` or `ShapeLayerPresentation`.
  Delete or replace: `SingleSortedFinitePayloadBound`,
  `singleSortedFiniteRank_nonempty_child_lt_of_payload_bound`, and branch
  lemmas for one/two/many connect/bud child rank.
  Validation:
  ```bash
  rg -n 'SingleSortedFinitePayloadBound|singleSortedFiniteRank_nonempty_child_lt_of_payload_bound|singleSortedFiniteLayer_.*child_rank_lt|rank_scaled_payload|scaled_payload_child_lt' BijForm/StringDiagram/FiniteCoding/Syntax.lean
  ```

- [x] Replace `singleSortedFiniteLayer_shape_child_rank_lt` boundary dispatch
  with generated shape-code automation.
  Evidence: the proof manually runs `openBoundaryCases`, cases on shapes, and
  forwards to branch lemmas.
  Owner: generated shape-code rank automation for `SingleSortedFiniteFrontierCase`.
  Delete or replace: the boundary-case proof body.
  Validation:
  ```bash
  rg -n 'singleSortedFiniteLayer_shape_child_rank_lt|openBoundaryCases|singleSortedFiniteLayer_.*child_rank_lt' BijForm/StringDiagram/FiniteCoding/Syntax.lean
  ```

## String Diagram Render, Traversal, And Bridge Proofs

- [x] Replace branch-specific render append witnesses with `RenderDelta`
  projections.
  Evidence: `RenderDelta` already records endpoint/edge/node append facts, but
  `connectStep_edgesAppend`, `budStep_edgesAppend`,
  `connectStep_nodesAppend`, `budStep_nodesAppend`, and endpoint append facts
  repackage the same data.
  Owner: `RenderDelta` namespace with generic `edgesWitness`,
  `nodesWitness`, and `endpointsWitness` projections.
  Delete or replace: branch-specific `*_Append` witness definitions.
  Validation:
  ```bash
  rg -n 'connectStep_.*Append|budStep_.*Append|RenderDelta' BijForm/StringDiagram/Renderer/Steps.lean
  ```

- [x] Replace trace append recursion and first-new index/get proofs with
  generic trace append schemas.
  Evidence: `renderTrace_endpointsAppend`, `renderTrace_edgesAppend`, and
  `renderTrace_nodesAppend` have the same recursive shape; new edge/node
  index/get proofs repeat `AppendStep.firstSuffixIndex`.
  Owner: `RenderTrace` generic append over selected `RenderDelta` field plus
  reusable first-suffix theorem.
  Delete or replace: per-field trace append witnesses and
  `renderTrace_*_new_*Index/get` facts.
  Validation:
  ```bash
  rg -n 'renderTrace_.*Append|renderTrace_.*new_.*Index|renderTrace_.*new_.*get|firstSuffixIndex' BijForm/StringDiagram/Renderer/Trace.lean
  ```

- [x] Replace first-pending child order trace family with one delta/certificate
  record.
  Evidence: endpoint/edge/node suffix defs and append-step wrappers are
  triplicated; `ChildOrderTrace` and `firstPendingChild_orderTrace` rebuild
  connect/bud delta structure.
  Owner: `FirstPendingStep.Delta` or `FirstPendingStep.OrderDelta`.
  Delete or replace: `endpointOrder_firstPendingChild_step`,
  `edgeOrder_firstPendingChild_step`, `nodeOrder_firstPendingChild_step`, and
  most of `firstPendingChild_orderTrace`.
  Validation:
  ```bash
  rg -n 'endpointOrder_firstPendingChild_step|edgeOrder_firstPendingChild_step|nodeOrder_firstPendingChild_step|firstPendingChild_orderTrace|ChildOrderTrace' BijForm/StringDiagram/Traversal/State.lean
  ```

- [x] Add generic append-trace field preservation for graph render relations.
  Evidence: `endpointLabel_of_appendTrace`, `edgeLabel_of_appendTrace`,
  `nodeLabel_of_appendTrace`, `nodeIncidentFields_of_appendTrace`, and side
  variants build the same `AppendTraceRelation` prefix/suffix preservation.
  Owner: `AppendTraceRelation` field-extension schema.
  Delete or replace: repeated local `hlabelRel`, `hlengthRel`,
  `hincidentRel`, and `hsideRel` construction blocks.
  Validation:
  ```bash
  rg -n 'endpointLabel_of_appendTrace|edgeLabel_of_appendTrace|nodeLabel_of_appendTrace|nodeIncidentFields_of_appendTrace|hlabelRel|hlengthRel|hincidentRel|hsideRel' BijForm/StringDiagram/Bridge/GraphRenderRelation.lean
  ```

- [x] Replace connect/bud child frontier-pending preservation with one
  child-trace schema.
  Evidence: `connectChild_frontierPending` and `budChild_frontierPending`
  prove the same erased/appended pending-id alignment from
  `pending_cons_values`, `IndexedListRel`, and child order traces.
  Owner: `GraphRenderRelated.FrontierPendingFields.ofChildTrace`.
  Delete or replace: both branch-specific frontier-pending theorems.
  Validation:
  ```bash
  rg -n 'connectChild_frontierPending|budChild_frontierPending|pending_cons_values|FrontierPendingFields' BijForm/StringDiagram/Bridge/GraphRenderRelation.lean
  ```

- [x] Replace renderer invariant preservation branch proofs with delta
  invariant schemas.
  Evidence: `connectStep_validIds` / `budStep_validIds` and
  `connectStep_endpointPartition` / `budStep_endpointPartition` repeat
  old-vs-new endpoint, freshness, append, bound, and label splits.
  Owner: `RenderDelta.ValidIds` and `RenderDelta.EndpointPartition`.
  Delete or replace: most branch-specific invariant proof bodies; keep only
  branch delta facts and freshness inputs.
  Validation:
  ```bash
  rg -n 'connectStep_validIds|budStep_validIds|connectStep_endpointPartition|budStep_endpointPartition|RenderDelta' BijForm/StringDiagram/Renderer/Steps.lean
  ```

- [x] Unify index/frontier transport instead of keeping local cast helpers.
  Evidence: `listIndexCast` is heavily used, while separate helpers exist for
  renderer state, search state, frontier completeness, render prefix related
  states, `toDiag_cast`, and `Diag.bud_transport`.
  Owner: `IndexTransport` or `FrontierCast` namespace with public simp lemmas
  for state fields and constructor transport.
  Delete or replace: private `cast_pending`, `cast_seenNodes`,
  `cast_processedEdges`, manual cast-length blocks in syntax round-trip/search,
  and branch-specific `bud_transport` if it becomes a generic constructor
  transport corollary.
  Validation:
  ```bash
  rg -n 'cast_pending|cast_seenNodes|cast_processedEdges|listIndexCast|toDiag_cast|bud_transport|cast-length' BijForm/StringDiagram
  ```

- [x] Delete branch wrapper remnants once selected-step certificates carry
  generic deltas.
  Evidence: `EdgeMateData` is a one-field wrapper around `EdgeMate`;
  `FirstPendingStepSearchView` and `RenderPrefixChildStep` carry
  branch-specific proof payloads that downstream proofs immediately destruct.
  Owner: executable/search certificate API returning `FirstPendingStep` plus
  generic delta/evidence records.
  Delete or replace: `EdgeMateData`, branch-specific search-view destructuring
  helpers, and `RenderPrefixChildStep`.
  Validation:
  ```bash
  rg -n 'EdgeMateData|FirstPendingStepSearchView|RenderPrefixChildStep' BijForm/StringDiagram
  ```

## Boundary Hygiene

These items are intentionally separate from the proof-debt list above. They are
tracked here because they were found during the same simplification survey and
were explicitly requested to remain visible.

- [x] Move concrete unordered-pair/BinarySwap example material out of shared
  tuple-action infrastructure or generalize it.
  Evidence: `TupleAction.lean` contains `BinarySwap`, while shared tuple-action
  support should expose `ConcreteQuotientCode`, `FiniteAction`, and orbit
  coding schemas.
  Owner: either an examples module or a genuinely generic finite action schema.
  Delete or replace: concrete `BinarySwap` shared-layer declarations if they
  are only example material.
  Validation:
  ```bash
  rg -n 'BinarySwap|unorderedPair' BijForm/TupleAction.lean BijForm/Examples
  ```

- [x] Fix README/API drift for string-diagram finite coding rank names after
  the finite-coding rank schema is simplified.
  Evidence: README mentions `StringDiagram.singleSortedFiniteLayer_child_rank_lt`,
  while source currently has private `singleSortedFiniteLayer_shape_child_rank_lt`.
  Owner: README only after the source API is settled.
  Delete or replace: stale public-surface names in docs.
  Validation:
  ```bash
  rg -n 'singleSortedFiniteLayer_child_rank_lt|singleSortedFiniteLayer_shape_child_rank_lt' README.md BijForm
  ```
