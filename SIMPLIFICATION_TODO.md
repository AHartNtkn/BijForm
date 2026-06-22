# Simplification Todo

This file tracks simplification opportunities found in the repo-wide audit.
Unchecked items are open. When an item is completed, check it and add the
commit or validation receipt beneath it.

Validation for code changes remains `lake build` plus any item-specific audit
listed below. Documentation-only tracker edits should pass `git diff --check`.

## Core Coding Foundation

- [x] Collapse generated-code specializations into one canonical construction.
  - Owner: `BijForm.DependentPolynomial.GeneratedCode`
  - Evidence: `GeneratedCode`, `GeneratedShapeCode`, `GeneratedRankedNatCode`,
    and `GeneratedNatCode` in `BijForm/DependentPolynomial.lean`.
  - Action: make Nat, ranked-Nat, and finite/infinite shape codings views or
    constructors around `GeneratedCode` rather than parallel records.
  - Validation: examples using canonical Nat, ranked-Nat, and shape APIs still
    build; no specialized `.toGeneratedCode` conversions remain.
  - Completed: Nat and ranked-Nat generated codes are canonical
    `GeneratedCode` aliases, and shape codings store a canonical `code` field
    instead of duplicating generated-code fields.

- [x] Unify layer-presentation records.
  - Owner: `BijForm.DependentPolynomial.LayerPresentation`
  - Evidence: `LayerShapePresentation`, `SyntaxPresentation`,
    `NatLayerPresentation`, `RankedNatLayerPresentation`, and
    `ShapeLayerPresentation` repeat layer plus rank/descent fields.
  - Action: keep one presentation abstraction and derive syntax/Nat/ranked/shape
    views from it.
  - Validation: source search for old wrapper assembly shrinks and all examples
    build through the unified abstraction.
  - Completed: `LayerPresentation` is the sole layer/rank/descent record;
    syntax, Nat, and ranked-Nat presentations are views, and shape presentation
    stores only shape metadata plus a canonical presentation.

- [x] Split initial algebra machinery out of `DependentPolynomial.lean`.
  - Owner: new `BijForm.InitialAlgebra` or equivalent core module.
  - Evidence: `Mu`, `Mu.fold`, `WellFoundedCode`, generated code, shapes, and
    presentation DSL all live in `BijForm/DependentPolynomial.lean`.
  - Action: move `Mu`, fold, and initial-algebra coding APIs to a focused module
    while leaving polynomial container definitions in `DependentPolynomial`.
  - Validation: import graph builds without cycles; downstream modules still
    import the intended public API.
  - Completed: `BijForm.DependentPolynomial` now contains the container and
    output-fiber layer; `BijForm.InitialAlgebra` owns `Mu`, fold,
    generated-code, shape-code, and presentation APIs.

- [x] Remove the parallel `Obj` and `FiberObj` layer representation model.
  - Owner: `BijForm.DependentPolynomial` and `BijForm.InitialAlgebra`
  - Evidence: `Obj`, `FiberObj`, `objFiberIso`, and child transport code across
    the container and initial-algebra boundary.
  - Action: make one representation authoritative, either by storing `Fiber`
    inside `Obj` or by making one representation an abbrev over the other.
  - Validation: no duplicate object/fiber layer conversion path remains.
  - Completed: `Obj` is the only layer-with-children representation; the
    generated-code bridge now maps `Obj` directly to `CodeLayer`.

- [x] Replace child eta tactic variants with one generic helper.
  - Owner: `BijForm.InitialAlgebra`
  - Evidence: `child_eta_empty`, `child_eta_unit`, and `child_eta_bool` are
    aliases for the same tactic in `BijForm.InitialAlgebra`.
  - Action: provide one child-function extensionality helper.
  - Validation: `rg "child_eta_(empty|unit|bool)" BijForm --glob '*.lean'`
    has no matches.
  - Completed: `child_eta_cases` is the single primitive tactic, and
    `child_eta_rfl child` is the only close-by-rfl wrapper.

- [x] Add generic `CodeLayer` child equality/extensionality lemmas.
  - Owner: `BijForm.InitialAlgebra`, namespace `DepPoly.CodeLayer`
  - Evidence: repeated `Sigma.ext`, `heq_of_eq`, `funext`, and child transport
    proof bodies in `TypedBinding`, examples, and `DependentPolynomial`.
  - Action: package dependent-pair child equality and heterogeneous child
    transport behind reusable lemmas.
  - Validation: source search for manual `Sigma.ext rfl`, `heq_of_eq`, and
    child eta proof bodies drops in examples.
  - Completed: `CodeLayer.ext`, `CodeLayer.ext_rfl`, and
    `CodeLayer.ext_layer` now own dependent-pair reconstruction. Targeted
    `TypedBinding`, `Num`, `Peano`, and `Sorted` proofs now route layer
    equality through those helpers; remaining local `heq_of_eq` occurrences are
    child-equality witnesses or non-`CodeLayer` tuple proofs.

- [x] Move generic dependent argument tuple machinery out of typed binding.
  - Owner: `BijForm.DependentTuple`
  - Evidence: `ArgTuple`, `ArgTuple.ofChild`, `ArgTuple.toChild`, and
    `ArgTuple.iso` in `BijForm/TypedBinding.lean`.
  - Action: make the dependent list-of-arguments to child-function equivalence
    reusable outside typed binding.
  - Validation: `TypedBinding` imports the generic owner; no typed-binding-only
    names are needed for generic arity tuples.
  - Completed: `ListPiTuple` now owns the list-indexed dependent product and
    its equivalence with `Fin`-indexed child functions. `TypedBinding.ArgTuple`
    is a typed-binding specialization that delegates to the generic module.

## Fin, List, and Table Helpers

- [x] Finish replacing raw `Fin.ext` with shared helpers.
  - Owner: `BijForm.Coding`
  - Evidence: direct `Fin.ext` remains in `BijForm/StringDiagram/Basic.lean`
    and `BijForm/Examples/Num.lean`.
  - Action: route these through `fin_eq_of_val_eq` or a more specific helper.
  - Validation: `rg -n "Fin\\.ext" BijForm` only shows the helper
    implementation or justified nontrivial uses.
  - Completed: all non-owner occurrences now use `fin_eq_of_val_eq`; the only
    remaining `Fin.ext` source hit is the helper implementation in
    `BijForm/Coding.lean`.

- [x] Add reusable `Fin 0` eliminators and empty-code isomorphisms.
  - Owner: `BijForm.Coding` and `BijForm.CodeAlgebra`
  - Evidence: repeated `False.elim (Nat.not_lt_zero ...)`, `nomatch`, and
    empty-side code branches in `Coding`, `CodeAlgebra`, and NF examples.
  - Action: add `Fin 0` eliminator, `Fin 0` to `Empty` iso, and codec helpers
    for empty sum/product sides.
  - Validation: source search for manual `Nat.not_lt_zero` eliminations drops.
  - Completed: `fin_zero_elim`, `fin_zero_empty_iso`, and
    `fin_zero_prod_empty_iso` now live in `BijForm.Coding`; direct
    `Nat.not_lt_zero` eliminations were replaced, and the closed app-term empty
    carrier composes through the reusable empty product iso.

- [x] Move `FiniteSubtypeTable` out of root `Coding`.
  - Owner: `BijForm.FiniteSubtypeTable`
  - Evidence: `FiniteSubtypeTable` in `BijForm/Coding.lean` is table
    enumeration infrastructure; current main consumer is
    `Examples/SymmetricInteractionNet.lean`.
  - Action: keep root `Coding` focused on `Iso` and primitive equality helpers.
  - Validation: `SymmetricInteractionNet` imports the new owner and builds.
  - Completed: table structure and namespace API moved to
    `BijForm.FiniteSubtypeTable`; `Coding` no longer contains table machinery,
    and `SymmetricInteractionNet` imports the new owner directly.

- [x] Add structured list-index transport APIs.
  - Owner: `BijForm.StringDiagram.Basic`
  - Evidence: heavy `Fin.cast`, `fin_eq_of_val_eq`, and manual list-index
    transport in `GraphRenderRelation`, `Renderer/Steps`, and
    `SyntaxRoundTrip`.
  - Action: introduce `ListIndexTransport` or `AppendView` helpers for old/new
    indices, erased indices, casts, and `get` equalities.
  - Validation: source search for `Fin.cast` and low-level list get transport
    drops sharply in renderer and bridge files.
  - Partial: added `listIndexCast` in `StringDiagram.Basic`. `SyntaxRoundTrip`
    now has no raw `Fin.cast`; `Renderer.Steps` keeps one arity/incident cast
    that is outside the list-owned index-cast shape. `GraphRenderRelation`
    remains the main open cleanup surface.
  - Partial: added relation-owned `GraphRenderRelated.endpointIndex`,
    `edgeIndex`, `nodeIndex`, and `pendingIndex` helpers. Direct
    `GraphRenderRelation` relation-length casts dropped, but the bridge file
    still needs a broader ordered-trace/list-transport cleanup before this item
    is complete.
  - Partial: routed more final preservation proof sites through the relation
    helpers; `GraphRenderRelation` still has raw child-step and incident-slot
    transports that need a separate helper family.
  - Partial: added generic `endpointOrderIndex`, `edgeOrderIndex`, and
    `nodeOrderIndex` helpers beside the order-list definitions and routed one
    bud-child preservation block through them. Raw child-step casts remain in
    connect-child, later bud-child, and incident-slot proof regions.
  - Partial: routed the connect-child edge-label, edge-endpoint, node-label,
    and node-incident proof regions through the order-list helpers where the
    cast was pure order-index transport. Later bud-child and dependent
    incident-slot transports remain open.
  - Partial: routed the bud-child node-incident-length proof through
    `nodeOrderIndex` for child node-order lookups. Later bud-child frontier,
    edge, and dependent incident-slot transports remain open.
  - Partial: routed the bud-child pending/frontier pointwise endpoint relation
    through `endpointOrderIndex`. The relation-field bridge plus later
    bud-child label, edge, and dependent incident-slot transports remain open.
  - Partial: routed bud-child endpoint-label and edge-label preservation
    branches through `endpointOrderIndex` and `edgeOrderIndex`. The pending
    relation-field bridge plus later edge-left/right and dependent
    incident-slot transports remain open.
  - Partial: routed bud-child edge-left and edge-right preservation branches
    through `endpointOrderIndex` and `edgeOrderIndex` for child order lookups.
    The pending relation-field bridge and node/incident-slot preservation
    region remain open.
  - Partial: routed bud-child node-label and node-incident preservation
    branches through `nodeOrderIndex` and `endpointOrderIndex` for child order
    lookups. The remaining raw `hchild*Length` hits are the pending
    relation-field bridge; dependent incident-slot casts still need a separate
    helper family.
  - Completed: added list-owned `listIndexCast`, order-owned
    `endpointOrderIndex`/`edgeOrderIndex`/`nodeOrderIndex`, relation-owned
    `endpointIndex`/`edgeIndex`/`nodeIndex`/`pendingIndex`, and
    `nodeIncidentIndex`. Proof-local child order and incident-slot transports
    in `GraphRenderRelation` now route through helpers; the only remaining raw
    `hchild*Length` hits are the `pending_id` relation-field bridge.

## Code Algebra and Rank Descent

- [x] Replace hard-coded nested Nat codecs with a declarative codec builder.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: `sumProdNat`, `natOrProdOrProdNat`,
    `prodOrNatOrProdOrNat`, and matching branch-bound lemmas.
  - Action: define a branch-code descriptor or nested sum/product codec API that
    generates common projection and child-bound facts.
  - Validation: Num, Lambda, Peano, Sorted, NF, and finite string-diagram rank
    proofs use generic codec-path lemmas instead of bespoke nested-code names.
  - Partial: added right-associated `toNatSum3` and `toNatSum4` builders with
    branch-bound lemmas. `natOrProdOrProdNat` and `prodOrNatOrProdOrNat` now
    assemble through those builders while preserving their public names and
    carrier shapes. Example rank proofs still need to move from specialized
    nested-code theorem names to the generic branch-path lemmas.
  - Completed: Num, Peano, HBT, and Lambda rank proofs now use generic
    `toNatSum`, `toNatSum3`, and `toNatSum4` branch-path lemmas instead of
    specialized nested-code theorem names. Source scan for
    `natOrProdOrProdNat_toFun`, `prodOrNatOrProdOrNat_toFun`, and
    `sumProdNat_toFun` in examples and string-diagram modules has no matches.

- [x] Add generic child-bound propagation through codec combinators.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: repeated `toNatSum_*`, `toNatProd_*`,
    `finPrefixNat_toFun_inr_*`, and `finSumProdNat_*` proofs.
  - Action: introduce reusable `SubcodeLe` and `SubcodeLt` style relations for
    `Iso.sum`, `Iso.prod`, `Iso.trans`, finite prefixes, and tagged branches.
  - Validation: rank descent proofs in examples become applications of these
    propagation lemmas.
  - Partial: added `SubcodeLe` and `SubcodeLt` relations with base Nat/product
    payload facts plus propagation lemmas for `Iso.trans`, Nat sums,
    three-/four-way Nat sums, Nat products, and finite prefixes.
    `NumNat_layer_child_lt` now uses subcode propagation instead of manual
    `finPrefixNat` plus nested-sum bound chains.
  - Partial: `PeanoNat_layer_child_lt` now uses `SubcodeLt` propagation facts
    for its four-way Nat sum branches instead of direct `toNatSum4` branch
    lemma applications.
  - Completed: added finite-product and nested-product `SubcodeLe` helpers.
    HBT, Lambda, and Sorted rank/descent proofs now use `SubcodeLt` paths; a
    source scan over examples and finite string-diagram syntax reports no
    remaining direct low-level child-bound lemma uses.

- [x] Move generic scaled-rank payload lemmas out of finite string diagrams.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: private `rank_scaled_payload_lt` and
    `rank_scaled_payload_le_with_gap` in
    `BijForm/StringDiagram/FiniteCoding/Syntax.lean`.
  - Action: publish general arithmetic/rank helper lemmas where examples can
    reuse them.
  - Validation: `#check BijForm.CodeAlgebra.rank_scaled_payload_lt` or the final
    chosen public name after importing `BijForm.CodeAlgebra`.
  - Completed: `CodeAlgebra` now owns `rank_scaled_payload_lt` and
    `rank_scaled_payload_le_with_gap`; finite string-diagram syntax uses the
    public names and has no private scaled-rank copies.

- [x] Make closed-form pairing the single public product codec.
  - Owner: `BijForm.Pairing`
  - Evidence: scan-based `encode`/`decode`/`iso` and closed-form
    `encodeFast`/`decodeFast`/`isoFast` coexist.
  - Action: make the proved closed form the public pairing route; keep scan
    machinery private proof scaffolding only where needed.
  - Validation: `CodeAlgebra.prodNat` and all product-code users build through
    the closed-form public API.
  - Completed: `Pairing.encode`, `Pairing.decode`, and `Pairing.iso` now use
    the closed-form path; the shell-scan encoder/decoder are private proof
    scaffolding, and `encodeFast`/`decodeFast`/`isoFast` are gone.

## Examples

- [x] Replace repeated `SyntaxPresentation.ofLayerMaps` inverse boilerplate.
  - Owner: `BijForm.DependentPolynomial` plus example modules.
  - Evidence: repeated same-fiber unpacking, `cases out_eq`, constructor cases,
    and `child_eta_rfl` in `Num`, `Peano`, `Lambda`, `HBT`, `FinChain`,
    `Sorted`, and `StringDiagram/Polynomial`.
  - Action: add a shared constructor-layer presentation helper that examples
    instantiate with domain-specific constructor clauses and rank.
  - Validation: source search for `SyntaxPresentation.ofLayerMaps` and
    repeated `child_eta_rfl child` proof bodies drops in examples.
  - Partial: added `SyntaxPresentation.ofLayerIso` and migrated HBT, Num,
    FinChain, Lambda, Peano, Sorted, and string-diagram polynomial syntax
    presentations off `SyntaxPresentation.ofLayerMaps`. Constructor-specific
    `child_eta_rfl child` inverse proof bodies remain visible and still need a
    deeper constructor-clause helper.
  - Partial: added `CodeLayer.canonical_left_inv_by_fiber` and
    `finish_code_layer_left_inv` in `BijForm.InitialAlgebra`. The seven
    `SyntaxPresentation.ofLayerIso` blocks now route canonical same-fiber
    layer/fiber unpacking and child eta through shared helpers; the remaining
    `child_eta_rfl child` occurrences are in non-syntax Nat/carrier layer
    presentations with additional payload coding obligations.
  - Partial: routed the five core example `CodeLayerPresentation.ofMaps`
    layer-shape left inverses through `CodeLayer.canonical_left_inv_by_fiber`.
    HBT, Num, Peano, Lambda, and FinChain no longer own the outer
    layer/fiber destructuring in those blocks. Remaining surfaces are fixed
    sorted carrier/payload isomorphisms, typed-binding internals, and finite
    string-diagram frontier-case proofs.
  - Partial: added fixed-index `CodeLayer.canonical_left_inv_at_by_fiber`.
    `sortedConstructorPayloadIso` and the nontrivial fixed branch of
    `SortedCarrierLayerIso` now use the shared fixed-fiber layer/fiber
    destructuring helper. Remaining direct child-eta closers in Num, Peano,
    and Sorted are branch-local payload cases after shared scaffold removal;
    remaining layer/fiber scaffold surfaces are typed-binding internals and
    finite string-diagram frontier-case proofs.
  - Completed: named syntax/example surfaces no longer use
    `SyntaxPresentation.ofLayerMaps`; syntax and core same-fiber layer inverse
    scaffolds route through `CodeLayer.canonical_left_inv_by_fiber` or
    `CodeLayer.canonical_left_inv_at_by_fiber`. Remaining direct child-eta
    closers in examples are payload-local branches after shared scaffold
    removal, and finite string-diagram frontier branching is tracked by the
    finite frontier table item below.

- [x] Factor finite and infinite sorted branch payload coding.
  - Owner: `BijForm.Examples.Sorted`, backed by `CodeAlgebra` payload lemmas.
  - Evidence: `SortedFiniteConstructorPayloadIso`,
    `SortedInfiniteConstructorPayloadIso`, and parallel child-rank proofs.
  - Action: create one branch payload iso and one rank lemma parameterized by
    pivot codec and child-bound witnesses.
  - Validation: source search for duplicated finite/infinite sorted payload
    proof blocks drops.
  - Partial: replaced the separate finite/infinite constructor payload isos
    with one `sortedConstructorPayloadIso` parameterized by upper bound and
    pivot codec. The finite and infinite child-rank lemmas remain separate and
    still need a parameterized descent helper.
  - Completed: added `sortedConstructorPayload_child_rank_lt` parameterized by
    upper bound, pivot codec, tail codec, and left/right `SubcodeLt` witnesses.
    Finite and infinite child-rank theorems are now thin instantiations.

- [x] Generalize typed-binding NF constructor-family carrier coding.
  - Owner: `BijForm.TypedBinding`
  - Evidence: `NFNormalFamilyCarrierIso`, `NFAppFamilyCarrierIso`, and long
    `NFGeneratedLayer_child_rank_lt` proof in
    `BijForm/Examples/TypedBinding/NF.lean`.
  - Action: add typed-binding helpers for finite constructor families by return
    sort and public rank lemmas for generated layer codings.
  - Validation: NF rank proof uses public `LayerShape.layerCoding`/
    `LayerShape.layerCarrierCoding` projection lemmas instead of directly
    naming `LayerShape.iso`, `LayerShape.familyCarrierIso`,
    `ArgTuple.ofChild`, or codec internals repeatedly.
  - Partial: added `ArgTuple.singleIso`, `ArgTuple.pairIso`,
    `CtorFamily.singleIso`, `CtorFamily.sumIso`, and
    `LayerShape.layerCoding`, `LayerShape.layerCarrierCoding`, and their
    operation projection lemmas in `TypedBinding`; routed both NF
    normal-expression and app-term family carriers through those helpers. The
    local `NF*FamilyToCarrier`/`NF*FamilyOfCarrier` maps are gone, and
    `NFGeneratedLayer_child_rank_lt` no longer directly names
    `LayerShape.iso`, `LayerShape.familyCarrierIso`, `LayerShape.layerToShape`,
    `LayerShape.familyIso`, `CtorLayer.familyIso`, `CtorLayer.toFamily`,
    `ArgTuple.ofChild`, or `ListPiTuple.ofPi`.
  - Completed: extracted public NF constructor-child rank lemmas for `dum`,
    `lam`, app-function, and app-argument children. `NFGeneratedLayer_child_rank_lt`
    is now a dispatcher over those lemmas, and its body no longer contains
    `hparent`, `let tail`, direct `CodeAlgebra.finProdNatOrNat`/
    `CodeAlgebra.finTaggedProdNat` calls, or `omega`.

- [x] Add noncanonical typed-binding layer inverse helpers.
  - Owner: `BijForm.TypedBinding`
  - Evidence: `SyntaxIso.layer_left_inv` and
    `LayerShape.layerShape_left_inv` still manually destruct noncanonical
    `CodeLayer` values over `TypedBinding.inversion`.
  - Action: add typed-binding-owned helpers for `FiberCode` layer inverse
    proofs so callers supply only variable/operator branch clauses.
  - Validation: typed-binding left-inverse proofs no longer contain local
    `cases layer`/`cases code` scaffolds.
  - Completed: added `FiberCode.LayerChild` and
    `FiberCode.codeLayer_left_inv_by_cases`; `SyntaxIso.layer_left_inv` and
    `LayerShape.layerShape_left_inv` now supply only variable/operator branch
    proofs.

- [ ] Replace HBT child-swap normal-form boilerplate with quotient helpers.
  - Owner: `BijForm.QuotientPolynomial` and `BijForm.CodeAlgebra`
  - Evidence: manual `HBTChildSwapNorm`, `HBTChildSwapDenorm`, and binary swap
    relation proofs in `BijForm/Examples/HBTQuotient.lean`.
  - Action: add generic binary child swap quotient descent and route unordered
    pair coding through existing `CodeAlgebra.unorderedPair*` APIs.
  - Validation: HBT quotient example exposes the same public final isomorphisms
    through generic quotient descent.
  - Partial: added `QuotientPresentation.DescendedGeneratedCode.ofMuNormalizer`
    for generated-code descent from `Mu` normalizer/denormalizer laws. HBT
    branch congruence, eta, and swap relation chains are now named helper
    lemmas, and `HBTChildSwapDescendedNatCode` is an instantiation of the
    generic normalizer helper. The broader generic binary child-swap descent
    abstraction remains open.

- [ ] Generate finite string-diagram entry tables for finite signatures.
  - Owner: `BijForm.StringDiagram.FiniteCoding.Syntax`
  - Evidence: the SIN example used to own local entry equality plus separate
    unary and non-unary entry tables.
  - Action: build unary and non-unary `FiniteSubtypeTable`s from node
    enumeration and arity data.
  - Validation: source search for the old local entry-equality and split-table
    identifiers has no tracked matches.
  - Partial: added `FiniteSubtypeTable.filterAll`,
    `Signature.entryDecidableEq`, `Signature.unaryEntryTable`,
    `Signature.nonUnaryEntryTable`, and
    `SingleSortedFiniteCodingData.ofEntryTable`. The SIN example now supplies
    one complete constructor-entry table and derives unary/non-unary tables
    generically. Full table generation from node enumeration remains open.

- [ ] Review low-value generated-code pass-through wrappers.
  - Owner: example modules and `BijForm.DependentPolynomial.GeneratedCode`
  - Evidence: many local `GeneratedCode`, syntax iso, Nat iso, shape iso, and
    finite iso wrappers across examples.
  - Action: keep public characterization theorems required by the repository
    goal, but replace internal aliases with consistent generic composition
    helpers.
  - Validation: public example surfaces remain available; internal wrapper
    source count drops.

## String Diagrams, Rendering, and Traversal

- [ ] Factor graph-render relation into ordered trace machinery.
  - Owner: `BijForm.StringDiagram.Bridge.GraphRenderRelation` plus shared order
    helpers.
  - Evidence: `GraphRenderRelated.connectChild` and `.budChild` manually
    synchronize endpoint, edge, node order, labels, bounds, incidence,
    frontier, and pending state.
  - Action: introduce `OrderedTraceRelation` or `AppendStepRelation`
    parameterized by field projections and per-field laws.
  - Validation: public `toDiag` and `toPortHypergraphIso` theorems derive from
    the generic relation.

- [ ] Introduce declarative render deltas for connect and bud.
  - Owner: `BijForm.StringDiagram.Renderer.Steps`
  - Evidence: `connectStep` and `budStep` have parallel invariant preservation
    families for valid ids, endpoint partition, node incident nodup, and owner
    id partition.
  - Action: define `RenderDelta` describing appended endpoints/edges/nodes and
    frontier transformation, then derive old/new membership, get, length, and
    invariant preservation.
  - Validation: existing `connectStep_*` and `budStep_*` theorem consumers build
    through delta-derived facts.

- [ ] Factor render trace prefix/index proofs.
  - Owner: `BijForm.StringDiagram.Renderer.Trace`
  - Evidence: endpoints, edges, and nodes repeat prefix/append trace reasoning
    and new-index/get lemmas.
  - Action: create a generic `TraceField` or `AppendTrace` API with projection,
    suffix, old index, and new index theorems.
  - Validation: bridge proofs still have the trace computation and new-index
    facts they need.

- [ ] Factor traversal child-state updates.
  - Owner: `BijForm.StringDiagram.Traversal.State`
  - Evidence: `connectChild`, `budChild`, and their `RenderPrefixRelated` and
    `IsoRelated` preservation lemmas repeat pending, seen, processed, frontier
    completeness, and iso-preservation logic.
  - Action: define `SearchStepDelta` or `FirstPendingStep.apply` returning the
    child state and common facts once.
  - Validation: connect/bud iso-preservation becomes one generic theorem plus
    small constructors.

- [ ] Generalize first-pending finite search correctness.
  - Owner: `BijForm.StringDiagram.Traversal.Search`
  - Evidence: `firstPendingConnectSearch?`, `firstPendingBudSearch?`, and
    `firstPendingStepSearch?` duplicate `findSome?` witness, exactness, and
    priority proofs.
  - Action: prove a generic finite-search correctness theorem and encode
    connect-before-bud priority in one result type.
  - Validation: `toDiag_step`, `toDiag_connect`, `toDiag_bud`, and
    `toDiag_isoRelated` still build.

- [ ] Package render trace evidence.
  - Owner: `BijForm.StringDiagram.Hypergraph`
  - Evidence: callers manually thread evidence tuples like `hv hp hn pref ho
    hall` through `Hypergraph`, `SyntaxRoundTrip`, and `Quotient`.
  - Action: add `RenderTraceEvidence` with projections for graph evidence, open
    evidence, endpoint prefix, owner partition, and reachability.
  - Validation: bridge files no longer assemble the invariant tuple manually.

- [ ] Table-drive finite string-diagram frontier cases.
  - Owner: `BijForm.StringDiagram.FiniteCoding.Syntax`
  - Evidence: frontier cardinality split is repeated across layer shape,
    carrier iso, to/from shape maps, inverses, and rank proof.
  - Action: define a `FrontierCase` eliminator/table with allowed constructors,
    carrier iso, child carrier, and rank contribution.
  - Validation: public syntax/open-graph finite and Nat isomorphisms remain
    unchanged.

- [ ] Move semantic graph/order facts out of bridge files.
  - Owner: `BijForm.StringDiagram.Hypergraph` or `Traversal.State`
  - Evidence: `incident_mem_node_eq`, `boundary_mem_not_incident_mem`,
    `incidentFlatMap_nodup_of_nodup`, and `endpointOrder_nodup` live in
    `Bridge/GraphRenderRelation.lean`.
  - Action: move owner/order and flat-map nodup facts to the semantic graph or
    traversal order API.
  - Validation: bridge files compose these facts instead of owning duplicate
    hypergraph reasoning.

- [ ] Reduce duplicated preserved/reflected fields in `PortHypergraphIso`.
  - Owner: `BijForm.StringDiagram.Hypergraph.PortHypergraphIso`
  - Evidence: forward and reflected facts are represented and transported in
    parallel in `PortHypergraphIso`.
  - Action: store minimal forward preservation data plus equivalences; derive
    reflected and symmetric facts as namespace theorems.
  - Validation: traversal iso-related proofs consume derived reflected lemmas.

## Quotients and Validation Tooling

- [ ] Extract generic quotient-normal-form coding.
  - Owner: new quotient-code boundary or `BijForm.QuotientPolynomial`
  - Evidence: `TupleAction.ConcreteQuotientCode` and quotient-polynomial
    descended code both encode normalize/denormalize descent to concrete
    carriers.
  - Action: create one generic quotient-normal-form coding abstraction and
    instantiate it for tuple actions and polynomial code quotients.
  - Validation: `TupleAction.BinarySwap` and `Examples/HBTQuotient.lean` build
    through the shared abstraction.

- [ ] Add generic setoid transport across `Iso`.
  - Owner: `BijForm.Coding` or `BijForm.QuotientPolynomial`
  - Evidence: syntax/code relation transport is duplicated in
    `QuotientPolynomial.lean`.
  - Action: add `Iso.transportSetoid` and indexed quotient transport helpers.
  - Validation: `syntaxCarrierIso`, `codeIso`, and HBT quotient examples build
    through the generic transport.

- [ ] Replace stale-name audit greps with Lean validation surfaces.
  - Owner: audit tooling plus quotient/example validation modules.
  - Evidence: `scripts/audit.sh` greps for old declaration names and exact
    source strings.
  - Action: add Lean modules that typecheck intended quotient and example
    public surfaces, then remove greps that only prove old spellings are absent.
  - Validation: `lake build` includes the validation modules and `scripts/audit.sh`
    no longer contains stale-name policy greps.

- [ ] Consolidate audit command ownership.
  - Owner: Lake/tooling.
  - Evidence: `Audit.lean` shells to `scripts/audit.sh`, and the shell script
    runs `lake build`.
  - Action: make either the shell script or a real Lake script the single
    authoritative audit owner.
  - Validation: the chosen command works from repo root and from a subdirectory;
    docs name only that command.

- [ ] Replace the GraphRenderRelation-only AWK `Fin.ext` audit.
  - Owner: finite-index helper boundary plus audit tooling.
  - Evidence: `scripts/check-trivial-fin-ext.awk` parses formatting in one file
    while raw `Fin.ext` can exist elsewhere.
  - Action: remove the AWK gate or replace it with a project-wide lint that has
    a documented allowed helper boundary.
  - Validation: lint evidence targets the whole tracked Lean source set or the
    AWK test files are deleted with the gate.

- [ ] Make proof-gap validation semantic enough to avoid lexical false comfort.
  - Owner: formalization validation tooling.
  - Evidence: `scripts/audit.sh` classifies `sorry` by nearby words and writes
    fixed temp files under `/tmp`.
  - Action: use temporary files from `mktemp` and move toward a declaration-level
    proof-gap inventory, such as declarations depending on `sorryAx` matched to
    explicit unfinished markers.
  - Validation: labeled and unlabeled proof-gap fixtures behave as intended, and
    parallel audit runs do not share fixed temp paths.

- [ ] Remove README declaration inventory as a second source of truth.
  - Owner: README/docs.
  - Evidence: README manually lists large declaration inventories, and audit
    tooling then protects pieces of that list with stale-name greps.
  - Action: shrink README to stable module-level orientation or generate
    declaration inventories from source state.
  - Validation: no audit grep exists solely to keep README declaration names
    current.
