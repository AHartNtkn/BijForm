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

- [ ] Split initial algebra machinery out of `DependentPolynomial.lean`.
  - Owner: new `BijForm.InitialAlgebra` or equivalent core module.
  - Evidence: `Mu`, `Mu.fold`, `WellFoundedCode`, generated code, shapes, and
    presentation DSL all live in `BijForm/DependentPolynomial.lean`.
  - Action: move `Mu`, fold, and initial-algebra coding APIs to a focused module
    while leaving polynomial container definitions in `DependentPolynomial`.
  - Validation: import graph builds without cycles; downstream modules still
    import the intended public API.

- [ ] Remove the parallel `Obj` and `FiberObj` layer representation model.
  - Owner: `BijForm.DependentPolynomial`
  - Evidence: `Obj`, `FiberObj`, `objFiberIso`, and child transport code in
    `BijForm/DependentPolynomial.lean`.
  - Action: make one representation authoritative, either by storing `Fiber`
    inside `Obj` or by making one representation an abbrev over the other.
  - Validation: no duplicate object/fiber layer conversion path remains.

- [ ] Replace child eta tactic variants with one generic helper.
  - Owner: `DepPoly.CodeLayer`
  - Evidence: `child_eta_empty`, `child_eta_unit`, and `child_eta_bool` are
    aliases for the same tactic in `BijForm/DependentPolynomial.lean`.
  - Action: provide one child-function extensionality helper plus `CodeLayer`
    extensionality lemmas.
  - Validation: `rg "child_eta_(empty|unit|bool)" BijForm` drops to the helper
    boundary or disappears.

- [ ] Add generic `CodeLayer` child equality/extensionality lemmas.
  - Owner: `DepPoly.CodeLayer`
  - Evidence: repeated `Sigma.ext`, `heq_of_eq`, `funext`, and child transport
    proof bodies in `TypedBinding`, examples, and `DependentPolynomial`.
  - Action: package dependent-pair child equality and heterogeneous child
    transport behind reusable lemmas.
  - Validation: source search for manual `Sigma.ext rfl`, `heq_of_eq`, and
    child eta proof bodies drops in examples.

- [ ] Move generic dependent argument tuple machinery out of typed binding.
  - Owner: new finite-arity/dependent tuple boundary, or `DepPoly`.
  - Evidence: `ArgTuple`, `ArgTuple.ofChild`, `ArgTuple.toChild`, and
    `ArgTuple.iso` in `BijForm/TypedBinding.lean`.
  - Action: make the dependent list-of-arguments to child-function equivalence
    reusable outside typed binding.
  - Validation: `TypedBinding` imports the generic owner; no typed-binding-only
    names are needed for generic arity tuples.

## Fin, List, and Table Helpers

- [ ] Finish replacing raw `Fin.ext` with shared helpers.
  - Owner: `BijForm.Coding`
  - Evidence: direct `Fin.ext` remains in `BijForm/StringDiagram/Basic.lean`
    and `BijForm/Examples/Num.lean`.
  - Action: route these through `fin_eq_of_val_eq` or a more specific helper.
  - Validation: `rg -n "Fin\\.ext" BijForm` only shows the helper
    implementation or justified nontrivial uses.

- [ ] Add reusable `Fin 0` eliminators and empty-code isomorphisms.
  - Owner: `BijForm.Coding` and `BijForm.CodeAlgebra`
  - Evidence: repeated `False.elim (Nat.not_lt_zero ...)`, `nomatch`, and
    empty-side code branches in `Coding`, `CodeAlgebra`, and NF examples.
  - Action: add `Fin 0` eliminator, `Fin 0` to `Empty` iso, and codec helpers
    for empty sum/product sides.
  - Validation: source search for manual `Nat.not_lt_zero` eliminations drops.

- [ ] Move `FiniteSubtypeTable` out of root `Coding`.
  - Owner: finite subtype/table module under `CodeAlgebra` or a new finite-table
    boundary.
  - Evidence: `FiniteSubtypeTable` in `BijForm/Coding.lean` is table
    enumeration infrastructure; current main consumer is
    `Examples/SymmetricInteractionNet.lean`.
  - Action: keep root `Coding` focused on `Iso` and primitive equality helpers.
  - Validation: `SymmetricInteractionNet` imports the new owner and builds.

- [ ] Add structured list-index transport APIs.
  - Owner: `BijForm.StringDiagram.Basic`
  - Evidence: heavy `Fin.cast`, `fin_eq_of_val_eq`, and manual list-index
    transport in `GraphRenderRelation`, `Renderer/Steps`, and
    `SyntaxRoundTrip`.
  - Action: introduce `ListIndexTransport` or `AppendView` helpers for old/new
    indices, erased indices, casts, and `get` equalities.
  - Validation: source search for `Fin.cast` and low-level list get transport
    drops sharply in renderer and bridge files.

## Code Algebra and Rank Descent

- [ ] Replace hard-coded nested Nat codecs with a declarative codec builder.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: `sumProdNat`, `natOrProdOrProdNat`,
    `prodOrNatOrProdOrNat`, and matching branch-bound lemmas.
  - Action: define a branch-code descriptor or nested sum/product codec API that
    generates common projection and child-bound facts.
  - Validation: Num, Lambda, Peano, Sorted, NF, and finite string-diagram rank
    proofs use generic codec-path lemmas instead of bespoke nested-code names.

- [ ] Add generic child-bound propagation through codec combinators.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: repeated `toNatSum_*`, `toNatProd_*`,
    `finPrefixNat_toFun_inr_*`, and `finSumProdNat_*` proofs.
  - Action: introduce reusable `SubcodeLe` and `SubcodeLt` style relations for
    `Iso.sum`, `Iso.prod`, `Iso.trans`, finite prefixes, and tagged branches.
  - Validation: rank descent proofs in examples become applications of these
    propagation lemmas.

- [ ] Move generic scaled-rank payload lemmas out of finite string diagrams.
  - Owner: `BijForm.CodeAlgebra`
  - Evidence: private `rank_scaled_payload_lt` and
    `rank_scaled_payload_le_with_gap` in
    `BijForm/StringDiagram/FiniteCoding/Syntax.lean`.
  - Action: publish general arithmetic/rank helper lemmas where examples can
    reuse them.
  - Validation: `#check BijForm.CodeAlgebra.rank_scaled_payload_lt` or the final
    chosen public name after importing `BijForm.CodeAlgebra`.

- [ ] Make closed-form pairing the single public product codec.
  - Owner: `BijForm.Pairing`
  - Evidence: scan-based `encode`/`decode`/`iso` and closed-form
    `encodeFast`/`decodeFast`/`isoFast` coexist.
  - Action: make the proved closed form the public pairing route; keep scan
    machinery private proof scaffolding only where needed.
  - Validation: `CodeAlgebra.prodNat` and all product-code users build through
    the closed-form public API.

## Examples

- [ ] Replace repeated `SyntaxPresentation.ofLayerMaps` inverse boilerplate.
  - Owner: `BijForm.DependentPolynomial` plus example modules.
  - Evidence: repeated same-fiber unpacking, `cases out_eq`, constructor cases,
    and `child_eta_*_rfl` in `Num`, `Peano`, `Lambda`, `HBT`, `FinChain`,
    `Sorted`, and `StringDiagram/Polynomial`.
  - Action: add a shared constructor-layer presentation helper that examples
    instantiate with domain-specific constructor clauses and rank.
  - Validation: source search for `SyntaxPresentation.ofLayerMaps` and
    `child_eta_*_rfl child` drops in examples.

- [ ] Factor finite and infinite sorted branch payload coding.
  - Owner: `BijForm.Examples.Sorted`, backed by `CodeAlgebra` payload lemmas.
  - Evidence: `SortedFiniteConstructorPayloadIso`,
    `SortedInfiniteConstructorPayloadIso`, and parallel child-rank proofs.
  - Action: create one branch payload iso and one rank lemma parameterized by
    pivot codec and child-bound witnesses.
  - Validation: source search for duplicated finite/infinite sorted payload
    proof blocks drops.

- [ ] Generalize typed-binding NF constructor-family carrier coding.
  - Owner: `BijForm.TypedBinding`
  - Evidence: `NFNormalFamilyCarrierIso`, `NFAppFamilyCarrierIso`, and long
    `NFGeneratedLayer_child_rank_lt` proof in
    `BijForm/Examples/TypedBinding/NF.lean`.
  - Action: add typed-binding helpers for finite constructor families by return
    sort and public rank lemmas for generated `LayerShape.familyCarrierIso`.
  - Validation: NF rank proof no longer unfolds `LayerShape.iso`,
    `ArgTuple.ofChild`, and codec internals repeatedly.

- [ ] Replace HBT child-swap normal-form boilerplate with quotient helpers.
  - Owner: `BijForm.QuotientPolynomial` and `BijForm.CodeAlgebra`
  - Evidence: manual `HBTChildSwapNorm`, `HBTChildSwapDenorm`, and binary swap
    relation proofs in `BijForm/Examples/HBTQuotient.lean`.
  - Action: add generic binary child swap quotient descent and route unordered
    pair coding through existing `CodeAlgebra.unorderedPair*` APIs.
  - Validation: HBT quotient example exposes the same public final isomorphisms
    through generic quotient descent.

- [ ] Generate finite string-diagram entry tables for finite signatures.
  - Owner: `BijForm.StringDiagram.FiniteCoding.Syntax`
  - Evidence: manual `SINEntry` decidable equality, unary table, and non-unary
    table in `BijForm/Examples/SymmetricInteractionNet.lean`.
  - Action: build unary and non-unary `FiniteSubtypeTable`s from node
    enumeration and arity data.
  - Validation: source search for `SINEntry.decidableEq`,
    `SINUnaryEntryTable`, and `SINNonUnaryEntryTable` drops or becomes a small
    instantiation of the generic table builder.

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
