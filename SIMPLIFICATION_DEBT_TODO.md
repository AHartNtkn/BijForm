# Simplification Debt Todo

This file tracks remaining cleanup needed after the current
`simplify-generated-spine` branch. It is not a completion report. An item is
open until the old local proof shape, duplicate path, public wrapper, or manual
case split has been deleted, not merely hidden behind a new helper.

Pre-tracker branch size against `master`, measured before adding this file:

- `35 files changed, 11264 insertions(+), 9717 deletions(-)`
- Net: `1547` more inserted lines than deleted lines

That ratio is not acceptable simplification evidence by itself. The work below
is ordered to turn helper additions into actual deletion.

## Completion Rules

- Run `git diff --shortstat master...HEAD` before and after each item.
- A helper addition only counts as simplification when it deletes more local
  proof or construction code than it adds, or when it replaces a larger public
  surface with a smaller one.
- Do not keep old names as aliases, public wrappers, or pass-through views just
  to preserve current callers. Update callers and delete the obsolete surface.
- Validation is `lake build`, `git diff --check`, and the item-specific source
  scans listed below. Do not add hook, CI, or audit-executable infrastructure
  for this tracker.

## High-Priority Deletion Work

- [x] Table-drive finite string-diagram frontier cases.
  - Owner: `BijForm.StringDiagram.FiniteCoding.Syntax`.
  - Original debt: the original tracker still had this unchecked, and
    finite layer definitions repeated frontier cardinality classification
    across the shape carrier, carrier iso, maps, inverse proofs, and rank proof.
  - Delete: repeated frontier cardinality splits across layer shape, carrier
    iso, to/from shape maps, inverse proofs, and rank proofs.
  - Replace with: one `SingleSortedFiniteFrontierCase` owner that stores the
    shape, carrier iso, layer-to-shape map, and shape-to-layer map for a
    boundary; public layer surfaces are projections from that owner.
  - Validation:
    `lake env lean BijForm/StringDiagram/FiniteCoding/Syntax.lean`, `lake build`,
    `git diff --check`, and a scoped source scan over
    `singleSortedFiniteLayerShape`, `singleSortedFiniteLayerShapeCarrierIso`,
    `singleSortedFiniteLayerToShape`, and `singleSortedFiniteLayerFromShape`
    that requires projection from `singleSortedFiniteFrontierCase` and rejects
    separate `openBoundaryCases` bodies; inverse and rank proofs may eliminate
    frontier cases only after consuming those projection surfaces.
  - Completed: `BijForm.StringDiagram.FiniteCoding.Syntax` now owns boundary
    classification through `singleSortedFiniteFrontierCase`; the layer shape,
    carrier iso, layer-to-shape map, and shape-to-layer map are projections from
    that owner. One-frontier entry arity dispatch is data inside that frontier
    case rather than a separate frontier classifier.

- [x] Finish deleting raw string-diagram index transport scaffolding.
  - Owners: `BijForm.StringDiagram.Basic`,
    `BijForm.StringDiagram.Bridge.GraphRenderRelation`,
    `BijForm.StringDiagram.Renderer.Core`,
    `BijForm.StringDiagram.Renderer.Steps`,
    `BijForm.StringDiagram.Renderer.Trace`,
    `BijForm.StringDiagram.Traversal.State`, and
    `BijForm.StringDiagram.Hypergraph`.
  - Original debt: source scan still showed direct `Fin.cast` use in renderer,
    traversal, hypergraph, and bridge files, including over one hundred hits in
    `GraphRenderRelation.lean`.
  - Delete: proof-body `Fin.cast` chains, repeated length-congruence casts,
    manual `get` transport proofs, and old/new index reconstruction at call
    sites.
  - Replace with: owner-level list/index transport APIs for endpoint, edge,
    node, incident-slot, pending, erased, appended, and tail indices. Callers
    should use semantic transport lemmas, not raw casts.
  - Validation:
    `rg -n "Fin\\.cast" BijForm/StringDiagram/Bridge BijForm/StringDiagram/Renderer BijForm/StringDiagram/Traversal BijForm/StringDiagram/Hypergraph.lean`
    should be empty outside owner helper implementations.
  - Completed: `GraphRenderRelated`, `FrontierPendingFields`, and
    `NodeIncidentFields` now expose `listIndexCast` in their field statements
    instead of raw relation-boundary casts. The connect/bud child label proofs
    also use append-trace right indices plus `listIndexCast` instead of local
    `childIndex := Fin.cast ...` boilerplate. A follow-up edge-left/right and
    bud node-incident pass removed the remaining bridge-local raw casts, so
    `GraphRenderRelation.lean` direct `Fin.cast` hits dropped from `103` to
    `0`. Hypergraph proof-body casts now route through `listIndexCast`,
    `eraseFin_eq_of_eq_of_val_eq`, and signature node-port index helpers;
    `Hypergraph.lean` direct `Fin.cast` hits dropped to `0`. The
    renderer trace rest/fresh-node edge expressions now use `listIndexCast`,
    so `Renderer/Trace.lean` direct `Fin.cast` hits dropped to `0`. The item
    renderer `connectStep_*_get` lemmas now delegate to
    `list_get_of_eq_of_val_eq`, and the old-node incident-label proof now uses
    `Sig.nodePortIndexOfLength`; `Renderer/Steps.lean` direct `Fin.cast` hits
    dropped to `0`. Renderer core incident evidence, incident lookup proofs,
    tail frontier labels, and node-incident nodup recursion now use
    `listIndexCast` and `Sig.nodePortIndexOfLength`. Traversal helper
    definitions for rest-label indices, bud entries, connect-child pending
    labels, and connect-child endpoint-order gets now use shared list/signature
    transport; render-prefix connect/bud child proof clusters now use
    `listMapIndex`, `listIndexCast`, and `eraseFin_eq_of_eq_of_val_eq`, so
    `Traversal/State.lean` direct `Fin.cast` hits dropped to `0`. The broad
    validation scan over `Bridge`, `Renderer`, `Traversal`, and
    `Hypergraph.lean` is empty; raw casts remain only in owner-level generic
    helpers outside that consumer boundary.

- [ ] Collapse the graph-render relation helper volume into schemas.
  - Owners: `BijForm.StringDiagram.Bridge.GraphRenderRelation`,
    `BijForm.StringDiagram.Renderer.Trace`, and
    `BijForm.StringDiagram.Renderer.Steps`.
  - Why this remains open: the branch deletes a lot from
    `GraphRenderRelation.lean`, but the file still has the largest residual
    proof surface and many repeated endpoint, edge, node, incident, and order
    field preservation proofs.
  - Delete: connect/bud-specific copies of the same field-preservation facts,
    repeated endpoint-left/right index proofs, duplicated order-length proofs,
    and local relation constructors that only reassemble the same record shape.
  - Replace with: generic render-step field schemas for endpoint, edge, node,
    incident-slot, pending, and trace-order preservation, instantiated once for
    connect and bud.
  - Validation:
    `git diff --stat master...HEAD -- BijForm/StringDiagram/Bridge/GraphRenderRelation.lean`
    should move materially toward deletion, and the raw `Fin.cast` scan for
    this file should approach zero outside owner transport lemmas.
  - Partial: label preservation now uses shared append-trace schemas
    `GraphRenderRelated.endpointLabel_of_appendTrace`,
    `GraphRenderRelated.edgeLabel_of_appendTrace`, and
    `GraphRenderRelated.nodeLabel_of_appendTrace`; bridge proofs also consume
    `AppendTraceRelation.get_listIndexCast` for the common right-index
    transport step instead of repeating local `rightIndex = listIndexCast`
    proof blocks. The old connect/bud label helper theorem declarations were
    deleted, and final child relation assembly now calls the schemas directly.
    Renderer trace first-new edge/node indices now instantiate generic
    `AppendStep.firstSuffixIndex` / `get_firstSuffixIndex`, and unused
    `_new_*Index_val` wrappers were deleted. The single-use
    `connectChild_nodeIncidentFields` and `connectChild_nodeIncident` helper
    theorem surfaces were deleted; their proof work is local to
    `connectChild` assembly now. The item remains open because
    pending/frontier alignment and final connect/bud record assembly are still
    separate helper families.
  - Partial: single-use `connectChild_edgeEndpointBounds` was deleted; connect
    child assembly now uses the branch-independent
    `GraphRenderRelated.edgeEndpointBounds_of_appendTrace` schema. The item
    remains open for pending/frontier alignment and final connect/bud record
    assembly.
  - Partial: branch-specific edge-side theorem surfaces
    `connectChild_edgeLeft`, `connectChild_edgeRight`, `budChild_edgeLeft`,
    and `budChild_edgeRight` were deleted. Connect and bud assembly now use
    `GraphRenderRelated.edgeEndpointSide_of_appendTrace` with branch-local
    suffix endpoint witnesses. The item remains open for pending/frontier
    alignment and final connect/bud record assembly.
  - Partial: bud-specific node-incident wrappers
    `budChild_nodeIncidentFields` and `budChild_nodeIncident` were deleted.
    Connect and bud assembly now use
    `GraphRenderRelated.nodeIncidentFields_of_appendTrace` and
    `GraphRenderRelated.nodeIncident_of_appendTrace`. The item remains open
    for pending/frontier alignment and final connect/bud record assembly.

- [x] Finish payload-local inverse boilerplate removal in coding examples.
  - Owners: `BijForm.InitialAlgebra`,
    `BijForm.StringDiagram.FiniteCoding.Syntax`,
    `BijForm.Examples.Num`, `BijForm.Examples.Peano`,
    `BijForm.Examples.Sorted`, and `BijForm.TypedBinding`.
  - Why this remains open: source scan still shows `heq_of_eq`,
    `child_eta_rfl child`, and `cases rest with` in examples and syntax
    presentations after the generic `CodeLayer` helpers were added.
  - Delete: local heterogeneous child equality witnesses, child eta closers,
    and ad hoc rest-list destructuring in inverse proofs.
  - Replace with: generic constructor-payload inverse lemmas for no-child,
    single-child, and multi-child constructors, placed in the lowest shared
    owner that can serve examples and typed binding.
  - Validation:
    `rg -n "heq_of_eq|child_eta_rfl child|cases rest with" BijForm/Examples BijForm/TypedBinding.lean BijForm/StringDiagram/FiniteCoding/Syntax.lean`
    should show only owner-level helper implementations or nothing.
  - Partial: `BijForm.Examples.Num` now routes same-constructor child eta
    branches through `CodeLayer.ext_rfl` instead of local `CodeLayer.ext_layer`
    plus `heq_of_eq`, and the local `child_eta_rfl child` endings there were
    deleted. `BijForm.TypedBinding` now uses direct nested sigma patterns for
    `FiberCode` var payloads, `ArgTuple.ofChild_toChild` for pair tuple
    reconstruction, and constructor-family inverse proofs rewrite through the
    existing argument-tuple and constructor-iso inverse facts instead of local
    `heq_of_eq` assembly. Peano Nat-layer no-child branches, the sorted leaf
    no-child branch, and the finite syntax finish branch now call the
    owner-level `finish_code_layer_left_inv` macro instead of spelling direct
    `child_eta_rfl child` locally.
  - Completed: the remaining example sum-tail destructuring in Num and Peano
    was replaced by direct nested structural patterns; Peano's equality branch
    now uses `CodeLayer.ext_rfl`; finite syntax connect/bud helper
    extensionality eliminates child equality before calling
    `CodeLayer.canonical_ext_param`. The payload scan over examples,
    `TypedBinding.lean`, and finite syntax is empty; only owner-level
    `InitialAlgebra.lean` macros still contain the generic eta tactic names.

- [x] Finish typed-binding proof-surface cleanup.
  - Owners: `BijForm.TypedBinding` and
    `BijForm.Examples.TypedBinding.NF`.
  - Why this remains open: the branch added more reusable typed-binding
    machinery, but `TypedBinding.lean` still has local rest destructuring and
    heterogeneous equality proof bodies, and `NF.lean` still exposes generic
    carrier-iso construction vocabulary.
  - Delete: NF proof-body dependence on generic implementation names such as
    `LayerShape.familyCarrierIso`, plus local `cases rest with`,
    `heq_of_eq`, and `child_eta_rfl child` proof fragments in typed-binding
    presentation proofs.
  - Replace with: public typed-binding/NF helper lemmas that state the intended
    layer and constructor-family facts directly. NF proofs should mention the
    NF proof surface, not the generic carrier-construction machinery.
  - Validation:
    `rg -n "LayerShape\\.familyCarrierIso|cases rest with|heq_of_eq|child_eta_rfl child" BijForm/TypedBinding.lean BijForm/Examples/TypedBinding/NF.lean`
    should have no old-model proof-body hits.
  - Completed: `LayerShape.familyCarrierIso` was deleted and replaced by the
    owner-level `LayerShape.carrierCoding`; NF shape encoders now consume that
    surface. `FiberCode.var_codeLayer_eta` and `FiberCode.op_codeLayer_eta`
    own the no-child and same-child layer eta proofs used by both syntax and
    layer-shape inverses, so the tracked local `child_eta_rfl child` and
    `heq_of_eq` fragments are gone from `TypedBinding.lean`.

- [x] Delete specialized nested-code theorem surfaces after generic routing.
  - Owner: `BijForm.CodeAlgebra`.
  - Original debt: `CodeAlgebra.lean` still contained specialized theorem
    families named for concrete nested shapes:
    `sumProdNat_toFun_*`, `natOrProdOrProdNat_toFun_*`, and
    `prodOrNatOrProdOrNat_toFun_*`.
  - Delete: specialized public theorem families whose only purpose is to keep
    old nested-code proof paths alive.
  - Replace with: generic declarative codec-builder bound lemmas and branch
    path/subcode lemmas used directly by examples.
  - Validation:
    `rg -n "sumProdNat_toFun|natOrProdOrProdNat_toFun|prodOrNatOrProdOrNat_toFun" BijForm --glob '*.lean'`
    should be empty unless a remaining name is the canonical generic theorem.
  - Completed: the specialized `*_toFun_*` theorem families were deleted.
    Remaining `sumProdNat` inverse proofs call generic `toNatSum_inr_lt_of_le`
    and `prodNat_toFun_*_le` facts directly, and the validation scan is empty.

- [x] Make packaged render evidence the only bridge-visible invariant API.
  - Owners: `BijForm.StringDiagram.Hypergraph` and
    `BijForm.StringDiagram.Bridge`.
  - Original debt: `RenderTraceEvidence` existed, but the raw
    `openEvidenceOfInvariants` constructor is still a visible lower-level
    surface. A second pass found the bridge/traversal relation surface still
    accepted projected `OpenPortHypergraphEvidence` rather than packaged render
    trace evidence.
  - Delete: bridge-facing raw invariant tuple assembly and any public raw
    constructor that lets callers bypass the evidence package.
  - Replace with: package constructors and projections as the only public API
    consumed outside the semantic graph owner.
  - Validation:
    `rg -n "openEvidenceOfInvariants|hv hp hn pref ho hall" BijForm/StringDiagram/Bridge BijForm/StringDiagram/FiniteCoding BijForm/StringDiagram/Renderer BijForm/StringDiagram/Traversal --glob '*.lean'`
    should show no bridge-facing raw invariant assembly.
  - Completed: the obsolete `openEvidenceOfInvariants` and diagram-level
    `renderTrace*_graphEvidence` / `renderTrace*_openEvidence` helper surfaces
    were deleted. `RenderPrefixRelated`, `RenderPrefixChildStep`, and syntax
    round-trip bridge proofs now take `RenderState.RenderTraceEvidence`
    directly and project `toOpenPortHypergraph` / `toPortHypergraph` from that
    package. The validation scan above is empty, the old helper-name scan is
    empty, and a signature scan for bridge/traversal `OpenPortHypergraphEvidence`
    render-prefix parameters is empty.

## Second-Pass Simplification Work

- [x] Collapse remaining traversal connect/bud branch facts into first-pending
  schemas.
  - Owners: `BijForm.StringDiagram.Traversal.State` and
    `BijForm.StringDiagram.Traversal.Search`.
  - Original debt: the completed tracker item said branch connect/bud lemmas
    remained as low-level implementation facts. That was slice-complete, not
    maximal simplification.
  - Complete: branch computation, frontier-completeness, termination,
    render-prefix, iso, order-trace, and endpoint/edge/node order wrappers
    were folded into first-pending schemas. The public path is now
    `FirstPendingStep`, `firstPendingChild_*`,
    `RenderPrefixRelated.firstPendingChild`, `IsoRelated.firstPendingChild`,
    and `firstPendingChild_orderTrace`.
  - Validation: scans are empty for the deleted connect/bud wrapper names and
    positive for the first-pending traversal/order schemas.

- [x] Delete low-value generated-code and presentation pass-through wrappers.
  - Owners: `BijForm.InitialAlgebra`,
    `BijForm.DependentPolynomial`, and examples using generated codes.
  - Original debt: the branch moved major machinery into
    `InitialAlgebra.lean` and added views around canonical generated code, but
    line count still increased. Public views that only preserve old naming are
    remaining debt.
  - Delete: pass-through generated-code aliases, presentation views, conversion
    helpers, and wrapper theorems that do not expose a distinct mathematical
    concept.
  - Replace with: one canonical generated-code API plus only the examples'
    genuinely readable entry points.
  - Validation:
    `rg -n "toGeneratedCode|GeneratedShapeCode|GeneratedRankedNatCode|GeneratedNatCode|NatLayerPresentation|RankedNatLayerPresentation|ShapeLayerPresentation" BijForm --glob '*.lean'`
    should justify each remaining public name as canonical, not transitional.
  - Completed: forwarding methods in the `GeneratedNatCode`,
    `GeneratedRankedNatCode`, `NatLayerPresentation`,
    `RankedNatLayerPresentation`, and `ShapeLayerPresentation` namespaces were
    deleted, as were `GeneratedCode.natCodeIso` and
    `GeneratedCode.rankedNatCodeIso`; the redundant `GeneratedRankedNatCode`
    alias was also deleted. Examples now use `LayerPresentation.generatedCode`,
    `GeneratedCode.codeIso`, and direct `ShapeLayerPresentation` records. The
    remaining broad-scan names are canonical data types, real constructors such
    as Nat/ranked layer presentation constructors and typed-binding
    `toGeneratedCode`, or example-level generated-code deliverables.

- [x] Revisit `ListPiTuple` and typed-binding tuple helper placement for
  maximal visibility.
  - Owners: `BijForm.DependentTuple`, `BijForm.TypedBinding`, and
    `BijForm.InitialAlgebra`.
  - Why this remains open: tuple machinery was moved out of typed binding, but
    remaining example and presentation inverse proofs still destruct tuple/rest
    shapes manually.
  - Delete: typed-binding-only tuple wrappers and local child tuple
    reconstruction proofs that should be generic.
  - Replace with: shared tuple/list child reconstruction lemmas used by
    typed-binding, finite string diagrams, and example presentations.
  - Validation:
    source scans for `cases rest with`, `ListPiTuple.ofPi`, and
    `ArgTuple.ofChild` should show generic owner definitions plus direct
    semantic use, not proof-body plumbing.
  - Partial: `TypedBinding.FiberCode` no longer destructs nested var payloads
    through local `cases rest with`, and `ArgTuple.pairIso` now uses
    `ArgTuple.ofChild_toChild` instead of manually destructing the two-element
    tuple tail.
  - Completed: `ArgTuple.singleIso` now also delegates its left inverse to
    `ArgTuple.ofChild_toChild`. Tuple conversion hits are owner definitions,
    inverse lemmas, or semantic construction sites; the only remaining
    `cases tuple with` scan hit is inside the owner proof
    `ListPiTuple.ofPi_toPi`.

- [x] Delete the old tracker that marked targeted slices as complete.
  - Owner: `SIMPLIFICATION_TODO.md`.
  - Original debt: checked entries in the old tracker contained notes such as
    `Partial`, `remaining`, `remain`, or described low-level implementation
    facts that still existed. Those checkmarks were historical slice status,
    not proof that the branch was maximally simplified.
  - Delete: misleading completion wording that implied the whole class was done
    when residual old-model source remained.
  - Replace with: this debt tracker as the single tracked TODO for remaining
    simplification work on the branch.
  - Validation:
    `git ls-files SIMPLIFICATION_TODO.md` should be empty, and
    `rg --files -g '*TODO*' -g '*TOOD*'` should only report this debt tracker.
  - Completed: the old `SIMPLIFICATION_TODO.md` was deleted in commit
    `40b9f0c`; the only tracked TODO-like file is now
    `SIMPLIFICATION_DEBT_TODO.md`.

## Branch Exit Criteria

- [ ] `git diff --shortstat master...HEAD` is deletion-heavy, or every net
  insertion is attached to a smaller public API and a larger deleted local proof
  surface.
- [ ] `lake build` passes after the cleanup branch.
- [ ] `git diff --check` passes.
- [ ] The item-specific scans above show no old-model proof bodies, duplicate
  construction paths, or obsolete public wrappers outside their owner
  implementation sites.
- [x] The original `SIMPLIFICATION_TODO.md` does not present targeted slices as
  total simplification when this file still contains corresponding open debt.
