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
  - Replace with: one `FrontierCase` table or eliminator that stores the
    allowed constructor case, carrier iso, child carrier, and rank contribution.
  - Validation:
    `lake env lean BijForm/StringDiagram/FiniteCoding/Syntax.lean`, `lake build`,
    `git diff --check`, and a scoped source scan over
    `singleSortedFiniteLayerShape`, `singleSortedFiniteLayerShapeCarrierIso`,
    `singleSortedFiniteLayerToShape`, `singleSortedFiniteLayerFromShape`,
    `singleSortedFiniteLayer_left_inv`, `singleSortedFiniteLayer_right_inv`, and
    `singleSortedFiniteLayer_shape_child_rank_lt` that requires
    `openBoundaryCases` in each block and rejects direct list-boundary equation
    clauses or local `cases boundary/frontier/rest` classification.
  - Completed: `BijForm.StringDiagram.FiniteCoding.Syntax` now owns boundary
    classification through `openBoundaryCases` for the layer shape, carrier
    iso, layer-to-shape map, shape-to-layer map, inverse proofs, and child-rank
    proof. One-frontier entry arity dispatch remains isolated in
    `singleSortedFiniteOneFrontierBudShape` and is not a frontier classifier.

- [ ] Finish deleting raw string-diagram index transport scaffolding.
  - Owners: `BijForm.StringDiagram.Basic`,
    `BijForm.StringDiagram.Bridge.GraphRenderRelation`,
    `BijForm.StringDiagram.Renderer.Core`,
    `BijForm.StringDiagram.Renderer.Steps`,
    `BijForm.StringDiagram.Renderer.Trace`,
    `BijForm.StringDiagram.Traversal.State`, and
    `BijForm.StringDiagram.Hypergraph`.
  - Why this remains open: source scan still shows direct `Fin.cast` use in
    renderer, traversal, hypergraph, and bridge files, including over one
    hundred hits in `GraphRenderRelation.lean`.
  - Delete: proof-body `Fin.cast` chains, repeated length-congruence casts,
    manual `get` transport proofs, and old/new index reconstruction at call
    sites.
  - Replace with: owner-level list/index transport APIs for endpoint, edge,
    node, incident-slot, pending, erased, appended, and tail indices. Callers
    should use semantic transport lemmas, not raw casts.
  - Validation:
    `rg -n "Fin\\.cast" BijForm/StringDiagram/Bridge BijForm/StringDiagram/Renderer BijForm/StringDiagram/Traversal BijForm/StringDiagram/Hypergraph.lean`
    should be empty outside owner helper implementations.
  - Partial: `GraphRenderRelated`, `FrontierPendingFields`, and
    `NodeIncidentFields` now expose `listIndexCast` in their field statements
    instead of raw relation-boundary casts. The connect/bud child label proofs
    also use append-trace right indices plus `listIndexCast` instead of local
    `childIndex := Fin.cast ...` boilerplate. A follow-up edge-left/right and
    bud node-incident pass removed the remaining bridge-local raw casts, so
    `GraphRenderRelation.lean` direct `Fin.cast` hits dropped from `103` to
    `0`. Hypergraph proof-body casts now route through `listIndexCast`,
    `eraseFin_eq_of_eq_of_val_eq`, and signature node-port index helpers;
    `Hypergraph.lean` direct `Fin.cast` hits are down to the two
    `PortHypergraphIso` incidence-slot transport helper implementations. The
    item remains open because renderer and traversal casts still remain.

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

- [ ] Finish payload-local inverse boilerplate removal in coding examples.
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

- [ ] Finish typed-binding proof-surface cleanup.
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

- [ ] Delete specialized nested-code theorem surfaces after generic routing.
  - Owner: `BijForm.CodeAlgebra`.
  - Why this remains open: `CodeAlgebra.lean` still contains specialized theorem
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

- [ ] Make packaged render evidence the only bridge-visible invariant API.
  - Owners: `BijForm.StringDiagram.Hypergraph` and
    `BijForm.StringDiagram.Bridge`.
  - Why this remains open: `RenderTraceEvidence` now exists, but the raw
    `openEvidenceOfInvariants` constructor is still a visible lower-level
    surface.
  - Delete: bridge-facing raw invariant tuple assembly and any public raw
    constructor that lets callers bypass the evidence package.
  - Replace with: package constructors and projections as the only public API
    consumed outside the semantic graph owner.
  - Validation:
    `rg -n "openEvidenceOfInvariants|hv hp hn pref ho hall" BijForm/StringDiagram/Bridge BijForm/StringDiagram/FiniteCoding BijForm/StringDiagram/Renderer BijForm/StringDiagram/Traversal --glob '*.lean'`
    should show no bridge-facing raw invariant assembly.

## Second-Pass Simplification Work

- [ ] Collapse remaining traversal connect/bud branch facts into first-pending
  schemas.
  - Owners: `BijForm.StringDiagram.Traversal.State` and
    `BijForm.StringDiagram.Traversal.Search`.
  - Why this remains open: the completed tracker item says branch connect/bud
    lemmas remain as low-level implementation facts. That is slice-complete,
    not maximal simplification.
  - Delete: branch-specific wrappers that repeat pending, seen, processed,
    frontier-completeness, remaining-edge descent, and iso-preservation facts.
  - Replace with: first-pending child schemas whose connect and bud cases are
    small data constructors, not duplicated proof families.
  - Validation:
    `rg -n "connectChild|budChild|firstPendingChild|RenderPrefixChildStep|IsoImage" BijForm/StringDiagram/Traversal BijForm/StringDiagram/Bridge --glob '*.lean'`
    should show the generic first-pending surface as the public path and no
    duplicate connect/bud preservation families at call sites.

- [ ] Delete low-value generated-code and presentation pass-through wrappers.
  - Owners: `BijForm.InitialAlgebra`,
    `BijForm.DependentPolynomial`, and examples using generated codes.
  - Why this remains open: the branch moved major machinery into
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

- [ ] Revisit `ListPiTuple` and typed-binding tuple helper placement for
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

- [ ] Re-open checked tracker items that are only targeted-slice complete.
  - Owner: `SIMPLIFICATION_TODO.md`.
  - Why this remains open: several checked items contain notes such as
    `Partial`, `remaining`, `remain`, or describe low-level implementation facts
    that still exist. Those checkmarks are historical slice status, not proof
    that the branch is maximally simplified.
  - Delete: misleading completion wording that implies the whole class is done
    when residual old-model source remains.
  - Replace with: links from the old tracker entries to this debt tracker, or
    split the old entries into "completed slice" and "remaining deletion work".
  - Validation:
    `rg -n "Partial|remaining|remain|still|open" SIMPLIFICATION_TODO.md`
    should not find unchecked debt hidden under checked completion claims.

## Branch Exit Criteria

- [ ] `git diff --shortstat master...HEAD` is deletion-heavy, or every net
  insertion is attached to a smaller public API and a larger deleted local proof
  surface.
- [ ] `lake build` passes after the cleanup branch.
- [ ] `git diff --check` passes.
- [ ] The item-specific scans above show no old-model proof bodies, duplicate
  construction paths, or obsolete public wrappers outside their owner
  implementation sites.
- [ ] The original `SIMPLIFICATION_TODO.md` does not present targeted slices as
  total simplification when this file still contains corresponding open debt.
