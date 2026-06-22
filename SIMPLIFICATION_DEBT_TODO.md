# Simplification Debt TODO

This file tracks unfinished cleanup only. Completed simplifications live in the
git history for this branch.

## Open Work

- [ ] Collapse the remaining graph-render relation assembly.
  - Owners: `BijForm.StringDiagram.Bridge.GraphRenderRelation`,
    `BijForm.StringDiagram.Renderer.Trace`, and
    `BijForm.StringDiagram.Renderer.Steps`.
  - Remaining debt: `GraphRenderRelated.connectChild_frontierPending`,
    `GraphRenderRelated.budChild_frontierPending`, and the final
    `GraphRenderRelated.connectChild` / `GraphRenderRelated.budChild` record
    assembly still expose branch-specific proof surfaces.
  - Replace with: a branch-independent frontier/pending alignment schema and,
    if it reduces proof volume rather than moving it, a shared child-relation
    assembly path parameterized by first-pending branch data.
  - Do not count this complete while connect/bud-specific frontier/pending
    wrappers remain, or while final graph relation assembly still duplicates
    the same record-field wiring.
  - Validation: `lake build`, `git diff --check`, a source scan showing no
    renamed connect/bud frontier-pending wrappers, and a branch diff that is
    deletion-heavy or has every remaining net insertion justified.

## Branch Exit Checks

- [ ] `git diff --shortstat master...HEAD` is deletion-heavy, or every net
  insertion is justified as reusable library surface rather than cleanup
  bookkeeping.
- [ ] `lake build` passes.
- [ ] `git diff --check` passes.
- [ ] Item-specific scans show no old-model proof bodies, duplicate helper
  wrappers, or compatibility aliases for deleted simplification targets.
