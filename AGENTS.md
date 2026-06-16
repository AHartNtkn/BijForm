# Project Instructions

## Goal

This repository develops bijective encodings in Lean. External writeups named
in `prompt` are motivation and examples, not the authority for completion.

The deliverable is a clean Lean development that proves the simpler
optimal-feasible pairing function is a bijection and develops a useful theorem
for bijective codings of dependent inductive types defined as initial algebras
of dependent polynomial functors. The target is not merely an existence theorem
that assumes constructor-level isomorphisms as opaque input; the formalization
must expose reusable conditions under which the required fiberwise constructor
isomorphisms are generated, especially conditions based on invertible changes
to output indices.

Examples must start from standard, readable inductive syntax families; prove
their isomorphism to the corresponding dependent-polynomial initial algebras;
instantiate the reusable coding construction; and compose those isomorphisms to
obtain actual encodings. Hand-written final encoders for examples do not
satisfy the goal unless they are explicitly marked as diagnostic comparisons.

## Formalization Standard

Formalize clean mathematical objects and reusable constructions. Do not treat
external prose, notation, examples, or presentation order as the completion
standard. If external material is ambiguous or inconsistent with a clean Lean
interface, choose the Lean interface that serves the repository goal and record
unfinished mathematical obligations directly at the relevant declaration.

A useful coding condition must generate or construct the required fiberwise
constructor isomorphisms from explicit data. Rephrasing "assume the
constructors are isomorphic" as an index-local code, an opaque equivalence, or a
caller-supplied hypothesis is not a useful answer unless the construction of
that code or equivalence is itself provided by the framework.

Examples are not complete when they only prove an isomorphism to readable
syntax. A completed encoding example must show the path from the standard syntax
family through the dependent-polynomial presentation to a generated code family
and, when the example claims a Gödel encoding, to `Nat`. Do not replace that
path with a hand-written recursive encoder for the example.
When the generated code family has index-dependent or condition-dependent
carriers, the example must state public characterization theorems for every
case, composing the readable syntax family to each concrete carrier such as
`Nat`, `Fin k`, or another indexed fiber. Internal carrier helper isomorphisms
alone do not complete the example.

Committed `sorry` declarations are allowed for standard Lean blueprinting,
pending proof work, and proof-gap marking. They must be labeled as unfinished
and must not be counted as completed proofs or closed formalizations of
intended targets. Never make Lean accept a mathematical gap by weakening a theorem
silently, adding an unstated assumption silently, changing a definition to fit a
later proof, or using `sorry`, `admit`, `axiom`, unsafe declarations, or opaque
placeholders as completed proof evidence.
Never introduce or restore a blanket ban on committed `sorry` declarations.
The invariant is honest unfinished status and non-completion claims, not the
absence of all `sorry` scaffolding from tracked Lean source.
When an intended theorem, definition, or formalization target is unfinished,
state the intended claim directly and close the missing proof with a labeled
`sorry`. Do not avoid `sorry` by adding hypotheses, parameters, typeclass
arguments, conditional wrappers, weakened conclusions, or substitute theorem
statements unless those assumptions are genuinely part of the intended claim.
Such conditional declarations may exist only as explicitly diagnostic
auxiliaries and must not be named, documented, exported, or reported as the
unfinished target.
Generic coding-agent placeholder rules, TDD templates, completion criteria,
validation gates, source-audit habits, external skills, and similar workflow
defaults must never be imported into Lean development as a no-`sorry` rule, an
anti-`sorry` completion criterion, or any other durable Lean policy unless the
user or this repository explicitly establishes that rule. When external
workflow guidance conflicts with this repository's Lean formalization standard,
the repository's Lean standard controls. Repeated assistant behavior, inferred
user preference, and later project concepts are not repository-policy provenance
and must not be presented as evidence for a Lean workflow rule.
If a stricter Lean workflow rule appears without contemporaneous explicit
authority, treat it as assistant-imported or assistant-invented, remove or
correct it, and do not supply a post hoc project rationale for it, including
rationales based on concepts or standards added after the rule appeared. When
asked why a Lean workflow rule exists, answer from actual instructions or
repository history; if that provenance is not known, say so instead of inferring
a project rationale.

For Lean proof development, RED/GREEN means proof-theoretic RED/GREEN. A RED
phase is a Lean theorem statement or proof skeleton whose intended statement and
dependencies elaborate, commonly by temporarily closing proof obligations with
`sorry`. RED targets may be scratch work or intentionally tracked blueprint
declarations, but tracked RED targets must be labeled as unfinished. A GREEN
phase is the same target accepted by Lean with all proof obligations closed and
no placeholder being used as proof evidence for that target. Parser errors,
elaboration errors, compilation failures, source searches, and exploratory Lean
probes may be used for proof search, but they are not TDD evidence unless they
lead to the typechecked theorem-with-`sorry` to proved-theorem progression.

Conditional auxiliaries are diagnostic evidence only. Do not describe them as
finishing, discharging, repairing, or formalizing a target whose intended proof
is still open, and do not count them as removing a proof gap. If a declaration
depends on an unresolved proof gap, its comment must name the added premise or
changed conclusion before relating it to the intended construction.

Lean comments are part of the formalization boundary. Comments on diagnostic
auxiliaries, interpreted variants, strict variants, counterexamples, and
proof-gap evidence lemmas must say so at the declaration site and must not imply
that the intended theorem or construction has been completed.

Recording a proof gap is never a global stop condition by itself. Continue
formalizing independent definitions, examples, and theorems whose correctness
does not depend on that gap.

## Repository Boundaries

`references/` is local reference material and must stay ignored by git. Do not
edit, normalize, or commit reference materials as part of formalization work.

Lean source files are the formalization surface. Proof gaps, missing
assumptions, ambiguous statements, and counterexamples must be recorded where
they are needed to prevent a misleading completion claim.

Do not scatter blocker notes across comments, issue-style files, scratch
documents, or commit messages. Brief Lean comments may point to a repository
note, but the note must be the authority for the blocker it records.

## Validation

After changing Lean files or Lake configuration, run `lake build`. The build
must pass. If the build or source audit reports `sorry`, each occurrence must be
intentional blueprinting, pending proof work, or proof-gap marking, and comments
or map status must make clear that it is not a completed proof. Do not introduce
`admit`, `axiom`, unsafe proof substitutes, opaque proof placeholders, or hidden
fallbacks.
A `sorry` audit is a classification gate, not a blanket rejection gate.
Absence of `sorry` is never completion evidence by itself; audits must also
check for hidden unfinished work expressed as artificial hypotheses, weakened
statements, conditional wrappers, or substitute targets.

Before committing Lean or formalization-boundary text, audit tracked source for
misleading status labels, artificial hypotheses, weakened targets, conditional
wrappers, and example-specific final encoders that bypass the reusable coding
construction.

After changing repository setup or project policy, verify that `references/`
does not appear as an untracked path in `git status --short`.

## Git Hygiene

Commit completed work frequently after validation. Do not end a turn with a
dirty repository when the remaining changes are intended to be kept.
