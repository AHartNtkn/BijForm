# Project Instructions

## Goal

This repository formalizes bijective encodings in Lean, starting from the two
source blog posts named in `prompt`. The deliverable is a Lean development that
proves the simpler optimal-feasible pairing function is a bijection and develops
a useful general theorem for bijective codings of dependent inductive types
defined as initial algebras of dependent polynomial functors.

The formalization targets are the pairing-function construction in
"An Optimal And Feasible Pairing Function" and the dependent Gödel-encoding
scheme in "Basic Bijective Godel Encodings". The target is not merely an
existence theorem that assumes constructor-level isomorphisms as opaque input;
the formalization should expose reusable conditions under which the required
fiberwise constructor isomorphisms are generated, especially conditions based
on invertible changes to output indices.

## Formalization Standard

Formalize every paper claim that can be formalized faithfully under the
definitions already established in Lean. When a claim needs a stronger
assumption, a different statement, a missing definition, or a counterexample
appears, record the issue explicitly and stop only the work that depends on
that unresolved issue. Continue formalizing independent later claims.
Unattempted or not-yet-reached paper targets are pending inventory, not proof
gaps. Do not record a proof gap merely because a target is pending. If you claim
that blockers have been identified for any scope, then every unformalized target
in that scope must be explicitly linked to an open proof gap that blocks that
target. Do not stop globally unless every remaining avenue for faithful
formalization is stopped by recorded open issues.

Committed `sorry` declarations are allowed for standard Lean blueprinting,
pending proof work, and proof-gap marking. They must be labeled as unfinished
and must not be counted as completed proofs or faithful closed formalizations of
paper targets. Never make Lean accept a paper flaw by weakening a theorem
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

If Lean exposes a blocker, preserve the original claim's identity and paper
location in the proof-gap record. Do not implement or package hypothetical
replacement statements as tracked Lean declarations for a paper claim stopped by
an open proof gap. Needed corrections remain proof gaps until the paper actually
changes. A theorem with stronger assumptions or a changed conclusion may be kept
only as a conditional auxiliary lemma when its hypotheses explicitly name the
missing obligation and its comment does not claim to formalize the original
paper theorem. Do not create corrected predicates, repaired definitions, or
substitute theorem packages for paper claims stopped by an open proof gap.

Conditional auxiliaries are diagnostic evidence only. Do not describe them as
finishing, discharging, repairing, or formalizing a paper target stopped by an
open proof gap, and do not count them as removing a proof gap. If a declaration
depends on an unresolved proof gap, its comment must name the added premise or
changed conclusion before relating it to the paper location.
Do not use context-dependent shorthand that identifies a conditional or
proof-gap evidence declaration only by its relation to paper indices. The
comment must first state the diagnostic status and the explicit added
obligations.
The existence of a tracked auxiliary near a paper theorem is never completion
evidence for the paper theorem unless the declaration is the faithful theorem
itself.

Do not silently normalize source-level defects in paper symbols or formulas. If
the paper uses an undefined name, misspelled notation, wrong arity, or ill-typed
expression, record the defect before tracking any Lean declaration that uses an
intended reading. The declaration comment must identify the literal source
defect and state that the intended reading is boundary evidence, not a literal
formalization of the defective text.

Lean comments are part of the formalization boundary. Use an unqualified
"Paper line ..." declaration comment only for a faithful paper statement or a
direct faithful component. Conditional auxiliaries, interpreted variants,
strict variants, counterexamples, and proof-gap evidence lemmas must say so at the
declaration site and must not imply that the original paper claim has been
formalized.

Proof-gap records are blockers for dependent paper targets, not blocked targets
themselves. Do not describe a proof gap as something to bypass, fix in Lean, or
discharge by inventing a corrected statement. A dependent target can resume only
after the paper statement changes or the missing paper obligation is supplied
explicitly by the paper.

Recording a proof gap is never a global stop condition by itself. If the gap
currently blocks no named downstream paper target, say so in the record and
continue formalizing independent claims.

## Repository Boundaries

`references/` is local source evidence and must stay ignored by git. Do not
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
misleading status labels. Do not use hyphenated paper/index status wording in
tracked source; use neutral Lean-indexed wording for index translations and
diagnostic conditional wording for conditional auxiliaries.

After changing repository setup or project policy, verify that `references/`
does not appear as an untracked path in `git status --short`.

## Git Hygiene

Commit completed work frequently after validation. Do not end a turn with a
dirty repository when the remaining changes are intended to be kept.
