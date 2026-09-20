# CUCB descriptive evidence: extraction and provenance

This is a reproducible development record for the combinatorial ICLR case.
It describes actual proof references and accepted mathematical scope, not a
controlled efficiency experiment. The complete ten-topic evaluation remains open.

## Scope and snapshots

The compiled graph is pinned to
`b79f236c648c087f49c982f964f9b9e763d5b0e4`. It selects the 38 production owner
modules bound in `cucb-semantic-review.json`, including the finite examples.
The six `Tests` modules in that review packet are not graph seeds. The public
root was incrementally rebuilt before extraction: 9,017 jobs passed. This is
separate from the preceding full production validation at
`7853623e13de040e2feccc7e7c2a8e4b18ff6eea` (root, Tests, 437 Python tests with
seven skips, contributor contract and local site checks).

The graph has SHA-256
`5a9605a3c1870273df7b6d5ae6d7db0b52d219ca43c7620902e7a1927bc7d691`.
It contains 739 CUCB-owned declarations, 1,673 direct boundary nodes, 44,048
direct reference edges and 113 module-import records. These counts include
definitions, generated declarations, type references and proof references;
they are not new-theorem counts. Imports are not theorem implications.

## What the reuse counts mean

The extractor resolves each seed's actual Lean environment owner. It does not
use a namespace prefix or trust a module's constant-name array alone. For
example, the generated `BanditRLProof.Thompson.uniformActionMeasure.eq_1`
is owned by a CUCB module and is correctly included as a CUCB seed despite its
name. Its reference to the original uniform-measure definition remains a
generated reference, not an additional human-written theorem.

Of the direct references to other ABRL-owned modules, 38 occur in proof/value
terms and reach 15 distinct targets, including generated declarations. There
are 35 value-only pairs and three pairs whose canonical edge is a type edge
but also occurs in the value. Ignoring `also_in_value` would omit the latter.
Counts refer to distinct source-target pairs, not syntactic use frequency,
transitive closure, independent trials or work saved.

Compare each target's owning Git blob with the initial library
`eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`:

| Target owner under BanditRLProof | Initial-base status | Proof-reference pairs |
| --- | --- | ---: |
| Algorithms/ThompsonRecursiveSampler.lean | unchanged | 13 |
| ConcentrationFixedMGF.lean | unchanged | 10 |
| ConcentrationSubGaussian.lean | unchanged | 3 |
| ProbabilityUnionBound.lean | unchanged | 3 |
| ConcentrationConditionalMGF.lean | absent | 2 |
| FiniteGapCutoff.lean | absent | 1 |
| FiniteGapLayerCake.lean | absent | 1 |
| PowerCutoffNormalization.lean | absent | 2 |
| PowerTailIntegral.lean | absent | 3 |

Thus 29 pairs target four unchanged initial-library files, and nine target
five files added later. No target-owning file in this comparison is present
but modified. File-level provenance does not generally establish the original
availability of individual declarations in a modified file.

The addition history further separates those nine later pairs. The conditional
MGF interface was introduced during HOO development (`e4c3380`), providing two
actual references from CUCB. The other four files were introduced during CUCB
development (`1e6d970`, `a5f08d4`, `df44c5b`) and account for seven pairs. These
are shared mathematical components developed with this route; they must not
be described as seven uses of a pre-existing library. Full addition commits
and source-target pairs are retained in `cucb-case-summary.json`.

The Thompson owner contributes the finite uniform measure and probability
instance used by the concrete finite environments/oracle, including generated
proofs. These references do not transfer Thompson posterior or regret theory
to CUCB and are not evidence of a stronger bandit algorithm.

## Mathematical work beyond reference counts

The frozen target is Chen et al. (JMLR 2016), Algorithm 1 and the full refined
Theorem 1 plus both polynomial-smoothness branches of Theorem 2, with disclosed
model and proof deltas. The learner keeps the actual clipped indices and fresh
approximation oracle without forced initialization. Its signed alpha-beta
approximation regret is evaluated under one causal reward/feedback trajectory.

The accepted repair replaces an invalid mixed-trigger threshold rescaling in
the analysis with normalized charging. Charging remains an analysis device,
not an alteration of the learner. Conditional exponential bounds are derived
on the actual oracle/feedback mixture, followed by concentration, finite
layer-cake counting and a common cutoff. The oracle-failure credit and integer
initial charge are retained. Separately proved finite concavity is not claimed
as a dependency of the final common-cutoff endpoint.

The model explicitly requires compatible observed marginals, an inverse-range
condition for the smoothness function, a measurable fresh oracle and a finite
family of distinct selected subsets. These conditions rule out an unrestricted
claim about outcome-dependent censoring or every application in the source.
The reader and semantic receipt disclose the complete boundary.

The primary 64-atom canary has noisy arm values, overlapping two-arm actions,
probabilistic extra observations and nonlinear product rewards. Its actual
first-round regret is 1/4. Separate consumers cover both triggering branches,
a genuinely random beta=1/2 oracle, and the signed no-bad-action boundary.
The beta=1/2 oracle is input-independent; it is not a learning-efficiency test.

CMOSS v2 was read through both complete relevant proofs and received a
non-import disposition. Its explicit auxiliary-bound counterexample and
adaptive cascading-transfer gap are preserved as source-audit outcomes, not
as a refutation of every intended interior rate or an accepted repaired
comparison theorem.

## Reproduction

From the worktree, to rebuild the root and regenerate the graph:

```powershell
python runs/extended-topics-20260919/summarize_cucb_case.py --export --graph E:/ABRL/maintenance/extended-topics-20260919-claude/review-20260919/cucb-review/cucb-direct-graph.json --output runs/extended-topics-20260919/cucb-case-summary.json
```

To replay the summary without rebuilding:

```powershell
python runs/extended-topics-20260919/summarize_cucb_case.py --graph E:/ABRL/maintenance/extended-topics-20260919-claude/review-20260919/cucb-review/cucb-direct-graph.json --graph-sha256 5a9605a3c1870273df7b6d5ae6d7db0b52d219ca43c7620902e7a1927bc7d691 --output runs/extended-topics-20260919/cucb-case-summary.json
```

The graph, generated `.lean`, `.build.log` and `.provenance.json` can be
relocated together using `--graph`. Their hashes are checked. Both pinned
commits must exist in Git history; missing history is an error, not evidence
that a file was absent. Reviewed working-file hashes are raw-byte hashes;
comparison with committed contents explicitly normalizes CRLF to LF.
Export rejects changed tracked Lean/toolchain/manifest inputs and runs an
incremental root build. Replay checks recorded extraction evidence but does
not rerun the build, full gate or private semantic reviews. The local archive
is still required; this is not a portable anonymous release bundle.

## Publication boundary

Lean Graph: no production theorem or edge modification; this is a compiled
descriptive export. Overview: evidence extraction progress, topic incomplete.
Functor Hypergraph: no new transport theorem or stabilized bridge. The existing
reader, result registry, canonical manuscript and anonymous materials are
unchanged. Independent statistics review and the paper insertion remain
separate artifacts. Required controlled evaluations and the final all-topic
evidence join are still open; completed topics remain 0/10.
