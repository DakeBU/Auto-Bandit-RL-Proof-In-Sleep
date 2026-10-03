# HOO descriptive evidence: extraction and provenance

This is a reproducibility note for the forthcoming Lipschitz Evaluation case,
not an efficiency experiment or acceptance of the complete topic. It adds no
Lean declarations and changes no theorem, source contract or published graph.

## Two different snapshots

The compiled dependency graph is pinned to `0378d467c709220c38ef0cc8e6db2215a349571b`.
It was exported from 28 HOO modules before the reward-family adapter was added.
Production validation instead refers to `785af09b2c0fe9b095bfc521a14ce27b62e3a946`.
The latter includes the public reward-family interface, its canary and nine
shared reading references. These snapshots must not be combined into a claim
that the dependency export covers the new adapter.

## Corrected attribution of compiled references

The immutable historical export records 506 seeds, 1,576 boundary nodes,
25,765 edges and 84 module-import relations. The seeds come from module
constant-name arrays. Those arrays can contain duplicate generated declarations;
the exporter deduplicates names but does not filter their resolved environment
owner after collecting them.

In this graph, `BanditRLProof.Concentration.HasCondMGFUpperBoundAt.congr_simp`
is one such seed. Its recorded owner is `BanditRLProof.ConcentrationSubGaussian`,
outside the 28 HOO modules. Its proof reference to
`BanditRLProof.Concentration.HasCondMGFUpperBoundAt` contributes one of the
historically reported 37 external-to-HOO project proof-reference pairs.

Filtering both source and target by their resolved owning module gives **36
HOO-to-other-project proof-reference pairs**, still involving **21 distinct
target declarations**. There are **505 HOO-owned nodes**. The new summary retains
both the historical counts and the excluded pair; it does not rewrite the
original export or acceptance receipt. Generated targets remain included, so
21 targets must not be described as 21 independent human-written lemmas.

Proof references use `kind=value OR also_in_value=true`; references appearing
in both type and proof must not be lost because their canonical edge is typed.
Pairs count direct source-target relations, not syntactic use frequency,
transitive dependency closure, independent trials or effort saved.

## Initial-library versus later development

Compare target-owning file Git blobs at the graph snapshot with the initial
frozen library `eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`:

| Owning file under BanditRLProof | Initial-base status | Filtered pairs |
| --- | --- | ---: |
| ConcentrationFixedMGF.lean | unchanged | 19 |
| ConcentrationSubGaussian.lean | unchanged | 2 |
| Core.lean | unchanged | 4 |
| MeasurablePullCountCast.lean | unchanged | 1 |
| ProbabilityUnionBound.lean | unchanged | 2 |
| Algorithms/HeavyTailExpectedCount.lean | absent | 1 |
| Algorithms/HeavyTailUCB.lean | absent | 4 |
| ConcentrationConditionalMGF.lean | absent | 1 |
| HeavyTailTailSum.lean | absent | 2 |

Thus 28 pairs point into five unchanged initial-library files and eight into
four files introduced later in the program. This demonstrates concrete use of
both initial and subsequently developed interfaces. It does not measure how
much work their availability saved. File provenance is deliberately distinct
from declaration-level provenance; no modified-at-base file occurs here.

## Reproduction and validation boundary

From the research worktree run:

```powershell
python runs/extended-topics-20260919/summarize_lipschitz_case.py --output runs/extended-topics-20260919/lipschitz-case-summary.json
```

The default graph path is read from `hoo-compiled-references.json`. Use
`--graph PATH` to relocate the same graph; its SHA-256 must match. The graph can
be regenerated with `export_hoo_dependencies.py` against the pinned historical
snapshot and compiled environment. The local evidence archive, Git history and
recorded production working files are required for this replay; this is not yet
a self-contained anonymous release bundle.

The script recomputes node/edge counts, checks complete edge endpoints, selects
proof pairs, compares initial Git blobs and validates production evidence
bindings. Production receipt hashes refer to raw Windows working-file bytes,
including mixed line endings. The script verifies those raw hashes and compares
their contents with the production commit after explicit CRLF-to-LF
normalization. Both raw-file and Git-blob SHA-256 values are reported; they must
not be presented as identical byte hashes when line endings differ.

The recorded production gate passed the shared root, Tests, full harness and
site checks: 9,017 root build jobs, 9,116 Tests jobs, 437 Python tests with seven
skips. This script does not rerun those gates or revalidate the private review
and log archives. Build jobs are not new-theorem counts. Controlled runs remain
empty and no efficiency effect is estimated.

## Publication and remaining work

Lean Graph: no formal edge change; this note corrects attribution in descriptive
statistics. Overview: evidence-method progress only, with topic completion still
false. Functor Hypergraph: no new mechanism or transport claim. Teaching pages,
results, registry, canonical manuscript and anonymous materials are unchanged
because no theorem or publication mapping changes here.

The independent statistics review, prose Evaluation/appendix case, all-topic
protocol, actual required evaluations and final evidence join remain separate
obligations. Complete topics remain 0/10.
