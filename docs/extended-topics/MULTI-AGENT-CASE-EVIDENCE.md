# Multi-agent descriptive evidence, 2026-09-20

This packet reports compiled structure and accepted mathematical scope. It
contains no controlled formalizer runs or estimate of time/token savings.
Independent statistics and prose review bindings are recorded separately in
`runs/extended-topics-20260920/multi-agent-case-validation.json`.

## Inputs and observations

- Initial library: `eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`.
- Compiled snapshot: `4a09e817cabd67f4ffc3b248ff1487ae55f6dea3`.
- Scope: all twelve `BanditRLProof/Algorithms/MusicalChairs*.lean` modules at
  that snapshot. Tests are not graph seeds. All twelve owner files were absent
  from the initial library.
- Direct graph: 660 owned nodes, 1,558 boundary nodes, 32,683 unique directed
  source-target pairs and 84 module-import edges. Owned nodes include generated
  and private declarations; they are not the 371 source-scanned public reading
  references or the 410 promoted production/test names in the axiom audit.
- Proof/value pairs: 1,227 within one owner module; 902 crossing between the
  twelve owner modules; 15,126 targeting Mathlib; and 14,288 targeting Lean
  core or other external owners. The internal cross-module pairs reach 145
  distinct targets, including generated declarations.
- **Project proof/value pairs outside the twelve-module case: zero.** There
  is no observed direct proof/value reference from this case to a pre-existing
  ABRL project declaration outside the selected modules. None of the twelve
  modules existed at the initial baseline. This case therefore provides no
  positive direct-reference evidence of initial-library theorem reuse.

These are unique constant-reference pairs, not occurrence counts, mathematical
lemma counts, number of independent results, or effort saved. Mathlib/core
targets include types, constructors, instances and tactic-generated proof
machinery. Their much larger counts must not be relabeled as thousands of
reused mathematical lemmas. Shared root membership and module imports also do
not establish actual proof-term reuse of an existing project theorem.

## New interfaces and real consumers

The within-case graph connects genuine producer/consumer stages. The actual
finite coordination law supports a uniform fixation hazard, a survival sum and
an occupation bound. Charging lost reward to unfixed players yields the
common-set coordination mean deficit. Independent exploration and bounded
reward concentration then produce an event on which local population estimates
and ranked candidates identify the true top set. The constructed learned
continuation kernel transports the coordination guarantee onto that event.
The complete reward process supplies the unconditional visible-regret bound.

For example, `expectedCoordinationRegret_real_le` is consumed by the learned
continuation analysis, and `source_conditional_coordination_regret` enters the
full learner's phase split. These are interfaces developed inside this case,
not evidence that the initial library already contained the complete route.
Their mathematical acceptance rests on the source/promotion receipts; a graph
edge alone does not prove fidelity or a cross-setting transport theorem.

## Reproduction

Run at the compiled snapshot, or a checkout with identical tracked Lean,
toolchain and dependency-manifest inputs and the required receipt files.
Retain Git history for both commits. The script is an adaptation of the
earlier causal evidence extractor; it verifies each expected replacement in
the shared compiled-environment exporter rather than parsing textual imports
as proof edges.

```powershell
python runs/extended-topics-20260920/summarize_multi_agent_case.py --export --graph <OUTPUT>/multi-agent-direct-graph.json --output <OUTPUT>/multi-agent-case-summary.json
```

The extraction bundle contains the graph, generated `.lean` exporter,
`.provenance.json` and public-root `.build.log`. The exporter starts from
`tools/ProofGraphExport.lean` and retains every direct target of a selected
owner declaration, including project targets outside the scope and Mathlib/core
targets. It does not recursively expand the boundary. It builds the public root
incrementally; it does not rerun Tests/full harness or perform a clean-room
toolchain rebuild.

To replay the summary, preserve that bundle and use the graph hash in the
checked-in `runs/extended-topics-20260920/multi-agent-case-summary.json`:

```powershell
python runs/extended-topics-20260920/summarize_multi_agent_case.py --graph <OUTPUT>/multi-agent-direct-graph.json --graph-sha256 <SHA256> --output <OUTPUT>/replayed-summary.json
```

Replay validates source/receipt and bundle fingerprints, exact owner scope,
unique pairs, target closure and Git provenance. A pair qualifies as proof/value
reuse when its edge kind is `value`, or a type edge has `also_in_value=true`.
An occurrence in both fields still counts once. The separate production
validation receipt supplies the previously passed combined root/Tests, full
harness, axiom and site gates. The source-selection receipt was added after
the compiled snapshot; it does not change any Lean input or graph count.

## Evaluation boundary

The case demonstrates a complete selected static learner extension and reusable
interfaces developed during that extension. It is also a negative case for
direct reuse of the initial ABRL theorem library. No Mathlib-only baseline,
randomized access intervention, controlled repeated runs, confidence interval,
runtime comparison or efficiency effect is present. The all-topic controlled
protocol remains a separate obligation; development work cannot be relabeled
as independent benchmark repeats. The Evaluation/appendix draft remains outside
the canonical manuscript and anonymous submission in `ICLR-MULTI-AGENT-CASE.md`.
