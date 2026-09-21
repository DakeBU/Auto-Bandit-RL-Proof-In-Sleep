# Causal descriptive evidence, 2026-09-20

This packet measures compiled structure at an explicit code snapshot. It does
not run a controlled comparison or estimate time/token savings.

## Frozen inputs and observed results

- Initial library: `eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`.
- Compiled snapshot: `296b09127c041670fe552df18d7d6846e8560ae5`.
- Scope: all twenty `BanditRLProof/Algorithms/Causal*.lean` modules at that
  snapshot; Tests are excluded as graph seeds.
- Direct graph: 464 owned nodes, 1,079 boundary nodes, 18,024 source-target
  edges, 59 module imports. Generated and private declarations are included.
- External project value/proof references: 20 unique pairs, 8 distinct targets.
  Eighteen pairs target unchanged initial-library files; two target
  `HeavyTailFixedTilt.lean`, absent at the initial baseline.
- These counts are not twenty reused mathematical theorems. Targets include
  a class and generated declarations. A generated `choose.congr_simp` target
  has an RL owner file; this does not establish transfer of RL regret theory.

The two heavy-tail calls are `bounded_centering_mgf` and
`independent_sum_mgf` in `CausalSampleMGF.lean`. The actual causal product
sample law supplies boundedness, second moment and independence. The older
fixed-MGF interface supplies the tail conversion, and finite argmax interfaces
support actual recommendations. Internal causal-law, allocation and encoding
dependencies remain inside the twenty-module scope and are not counted as
external reuse.

## Reproduction

Run from a checkout of the compiled snapshot or one with byte-equivalent
tracked Lean, toolchain and dependency inputs. Preserve the Git history for
both snapshots. Use an output directory for the extraction artifacts:

```powershell
python runs/extended-topics-20260919/summarize_causal_case.py --export --graph <OUTPUT>/causal-direct-graph.json --output <OUTPUT>/causal-case-summary.json
```

The script checks source/receipt fingerprints, builds the public root, derives
a focused exporter from `tools/ProofGraphExport.lean`, and runs it against the
compiled Lean environment. Its graph, generated `.lean` exporter,
`.provenance.json` and `.build.log` form one extraction bundle. To replay,
keep those files together and supply the graph SHA256 from the checked-in
`runs/extended-topics-20260919/causal-case-summary.json`:

```powershell
python runs/extended-topics-20260919/summarize_causal_case.py --graph <OUTPUT>/causal-direct-graph.json --graph-sha256 <SHA256> --output <OUTPUT>/replayed-summary.json
```

Replay rechecks the graph and companion fingerprints, ownership, pair
uniqueness, recorded extraction provenance, source snapshot and Git file
provenance. It recomputes the descriptive counts. It does not execute a fresh
Lean build; `--export` does. These are incremental builds, not clean-room
toolchain rebuilds. The separate production receipt binds the previously
completed root, Tests, full harness and site checks. Independent extraction
and prose reviews are bound by `causal-case-validation.json`.

## Meaning and limitations

An edge is retained if the constant occurs in the declaration value/proof,
including a type edge marked `also_in_value`; multiple occurrences of the
same pair count once. Type-only references and imports do not qualify as
proof/value reuse. The graph retains the direct external boundary and does
not recursively expand Mathlib. File provenance proves byte identity or
absence at the selected commits, not the marginal effort attributable to a
declaration. No baseline formalizer run, intervention on library access,
runtime comparison, confidence interval or efficiency effect is present.

The Evaluation/appendix draft is `ICLR-CAUSAL-CASE.md`. Its scientific claims
are tied to the actual source-facing endpoints and local canaries, including
disclosed proof repairs. It remains outside the canonical and anonymous
manuscripts. This descriptive case does not complete causal's remaining source
selection or all-topic controlled evaluation obligations.
