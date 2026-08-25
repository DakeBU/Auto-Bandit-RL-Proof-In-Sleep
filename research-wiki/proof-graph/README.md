# Proof Graph Laboratory artifacts

These files are versioned audit summaries.  The full 155 MB environment graphs
are local artifacts and are identified here by SHA-256 rather than committed.

| File | Role | Evidence status |
| --- | --- | --- |
| `benchmark_roots.json` | frozen unchanged EXP3, half-Tsallis, and OFUL terminals | compiled roots |
| `benchmark_measurements.json` | one-run local Lean module check times and environment | local observation |
| `benchmark_report.json` | proof-cost, shared support, ZDD ordering, hypergraph LB, MIP planning summary | prototype over compiled roots |
| `benchmark_replication.json` | exact frozen-versus-current fixed-root support/depth/proxy and ZDD structure comparison | deterministic fixed-support replication |
| `proof_cost.schema.json` | nonnegative vector/Pareto cost contract | schema/prototype |
| `novelty_audit.json` | five-part proof-structural novelty protocol and falsification rules | prototype protocol |
| `cng_candidate_roots.json` | exact compiled finite CNG leaves and held-out split | partial compiled algebra |
| `cng_candidate_evaluation.json` | frozen-versus-candidate structural proxy and current negative transfer/compression result | prototype observation |

The exporter reads compiled Lean declaration types and values.  It is not a
kernel trace, tactic trace, or proof-state capture.  The ZDD holds only fixed
universe support families; the MIP is only a library planner.  Raw new-node
count is explicitly not a novelty metric.

`benchmark_replication.json` binds the frozen graph SHA-256
`177233bc84b7f18928f66b1bf95545095d7dd1373f32d7dd2ed286c46bc520c9` to the
current graph SHA-256
`126e92a6006f55c5da42cd40cc84aef176d23ade6d796591b78d3e27b116ec56`.
The graph grew, but the three frozen project-support digests and selected cost
metrics, plus the deterministic ZDD node/serialized-size metrics for all four
orders, remained exact.  This is a **deterministic fixed-support replication**.
It is not evidence of search acceleration, semantic novelty, or
irreducibility.

The current CNG evaluation is deliberately negative: structural proxy
signatures appear, but irreducibility is not established; the frozen benchmark
closures are unchanged and held-out OFUL has no CNG dependency.  Therefore no
backward compression or held-out transfer is demonstrated, the full Pareto
relation is not assessed, and no proof-structural discovery is claimed.

All artifacts exclude Chapter 13--17 and the concurrent lower-bound spine's
declarations, cards, pages, and active frontier.
