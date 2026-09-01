# Harness Self-Comparison

ABRL can now compare two internal execution patterns without equating activity
with mathematics:

1. **Hierarchical:** upper freezes the target, middle decomposes the route,
   lower attempts a leaf, and reviewer gates the result.
2. **Master–worker:** a light master freezes independent deliverables, ordinary
   workers explore disjoint routes concurrently, the master synthesizes, and an
   independent reviewer runs the same gate.

The second arm addresses context duplication and slow sequential exploration.
It also creates a possible master bottleneck, merge conflicts, and duplicated
routes. Therefore ABRL measures it instead of adopting it by intuition.

## Evidence Contract

Only experiments with both arms, the same explicit `experiment_id`, the same
explicit `target_fingerprint`, and reviewer-classified attempts are matched.
Historical rows that lack these fields remain useful debugging history but do
not select a winner.

Each attempt records:

- progress class and reviewer validation;
- obligations before and after;
- new and reused declarations;
- proof-DAG size and depth when available;
- wall time, Lean-check time, prompt characters, and token counts;
- exact error signature and verifier evidence.

Progress classes are `unreviewed`, `no-progress`, `diagnostic`,
`retrieval-reuse`, `statement-repair`, `compiled-leaf`, `closed-frontier`, and
`terminal`. A zero process exit is logged as `executed`, never `compiled`.

## Adaptive Decision

`harness-compare` first computes deterministic matched metrics, writes a
Markdown report, draws a Mermaid attempt graph, and emits a bounded GPT review
packet. GPT may explain duplication, context cost, critical path, and the
master bottleneck, then propose an internal harness diagram. It cannot promote
unreviewed work or change the target.

At least two matched experiments are required before the tool recommends a new
default. With less evidence, `adaptive` retains the hierarchical default and
selects the less-sampled arm for the next experiment.

```bash
python3 tools/bandit.py harness-compare --task TASK_ID

python3 tools/bandit.py harness-compare --task TASK_ID \
  --execute-review --agent-profile codex-parallel.example.json
```

Outputs are written to `runs/harness-comparison/latest.{json,md,mmd}` and
`runs/harness-comparison/latest.prompt.md` by default.

When the two arms run in isolated worktrees, pass both immutable exported logs
without merging or overwriting either source:

```bash
python3 tools/bandit.py harness-compare --task TASK_ID \
  --trials path/to/hierarchical-trials.jsonl \
  --trials path/to/master-worker-trials.jsonl
```

## Interpretation

Master–worker is most plausible when several mathematically distinct routes
can be frozen with disjoint ownership. Hierarchical control is more plausible
when the theorem statement, source assumptions, or local API are still unclear.
The likely long-run design is hybrid: hierarchy for target fidelity and route
selection, bounded parallel workers for independent proof leaves, and one
reviewer-owned acceptance gate. The evidence—not the diagram—must decide.
