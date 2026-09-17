# Extended topics development packet

This branch contains actual new mathematics and a partial formalization, not a
completed heavy-tailed bandit algorithm theorem. Start with [the frozen
protocol](PROTOCOL.md), [source audit](SOURCE-AUDIT.md), [derivation](DERIVATION.md),
and [obligations](OBLIGATIONS.md).

## What is proved

For raw absolute (1+epsilon)-moments, the Lean modules supply truncation bias,
the truncated second moment, a centered fixed-tilt MGF, and independent-prefix
one-sided concentration. Existing stream-consumption algebra identifies actual
transformed observations with their latent prefix. The reserved transfer proves
clipped-estimator corruption stability on the actual same action trace, and
diagnoses why hard truncation cannot use the same stability argument.

## What is not proved

The complete original or repaired robust-UCB expected-regret theorem remains
open. A source-fixed confidence schedule needs two-sided tuning, a measurable
causal algorithm, adaptive-count peeling, count/regret assembly, and independent
semantic review. The clipped clean estimator's moment-based confidence theorem
also remains open. There are no controlled productivity results and no new
algorithmic rate claim.

## Reproduce

Use the pinned Lean/Lake project. The build must have sufficient memory for the
combined public root. Run from this worktree:

```powershell
lake build BanditRLProof Tests
python tools/bandit.py check
python website/scripts/build_site.py --lean-verified
python website/scripts/check_site.py
# After committing tracked sources, regenerate exact compiled dependencies:
python tools/extended_topics_evidence.py --graph <private-output>/full-graph.json --output <output>/evidence.json
```

Use `--lean-verified` only after the gate passes for the current Lean sources.
The evidence script rebuilds/imports the public root, checks unchanged frozen
base modules, and captures fresh type/value edges. It produces a descriptive
report with explicit open obligations and an empty controlled-run list. It does
not run models or infer unavailable token usage. Keep its outputs outside the
tracked files during extraction, then commit the small report separately so
the report's source commit remains unambiguous.

Private PDF sources, paper insertion draft and local ownership receipt are under
the ABRL maintenance directory. The canonical long manuscript and frozen
anonymous snapshot are unchanged. Retain this worktree for the open producer
and algorithm work; its dependency junction must not be deleted through.
