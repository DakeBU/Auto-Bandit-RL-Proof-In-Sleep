# Extended topics development packet

This branch contains the corrected unchanged-source-policy robust-UCB expected-regret
chain, its finite printed-coefficient counterexample, a separate conservative
adaptation, and an ongoing all-ten-topic program; zero topics have been accepted. Start with [the frozen
protocol](PROTOCOL.md), [source audit](SOURCE-AUDIT.md), [derivation](DERIVATION.md),
and [obligations](OBLIGATIONS.md).

The next mandatory line is [HOO for Lipschitz bandits](LIPSCHITZ-HOO-CONTRACT.md).
Its source contract was committed before implementation. Its actual causal tree
algorithm, concentration, dimension producers, all-horizon regret and noisy model
witness have compiled milestones. Independent semantic acceptance remains open.
Execution stays on heavy-tailed until its acceptance obligations are closed;
these later-topic milestones do not authorize skipping the strict order.

## What is proved

For raw absolute (1+epsilon)-moments, the Lean modules supply moment-derived
two-sided confidence, radius tuning, a causal measurable robust-UCB policy,
adaptive-count bounds and its expected pseudo-regret theorem. This is the
documented conservative adaptation, not the unchanged printed constant theorem.

The reserved clipping transfer now supplies its own moment bias and second
moment, consumes the shared centered-MGF and mean-error assembly, and derives
scheduled confidence under arbitrary adaptive prefix selection and an L1
corruption budget on the consumed prefix. Existing stream-consumption algebra
identifies the estimator with actual observed rewards along the same action
trace. See [the transfer derivation](CLIPPING-TRANSFER.md) for scope and gates.

## What is not proved

The literal printed robust-UCB coefficient has an accepted finite Lean
counterexample; the unchanged policy has a separately accepted corrected regret
bound. Full recent-source adjudication and whole-topic acceptance remain open.
See [the authoritative ledger](ALL-TOPICS-LEDGER.json) for packet-specific
semantic review and joint-validation receipts. Clipping stability does not
establish corruption-robust regret or compare two policies reacting differently
to corruption. The other nine topics remain unaccepted even where endpoints
have compiled milestones. The all-topic evaluation remains open. There are no controlled
productivity results and no new algorithmic rate claim.

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
