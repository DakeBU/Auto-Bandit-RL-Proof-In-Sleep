# Agent Profiles

Agent profiles are optional command-template maps for executing prompt decks.
`tools/bandit.py` can also take a single `--agent-cmd` template directly.

Hierarchical decks use `upper`, `middle`, `lower`, and `reviewer` keys.
Master–worker decks use `master`, `worker`, and `reviewer`; worker commands are
launched concurrently only after the master plan completes. A `default` key can
serve either mode. See `docs/harness_self_comparison.md` before treating a
larger worker count as useful progress.
