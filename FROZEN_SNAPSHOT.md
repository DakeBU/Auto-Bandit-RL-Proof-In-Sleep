# Frozen anonymous review snapshot

This branch freezes the complete project state based on development revision

```text
c16ea983e73054585e76465baa9e27a75c768622
```

for double-blind review.

The snapshot keeps the full Lean library, textbook and BanditRLwiki sources, paper audits, proof-graph memory, harness and evaluation protocols, website generator, tests, and documentation. Reviewer-facing entry points replace project authorship and author-controlled URLs with anonymous equivalents; mathematical source attribution is retained.

## Evidence policy

The review workflow must pass before a deployable website archive is distributed. It runs the main Lean/repository gate, validates the target-drift evaluation protocols, builds and checks the full BanditRLlib site, applies reviewer-facing anonymization, scans the final static site for identity leaks, and verifies key reader surfaces before producing the ZIP.

A website label or source-audit record does not create proof status. Compiled declarations, source-fidelity judgments, literature claims, and open frontier leaves remain separate evidence types.

The branch does not auto-sync with development. A new submission snapshot requires an explicit refreeze and a fresh verification run.
