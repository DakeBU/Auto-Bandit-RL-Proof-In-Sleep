# Target-drift suite v1

Status: `challenge_bank_frozen_execution_not_started`

This directory freezes the first controlled target-drift suite for the ABRL
evaluation.  It contains 30 authored cases:

- 18 recent-paper-derived probes, six for each source-frozen NeurIPS 2025
  paper;
- 12 textbook controls, two for each of six drift classes;
- three matched workflow conditions and five paired seeds, yielding 450
  planned runs.

The suite is a preregistration artifact, not a result.  Every case is marked
`authored_unrun`; there are no outcome, score, or effect-size fields.  Model
version, prompts, budgets, retry policy, randomized presentation order, and
expert-grading identities must be appended and frozen before execution.

`challenges.json` is an authoring/adjudication manifest.  An evaluated agent
must receive only the challenge-specific source packet and task prompt, never
the `expected_affected_fields` key.  A future runner must materialize a sealed
agent view and record its digest before the first run.  Publication of this
manifest does not itself establish blinding.

Validate the freeze with:

```text
python tools/validate_target_drift_suite.py
```

The validator checks allocation, unique identifiers, source hashes, planned
run arithmetic, and the absence of result-shaped fields.
