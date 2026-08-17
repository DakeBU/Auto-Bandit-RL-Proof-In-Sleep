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

The execution layer is now explicit but intentionally unfrozen:

- `execution-template.json` lists every model, budget, retry, randomization,
  sealed-view, and grader choice that must be fixed before the first run;
- `source-files.template.json` requires a local hash-verified copy of all four
  sources, including an exact revision/hash for the online textbook;
- `prompts/` contains matched condition templates whose source/task fields are
  identical and whose workflow resources differ by condition;
- `grading-rubric.json` freezes the binary primary endpoint and independent
  adjudication rule without containing outcomes;
- `tools/prepare_target_drift_execution.py` validates this template and uses a
  two-step seal: a hash-complete `preseal_ready` configuration may leave only
  the aggregate digest unset; after materialization records the digest over
  `agent_cases.json` and `run_manifest.json`, a `frozen_ready` rerun must
  reproduce it exactly at the recorded repository commit.

Validate the still-unrun execution template with:

```text
python tools/prepare_target_drift_execution.py --check-template
```

Do not set `execution_status` to `preseal_ready` until provider/model version,
budgets, prompts and hashes, five seeds, failure policy, exact source files,
and independent grader identities/policy are fixed.  Record the preseal digest,
then set `execution_status` to `frozen_ready` and reproduce the pack before the
first run.  The
materializer strips `faithful_contract`, `expected_affected_fields`,
`drift_class`, and `stratum` from the evaluated agent view.
