# Proposed task packages

Every new task family must be proposed as `tasks/<task-id>/task.json` with the
instruction, environment, reference and verifier contract required by
[TASK_PROTOCOL.md](../TASK_PROTOCOL.md). CI runs `validate-all` on every package;
missing files, invalid seals and incomplete candidate evidence fail the build.
Do not add new families directly to the legacy four-core warmup registry.

Draft and candidate packages are proposals, not admitted evaluation data.
Maintain an independently reviewed, immutable suite release before exporting
them for scored evaluation. No proposed agentic tasks are admitted here yet.

The [first expansion](../expansion/README.md) proposes six public-dev drafts in
two families: importance-weighted variance (`BRB-IW-K/R/L`) and finite-horizon
Bellman evaluation (`BRB-BE-K/R/L`). Each family has knowledge/understanding,
reasoning and Lean views. The evidence ledger distinguishes local kernel and
rubric controls from isolated agent execution and release admission.
