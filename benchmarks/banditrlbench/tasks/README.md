# Proposed task packages

Every new task family must be proposed as `tasks/<task-id>/task.json` with the
instruction, environment, reference and verifier contract required by
[TASK_PROTOCOL.md](../TASK_PROTOCOL.md). CI runs `validate-all` on every package;
missing files, invalid seals and incomplete candidate evidence fail the build.
Do not add new families directly to the legacy four-core warmup registry.

Draft and candidate packages are proposals, not admitted evaluation data.
Maintain an independently reviewed, immutable suite release before exporting
them for scored evaluation. No proposed agentic tasks are admitted here yet.
