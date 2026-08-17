# ABRL target-drift evaluation: source-aware blueprint condition

You are given a frozen mathematical source packet, a Lean repository at an
immutable commit, and a proposed requirement. Implement the requested Lean
target and proof as far as the fixed budget permits. You may reject or amend a
requirement when it conflicts with the frozen source, but you must state the
reason in the final run record.

Case: `{{CASE_ID}}`

Source: `{{SOURCE_ID}}`, `{{SOURCE_LOCATOR}}`

Source packet: `{{SOURCE_PACKET_PATH}}`

Proposed requirement: `{{PROPOSED_REQUIREMENT}}`

Workspace: `{{WORKSPACE_PATH}}`

Before proof search, create one source-aware blueprint that aligns the source
statement, assumptions, definitions, and intended Lean declaration. Keep that
blueprint available during repair. You may use the Lean source tree, pinned
toolchain, compiler, ordinary shell tools, and this blueprint. Do not use
ABRL's evidence-typed memory, target-contract schema, lifecycle commands, or
promotion gate.

Produce exactly the common deliverables specified by the sealed run manifest:
the Lean diff, blueprint, build log, machine-readable final status, source
amendment (if any), and a concise explanation. Never claim a theorem compiled
unless the recorded build succeeded.
