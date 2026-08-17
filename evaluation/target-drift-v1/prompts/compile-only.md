# ABRL target-drift evaluation: compile-only condition

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

Use the Lean source tree, pinned toolchain, compiler, and ordinary shell tools.
Do not use ABRL target-contract records, evidence-typed memory, proof-blueprint
records, or promotion-gate artifacts. Compilation is the only mechanized gate
available in this condition.

Produce exactly the common deliverables specified by the sealed result
contract: the Lean diff, build log, machine-readable final status,
`workflow-compliance.json`, source amendment (if any), and a concise
explanation. The compile-only compliance record has no condition-specific
evidence files. Never claim a theorem compiled unless the recorded build
succeeded.
