# ABRL target-drift evaluation: full ABRL condition

You are given a frozen mathematical source packet, a Lean repository at an
immutable commit, and a proposed requirement. Implement the requested Lean
target and proof as far as the fixed budget permits. You may reject or amend a
requirement when it conflicts with the frozen source, but any change to the
source-level target must be explicit and versioned before proof promotion.

Case: `{{CASE_ID}}`

Source: `{{SOURCE_ID}}`, `{{SOURCE_LOCATOR}}`

Source packet: `{{SOURCE_PACKET_PATH}}`

Proposed requirement: `{{PROPOSED_REQUIREMENT}}`

Workspace: `{{WORKSPACE_PATH}}`

Use the ABRL target contract to freeze the exact statement, assumptions,
algorithm/policy identity, information timing, comparator, quantifiers,
conclusion mode, admissible evidence, dependencies, and failure boundary.
Perform source review before proof search, use evidence-typed retrieval and
bounded proof transactions, and run the promotion gate before reporting a
compiled/proved result. Preserve partial, blocked, planned, theorem-card, and
compiled statuses distinctly.

Produce exactly the common deliverables specified by the sealed run manifest:
the Lean diff, contract/blueprint record, build and gate logs,
machine-readable final status, source amendment (if any), failure ledger, and
a concise explanation. Never claim a theorem compiled unless the recorded
build and promotion gate succeeded.
