# Paper-source contract pre-audit v1

Status: `ai_assisted_pre_audit_complete_human_expert_validation_pending`

This evidence package records a source-level review of the 18 paper-derived
contracts in the target-drift challenge bank.  Two isolated AI reviewer
instances read the same three hash-frozen PDFs and returned their judgments
without seeing each other's output.  A third AI-assisted adjudication pass
re-read the disputed source locations.  This is useful rubric calibration and
pre-execution quality control; it is **not** independent human expert
validation and it is **not** a target-drift experiment result.

The review found agreement that all 18 injected drifts change a
source-critical field.  On the original faithful contracts, the adjudicated
result is 15 `match`, one `mismatch`, and two `unclear`.  Five original source
locators were adjudicated `imprecise`.  Seven cases consequently received a
versioned pre-execution wording or locator correction.  No evaluated-agent,
checker, or comparator outcome had been observed before the amendment.

Files:

- `protocol.json`: scope, blinding boundary, source hashes, and claim limits;
- `reviewer-a.json`, `reviewer-b.json`: the two isolated AI judgments;
- `adjudication.json`: source-anchored resolution of every case;
- `summary.json`: agreement and adjudicated counts;
- `amendment.json`: before/after hashes and exact pre-execution changes;
- `pre-amendment/`: byte-for-byte snapshots and a Git-object manifest binding
  each `before_sha256` to the versioned base state.

The package does not report a post-amendment `18/18` self-check: no
independent per-case post-amendment review record was retained.  Current input
hashes prove which files changed, but they are not a substitute for that
case-level semantic evidence.

Validate the package with:

```text
python tools/validate_source_contract_audit.py
python -m unittest tools.test_source_contract_audit
```

Publication wording must retain all three boundaries: the review was
AI-assisted, it covered only the 18 paper-derived cases, and human expert
dual review plus independent adjudication remains pending.
