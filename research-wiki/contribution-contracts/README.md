# ABRL contribution contracts

Every substantive contribution PR changes or adds at least one JSON file here.

The schema is `docs/contribution-contract.schema.json`. The diff-aware gate is:

```bash
python3 tools/check_contributor_contract.py --base BASE_COMMIT
```

A contract is not a theorem certificate. It is the integration ledger binding one bounded contribution to its source, route, affected files, reuse decision, reader contract, independent semantic review, Lean/Overview/Functor graph deltas, progress/site surfaces, remaining boundary, verification, and credit.

Do not reuse one old manifest for unrelated future changes. Update the manifest when any covered production file changes.
