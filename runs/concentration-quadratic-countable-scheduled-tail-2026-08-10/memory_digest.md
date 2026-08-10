# Lifecycle Memory Digest

Task: `CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL`
Role: `reviewer`
Selected records: `mem-26c1f8ea632bb05f`
Policy: last `5` task/role-relevant active records plus explicit verified lemmas.

```json
{
  "policy": "explicit verified lemmas plus bounded role-relevant recent records",
  "record_count": 1,
  "records": [
    {
      "assumptions": [
        "pointwise positive schedules and per-index fixed-tilt quadratic tail family"
      ],
      "created_at": "2026-08-10T04:42:02+00:00",
      "declaration": "BanditRLProof.Concentration.measure_iUnion_scheduled_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail",
      "details": {},
      "file": "BanditRLProof/ConcentrationQuadraticScheduled.lean",
      "id": "mem-26c1f8ea632bb05f",
      "provenance": {
        "kind": "local_lean",
        "reference": "BanditRLProof.ConcentrationQuadraticScheduled"
      },
      "roles": [
        "lower"
      ],
      "status": "accepted",
      "supersession": {
        "reason": "",
        "supersedes": []
      },
      "task": "CONCENTRATION-QUADRATIC-COUNTABLE-SCHEDULED-TAIL",
      "type": "verified_lemma",
      "verifier_evidence": [
        "SafeVerify 0e782bcd, baseline axioms, independent review, full bandit check"
      ]
    }
  ]
}
```
