# Lifecycle Memory Digest

Task: `EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`
Role: `lower`
Selected records: `mem-7ceab55257453017`
Policy: last `5` task/role-relevant active records plus explicit verified lemmas.

```json
{
  "policy": "explicit verified lemmas plus bounded role-relevant recent records",
  "record_count": 1,
  "records": [
    {
      "assumptions": [
        "one fixed generated process; deterministic variance budget n+1; positive outer delta; inherited Standard Borel probability and 0<gamma<=1 contracts"
      ],
      "created_at": "2026-08-10T05:54:05+00:00",
      "declaration": "BanditRLProof.Exp3.measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le",
      "details": {},
      "file": "BanditRLProof/Exp3RealizedDeviationAllTime.lean",
      "id": "mem-7ceab55257453017",
      "provenance": {
        "kind": "local_lean",
        "reference": "BanditRLProof.Exp3RealizedDeviationAllTime"
      },
      "roles": [
        "lower"
      ],
      "status": "accepted",
      "supersession": {
        "reason": "",
        "supersedes": []
      },
      "task": "EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL",
      "type": "verified_lemma",
      "verifier_evidence": [
        "SafeVerify 5479f334; ten baseline axiom reports; six Tests.Basic canaries; independent review; full bandit check"
      ]
    }
  ]
}
```
