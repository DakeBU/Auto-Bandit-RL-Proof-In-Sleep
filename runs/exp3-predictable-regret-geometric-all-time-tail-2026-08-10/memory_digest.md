# Lifecycle Memory Digest

Task: `EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL`
Role: `lower`
Selected records: `mem-b8cfa9865d91f12a`
Policy: last `5` task/role-relevant active records plus explicit verified lemmas.

```json
{
  "policy": "explicit verified lemmas plus bounded role-relevant recent records",
  "record_count": 1,
  "records": [
    {
      "assumptions": [
        "one fixed generated process and supported comparator; eta>0; 0<gamma<1; positive outer delta; geometric outer share and parent internal half split"
      ],
      "created_at": "2026-08-10T06:19:22+00:00",
      "declaration": "BanditRLProof.Exp3.measure_sampledPredictableRegretGeometricAllTimeFailureSet_le",
      "details": {},
      "file": "BanditRLProof/Exp3PredictableRegretAllTime.lean",
      "id": "mem-b8cfa9865d91f12a",
      "provenance": {
        "kind": "local_lean",
        "reference": "BanditRLProof.Exp3PredictableRegretAllTime"
      },
      "roles": [
        "lower"
      ],
      "status": "accepted",
      "supersession": {
        "reason": "",
        "supersedes": []
      },
      "task": "EXP3-PREDICTABLE-REGRET-GEOMETRIC-ALL-TIME-TAIL",
      "type": "verified_lemma",
      "verifier_evidence": [
        "SafeVerify dc280a8f; four baseline axiom reports; three Tests.Basic canaries; independent review; full bandit check"
      ]
    }
  ]
}
```
