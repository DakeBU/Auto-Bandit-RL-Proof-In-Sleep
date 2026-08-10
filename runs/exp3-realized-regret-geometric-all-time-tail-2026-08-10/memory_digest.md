# Lifecycle Memory Digest

Task: `EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL`
Role: `lower`
Selected records: `mem-2a0ffec376992850`
Policy: last `5` task/role-relevant active records plus explicit verified lemmas.

```json
{
  "policy": "explicit verified lemmas plus bounded role-relevant recent records",
  "record_count": 1,
  "records": [
    {
      "assumptions": [
        "one fixed generated process and supported comparator; eta>0; 0<gamma<1; positive total delta; exact delta/2 split between predictable-regret and realized-deviation event families"
      ],
      "created_at": "2026-08-10T06:46:08+00:00",
      "declaration": "BanditRLProof.Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le",
      "details": {},
      "file": "BanditRLProof/Exp3RealizedRegretAllTime.lean",
      "id": "mem-2a0ffec376992850",
      "provenance": {
        "kind": "local_lean",
        "reference": "BanditRLProof.Exp3RealizedRegretAllTime"
      },
      "roles": [
        "lower"
      ],
      "status": "accepted",
      "supersession": {
        "reason": "",
        "supersedes": []
      },
      "task": "EXP3-REALIZED-REGRET-GEOMETRIC-ALL-TIME-TAIL",
      "type": "verified_lemma",
      "verifier_evidence": [
        "SafeVerify 34d6b6dd; six baseline axiom reports; five Tests.Basic canaries; independent review; full bandit check"
      ]
    }
  ]
}
```
