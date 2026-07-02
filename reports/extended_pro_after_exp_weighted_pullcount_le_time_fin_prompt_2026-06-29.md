# Extended Pro Review Prompt: After EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN
```

New compiled file:

```text
BanditRLProof/ExpectationFiniteBanditBounds.lean
```

New theorem:

```lean
theorem lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Fin K -> ENNReal) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        gap a * (n : ENNReal))
```

The proof is a thin specialization of
`lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time` with
`arms := (Finset.univ : Finset (Fin K))`.

Verification passed:

```text
python3 tools/bandit.py check
Build completed successfully.
Build completed successfully.
check passed
```

I also updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf cards and recommendation output;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `README.md`;
- `docs/project_overview_next_plan.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- UCB/ETC proof-obligation ledgers and retrieval indexes.

Current compiled expectation/probability bridge layer now includes:

- `lintegral_actionTrace_eval_eq_indicator_one`;
- `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`;
- `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`;
- `lintegral_finset_sum_gap_mul_natCast_pullCount_eq`;
- `lintegral_natCast_pullCount_le_time`;
- `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`;
- `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.

Please review whether this is now the right stopping point before scalar
conversion.

Questions:

1. Is `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` reasonable as implemented?
2. What is the single best next executable leaf now?
3. If the next step is scalar conversion for `FiniteBanditModel.gap : Fin K ->
   Rat`, should the project first build a nonnegativity lemma, a `Rat ->
   ENNReal` conversion wrapper, a `Rat -> Real` Bochner expectation route, or
   something else?
4. What exact Lean-facing statement/imports/regularity contracts/failure
   policy would you recommend?
5. How much work should be completed before asking you again?
