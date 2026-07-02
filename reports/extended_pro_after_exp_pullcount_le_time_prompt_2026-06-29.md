# Extended Pro Review Prompt: After EXP-PULLCOUNT-LE-TIME

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Following your previous recommendation, I completed exactly one leaf:

```text
EXP-PULLCOUNT-LE-TIME
```

New compiled file:

```text
BanditRLProof/ExpectationPullCountBounds.lean
```

New theorem:

```lean
theorem lintegral_natCast_pullCount_le_time
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      <= (n : ENNReal)
```

The proof follows your route:

- rewrite with `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`;
- use `MeasureTheory.prob_le_one` on every event measure;
- use `Finset.sum_le_sum`;
- simplify the constant-one sum over `Finset.range n`.

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
- `lintegral_natCast_pullCount_le_time`.

Please recommend exactly one next executable leaf.

Questions:

1. Should the next leaf be the weighted probability bound
   `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`, a
   `Fin K`/`Finset.univ` specialization, or the first scalar-conversion design
   toward `Rat`/`Real` expected regret?
2. What exact Lean-facing statement and imports would you recommend next?
3. What regularity contracts should be explicit?
4. What should be the failure policy?
5. How much work should be completed before asking you again?
