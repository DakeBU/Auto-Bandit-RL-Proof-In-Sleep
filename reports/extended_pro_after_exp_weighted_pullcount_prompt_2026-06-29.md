# Extended Pro Review Prompt: After EXP-WEIGHTED-PULLCOUNT-LINTEGRAL

We are working in the Lean 4 repository `Auto-Bandit-RL-Proof-In-Sleep`.

Current goal: build a Lean-checked foundation for bandit/RL proof libraries,
starting with finite stochastic bandit bookkeeping, measure/probability
bridges, concentration routes, and then UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL
and RL theorem routes.

Compiled local progress now includes:

- deterministic finite bookkeeping leaves for `pullCount`, `sumRewards`, and
  `pseudoRegret`;
- Mathlib-backed `Finset.range` wrappers:
  `pullCount_eq_finset_filter_card`,
  `sumRewards_eq_finset_filter_sum`,
  `pseudoRegret_eq_finset_sum`;
- deterministic regret/count consumers:
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount`,
  `finset_sum_pullCount_eq_time`;
- measurable action/reward/local quantity leaves:
  `measurableSet_actionTrace_eval_eq`,
  `measurable_actionTrace_eval_eq_indicator_const`,
  `measurable_actionTrace_eval_eq_indicator_reward`,
  `measurable_finset_sum_indicator_reward`,
  `measurable_sumRewards`,
  `measurable_pseudoRegret`,
  `measurable_pullCount`,
  `measurable_natCast_pullCount`;
- lower-integral expectation bridges:
  `lintegral_actionTrace_eval_eq_indicator_one`,
  `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`,
  `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`,
  `lintegral_finset_sum_gap_mul_natCast_pullCount_eq`.

The new compiled theorem is:

```lean
theorem lintegral_finset_sum_gap_mul_natCast_pullCount_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Action -> ENNReal) (arms : Finset Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      =
    arms.sum
      (fun a : Action =>
        gap a *
          (Finset.range n).sum
            (fun t : Nat =>
              mu {omega : Omega | action omega t = a}))
```

Verification just passed:

```text
python3 tools/bandit.py check
Build completed successfully.
Build completed successfully.
check passed
```

I also updated:

- `tools/bandit.py` local leaf cards and recommendation output;
- `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`;
- `docs/completion_gap_audit.md`;
- `README.md`;
- `docs/project_overview_next_plan.md`;
- `docs/collaborator_unfinished_work_guide.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- UCB/ETC proof-obligation ledgers and retrieval indexes.

Please review the next-step plan.

Questions:

1. Is this weighted lower-integral bridge the right stopping point before
   Bochner expectation, integrability, filtration, or concentration?
2. What is the single best next unfinished leaf to attempt, given the current
   library state?
3. Should the next leaf be an import-route wrapper, such as bounded reward
   integrability or finite-sum expectation linearity, or a project-local
   `ENNReal`/probability bridge?
4. What exact Lean-facing statement and imports would you recommend next?
5. What failure policy should be used if the next leaf exposes missing
   regularity assumptions?
