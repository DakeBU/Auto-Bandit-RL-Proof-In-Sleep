# Extended Pro Review Prompt: After Oracle Choice Measurability Bridge

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local
  proof.
- The abstract oracle/event/probability layer now contains:
  - `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`;
  - `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`;
  - `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`;
  - `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`;
  - `ETC.measurableSet_commitOracle_ne_bestArm`;
  - `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.
- We are not allowed to jump to full ETC regret, UCB regret, Tsallis-INF,
  OFUL, RL/MDP theorem, concrete finite argmax construction, or concentration
  unless you can justify that the current local event/probability/oracle layer
  is saturated.

The latest completed Lean leaf is:

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)]
    [MeasurableSpace (Fin K -> Rat)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_emp :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

It compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`. Extended
Pro first selected `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`; its
own failure policy said the project-local compiled candidate should be used
immediately if `measurable_of_countable` and the explicit
`[Countable (Fin K -> Rat)]` / `[MeasurableSingletonClass (Fin K -> Rat)]`
contracts compile. They do compile. The theorem uses `measurable_of_countable`
for `fun score : Fin K -> Rat => oracle.choose score` and composes it with
the empirical-mean vector measurability assumption.

Verification after the leaf passed:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurable_commitOracle_choose_of_measurable_empMeanVector --statement
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf.

Candidate A:

`ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`

Prove or route-card the coordinate-to-vector empirical-mean measurability
bridge needed by the latest compiled oracle-choice theorem:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K -> Rat)]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

If this exact statement needs additional product measurable-space assumptions
or a different Mathlib API, state the corrected Lean-facing theorem.

Candidate B:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Write the exact
statement/import/proof-route card for constructing a finite argmax-backed
`ETC.CommitOracle K` later, including tie-breaking and argmax correctness.

Candidate C:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove a concentration inequality. Write the exact import-route card for
the future pairwise empirical-mean tail assumption consumed by the compiled
probability wrappers, including the missing measurability, independence,
filtration, and integrability contracts.

For the selected leaf, please provide:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or
  theorem-card-only;
- failure policy.

Also state explicitly which candidates should not be attempted in the same
batch.
