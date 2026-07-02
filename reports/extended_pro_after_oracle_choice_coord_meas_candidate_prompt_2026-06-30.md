# Extended Pro Review Prompt: After Oracle Choice Coordinate Measurability

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local proof.
- The latest reviewer-approved and compiled leaf is:
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`.
- It compiles locally as:

```lean
theorem ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

Proof route:

```lean
by
  have hvec :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) :=
    ETC.measurable_empMeanVector_of_forall_measurable
      (empMean := empMean) hmeas_coord
  exact
    ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
      (oracle := oracle)
      (empMean := empMean)
      hvec
```

Verification after the leaf passed:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurable_commitOracle_choose_of_forall_measurable_empMean --statement
```

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf.

Candidate A:

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`

Compose coordinatewise empirical-mean measurability, the new oracle-choice
measurability wrapper, and the existing oracle wrong-event measurability
wrapper to prove the wrong-commit event is measurable directly from coordinate
measurability. Candidate Lean-facing shape:

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

If this exact statement has the wrong measurable-space instance assumptions,
state the corrected theorem.

Candidate B:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Write the exact route card for
constructing a finite argmax-backed `ETC.CommitOracle K` later, including
tie-breaking and argmax correctness.

Candidate C:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove concentration. Write the exact import-route card for the future
pairwise empirical-mean tail assumption consumed by the compiled probability
wrappers, including measurability, independence, filtration, and integrability
contracts.

For the selected leaf, please provide:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or theorem-card-only;
- failure policy.

Also state explicitly which candidates should not be attempted in the same
batch.
