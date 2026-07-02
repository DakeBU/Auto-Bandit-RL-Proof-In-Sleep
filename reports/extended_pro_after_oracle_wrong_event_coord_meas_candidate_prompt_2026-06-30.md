# Extended Pro Review Prompt: After Oracle Wrong-Event Coordinate Measurability

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local proof.
- The latest reviewer-approved and compiled leaf is:
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`.
- It compiles locally as:

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

Proof route:

```lean
by
  have hchoose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega)) :=
    ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
      (oracle := oracle)
      (empMean := empMean)
      hmeas_coord
  exact
    ETC.measurableSet_commitOracle_ne_bestArm
      (model := model)
      (oracle := oracle)
      (empMean := empMean)
      hchoose
```

Verification after the leaf passed:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean --statement
```

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf or route card.

Candidate A:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Write the exact route card for
constructing a finite argmax-backed `ETC.CommitOracle K` later, including
tie-breaking, `Fin K` nonemptiness, selected score maximality, measurability
contracts, and how it will feed the existing abstract oracle argmax consumer.

Candidate B:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove concentration. Write the exact import-route card for the future
pairwise empirical-mean tail assumption consumed by the compiled probability
wrappers, including measurable events, probability measure assumptions,
independence or filtration/adaptedness, bounded/sub-Gaussian reward contracts,
integrability, and the exact local tail-consumer target.

Candidate C:

`FILTRATION-HISTORY-ROUTE-CARD`

Do not implement filtration yet. Write the exact route card for finite history
sigma-algebras and filtration/adaptedness contracts that would later support
conditionally sub-Gaussian rewards and martingale differences.

For the selected leaf/card, please provide:

- exact Lean-facing statement;
- local APIs/imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib/LML/local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or theorem-card-only;
- failure policy.

Also state explicitly which candidates should not be attempted in the same
batch.
