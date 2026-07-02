# Extended Pro Review Prompt: After EmpMean Vector Measurability Bridge

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local proof.
- The latest reviewer-approved and compiled leaf is:
  `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE`.
- It compiles locally as:

```lean
theorem ETC.measurable_empMeanVector_of_forall_measurable
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))
```

Proof:

```lean
by
  exact measurable_pi_lambda _ hmeas_coord
```

Verification after the leaf passed:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurable_empMeanVector_of_forall_measurable --statement
```

This leaf was selected by the previous Extended Pro review because it directly
supplies the `hmeas_emp` producer for:

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
```

Please review whether the completed empirical-mean vector leaf is reasonable
and choose exactly one next unfinished leaf.

Candidate A:

`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES`

Compose the new vector bridge with the existing oracle-choice measurability
bridge.  Candidate Lean-facing shape:

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

If this exact statement has the wrong measurable-space instance assumptions,
state the corrected theorem.

Candidate B:

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`

Compose coordinatewise empirical-mean measurability, oracle-choice
measurability, and the existing oracle wrong-event measurability wrapper to
prove the wrong-commit event measurable directly from coordinate measurability.

Candidate C:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet.  Write the exact route card for
constructing a finite argmax-backed `ETC.CommitOracle K` later, including
tie-breaking and argmax correctness.

Candidate D:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove concentration.  Write the exact import-route card for the future
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
