# Extended Pro Review Prompt: After Oracle Wrong-Event Measurability

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local
  proof.
- The finite-sum wrappers `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and
  `PSEUDOREGRET-FINSET` are already compiled.
- The abstract oracle/event/probability layer now contains:
  - `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`;
  - `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`;
  - `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`;
  - `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`;
  - `ETC.measurableSet_commitOracle_ne_bestArm`.
- We are not allowed to jump to full ETC regret, UCB regret, Tsallis-INF,
  OFUL, RL/MDP theorem, concrete finite argmax construction, or concentration
  unless you can justify that the current local event/probability/oracle layer
  is saturated.

The latest completed Lean leaf is:

```lean
theorem ETC.measurableSet_commitOracle_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
```

It compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`. It
specializes `ETC.measurableSet_commitArm_ne_bestArm` to the composed oracle
choice map. It deliberately assumes the composed measurability contract
directly, so it does not construct a concrete argmax oracle, prove
`oracle.choose` measurability from empirical means, add probability
assumptions, import concentration, introduce filtrations, or prove final ETC
regret.

Verification after the leaf passed:

```text
lake build BanditRLProof.Algorithms.ETCMeasurability
lake build Tests
python3 tools/bandit.py list-lean-decls ETC.measurableSet_commitOracle_ne_bestArm --statement
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf.

Candidate A:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Instead, write an exact
statement/import/proof-route card for constructing a finite argmax-backed
`ETC.CommitOracle K` later. This card must decide whether the route should use
Mathlib `Finset` argmax APIs, a project-local recursion over `Fin K`, or a
small wrapper theorem around an existing Mathlib declaration. It should be a
theorem-card-only planning artifact unless you can identify a very small
compiled local theorem that must come first.

Candidate B:

`ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`

Do not prove a concentration inequality. Instead, write an exact import-route
card for the future pairwise empirical-mean tail assumption consumed by the
compiled probability wrappers. The card must identify the Mathlib/LML
declarations or theorem-card gaps for sub-Gaussian/Hoeffding style tails,
state the eventual Lean-facing tail lemma shape, and state which measurability,
independence, filtration, and integrability contracts are still missing.

Candidate C:

`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD`

Do not prove a concrete oracle construction. Instead, write an exact
statement/import/proof-route card for eventually discharging
`Measurable (fun omega => oracle.choose (empMean omega))` from a concrete
finite argmax oracle plus empirical-mean measurability. The card must say
whether this should wait until a concrete argmax implementation exists, and
must not assume arbitrary function measurability for free.

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
