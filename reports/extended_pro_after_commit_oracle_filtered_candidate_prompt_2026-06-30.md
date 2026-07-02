# Extended Pro Review Prompt: After Oracle Filtered-Sum Probability Wrapper

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
  - `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`.
- We are not allowed to jump to full ETC regret, UCB regret, Tsallis-INF,
  OFUL, RL/MDP theorem, concrete finite argmax construction, or concentration
  unless you can justify that the current local event/probability/oracle layer
  is saturated.

The latest completed Lean leaf is:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

It compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`. It
specializes the existing arbitrary commit-arm filtered-sum pairwise-tail
probability consumer to `commitArm omega := oracle.choose (empMean omega)`.
It does not require oracle measurability, event measurability, a probability
instance, concrete argmax construction, concentration, filtration, or final
ETC regret.

Verification after the leaf passed:

```text
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-lean-decls ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail --statement
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf.

Candidate A:

`ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL`

Specialize the already compiled
`ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail` to
`commitArm omega := oracle.choose (empMean omega)`, producing the if-zeroed
`Finset.univ` sum shape for oracle-selected wrong commits:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

Candidate B:

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY`

Prove only the measurability of the oracle-selected wrong-commit event under a
direct measurability assumption for the composed oracle choice. Do not prove
oracle measurability from `empMean`.

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

Candidate C:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Do not implement a concrete argmax oracle yet. Instead, write an exact
statement/import/proof-route card for constructing a finite argmax-backed
`ETC.CommitOracle K` later. This card must decide whether the route should use
Mathlib `Finset` argmax APIs, a project-local recursion over `Fin K`, or a
smaller wrapper theorem around an existing Mathlib declaration. It should be a
theorem-card-only planning artifact unless you can identify a very small
compiled local theorem that must come first.

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
