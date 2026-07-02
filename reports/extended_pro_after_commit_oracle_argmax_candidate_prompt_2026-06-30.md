# Extended Pro Review Prompt: After Abstract Commit-Oracle Argmax Consumer

We are working in the Lean 4 project `Auto-Bandit-RL-Proof-In-Sleep`.

Current boundary:

- `python3 tools/bandit.py unfinished` still records
  `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` as theorem-card-only, not a local
  proof.
- The finite-sum wrappers `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and
  `PSEUDOREGRET-FINSET` are already compiled.
- We are not allowed to jump to a broad theorem such as full ETC regret, UCB
  regret, Tsallis-INF, OFUL, or RL/MDP theorem.
- Theorem-card and weapon-only rows are route evidence only, not local proofs.

The latest completed Lean leaf is:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores)) :
    Set.Subset
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

It compiles locally in `BanditRLProof.Algorithms.ETCMeasurability`. It only
consumes an abstract `ETC.CommitOracle` argmax certificate and the existing
wrong-commit set-inclusion theorem. It does not construct a concrete argmax
oracle, prove oracle measurability, add concentration, add filtration, or prove
the final ETC theorem.

Verification just passed:

```text
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-lean-decls ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle --statement
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

`check` passed: `lake build`, `lake build Tests`, and CLI tests all succeeded.

Please review whether this completed leaf is reasonable and choose exactly one
next unfinished leaf. Do not choose pairwise concentration, filtration,
conditional expectation, or final ETC/UCB theorem yet unless you can justify
why the local event/probability/oracle layer is already saturated.

Candidate A:

`ETC-COMMIT-ORACLE-PROB-WRAPPER`

Specialize the existing arbitrary-measure wrong-commit probability assembly to
`commitArm omega := oracle.choose (empMean omega)`, still under the abstract
`hchoose_argmax` contract.

Candidate B:

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY`

A thin event-measurability wrapper for
`{omega | oracle.choose (empMean omega) = model.bestArm -> False}`, consuming a
direct measurability assumption for `fun omega => oracle.choose (empMean omega)`
without proving the oracle itself measurable.

Candidate C:

`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`

Only write a route card for a future concrete finite argmax oracle; do not add a
local Lean proof yet. This should specify exact Mathlib imports/API and failure
policy for constructing a `Fin K -> Rat` argmax.

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
