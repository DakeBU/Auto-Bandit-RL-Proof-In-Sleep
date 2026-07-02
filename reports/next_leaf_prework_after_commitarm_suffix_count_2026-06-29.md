# Next Leaf Prework After Commit-Arm Suffix Count

- Date: 2026-06-29
- Status: prework only, not reviewer-approved, not a local proof.
- Boundary: do not implement either candidate until Extended Pro or the user
  explicitly approves crossing the current ETC boundary.

## Current Verified Boundary

`python3 tools\bandit.py check` passes after:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT`
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT`
- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT`

The current `unfinished` recommendation says to stop and ask reviewer/Extended
Pro before adding phase-splitting helpers, extending `actionWithCommit` regret
past the exploration horizon, or moving to expectation, filtration,
concentration, or final theorem routes.

## Candidate A: Phase-Splitting Regret Equality

Leaf id proposal:
`ETC-ACTION-WITH-COMMIT-PSEUDOREGRET-SUFFIX-SPLIT`

Lean-facing statement:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) +
        (((r : Nat) : Rat) * model.gap commitArm)
```

Local APIs/imports:

- File target: `BanditRLProof/Algorithms/ETCRegretLemmas.lean`
- Existing imports already include:
  - `BanditRLProof.RegretCountBounds`
  - `BanditRLProof.Algorithms.ETCTraceCountLemmas`
- Direct local declarations:
  - `pseudoRegret_succ`
  - `ETC.actionWithCommit_eq_commitArm_of_ge`

Intended proof route:

1. Induct on `r`.
2. Base case: reduce with `pseudoRegret ... (horizon + 0)` and Nat/Rat casts.
3. Step case:
   - rewrite `Nat.add_succ`;
   - unfold one step with `pseudoRegret_succ`;
   - rewrite the action at time `spec.explorationPulls * K + r` with
     `ETC.actionWithCommit_eq_commitArm_of_ge`;
   - use the induction hypothesis;
   - close the Rat arithmetic for `(r + 1) * gap`.

Regularity contracts:

- `spec : ETC.Spec K`
- `model : FiniteBanditModel K`
- `commitArm : Fin K`
- `r : Nat`
- no empirical commit correctness;
- no probability, expectation, filtration, or concentration assumptions.

Retrieval evidence:

- `python3 tools\bandit.py list-lean-decls actionWithCommit --statement`
  lists `ETC.actionWithCommit_eq_commitArm_of_ge`.
- `python3 tools\bandit.py list-lean-decls pseudoRegret_add_eq --statement`
  shows existing zero-suffix helpers only for best-arm/gap-zero segments, so an
  arbitrary-commit split is not already present.

Classification:

- `project-local` candidate.

Failure policy:

- If Rat/Nat cast arithmetic becomes the main obstacle, do not add broad
  algebra imports casually. Stop with a proof attempt note and either ask
  Extended Pro for the smallest arithmetic lemma or switch to Candidate B.
- Do not use this leaf to claim ETC regret optimality or wrong-commit
  probability.

## Candidate B: Unsimplified Post-Horizon Count-Budget Regret Bound

Leaf id proposal:
`ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET-BOUND`

Lean-facing statement:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          model.gap a *
            (((spec.explorationPulls +
                (if commitArm = a then r else 0) : Nat) : Rat)))
```

Local APIs/imports:

- File target: `BanditRLProof/Algorithms/ETCRegretLemmas.lean`
- Existing imports already include:
  - `BanditRLProof.RegretCountBounds`
  - `BanditRLProof.Algorithms.ETCTraceCountLemmas`
- Direct local declarations:
  - `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`
  - `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`

Intended proof route:

1. Apply `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`.
2. Instantiate `B a = spec.explorationPulls + if commitArm = a then r else 0`.
3. For each arm, discharge `pullCount ... <= B a` by rewriting with
   `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`, then using
   `le_of_eq`.

Regularity contracts:

- `spec : ETC.Spec K`
- `model : FiniteBanditModel K`
- `commitArm : Fin K`
- `r : Nat`
- finite arms through `Fin K` and `Finset.univ`;
- no probability, expectation, empirical means, or commit selection rule.

Retrieval evidence:

- `python3 tools\bandit.py list-lean-decls ETC.pullCount_actionWithCommit --statement`
  lists the compiled suffix count theorem and both commit/noncommit corollaries.
- `python3 tools\bandit.py list-lean-decls pseudoRegret_actionWithCommit --statement`
  lists only the exploration-horizon regret bound, so no post-horizon regret
  bound is currently compiled.

Classification:

- `project-local` candidate.

Failure policy:

- Keep the theorem in the unsimplified count-budget form first.
- Do not try to simplify the RHS into
  `(sum gaps) * explorationPulls + gap commitArm * r` in the same leaf.
- If `Finset`/cast simplification causes proof churn, stop with the exact failed
  goal and ask Extended Pro whether to add a smaller arithmetic helper first.

## Recommendation For Reviewer Prompt

Ask Extended Pro to choose between Candidate A and Candidate B. Candidate A is
mathematically cleaner for phase splitting. Candidate B is likely the smaller
Lean leaf because it consumes the already compiled pull-count suffix theorem and
the existing regret-count adapter.

