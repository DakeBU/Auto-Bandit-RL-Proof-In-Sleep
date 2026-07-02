# Manual Extended Pro Handoff: Commit-Arm Suffix Count Boundary

- Date: 2026-06-30
- Boundary: `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT`
- Prompt source:
  `reports/extended_pro_after_commitarm_suffix_count_candidate_prompt_2026-06-29.md`
- Response template:
  `reports/extended_pro_after_commitarm_suffix_count_response_template_2026-06-29.md`
- Completed response target:
  `reports/extended_pro_after_commitarm_suffix_count_2026-06-30.md`

## Current Gate State

```powershell
python3 tools\bandit.py review-status --json
```

The current expected state is `response_received: false`.  Do not cross the
boundary until a completed response artifact is saved and:

```powershell
python3 tools\bandit.py review-status --require-response
```

returns success.

## Manual Submission Steps

1. Print the prompt:

   ```powershell
   python3 tools\bandit.py extended-pro-prompt
   ```

2. Paste the full prompt into ChatGPT Extended Pro.

3. Wait for the full response. Ask for no follow-up unless the page reports an
   explicit failure.

4. Save the raw Extended Pro answer to a temporary text file, for example:

   ```powershell
   reports\extended_pro_after_commitarm_suffix_count_raw_2026-06-30.md
   ```

5. Record a completed response artifact:

   ```powershell
   python3 tools\bandit.py extended-pro-record-response `
     --raw reports\extended_pro_after_commitarm_suffix_count_raw_2026-06-30.md `
     --output reports\extended_pro_after_commitarm_suffix_count_2026-06-30.md `
     --chosen-leaf "FILL FROM EXTENDED PRO" `
     --classification "FILL FROM EXTENDED PRO"
   ```

   If you prefer to fill the response manually, print the template with:

   ```text
   python3 tools\bandit.py extended-pro-response-template
   ```

6. Verify the response gate and Lean gate:

   ```powershell
   python3 tools\bandit.py review-status --require-response
   python3 tools\bandit.py check
   ```

## Prompt To Submit

`````text
# Extended Pro Review Prompt: Choose Next ETC Leaf

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` compiles locally.
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` compiles locally.
- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` compiles locally.
- `python3 tools\bandit.py check` passes:
  - `lake build`
  - `lake build Tests`

Current boundary from `python3 tools\bandit.py unfinished`:

- stop and ask reviewer/Extended Pro before adding phase-splitting helpers,
  extending `actionWithCommit` regret past the exploration horizon, or moving
  to Rat-valued/Bochner expected regret, filtration, concentration, or any
  algorithm-specific final theorem.

Newest compiled theorem:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) commitArm
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + r
```

Relevant local APIs:

```lean
theorem ETC.actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm

theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0)

theorem pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Nat)
    (hB : forall a : Fin K, pullCount action a n <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (((B a : Nat) : Rat)))
```

Please choose the next exact single leaf. Two candidates follow.

## Candidate A: Phase-Splitting Regret Equality

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

Intended proof route:

1. Induct on `r`.
2. Use `pseudoRegret_succ`.
3. Use `ETC.actionWithCommit_eq_commitArm_of_ge`.
4. Close Nat-to-Rat arithmetic.

Concern:

- This is conceptually clean but may spend time on Rat/Nat cast arithmetic.

## Candidate B: Unsimplified Count-Budget Regret Bound

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

Intended proof route:

1. Apply `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`.
2. Instantiate `B a = spec.explorationPulls + if commitArm = a then r else 0`.
3. Discharge the count bound with
   `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq` and `le_of_eq`.

Concern:

- This is less simplified mathematically, but likely the smaller Lean leaf.
- Do not simplify the RHS into an exploration term plus
  `model.gap commitArm * r` in the same leaf.

Requested response:

1. Pick exactly one candidate, or reject both with a smaller replacement.
2. Give the exact Lean-facing statement.
3. Give imports/local APIs.
4. Give the intended proof route.
5. Give regularity contracts.
6. Give retrieval evidence/classification.
7. Give failure policy.
`````
