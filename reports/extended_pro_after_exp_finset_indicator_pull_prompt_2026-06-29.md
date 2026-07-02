# Extended Pro review request after EXP-FINSET-INDICATOR-PULL

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the `ENNReal`
finite-sum lower-integral bridge and recommend exactly one next executable
leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into
Mathlib-backed probability foundations, then toward concentration inequalities
and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished or local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid Bochner expected regret, conditional expectation, filtration, kernels,
  and concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your recommendation after `EXP-INDICATOR-PULL` was:

- accept `EXP-INDICATOR-PULL / lintegral_actionTrace_eval_eq_indicator_one`;
- add an `ENNReal` finite-sum lower-integral bridge before connecting to
  `pullCount`;
- use arbitrary measures and `Set.indicator (1 : Omega -> ENNReal)`;
- use `MeasureTheory.lintegral_finset_sum` because the local Mathlib version
  does not expose `MeasureTheory.lintegral_finsetSum`;
- do not add `pullCount`, Nat casts, Bochner expectation, `Rat`, `Real`,
  histories, policies, filtrations, kernels, or concentration in this batch.

I implemented it.

New file:

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import BanditRLProof.ExpectationFoundation
```

New theorem:

```lean
theorem lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (s : Finset Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
      =
    s.sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  have hmeas :
      forall t : Nat, t ∈ s ->
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega) := by
    intro t _ht
    exact measurable_actionTrace_eval_eq_indicator_const
      (action := action)
      (hmeas := haction)
      (a := a)
      (t := t)
      (c := (1 : ENNReal))
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
        =
      s.sum
        (fun t : Nat =>
          MeasureTheory.lintegral mu
            (fun omega : Omega =>
              (({omega' : Omega | action omega' t = a} : Set Omega).indicator
                (1 : Omega -> ENNReal)) omega)) := by
          simpa [Finset.sum_apply] using
            (@MeasureTheory.lintegral_finset_sum
              Omega Nat _ mu s
              (f := fun t omega =>
                (({omega' : Omega | action omega' t = a} : Set Omega).indicator
                  (1 : Omega -> ENNReal)) omega)
              hmeas)
    _ =
      s.sum
        (fun t : Nat =>
          mu {omega : Omega | action omega t = a}) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact lintegral_actionTrace_eval_eq_indicator_one
            (mu := mu)
            (action := action)
            (haction := haction)
            (a := a)
            (t := t)
```

Root import:

```lean
import BanditRLProof.ExpectationSums
```

Consumer test added in `Tests/Basic.lean`.

Documentation and harness updates:

- added `LOCAL-LEAF-EXPECTATION-SUMS`;
- added `EXP-FINSET-INDICATOR-PULL` as compiled-local in the Mathlib
  foundation leaf map;
- updated README, completion-gap audit, collaborator guide, project overview,
  theory tree, and UCB/ETC proof-obligation ledgers;
- refreshed retrieval indexes and UCB/ETC memory packets.

Verification:

```text
lake build BanditRLProof.ExpectationSums
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py list-lean-decls lintegral_finset_sum_actionTrace_eval_eq_indicator_one --statement
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Final check:

```text
Build completed successfully (1760 jobs).
Build completed successfully (1762 jobs).
$ lake build
$ lake build Tests
check passed
```

Local retrieval index:

```text
local declarations: 100
lintegral_actionTrace_eval_eq_indicator_one 1 BanditRLProof/ExpectationFoundation.lean
lintegral_finset_sum_actionTrace_eval_eq_indicator_one 1 BanditRLProof/ExpectationSums.lean
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card`
does not list `EXP-INDICATOR-PULL` or `EXP-FINSET-INDICATOR-PULL`.

Remaining unfinished/theorem-card rows include:

- `MEAS-HISTORY`
- `MEAS-POLICY`
- `EXP-REGRET-PULLCOUNT` theorem-card only
- `KERNEL-POLICY-BIND`
- `COND-EXPECT-REWARD`
- `POSTERIOR-KERNEL`
- `TS-PROB-MATCH` theorem-card only
- `FILTRATION-HISTORY`
- `ADAPTED-ACTION`
- `MART-DIFF-REWARD`
- `STOPPING-TIME-BUDGET`
- `TAIL-SUMMABILITY-UCB`
- FTRL/EXP3/Tsallis/OFUL leaves

## Existing compiled foundation

- deterministic finite-prefix/list bridges;
- `PULLCOUNT-FINSET`;
- `SUMREWARDS-FINSET`;
- `PSEUDOREGRET-FINSET`;
- `REGRET-PULLCOUNT`;
- `PULLCOUNT-SUM-TIME`;
- `MEAS-FIN-ACTION`;
- `MEAS-PULL-INDICATOR`;
- `MEAS-REWARD`;
- `MEAS-SELECTED-REWARD-FINITE-SUM`;
- `MEAS-SUMREWARDS`;
- `MEAS-REGRET`;
- `MEAS-PULLCOUNT`;
- `MEAS-PULLCOUNT-CAST`;
- `EXP-INDICATOR-PULL`;
- `EXP-FINSET-INDICATOR-PULL`.

## Questions

1. Is `EXP-FINSET-INDICATOR-PULL /
   lintegral_finset_sum_actionTrace_eval_eq_indicator_one` reasonable as
   implemented?
2. What is the single best next executable leaf now?
3. Should the next step connect the finite-sum bridge to `pullCount` through an
   `ENNReal` measure-theoretic pull-count identity, or should it move to
   `MEAS-HISTORY`, `MEAS-POLICY`, or a Bochner expectation canary?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe,
   proof route, regularity contracts, status classification, and failure
   policy.

Please keep the recommendation focused on one local Lean leaf and a minimal
batch before asking again.
