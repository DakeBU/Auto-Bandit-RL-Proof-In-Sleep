# Extended Pro review request after EXP-PULLCOUNT-LINTEGRAL

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the `ENNReal`
lower-integral pull-count identity and recommend exactly one next executable
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
- Avoid full expected regret, conditional expectation, filtration, kernels,
  and concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your recommendation after `EXP-FINSET-INDICATOR-PULL` was:

- accept `EXP-FINSET-INDICATOR-PULL /
  lintegral_finset_sum_actionTrace_eval_eq_indicator_one`;
- connect the finite-sum lower-integral bridge back to local `pullCount`;
- stay in `ENNReal / lintegral`;
- add `[DecidableEq Action]` only because the theorem connects to recursive
  `pullCount`;
- do not move to `MEAS-HISTORY`, `MEAS-POLICY`, Bochner expectation, expected
  regret, kernels, filtrations, or concentration.

I implemented it.

New file:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.ExpectationSums
import BanditRLProof.LeafLemmas
```

New theorem:

```lean
theorem lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      =
    (Finset.range n).sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  -- private pointwise helper rewrites scalar-casted pullCount to a
  -- Finset.range sum of action-event indicators.
  -- Then apply lintegral_finset_sum_actionTrace_eval_eq_indicator_one.
```

Private helper:

```lean
private theorem ennreal_natCast_pullCount_eq_finset_range_indicator_one
    {Omega : Type u} {Action : Type v} [DecidableEq Action]
    (action : Omega -> ActionTrace Action) (a : Action) (n : Nat)
    (omega : Omega) :
    ((pullCount (action omega) a n : Nat) : ENNReal) =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (1 : Omega -> ENNReal)) omega)
```

Implementation note:

- The helper compiled by induction on `n`.
- `Nat.cast_add` was only needed in the equality branch; the non-equality
  branch did not need it and the unused simp argument was removed.

Root import:

```lean
import BanditRLProof.ExpectationPullCount
```

Consumer test added in `Tests/Basic.lean`.

Documentation and harness updates:

- added `LOCAL-LEAF-EXPECTATION-PULLCOUNT`;
- added `EXP-PULLCOUNT-LINTEGRAL` as compiled-local in the Mathlib foundation
  leaf map;
- updated README, completion-gap audit, collaborator guide, project overview,
  theory tree, and UCB/ETC proof-obligation ledgers;
- refreshed retrieval indexes and UCB/ETC memory packets.

Verification:

```text
lake build BanditRLProof.ExpectationPullCount
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py list-lean-decls lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq --statement
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Final check:

```text
Build completed successfully (1761 jobs).
Build completed successfully (1763 jobs).
$ lake build
$ lake build Tests
check passed
```

Local retrieval index:

```text
local declarations: 101
lintegral_finset_sum_actionTrace_eval_eq_indicator_one 1 BanditRLProof/ExpectationSums.lean
lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq 1 BanditRLProof/ExpectationPullCount.lean
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card`
does not list `EXP-INDICATOR-PULL`, `EXP-FINSET-INDICATOR-PULL`, or
`EXP-PULLCOUNT-LINTEGRAL`.

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
- `EXP-FINSET-INDICATOR-PULL`;
- `EXP-PULLCOUNT-LINTEGRAL`.

## Questions

1. Is `EXP-PULLCOUNT-LINTEGRAL /
   lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`
   reasonable as implemented?
2. What is the single best next executable leaf now?
3. Should the next step be a constrained expected-regret bridge, another
   `ENNReal` count-sum corollary, a Bochner expectation canary, or
   `MEAS-HISTORY`/`MEAS-POLICY`?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe,
   proof route, regularity contracts, status classification, and failure
   policy.

Please keep the recommendation focused on one local Lean leaf and a minimal
batch before asking again.
