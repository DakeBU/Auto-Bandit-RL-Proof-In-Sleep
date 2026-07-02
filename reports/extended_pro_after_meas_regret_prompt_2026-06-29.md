# Extended Pro review request after MEAS-REGRET

Repository: `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`

Please review the current ABRL Lean formalization state after the pseudo-regret measurability leaf and recommend exactly one next executable leaf.

## Current goal

Advance the project from deterministic bandit/regret algebra into Mathlib-backed probability foundations, then toward concentration inequalities and complete UCB/ETC/Thompson/EXP3/Tsallis-INF/OFUL/RL theorem routes.

Policy:

- Do not treat theorem cards as local Lean proofs.
- Do not start from broad algorithm theorem statements.
- Pick exactly one executable unfinished/local leaf.
- Prefer a small Mathlib-backed leaf that compiles locally.
- Avoid probability measures, expectation, filtration, or concentration unless the next leaf genuinely needs them.

## New work completed since your last review

Your last recommendation was:

- accept `MEAS-SUMREWARDS` as-is;
- implement `MEAS-REGRET`, narrowly as pseudo-regret random-variable measurability;
- use a new file `BanditRLProof/MeasurableRegret.lean`;
- consume `pseudoRegret_eq_finset_sum`;
- use finite-domain measurability for `model.gap`;
- do not introduce probability measures, expectation, filtration, or concentration.

I implemented it.

New file:

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MathlibWrappers
```

New theorem:

```lean
theorem measurable_pseudoRegret
    {Omega : Type u}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    Measurable
      (fun omega : Omega => pseudoRegret model (action omega) n) := by
  have hgap : Measurable (fun a : Fin K => model.gap a) := by
    exact measurable_of_finite (fun a : Fin K => model.gap a)
  have hsum :
      Measurable
        (fun omega : Omega =>
          (Finset.range n).sum
            (fun t : Nat => model.gap (action omega t))) := by
    refine Finset.induction_on (Finset.range n) ?h_empty ?h_insert
    · simp
    · intro t s ht ih
      have hterm :
          Measurable
            (fun omega : Omega => model.gap (action omega t)) := by
        exact hgap.comp (haction t)
      simpa [Finset.sum_insert, ht] using hterm.add ih
  have hfun :
      (fun omega : Omega => pseudoRegret model (action omega) n)
        =
      (fun omega : Omega =>
        (Finset.range n).sum
          (fun t : Nat => model.gap (action omega t))) := by
    funext omega
    simpa using
      (pseudoRegret_eq_finset_sum
        (model := model)
        (action := action omega)
        (t := n))
  rw [hfun]
  exact hsum
```

Root import:

```lean
import BanditRLProof.MeasurableRegret
```

Consumer test added in `Tests/Basic.lean`.

Verification:

```text
lake build BanditRLProof.MeasurableRegret
lake build Tests.Basic
python3 -m py_compile tools\bandit.py
python3 tools\bandit.py reference-index
python3 tools\bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools\bandit.py memory-refresh BRL-ETC-PORT-001
python3 tools\bandit.py check
```

All passed. Full check:

```text
Build completed successfully (1704 jobs).
check passed
```

Local retrieval index:

```text
local declarations: 96
LOCAL-LEAF-MEASURABLE-REGRET:
- measurable_pseudoRegret
```

`python3 tools\bandit.py unfinished --status missing-leaf --status theorem-card` no longer lists `MEAS-REGRET`.

Remaining unfinished/theorem-card rows include:

- `MEAS-HISTORY`
- `MEAS-POLICY`
- `EXP-INDICATOR-PULL`
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
- `MEAS-REGRET`.

## Questions

1. Is `MEAS-REGRET / measurable_pseudoRegret` reasonable as implemented?
2. What is the single best next executable leaf now?
3. Should the next step be the first expectation canary, `EXP-INDICATOR-PULL`, a measurable pull-count bridge, or a history/policy measurability leaf?
4. Please provide the exact Lean-facing statement shape, imports/APIs to probe, proof route, regularity contracts, status classification, and failure policy.

Please keep the recommendation focused on one local Lean leaf and a minimal batch before asking again.
