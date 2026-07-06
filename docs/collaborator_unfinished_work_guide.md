# Collaborator Unfinished Work Guide

This guide is the entry point for contributors who want to move ABRL forward
without drifting into broad uncompiled theorem work.

## Start Here

Run:

```bash
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
```

Rows marked `theorem-card` are not local proofs until imported or ported.
Rows marked `weapon-only` are route inspiration only, not proof dependencies.
Rows marked `gate-pending` have local Lean text but are not certified until
`python3 tools/bandit.py check` succeeds.

## Review Direction

ChatGPT Extended Pro is no longer a required route gate.  When route judgment
is needed, use the local two-agent review workflow:

1. prepare the current boundary and candidate leaves;
2. ask one local agent to review Lean/API feasibility;
3. ask one local agent to review mathematical dependency order;
4. record the reconciled decision under `reports/local_dual_review_*.md`;
5. execute exactly the selected narrow leaf or route card.

Use:

```bash
python3 tools/bandit.py review-status
python3 tools/bandit.py review-prompt
```

Historical `extended_pro_*` files remain provenance only.

## Leaf Discipline

Do not start from a broad theorem such as "prove UCB regret" or "formalize
Tsallis-INF".  Pick exactly one unfinished leaf row and turn it into a concrete
leaf packet before editing Lean.

For each leaf, write:

- exact Lean-facing statement;
- local APIs and imports;
- intended proof route;
- regularity contracts;
- retrieval evidence from Mathlib, LML, and local declarations;
- status: imported, port candidate, Mathlib candidate, project-local, or
  theorem-card-only;
- failure policy.

## Closed Dependency-Light Leaves

The deterministic finite-prefix bridge trio is compiled locally:

```lean
theorem pullCount_eq_list_filter_length
    {Action : Type u} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a t =
      ((List.range t).filter (fun s : Nat => decide (action s = a))).length

theorem sumRewards_eq_list_range_foldl
    {Action Reward : Type u} [DecidableEq Action]
    [OfNat Reward 0] [HAdd Reward Reward Reward]
    (action : ActionTrace Action) (reward : RewardTrace Reward)
    (a : Action) (t : Nat) :
    sumRewards action reward a t =
      (List.range t).foldl
        (fun acc s => acc + if action s = a then reward s else 0)
        0

theorem pseudoRegret_eq_list_range_foldl
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (List.range t).foldl
        (fun acc s => acc + model.gap (action s))
        0
```

The first filtered reward-sum refinement is also compiled:

```lean
theorem sumRewards_eq_list_range_filter_foldl
    (hzero : forall x : Reward, x + 0 = x) :
    sumRewards action reward a t =
      ((List.range t).filter (fun s : Nat => decide (action s = a))).foldl
        (fun acc s => acc + reward s)
        0
```

The first ETC round-robin count-prep leaf is:

```lean
theorem ETC.exploreArm_add_K (spec : ETC.Spec K) (t : Nat) :
    ETC.exploreArm spec (t + K) = ETC.exploreArm spec t
```

The public modular characterization of the ETC selector is:

```lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val
```

The first ETC round-robin count scaffold is also compiled:

```lean
theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1
```

The ETC full-cycle extension recurrence is compiled:

```lean
theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1
```

The ETC multiple-full-cycle count theorem is compiled:

```lean
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m
```

The configured ETC exploration-horizon count adapter is compiled:

```lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls
```

The pure ETC exploration-prefix pseudo-regret scaffold is compiled:

```lean
theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

## Closed Mathlib Wrapper Leaves

The first Mathlib-backed canary is compiled locally:

```lean
import Mathlib.Data.Finset.Card

theorem pullCount_eq_finset_filter_card
    {Action : Type u} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).card
```

The proof route is induction on `t`, with `Finset.range_add_one`,
`Finset.filter_insert`, and the half-open fact that `t` is not in
`Finset.range t`.

The selected reward-sum wrapper is compiled with an intentionally stronger
Mathlib additive contract:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem sumRewards_eq_finset_filter_sum
    {Action Reward : Type u} [DecidableEq Action] [AddCommMonoid Reward]
    (action : ActionTrace Action) (reward : RewardTrace Reward)
    (a : Action) (t : Nat) :
    sumRewards action reward a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).sum
        (fun s : Nat => reward s)
```

The proof route is induction on `t`, `sumRewards_succ`,
`Finset.range_add_one`, `Finset.filter_insert`, and `add_comm` in the inserted
summand branch.

The pseudo-regret finite-sum wrapper is also compiled:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Rat

theorem pseudoRegret_eq_finset_sum
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (Finset.range t).sum (fun s : Nat => model.gap (action s))
```

The proof route is induction on `t`, `pseudoRegret_succ`, and
`Finset.sum_range_succ`.  `Mathlib.Algebra.Field.Rat` supplies the
`AddCommMonoid Rat` instance required by `Finset.sum`.

## Closed Consumer Leaf

The deterministic regret-by-pull-count decomposition is compiled locally:

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.MathlibWrappers

theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (pullCount action a t : Rat))
```

The proof route consumes `pseudoRegret_eq_finset_sum`,
`pullCount_eq_finset_filter_card`, `Finset.sum_fiberwise'`,
`Finset.sum_const`, and `nsmul_eq_mul'`.

The finite-action pull-count partition leaf is compiled locally:

```lean
import Mathlib.Data.Fintype.Basic
import BanditRLProof.MathlibWrappers

theorem finset_sum_pullCount_eq_time
    {Action : Type u} [Fintype Action] [DecidableEq Action]
    (action : ActionTrace Action) (t : Nat) :
    (Finset.univ : Finset Action).sum
      (fun a : Action => pullCount action a t) = t
```

The proof route consumes `pullCount_eq_finset_filter_card` and
`Finset.card_eq_sum_card_fiberwise`.

The first measurable action-event leaf is compiled locally:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import BanditRLProof.Core

theorem measurableSet_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a}
```

The proof route applies the measurable time-`t` action random variable to the
measurable singleton `{a}` and simplifies the preimage.

The pull-event indicator measurability leaf is also compiled locally:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core

theorem measurable_actionTrace_eval_eq_indicator_const
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [Zero Beta]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) (c : Beta) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun _ : Omega => c))
```

The proof route consumes `measurableSet_actionTrace_eval_eq`,
`measurable_const`, and `Measurable.indicator`.

The selected-reward indicator measurability leaf is also compiled locally:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import BanditRLProof.Core

theorem measurable_actionTrace_eval_eq_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t))
```

The proof route consumes `measurableSet_actionTrace_eval_eq`, the reward
evaluation measurability hypothesis, and `Measurable.indicator`.  It is not an
expectation, integrability, or concentration theorem.

The selected-reward finite-sum measurability leaf is compiled locally:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation

theorem measurable_finset_sum_indicator_reward
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (s : Finset Nat) :
    Measurable
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega))
```

The proof route is finite-set induction plus `Measurable.add`, reusing
`measurable_actionTrace_eval_eq_indicator_reward` for each summand.  It is still
pre-expectation and pre-filtration.

The local `sumRewards` measurability bridge is compiled locally:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import BanditRLProof.MeasurableSums
import BanditRLProof.MathlibWrappers

theorem measurable_sumRewards
    {Omega : Type u} {Action : Type v} {Reward : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n)
```

This leaf uses `sumRewards_eq_finset_filter_sum`,
`Finset.sum_indicator_eq_sum_filter`, and
`measurable_finset_sum_indicator_reward`.  The `Action` and `Reward` universes
are intentionally aligned with the current `MathlibWrappers` API.

The pseudo-regret random-variable measurability bridge is compiled locally:

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MathlibWrappers

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
      (fun omega : Omega => pseudoRegret model (action omega) n)
```

This leaf uses `measurable_of_finite` for the finite-domain gap function,
composition with measurable action evaluations, finite-set induction with
`Measurable.add`, and `pseudoRegret_eq_finset_sum`.  It is still
pre-expectation: no measure, integral, filtration, or concentration theorem is
introduced.

The pull-count random-variable measurability bridge is compiled locally:

```lean
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
import BanditRLProof.LeafLemmas

theorem measurable_pullCount
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => pullCount (action omega) a n)
```

This leaf uses induction on the local recursive `pullCount`, the measurable
action-equality event bridge, `Measurable.ite`, and `Measurable.add`.  It is a
prerequisite for expected pull-count identities, not an expectation theorem.

The scalar-casted pull-count measurability bridge is compiled locally:

```lean
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasurablePullCount

theorem measurable_natCast_pullCount
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : Beta))
```

This leaf proves the scalar form needed by regret algebra without requiring a
measurable-space contract on `Nat`.  Later consumers can instantiate
`Beta := Rat`.

## Suggested Leaf Order

1. Keep the compiled dependency-light bridges stable.
2. Treat `PULLCOUNT-FINSET`, `SUMREWARDS-FINSET`, and
   `PSEUDOREGRET-FINSET` as the closed deterministic Mathlib wrapper layer.
3. Treat `REGRET-PULLCOUNT` as the first closed deterministic consumer leaf.
4. Treat `PULLCOUNT-SUM-TIME` as the closed deterministic finite-action count
   partition leaf.
5. Treat `MEAS-FIN-ACTION` as the first closed probability/measure canary.
6. Treat `MEAS-PULL-INDICATOR` as the second closed probability/measure
   canary.
7. Treat `MEAS-REWARD` as the selected-reward indicator measurability canary.
8. Treat `MEAS-HISTORY` as the finite action/reward history
   product-measurability surface over `Finset.Iic` prefixes.
9. Treat `MEAS-SELECTED-REWARD-FINITE-SUM` as the selected-reward finite-sum
   measurability bridge.
10. Treat `MEAS-SUMREWARDS` as the local recursive reward-sum measurability
   bridge.
11. Treat `MEAS-REGRET` as the local pseudo-regret random-variable
    measurability bridge.
12. Treat `MEAS-PULLCOUNT` as the local pull-count random-variable
    measurability bridge.
13. Treat `MEAS-PULLCOUNT-CAST` as the scalar-casted pull-count measurability
    bridge.
14. Treat `EXP-INDICATOR-PULL` as the first lower-integral
    indicator/event-measure canary.
15. Treat `EXP-FINSET-INDICATOR-PULL` as the lower-integral finite-sum bridge
    for action-event indicators.
16. Treat `EXP-PULLCOUNT-LINTEGRAL` as the lower-integral pull-count identity.
17. Treat `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` as the lower-integral weighted
    pull-count bridge.
18. Treat `EXP-PULLCOUNT-LE-TIME` as the probability-measure pull-count
    budget bound.
19. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME` as the probability-measure weighted
    pull-count budget bound.
20. Treat `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` as the `Fin K`/`Finset.univ`
    specialization of the weighted probability budget bound.
21. Treat `EXP-MODEL-GAP-OFREAL-BOUND` as the `ENNReal.ofReal` surrogate
    model-gap bound, not as faithful Rat-valued expected regret.
22. Treat `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` as the scalar
    `ENNReal.ofReal` faithfulness leaf for nonnegative real weights and Nat
    counts.
23. Treat `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` as the pointwise
    scalar/model bridge from Rat pseudo-regret to the `ENNReal.ofReal`
    weighted pull-count expression under explicit gap nonnegativity.
24. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND` as the `ENNReal.ofReal`
    lower-integral pseudo-regret bound under explicit gap nonnegativity.
25. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` as the Rat-level
    gap nonnegativity contract adapter for the lower-integral pseudo-regret
    bound.
26. Treat `FINITE-BANDIT-GAP-BESTARM` as the compiled zero-gap invariant for
    the selected best arm.
27. Treat `FINITE-BANDIT-BESTARM-DOMINATES` as the compiled model-invariant
    prerequisite for deriving `FiniteBanditModel.gap_nonneg`.
28. Treat `FINITE-BANDIT-GAP-NONNEG` as the compiled model-invariant source
    for the explicit Rat-level gap nonnegativity contract.
    The same model-invariant module now also exposes
    `FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
    `FINITE-BANDIT-MAXGAP-NONNEG` for sharper suffix bounds.
29. Treat `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` as the compiled
    no-explicit-`hgap` `ENNReal.ofReal` lower-integral pseudo-regret bound.
30. Treat `REGRET-COUNT-BOUND` as the deterministic count-bound-to-regret
    scaffold.
31. Treat `REGRET-NAT-COUNT-BOUND` as the deterministic Nat-count-to-regret
    adapter.
32. Treat `REGRET-UNIFORM-NAT-COUNT-BOUND` as the deterministic uniform
    Nat-count-to-regret adapter.
33. Treat `ETC-EXPLOREARM-EQ-IFF-MOD` as the deterministic modular selector
    helper for future ETC count theorems.
34. Treat `ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` as the first deterministic ETC
    round-robin count scaffold.
35. Treat `ETC-ROUND-ROBIN-ADD-K-COUNT` as the deterministic full-cycle
    extension recurrence for ETC pull counts.
36. Treat `ETC-ROUND-ROBIN-MUL-K-COUNT` as the deterministic multiple-full-cycle
    ETC count theorem.
37. Treat `ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` as the deterministic
    configured exploration-horizon count adapter.
38. Treat `ETC-EXPLORATION-REGRET-BOUND` as the deterministic exploration-only
    ETC pseudo-regret scaffold.
39. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` as the fixed-commit ETC trace
    boundary on the exploration prefix.
40. Treat `ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` as the fixed-commit ETC trace
    boundary after the exploration horizon.
41. Treat `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` as the fixed-commit
    ETC trace boundary after the exploration horizon when the commit arm is
    the selected best arm.
42. Treat `ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` as the
    exploration-prefix pull-count transfer for the fixed-commit ETC trace.
43. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` as the configured
    exploration-horizon pull count for the fixed-commit ETC trace.
44. Treat `ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` as the
    deterministic fixed-commit ETC trace regret scaffold at the exploration
    horizon.
45. Treat `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` as the one-step
    post-commit pull-count recurrence for the fixed-commit ETC trace.
46. Treat `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` as the closed-form
    post-exploration suffix pull count for the fixed-commit ETC trace.
47. Treat `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` as the non-commit-arm
    post-exploration pull-count stability corollary.
48. Treat `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` as the commit-arm
    post-exploration pull-count corollary.
49. Use local two-agent review before adding phase-splitting helpers, extending
    `actionWithCommit` regret past the exploration horizon, or moving to
    Rat-valued expected regret, Bochner expectation, filtration, or the next
    algorithm-specific leaf.

## Closed Model-Invariant Leaf

`FINITE-BANDIT-GAP-BESTARM` is compiled locally:

```lean
import BanditRLProof.Core

@[simp] theorem FiniteBanditModel.gap_bestArm
    {K : Nat}
    (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0
```

- Local APIs/imports: `FiniteBanditModel.gap`, `FiniteBanditModel.bestArm`,
  and `BanditRLProof.Core`.
- Intended proof route: simplify the definitional best-arm branch of
  `FiniteBanditModel.gap`.
- Regularity contracts: only `model : FiniteBanditModel K`; no regret,
  expectation, probability, filtration, or concentration assumptions.
- Retrieval evidence: compiled theorem in `BanditRLProof.Core`, used by local
  best-arm pseudo-regret lemmas.
- Status: project-local compiled leaf.
- Failure policy: keep this theorem canonical in `Core.lean`; do not duplicate
  it in model-invariant or ETC files.

`FINITE-BANDIT-BESTARM-DOMINATES` is compiled locally:

```lean
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import BanditRLProof.Core

theorem FiniteBanditModel.mean_le_bestArm_mean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm
```

- Local APIs/imports: `FiniteBanditModel.bestArm`, `List.finRange`,
  `List.mem_finRange`, ordered `Rat`.
- Intended proof route: prove a private fold invariant for the best-arm
  selector, then instantiate it on `List.finRange K`.
- Regularity contracts: only `model.hK : 0 < K` from `FiniteBanditModel K` and
  `a : Fin K`; no probability, expectation, or concentration assumptions.
- Retrieval evidence: local selector in `BanditRLProof.Core`, Mathlib
  `Fintype`/`Fin` list enumeration, ordered-field facts for `Rat`.
- Status: project-local compiled leaf.
- Failure policy: if the selector changes, re-prove the fold invariant locally
  before using the theorem to derive `FiniteBanditModel.gap_nonneg`.

`FINITE-BANDIT-GAP-NONNEG` is compiled locally:

```lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a
```

- Local APIs/imports: `FiniteBanditModel.gap`, `FiniteBanditModel.bestMean`,
  `FiniteBanditModel.mean_le_bestArm_mean`, ordered `Rat`.
- Intended proof route: split on whether `a = model.bestArm`; the best-arm case
  reduces to gap zero, while the non-best case unfolds `bestMean` and uses
  `sub_nonneg.mpr (mean_le_bestArm_mean model a)`.
- Regularity contracts: exactly `model : FiniteBanditModel K` and `a : Fin K`;
  no measure, expectation, action trace, or concentration assumptions.
- Retrieval evidence: local `gap` definition in `BanditRLProof.Core`, compiled
  best-arm dominance leaf in `BanditRLProof.FiniteBanditModelInvariants`, and
  ordered-field subtraction facts for `Rat`.
- Status: project-local compiled leaf.
- Failure policy: if `gap` changes shape, inspect the definition first and
  prove any missing model-semantic invariant separately; do not patch this by
  adding external hypotheses or probability imports.

`FINITE-BANDIT-MAXGAP`, `FINITE-BANDIT-GAP-LE-MAXGAP`, and
`FINITE-BANDIT-MAXGAP-NONNEG` are compiled locally:

```lean
noncomputable def FiniteBanditModel.maxGap
    {K : Nat}
    (model : FiniteBanditModel K) : Rat

theorem FiniteBanditModel.gap_le_maxGap
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.gap a <= model.maxGap

theorem FiniteBanditModel.maxGap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) :
    (0 : Rat) <= model.maxGap
```

- Local APIs/imports: `FiniteBanditModel.gap`, `FiniteBanditModel.gap_bestArm`,
  `Finset.sup'`, `Finset.le_sup'`, `Finset.univ`, ordered `Rat`, and
  `Mathlib.Data.Finset.Lattice.Fold`.
- Intended proof route: define `maxGap` as `Finset.sup'` over
  `(Finset.univ : Finset (Fin K))`, using `model.bestArm` as the nonempty
  witness.  The pointwise upper bound is `Finset.le_sup'`; nonnegativity follows
  from the best-arm zero-gap fact and the pointwise upper bound.
- Regularity contracts: exactly `model : FiniteBanditModel K` and, for the
  pointwise theorem, `a : Fin K`; no measure, expectation, action trace,
  concentration, filtration, or algorithm assumptions.
- Retrieval evidence: local declarations
  `FiniteBanditModel.maxGap`, `FiniteBanditModel.gap_le_maxGap`, and
  `FiniteBanditModel.maxGap_nonneg` in
  `BanditRLProof.FiniteBanditModelInvariants`, plus Mathlib `Finset.sup'`.
- Status: project-local compiled finite model-invariant leaves.
- Failure policy: keep this as deterministic finite-model infrastructure.  Do
  not replace it with probabilistic assumptions, and do not use it to claim a
  Bochner/Rat-valued expected-regret theorem.

## Closed Finite-Sum Integrability Leaf

`INT-FINITE-SUM` is compiled locally as a reusable Mathlib wrapper:

```lean
theorem IntegrabilitySums.integrable_finset_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    {E : Type w} [TopologicalSpace E] [ESeminormedAddCommMonoid E]
    [ContinuousAdd E]
    (mu : Measure Omega)
    (s : Finset Idx)
    (f : Idx -> Omega -> E)
    (hf : forall i, i ∈ s -> Integrable (f i) mu) :
    Integrable (fun omega : Omega => s.sum (fun i => f i omega)) mu
```

```lean
theorem IntegrabilitySums.integrable_univ_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    {E : Type w} [TopologicalSpace E] [ESeminormedAddCommMonoid E]
    [ContinuousAdd E]
    (mu : Measure Omega)
    (f : Idx -> Omega -> E)
    (hf : forall i : Idx, Integrable (f i) mu) :
    Integrable
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => f i omega))
      mu
```

- Local APIs/imports: `BanditRLProof.IntegrabilitySums`, importing
  `Mathlib.MeasureTheory.Function.L1Space.Integrable`; exported by
  `BanditRLProof`.
- Intended proof route: thin wrappers over
  `MeasureTheory.integrable_finset_sum`; the `[Fintype]` variant supplies the
  finite-arm `(Finset.univ : Finset Idx)` shape.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  finite index set, additive integrable codomain
  `[TopologicalSpace E] [ESeminormedAddCommMonoid E] [ContinuousAdd E]`, and
  per-term integrability.  No probability instance, event measurability,
  Bochner integral equality, conditional expectation, concentration, or final
  regret theorem.
- Retrieval evidence: local declarations are
  `IntegrabilitySums.integrable_finset_sum` and
  `IntegrabilitySums.integrable_univ_sum`; Mathlib evidence is
  `MeasureTheory.integrable_finset_sum` /
  `MeasureTheory.integrable_finset_sum'`.
- Status: project-local compiled Mathlib-backed import wrapper for
  `INT-FINITE-SUM`.
- Failure policy: only repair the Mathlib import/signature or finite-sum target
  shape; do not use this leaf to claim expectation linearity
  (`EXP-FINITE-SUM`) or expected-regret decomposition.

## Closed Bochner Finite-Sum Expectation Leaf

`EXP-FINITE-SUM` is compiled locally as a reusable Mathlib wrapper:

```lean
theorem ExpectationBochnerSums.integral_finset_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    {E : Type w} [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure Omega)
    (s : Finset Idx)
    (f : Idx -> Omega -> E)
    (hf : forall i, i ∈ s -> Integrable (f i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega => s.sum (fun i => f i omega)) =
    s.sum (fun i => MeasureTheory.integral mu (f i))
```

```lean
theorem ExpectationBochnerSums.integral_univ_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure Omega)
    (f : Idx -> Omega -> E)
    (hf : forall i : Idx, Integrable (f i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => f i omega)) =
    (Finset.univ : Finset Idx).sum
      (fun i => MeasureTheory.integral mu (f i))
```

- Local APIs/imports: `BanditRLProof.ExpectationBochnerSums`, importing
  `Mathlib.MeasureTheory.Integral.Bochner.Basic` and
  `BanditRLProof.IntegrabilitySums`; exported by `BanditRLProof`.
- Intended proof route: thin wrapper over `MeasureTheory.integral_finset_sum`;
  the `[Fintype]` variant supplies the finite-arm `(Finset.univ :
  Finset Idx)` shape.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  finite index set, Bochner codomain
  `[NormedAddCommGroup E] [NormedSpace Real E]`, and per-term integrability.
  No probability instance, conditional expectation, concentration, action-trace
  model, or expected-regret decomposition.
- Retrieval evidence: local declarations are
  `ExpectationBochnerSums.integral_finset_sum` and
  `ExpectationBochnerSums.integral_univ_sum`; Mathlib evidence is
  `MeasureTheory.integral_finset_sum`.
- Status: project-local compiled Mathlib-backed import wrapper for
  `EXP-FINITE-SUM`.
- Failure policy: only repair the Mathlib import/signature or finite-sum target
  shape; the bandit-specific expected-regret decomposition is closed separately
  under stronger contracts as `EXP-REGRET-PULLCOUNT`; do not use this leaf to
  claim Bayesian regret or final algorithmic regret theorems.

## Closed Bochner/Real Expected-Regret Pull-Count Leaf

`EXP-REGRET-PULLCOUNT` is compiled locally as the bandit-specific Real-valued
Bochner expectation lift of the deterministic pull-count regret decomposition:

```lean
theorem integrable_real_pseudoRegret_of_integrable_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    Integrable
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real)) mu
```

```lean
theorem integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ((model.gap a : Rat) : Real) *
          MeasureTheory.integral mu
            (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Real)))
```

- Local APIs/imports: `BanditRLProof.ExpectationRegretPullCount`, importing
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`,
  `BanditRLProof.ExpectationBochnerSums`, and
  `BanditRLProof.RegretDecomposition`; exported by `BanditRLProof`.
- Intended proof route: cast the deterministic
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount` equality to `Real`, apply
  `ExpectationBochnerSums.integral_univ_sum` to the finite arm sum, and use
  `MeasureTheory.integral_const_mul` to pull each Real-cast gap outside the
  Bochner integral.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `action : Omega -> ActionTrace (Fin K)`,
  finite horizon `n`, and per-arm integrability of the Real-cast pull count.
  This contract derives Real-valued pseudo-regret integrability; it does not
  require gap nonnegativity, probability measure structure, concentration,
  filtrations, conditional expectation, or policy predictability.
- Retrieval evidence: local declarations are
  `integrable_real_pseudoRegret_of_integrable_pullCount` and
  `integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount`; supporting
  local cards are `LOCAL-LEAF-REGRET-DECOMPOSITION` and
  `LOCAL-LEAF-EXPECTATION-BOCHNER-SUMS`; Mathlib evidence is
  `MeasureTheory.integral_finset_sum`, `MeasureTheory.integral_const_mul`, and
  `Integrable.const_mul`.
- Status: project-local compiled Bochner/Real expected-regret decomposition for
  `EXP-REGRET-PULLCOUNT`.
- Failure policy: repair only the Real-cast Bochner decomposition, import shape,
  or integrability adapter.  Do not reinterpret this as a Rat-valued expectation
  theorem, an `ENNReal.ofReal` lower-integral theorem, a concentration result,
  Bayesian regret, UCB/ETC final regret, or an adaptive-policy theorem.

## Closed Model-Derived Lower-Integral Leaf

`EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` is compiled locally:

```lean
theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal))
```

- Local APIs/imports: `ExpectationPseudoRegretRatBounds`,
  `FiniteBanditModel.gap_nonneg`, and the existing probability/lower-integral
  contracts already required by the explicit-`hgap` theorem.
- Intended proof route: one-step reuse of
  `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`
  with `hgap := fun a => FiniteBanditModel.gap_nonneg model a`.
- Regularity contracts: probability measure, measurable finite-arm action
  evaluations, and `FiniteBanditModel K`; no Bochner expectation,
  integrability, filtration, kernel, concentration, or algorithm theorem.
- Retrieval evidence: compiled explicit Rat-gap adapter plus compiled
  model-gap nonnegativity leaf.
- Status: project-local compiled lower-integral surrogate.
- Failure policy: do not reprove gap nonnegativity or reopen the expectation
  chain; fix imports or theorem qualification only.

## Closed Deterministic Count-Bound Leaf

`REGRET-COUNT-BOUND` is compiled locally:

```lean
theorem pseudoRegret_le_finset_sum_gap_mul_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Rat)
    (hB : forall a : Fin K,
      ((pullCount action a n : Nat) : Rat) <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * B a)
```

- Local APIs/imports: `RegretDecomposition`,
  `FiniteBanditModel.gap_nonneg`, ordered finite sums, ordered `Rat`.
- Intended proof route: rewrite pseudo-regret with
  `pseudoRegret_eq_finset_sum_gap_mul_pullCount`, then apply
  `Finset.sum_le_sum` and `mul_le_mul_of_nonneg_left` using `hB` and
  `FiniteBanditModel.gap_nonneg`.
- Regularity contracts: deterministic action trace, finite-arm model, horizon,
  Rat-valued bound function `B`, and pointwise count bounds; no probability,
  expectation, filtration, concentration, or algorithm-specific assumptions.
- Retrieval evidence: compiled `REGRET-PULLCOUNT`, compiled
  `FINITE-BANDIT-GAP-NONNEG`, Mathlib `Finset.sum_le_sum`, ordered Rat
  multiplication monotonicity.
- Status: project-local compiled deterministic scaffold.
- Failure policy: keep this algorithm-neutral; do not specialize to UCB/ETC or
  import probability machinery to prove count bounds.

`REGRET-NAT-COUNT-BOUND` is compiled locally:

```lean
theorem pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (((B a : Nat) : Rat)))
```

- Local APIs/imports: `RegretCountBounds` and Nat-to-Rat order casts.
- Intended proof route: instantiate
  `pseudoRegret_le_finset_sum_gap_mul_count_bound` with
  `B := fun a => ((B a : Nat) : Rat)` and convert `hB` using `Nat.cast_le`.
- Regularity contracts: deterministic action trace, finite-arm model, horizon,
  Nat-valued bound function, and pointwise count bounds; no probability,
  expectation, filtration, concentration, or algorithm-specific assumptions.
- Retrieval evidence: compiled `REGRET-COUNT-BOUND` plus Mathlib
  `Nat.cast_le` from the Nat cast order layer.
- Status: project-local compiled deterministic adapter.
- Failure policy: keep this algorithm-neutral; do not start ETC/UCB-specific
  count facts in the same batch.

`REGRET-UNIFORM-NAT-COUNT-BOUND` is compiled locally:

```lean
theorem pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n B : Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B) :
    pseudoRegret model action n <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) * (((B : Nat) : Rat))
```

- Local APIs/imports: `RegretCountBounds` and `Finset.sum_mul`.
- Intended proof route: instantiate
  `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound` with a constant bound
  function, then factor the constant with `Finset.sum_mul`.
- Regularity contracts: deterministic action trace, finite-arm model, horizon,
  a uniform Nat-valued bound, and pointwise count bounds; no probability,
  expectation, filtration, concentration, or algorithm-specific assumptions.
- Retrieval evidence: compiled `REGRET-NAT-COUNT-BOUND` plus Mathlib
  `Finset.sum_mul`.
- Status: project-local compiled deterministic adapter.
- Failure policy: keep this algorithm-neutral; ask reviewer before generalizing
  algorithm-specific count scaffolds.

`ETC-EXPLOREARM-EQ-IFF-MOD` is compiled locally:

```lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val
```

- Local APIs/imports: existing `BanditRLProof.Algorithms.ETC` imports only.
- Intended proof route: one direction uses `congrArg Fin.val`; the reverse
  direction uses `Fin.ext`; both simplify with `ETC.exploreArm_val`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, `t : Nat`, and
  `a : Fin K`; `spec.hK` remains the positivity source.
- Retrieval evidence: local `ETC.exploreArm_val`; no Finset, pull-count,
  regret, probability, or concentration dependency.
- Status: project-local compiled ETC modular helper.
- Failure policy: do not weaken to one direction unless the iff exposes a real
  API problem; do not start the multiple-full-cycle count theorem in the same
  batch.

`ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1
```

- Local APIs/imports: `Mathlib.Data.Finset.Card`,
  `BanditRLProof.MathlibWrappers`, and `BanditRLProof.Algorithms.ETC`.
- Intended proof route: rewrite `pullCount` to a filtered `Finset.range K`
  cardinality, prove the filtered set is exactly `{a.val}`, then simplify the
  singleton cardinality.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, and
  `a : Fin K`; `spec.hK` supplies `0 < K`; no full ETC action trace,
  probability, expectation, filtration, concentration, or regret bound.
- Retrieval evidence: compiled `pullCount_eq_finset_filter_card`, local
  `ETC.exploreArm_val`, and Mathlib `Finset.range`/singleton-card APIs.
- Status: project-local compiled deterministic ETC count scaffold.
- Failure policy: do not define the full ETC trace in the same batch; if the
  filtered-finset proof becomes brittle, isolate the bounded-time
  `ETC.exploreArm spec s = a` iff `s = a.val` helper.

`ETC-ROUND-ROBIN-ADD-K-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCCountLemmas`,
  `ETC.pullCount_exploreArm_K_eq_one`, `ETC.exploreArm_add_K`, and the
  dependency-light `pullCount_succ` API available through local imports.
- Intended proof route: induct on `t`; base case consumes the first-cycle
  count theorem; successor case rewrites both sides with `pullCount_succ`,
  applies periodicity `ETC.exploreArm_add_K`, and closes by cases on whether
  the current arm equals `a`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, `a : Fin K`,
  and `t : Nat`; no full ETC action trace, probability, expectation,
  filtration, concentration, or regret bound.
- Retrieval evidence: compiled first-cycle count theorem, local ETC
  periodicity, and dependency-light pull-count recursion.
- Status: project-local compiled deterministic ETC count scaffold.
- Failure policy: do not jump to the full `m * K` theorem in the same batch if
  recurrence arithmetic breaks; first isolate the successor-step arithmetic or
  shifted-cycle proof.

`ETC-ROUND-ROBIN-MUL-K-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCCountLemmas` and the
  compiled `ETC.pullCount_exploreArm_add_K_eq_add_one` recurrence.
- Intended proof route: induct on `m`; base case simplifies the zero horizon;
  successor case rewrites with `Nat.succ_mul`, applies the add-`K` recurrence
  at `t := m * K`, then rewrites with the induction hypothesis.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, `a : Fin K`,
  and `m : Nat`; no full ETC action trace, probability, expectation,
  filtration, concentration, or regret bound.
- Retrieval evidence: compiled add-`K` recurrence and local pull-count
  recursion; no direct Finset proof needed in this leaf.
- Status: project-local compiled deterministic ETC count scaffold.
- Failure policy: if multiplication orientation becomes brittle, keep the
  statement as `m * K` and make the successor step explicit with
  `Nat.succ_mul`; do not switch to full trace or commit-phase work in the same
  batch.

`ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCCountLemmas` and the
  compiled `ETC.pullCount_exploreArm_mul_K_eq` theorem.
- Intended proof route: instantiate the multiple-cycle theorem with
  `m := spec.explorationPulls`; do not reprove by induction.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, and
  `a : Fin K`; no full ETC action trace, probability, expectation, filtration,
  concentration, empirical mean, commit argmax, or regret theorem.
- Retrieval evidence: compiled multiple-cycle ETC count theorem.
- Status: project-local compiled deterministic ETC count adapter.
- Failure policy: if named-argument elaboration is brittle, use positional
  application; do not define the full trace in the same batch.

`ETC-EXPLORATION-REGRET-BOUND` is compiled locally:

```lean
theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

- Local APIs/imports: `BanditRLProof.RegretCountBounds` and
  `BanditRLProof.Algorithms.ETCCountLemmas`.
- Intended proof route: instantiate
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` with
  `action := ETC.exploreArm spec`, horizon `spec.explorationPulls * K`, and
  uniform count bound `B := spec.explorationPulls`; discharge the count bound
  with `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, and
  `model : FiniteBanditModel K`; no full ETC trace, probability, expectation,
  filtration, concentration, empirical mean, or commit argmax.
- Retrieval evidence: compiled configured exploration count adapter and
  compiled uniform Nat-count pseudo-regret adapter.
- Status: project-local compiled deterministic ETC regret scaffold.
- Failure policy: keep the RHS orientation aligned with
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`; do not introduce a
  phase-switching trace or probability layer in the same batch.

`ETC-ACTION-WITH-COMMIT-EXPLORE-PHASE` is compiled locally:

```lean
def ETC.actionWithCommit
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) :
    ActionTrace (Fin K)

@[simp] theorem ETC.actionWithCommit_eq_exploreArm_of_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t
```

- Local APIs/imports: `BanditRLProof.Core` and
  `BanditRLProof.Algorithms.ETC`.
- Intended proof route: unfold the phase-switching trace and simplify the
  `if` branch with `h`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm : Fin K`, and `h : t < spec.explorationPulls * K`; no empirical
  means, commit argmax, probability, concentration, counts, or regret facts.
- Retrieval evidence: compiled `ETC.Spec`, `ActionTrace`, and
  `ETC.exploreArm`.
- Status: project-local compiled ETC trace-boundary leaf.
- Failure policy: keep that batch limited to the exploration-prefix theorem;
  the commit-phase theorem was handled as the separate leaf recorded below.

`ETC-ACTION-WITH-COMMIT-COMMIT-PHASE` is compiled locally:

```lean
@[simp] theorem ETC.actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm
```

- Local APIs/imports: the existing `BanditRLProof.Algorithms.ETCTrace` imports
  only `BanditRLProof.Core` and `BanditRLProof.Algorithms.ETC`.
- Intended proof route: convert the public `<=` condition to the inactive
  exploration branch with `Nat.not_lt_of_ge h`, then simplify
  `ETC.actionWithCommit`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm : Fin K`, and `h : spec.explorationPulls * K <= t`; no empirical
  means, commit argmax, probability, concentration, counts, or regret facts.
- Retrieval evidence: compiled `ETC.actionWithCommit` and the standard Nat
  order bridge `Nat.not_lt_of_ge`.
- Status: project-local compiled ETC trace-boundary leaf.
- Failure policy: keep the public statement in `<=` form; do not add the
  `not_lt` companion, pull-count transfer, or regret facts in the same batch.

`ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE` is compiled locally:

```lean
theorem ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (t : Nat)
    (hcommit : commitArm = model.bestArm)
    (ht : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = model.bestArm
```

- Local APIs/imports: the existing `BanditRLProof.Algorithms.ETCTrace` imports
  only `BanditRLProof.Core` and `BanditRLProof.Algorithms.ETC`.
- Intended proof route: rewrite with
  `ETC.actionWithCommit_eq_commitArm_of_ge`, then close with `hcommit`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, `t : Nat`,
  `hcommit : commitArm = model.bestArm`, and
  `ht : spec.explorationPulls * K <= t`; no empirical means, commit argmax,
  probability, concentration, counts, or regret facts.
- Retrieval evidence: Extended Pro chose this leaf in
  `reports/extended_pro_after_bestarm_suffix_regret_bound_response_2026-06-30.md`;
  local declaration `ETC.actionWithCommit_eq_commitArm_of_ge` is the only proof
  dependency.
- Status: project-local compiled ETC trace-boundary leaf.
- Failure policy: do not import regret/count/probability/concentration files
  into `ETCTrace.lean`; do not prove RHS algebra simplification in this batch.

`ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    pullCount (ETC.actionWithCommit spec commitArm) a n =
      pullCount (ETC.exploreArm spec) a n
```

- Local APIs/imports: `BanditRLProof.LeafLemmas` and
  `BanditRLProof.Algorithms.ETCTrace`.
- Intended proof route: induct on `n` after reverting `hn`; for the successor
  step derive `n < spec.explorationPulls * K`, rewrite both `pullCount_succ`
  recurrences, use the induction hypothesis, and rewrite the action at time
  `n` with `ETC.actionWithCommit_eq_exploreArm_of_lt`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, `n : Nat`, and
  `hn : n <= spec.explorationPulls * K`; no regret, empirical means, commit
  argmax, probability, concentration, or final theorem facts.
- Retrieval evidence: compiled `pullCount_succ` and the fixed-commit ETC
  exploration-phase theorem.
- Status: project-local compiled ETC deterministic trace/count transfer.
- Failure policy: keep that batch limited to the prefix transfer; the
  exploration-horizon count was handled as the separate leaf recorded below.

`ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) =
      spec.explorationPulls
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCTraceCountLemmas` imports
  `BanditRLProof.Algorithms.ETCCountLemmas` to consume the pure round-robin
  exploration-horizon count theorem.
- Intended proof route: rewrite the `actionWithCommit` pull count at horizon
  with `ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le` using
  `Nat.le_refl`, then close with
  `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`, and
  `commitArm a : Fin K`; no regret, empirical means, commit argmax,
  probability, concentration, or final theorem facts.
- Retrieval evidence: compiled exploration-prefix pull-count transfer and the
  compiled pure ETC exploration-horizon count adapter.
- Status: project-local compiled ETC trace/count adapter.
- Failure policy: do not prove regret facts, post-exploration corollaries, or
  phase-splitting helpers in the same batch.

`ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) {t : Nat}
    (ht : spec.explorationPulls * K <= t) :
    pullCount (ETC.actionWithCommit spec commitArm) a (Nat.succ t) =
      pullCount (ETC.actionWithCommit spec commitArm) a t +
        if commitArm = a then 1 else 0
```

- Local APIs/imports: `BanditRLProof.LeafLemmas`,
  `BanditRLProof.Algorithms.ETCTrace`, and the current
  `BanditRLProof.Algorithms.ETCTraceCountLemmas` import path.
- Intended proof route: rewrite with `pullCount_succ`, use
  `ETC.actionWithCommit_eq_commitArm_of_ge spec commitArm ht`, then close by
  simplifying the selected-arm branch.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and `ht : spec.explorationPulls * K <= t`; no
  empirical means, commit argmax, probability, concentration, regret, or final
  theorem facts.
- Retrieval evidence: compiled `pullCount_succ` and compiled fixed-commit ETC
  commit-phase theorem.
- Status: project-local compiled ETC deterministic trace/count update.
- Failure policy: do not prove additional suffix corollaries, regret facts,
  empirical commit correctness, or probability facts in the same batch.

`ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0)
```

- Local APIs/imports: the existing
  `BanditRLProof.Algorithms.ETCTraceCountLemmas` imports are enough.
- Intended proof route: induct on `r`; the base case consumes
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`; the successor
  step proves `spec.explorationPulls * K <= spec.explorationPulls * K + r`,
  consumes `ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge`,
  rewrites with `Nat.add_succ`, applies the induction hypothesis, then closes
  by cases on `commitArm = a`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and `r : Nat`; no regret, empirical means, commit
  argmax, probability, concentration, filtration, conditional expectation, or
  final theorem facts.
- Retrieval evidence: compiled fixed-commit ETC exploration-horizon count,
  compiled one-step post-commit count recurrence, and Nat arithmetic
  simplification including `Nat.le_add_right` and `Nat.add_succ`.
- Status: project-local compiled ETC deterministic trace/count closed form.
- Failure policy: keep the public horizon orientation
  `spec.explorationPulls * K + r`; do not prove phase splitting, regret facts,
  empirical commit correctness, or probability facts in the same batch.

`ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne
    {K : Nat} (spec : ETC.Spec K) {commitArm a : Fin K}
    (hne : commitArm ≠ a) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls
```

- Local APIs/imports: the existing
  `BanditRLProof.Algorithms.ETCTraceCountLemmas` imports are enough.
- Intended proof route: consume
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq` and simplify
  the `if commitArm = a then r else 0` branch with `hne`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, `hne : commitArm ≠ a`, and `r : Nat`; no regret,
  empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final theorem facts.
- Retrieval evidence: compiled fixed-commit ETC closed-form suffix count plus
  standard `if_neg`/Nat zero-add simplification through `simp`.
- Status: project-local compiled ETC deterministic trace/count corollary.
- Failure policy: do not prove phase splitting, regret facts, empirical commit
  correctness, or probability facts in the same batch.

`ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) commitArm
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + r
```

- Local APIs/imports: the existing
  `BanditRLProof.Algorithms.ETCTraceCountLemmas` imports are enough.
- Intended proof route: consume
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq` at
  `a := commitArm` and simplify the selected `if` branch.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm : Fin K`, and `r : Nat`; no regret, empirical means, commit
  argmax, probability, concentration, filtration, conditional expectation, or
  final theorem facts.
- Retrieval evidence: compiled fixed-commit ETC closed-form suffix count plus
  standard `if_pos rfl` simplification through `simp`.
- Status: project-local compiled ETC deterministic trace/count corollary.
- Failure policy: do not prove phase splitting, regret facts, empirical commit
  correctness, or probability facts in the same batch.

`ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.RegretCountBounds` and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`; consume
  `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound` and
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`.
- Intended proof route: instantiate the generic Nat-count regret adapter with
  `B a = spec.explorationPulls + (if commitArm = a then r else 0)`, then close
  the count bound using the fixed-commit suffix count theorem and `le_of_eq`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, and `r : Nat`; no RHS
  simplification, phase split, empirical means, commit argmax, probability,
  concentration, filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate B in
  `reports/extended_pro_after_commitarm_suffix_count_response_2026-06-30.md`;
  local declarations provide the exact count theorem and regret-count adapter.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove Candidate A, simplify the RHS, add empirical
  means/commit argmax, or move to probability/concentration facts in the same
  batch.

`ETC-ACTION-WITH-COMMIT-COARSE-SUFFIX-REGRET-BOUND` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls + r : Nat) : Rat))
```

- Local APIs/imports: `BanditRLProof.RegretCountBounds` and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`; consume
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` and
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`.
- Intended proof route: instantiate the uniform Nat-count regret adapter with
  budget `spec.explorationPulls + r`, rewrite the fixed-commit suffix pull
  count, and close the `if commitArm = a then r else 0 <= r` side condition by
  cases.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, and `r : Nat`; no phase
  split, RHS simplification, empirical means, commit argmax, probability,
  concentration, filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate C in
  `reports/extended_pro_after_suffix_budget_regret_response_2026-06-30.md`;
  local declarations provide the exact suffix count theorem and uniform
  regret-count adapter.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove Candidate A or Candidate B from the second
  review, simplify the existing Finset budget RHS, or move to
  probability/concentration facts in the same batch.

`ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) +
        (((r : Nat) : Rat) * model.gap commitArm)
```

- Local APIs/imports: `pseudoRegret_succ` and
  `ETC.actionWithCommit_eq_commitArm_of_ge`, available through the current
  `BanditRLProof.Algorithms.ETCRegretLemmas` imports.
- Intended proof route: induct on `r`; in the successor case rewrite the
  action at time `spec.explorationPulls * K + r` to `commitArm`, unfold the
  pseudo-regret recurrence, and close the Rat arithmetic with
  `Nat.cast_succ`, `add_mul`, `one_mul`, and associativity.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, and `r : Nat`; no
  empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate B in
  `reports/extended_pro_after_coarse_suffix_regret_response_2026-06-30.md`;
  local declarations provide the trace phase theorem and pseudo-regret
  recurrence.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove the generic constant-arm suffix lemma or RHS
  simplification in the same batch.

`ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K)
```

- Local APIs/imports: the phase-split equality
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`
  and `FiniteBanditModel.gap_bestArm`, visible through the current imports.
- Intended proof route: rewrite with the phase-split equality, rewrite
  `commitArm` to `model.bestArm`, then simplify the zero gap and zero suffix
  arithmetic.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, `r : Nat`, and
  `hcommit : commitArm = model.bestArm`; no empirical means, commit argmax,
  probability, concentration, filtration, conditional expectation, or final
  theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_gap_bestarm_response_2026-06-30.md`; local
  declarations provide the exact phase split and best-arm zero-gap theorem.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove the best-arm commit trace lemma, generic
  constant-arm suffix lemma, or RHS simplification in the same batch.

`ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

- Local APIs/imports:
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm`
  and
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`.
- Intended proof route: rewrite the suffix horizon to the exploration horizon
  with the no-extra-suffix theorem, then apply the existing exploration-horizon
  regret bound.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, `r : Nat`, and
  `hcommit : commitArm = model.bestArm`; no empirical means, commit argmax,
  probability, concentration, filtration, conditional expectation, or final
  theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_bestarm_suffix_no_regret_response_2026-06-30.md`;
  local declarations provide both direct inputs.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove the best-arm commit trace lemma, generic
  constant-arm suffix lemma, RHS simplification, or probabilistic ETC
  wrong-commit analysis in the same batch.

`ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * model.gap commitArm)
```

- Local APIs/imports: the phase-split equality and the exploration-horizon
  regret bound in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- Intended proof route: rewrite with the phase-split equality, apply the
  exploration-horizon bound, and keep the suffix term by `add_le_add` with
  `le_refl`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, and `r : Nat`; no RHS
  simplification, empirical means, commit argmax, probability, concentration,
  filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_phase_split_regret_response_2026-06-30.md`;
  local declarations provide the exact phase split and exploration-horizon
  bound.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove the Finset RHS simplification or generic
  constant-arm suffix lemma in the same batch.

Current boundary after this leaf:

- Ask reviewer/Extended Pro again before crossing from best-arm suffix regret
  bound into generic constant-arm suffix lemmas, RHS algebraic
  simplification, empirical commit selection, or probabilistic ETC wrong-commit
  analysis.

Current review update:

- Extended Pro selected `ETC-WRONG-COMMIT-PROBABILITY-DESIGN` after the
  deterministic best-arm commit-phase boundary.
- This is theorem-card-only / missing-leaf design, not a local Lean proof.
- The design lives at
  `research-wiki/open-problems/etc-wrong-commit-probability-design.md`.
- Extended Pro then selected the small commit-arm wrong-event measurability
  canary; it is recorded below as `ETC-MEAS-COMMITARM-NE-BESTARM`.
- Extended Pro then selected the pure wrong-commit set-inclusion leaf; it is
  recorded below as `ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT`.
- Extended Pro then selected the measure monotonicity wrapper; it is recorded
  below as `ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET`.
- Extended Pro then selected the pairwise empirical-mean comparison-event
  measurability canary; it is recorded below as
  `ETC-MEAS-EMPMEAN-GE-EMPMEAN`.
- Extended Pro then selected the finite existential wrong-mean event
  measurability wrapper; it is recorded below as
  `ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM`.
- Extended Pro then selected the finite-union probability upper-bound wrapper;
  it is recorded below as
  `ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM`.
- Extended Pro then selected the final elementary event-probability assembly;
  it is recorded below as
  `ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS`.
- Extended Pro then selected the abstract unguarded pairwise-tail consumer
  wrapper; it is recorded below as
  `ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL`.
- Extended Pro then selected the if-zeroed nonbest pairwise-tail consumer
  wrapper; it is recorded below as
  `ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL`.
- Extended Pro then selected the true filtered-sum pairwise-tail consumer
  wrapper; it is recorded below as
  `ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL`.
- Extended Pro then selected the deterministic Nat-level exploration
  pull-count positivity leaf; it is recorded below as
  `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`.
- Extended Pro then selected the Rat-cast denominator adapter; it is recorded
  below as
  `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS`.
- Extended Pro then selected the Rat nonzero denominator adapter; it is
  recorded below as
  `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO`.
- Do not start broad Hoeffding, martingale, conditional expectation, or final
  ETC theorem work from this card.

`ETC-MEAS-COMMITARM-NE-BESTARM` is compiled locally:

```lean
theorem ETC.measurableSet_commitArm_ne_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False}
```

- Local APIs/imports: `Mathlib.MeasureTheory.MeasurableSpace.Basic` and
  `BanditRLProof.Core`, in `BanditRLProof.Algorithms.ETCMeasurability`.
- Intended proof route: take the preimage of the singleton `{model.bestArm}`
  through `hmeas_commit`, then close under complement and rewrite to the
  implication-to-`False` event shape.
- Regularity contracts: only measurable `Omega`, measurable singleton
  codomain `Fin K`, `model : FiniteBanditModel K`, measurable
  `commitArm`; no measure, empirical means, argmax, probability,
  concentration, filtration, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_wrong_commit_design_response_2026-06-30.md`;
  local declaration is `ETC.measurableSet_commitArm_ne_bestArm`.
- Status: project-local compiled event/measurability leaf.
- Failure policy: if future generalization fails, do not proceed to
  empirical-mean comparisons or probability bounds in the same batch; record
  the exact import/typeclass obstruction.

`ETC-WRONG-COMMIT-SUBSET-WRONG-MEAN-EVENT` is compiled locally:

```lean
theorem ETC.wrong_commit_subset_exists_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    Set.Subset
      {omega : Omega | commitArm omega = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}
```

- Local APIs/imports: `BanditRLProof.Core`, `Set.Subset`, `Rat` order, and the
  existing `BanditRLProof.Algorithms.ETCMeasurability` module.  No new
  probability or ordered-measurability import is required.
- Intended proof route: introduce `omega` in the wrong-commit event; use
  `commitArm omega` as the existential witness; reuse `hwrong` as the proof the
  witness is not `model.bestArm`; use `hcommit_argmax omega model.bestArm`,
  with a `change` from `>=` to `<=` if needed.
- Regularity contracts: `model : FiniteBanditModel K`,
  `commitArm : Omega -> Fin K`, `empMean : Omega -> Fin K -> Rat`, and the
  explicit commit-arm argmax contract.  No `MeasurableSpace`, `Measure`,
  measurable `commitArm`, measurable `empMean`, probability, concentration,
  filtration, or final theorem facts are used.
- Retrieval evidence: Extended Pro chose Candidate C in
  `reports/extended_pro_after_commitarm_ne_bestarm_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.
- Status: project-local compiled event-reduction leaf.
- Failure policy: if a future strengthened form fails, do not pivot to
  empirical-mean measurability, finite unions, concentration, or the final
  probability theorem in the same batch; record the exact coercion/import
  obstruction.

`ETC-PROB-WRONG-COMMIT-LE-WRONG-MEAN-EVENTS-OF-SUBSET` is compiled locally:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

- Local APIs/imports: `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`,
  `Mathlib.MeasureTheory.MeasurableSpace.Basic`, `BanditRLProof.Core`, and the
  local subset theorem in `BanditRLProof.Algorithms.ETCMeasurability`; the file
  opens `MeasureTheory`.
- Intended proof route: apply `mu.mono` to
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm model commitArm empMean
  hcommit_argmax`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `commitArm : Omega -> Fin K`,
  `empMean : Omega -> Fin K -> Rat`, and the explicit commit-arm argmax
  contract.  No probability instance, event measurability, empirical-mean
  measurability, finite union, concentration, filtration, or final theorem
  facts are used.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_wrong_commit_subset_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset`; Mathlib
  evidence is `mu.mono` / `Measure.mono`.
- Status: project-local compiled probability-wrapper leaf.
- Failure policy: if a future strengthened form fails, only repair
  `Measure`/`mu.mono` namespace/import exposure or set-notation normalization;
  do not pivot to empirical-mean measurability, finite unions, concentration,
  or the final theorem in the same batch.

`ETC-MEAS-EMPMEAN-GE-EMPMEAN` is compiled locally:

```lean
theorem ETC.measurableSet_empMean_ge_empMean
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b}
```

- Local APIs/imports: `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`,
  `Mathlib.MeasureTheory.MeasurableSpace.Instances`,
  `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`,
  `Mathlib.MeasureTheory.MeasurableSpace.Basic`, and `BanditRLProof.Core`, in
  `BanditRLProof.Algorithms.ETCMeasurability`; uses `measurableSet_le`.
- Intended proof route: rewrite `>=` to `<=`, then apply
  `measurableSet_le (hmeas_empMean b) (hmeas_empMean a)`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `empMean : Omega -> Fin K -> Rat`, coordinate measurability of `empMean`;
  no `Measure`, probability instance, `commitArm`, argmax, finite union,
  concentration, filtration, empirical-mean construction, or final theorem.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_wrong_commit_measure_wrapper_response_2026-06-30.md`;
  local declaration is `ETC.measurableSet_empMean_ge_empMean`; Mathlib evidence
  is `measurableSet_le` plus Rat measurable instances.
- Status: project-local compiled event-regularity leaf.
- Failure policy: only repair ordered-measurability imports/API or
  `ge`/`le` normalization; do not pivot to finite union, concentration, or
  final theorem in the same batch.

`ETC-MEAS-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM` is compiled locally:

```lean
theorem ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm}
```

- Local APIs/imports: `Mathlib.MeasureTheory.Constructions.BorelSpace.Order`,
  `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`,
  `Mathlib.MeasureTheory.MeasurableSpace.Basic`,
  `Mathlib.MeasureTheory.MeasurableSpace.Instances`, and `BanditRLProof.Core`,
  in `BanditRLProof.Algorithms.ETCMeasurability`; uses
  `Finset.measurableSet_biUnion`, `Finset.univ`, and
  `ETC.measurableSet_empMean_ge_empMean`.
- Intended proof route: rewrite the existential over `Fin K` as a bounded
  union over `(Finset.univ : Finset (Fin K))`; apply
  `Finset.measurableSet_biUnion`; split on `a = model.bestArm`; the best-arm
  branch is empty, and the non-best branch reduces to the compiled pairwise
  empirical-mean comparison event.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `model : FiniteBanditModel K`, `empMean : Omega -> Fin K -> Rat`,
  coordinate measurability of `empMean`; no `Measure`, probability instance,
  `commitArm`, argmax, concentration, filtration, empirical-mean construction,
  or final theorem.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_empmean_pairwise_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm`; Mathlib evidence
  is `Finset.measurableSet_biUnion` in `MeasurableSpace.Defs`.
- Status: project-local compiled event-regularity leaf.
- Failure policy: only repair bounded-union elaboration or propositional guard
  rewriting; do not pivot to concentration, empirical-mean construction, or
  final theorem in the same batch.

`TAIL-UNION-FINITE` is compiled locally as a reusable Mathlib wrapper:

```lean
theorem ProbabilityUnionBound.measure_biUnion_finset_le
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v}
    (mu : Measure Omega)
    (s : Finset Idx)
    (E : Idx -> Set Omega) :
    mu (⋃ i ∈ s, E i) <=
      s.sum (fun i => mu (E i))
```

```lean
theorem ProbabilityUnionBound.measure_iUnion_fintype_le_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    (mu : Measure Omega)
    (E : Idx -> Set Omega) :
    mu (⋃ i, E i) <=
      (Finset.univ : Finset Idx).sum (fun i => mu (E i))
```

- Local APIs/imports: `BanditRLProof.ProbabilityUnionBound`, importing
  `Mathlib.MeasureTheory.Measure.MeasureSpaceDef` and
  `Mathlib.MeasureTheory.OuterMeasure.Basic`; exported by `BanditRLProof`.
- Intended proof route: thin wrappers over
  `MeasureTheory.measure_biUnion_finset_le` and
  `MeasureTheory.measure_iUnion_fintype_le`; the `[Fintype]` variant uses
  `(Finset.univ : Finset Idx)` to match finite-arm proof style.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  finite event family `E`; no event measurability, probability instance,
  concentration, filtration, empirical-mean construction, or final theorem.
- Retrieval evidence: local declarations are
  `ProbabilityUnionBound.measure_biUnion_finset_le` and
  `ProbabilityUnionBound.measure_iUnion_fintype_le_sum`; Mathlib evidence is
  `MeasureTheory.measure_biUnion_finset_le` /
  `MeasureTheory.measure_iUnion_fintype_le`.
- Status: project-local compiled Mathlib-backed import wrapper for
  `TAIL-UNION-FINITE`.
- Failure policy: only repair the Mathlib import/signature or finite-union
  target shape; do not start concentration, reward-law, or final regret theorem
  work in the same batch.

`TAIL-SUMMABILITY-UCB` is compiled locally as an abstract finite-horizon
bad-event summability wrapper:

```lean
def UCBSummability.finiteHorizonBadEvent
    {Omega : Type u} {Arm : Type v}
    (bad : Arm -> Nat -> Set Omega) (T : Nat) : Set Omega :=
  ⋃ a, ⋃ t ∈ Finset.range T, bad a t
```

```lean
theorem UCBSummability.measure_finiteHorizonBadEvent_le_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (T : Nat) :
    mu (UCBSummability.finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => mu (bad a t)))
```

```lean
theorem UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum
    {Omega : Type u} [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (tail : Arm -> Nat -> ENNReal)
    (T : Nat)
    (htail : forall a t, t < T -> mu (bad a t) <= tail a t) :
    mu (UCBSummability.finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => tail a t))
```

- Local APIs/imports: `BanditRLProof.UCBSummability`, importing
  `BanditRLProof.ProbabilityUnionBound`; exported by `BanditRLProof`.
- Intended proof route: define the double finite bad-event union over all arms
  and `Finset.range T`; apply
  `ProbabilityUnionBound.measure_iUnion_fintype_le_sum` to the arm union,
  apply `ProbabilityUnionBound.measure_biUnion_finset_le` to each time-indexed
  union, then use `Finset.sum_le_sum` and `Finset.mem_range` to consume the
  per-event tail bound.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `[Fintype Arm]`, finite horizon `T`, bad events
  `bad : Arm -> Nat -> Set Omega`, and a per-arm/per-time ENNReal bound
  `htail` for `t < T`; no event measurability, probability instance,
  sub-Gaussian proof, UCB confidence-radius algebra, log/sqrt side conditions,
  asymptotic summability, pull-count theorem, or final regret theorem.
- Retrieval evidence: local declarations are
  `UCBSummability.finiteHorizonBadEvent`,
  `UCBSummability.measure_finiteHorizonBadEvent_le_sum`, and
  `UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum`; they reuse
  `ProbabilityUnionBound.measure_iUnion_fintype_le_sum` and
  `ProbabilityUnionBound.measure_biUnion_finset_le`, whose Mathlib evidence is
  `MeasureTheory.measure_iUnion_fintype_le` and
  `MeasureTheory.measure_biUnion_finset_le`.
- Status: project-local compiled abstract UCB bad-event finite-horizon
  summability leaf.
- Failure policy: only repair the finite-union target shape, `Finset.range`
  membership bridge, or local probability-union wrapper import; do not pivot to
  UCB log/sqrt concentration, asymptotic series bounds, or final UCB regret in
  the same batch.

`ETC-PROB-EXISTS-NE-BESTARM-EMPMEAN-GE-BESTARM-LE-SUM` is compiled locally:

```lean
theorem ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

- Local APIs/imports: `Mathlib.MeasureTheory.OuterMeasure.Basic`,
  `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`, and the existing
  `BanditRLProof.Algorithms.ETCMeasurability` imports; uses
  `MeasureTheory.measure_biUnion_finset_le`.
- Intended proof route: define the guarded pairwise event family `E`; rewrite
  the existential event as `⋃ a ∈ (Finset.univ : Finset (Fin K)), E a`; apply
  `MeasureTheory.measure_biUnion_finset_le`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `empMean : Omega -> Fin K -> Rat`; no
  probability instance, event measurability, `hmeas_empMean`, `commitArm`,
  argmax, concentration, filtration, empirical-mean construction, or final
  theorem.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_finite_wrong_mean_event_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`; Mathlib evidence is
  `MeasureTheory.measure_biUnion_finset_le`.
- Status: project-local compiled probability-wrapper leaf.
- Failure policy: only repair `measure_biUnion_finset_le` import/signature or
  bounded-union set equality; do not pivot to empirical-mean construction,
  pairwise tails, or final theorem until this wrapper compiles.

`ETC-PROB-WRONG-COMMIT-LE-SUM-WRONG-MEAN-EVENTS` is compiled locally:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm})
```

- Local APIs/imports: existing `BanditRLProof.Algorithms.ETCMeasurability`
  imports; uses `le_trans` over the two compiled probability wrappers.
- Intended proof route: compose
  `ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset` with
  `ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `commitArm : Omega -> Fin K`,
  `empMean : Omega -> Fin K -> Rat`, and the explicit empirical-mean argmax
  contract; no probability instance, event measurability, `hmeas_empMean`,
  concentration, filtration, empirical-mean construction, pairwise tail bounds,
  or final theorem.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_finite_union_wrong_mean_prob_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`.
- Status: project-local compiled elementary probability-assembly leaf.
- Failure policy: if `le_trans` inference breaks, use the reviewer-provided
  `calc` proof; do not pivot to empirical-mean construction or pairwise tails
  in the same batch.

`ETC-PROB-WRONG-COMMIT-LE-SUM-PAIRWISE-TAIL` is compiled locally:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail
```

- Local APIs/imports: existing
  `BanditRLProof.Algorithms.ETCMeasurability` imports; uses
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`,
  `Finset.sum_le_sum`, `mu.mono`, and `simp` for the guarded best-arm empty
  event.
- Intended proof route: first bound wrong commit by the finite sum of guarded
  pairwise wrong-mean events; then compare each guarded summand to `tail a`.
  The best-arm summand is empty, and each non-best summand is bounded by
  erasing the guard and applying `hpair_tail`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `commitArm : Omega -> Fin K`,
  `empMean : Omega -> Fin K -> Rat`, `tail : Fin K -> ENNReal`, the explicit
  empirical-mean argmax contract, and abstract non-best pairwise tail
  assumptions.  No probability instance, event measurability,
  empirical-mean construction, actual concentration theorem, filtration,
  conditional expectation, independence, or final theorem facts are used.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_wrong_commit_sum_assembly_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail`.
- Status: project-local compiled tail-consumer probability-wrapper leaf.
- Failure policy: if a future strengthened form fails, only repair
  guarded-event erasure, `Finset.sum_le_sum`, or tail-contract shape; do not
  pivot to empirical-mean construction, Hoeffding, filtration, or final ETC
  theorem work in the same batch.

`ETC-PROB-WRONG-COMMIT-LE-SUM-NONBEST-PAIRWISE-TAIL` is compiled locally:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a)
```

- Local APIs/imports: existing
  `BanditRLProof.Algorithms.ETCMeasurability` imports; uses
  `ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events`,
  `Finset.sum_le_sum`, `mu.mono`, and `simp` for the best-arm zero branch.
- Intended proof route: first bound wrong commit by the finite sum of guarded
  pairwise wrong-mean events; then compare each guarded summand to
  `if a = model.bestArm then 0 else tail a`.  The best-arm summand is empty,
  and each non-best summand is bounded by erasing the guard and applying
  `hpair_tail`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `commitArm : Omega -> Fin K`,
  `empMean : Omega -> Fin K -> Rat`, `tail : Fin K -> ENNReal`, the explicit
  empirical-mean argmax contract, and abstract non-best pairwise tail
  assumptions.  No probability instance, event measurability,
  empirical-mean construction, actual concentration theorem, filtration,
  conditional expectation, independence, filtered-sum normalization, or final
  theorem facts are used.
- Retrieval evidence: Extended Pro chose the if-zeroed Candidate A variant in
  `reports/extended_pro_after_pairwise_tail_response_2026-06-30.md`; local
  declaration is
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`.
- Status: project-local compiled if-zeroed tail-consumer probability-wrapper
  leaf.
- Failure policy: if a future strengthened form fails, only repair
  guarded-event erasure, `Finset.sum_le_sum`, or `if`-branch simplification;
  do not pivot to empirical-mean construction, Hoeffding, filtration, true
  filtered-sum normalization, or final ETC theorem work in the same batch.

`ETC-PROB-WRONG-COMMIT-LE-FILTERED-SUM-PAIRWISE-TAIL` is compiled locally:

```lean
theorem ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

- Local APIs/imports: existing
  `BanditRLProof.Algorithms.ETCMeasurability` imports; uses
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail`,
  `Finset.sum_filter`, `Finset.sum_congr`, and proof-local `classical`.
- Intended proof route: invoke the compiled if-zeroed nonbest tail consumer;
  prove the RHS equality from the if-zeroed `Finset.univ` sum to the filtered
  non-best-arm sum by `Finset.sum_filter` and a pointwise `by_cases` split on
  `a = model.bestArm`; rewrite the bound.
- Regularity contracts: same arbitrary-measure contracts as the if-zeroed
  wrapper.  No probability instance, event measurability, empirical-mean
  construction, actual concentration theorem, filtration, conditional
  expectation, independence, or final theorem facts are used.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_nonbest_pairwise_tail_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail`.
- Status: project-local compiled filtered-sum tail-consumer
  probability-wrapper leaf.
- Failure policy: if a future strengthened form fails, only repair
  `Finset.sum_filter`, `Finset.sum_congr`, or proposition/if simplification;
  do not pivot to empirical-mean construction, Hoeffding, filtration, or final
  ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is the next selected leaf;
  it is compiled locally below.

`ETC-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is compiled locally:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`, consuming
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.
- Intended proof route: rewrite the pull count at horizon
  `spec.explorationPulls * K` to `spec.explorationPulls`, then close with
  `hexplorationPulls_pos`.
- Regularity contracts: `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and
  `hexplorationPulls_pos : 0 < spec.explorationPulls`; no measure, empirical
  means, Nat/Rat/Real denominator casts, probability, concentration,
  filtration, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_filtered_sum_pairwise_tail_response_2026-06-30.md`;
  local declaration is
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos`.
- Status: project-local compiled deterministic trace-count support leaf.
- Failure policy: if a future strengthened form fails, only inspect the exact
  count theorem or the narrower pure exploration positivity route; do not
  pivot to empirical-mean construction, Hoeffding, filtration, or final ETC
  theorem work in the same batch.

Current boundary after this leaf:

- `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is the next selected
  leaf; it is compiled locally below.

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-POS` is compiled locally:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`, consuming
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos` and the existing
  Nat-to-Rat cast support available in the import chain.
- Intended proof route: obtain the compiled Nat positivity theorem as `hnat`,
  then close by `exact_mod_cast hnat`.
- Regularity contracts: `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and
  `hexplorationPulls_pos : 0 < spec.explorationPulls`; no measure, empirical
  means, nonzero denominator corollary, probability, concentration,
  filtration, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_exploration_pulls_pos_response_2026-06-30.md`;
  local declaration is
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos`.
- Status: project-local compiled Rat denominator adapter.
- Failure policy: if a future strengthened form fails, only inspect the cast
  transport or local Rat import chain; do not pivot to empirical-mean
  construction, Hoeffding, filtration, or final ETC theorem work in the same
  batch.

Current boundary after this leaf:

- `ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` is the next
  selected leaf; it is compiled locally below.

`ETC-RATCAST-ACTION-WITH-COMMIT-EXPLORATION-PULLS-NE-ZERO` is compiled locally:

```lean
theorem ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`, consuming
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos` and
  `ne_of_gt`.
- Intended proof route: obtain the compiled Rat positivity theorem as `hpos`,
  then close by `ne_of_gt hpos`.
- Regularity contracts: `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and
  `hexplorationPulls_pos : 0 < spec.explorationPulls`; no measure, empirical
  means, division API, probability, concentration, filtration, or final theorem
  facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_ratcast_exploration_pulls_pos_response_2026-06-30.md`;
  local declaration is
  `ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero`.
- Status: project-local compiled Rat nonzero-denominator adapter.
- Failure policy: if a future strengthened form fails, only inspect nonzero
  elaboration; do not pivot to empirical-mean construction, Hoeffding,
  filtration, or final ETC theorem work in the same batch.

Current boundary after this leaf:

- Extended Pro selected
  `ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION`; it is compiled locally below.

`ETC-EMP-MEAN-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally:

```lean
def ETC.empMeanAtExploration
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) : Rat

theorem ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a : Fin K) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMean`, importing
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Intended proof route: unfold the deterministic empirical mean and rewrite
  the denominator with
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.
- Regularity contracts: `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm a : Fin K`, and `reward : RewardTrace Rat`; no
  `hexplorationPulls_pos` is needed for the rewrite because Rat division is
  total.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_ratcast_ne_zero_response_2026-06-30.md`;
  local declarations are `ETC.empMeanAtExploration` and
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`.
- Status: project-local compiled deterministic empirical-mean API.
- Failure policy: if a future strengthened form fails, only inspect the
  denominator rewrite or namespace/import surface; do not pivot to argmax,
  empirical-mean measurability, Hoeffding, filtration, or final ETC theorem
  work in the same batch.

Current boundary after this leaf:

- Extended Pro selected
  `ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION`; it is compiled
  locally below.

`ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` is compiled locally:

```lean
theorem ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : RewardTrace Rat) (a b : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.empMeanAtExploration spec commitArm reward b <=
      ETC.empMeanAtExploration spec commitArm reward a ↔
    sumRewards (ETC.actionWithCommit spec commitArm) reward b
        (spec.explorationPulls * K) <=
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
        (spec.explorationPulls * K)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMean`, importing
  `Mathlib.Algebra.Order.Field.Rat` and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Intended proof route: rewrite both empirical means with
  `ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls`, cast
  `0 < spec.explorationPulls` to a positive `Rat` denominator, and apply
  `div_le_div_iff_of_pos_right`.
- Regularity contracts: `{K : Nat}`, `spec : ETC.Spec K`,
  `commitArm : Fin K`, `reward : RewardTrace Rat`, `a b : Fin K`, and
  `0 < spec.explorationPulls`; no `Measure`, measurability, concentration,
  independence, filtration, or final ETC theorem facts.
- Retrieval evidence: local declaration is
  `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`;
  it consumes the compiled empirical-mean denominator rewrite and Mathlib's
  ordered-field division comparison lemma.
- Status: project-local compiled deterministic algebra leaf.
- Failure policy: if a future strengthened form fails, inspect only the
  denominator positivity cast, the two rewrites, or the comparison direction;
  do not pivot to Hoeffding, sub-Gaussian tails, filtration, or final ETC
  theorem work in the same batch.

`ETC-MEASURABLE-SUMREWARDS-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally:

```lean
theorem ETC.measurable_sumRewards_actionWithCommit_exploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `BanditRLProof.MeasurableLocalQuantities`,
  `ETC.actionWithCommit`, and `measurable_sumRewards`.
- Intended proof route: instantiate `measurable_sumRewards` with the constant
  stochastic action trace
  `fun _ : Omega => ETC.actionWithCommit spec commitArm`; discharge action
  coordinate measurability by `measurable_const`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `[MeasurableSpace Rat]`, `[MeasurableAdd₂ Rat]`, stochastic
  `reward : Omega -> RewardTrace Rat`, and timewise reward-coordinate
  measurability.  No `Measure`, `MeasurableDiv`, division contract,
  empirical-mean measurability theorem, argmax, concentration, filtration, or
  final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_empmean_definition_response_2026-06-30.md`;
  local declaration is
  `ETC.measurable_sumRewards_actionWithCommit_exploration`.
- Status: project-local compiled numerator-measurability bridge.
- Failure policy: if a future strengthened form fails, only inspect
  `measurable_sumRewards`, imports, or the constant-action trace; do not pivot
  to division measurability, argmax wiring, Hoeffding, filtration, or final ETC
  theorem work in the same batch.

Current boundary after this leaf:

- Extended Pro selected
  `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST`; it is
  compiled locally below.

`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION-OF-DIV-CONST` is
compiled locally:

```lean
theorem ETC.measurable_empMeanAtExploration_of_measurable_div_const
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `ETC.empMeanAtExploration`,
  `ETC.measurable_sumRewards_actionWithCommit_exploration`, and the local
  `sumRewards`/`pullCount` APIs.
- Intended proof route: use the compiled numerator-measurability bridge for
  `sumRewards`, compose it with the explicit
  `forall c : Rat, Measurable (fun x : Rat => x / c)` contract, then close by
  unfolding `ETC.empMeanAtExploration`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `[MeasurableSpace Rat]`, `[MeasurableAdd₂ Rat]`, stochastic
  `reward : Omega -> RewardTrace Rat`, timewise reward-coordinate
  measurability, and explicit Rat division-by-constant measurability.  No
  `Measure`, Mathlib/Rat division import decision, argmax, concentration,
  filtration, or final theorem facts.
- Retrieval evidence: Extended Pro chose Candidate A in
  `reports/extended_pro_after_empmean_numerator_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.measurable_empMeanAtExploration_of_measurable_div_const`.
- Status: project-local compiled full empirical-mean measurability wrapper.
- Failure policy: if a future strengthened form fails, only inspect the
  division-by-constant contract, numerator bridge, imports, or the definitional
  unfolding; do not pivot to Mathlib division imports, argmax wiring,
  Hoeffding, filtration, or final ETC theorem work in the same batch.

Current boundary after this leaf:

- Extended Pro selected
  `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON`; it is compiled locally
  below.

`RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` is compiled locally:

```lean
theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c)
```

- Local APIs/imports:
  `BanditRLProof.RatMeasurability`, importing
  `Mathlib.Data.Rat.Encodable` and
  `Mathlib.MeasureTheory.MeasurableSpace.Basic`.
- Intended proof route: use countability of `Rat` and
  `measurable_of_countable` to prove measurability of division by a fixed
  rational.
- Regularity contracts: `[MeasurableSpace Rat]` and
  `[MeasurableSingletonClass Rat]`.  The theorem deliberately does not claim
  this under only an arbitrary measurable space on `Rat`.
- Retrieval evidence: Extended Pro chose the corrected Candidate A in
  `reports/extended_pro_after_empmean_div_const_response_2026-06-30.md`;
  local declaration is `measurable_rat_div_const`.
- Status: project-local compiled import-route wrapper.
- Failure policy: if a future strengthened form fails, only inspect
  `Mathlib.Data.Rat.Encodable`, `measurable_of_countable`, and the
  `[MeasurableSingletonClass Rat]` contract; do not pivot to argmax wiring,
  Hoeffding, filtration, or final ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally
  below.

`ETC-MEASURABLE-EMPMEAN-ACTION-WITH-COMMIT-EXPLORATION` is compiled locally:

```lean
theorem ETC.measurable_empMeanAtExploration
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `ETC.measurable_empMeanAtExploration_of_measurable_div_const` and
  `measurable_rat_div_const`.
- Intended proof route: instantiate the explicit-division empirical-mean
  theorem with `hdiv_const := measurable_rat_div_const`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `[MeasurableSpace Rat]`, `[MeasurableSingletonClass Rat]`,
  `[MeasurableAdd₂ Rat]`, stochastic `reward : Omega -> RewardTrace Rat`, and
  timewise reward-coordinate measurability.  No `Measure`, argmax,
  concentration, filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: this is the direct follow-up selected after
  `reports/extended_pro_after_empmean_div_const_response_2026-06-30.md`;
  local declaration is `ETC.measurable_empMeanAtExploration`.
- Status: project-local compiled empirical-mean measurability wrapper.
- Failure policy: if a future strengthened form fails, only inspect the Rat
  measurable-singleton contract, explicit-division theorem, and imports; do
  not pivot to argmax wiring, Hoeffding, filtration, or final ETC theorem work
  in the same batch.

Current boundary after this leaf:

- `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` is compiled locally
  below.

`ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` is compiled locally:

```lean
theorem ETC.measurable_empMeanAtExploration_coordinates
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    forall a : Fin K,
      Measurable (fun omega : Omega =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec commitArm (reward omega) b) a)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`, consuming
  `ETC.measurable_empMeanAtExploration`.
- Intended proof route: introduce `a` and close by
  `ETC.measurable_empMeanAtExploration spec commitArm a reward hreward`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `[MeasurableSpace Rat]`, `[MeasurableSingletonClass Rat]`,
  `[MeasurableAdd₂ Rat]`, stochastic `reward : Omega -> RewardTrace Rat`, and
  timewise reward-coordinate measurability.  No `Measure`, commit oracle,
  argmax proof, concentration, filtration, conditional expectation, or final
  theorem facts.
- Retrieval evidence: Extended Pro selected
  `ETC-MEASURABLE-EMPMEAN-AT-EXPLORATION-COORDINATES` in
  `reports/extended_pro_after_empmean_meas_response_2026-06-30.md`; local
  declaration is `ETC.measurable_empMeanAtExploration_coordinates`.
- Status: project-local compiled empirical-mean coordinate wrapper.
- Failure policy: if a future strengthened form fails, only inspect the
  already compiled no-`hdiv_const` empirical-mean theorem and its imports; do
  not pivot to Hoeffding, filtration, or final ETC theorem work in the same
  batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` is compiled locally below.

`ETC-COMMIT-ORACLE-ARGMAX-CONSUMER` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.CommitOracle` from `BanditRLProof.Algorithms.ETC` and
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm`.
- Intended proof route: instantiate the existing wrong-commit set-inclusion
  theorem with `commitArm omega := oracle.choose (empMean omega)` and derive
  its `hcommit_argmax` argument from `hchoose_argmax`.
- Regularity contracts: `model : FiniteBanditModel K`,
  `oracle : ETC.CommitOracle K`, `empMean : Omega -> Fin K -> Rat`, and the
  explicit abstract argmax certificate
  `forall scores a, scores a <= scores (oracle.choose scores)`.  No `Measure`,
  measurability, concrete oracle construction, oracle optimality proof,
  concentration, filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: Extended Pro recommended this as the next plausible leaf
  in `reports/extended_pro_after_empmean_meas_response_2026-06-30.md`; local
  declaration is
  `ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle`.
- Status: project-local compiled event-reduction consumer.
- Failure policy: if a future strengthened form fails, inspect only the
  abstract oracle contract and the existing set-inclusion theorem; do not
  pivot to Hoeffding, filtration, or final ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-PROB-WRAPPER` is compiled locally below.

`ETC-COMMIT-ORACLE-PROB-WRAPPER` is compiled locally:

```lean
theorem ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
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
    (Finset.univ : Finset (Fin K)).sum tail
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail` and
  `ETC.CommitOracle`.
- Intended proof route: specialize the existing arbitrary-commit-arm
  pairwise-tail consumer with
  `commitArm omega := oracle.choose (empMean omega)` and derive
  `hcommit_argmax` from `hchoose_argmax`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, `tail : Fin K -> ENNReal`, abstract
  oracle argmax certificate, and abstract non-best pairwise-tail assumptions.
  No probability instance, event measurability, concrete oracle construction,
  actual concentration theorem, filtration, or final ETC theorem facts.
- Retrieval evidence: Extended Pro selected Candidate A in
  `reports/extended_pro_after_commit_oracle_argmax_response_2026-06-30.md`;
  local declaration is `ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail`.
- Status: project-local compiled oracle-specialized probability wrapper.
- Failure policy: if a future strengthened form fails, inspect only the
  existing arbitrary commit-arm pairwise-tail theorem and the oracle argmax
  certificate shape; do not reprove finite unions or pivot to concentration,
  filtration, or final ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` is compiled locally below.

`ETC-COMMIT-ORACLE-FILTERED-SUM-PAIRWISE-TAIL` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail` and
  `ETC.CommitOracle`.
- Intended proof route: specialize the existing arbitrary-commit-arm filtered
  pairwise-tail consumer with
  `commitArm omega := oracle.choose (empMean omega)` and derive
  `hcommit_argmax` from `hchoose_argmax`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, `tail : Fin K -> ENNReal`, abstract
  oracle argmax certificate, and abstract non-best pairwise-tail assumptions.
  No probability instance, event measurability, concrete oracle construction,
  actual concentration theorem, filtration, or final ETC theorem facts.
- Retrieval evidence: Extended Pro selected Candidate B in
  `reports/extended_pro_after_commit_oracle_prob_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail`.
- Status: project-local compiled oracle-specialized filtered-sum probability
  wrapper.
- Failure policy: if a future strengthened form fails, inspect only the
  existing arbitrary filtered theorem and the oracle argmax certificate shape;
  do not add oracle measurability, construct a concrete oracle, backfill the
  if-zeroed nonbest wrapper, or pivot to concentration, filtration, or final
  ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` is compiled locally below.

`ETC-COMMIT-ORACLE-NONBEST-PAIRWISE-TAIL` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail` and
  `ETC.CommitOracle`.
- Intended proof route: specialize the existing arbitrary-commit-arm if-zeroed
  pairwise-tail consumer with
  `commitArm omega := oracle.choose (empMean omega)` and derive
  `hcommit_argmax` from `hchoose_argmax`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `model : FiniteBanditModel K`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, `tail : Fin K -> ENNReal`, abstract
  oracle argmax certificate, and abstract non-best pairwise-tail assumptions.
  No probability instance, event measurability, concrete oracle construction,
  actual concentration theorem, filtration, or final ETC theorem facts.
- Retrieval evidence: Extended Pro selected Candidate A in
  `reports/extended_pro_after_commit_oracle_filtered_response_2026-06-30.md`;
  local declaration is
  `ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail`.
- Status: project-local compiled oracle-specialized if-zeroed probability
  wrapper.
- Failure policy: if a future strengthened form fails, inspect only the
  existing arbitrary if-zeroed theorem and the oracle argmax certificate shape;
  do not add oracle measurability, construct a concrete oracle, prove new
  finite-sum normalizations, or pivot to concentration, filtration, or final
  ETC theorem work in the same batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` is compiled locally below.

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.measurableSet_commitArm_ne_bestArm` and `ETC.CommitOracle`.
- Intended proof route: specialize the existing arbitrary commit-arm
  wrong-event measurability lemma with
  `commitArm omega := oracle.choose (empMean omega)` and pass the direct
  composed measurability assumption as `hmeas_commit`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `model : FiniteBanditModel K`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, and
  `Measurable (fun omega => oracle.choose (empMean omega))`.  No measure,
  probability instance, empirical-mean measurability proof, concrete oracle
  construction, actual concentration theorem, filtration, or final ETC theorem
  facts.
- Retrieval evidence: Extended Pro selected Candidate A in
  `reports/extended_pro_after_commit_oracle_nonbest_response_2026-06-30.md`;
  local declaration is `ETC.measurableSet_commitOracle_ne_bestArm`.
- Status: project-local compiled oracle-selected wrong-event measurability
  wrapper.
- Failure policy: if a future strengthened form fails, keep this leaf as the
  direct-composed-measurability wrapper; do not smuggle in arbitrary oracle
  measurability, construct a concrete argmax oracle, prove empirical-mean
  measurability, or pivot to concentration, filtration, or final ETC theorem
  work in the same batch.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` is compiled locally below.

`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-BRIDGE` is compiled locally:

```lean
theorem ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)]
    [MeasurableSpace (Fin K -> Rat)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_emp :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega))
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.CommitOracle` and Mathlib's `measurable_of_countable`.
- Intended proof route: prove
  `Measurable (fun score : Fin K -> Rat => oracle.choose score)` by
  `measurable_of_countable _`, then compose with the empirical-mean vector
  measurability assumption.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSpace (Fin K -> Rat)]`,
  `[MeasurableSingletonClass (Fin K -> Rat)]`,
  `[Countable (Fin K -> Rat)]`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, and
  `Measurable (fun omega => (empMean omega : Fin K -> Rat))`.  No concrete
  oracle construction, argmax correctness proof, pairwise concentration,
  filtration, or final ETC theorem facts.
- Retrieval evidence: Extended Pro selected
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-ROUTE-CARD` in
  `reports/extended_pro_after_commit_oracle_event_meas_response_2026-06-30.md`
  and identified this project-local compiled candidate; local declaration is
  `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.
- Status: project-local compiled Mathlib-backed oracle-choice measurability
  bridge.
- Failure policy: keep the countable `Rat` score-vector assumptions explicit;
  do not weaken back to assuming `hmeas_choose`, do not construct a concrete
  argmax oracle, and do not pivot to concentration, filtration, or final ETC
  theorem work in the same batch.

Current boundary after this leaf:

- `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` is compiled locally below.

`ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  Mathlib's Pi measurable-space API `measurable_pi_lambda`.
- Intended proof route: keep the function type on the standard Pi
  measurable-space instance induced by `[MeasurableSpace Rat]`; apply
  `measurable_pi_lambda _ hmeas_coord`.
- Regularity contracts: `[MeasurableSpace Omega]`, `[MeasurableSpace Rat]`,
  `empMean : Omega -> Fin K -> Rat`, and coordinate measurability
  `forall a, Measurable (fun omega => empMean omega a)`.  Do not assume an
  arbitrary `[MeasurableSpace (Fin K -> Rat)]`; no oracle construction,
  argmax correctness, pairwise concentration, filtration, or final ETC theorem
  facts.
- Retrieval evidence: Extended Pro selected
  `ETC-EMPMEAN-VECTOR-MEASURABILITY-BRIDGE` in
  `reports/extended_pro_after_commit_oracle_choice_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.measurable_empMeanVector_of_forall_measurable`.
- Status: project-local compiled Mathlib Pi-space empirical-mean
  coordinate-to-vector measurability bridge.
- Failure policy: if elaboration of the annotated target is unstable, prefer
  the lambda-expanded target
  `Measurable (fun omega : Omega => fun a : Fin K => empMean omega a)`;
  search for `measurable_pi_iff` if `measurable_pi_lambda` is renamed.  Do not
  replace this leaf with concrete argmax construction, concentration,
  filtration, or final ETC work.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` is compiled locally
  below.

`ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` is compiled locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.measurable_empMeanVector_of_forall_measurable` and
  `ETC.measurable_commitOracle_choose_of_measurable_empMeanVector`.
- Intended proof route: package coordinatewise empirical-mean measurability
  into vector-valued measurability, then feed that into the existing
  countable score-vector oracle-choice bridge.
- Regularity contracts: `[MeasurableSpace Omega]`, `[MeasurableSpace Rat]`,
  `[MeasurableSpace (Fin K)]`,
  `[MeasurableSingletonClass (Fin K -> Rat)]`,
  `[Countable (Fin K -> Rat)]`, `oracle : ETC.CommitOracle K`,
  `empMean : Omega -> Fin K -> Rat`, and coordinate measurability.  Do not add
  an arbitrary local `[MeasurableSpace (Fin K -> Rat)]`; no concrete oracle
  construction, argmax correctness, probability, concentration, filtration, or
  final ETC theorem facts.
- Retrieval evidence: Extended Pro selected
  `ETC-COMMIT-ORACLE-CHOICE-MEASURABILITY-OF-COORDINATES` in
  `reports/extended_pro_after_empmean_vector_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean`.
- Status: project-local compiled coordinatewise empirical-mean-to-oracle-choice
  measurability composition wrapper.
- Failure policy: mirror the existing oracle-choice bridge's typeclass
  telescope while letting `[MeasurableSpace Rat]` synthesize the Pi measurable
  space.  Do not unfold `oracle.choose`, construct a concrete argmax oracle, or
  pivot to probability, concentration, filtration, or final theorem work.

Current boundary after this leaf:

- `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` is compiled
  locally below.

`ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` is compiled
locally:

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

- Local APIs/imports: `BanditRLProof.Algorithms.ETCMeasurability`, consuming
  `ETC.measurable_commitOracle_choose_of_forall_measurable_empMean` and
  `ETC.measurableSet_commitOracle_ne_bestArm`.
- Intended proof route: derive composed oracle-choice measurability from
  coordinatewise empirical-mean measurability, then feed it into the existing
  oracle-selected wrong-event measurability wrapper.
- Regularity contracts: `[MeasurableSpace Omega]`, `[MeasurableSpace Rat]`,
  `[MeasurableSpace (Fin K)]`, `[MeasurableSingletonClass (Fin K)]`,
  `[MeasurableSingletonClass (Fin K -> Rat)]`,
  `[Countable (Fin K -> Rat)]`, `model : FiniteBanditModel K`,
  `oracle : ETC.CommitOracle K`, `empMean : Omega -> Fin K -> Rat`, and
  coordinate measurability.  No probability measure, concrete oracle
  construction, argmax correctness, concentration, filtration, or final ETC
  theorem facts.
- Retrieval evidence: Extended Pro selected
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES` in
  `reports/extended_pro_after_oracle_choice_coord_meas_response_2026-06-30.md`;
  local declaration is
  `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`.
- Status: project-local compiled coordinatewise empirical-mean-to-oracle
  wrong-event measurability composition wrapper.
- Failure policy: match the target of
  `ETC.measurableSet_commitOracle_ne_bestArm`; use `simpa [Ne]` only if a
  future wrapper switches to `!=` notation.  Do not add arbitrary measurable
  spaces, construct argmax oracles, or pivot to concentration/final theorem
  work in the same batch.

Current boundary after this leaf:

- Use the local two-agent review workflow before choosing the next broad
  post-coordinate-wrong-event route or leaf.  The current recorded local review
  is
  `reports/local_dual_review_after_oracle_wrong_event_coord_meas_decision_2026-06-30.md`;
  it selected `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX`, which is now compiled
  locally in `BanditRLProof.Algorithms.ETCArgmaxOracle`.
  The follow-up local dual review in
  `reports/local_dual_review_after_concrete_argmax_decision_2026-06-30.md`
  selected `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL`, which is
  also compiled locally.  Do not start actual pairwise concentration,
  adaptedness/conditional reward-law work, or a final theorem in the same
  batch.
  `ETC-PAIRWISE-TAIL-CONTRACT-SURFACE` and
  `ETC-EMP-MEAN-COMPARISON-AS-FINITE-SUM` are now compiled locally.

`TAIL-HOEFFDING-BOUNDED` is compiled locally:

```lean
noncomputable def Concentration.intervalVarianceProxy (lo hi : Real) : NNReal

theorem Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega -> Real} {lo hi mean : Real}
    (hmeas : AEMeasurable X mu)
    (hbound : Filter.Eventually
      (fun omega => Set.Icc lo hi (X omega)) (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu X = mean) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega => X omega - mean)
      (Concentration.intervalVarianceProxy lo hi) mu
```

- Local APIs/imports: `BanditRLProof.ConcentrationSubGaussian`, importing
  `Mathlib.Probability.Moments.SubGaussian`.
- Intended proof route: apply Mathlib
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` to obtain the centered
  witness around `integral mu X`, then rewrite the center with the exact mean
  identity using `HasSubgaussianMGF.congr`.
- Regularity contracts: `[MeasurableSpace Omega]`, probability measure `mu`,
  real random variable `X`, `AEMeasurable X mu`, an a.s. interval bound
  `Set.Icc lo hi (X omega)`, and exact mean identity
  `MeasureTheory.integral mu X = mean`.  No independence, finite-sum tail
  assembly, ETC reward law, filtration, conditional expectation, or final
  theorem facts.
- Retrieval evidence: Mathlib module
  `Mathlib.Probability.Moments.SubGaussian`, declaration
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, and local declarations
  `Concentration.intervalVarianceProxy` and
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`.
- Status: project-local compiled Mathlib import-wrapper leaf.
- Failure policy: if downstream use needs an event-probability bound, compose
  this MGF source with `TAIL-SUBGAUSS-SUM` or the existing ETC pairwise-tail
  producers.  Do not treat this wrapper alone as a final Hoeffding regret
  theorem or as a proof of independence, reward-law construction, filtration,
  conditional expectation, UCB, Thompson sampling, EXP3/Tsallis/OFUL/RL, or a
  final ETC theorem.

Current boundary after this leaf:

- `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean` now
  reuses the generic `Concentration` wrapper while preserving the ETC-shaped
  reward/arm/time interface.  The actual finite-sum/event tail remains handled
  by the sub-Gaussian tail producer leaves below.

`TAIL-VARIANCE-ROBUST` is compiled locally:

```lean
theorem Concentration.variance_chebyshev_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {X : Omega -> Real}
    (hX : MemLp X 2 mu)
    {eps : Real} (heps : 0 < eps) :
    mu {omega | eps <= |X omega - integral mu X|} <=
      ENNReal.ofReal (ProbabilityTheory.variance X mu / eps ^ 2)

theorem Concentration.evariance_chebyshev_tail
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega)
    {X : Omega -> Real}
    (hX : AEStronglyMeasurable X mu)
    {eps : NNReal} (heps : Ne eps 0) :
    mu {omega | (eps : Real) <= |X omega - integral mu X|} <=
      ProbabilityTheory.evariance X mu / (eps : ENNReal) ^ 2

theorem Concentration.variance_sum_of_pairwise_indep
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real} {s : Finset Idx}
    (h_mem : forall i : Idx, Membership.mem s i -> MemLp (X i) 2 mu)
    (h_pairwise :
      Set.Pairwise ((s : Finset Idx) : Set Idx)
        (fun i j => ProbabilityTheory.IndepFun (X i) (X j) mu)) :
    ProbabilityTheory.variance (Finset.sum s X) mu =
      Finset.sum s (fun i => ProbabilityTheory.variance (X i) mu)
```

- Local APIs/imports: `BanditRLProof.ConcentrationVariance`, importing
  `Mathlib.Probability.Moments.Variance`.
- Intended proof route: apply Mathlib
  `ProbabilityTheory.meas_ge_le_variance_div_sq`,
  `ProbabilityTheory.meas_ge_le_evariance_div_sq`, and
  `ProbabilityTheory.IndepFun.variance_sum` directly, preserving their
  assumptions in project-local names.
- Regularity contracts: real Chebyshev route needs `[MeasurableSpace Omega]`,
  finite measure `mu`, `MemLp X 2 mu`, and `0 < eps`; extended-real route
  needs `AEStronglyMeasurable X mu` and nonzero `eps : NNReal`; finite-sum
  route needs per-summand `MemLp` on an explicit `Finset` plus pairwise
  independence over the coerced support set.
- Retrieval evidence: Mathlib module
  `Mathlib.Probability.Moments.Variance`, declarations
  `ProbabilityTheory.meas_ge_le_variance_div_sq`,
  `ProbabilityTheory.meas_ge_le_evariance_div_sq`, and
  `ProbabilityTheory.IndepFun.variance_sum`; local declarations are
  `Concentration.variance_chebyshev_tail`,
  `Concentration.evariance_chebyshev_tail`, and
  `Concentration.variance_sum_of_pairwise_indep`.
- Status: project-local compiled Mathlib import-wrapper leaf.
- Failure policy: use this only as the finite-variance/Chebyshev foundation.
  Do not treat it as a median-of-means, truncation, robust-UCB, empirical-mean
  specialization, reward-law construction, filtration theorem, or final bandit
  regret proof.  Split any such downstream use into separate leaves.

Current boundary after this leaf:

- `TAIL-VARIANCE-ROBUST` now has a minimal compiled Chebyshev/variance
  foundation.  Robust mean estimators and theorem-specific heavy-tailed bandit
  concentration remain future leaves.

`TAIL-SUBGAUSS-SUM` is compiled locally:

```lean
theorem Concentration.subGaussian_sum_tail_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= s.sum (fun i => X i omega)} <=
      Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))
```

- Local APIs/imports: `BanditRLProof.ConcentrationSubGaussian`, importing
  `Mathlib.Probability.Moments.SubGaussian`.
- Intended proof route: apply Mathlib
  `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`
  directly.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  finite index set `s : Finset Idx`, independent summands
  `ProbabilityTheory.iIndepFun X mu`, per-summand
  `ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu`, and `0 <= eps`.
  No ETC reward law, empirical-mean specialization, `ENNReal` tail conversion,
  filtration, conditional expectation, or final theorem facts.
- Retrieval evidence: Mathlib module
  `Mathlib.Probability.Moments.SubGaussian` and declaration
  `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`;
  local declaration is
  `Concentration.subGaussian_sum_tail_of_iIndepFun`.
- Status: project-local compiled Mathlib import-wrapper leaf.
- Failure policy: if downstream specialization fails, split only
  ETC reward-difference specialization leaves; do not pivot to full Hoeffding,
  filtration/history, conditional expectation, UCB, Thompson sampling,
  EXP3/Tsallis/OFUL/RL, or final ETC regret in the same batch.

Current boundary after this leaf:

- `TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is compiled locally below.

`TAIL-SUBGAUSS-DIFF-SUM-IMPORT` is compiled locally:

```lean
theorem Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {Idx : Type v} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= s.sum (fun i => X i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real))))
```

- Local APIs/imports: `BanditRLProof.ConcentrationSubGaussian`, consuming
  `Concentration.subGaussian_sum_tail_of_iIndepFun`, `Measure.real`,
  `measure_ne_top`, and `ENNReal.le_ofReal_iff_toReal_le`.
- Intended proof route: apply the real-valued sub-Gaussian finite-sum tail
  wrapper; rewrite `mu.real event` to `(mu event).toReal`; convert the bound to
  `mu event <= ENNReal.ofReal ...` using finite-measure non-topness and
  positivity of `Real.exp`.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu : Measure Omega`,
  `[IsFiniteMeasure mu]`, abstract real-valued summands
  `X : Idx -> Omega -> Real`, `iIndepFun X mu`, per-summand
  `HasSubgaussianMGF`, finite index set `s`, and `0 <= eps`.  No ETC reward
  law, empirical-mean specialization, filtration, conditional expectation, or
  final theorem facts.
- Retrieval evidence: local declarations are
  `Concentration.subGaussian_sum_tail_of_iIndepFun` and
  `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`; Mathlib evidence
  is `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`,
  `Measure.real`, and `ENNReal.le_ofReal_iff_toReal_le`.
- Status: project-local compiled Mathlib import/boundary-wrapper leaf.
- Failure policy: if downstream ETC specialization fails, split only
  Rat-to-Real reward-difference shape, `sumRewards` to exploration `Finset.sum`,
  or independence transport leaves; do not pivot to concrete
  filtration/history instantiation, bounded Hoeffding, or final ETC theorem in
  the same batch.

Current boundary after this leaf:

- `TAIL-COND-SUBGAUSS` is compiled locally below.

`TAIL-COND-SUBGAUSS` is compiled locally:

```lean
theorem Concentration.condSubGaussian_sum_tail_of_stronglyAdapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : Filtration Nat mOmega}
    (h_adapted : StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))
```

- Local APIs/imports: `BanditRLProof.ConcentrationSubGaussian`, importing
  `Mathlib.Probability.Moments.SubGaussian` and exposing both the real-valued
  wrapper above and
  `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`.
- Intended proof route: apply Mathlib
  `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` directly;
  the ENNReal adapter then uses the same `Measure.real` conversion pattern as
  `TAIL-SUBGAUSS-DIFF-SUM-IMPORT`.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[StandardBorelSpace Omega]`, zero-or-probability measure `mu`,
  `Y : Nat -> Omega -> Real`, `cY : Nat -> NNReal`,
  `F : Filtration Nat mOmega`, `StronglyAdapted F Y`, unconditional
  `HasSubgaussianMGF (Y 0)`, conditional
  `HasCondSubgaussianMGF (F i) (F.le i) (Y (i + 1))` for `i < n - 1`, and
  `0 <= eps`.  No full policy predictability, reward-law instantiation,
  empirical means, or final theorem facts.
- Retrieval evidence: Mathlib declarations
  `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` and
  `ProbabilityTheory.HasCondSubgaussianMGF`; local declarations are
  `Concentration.condSubGaussian_sum_tail_of_stronglyAdapted` and
  `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`.
- Status: project-local compiled Mathlib import/boundary-wrapper leaf.
- Failure policy: if adaptive ETC specialization fails, split only
  history-filtration construction, action/reward adaptedness, or conditional
  MGF witness leaves; do not start final adaptive ETC regret in the same batch.

Current boundary after this leaf:

- `MEAS-HISTORY` and `FILTRATION-HISTORY` are compiled locally below.

`MEAS-HISTORY` is compiled locally:

```lean
def History.FiniteActionHistory
def History.FiniteRewardHistory
def History.FiniteHistory
def History.FinitePairHistory

def History.finiteActionHistoryOfTrace
def History.finiteRewardHistoryOfTrace
def History.finiteHistoryOfTrace
def History.finitePairHistoryOfTrace

@[simp] theorem History.finiteActionHistoryOfTrace_apply
@[simp] theorem History.finiteRewardHistoryOfTrace_apply
@[simp] theorem History.finiteHistoryOfTrace_fst
@[simp] theorem History.finiteHistoryOfTrace_snd
@[simp] theorem History.finitePairHistoryOfTrace_apply
def History.pairHistoryRewardProjection
@[simp] theorem History.pairHistoryRewardProjection_apply
@[simp] theorem History.pairHistoryRewardProjection_finitePairHistoryOfTrace

theorem History.measurable_finiteActionHistory_eval
theorem History.measurable_finiteRewardHistory_eval
theorem History.measurable_finiteHistory_action_eval
theorem History.measurable_finiteHistory_reward_eval
theorem History.measurable_pairHistoryRewardProjection
theorem History.measurable_finitePairHistoryOfTrace

theorem History.measurable_finiteActionHistoryOfTrace
theorem History.measurable_finiteRewardHistoryOfTrace
theorem History.measurable_finiteHistoryOfTrace
```

- Exact Lean-facing statement: finite action histories, finite reward
  histories, and paired finite histories are explicit Pi/product objects over
  `Finset.Iic t`; trace-restriction maps from full traces into those finite
  objects are measurable when every action and reward coordinate is
  measurable; pair-coordinate trace prefixes are also explicit finite history
  objects; coordinate projections from the finite objects are measurable; the
  reward projection from finite `(Action, Reward)` pair histories is a
  measurable map into finite reward histories.
- Local APIs/imports: `BanditRLProof.HistoryFiltration`, importing
  `Mathlib.Probability.Process.Filtration` and
  `BanditRLProof.MeasureFoundation`.  The proof surface uses `Finset.Iic`,
  `measurable_pi_apply`, `measurable_pi_lambda`, and product measurability via
  `Measurable.prod`.
- Intended proof route: represent the finite prefix as a dependent function
  over `Finset.Iic t`, prove coordinate measurability by Pi-space projection,
  prove trace restriction measurability by `measurable_pi_lambda` from the
  timewise measurable trace coordinates, package action and reward
  restrictions with product measurability, prove pair-coordinate trace-prefix
  measurability by coordinatewise product measurability, and prove
  pair-history reward projection measurability by `measurable_pi_lambda` plus
  `measurable_snd`.
- Regularity contracts: measurable action and reward spaces are required for
  finite product objects and coordinate projections.  Trace-restriction
  measurability also requires `[MeasurableSpace Omega]` plus timewise
  measurability of the full action and reward traces.  No singleton,
  countability, filtration, kernel, conditional expectation, or final theorem
  assumptions are included in this leaf.
- Retrieval evidence: local card
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`; Mathlib routes
  `MLIB-MEASURE-INTEGRAL` and `MLIB-PROBABILITY-KERNEL`; local declarations
  are the `History.Finite*`, `History.finite*OfTrace`, and
  `History.measurable_finite*` declarations listed above.
- Status: project-local compiled finite-history product-measurability surface.
- Failure policy: do not claim filtration generation, policy predictability,
  kernel-law assembly, conditional reward-law transfer, posterior kernels,
  conditional expectation identities, or final adaptive ETC regret from this
  leaf.  Those remain separate leaves or theorem cards.

`FILTRATION-HISTORY` is compiled locally:

```lean
def History.historyFiltration
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Filtration Nat mOmega
```

The module also exposes:

```lean
def History.historyGenerators
theorem History.historyGenerators_mono
def History.historyMeasurableSpace
theorem History.historyMeasurableSpace_mono
theorem History.historyMeasurableSpace_le
theorem History.historyFiltration_apply
theorem History.measurableSet_action_mem_historyFiltration
theorem History.measurableSet_reward_mem_historyFiltration
```

- Local APIs/imports: `BanditRLProof.HistoryFiltration`, importing
  `Mathlib.Probability.Process.Filtration` and
  `BanditRLProof.MeasureFoundation`.
- Intended proof route: define the past-history generator set from singleton
  action and reward coordinate preimages with `i < t`; prove generator
  monotonicity by `lt_of_lt_of_le`; define the generated sigma-algebra with
  `MeasurableSpace.generateFrom`; construct the Mathlib `Filtration` with the
  monotonicity proof and `generateFrom_le`; expose past action/reward
  singleton-event measurability by `MeasurableSpace.measurableSet_generateFrom`.
- Regularity contracts: ambient `[MeasurableSpace Omega]`,
  singleton-measurable action and reward spaces, timewise measurable action and
  reward coordinates.  This is a discrete singleton-event history canary; it
  does not prove policy predictability, action/reward adaptedness as a process,
  conditional expectation identities, conditional MGF witnesses, kernels, or
  final adaptive ETC regret.
- Retrieval evidence: Mathlib `MeasureTheory.Filtration`,
  `MeasurableSpace.generateFrom_mono`, `MeasurableSpace.generateFrom_le`, and
  `MeasurableSpace.measurableSet_generateFrom`; local declarations listed
  above are in `BanditRLProof.HistoryFiltration`.
- Status: project-local compiled history-filtration canary.
- Failure policy: if the adaptive route fails, split only adapted-action,
  adapted-reward, or conditional reward-law witness leaves.  Do not start
  final adaptive ETC regret, UCB, Thompson/EXP3/Tsallis/OFUL/RL, or broad
  kernel work in the same batch.

Current boundary after this leaf:

- `ADAPTED-ACTION` is compiled locally as a countable/discrete
  past-coordinate measurability canary below.  It is not a full arbitrary
  policy-predictability theorem.

`ADAPTED-ACTION` is compiled locally:

```lean
theorem History.measurable_action_mem_historyFiltration_of_lt
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) :
    @Measurable Omega Action
      (History.historyFiltration action reward haction hreward t)
      inferInstance
      (fun omega => action omega i)
```

The module also exposes the reward-side companion canary:

```lean
theorem History.measurable_reward_mem_historyFiltration_of_lt
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [Countable Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) :
    @Measurable Omega Reward
      (History.historyFiltration action reward haction hreward t)
      inferInstance
      (fun omega => reward omega i)
```

- Local APIs/imports: `BanditRLProof.HistoryFiltration`, using the compiled
  `History.historyFiltration`,
  `History.measurableSet_action_mem_historyFiltration`, and
  `History.measurableSet_reward_mem_historyFiltration` declarations.
- Intended proof route: apply Mathlib `measurable_to_countable'` with the
  source measurable space explicitly set to
  `History.historyFiltration action reward haction hreward t`; discharge each
  singleton preimage with the existing generated-history singleton-event
  measurability theorem.
- Regularity contracts: ambient `[MeasurableSpace Omega]`,
  singleton-measurable action/reward spaces, countable action space for the
  action theorem, countable reward space for the companion theorem, timewise
  measurable action/reward coordinates, and `i < t`.  This proves past
  coordinate measurability in the generated history, not predictability of an
  arbitrary policy map, not kernels, not conditional expectations, and not
  conditional MGF witnesses.
- Retrieval evidence: Mathlib `measurable_to_countable'`; local declarations
  `History.historyFiltration`,
  `History.measurableSet_action_mem_historyFiltration`, and
  `History.measurableSet_reward_mem_historyFiltration`.
- Status: project-local compiled adapted-coordinate canary.
- Failure policy: if the conditional route fails after this leaf, split a
  conditional reward-law witness or a full policy-predictability theorem.  Do
  not treat this canary as a replacement for arbitrary adaptive policy
  semantics.

`MEAS-POLICY` is compiled locally:

```lean
structure Policy.MeasurablePolicy
    (State : Type u) (Action : Type v)
    [MeasurableSpace State] [MeasurableSpace Action] where
  action : State -> Action
  measurable_action : Measurable action

theorem Policy.measurable_action_of_measurable_state
    [MeasurableSpace Omega] [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action)
    (state : Omega -> State)
    (hstate : Measurable state) :
    Measurable (fun omega : Omega => policy.action (state omega))

theorem Policy.measurable_action_mem_filtration_of_measurable_state
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Policy.MeasurablePolicy State Action)
    (state : Omega -> State)
    (t : Nat)
    (hstate :
      @Measurable Omega State
        (F t) inferInstance state) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega => policy.action (state omega))

theorem Policy.measurable_action_mem_historyFiltration_of_measurable_state
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace TraceAction] [MeasurableSingletonClass TraceAction]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [MeasurableSpace State] [MeasurableSpace PolicyAction]
    (traceAction : Omega -> ActionTrace TraceAction)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => traceAction omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (policy : Policy.MeasurablePolicy State PolicyAction)
    (state : Omega -> State)
    (t : Nat)
    (hstate :
      @Measurable Omega State
        (History.historyFiltration traceAction reward haction hreward t)
        inferInstance
        state) :
    @Measurable Omega PolicyAction
      (History.historyFiltration traceAction reward haction hreward t)
      inferInstance
      (fun omega : Omega => policy.action (state omega))
```

- Local APIs/imports: `BanditRLProof.PolicyMeasurability`, importing
  `BanditRLProof.HistoryFiltration`.
- Intended proof route: package a policy action map with its Mathlib
  `Measurable` proof, then use `Measurable.comp` to compose it with a
  measurable history/context state.  The filtration and history-filtration
  variants use the same proof at the sub-sigma-algebra `F t` or
  `History.historyFiltration ... t`.
- Regularity contracts: measurable state and action spaces, a measurable
  history/context state, and a measurable policy map.  The history-filtration
  specialization additionally requires singleton-measurable trace action and
  reward spaces plus timewise coordinate measurability.
- Retrieval evidence: local declarations
  `Policy.MeasurablePolicy`,
  `Policy.measurable_action_of_measurable_state`,
  `Policy.measurable_action_mem_filtration_of_measurable_state`, and
  `Policy.measurable_action_mem_historyFiltration_of_measurable_state`;
  Mathlib route is `Measurable.comp`.
- Status: project-local compiled policy measurability/predictability surface.
- Failure policy: this leaf only proves measurability after a history/context
  state has already been supplied.  It does not construct policy kernels,
  trajectory laws, reward kernels, conditional reward laws, or final adaptive
  regret.

`POLICY-GENERATED-ACTION-TRACE-MEASURABILITY` is compiled locally:

```lean
def Policy.generatedActionTrace
    [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State) :
    Omega -> ActionTrace Action

theorem Policy.measurable_generatedActionTrace_eval_of_measurable_state
    [MeasurableSpace Omega] [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (hstate : forall t : Nat, Measurable (state t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t)

theorem Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (F t) inferInstance (state t))
    (t : Nat) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t)

theorem Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace TraceAction] [MeasurableSingletonClass TraceAction]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [MeasurableSpace State] [MeasurableSpace PolicyAction]
    (traceAction : Omega -> ActionTrace TraceAction)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => traceAction omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (policy : Policy.MeasurablePolicy State PolicyAction)
    (state : Nat -> Omega -> State)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (History.historyFiltration traceAction reward haction hreward t)
          inferInstance
          (state t))
    (t : Nat) :
    @Measurable Omega PolicyAction
      (History.historyFiltration traceAction reward haction hreward t)
      inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t)

def Policy.generatedActionTraceSucc
    [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action) :
    Omega -> ActionTrace Action

theorem Policy.generatedActionTraceSucc_succ_eq
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action)
    (t : Nat) :
    (fun omega : Omega =>
      (Policy.generatedActionTraceSucc policy state defaultAction omega)
        (t + 1)) =
    (fun omega : Omega => (policy t).action (state t omega))

theorem Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (F t) inferInstance (state t))
    (t : Nat) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTraceSucc policy state defaultAction omega)
          (t + 1))
```

- Local APIs/imports: `BanditRLProof.PolicyMeasurability`, reusing
  `Policy.MeasurablePolicy`,
  `Policy.measurable_action_of_measurable_state`,
  `Policy.measurable_action_mem_filtration_of_measurable_state`, and
  `Policy.measurable_action_mem_historyFiltration_of_measurable_state`.
- Intended proof route: define the generated action trace pointwise by applying
  `policy.action` to the time-indexed state coordinate, then reuse the
  single-time policy/state composition lemmas at each `t`.  For the shifted
  time-indexed trace, define coordinate `t + 1` using `policy t` and prove the
  function-level equality plus predictable-coordinate measurability directly.
- Regularity contracts: measurable state/action spaces, a measurable policy,
  and a time-indexed state process whose coordinates are measurable either
  ambiently, against `F t`, or against the generated history filtration at
  time `t`.
- Retrieval evidence: local declarations
  `Policy.generatedActionTrace`,
  `Policy.measurable_generatedActionTrace_eval_of_measurable_state`,
  `Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state`,
  and
  `Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state`,
  plus `Policy.generatedActionTraceSucc`,
  `Policy.generatedActionTraceSucc_succ_eq`, and
  `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`.
- Status: project-local compiled policy-generated action-trace
  coordinate-measurability surface.
- Failure policy: this is a `KERNEL-POLICY-BIND` precursor only.  It does not
  construct reward kernels, bind kernels, trajectory measures, conditional
  reward laws, or final adaptive regret.

`KERNEL-REWARD` is compiled locally:

```lean
structure RewardKernel.MarkovRewardKernel
    (Index : Type u) (Reward : Type v)
    [MeasurableSpace Index] [MeasurableSpace Reward] where
  kernel : ProbabilityTheory.Kernel Index Reward
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel kernel

def RewardKernel.ofKernel
    (kernel : ProbabilityTheory.Kernel Index Reward)
    (hkernel : ProbabilityTheory.IsMarkovKernel kernel) :
    RewardKernel.MarkovRewardKernel Index Reward

theorem RewardKernel.measurable_apply_of_measurable_index
    [MeasurableSpace Omega]
    (rewardKernel : RewardKernel.MarkovRewardKernel Index Reward)
    (index : Omega -> Index)
    (hindex : Measurable index) :
    Measurable (fun omega : Omega => rewardKernel.kernel (index omega))

theorem RewardKernel.measurable_eventProbability_of_measurable_index
    [MeasurableSpace Omega]
    (rewardKernel : RewardKernel.MarkovRewardKernel Index Reward)
    (index : Omega -> Index)
    (hindex : Measurable index)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => rewardKernel.kernel (index omega) event)

theorem RewardKernel.isProbabilityMeasure_apply
    (rewardKernel : RewardKernel.MarkovRewardKernel Index Reward)
    (index : Index) :
    MeasureTheory.IsProbabilityMeasure (rewardKernel.kernel index)

def RewardKernel.selectedMeasure
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (context : Context) (action : Action) :
    MeasureTheory.Measure Reward

theorem RewardKernel.measurable_selectedMeasure_of_measurable
    [MeasurableSpace Omega]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (context : Omega -> Context)
    (action : Omega -> Action)
    (hcontext : Measurable context)
    (haction : Measurable action) :
    Measurable
      (fun omega : Omega =>
        RewardKernel.selectedMeasure rewardKernel
          (context omega) (action omega))

theorem RewardKernel.measurable_selectedEventProbability_of_policy_state
    [MeasurableSpace Omega] [MeasurableSpace State]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (context : Omega -> Context)
    (state : Omega -> State)
    (hcontext : Measurable context)
    (hstate : Measurable state)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega =>
        RewardKernel.selectedMeasure rewardKernel
          (context omega) (policy.action (state omega)) event)
```

- Local APIs/imports: `BanditRLProof.RewardKernel`, importing
  `BanditRLProof.PolicyMeasurability` and `Mathlib.Probability.Kernel.Basic`.
- Intended proof route: wrap a Mathlib `ProbabilityTheory.Kernel Index Reward`
  with its `ProbabilityTheory.IsMarkovKernel` instance, then use
  `Kernel.measurable`, `Kernel.measurable_coe`, `Measurable.comp`, and
  `Measurable.prod` to show that measurable arm/context indices select
  measurable random reward measures and event probabilities.  The policy/state
  wrappers reuse `Policy.measurable_action_of_measurable_state`.
- Regularity contracts: measurable index and reward spaces; for
  context/action lookup, measurable context and action spaces; for policy/state
  lookup, a measurable policy and a measurable state random variable.  Every
  selected reward measure is a probability measure by the Markov-kernel
  contract.
- Retrieval evidence: local declarations
  `RewardKernel.MarkovRewardKernel`, `RewardKernel.ofKernel`,
  `RewardKernel.measurable_apply_of_measurable_index`,
  `RewardKernel.measurable_eventProbability_of_measurable_index`,
  `RewardKernel.isProbabilityMeasure_apply`,
  `RewardKernel.selectedMeasure`,
  `RewardKernel.measurable_selectedMeasure_of_measurable`, and
  `RewardKernel.measurable_selectedEventProbability_of_policy_state`;
  Mathlib route is `MLIB-PROBABILITY-KERNEL`.
- Status: project-local compiled Mathlib-backed reward-kernel contract surface.
- Failure policy: this is still only a one-step reward-law lookup and
  regularity surface.  It does not bind policy and reward kernels, build an
  Ionescu-Tulcea trajectory measure, prove conditional reward-law identities,
  or prove final adaptive regret.

`POSTERIOR-KERNEL` is compiled locally as a Mathlib-backed posterior-kernel
contract surface:

```lean
structure PosteriorKernel.MarkovPosteriorKernel
    (History : Type u) (Env : Type v)
    [MeasurableSpace History] [MeasurableSpace Env] where
  kernel : ProbabilityTheory.Kernel History Env
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel kernel
```

```lean
def PosteriorKernel.ofKernel
    (kernel : ProbabilityTheory.Kernel History Env)
    (hkernel : ProbabilityTheory.IsMarkovKernel kernel) :
    PosteriorKernel.MarkovPosteriorKernel History Env
```

```lean
def PosteriorKernel.ofMeasureSelector
    (posterior : History -> Measure Env)
    (hposterior : Measurable posterior)
    (hprob : forall history, IsProbabilityMeasure (posterior history)) :
    PosteriorKernel.MarkovPosteriorKernel History Env
```

```lean
def PosteriorKernel.ofCountableHistorySelector
    [Countable History] [MeasurableSingletonClass History]
    (posterior : History -> Measure Env)
    (hprob : forall history, IsProbabilityMeasure (posterior history)) :
    PosteriorKernel.MarkovPosteriorKernel History Env
```

```lean
theorem PosteriorKernel.measurable_eventProbability_of_measurable_history
    [MeasurableSpace Omega]
    (posterior : PosteriorKernel.MarkovPosteriorKernel History Env)
    (history : Omega -> History)
    (hhistory : Measurable history)
    {event : Set Env}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => posterior.kernel (history omega) event)
```

```lean
structure PosteriorKernel.BayesianPosteriorSurface
    (Env : Type u) (History : Type v)
    [MeasurableSpace Env] [MeasurableSpace History] where
  prior : Measure Env
  likelihood : ProbabilityTheory.Kernel Env History
  posterior : PosteriorKernel.MarkovPosteriorKernel History Env
  prior_isProbability : IsProbabilityMeasure prior
  likelihood_isMarkovKernel :
    ProbabilityTheory.IsMarkovKernel likelihood
```

- Local APIs/imports: `BanditRLProof.PosteriorKernel`, importing
  `Mathlib.Probability.Kernel.Basic`; exported by `BanditRLProof`.
- Intended proof route: wrap a Mathlib
  `ProbabilityTheory.Kernel History Env` with its Markov-kernel proof; or build
  the kernel directly from a measurable posterior-measure selector with
  `ProbabilityTheory.Kernel.mk`; or, for countable/discrete finite-history
  spaces, use `ProbabilityTheory.Kernel.ofFunOfCountable`.  Event-probability
  measurability is inherited from `Kernel.measurable_coe` and composed with a
  measurable random history.
- Regularity contracts: measurable history and environment spaces; either a
  measurable selector `History -> Measure Env` plus pointwise probability, or
  countable/discrete history with pointwise probability.  The optional
  `BayesianPosteriorSurface` records a probability prior, a Markov likelihood
  kernel, and the posterior kernel, but does not assert Bayes' rule.
- Retrieval evidence: local declarations
  `PosteriorKernel.MarkovPosteriorKernel`, `PosteriorKernel.ofKernel`,
  `PosteriorKernel.ofMeasureSelector`,
  `PosteriorKernel.ofCountableHistorySelector`,
  `PosteriorKernel.measurable_kernel`,
  `PosteriorKernel.measurable_apply_of_measurable_history`,
  `PosteriorKernel.measurable_eventProbability_of_measurable_history`,
  `PosteriorKernel.isProbabilityMeasure_apply`,
  `PosteriorKernel.BayesianPosteriorSurface`, and
  `PosteriorKernel.BayesianPosteriorSurface.posterior_isProbabilityMeasure_apply`;
  Mathlib evidence is `ProbabilityTheory.Kernel`,
  `ProbabilityTheory.IsMarkovKernel`, `ProbabilityTheory.Kernel.mk`,
  `ProbabilityTheory.Kernel.ofFunOfCountable`, and
  `ProbabilityTheory.Kernel.measurable_coe`.
- Status: project-local compiled Mathlib-backed posterior-kernel contract
  surface for `POSTERIOR-KERNEL`.
- Failure policy: only repair the Mathlib kernel constructor/import, selector
  measurability, countable-history constructor, or event-probability wrapper.
  Do not prove Bayes' rule, regular conditional distribution existence,
  Thompson probability matching, posterior best-arm measurability, or Bayesian
  regret in the same batch.

`POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` is compiled locally:

```lean
def RewardKernel.policyContextStateIndex
    [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Context × State -> Context × Action

theorem RewardKernel.measurable_policyContextStateIndex
    [MeasurableSpace State]
    (policy : Policy.MeasurablePolicy State Action) :
    Measurable
      (RewardKernel.policyContextStateIndex
        (Context := Context) policy)

def RewardKernel.composePolicy
    [MeasurableSpace State]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    RewardKernel.MarkovRewardKernel (Context × State) Reward

theorem RewardKernel.composePolicy_kernel_apply
    [MeasurableSpace State]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    (RewardKernel.composePolicy rewardKernel policy).kernel pair =
      RewardKernel.selectedMeasure rewardKernel pair.1
        (policy.action pair.2)

theorem RewardKernel.isMarkovKernel_composePolicy
    [MeasurableSpace State]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.composePolicy rewardKernel policy).kernel

theorem RewardKernel.measurable_composePolicy_eventProbability
    [MeasurableSpace State]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun pair : Context × State =>
        (RewardKernel.composePolicy rewardKernel policy).kernel pair event)
```

- Local APIs/imports: `BanditRLProof.RewardKernel`, reusing
  `RewardKernel.MarkovRewardKernel`, `RewardKernel.selectedMeasure`,
  `Policy.MeasurablePolicy`, `measurable_fst`, `measurable_snd`, and
  `Measurable.prodMk`.
- Intended proof route: define the deterministic index map
  `(context, state) |-> (context, policy.action state)`, prove it measurable,
  and use the reward-kernel lookup from `KERNEL-REWARD` to construct a new
  Mathlib kernel over `Context × State`.  The Markov property is inherited
  pointwise from the selected context/action reward measure.
- Regularity contracts: measurable context, state, action, and reward spaces;
  a measurable policy `State -> Action`; and a Markov reward kernel indexed by
  `Context × Action`.
- Retrieval evidence: local declarations
  `RewardKernel.policyContextStateIndex`,
  `RewardKernel.measurable_policyContextStateIndex`,
  `RewardKernel.composePolicy`,
  `RewardKernel.composePolicy_kernel_apply`,
  `RewardKernel.isMarkovKernel_composePolicy`, and
  `RewardKernel.measurable_composePolicy_eventProbability`; Mathlib route is
  `MLIB-PROBABILITY-KERNEL`.
- Status: project-local compiled one-step policy/reward Markov-kernel
  composition surface.
- Failure policy: this is still not a finite-horizon trajectory law.  Do not
  claim Ionescu-Tulcea construction, conditional reward-law transfer,
  martingale-difference structure, or final adaptive regret from this leaf.

`POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` is compiled locally:

```lean
def RewardKernel.historyStepRewardKernel
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    RewardKernel.MarkovRewardKernel ((i : Finset.Iic n) -> Reward) Reward

def RewardKernel.historyStepKernelFamily
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> Reward) Reward

theorem RewardKernel.historyStepKernelFamily_apply
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n history =
      RewardKernel.selectedMeasure rewardKernel (context n history)
        ((policy n).action (state n history))

theorem RewardKernel.isMarkovKernel_historyStepKernelFamily
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n)) :
    forall n : Nat,
      ProbabilityTheory.IsMarkovKernel
        (RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate n)

theorem RewardKernel.measurable_historyStepKernelFamily_eventProbability
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic n) -> Reward =>
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate n history event)

noncomputable def RewardKernel.partialTrajectoryKernel
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic a) -> Reward)
      ((i : Finset.Iic b) -> Reward)

theorem RewardKernel.isMarkovKernel_partialTrajectoryKernel
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
        hcontext hstate a b)

theorem RewardKernel.measurable_partialTrajectoryKernel_eventProbability
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat)
    {event : Set ((i : Finset.Iic b) -> Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic a) -> Reward =>
        RewardKernel.partialTrajectoryKernel rewardKernel policy context state
          hcontext hstate a b history event)
```

- Local APIs/imports: `BanditRLProof.RewardKernel`, now importing
  `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj` in addition to the
  reward-kernel and policy-measurability surfaces.
- Intended proof route: for each time `n`, use measurable context and state
  extractors from the finite reward-history product `Finset.Iic n -> Reward`;
  compose the state extractor with the time-indexed measurable policy, then
  select the corresponding context/action reward law.  The resulting step
  kernels match Mathlib's constant-type-family `partialTraj` shape, so
  `RewardKernel.partialTrajectoryKernel` delegates finite-prefix assembly to
  `ProbabilityTheory.Kernel.partialTraj`.
- Regularity contracts: measurable context, state, action, and reward spaces;
  a time-indexed measurable policy; measurable context/state extractors from
  each finite reward-history product; and a Markov reward kernel indexed by
  `Context × Action`.
- Retrieval evidence: local declarations
  `RewardKernel.historyStepRewardKernel`,
  `RewardKernel.historyStepKernelFamily`,
  `RewardKernel.historyStepKernelFamily_apply`,
  `RewardKernel.isMarkovKernel_historyStepKernelFamily`,
  `RewardKernel.measurable_historyStepKernelFamily_eventProbability`,
  `RewardKernel.partialTrajectoryKernel`,
  `RewardKernel.isMarkovKernel_partialTrajectoryKernel`, and
  `RewardKernel.measurable_partialTrajectoryKernel_eventProbability`; Mathlib
  route is `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`.
- Status: project-local compiled finite-prefix reward-history partial
  trajectory surface.
- Failure policy: this is not yet the full bandit trajectory law.  Do not claim
  an action/reward joint trajectory, posterior kernel, conditional reward-law
  transfer, martingale-difference theorem, or final adaptive regret from this
  leaf.

`KERNEL-POLICY-BIND` is compiled locally:

```lean
def RewardKernel.policyActionOfContextState
theorem RewardKernel.measurable_policyActionOfContextState
noncomputable def RewardKernel.policyActionKernel
theorem RewardKernel.policyActionKernel_apply
theorem RewardKernel.isMarkovKernel_policyActionKernel

noncomputable def RewardKernel.composePolicyActionReward
theorem RewardKernel.composePolicyActionReward_kernel
theorem RewardKernel.isMarkovKernel_composePolicyActionReward
theorem RewardKernel.measurable_composePolicyActionReward_eventProbability
theorem RewardKernel.composePolicyActionReward_reward_event

noncomputable def RewardKernel.actionRewardHistoryStepKernel
noncomputable def RewardKernel.actionRewardHistoryStepKernelFamily
theorem RewardKernel.actionRewardHistoryStepKernelFamily_apply
theorem RewardKernel.isMarkovKernel_actionRewardHistoryStepKernelFamily
theorem RewardKernel.measurable_actionRewardHistoryStepKernelFamily_eventProbability
theorem RewardKernel.actionRewardHistoryStepKernelFamily_reward_event

noncomputable def RewardKernel.actionRewardPartialTrajectoryKernel
theorem RewardKernel.isMarkovKernel_actionRewardPartialTrajectoryKernel
theorem RewardKernel.measurable_actionRewardPartialTrajectoryKernel_eventProbability
```

- Exact Lean-facing statement: a measurable policy induces a deterministic
  action kernel on `Context × State`; producting that deterministic action
  kernel with the selected context/state reward kernel gives a one-step
  `(Action × Reward)` Markov kernel; a time-indexed family of such step kernels
  over finite `(Action × Reward)` pair histories feeds Mathlib
  `ProbabilityTheory.Kernel.partialTraj` to produce finite-prefix
  action/reward pair trajectory kernels with event-probability measurability.
- Local APIs/imports: `BanditRLProof.RewardKernel`, importing
  `Mathlib.Probability.Kernel.Composition.Prod` and
  `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`, plus the existing
  policy-measurability and reward-kernel contract surfaces.
- Intended proof route: use `ProbabilityTheory.Kernel.deterministic` for the
  policy-selected action, `ProbabilityTheory.Kernel.prod` to pair that action
  law with the composed policy/reward kernel, then instantiate `partialTraj`
  with constant coordinate type `Action × Reward`.  Markov-kernel facts come
  from Mathlib's deterministic/product/partialTraj instances; measurability of
  event probabilities comes from `Kernel.measurable_coe` and measurable
  context/state extractors.
- Regularity contracts: measurable context, state, action, and reward spaces;
  `RewardKernel.MarkovRewardKernel (Context × Action) Reward`; a time-indexed
  `policy : Nat -> Policy.MeasurablePolicy State Action`; and measurable
  context/state extractors from each finite `(Action × Reward)` pair-history
  object.
- Retrieval evidence: local card
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib routes
  `Mathlib.Probability.Kernel.Composition.Prod`,
  `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`, and
  `MLIB-PROBABILITY-KERNEL`; local declarations are the
  `RewardKernel.policyAction*`, `RewardKernel.composePolicyActionReward*`,
  `RewardKernel.actionRewardHistoryStep*`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel*` declarations listed
  above.
- Status: project-local compiled finite-prefix action/reward pair
  trajectory-kernel surface for `KERNEL-POLICY-BIND`.
- Failure policy: do not claim conditional reward-law transfer, posterior
  kernels, infinite action/reward trajectory law, conditional expectation
  identities, martingale-difference structure, or final adaptive regret from
  this leaf.

`LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP` is compiled locally:

```lean
theorem RewardKernel.partialTrajectoryKernel_succ_next_map
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
        hcontext hstate n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n

theorem RewardKernel.partialTrajectoryKernel_succ_next_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
          hcontext hstate n (n + 1) history) =
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n history

theorem RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
        context state hcontext hstate n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Prod Action Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n

theorem RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Prod Action Reward) :
    Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Prod Action Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          context state hcontext hstate n (n + 1) history) =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n history
```

- Exact Lean-facing statement: for both reward-history trajectories and
  action/reward pair trajectories, the `partialTraj` kernel from prefix `n` to
  prefix `n + 1`, mapped along the new coordinate `n + 1`, is exactly the
  configured history-step kernel at time `n`; pointwise measure forms are also
  compiled.
- Local APIs/imports: `BanditRLProof.RewardKernel`, local
  `RewardKernel.partialTrajectoryKernel`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`,
  `RewardKernel.historyStepKernelFamily`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`, and Mathlib
  `ProbabilityTheory.Kernel.map_partialTraj_succ_self`.
- Intended proof route: instantiate Mathlib
  `Kernel.map_partialTraj_succ_self` with the local constant type family
  `fun _ => Reward` or `fun _ => Prod Action Reward`, then obtain the
  pointwise measure form by applying kernel equality to the finite prefix and
  rewriting `Kernel.map_apply`.
- Regularity contracts: measurable context/state/action/reward spaces,
  `RewardKernel.MarkovRewardKernel (Prod Context Action) Reward`, time-indexed
  measurable policies, and measurable context/state extractors from finite
  reward histories or finite action/reward pair histories.
- Retrieval evidence: local card
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP`; local inputs
  `LOCAL-LEAF-POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` and
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib route
  `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `KERNEL-POLICY-BIND`, and
  `POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY`.
- Failure policy: do not treat this as a `condExpKernel` law identification.
  It proves the trajectory-kernel next-coordinate marginal of `partialTraj`;
  future work must still connect the generated-history conditional kernel to
  this trajectory step kernel.

`LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP` is compiled locally:

```lean
theorem RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply
    {Context : Type x} {State : Type u} {Action : Type y}
    {Reward : Type v}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Prod Action Reward) :
    RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy context state
        hcontext hstate n (n + 1) history =
      Measure.map
        (fun next : Prod Action Reward =>
          History.extendPairHistorySucc history next)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy context state
          hcontext hstate n history)
```

- Exact Lean-facing statement: for a frozen finite action/reward pair prefix
  `history : (i : Finset.Iic n) -> Prod Action Reward`, the local
  action/reward `partialTraj` kernel from `n` to `n + 1` is exactly the
  configured next-pair history-step kernel pushed forward through
  `History.extendPairHistorySucc history`.
- Local APIs/imports: `BanditRLProof.RewardKernel`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `History.extendPairHistorySucc`, `measurable_IicProdIoc`, Mathlib
  `ProbabilityTheory.Kernel.partialTraj_succ_self`,
  `ProbabilityTheory.Kernel.map_apply`, `ProbabilityTheory.Kernel.prod_apply`,
  `ProbabilityTheory.Kernel.id_apply`, `Measure.dirac_prod`, and
  `Measure.map_map`.
- Intended proof route: unfold the local `actionRewardPartialTrajectoryKernel`,
  apply Mathlib's one-step `partialTraj_succ_self`, rewrite the resulting
  mapped product kernel pointwise, collapse the Dirac product, compose the two
  `Measure.map` layers, and identify Mathlib's `IicProdIoc` gluing function
  with `History.extendPairHistorySucc` by coordinate extensionality.
- Regularity contracts: measurable context/state/action/reward spaces,
  `RewardKernel.MarkovRewardKernel (Prod Context Action) Reward`, a
  time-indexed measurable policy, and measurable context/state extractors from
  finite action/reward pair histories.  No countability assumption is needed
  for this RewardKernel-side theorem.
- Retrieval evidence: local card
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP`; supporting local
  declarations are `RewardKernel.actionRewardPartialTrajectoryKernel`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `History.extendPairHistorySucc`, and
  `History.measurable_extendPairHistorySucc`; Mathlib route is
  `Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj`.
- Status: project-local compiled Mathlib-backed supporting leaf for
  `COND-EXPECT-REWARD`, `KERNEL-POLICY-BIND`, and `MEAS-HISTORY`.
- Failure policy: do not treat this as the generated-history
  `condExpKernel`/`partialTraj` law.  It proves only the trajectory-kernel
  decomposition after the old prefix is already frozen; future work must still
  identify the conditional kernel of the concrete generated trace with this
  `partialTraj` extension law.

`LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER` is compiled locally:

```lean
structure RewardKernel.CenteredRewardKernelLaw

theorem RewardKernel.composePolicyActionReward_reward_event
theorem RewardKernel.actionRewardHistoryStepKernelFamily_reward_event

theorem RewardKernel.composePolicy_centeredReward_integrable
theorem RewardKernel.composePolicy_centeredReward_integral_eq_zero
theorem RewardKernel.composePolicy_centeredReward_hasSubgaussianMGF

theorem RewardKernel.historyStepKernelFamily_centeredReward_integrable
theorem RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero
theorem RewardKernel.historyStepKernelFamily_centeredReward_hasSubgaussianMGF
```

- Exact Lean-facing statement: a pointwise selected reward-law contract records
  centered integrability, zero integral, and `HasSubgaussianMGF` for every
  context/action reward law.  The compiled transfer wrappers show that
  policy-composed one-step reward kernels and finite reward-history step
  kernels inherit those facts, and that the reward marginal of one-step and
  history-step action/reward kernels is exactly the selected reward law.
- Local APIs/imports: `BanditRLProof.RewardKernel`, `Mathlib.Probability.Kernel.Composition.Prod`,
  and `Mathlib.Probability.Moments.SubGaussian`.
- Intended proof route: use definitional equality for `composePolicy`, Mathlib
  `Kernel.snd_prod` for the reward marginal of the product action/reward
  kernel, and the existing `historyStepKernelFamily_apply` /
  `actionRewardHistoryStepKernelFamily_apply` rewrites for finite-history
  step kernels.
- Regularity contracts: measurable context/state/action spaces, `Rat` reward
  coordinates for centered-law transfer, a `RewardKernel.MarkovRewardKernel
  (Context 脳 Action) Rat`, a `Policy.MeasurablePolicy`, and a
  `RewardKernel.CenteredRewardKernelLaw` witness.
- Retrieval evidence: local card
  `LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER`; Mathlib routes
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-SUBGAUSSIAN`, and
  `Mathlib.Probability.Kernel.Composition.Prod`.
- Status: project-local compiled kernel-level transfer surface supporting
  `COND-EXPECT-REWARD`.
- Failure policy: do not claim that this is a `condExpKernel` identification
  for `partialTraj`, a full adaptive-policy conditional reward law, a
  martingale-difference theorem, or a final ETC theorem.

`LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER` is compiled locally:

```lean
theorem RewardKernel.composePolicyActionReward_reward_map
    {State : Type u} [MeasurableSpace State]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    Measure.map Prod.snd
        ((RewardKernel.composePolicyActionReward rewardKernel policy).kernel
          pair) =
      RewardKernel.selectedMeasure rewardKernel pair.1 (policy.action pair.2)
```

```lean
theorem RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    Measure.map Prod.snd
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          context state hcontext hstate n history) =
      RewardKernel.selectedMeasure rewardKernel
        (context n history) ((policy n).action (state n history))
```

- Exact Lean-facing statement: mapping the one-step action/reward kernel, or
  the history-indexed action/reward step kernel, along `Prod.snd` recovers the
  selected reward measure.
- Local APIs/imports: `BanditRLProof.RewardKernel`,
  `Mathlib.Probability.Kernel.Composition.Prod`, and Mathlib
  `Measure.map`.
- Intended proof route: apply `Measure.ext`; for each measurable reward event
  use `Measure.map_apply measurable_snd`, then close with the compiled
  event-level marginal wrappers
  `RewardKernel.composePolicyActionReward_reward_event` and
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_event`.
- Regularity contracts: measurable context/state/action/reward spaces,
  `RewardKernel.MarkovRewardKernel (Context × Action) Reward`, a measurable
  policy or policy family, and measurable context/state extractors for the
  history-step wrapper.
- Retrieval evidence: local card
  `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER`; Mathlib routes
  `MLIB-PROBABILITY-KERNEL`, `Mathlib.Probability.Kernel.Composition.Prod`,
  and `Mathlib.MeasureTheory.Measure.Map`.
- Status: project-local compiled map-law transfer surface supporting
  `COND-EXPECT-REWARD` and `KERNEL-POLICY-BIND`.
- Failure policy: do not claim this proves the `condExpKernel` trajectory-law
  identification, frozen-past condition, arbitrary adaptive-policy
  predictability, posterior kernels, or final ETC/UCB regret.  It only upgrades
  the selected-reward marginal from event equality to measure pushforward
  equality.

`LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` is compiled locally:

```lean
theorem ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real)
    (h_integrable : Integrable X mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X = 0)
        (ae (mu.trim hm))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real))
```

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (b : Fin K) (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega)
            (fun y : Omega =>
              (((reward y (i + 1) - model.mean b : Rat) : Real))) = 0)
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: a trim-a.e. zero integral under
  `ProbabilityTheory.condExpKernel mu mcond` implies the ordinary conditional
  expectation is a.e. zero, with a succ-indexed centered-reward specialization
  for Mathlib's conditional tail shape.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, importing
  `Mathlib.Probability.Independence.Conditional` and `BanditRLProof.Regret`.
- Intended proof route: apply
  `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel`, compose with
  the supplied trim-a.e. zero kernel-integral hypothesis, then promote the
  resulting trim-a.e. equality to `ae mu` using `ae_eq_of_ae_eq_trim`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  `mcond <= mOmega`, centered reward integrability, and the explicit
  trim-a.e. conditional-kernel zero-integral hypothesis.  No independence,
  boundedness, policy predictability, or trajectory-law construction is
  derived here.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting subleaf for `COND-EXPECT-REWARD`.
  The broad row remains `missing-leaf`.
- Failure policy: repair only the `condExpKernel` / `condExp` bridge.  Do not
  claim `partialTraj`/history-to-`condExpKernel` identification, conditional
  sub-Gaussian witness construction, arbitrary adaptive-policy predictability,
  or final ETC/UCB regret from this leaf.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER` is compiled
locally:

```lean
theorem ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((i : Finset.Iic n) -> Rat))
    (X : Omega -> Real)
    (h_integrable : Integrable X mu)
    (h_kernel_eq : Filter.Eventually
      (fun omega : Omega =>
        integral (ProbabilityTheory.condExpKernel
          (Ω := Omega) (mΩ := mOmega) mu mcond omega) X =
        integral
          (RewardKernel.historyStepKernelFamily rewardKernel policy context
            state hcontext hstate n (history omega))
          (fun reward : Rat =>
            (((reward -
              mean (context n (history omega))
                ((policy n).action (state n (history omega))) :
                  Rat) : Real))))
      (ae (mu.trim hm))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real))
```

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq
```

- Exact Lean-facing statement: under an explicit trim-a.e. equality between
  the conditional-expectation kernel integral of the target variable and the
  corresponding `RewardKernel.historyStepKernelFamily` centered-reward
  integral, ordinary conditional mean-zero follows.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, importing
  `BanditRLProof.RewardKernel`, `BanditRLProof.Regret`, and
  `Mathlib.Probability.Independence.Conditional`.
- Intended proof route: rewrite the `condExpKernel` integral using the explicit
  `h_kernel_eq`, close the right side with
  `RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero`, then
  call `condExp_eq_zero_of_condExpKernel_integral_eq_zero`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  `mcond <= mOmega` or `F.le i`, centered target integrability, measurable
  context/state extractors, and a `RewardKernel.CenteredRewardKernelLaw`.
  The equality between `condExpKernel` and the history-step law is assumed.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER`; Mathlib
  routes `MLIB-CONDITIONAL-EXPECTATION` and `MLIB-PROBABILITY-KERNEL`; local
  inputs `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` and
  `LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER`.
- Status: project-local compiled supporting consumer for `COND-EXPECT-REWARD`.
  The broad row remains `missing-leaf`.
- Failure policy: if future work needs to prove, rather than assume, the
  equality between `condExpKernel` and `historyStepKernelFamily`, split that
  into a separate law-identification missing leaf.  Do not claim conditional
  sub-Gaussianity, arbitrary adaptive-policy predictability,
  martingale-difference structure, or final ETC/UCB regret from this consumer.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER` is
compiled locally:

```lean
theorem ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward
```

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq
```

- Exact Lean-facing statement: under an explicit trim-a.e.
  reward-coordinate pushforward equality
  `Measure.map nextReward (condExpKernel mu mcond omega) =
  RewardKernel.historyStepKernelFamily ... (history omega)` plus a frozen-past
  a.e. equality for the centered target variable under that conditional kernel,
  ordinary conditional mean-zero follows.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, importing
  `BanditRLProof.RewardKernel`, `BanditRLProof.Regret`, and
  `Mathlib.Probability.Independence.Conditional`.
- Intended proof route: use the frozen-past a.e. equality to rewrite the
  conditional-kernel integral, use Mathlib `integral_map` to move from the
  conditional kernel to its reward-coordinate pushforward, rewrite by the
  supplied map equality, close with
  `RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero`, then
  call `condExp_eq_zero_of_condExpKernel_integral_eq_zero`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  `mcond <= mOmega` or `F.le i`, measurable next-reward coordinate, centered
  target integrability, measurable context/state extractors, a
  `RewardKernel.CenteredRewardKernelLaw`, explicit reward-coordinate
  pushforward law equality, and explicit frozen-past a.e. equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER`;
  Mathlib routes `MLIB-CONDITIONAL-EXPECTATION`,
  `MLIB-PROBABILITY-KERNEL`, and `Mathlib.MeasureTheory.Integral.Bochner.Basic`;
  local inputs `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` and
  `LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER`.
- Status: project-local compiled supporting map-law consumer for
  `COND-EXPECT-REWARD`.  The broad row remains `missing-leaf`.
- Failure policy: if future work needs to prove the map equality or the
  frozen-past equality, split those into separate law-identification leaves.
  Do not claim arbitrary adaptive-policy predictability, conditional
  sub-Gaussianity, martingale-difference structure, or final ETC/UCB regret
  from this consumer.

`LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED` is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen
```

- Exact Lean-facing statement: if, trim-a.e. in
  `ae (mu.trim (F.le i))`, the finite reward history satisfies
  `history =ᵐ[condExpKernel mu (F i) omega] fun _ => history omega`,
  then, under the same conditional kernel, the succ-indexed centered target
  `fun y => ((reward y (i + 1) -
    mean (context i (history y))
      ((policy i).action (state i (history y))) : Rat) : Real)`
  is a.e. equal to the same expression with the history-dependent
  context/action mean frozen at `history omega`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, importing
  `BanditRLProof.RewardKernel`, `BanditRLProof.Regret`, and
  `Mathlib.Probability.Independence.Conditional`.
- Intended proof route: `filter_upwards` through the assumed history a.e.
  equality and simplify the deterministic context/state/policy/mean expression
  by the pointwise equality `history y = history omega`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  filtration `F`, measurable-policy structure for the policy actions, the
  finite-history function, and the explicit history frozen-past a.e.
  hypothesis.  No reward-kernel law, integrability, or measurable
  context/state extractor is needed for this deterministic bridge.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`; local consumer target
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER`.
- Status: project-local compiled supporting bridge for `COND-EXPECT-REWARD`.
  It reduces the map-law consumer's centered-target side condition to the
  smaller frozen finite-history obligation.  The broad row remains
  `missing-leaf`.
- Failure policy: do not treat this as the frozen-past theorem itself.  Future
  work must still prove the finite-history frozen-past property from the
  filtration/conditional-kernel construction and separately identify the
  `partialTraj` reward law with `condExpKernel`.

`LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL` is compiled
locally:

```lean
theorem ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet
```

```lean
theorem ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable
```

```lean
theorem ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable
```

- Exact Lean-facing statement: first, if `s` is measurable in the conditioning
  sigma-algebra `mcond`, then trim-a.e.
  `(condExpKernel mu mcond omega).real s` equals the indicator of `s` at
  `omega`.  Second, any countable-valued `mcond`-measurable variable `Y` is
  a.e. constant under `condExpKernel mu mcond omega`.  Third, if the finite
  reward history `history : Omega -> ((j : Finset.Iic i) -> Rat)` is
  measurable at filtration level `F i`, then it is frozen under
  `condExpKernel mu (F i)` trim-a.e.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, importing
  `BanditRLProof.RewardKernel`, `BanditRLProof.Regret`, and
  `Mathlib.Probability.Independence.Conditional`.
- Intended proof route: use
  `ProbabilityTheory.condExpKernel_ae_eq_trim_condExp` to identify
  conditional-kernel event real mass with conditional probability; use
  `condExp_of_stronglyMeasurable` for an event measurable in `mcond`; then
  use `ae_all_iff` over countable singleton fibers and
  `mem_ae_iff_prob_eq_one` for the conditional kernel probability measure to
  turn fiber mass one into an a.e. equality.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  `mcond <= mOmega` or `F.le i`, countable codomain with
  `[MeasurableSingletonClass A]`, `mcond`-measurability of `Y`, and, for the
  finite-history specialization, measurability of the history at `F i`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL`; Mathlib routes
  `MLIB-CONDITIONAL-EXPECTATION` and
  `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`; local consumer
  target `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD` and
  `FILTRATION-HISTORY`.  It discharges the finite-history frozen-past
  condition once the concrete finite-history measurability hypothesis is
  supplied.  The broad row remains `missing-leaf`.
- Failure policy: do not treat this as the trajectory-law identification.
  This leaf itself does not prove finite-history measurability; the next local
  leaf supplies coordinate and generated-history-filtration hookups.  Future
  work must still identify the reward coordinate of `partialTraj` with
  `condExpKernel`.

`LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (ae (mu.trim (F.le i)))
```

```lean
theorem ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: first, if every reward coordinate in
  `Finset.Iic i` is measurable at filtration level `F i`, then the finite
  reward-history prefix `History.finiteRewardHistoryOfTrace (reward omega) i`
  is frozen under `condExpKernel mu (F i)` trim-a.e.  Second, for the local
  shifted generated history filtration `History.historyFiltrationSucc`, the
  same frozen finite-history conclusion follows from timewise measurability of
  the action and reward traces.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, using
  `History.finiteRewardHistoryOfTrace`,
  `History.historyFiltrationSucc`, and
  `History.measurable_reward_mem_historyFiltration_of_lt` from
  `BanditRLProof.HistoryFiltration` via the existing import chain.
- Intended proof route: reduce the coordinate version to
  `finiteRewardHistory_condExpKernel_frozen_of_measurable` by building the
  Pi-space measurability proof with `measurable_pi_lambda`.  Then specialize
  to `History.historyFiltrationSucc` by applying
  `History.measurable_reward_mem_historyFiltration_of_lt` with
  `Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)` for each prefix coordinate.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  filtration monotonicity through `F.le i`, coordinate measurability at `F i`,
  and, for the generated-history specialization, measurable action/reward
  coordinates plus `[MeasurableSingletonClass Action]`; Rat supplies the
  countable/discrete reward-side instances used by the history-filtration API.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP`; local inputs
  `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL`,
  `LOCAL-LEAF-HISTORY-FILTRATION`, and
  `LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD` and
  `FILTRATION-HISTORY`.  It closes the concrete finite-history measurability
  hookup for the frozen-past route.  The broad row remains `missing-leaf`.
- Failure policy: do not treat this as a `partialTraj`/`condExpKernel`
  reward-law theorem, arbitrary adaptive-policy predictability theorem, or
  final adaptive ETC theorem.  It only supplies the finite-history frozen-past
  hypothesis once the conditioning filtration is the generated history
  filtration or once coordinate measurability is provided explicitly.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP` is compiled locally:

```lean
theorem ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (hhistory :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        (F i) inferInstance history) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          history
          (fun _y : Omega => history omega))
      (ae (mu.trim (F.le i)))

theorem ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (haction :
      forall j : Finset.Iic i,
        @Measurable Omega Action (F i) inferInstance
          (fun omega : Omega => action omega j.1))
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (ae (mu.trim (F.le i)))

theorem ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a finite action/reward pair prefix is frozen
  under `condExpKernel mu (F i)` whenever it is measurable at `F i`; coordinate
  measurability of every action and reward prefix coordinate supplies that
  measurability for `History.finitePairHistoryOfTrace`; and the generated
  `History.historyFiltrationSucc` specialization supplies those coordinate
  hypotheses from local history-filtration APIs.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `History.finitePairHistoryOfTrace`,
  `History.measurable_action_mem_historyFiltration_of_lt`,
  `History.measurable_reward_mem_historyFiltration_of_lt`,
  `condExpKernel_ae_eq_const_of_countable_measurable`, and
  `measurable_pi_lambda`.
- Intended proof route: reuse the generic countable-valued frozen-past theorem
  with `Y := history`; prove the finite pair trace is measurable by
  `measurable_pi_lambda` and coordinatewise product measurability; specialize
  to `History.historyFiltrationSucc` by applying the local past-coordinate
  action and reward measurability lemmas with `j.1 < i + 1`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable singleton action space, `[Countable Action]`, Rat reward
  coordinates, explicit coordinate measurability at `F i` or timewise
  measurability for the generated history filtration.  The `[Countable Action]`
  contract is necessary because the frozen object contains action coordinates.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP`; local inputs
  `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL`,
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`,
  `LOCAL-LEAF-HISTORY-FILTRATION`, and
  `LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `FILTRATION-HISTORY`, and `MEAS-HISTORY`.  It extends frozen-past support
  from reward-only prefixes to full finite action/reward pair prefixes.
- Failure policy: do not treat this as the `partialTraj`/`condExpKernel`
  pair-law identification.  It freezes the past pair prefix once that prefix is
  measurable; future work must still identify the conditional distribution of
  the next pair with the local trajectory/history-step kernel.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP` is compiled locally:

```lean
def History.extendPairHistorySucc
    {Action : Type v} {Reward : Type w} {t : Nat}
    (history : History.FinitePairHistory Action Reward t)
    (next : Prod Action Reward) :
    History.FinitePairHistory Action Reward (t + 1)

@[simp] theorem History.finitePairHistoryOfTrace_succ
    {Action : Type v} {Reward : Type w}
    (action : ActionTrace Action)
    (reward : RewardTrace Reward)
    (t : Nat) :
    History.finitePairHistoryOfTrace action reward (t + 1) =
      History.extendPairHistorySucc
        (History.finitePairHistoryOfTrace action reward t)
        (action (t + 1), reward (t + 1))

theorem History.measurable_extendPairHistorySucc
    {Action : Type v} {Reward : Type w} {t : Nat}
    [MeasurableSpace Action] [MeasurableSpace Reward] :
    Measurable
      (fun input :
          Prod (History.FinitePairHistory Action Reward t)
            (Prod Action Reward) =>
        History.extendPairHistorySucc input.1 input.2)

theorem ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega]
    (nu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat) (omega : Omega)
    (h_pair_history_frozen :
      Filter.EventuallyEq (ae nu)
        (fun y : Omega =>
          History.finitePairHistoryOfTrace (action y) (reward y) i)
        (fun _y : Omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) i)) :
    Filter.EventuallyEq (ae nu)
      (fun y : Omega =>
        History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
      (fun y : Omega =>
        History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
          (action y (i + 1), reward y (i + 1)))

theorem ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: `History.extendPairHistorySucc` appends a next
  `(Action, Reward)` pair to a finite pair prefix; the true trace prefix at
  `t + 1` is definitionally this extension of the prefix at `t`; the extension
  map is measurable; and under a frozen-prefix hypothesis, in particular under
  generated `History.historyFiltrationSucc`/`condExpKernel`, the random
  `i + 1` finite pair trace is a.e. the frozen old prefix extended by the
  random next pair.
- Local APIs/imports: `BanditRLProof.HistoryFiltration`,
  `BanditRLProof.ConditionalExpectationReward`,
  `History.extendPairHistorySucc`, `History.finitePairHistoryOfTrace_succ`,
  `History.measurable_extendPairHistorySucc`,
  `ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc`,
  and `measurable_pi_lambda`.
- Intended proof route: define the extension by case-splitting each
  `Finset.Iic (t + 1)` coordinate into old coordinates `<= t` and the terminal
  coordinate `t + 1`; prove the trace decomposition by `funext` and arithmetic
  on `Nat`; prove measurability coordinatewise; then combine the deterministic
  decomposition with the pair-prefix frozen-past theorem under the conditional
  kernel.
- Regularity contracts: measurable action/reward spaces for extension
  measurability; `[StandardBorelSpace Omega]`, finite `mu`,
  `[MeasurableSingletonClass Action]`, `[Countable Action]`, and timewise
  action/reward trace measurability for the generated conditional-kernel
  specialization.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP`; local
  inputs `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP`,
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`, and
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `FILTRATION-HISTORY`, `MEAS-HISTORY`, and `KERNEL-POLICY-BIND`.
- Failure policy: do not treat this as equality of joint laws.  It gives the
  a.e. random-variable decomposition needed before a joint map-law proof; the
  actual `partialTraj`/history-to-`condExpKernel` action/reward pair-law
  identification remains open.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER` is compiled
locally:

```lean
theorem ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the first theorem upgrades the generated
  `condExpKernel` successor decomposition from an a.e. equality to a
  `Measure.map` equality using the same source and target spaces as the
  remaining finite-pair-trace law.  The second theorem consumes an
  extension-map law and returns the full finite-pair-trace `partialTraj` law:
  `Measure.map (fun y => History.finitePairHistoryOfTrace (action y)
  (reward y) (i + 1)) (condExpKernel ...) =
  RewardKernel.actionRewardPartialTrajectoryKernel ... i (i + 1)
  (History.finitePairHistoryOfTrace (action omega) (reward omega) i)`,
  trim-a.e. under the generated history filtration.  The third theorem consumes
  an
  extension-map law: if the conditional kernel pushed through
  `History.extendPairHistorySucc` of the frozen old pair prefix and random next
  pair agrees with `RewardKernel.actionRewardPartialTrajectoryKernel` from
  `i` to `i + 1`, then the centered next reward has ordinary conditional
  expectation zero under generated `History.historyFiltrationSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `History.extendPairHistorySucc`,
  `ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  `Measure.map_congr`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: use the a.e. successor decomposition from the previous
  leaf, apply Mathlib `Measure.map_congr` pointwise under the trim-a.e.
  conditional-kernel event, then compose that pushforward equality with the
  supplied extension-map-to-`partialTraj` equality and feed the resulting
  full finite-pair-trace law into the existing partialTraj finite-pair-trace
  consumer.  The new named adapter exposes that middle composition as a
  reusable law theorem before the centered-reward consumer is applied.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite `mu`, measurable
  context/state/action spaces, `[MeasurableSingletonClass Action]`,
  `[Countable Action]`, timewise measurable action and reward traces, a
  centered-reward integrability hypothesis, and a
  `RewardKernel.CenteredRewardKernelLaw`.  The countability requirement is
  inherited from freezing finite action/reward pair prefixes.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER`; local
  inputs `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER`, and
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP`, with the matching
  RewardKernel-side extension wrapper
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `FILTRATION-HISTORY`, `MEAS-HISTORY`, and `KERNEL-POLICY-BIND`.  It narrows
  the remaining partialTraj law hypothesis from the whole `i + 1` pair trace
  to a deterministic extension of the frozen old pair prefix by the random next
  pair, while still exposing the derived whole-trace law for downstream
  consumers.
- Failure policy: do not claim the `partialTraj`/history-to-`condExpKernel`
  action/reward pair-law identification is proved.  This leaf only changes the
  shape of the remaining law assumption; the actual conditional-kernel
  trajectory-law theorem is still open.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
```

- Exact Lean-facing statement: if the conditional kernel of the next sampled
  `(Action, Reward)` pair, pushed forward by
  `fun y => (action y (i + 1), reward y (i + 1))`, is equal trim-a.e. to
  `RewardKernel.actionRewardHistoryStepKernelFamily`, then the same conditional
  kernel pushed through
  `fun y => History.extendPairHistorySucc oldPrefix
    (action y (i + 1), reward y (i + 1))`
  is equal trim-a.e. to
  `RewardKernel.actionRewardPartialTrajectoryKernel ... i (i + 1) oldPrefix`.
  A generated `History.historyFiltrationSucc` specialization fixes `oldPrefix`
  to `History.finitePairHistoryOfTrace (action omega) (reward omega) i`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `BanditRLProof.RewardKernel`, `History.extendPairHistorySucc`,
  `History.finitePairHistoryOfTrace`,
  `History.measurable_pairHistoryRewardProjection`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`.
- Intended proof route: prove the next-pair map is measurable from `haction`
  and `hreward`, prove the fixed-prefix extension map is measurable via
  `History.measurable_extendPairHistorySucc`, rewrite
  `Measure.map extendNext (Measure.map nextPair condKernel)` with
  `Measure.map_map`, rewrite the inner next-pair law hypothesis, and close the
  target with
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply`.
- Regularity contracts: standard Borel sample space, finite measure, measurable
  context/state/action spaces, timewise measurable action and reward traces, a
  measurable policy, measurable pairContext/pairState surfaces, and a trim-a.e.
  next-pair `condExpKernel` pushforward law.  The generated specialization also
  needs `[MeasurableSingletonClass Action]` to build
  `History.historyFiltrationSucc`; it does not need `[Countable Action]`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP`; local
  inputs are `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER`, and
  `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP`; Mathlib route is
  `Mathlib.MeasureTheory.Measure.Map`.
- Status: project-local compiled law-builder leaf for `COND-EXPECT-REWARD`,
  `KERNEL-POLICY-BIND`, `MEAS-HISTORY`, and `FILTRATION-HISTORY`.
- Failure policy: do not mark `COND-EXPECT-REWARD` complete from this theorem.
  It assumes the next-pair conditional-kernel law and only transports that law
  through the deterministic finite-prefix extension map.

`LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER` is compiled locally:

```lean
theorem RewardKernel.composePolicyActionReward_kernel_apply_eq_map_prod_mk

theorem RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk

theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq
```

- Exact Lean-facing statement: the RewardKernel wrappers expose the full
  one-step and history-step `(Action, Reward)` law as
  `Measure.map (Prod.mk selectedAction)` of the selected reward measure.  The
  ConditionalExpectationReward theorem says that if, trim-a.e. under the
  conditioning kernel, the next action is a.e. equal to the policy-selected
  action and the next reward pushforward equals the selected reward measure,
  then the full next-pair pushforward equals
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Local APIs/imports: `BanditRLProof.RewardKernel`,
  `BanditRLProof.ConditionalExpectationReward`,
  `RewardKernel.composePolicyActionReward`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `RewardKernel.selectedMeasure`, Mathlib `Kernel.prod_apply`,
  `Measure.dirac_prod`, `Measure.map_congr`, and `Measure.map_map`.
- Intended proof route: expand the policy/reward product kernel to a Dirac
  action times selected reward measure, rewrite Dirac-product as a fixed-action
  pushforward, use `Measure.map_congr` for the action a.e. equality, use
  `Measure.map_map` to factor the fixed-action pair map through the reward
  coordinate, rewrite the reward-coordinate law, and close against the
  RewardKernel full-shape wrapper.
- Regularity contracts: measurable context/state/action spaces, finite measure,
  standard Borel sample space, measurable policy, measurable pairContext and
  pairState, timewise measurable next action/reward coordinates, a conditional
  a.e. action equality to the policy-selected action, and a reward-coordinate
  `condExpKernel` pushforward equality to `RewardKernel.selectedMeasure`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER`; local inputs
  include `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP`,
  `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER`, and `ADAPTED-ACTION`;
  Mathlib route is `Mathlib.MeasureTheory.Measure.Map`.
- Status: project-local compiled split-law builder for `COND-EXPECT-REWARD`,
  `KERNEL-POLICY-BIND`, `ADAPTED-ACTION`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not prove action predictability/freezing or
  the reward-coordinate selected-measure law.  It only composes those two
  contract surfaces into the full next-pair law.

`LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW` is
compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a generated-action random next-pair source law
  stated as a conditional pushforward of
  `(fun y => (action y (i + 1), reward y (i + 1)))` into
  `Measure.map (Prod.mk (action omega (i + 1))) selectedMeasure` is rewritten
  into the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` pair law over
  `History.finitePairHistoryOfTrace`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`,
  `Policy.generatedActionTraceSucc`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `RewardKernel.selectedMeasure`, and Mathlib `Measure.map`.
- Intended proof route: derive the pointwise successor action equality from
  `Policy.generatedActionTraceSucc`, filter it together with the assumed
  random next-pair map law, then rewrite the fixed-action selected-measure RHS
  using
  `RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action and reward traces, measurable
  `pairContext`/`pairState`, equality of the actual action trace with the
  shifted generated action trace, and the explicit random next-pair
  conditional-kernel map law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`;
  local inputs include
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE`, and
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib route
  is `Mathlib.MeasureTheory.Measure.Map`.
- Status: project-local compiled law-shape adapter for `COND-EXPECT-REWARD`,
  `KERNEL-POLICY-BIND`, `ADAPTED-ACTION`, `KERNEL-REWARD`, and
  `MEAS-HISTORY`.
- Failure policy: this theorem does not construct the random next-pair source
  law, does not identify the ambient `partialTraj`/history law with
  `condExpKernel`, does not provide sub-Gaussian witnesses, and does not close
  the final adaptive theorem.  If the random pair law is unavailable, keep this
  leaf as a downstream adapter and work on the upstream law source.

`LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq
    {Omega : Type u} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (action : Omega -> ActionTrace Action)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next_meas :
      @Measurable Omega Action (F i) inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action (pairState i (pairHistory omega))))
      (ae (mu.trim (F.le i)))
```

- Exact Lean-facing statement: the theorem turns an `F i`-measurable,
  countable-valued next-action coordinate plus a trim-a.e. equality to the
  policy-selected action into the conditional a.e. action equality required by
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `BanditRLProof.RewardKernel`, `Filtration`, Mathlib
  `ProbabilityTheory.condExpKernel`, `Measure.trim`, `Filter.EventuallyEq`,
  and the local
  `ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable`.
- Intended proof route: apply the countable-valued conditional-kernel freezing
  theorem to `fun omega => action omega (i + 1)` at filtration level `F i`;
  combine the resulting trimmed-a.e. frozen action with
  `h_action_policy_eq`; rewrite the frozen constant from
  `action omega (i + 1)` to `(policy i).action (pairState i
  (pairHistory omega))`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable singleton/countable action space, measurable state/action spaces,
  a filtration `F`, an `F i`-measurable next-action coordinate, and a
  trim-a.e. policy-generation equality at the same time index and finite pair
  history.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP`; it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL`,
  `LOCAL-LEAF-POLICY-GENERATED-ACTION-TRACE-MEASURABILITY`, and feeds
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER`; Mathlib route is
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled action-freezing hookup for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, and `KERNEL-POLICY-BIND`.
- Failure policy: this theorem does not prove arbitrary policy predictability,
  does not construct the next-action measurability hypothesis, and does not
  prove the reward-coordinate selected-measure law.  If policy-generation is
  unavailable, keep this as a contract adapter and work on a separate
  predictability/policy-trace source.

`LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP` is
compiled locally:

```lean
theorem ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq

theorem ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq
```

- Exact Lean-facing statement: the first theorem assumes a finite pair history
  `pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat)` is
  measurable at `F i`, `pairState i` is measurable, and
  `(fun omega => action omega (i + 1)) =
   (fun omega => (policy i).action (pairState i (pairHistory omega)))`.
  It concludes the same conditional a.e. action equality required by
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`.
  The second theorem specializes this to
  `F = History.historyFiltrationSucc action reward haction hreward` and
  `pairHistory omega = History.finitePairHistoryOfTrace (action omega)
  (reward omega) i`, proving the pair-history measurability side from local
  history-filtration APIs.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `History.measurable_action_mem_historyFiltration_of_lt`,
  `History.measurable_reward_mem_historyFiltration_of_lt`,
  `Policy.MeasurablePolicy`, `Filter.EventuallyEq`, and the previous
  `action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq`.
- Intended proof route: compose measurable `pairState i` with the visible
  pair-history prefix, compose the measurable policy action with that state,
  use the pointwise action equality to rewrite the next-action coordinate and
  obtain both `h_action_next_meas` and trim-a.e. policy equality, then call the
  action-freezing policy hookup.  The generated-history specialization proves
  pair-prefix measurability coordinatewise from `History.historyFiltrationSucc`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable singleton/countable action space, measurable state/action spaces,
  measurable `pairState`, a finite pair-history prefix visible at the
  conditioning filtration, and a pointwise policy-generation equality for the
  next action.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP`,
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`,
  `LOCAL-LEAF-POLICY-MEASURABILITY`, and `FILTRATION-HISTORY`; it feeds the
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER`.
- Status: project-local compiled generated-history action-side hookup for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-HISTORY`, `MEAS-POLICY`, and
  `KERNEL-POLICY-BIND`.
- Failure policy: this theorem still assumes pointwise policy-generation
  equality for the next action.  It does not construct the reward-coordinate
  selected-measure law, the full next-pair law, or the final adaptive theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE` is
compiled locally:

```lean
def Policy.generatedActionTraceSucc

theorem Policy.generatedActionTraceSucc_succ_eq

theorem Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state

theorem ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc
```

- Exact Lean-facing statement: `Policy.generatedActionTraceSucc` is the
  shifted time-indexed generated action trace whose coordinate `t + 1` is
  `(policy t).action (state t omega)`.  The ConditionalExpectationReward
  theorem assumes the actual action trace equals this shifted generated trace
  with state `fun n omega => pairState n
  (History.finitePairHistoryOfTrace (action omega) (reward omega) n)`, then
  concludes the conditional a.e. action equality required by the next-pair
  split-law builder.
- Local APIs/imports: `BanditRLProof.PolicyMeasurability`,
  `Policy.generatedActionTraceSucc`,
  `Policy.generatedActionTraceSucc_succ_eq`,
  `Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state`,
  `BanditRLProof.ConditionalExpectationReward`,
  `History.finitePairHistoryOfTrace`, and the generated-history
  action-freezing hookup.
- Intended proof route: define the shifted action trace by matching on time;
  coordinate `t + 1` reduces to `policy t`.  In the conditional-expectation
  adapter, apply `congrFun` twice to the action-trace equality at `(omega,
  i + 1)`, simplify the shifted trace, and feed the resulting pointwise
  policy-generation equality to
  `action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable singleton/countable action space, measurable `pairState`, timewise
  measurable action and reward traces for `History.historyFiltrationSucc`, a
  default action for time `0`, and equality of the actual action trace with the
  shifted generated trace.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP`,
  `LOCAL-LEAF-POLICY-GENERATED-ACTION-TRACE-MEASURABILITY`,
  `LOCAL-LEAF-POLICY-MEASURABILITY`, and `FILTRATION-HISTORY`.
- Status: project-local compiled generated-trace source for the
  `COND-EXPECT-REWARD` action side.
- Failure policy: this theorem still assumes equality between the actual
  action trace and the shifted generated trace.  It does not prove the
  reward-coordinate selected-measure law, the full next-pair law, or the final
  adaptive theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP`
is compiled locally:

```lean
theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq

theorem ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq

theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq

theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
```

- Exact Lean-facing statement: the first theorem marginalizes an
  actual-action pair-product law through `Prod.snd`: if
  `Measure.map (fun y => (action omega (i+1), reward y (i+1)))` of the
  conditional kernel equals
  `Measure.map (Prod.mk (action omega (i+1)))` of the selected reward law,
  then the conditional reward coordinate has the actual-action selected reward
  law.  The random-pair freezing theorem accepts a law for
  `Measure.map (fun y => (action y (i+1), reward y (i+1)))` and uses the
  generated action trace to turn it into the frozen-action pair law consumed by
  the marginalization route.  The next theorem rewrites a reward-coordinate
  map law of the form
  `Measure.map (fun y => reward y (i + 1)) (condExpKernel mu (F i) omega) =
  RewardKernel.selectedMeasure rewardKernel (pairContext i (pairHistory omega))
  (action omega (i + 1))` into the policy-selected action version, assuming
  trim-a.e. `action omega (i + 1) = (policy i).action (pairState i
  (pairHistory omega))`.  The generated-history theorem assumes
  `action = Policy.generatedActionTraceSucc policy (fun n omega => pairState n
  (History.finitePairHistoryOfTrace (action omega) (reward omega) n))
  defaultAction` plus the actual-action reward-coordinate map law under
  `History.historyFiltrationSucc`, and concludes the full next-pair
  `condExpKernel` pushforward identity into
  `RewardKernel.actionRewardHistoryStepKernelFamily`.  The extension-map
  theorem specializes this to projected reward-history context/state extractors
  and concludes the `History.extendPairHistorySucc` pushforward law against
  `RewardKernel.actionRewardPartialTrajectoryKernel`.  The full-trace
  `partialTraj` theorem composes that extension-map law with the generated
  successor decomposition, exposing the law for
  `Measure.map (fun y => History.finitePairHistoryOfTrace (action y)
  (reward y) (i + 1)) (condExpKernel ...)`.  The pair-product law adapter
  accepts the upstream actual-action pair-product law directly and exposes the
  same full finite-pair-trace `partialTraj` law; the random-pair law adapter
  accepts the fully random next-pair law, freezes the action coordinate, and
  exposes that same full-trace law.  The final consumers add the centered reward
  integrability hypothesis and conclude ordinary succ-indexed conditional
  mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `Policy.generatedActionTraceSucc`,
  `ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc`,
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`,
  `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`,
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`,
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `History.finiteRewardHistoryOfTrace`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`, and
  `RewardKernel.selectedMeasure`.
- Intended proof route: derive trim-a.e. pointwise equality between the actual
  next action and the policy-selected action by simplifying the shifted
  generated trace at coordinate `i + 1`; if the source law is a fully random
  next-pair law, first use conditional a.e. equality of `action y (i + 1)` and
  pointwise equality of `action omega (i + 1)` to the same policy action, then
  apply `Measure.map_congr` to freeze the action coordinate; if the source law
  is a pair-product law, map both sides through `Prod.snd` and use
  `Measure.map_map` to get the actual-action reward-coordinate law; use the
  generated-action equality to rewrite that reward-coordinate map law to the
  policy-selected form; combine it with the generated action-freezing theorem
  in the generic next-pair
  split-law builder.  For the projected reward-history specialization, rewrite
  `History.pairHistoryRewardProjection (History.finitePairHistoryOfTrace ...)`
  to `History.finiteRewardHistoryOfTrace ...`, then pass the resulting
  next-pair law through the extension-map `partialTraj` builder, expose the
  full finite-pair-trace `partialTraj` law with the extension-to-trace adapter,
  lift the pair-product and fully random pair law shapes to that same law
  surface, and finally feed the existing centered-reward conditional mean-zero
  consumer.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton/countable action
  space for the action-freezing source, measurable `pairContext` and
  `pairState`, timewise measurable action/reward traces, a default action for
  the shifted trace, equality of the actual action trace to the shifted
  generated trace, an externally supplied actual-action reward-coordinate map
  law, actual-action pair-product law, or fully random next-pair law under the
  generated history filtration, and integrability of the centered reward for the final
  conditional mean-zero consumer.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER`,
  `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER`, and `FILTRATION-HISTORY`.
- Status: project-local compiled next-pair hookup for `COND-EXPECT-REWARD`,
  `ADAPTED-ACTION`, `MEAS-POLICY`, `KERNEL-POLICY-BIND`, and
  `KERNEL-REWARD`.  It now exports full finite-pair-trace `partialTraj` law
  adapters for reward-coordinate, actual-action pair-product, and fully random
  next-pair law shapes, plus the centered conditional mean-zero consumers.
- Failure policy: this theorem deliberately does not prove the actual-action
  or random pair/reward law or the ambient trajectory-to-`condExpKernel` identification.
  If the external reward source is not available, do not use this card as a
  theorem dependency; treat it as a route adapter only.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionActualRewardMapSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  action_generated :
    action =
      Policy.generatedActionTraceSucc policy
        (fun n omega =>
          state n (History.finiteRewardHistoryOfTrace (reward omega) n))
        defaultAction
  reward_map_eq_actual_action :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega => reward y (i + 1))
            (condExpKernel mu
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (ae (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le i)))

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource
```

- Exact Lean-facing statement: the source packages the shifted generated-action
  equality and only the actual next-action reward-coordinate conditional map
  law.  The `partialTraj` consumer turns that reward-coordinate law into the
  full finite-pair-trace `partialTraj` law through the existing generated-action
  actual reward-map route.  The conditional mean-zero consumer adds the
  centered reward-kernel law and centered-reward integrability.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`,
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`,
  `History.historyFiltrationSucc`,
  `History.finiteRewardHistoryOfTrace`,
  `RewardKernel.selectedMeasure`, and
  `RewardKernel.CenteredRewardKernelLaw`.
- Intended proof route: copy the structure fields into the existing
  generated-action actual reward-map consumers.  No new measure-theoretic
  proof is attempted in this wrapper.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton/countable action
  space, timewise measurable action/reward traces, equality of the action trace
  to the shifted generated policy trace, an actual next-action reward-coordinate
  conditional map law under
  `ae (mu.trim ((History.historyFiltrationSucc action reward haction hreward).le i))`,
  centered reward-kernel law, and centered-reward integrability for the
  conditional mean-zero consumer.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource`.
- Status: project-local compiled actual reward-coordinate source contract leaf
  for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the actual reward-coordinate law, the full random next-pair law,
  ambient trajectory-to-`condExpKernel` identification, integrability, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionActualRewardMapSource mu action rewardKernel policy
        context state defaultAction reward haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: from a
  `GeneratedActionActualRewardMapSource`, prove that the `condExpKernel`
  pushforward of the actual next `(action, reward)` pair at time `i + 1`
  equals `RewardKernel.actionRewardHistoryStepKernelFamily` at the frozen
  finite pair trace `History.finitePairHistoryOfTrace (action omega)
  (reward omega) i`, a.e. under the trimmed `History.historyFiltrationSucc`
  sigma-algebra at time `i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`,
  `History.pairHistoryRewardProjection`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`,
  `History.measurable_pairHistoryRewardProjection`,
  `History.finitePairHistoryOfTrace`,
  `History.historyFiltrationSucc`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: rewrite the packaged generated-action equality from
  reward histories to pair histories using
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`, compose
  `hcontext` and `hstate` with
  `History.measurable_pairHistoryRewardProjection`, then reuse the existing
  generated-action actual reward-map hookup theorem.
- Regularity contracts: standard Borel sample space, finite measure, measurable
  context/state/action spaces, measurable singleton and countable action space,
  timewise measurable action and reward traces, the packaged shifted
  generated-action equality, and the packaged actual next-action
  reward-coordinate `condExpKernel` map law from
  `GeneratedActionActualRewardMapSource`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`;
  upstream route cards
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP`,
  `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER`, and `FILTRATION-HISTORY`.
- Status: project-local compiled source-level canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is not a proof of the actual reward-coordinate law or
  the ambient trajectory-to-`condExpKernel` identification.  If the
  `GeneratedActionActualRewardMapSource` fields are unavailable, do not cite
  this theorem as a law source; use it only after that source has been
  constructed.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  hstate : forall n : Nat, Measurable (state n)
  reward_map_eq_actual_action :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega => reward y (i + 1))
            (condExpKernel mu
              ((History.historyFiltrationSucc
                (generatedActionFromRewardHistory policy state defaultAction
                  reward)
                reward
                (generatedActionFromRewardHistory_measurable
                  hreward hstate)) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (generatedActionFromRewardHistory policy state defaultAction
              reward omega (i + 1)))
        (ae (mu.trim
          ((History.historyFiltrationSucc
            (generatedActionFromRewardHistory policy state defaultAction reward)
            reward
            (generatedActionFromRewardHistory_measurable hreward hstate)
            hreward).le i)))

def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource
```

- Exact Lean-facing statement: the source is the definitional generated-action
  variant of `GeneratedActionActualRewardMapSource`.  The action trace is fixed
  to `generatedActionFromRewardHistory policy state defaultAction reward`; the
  structure stores measurable state extractors and the actual next-action
  reward-coordinate conditional map law under the generated
  `History.historyFiltrationSucc`.  The conversion def builds the explicit
  actual reward-map source, and the consumers expose full finite-pair-trace
  `partialTraj` law plus succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource`.
- Intended proof route: derive `haction` with
  `generatedActionFromRewardHistory_measurable`, convert the definitional
  source to `GeneratedActionActualRewardMapSource`, then reuse the existing
  actual reward-map consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton/countable action
  space, timewise measurable reward trace, measurable reward-history state
  extractors, an actual next-action reward-coordinate law under the generated
  history filtration, centered reward-kernel law, and centered-reward
  integrability for the conditional mean-zero consumer.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`,
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource`.
- Status: project-local compiled definitional actual reward-coordinate source
  contract leaf for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the actual reward-coordinate law, the full random next-pair law,
  ambient trajectory-to-`condExpKernel` identification, integrability, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionDefinitionalActualRewardMapSource mu rewardKernel policy
        context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (generatedActionFromRewardHistory policy state defaultAction reward)
            reward
            (generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i)))
```

- Exact Lean-facing statement: from a
  `GeneratedActionDefinitionalActualRewardMapSource`, prove that the
  `condExpKernel` pushforward of the generated next action
  `generatedActionFromRewardHistory ... (i + 1)` paired with the actual next
  reward equals `RewardKernel.actionRewardHistoryStepKernelFamily` at the
  frozen finite pair trace over `generatedActionFromRewardHistory`, a.e. under
  the trimmed generated `History.historyFiltrationSucc` sigma-algebra.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`,
  `History.finitePairHistoryOfTrace`,
  `History.historyFiltrationSucc`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: instantiate the explicit actual-source pair-law theorem
  at `generatedActionFromRewardHistory policy state defaultAction reward`,
  derive `haction` from `generatedActionFromRewardHistory_measurable`, convert
  the definitional source to `GeneratedActionActualRewardMapSource`, and reuse
  `source.hstate` for projected pair-state measurability.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, source-provided state
  measurability, and the packaged definitional actual next-action
  reward-coordinate `condExpKernel` map law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`;
  upstream route cards
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP`,
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`,
  `LOCAL-LEAF-POLICY-MEASURABILITY`, and `FILTRATION-HISTORY`.
- Status: project-local compiled definitional source-level canonical pair-law
  consumer for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not construct the definitional
  reward-coordinate source law or the ambient trajectory-to-`condExpKernel`
  identification.  If the source fields are unavailable, do not use it as a
  proof dependency; first construct the source.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionDefinitionalActualRewardMapSource mu rewardKernel policy
        context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (generatedActionFromRewardHistory
                policy state defaultAction reward y)
              (reward y) (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ...
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc
          (generatedActionFromRewardHistory policy state defaultAction reward)
          reward
          (generatedActionFromRewardHistory_measurable hreward source.hstate)
          hreward).le i)))
```

- Exact Lean-facing statement: from a
  `GeneratedActionDefinitionalActualRewardMapSource`, prove that the
  `condExpKernel` pushforward of the complete generated action/reward pair
  trace through time `i + 1` equals
  `RewardKernel.actionRewardPartialTrajectoryKernel` from prefix `i` to
  `i + 1`, with contexts and states lifted from pair histories through
  `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`,
  `History.historyFiltrationSucc`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: derive the hidden action measurability from
  `generatedActionFromRewardHistory_measurable`, lower the definitional source
  to the explicit `GeneratedActionActualRewardMapSource`, and reuse the
  explicit actual-source full finite-pair-trace `partialTraj` theorem.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, source-provided state
  measurability, and the packaged definitional actual next-action
  reward-coordinate `condExpKernel` map law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-TO-PARTIALTRAJ-LAW`;
  declaration
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource`;
  upstream route cards
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-ACTUAL-REWARD-MAP-SOURCE-CONTRACT`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER`,
  `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`,
  `LOCAL-LEAF-POLICY-MEASURABILITY`, and `FILTRATION-HISTORY`.
- Status: project-local compiled definitional source-level full finite-pair
  `partialTraj` consumer for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`,
  `MEAS-POLICY`, `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not construct the definitional
  reward-coordinate source law, integrability, sub-Gaussian witnesses, the
  ambient trajectory-to-`condExpKernel` identification, or a final adaptive
  theorem.  If the source fields are unavailable, first construct the source
  or use a more primitive law-identification route.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT` is
compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairMapSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  action_generated :
    action =
      Policy.generatedActionTraceSucc policy
        (fun n omega =>
          state n (History.finiteRewardHistoryOfTrace (reward omega) n))
        defaultAction
  random_pair_map_eq_actual_action :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (condExpKernel mu
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le i)))

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ... i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc action reward haction hreward).le i)))

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu) :
    Filter.EventuallyEq (ae mu)
      (condExp
        (m := (History.historyFiltrationSucc action reward haction hreward) i)
        (μ := mu)
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real)))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: `GeneratedActionRandomPairMapSource` packages
  the equality `action = Policy.generatedActionTraceSucc ... defaultAction`
  and a per-step random next-pair map law under generated
  `History.historyFiltrationSucc`.  The first theorem consumes this source and
  concludes the full finite-pair-trace `partialTraj` law.  The second theorem
  adds `RewardKernel.CenteredRewardKernelLaw` plus ambient centered-reward
  integrability and concludes ordinary succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`, importing
  `BanditRLProof.ConditionalExpectationReward`; it consumes
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`.
- Intended proof route: read the source fields, pass
  `source.action_generated` and
  `source.random_pair_map_eq_actual_action i` into the previously compiled
  generated-action/random-pair route, and leave integrability explicit for the
  conditional mean-zero consumer.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated shifted
  policy trace equality, per-step random next-pair conditional map law, and
  explicit centered-reward integrability for the final mean-zero theorem.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource`.
- Status: project-local compiled source-contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is a packaging/consumer contract.  It does not prove
  the generated random-pair law source, ambient trajectory-to-`condExpKernel`
  identification, centered-reward integrability, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionRandomPairMapSource mu action rewardKernel policy context
        state defaultAction reward haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a packaged
  `GeneratedActionRandomPairMapSource` directly gives the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` law for the next
  `(Action, Reward)` pair under
  `History.historyFiltrationSucc`, with the reward-history `context/state`
  lifted to pair histories through `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`, importing
  `BanditRLProof.ConditionalExpectationReward`; it calls
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action`,
  uses `GeneratedActionRandomPairMapSource.action_generated`,
  `GeneratedActionRandomPairMapSource.random_pair_map_eq_actual_action`,
  `History.pairHistoryRewardProjection`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`, and
  `History.measurable_pairHistoryRewardProjection`.
- Intended proof route: rewrite the source's generated-action equality from
  reward-history state form into pair-history state form using
  `pairHistoryRewardProjection_finitePairHistoryOfTrace`, rewrite the
  source's random next-pair map law through the same projection, then call the
  canonical random-pair history-step law adapter.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, measurable
  reward-history `context/state`, and the packaged generated random-pair map
  source.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-CONTRACT` and
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-RANDOM-PAIR-HISTORYSTEP-LAW`.
- Status: project-local compiled source-level canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `MEAS-HISTORY`.
- Failure policy: this theorem does not construct the generated random-pair
  law source, does not prove the ambient trajectory-to-`condExpKernel`
  identification, does not derive integrability or sub-Gaussian witnesses, and
  does not close the final adaptive theorem.  If the source package is absent,
  work upstream on random-pair law construction instead of treating this
  adapter as evidence of completion.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource
    ...
    (hstate : forall n : Nat, Measurable (state n))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward

def ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward
```

- Exact Lean-facing statement: the first definition converts a
  `GeneratedActionRandomPairMapSource` plus reward-history state measurability
  into `GeneratedActionActualRewardMapSource`.  The second definition converts
  the definitional random-pair source into the definitional actual reward-map
  source, using the source's own `hstate` field to derive action
  measurability.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq`,
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq`,
  `GeneratedActionRandomPairMapSource`,
  `GeneratedActionActualRewardMapSource`,
  `GeneratedActionRandomPairDefinitionalMapSource`, and
  `GeneratedActionDefinitionalActualRewardMapSource`.
- Intended proof route: freeze the generated random action coordinate under
  the conditional kernel using the shifted generated-action equality and
  measurable reward-history state extractors; convert the random pair law to
  the frozen actual-action pair-product law; marginalize the frozen pair law
  through `Prod.snd`; store the resulting reward-coordinate map law in the
  weaker actual reward-map source structure.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, reward-history state
  measurability for action freezing, and the random next-pair conditional map
  law supplied by the source.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declarations are
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`
  and
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: do not treat this as construction of the random next-pair
  law.  It only weakens an already-supplied random-pair source into an
  actual-action reward-coordinate source; ambient trajectory-to-`condExpKernel`
  identification, integrability, sub-Gaussianity, and final adaptive ETC/UCB
  theorems remain open.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairCenteredSource` produces the weaker
  `GeneratedActionActualRewardMapSource` for the same generated action/reward
  traces, reward kernel, policy, context, state, and default action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the centered package, then feed them to the existing random-pair-to-actual
  reward-map conversion.  No new conditional-expectation or measure-map proof
  is introduced in this wrapper.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the centered
  source's state measurability, centered reward-kernel law, random next-pair
  map source, and per-step ambient integrability fields.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, centered-kernel law, integrability fields, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource
    ...
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairBoundedCenteredSource` produces the weaker
  `GeneratedActionActualRewardMapSource` for the same generated action/reward
  traces, reward kernel, policy, context, state, and default action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the bounded-centered package, then feed them to the existing
  random-pair-to-actual reward-map conversion.  The a.e. measurability and
  interval-bound fields remain available for integrability consumers but are
  not used by this weaker source interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the bounded-centered
  source's state measurability, centered reward-kernel law, random next-pair
  map source, per-step a.e. centered-reward measurability, and per-step a.e.
  interval bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, centered-kernel law, a.e. bound evidence, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionFromRewardHistory
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat) :
    Omega -> ActionTrace Action

theorem ConditionalExpectationReward.generatedActionFromRewardHistory_measurable

structure ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  hstate : forall n : Nat, Measurable (state n)
  random_pair_map_eq_actual_action : forall i : Nat, ...

def ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource
```

- Exact Lean-facing statement: `generatedActionFromRewardHistory` is the
  shifted policy-generated action trace whose state input is
  `state n (History.finiteRewardHistoryOfTrace (reward omega) n)`.
  `generatedActionFromRewardHistory_measurable` derives every action
  coordinate's ambient measurability from timewise reward measurability plus
  measurable state extractors.  `GeneratedActionRandomPairDefinitionalMapSource`
  then packages only the measurable state extractors and the per-step random
  next-pair map law for that definitional action trace.  The conversion def
  builds `GeneratedActionRandomPairMapSource`; the consumers expose the full
  finite-pair-trace `partialTraj` law and succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `Policy.generatedActionTraceSucc`,
  `Policy.measurable_generatedActionTraceSucc_eval_of_measurable_state`,
  `History.measurable_finiteRewardHistoryOfTrace`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`, and the
  existing map-source consumers.
- Intended proof route: compose measurable reward-history restriction with the
  measurable state extractor, feed that into the policy-generated action trace
  measurability theorem, use `rfl` for the generated-action equality in the
  conversion def, copy the random next-pair law field, and reuse the existing
  map-source consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractor, and the per-step random next-pair conditional map law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource`,
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource`.
- Status: project-local compiled source-contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is still a contract/consumer wrapper.  It does not prove
  the random next-pair law, ambient trajectory-to-`condExpKernel`
  identification, centered-reward integrability, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionRandomPairDefinitionalMapSource mu rewardKernel policy
        context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (generatedActionFromRewardHistory policy state defaultAction reward
              y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory policy state defaultAction
              reward omega)
            (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (generatedActionFromRewardHistory policy state defaultAction
              reward)
            reward
            (generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i)))
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalMapSource` directly gives the
  canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law
  for the definitional action trace
  `generatedActionFromRewardHistory policy state defaultAction reward`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `generatedActionFromRewardHistory`,
  `generatedActionFromRewardHistory_measurable`,
  `generatedActionRandomPairMapSource_of_definitionalMapSource`, and
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`.
- Intended proof route: convert the definitional source into the explicit
  `GeneratedActionRandomPairMapSource` using
  `generatedActionRandomPairMapSource_of_definitionalMapSource`, supply the
  derived timewise action measurability from
  `generatedActionFromRewardHistory_measurable`, then call the source-level
  canonical pair-law consumer.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractor from the source, and the definitional random next-pair
  conditional map law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-MAP-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-MAP-SOURCE-CONTRACT`
  and
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`.
- Status: project-local compiled definitional source-level canonical pair-law
  consumer for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not prove the definitional random next-pair
  law, ambient trajectory-to-`condExpKernel` identification, integrability,
  sub-Gaussianity, or final adaptive theorem.  It only removes explicit
  action-trace and `haction` parameters before the canonical pair-law surface.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT` is
compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  centered_integrable :
    forall i : Nat,
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource
```

- Exact Lean-facing statement: the structure packages `hcontext`, `hstate`,
  `RewardKernel.CenteredRewardKernelLaw`, the previously compiled
  `GeneratedActionRandomPairMapSource`, and a per-step ambient integrability
  field for the centered generated-policy reward.  The trajectory-law consumer
  reuses the map source and the packaged context/state measurability to expose
  the full finite-pair-trace `partialTraj` law.  The mean-zero consumer reuses
  the map source, `kernel_law`, and `centered_integrable i` to conclude
  ordinary succ-indexed conditional mean-zero without a separate
  `h_integrable` argument.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`,
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, `History.historyFiltrationSucc`, and
  `History.finiteRewardHistoryOfTrace`.
- Intended proof route: project the fields from `source`, pass
  `source.map_source` to the previously compiled random-pair source consumers,
  use `source.hcontext`/`source.hstate` for projected pair-history
  measurability, use `source.kernel_law` for the centered reward-kernel law,
  and use `source.centered_integrable i` for the final ordinary
  conditional-expectation theorem.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, and per-step ambient
  centered-reward integrability.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource`.
- Status: project-local compiled centered-source contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is still a contract/consumer wrapper.  It does not
  derive the random next-pair law, ambient integrability fields, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionRandomPairCenteredSource mu action rewardKernel policy
        context state mean varianceProxy defaultAction reward haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ... i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc action reward haction hreward).le i)))
```

- Exact Lean-facing statement: a packaged
  `GeneratedActionRandomPairCenteredSource` directly exposes the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` law for the next
  `(Action, Reward)` pair under `History.historyFiltrationSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `GeneratedActionRandomPairCenteredSource.map_source`,
  `GeneratedActionRandomPairCenteredSource.hcontext`,
  `GeneratedActionRandomPairCenteredSource.hstate`, and
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource`.
- Intended proof route: project `source.map_source` and
  `source.hcontext`/`source.hstate`, then call the source-level canonical
  pair-law consumer for `GeneratedActionRandomPairMapSource`.  The centered
  law and integrability fields are preserved for later consumers but are not
  needed by this theorem.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, and the packaged
  centered generated random-pair source.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-CENTERED-SOURCE-CONTRACT` and
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RANDOM-PAIR-SOURCE-TO-HISTORYSTEP-PAIR-LAW`.
- Status: project-local compiled centered-source canonical pair-law consumer
  for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not construct the random next-pair law,
  derive centered law/integrability fields, identify the ambient trajectory law
  with `condExpKernel`, prove sub-Gaussianity, or close a final adaptive
  theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      GeneratedActionRandomPairBoundedCenteredSource mu action rewardKernel
        policy context state mean varianceProxy defaultAction reward haction
        hreward lo hi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ... i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc action reward haction hreward).le i)))
```

- Exact Lean-facing statement: a packaged
  `GeneratedActionRandomPairBoundedCenteredSource` directly exposes the
  canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law
  under `History.historyFiltrationSucc`, with the same projected
  pair-history context/state surface as the centered-source theorem.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `GeneratedActionRandomPairBoundedCenteredSource`,
  `generatedActionRandomPairCenteredSource_of_boundedCenteredSource`, and
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`.
- Intended proof route: lower the bounded-centered source to
  `GeneratedActionRandomPairCenteredSource` using the existing
  integrability-from-bounds conversion, then reuse the centered-source
  canonical pair-law consumer unchanged.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, per-step a.e.
  measurability, and per-step a.e. interval bounds for the centered reward.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT`
  and
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`.
- Status: project-local compiled bounded-centered-source canonical pair-law
  consumer for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this theorem does not construct the random next-pair law,
  derive the a.e. bound evidence, identify the ambient trajectory law with
  `condExpKernel`, prove sub-Gaussianity, or close a final adaptive theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) where
  hcontext : forall n : Nat, Measurable (context n)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  definitional_map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
      mu rewardKernel policy context state defaultAction reward hreward
  centered_integrable :
    forall i : Nat,
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu

def ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource
```

- Exact Lean-facing statement: the structure packages `hcontext`, a centered
  reward-kernel law, a definitional generated random-pair map source, and
  per-step ambient integrability of the generated centered reward.  The
  conversion exposes the corresponding explicit
  `GeneratedActionRandomPairCenteredSource` whose action trace is
  `generatedActionFromRewardHistory`; the two consumers expose the full
  finite-pair-trace `partialTraj` law and ordinary succ-indexed conditional
  mean-zero directly from that definitional centered source.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource`.
- Intended proof route: derive the explicit action trace and its timewise
  measurability from `generatedActionFromRewardHistory` and
  `source.definitional_map_source.hstate`, turn the packaged definitional map
  source into an explicit random-pair map source, copy `hcontext`,
  `kernel_law`, and `centered_integrable`, then reuse the centered-source
  consumers unchanged.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractor packaged in the definitional map source, definitional random
  next-pair source contract, centered reward-kernel law, and per-step ambient
  centered-reward integrability.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource`.
- Status: project-local compiled definitional centered-source contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is still a contract/consumer wrapper.  It does not
  derive the definitional random next-pair law, centered-reward integrability,
  ambient trajectory-to-`condExpKernel` identification, sub-Gaussianity, or
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      GeneratedActionRandomPairDefinitionalCenteredSource mu rewardKernel
        policy context state mean varianceProxy defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega =>
            (generatedActionFromRewardHistory policy state defaultAction reward
              y (i + 1), reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ... i
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory policy state defaultAction
              reward omega)
            (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc
          (generatedActionFromRewardHistory policy state defaultAction reward)
          reward
          (generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward source.definitional_map_source.hstate)
          hreward).le i)))
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalCenteredSource` directly exposes the
  canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law
  over `generatedActionFromRewardHistory`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `GeneratedActionRandomPairDefinitionalCenteredSource.definitional_map_source`,
  `generatedActionRandomPairCenteredSource_of_definitionalCenteredSource`,
  `generatedActionFromRewardHistory_measurable`, and
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource`.
- Intended proof route: convert the definitional centered source into the
  explicit centered source over `generatedActionFromRewardHistory`, derive
  timewise action measurability from the packaged state measurability, then
  call the centered-source canonical pair-law consumer.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, packaged definitional
  random-pair source, centered reward-kernel law, and packaged per-step
  centered-reward integrability.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-CONTRACT`
  and
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`.
- Status: project-local compiled definitional centered-source canonical
  pair-law consumer for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`,
  `MEAS-POLICY`, `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this theorem does not construct the definitional random
  next-pair law, derive centered law/integrability fields, identify the
  ambient trajectory law with `condExpKernel`, prove sub-Gaussianity, or close
  a final adaptive theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat) :
    Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalCenteredSource` exposes ambient
  integrability of the generated centered successor reward at each time `i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  `History.finiteRewardHistoryOfTrace`, and Mathlib `MeasureTheory.Integrable`.
- Intended proof route: project the packaged field
  `source.centered_integrable i`.  No boundedness or measurability derivation is
  performed in this leaf.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, definitional random-pair map
  source packaged in the centered source, centered reward-kernel law packaged in
  the source, and the per-step integrability field itself.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-CENTERED-SOURCE-INTEGRABILITY`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource`.
- Status: project-local compiled integrability projection leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this is not a boundedness-derived integrability theorem.  It
  does not derive centered integrability, the definitional random next-pair
  law, ambient trajectory-to-`condExpKernel` identification, sub-Gaussianity, or
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalCenteredSource` weakens to
  `GeneratedActionRandomPairMapSource` whose explicit action trace is
  `generatedActionFromRewardHistory policy state defaultAction reward`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  and
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`.
- Intended proof route: project `source.definitional_map_source` into
  `generatedActionRandomPairMapSource_of_definitionalMapSource`.  The centered
  reward-kernel law, context measurability, and centered integrability fields
  are deliberately unused because the target map-source interface only needs
  the packaged definitional random-pair source and generated action
  measurability.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractor from the packaged definitional map source, and the
  source-packaged definitional random next-pair law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is not a new random-pair law construction.  It does not
  derive the definitional random next-pair law, centered-kernel law,
  centered-reward integrability, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalCenteredSource` weakens to
  `GeneratedActionDefinitionalActualRewardMapSource` with the same reward
  kernel, generated policy, context/state maps, default action, reward trace,
  and reward-trace measurability witness.  The generated action trace remains
  definitionally `generatedActionFromRewardHistory`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`,
  and
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`.
- Intended proof route: project `source.definitional_map_source` into
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`.
  The centered reward-kernel law, context measurability, and ambient
  centered-reward integrability fields are deliberately unused because the
  target definitional actual-reward-map interface only needs the packaged
  definitional random-pair source.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace through the definitional map source, the source-packaged
  definitional random next-pair law, and the centered-source fields retained
  for stronger consumers.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is not a new reward-law construction.  It does not
  derive the definitional random next-pair law, centered-kernel law,
  centered-reward integrability, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalCenteredSource` weakens to the explicit
  `GeneratedActionActualRewardMapSource` whose action trace is
  `generatedActionFromRewardHistory policy state defaultAction reward`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource`,
  and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`.
- Intended proof route: first project the definitional centered source into the
  definitional actual-reward-map source, then reuse the existing
  definitional-to-explicit actual reward-map conversion.  The explicit action
  measurability proof is supplied by
  `generatedActionFromRewardHistory_measurable` using
  `source.definitional_map_source.hstate`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractor from the packaged definitional map source, and the
  source-packaged definitional random next-pair law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-CENTERED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, and `KERNEL-REWARD`.
- Failure policy: this is still a source-interface projection.  It does not
  derive the definitional random next-pair law, centered regularity fields,
  ambient trajectory-to-`condExpKernel` identification, sub-Gaussianity, or a
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  centered_aemeasurable :
    forall i : Nat, AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu
  centered_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (lo i) (hi i)
            (((reward omega (i + 1) -
              mean
                (context i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))
                ((policy i).action
                  (state i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real)))
        (ae mu)

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource

def ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource
```

- Exact Lean-facing statement: the bounded-centered structure packages the
  same generated random-pair source, context/state measurability, and centered
  reward-kernel law as the centered source, but replaces direct
  `centered_integrable` assumptions by per-step `AEMeasurable` evidence and
  a.e. interval bounds `Set.Icc (lo i) (hi i)` for the generated centered
  successor reward.  The integrability theorem derives the missing field, the
  conversion def builds `GeneratedActionRandomPairCenteredSource`, and the two
  consumers expose full finite-pair-trace `partialTraj` law and succ-indexed
  conditional mean-zero directly from the bounded source.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `MeasureTheory.Integrable.of_mem_Icc`,
  `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, `History.historyFiltrationSucc`, and
  `History.finiteRewardHistoryOfTrace`.
- Intended proof route: apply `MeasureTheory.Integrable.of_mem_Icc` to
  `source.centered_aemeasurable i` and `source.centered_bound i`, construct a
  centered source by copying the structural fields and filling
  `centered_integrable`, then reuse the centered-source consumers unchanged.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, and per-step a.e.
  measurability plus a.e. interval bound for the centered generated reward.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-BOUNDED-CENTERED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource`,
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource`.
- Status: project-local compiled bounded-centered source contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this is still a bounded contract/consumer wrapper.  It does
  not derive the random next-pair law, a.e. bound evidence, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  raw_reward_aemeasurable :
    forall i : Nat,
      AEMeasurable
        (fun omega : Omega => (((reward omega (i + 1) : Rat) : Real))) mu
  selected_mean_aemeasurable :
    forall i : Nat,
      AEMeasurable
        (fun omega : Omega =>
          (((mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu
  raw_reward_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (rewardLo i) (rewardHi i)
            (((reward omega (i + 1) : Rat) : Real)))
        (ae mu)
  selected_mean_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (meanLo i) (meanHi i)
            (((mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
        (ae mu)

theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource

def ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource
```

- Exact Lean-facing statement: the raw/mean bounded source packages the same
  generated random-pair source, context/state measurability, and centered
  reward-kernel law as the bounded-centered source, but replaces direct
  centered a.e. measurability and direct centered interval bounds by separate
  raw reward and selected mean a.e. measurability plus interval bounds.  The
  centered bound interval is
  `Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)`.  The conversion
  def builds `GeneratedActionRandomPairBoundedCenteredSource`, and the
  consumers expose generated centered-reward integrability, full
  finite-pair-trace `partialTraj` law, and succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `AEMeasurable.sub`, `Rat.cast_sub`, `Set.Icc`, `linarith`,
  `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, `History.historyFiltrationSucc`, and
  `History.finiteRewardHistoryOfTrace`.
- Intended proof route: derive centered a.e. measurability from
  `source.raw_reward_aemeasurable i` and `source.selected_mean_aemeasurable i`
  with `AEMeasurable.sub`, using `Rat.cast_sub` to align the target.  Derive
  the centered interval bound by filtering upward through
  `source.raw_reward_bound i` and `source.selected_mean_bound i`, then using
  interval arithmetic.  Construct the bounded-centered source with bounds
  `(rewardLo i - meanHi i, rewardHi i - meanLo i)` and reuse the compiled
  bounded-centered source consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, and per-step raw
  reward plus selected mean a.e. measurability/bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource`.
- Status: project-local compiled raw/mean bounded source contract leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the generated random next-pair law, raw reward bounds, selected mean
  measurability/bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      GeneratedActionRandomPairRawMeanBoundedSource mu action rewardKernel
        policy context state mean varianceProxy defaultAction reward haction
        hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ... i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae (mu.trim
        ((History.historyFiltrationSucc action reward haction hreward).le i)))
```

- Exact Lean-facing statement: a packaged
  `GeneratedActionRandomPairRawMeanBoundedSource` directly exposes the
  canonical `RewardKernel.actionRewardHistoryStepKernelFamily` next-pair law
  under `History.historyFiltrationSucc`, with the pair-history projected
  context/state arguments inherited from the source fields.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `GeneratedActionRandomPairRawMeanBoundedSource`,
  `generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource`,
  and
  `actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource`.
- Intended proof route: lower the raw/mean bounded source to
  `GeneratedActionRandomPairBoundedCenteredSource` with bounds
  `(rewardLo i - meanHi i, rewardHi i - meanLo i)`, then reuse the
  bounded-centered canonical pair-law consumer unchanged.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, raw reward a.e.
  measurability/bounds, and selected mean a.e. measurability/bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  compiled declaration
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`;
  it builds on
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-MEAN-BOUNDED-SOURCE-CONTRACT`
  and
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-BOUNDED-CENTERED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`.
- Status: project-local compiled raw/mean bounded canonical pair-law consumer
  for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this theorem does not construct the random next-pair law,
  derive raw/mean bound evidence, identify the ambient trajectory law with
  `condExpKernel`, prove sub-Gaussianity, or close a final adaptive theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource
    ...
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawMeanBoundedSource` produces the weaker
  `GeneratedActionActualRewardMapSource` for the same generated action/reward
  traces, reward kernel, policy, context, state, and default action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the raw/mean bounded package, then feed them to the existing
  random-pair-to-actual reward-map conversion.  The raw-reward and
  selected-mean a.e. measurability/bound fields remain available for
  centered-bound and integrability consumers but are not used by this weaker
  source interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the raw/mean bounded
  source's state measurability, centered reward-kernel law, random next-pair
  map source, raw reward a.e. measurability/bounds, and selected mean a.e.
  measurability/bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, and `INT-REWARD-BOUNDED`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, raw reward bound evidence, selected mean
  measurability/bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  selected_mean_aemeasurable :
    forall i : Nat,
      AEMeasurable
        (fun omega : Omega =>
          (((mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu
  raw_reward_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (rewardLo i) (rewardHi i)
            (((reward omega (i + 1) : Rat) : Real)))
        (ae mu)
  selected_mean_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (meanLo i) (meanHi i)
            (((mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
        (ae mu)

theorem ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward

def ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource
```

- Exact Lean-facing statement: the raw-bound/mean-bounded source packages the
  same generated random-pair source, context/state measurability, centered
  reward-kernel law, raw reward interval bounds, and selected mean
  a.e. measurability/bounds as the raw/mean bounded source, but removes the
  separate raw reward `AEMeasurable` field.  The theorem
  `rawReward_succ_aemeasurable_of_measurable_reward` derives Rat-to-Real raw
  reward a.e. measurability from the existing timewise reward trace
  measurability `hreward`.  The conversion def builds
  `GeneratedActionRandomPairRawMeanBoundedSource`, and the consumers expose
  centered a.e. measurability, centered bounds, integrability, full
  finite-pair-trace `partialTraj` law, and succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `measurable_of_countable`, `Measurable.comp`, `Measurable.aemeasurable`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, and `History.historyFiltrationSucc`.
- Intended proof route: compose the timewise measurable reward coordinate
  `hreward (i + 1)` with the countable-domain measurable cast
  `(fun reward : Rat => ((reward : Rat) : Real))`, turn the result into
  `AEMeasurable`, construct the raw/mean bounded source by copying the
  remaining fields, then reuse the raw/mean bounded source consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, raw reward interval
  bounds, and selected mean a.e. measurability/bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEAN-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward`,
  `ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource`.
- Status: project-local compiled raw-bound/mean-bounded source contract leaf
  for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the generated random next-pair law, raw reward interval bounds,
  selected mean measurability/bounds, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        MeasureTheory.Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (ProbabilityTheory.condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` produces, for each
  step `i`, the trim-a.e. equality between the conditional-kernel pushforward
  of the actual next action/reward pair `(action y (i + 1), reward y (i + 1))`
  and the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` at
  `History.finitePairHistoryOfTrace (action omega) (reward omega) i`, with
  context/state lifted through `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`,
  `ProbabilityTheory.condExpKernel`, `MeasureTheory.Measure.map`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: convert the raw-bound/mean-bounded source into the
  raw/mean bounded source via
  `generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource`,
  then apply the already compiled raw/mean bounded history-step pair-law
  consumer.  No new measure-map algebra is required in this leaf.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the packaged
  generated random next-pair map source, centered reward-kernel law, raw
  reward interval bounds, selected mean a.e. measurability/bounds, and the
  raw-reward a.e. measurability derived from `hreward` by the source
  conversion.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration is
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`.
- Status: project-local compiled canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is a source-layer projection/consumer.  It does not
  construct the random next-pair law, raw reward interval bounds, selected
  mean measurability/bounds, ambient `partialTraj`/history-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource
    ...
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeanBoundedSource` produces the weaker
  `GeneratedActionActualRewardMapSource` for the same generated action/reward
  traces, reward kernel, policy, context, state, and default action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the raw-bound/mean-bounded package, then feed them to the existing
  random-pair-to-actual reward-map conversion.  The raw reward bound and
  selected-mean a.e. measurability/bound fields remain available for
  centered-bound and integrability consumers but are not used by this weaker
  source interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the raw-bound/mean
  bounded source's state measurability, centered reward-kernel law, random
  next-pair map source, raw reward interval bounds, and selected mean
  a.e. measurability/bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, raw reward interval bounds, selected mean
  measurability/bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  mean_measurable :
    Measurable (fun pair : Prod Context Action => mean pair.1 pair.2)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  raw_reward_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (rewardLo i) (rewardHi i)
            (((reward omega (i + 1) : Rat) : Real)))
        (ae mu)
  selected_mean_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (meanLo i) (meanHi i)
            (((mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
        (ae mu)

theorem ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean

def ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
```

- Exact Lean-facing statement: the raw-bound/measurable-mean source packages
  the same generated random-pair source, context/state measurability, centered
  reward-kernel law, raw reward bounds, and selected mean bounds as the
  raw-bound/mean-bounded source, but replaces the selected mean
  `AEMeasurable` field with
  `Measurable (fun pair : Prod Context Action => mean pair.1 pair.2)`.  The
  theorem `selectedMean_succ_aemeasurable_of_measurable_mean` derives
  Rat-to-Real selected mean a.e. measurability by composing the measurable
  finite reward history, context, state, policy action, and mean surface.  The
  conversion def builds `GeneratedActionRandomPairRawBoundMeanBoundedSource`,
  and the consumers expose centered a.e. measurability, centered bounds,
  integrability, full finite-pair-trace `partialTraj` law, and succ-indexed
  conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `History.measurable_finiteRewardHistoryOfTrace`,
  `Policy.MeasurablePolicy.measurable_action`, `Measurable.comp`,
  `Measurable.prodMk`, `measurable_of_countable`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, and
  `History.historyFiltrationSucc`.
- Intended proof route: first derive selected mean a.e. measurability from
  `hreward`, `hcontext`, `hstate`, policy action measurability, and
  `mean_measurable`; construct the raw-bound/mean-bounded source by copying the
  remaining fields; then reuse the raw-bound/mean-bounded source consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, raw reward interval
  bounds, selected mean interval bounds, and a measurable mean surface.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`.
- Status: project-local compiled raw-bound/measurable-mean source contract leaf
  for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the generated random next-pair law, raw reward interval bounds,
  selected mean interval bounds, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        MeasureTheory.Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (ProbabilityTheory.condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` produces, for
  each step `i`, the trim-a.e. equality between the conditional-kernel
  pushforward of the actual next action/reward pair
  `(action y (i + 1), reward y (i + 1))` and the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` at
  `History.finitePairHistoryOfTrace (action omega) (reward omega) i`, with
  context/state lifted through `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`,
  `ProbabilityTheory.condExpKernel`, `MeasureTheory.Measure.map`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: convert the raw-bound/measurable-mean source into the
  raw-bound/mean-bounded source via
  `generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource`,
  then apply the already compiled raw-bound/mean-bounded history-step
  pair-law consumer.  No new pushforward algebra or selected-mean
  measurability proof is needed in this leaf.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the packaged
  generated random next-pair map source, centered reward-kernel law, raw
  reward interval bounds, selected mean interval bounds, and a measurable
  selected-mean surface.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration is
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`.
- Status: project-local compiled canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this is a source-layer projection/consumer.  It does not
  construct the random next-pair law, raw reward interval bounds, selected
  mean interval bounds, ambient `partialTraj`/history-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource
    ...
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource` produces the
  weaker `GeneratedActionActualRewardMapSource` for the same generated
  action/reward traces, reward kernel, policy, context, state, and default
  action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the raw-bound/measurable-mean package, then feed them to the existing
  random-pair-to-actual reward-map conversion.  The measurable mean surface,
  raw reward bounds, and selected mean bounds remain available for
  centered-bound and integrability consumers but are not used by this weaker
  source interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the
  raw-bound/measurable-mean source's state measurability, centered
  reward-kernel law, random next-pair map source, raw reward interval bounds,
  selected mean interval bounds, and a measurable mean surface.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, raw reward interval bounds, selected mean interval
  bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  mean_measurable :
    Measurable (fun pair : Prod Context Action => mean pair.1 pair.2)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  raw_reward_bound :
    forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          Set.Icc (rewardLo i) (rewardHi i)
            (((reward omega (i + 1) : Rat) : Real)))
        (ae mu)
  mean_range_bound :
    forall i : Nat, forall context : Context, forall action : Action,
      Set.Icc (meanLo i) (meanHi i)
        (((mean context action : Rat) : Real))

theorem ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound

def ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
```

- Exact Lean-facing statement: the raw-bound/measurable-mean-range source
  packages the generated random-pair source, context/state measurability,
  mean measurability, centered reward-kernel law, and raw reward bounds, but
  replaces the selected mean a.e. bound field with the deterministic pointwise
  contract
  `forall i context action, Set.Icc (meanLo i) (meanHi i)
    (((mean context action : Rat) : Real))`.  The theorem
  `selectedMean_succ_bound_of_mean_range_bound` turns that deterministic range
  into the generated selected-mean a.e. bound.  The conversion def builds
  `GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`, and the
  consumers expose centered a.e. measurability, centered bounds, integrability,
  full finite-pair-trace `partialTraj` law, and succ-indexed conditional
  mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `Filter.Eventually.of_forall`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, and
  `History.finiteRewardHistoryOfTrace`.
- Intended proof route: instantiate the pointwise mean range bound at
  `context i (History.finiteRewardHistoryOfTrace (reward omega) i)` and
  `(policy i).action (state i (...))`, lift it to an a.e. statement with
  `Filter.Eventually.of_forall`, construct the measurable-mean bounded source
  by copying the remaining fields, then reuse the measurable-mean source
  consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, raw reward interval
  bounds, measurable mean surface, and deterministic pointwise mean range
  bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled raw-bound/measurable-mean-range source
  contract leaf for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the generated random next-pair law, raw reward interval bounds,
  mean measurability, deterministic mean range bounds, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        MeasureTheory.Measure.map
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (ProbabilityTheory.condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`
  produces, for each step `i`, the trim-a.e. equality between the
  conditional-kernel pushforward of the actual next action/reward pair
  `(action y (i + 1), reward y (i + 1))` and the canonical
  `RewardKernel.actionRewardHistoryStepKernelFamily` at
  `History.finitePairHistoryOfTrace (action omega) (reward omega) i`, with
  context/state lifted through `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource`,
  `History.historyFiltrationSucc`, `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`,
  `ProbabilityTheory.condExpKernel`, `MeasureTheory.Measure.map`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: convert the raw-bound/measurable-mean-range source
  into the raw-bound/measurable-mean source via
  `generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource`,
  then apply the already compiled raw-bound/measurable-mean history-step
  pair-law consumer.  No new measure-map algebra or deterministic mean-range
  proof is needed in this leaf.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the packaged
  generated random next-pair map source, centered reward-kernel law, raw
  reward interval bounds, measurable mean surface, and deterministic pointwise
  mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration is
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this is a source-layer projection/consumer.  It does not
  construct the random next-pair law, raw reward interval bounds, mean
  measurability, deterministic mean range bounds, ambient
  `partialTraj`/history-to-`condExpKernel` identification, sub-Gaussianity,
  or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource
    ...
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`
  produces the weaker `GeneratedActionActualRewardMapSource` for the same
  generated action/reward traces, reward kernel, policy, context, state, and
  default action.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: project `source.hstate` and `source.map_source` from
  the raw-bound/measurable-mean-range package, then feed them to the existing
  random-pair-to-actual reward-map conversion.  The measurable mean surface,
  raw reward bounds, and deterministic mean range bounds remain available for
  centered-bound and integrability consumers but are not used by this weaker
  source interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, the
  raw-bound/measurable-mean-range source's state measurability, centered
  reward-kernel law, random next-pair map source, raw reward interval bounds,
  measurable mean surface, and deterministic pointwise mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-BOUND-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is a projection/weakening wrapper.  It does not derive
  the random next-pair law, raw reward interval bounds, mean measurability,
  deterministic mean range bounds, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  hstate : forall n : Nat, Measurable (state n)
  mean_measurable :
    Measurable (fun pair : Prod Context Action => mean pair.1 pair.2)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
  raw_reward_range_bound :
    forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real))
  mean_range_bound :
    forall i : Nat, forall context : Context, forall action : Action,
      Set.Icc (meanLo i) (meanHi i)
        (((mean context action : Rat) : Real))

theorem ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound

def ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
```

- Exact Lean-facing statement: the raw-range/measurable-mean-range source
  packages the generated random-pair source, context/state measurability,
  mean measurability, centered reward-kernel law, deterministic pointwise raw
  reward range bounds, and deterministic pointwise mean range bounds.  It
  replaces the raw reward a.e. bound field with the pointwise contract
  `forall i omega, Set.Icc (rewardLo i) (rewardHi i)
    (((reward omega (i + 1) : Rat) : Real))`.  The theorem
  `rawReward_succ_bound_of_reward_range_bound` turns that deterministic
  reward-trace range into the generated raw-reward a.e. bound.  The conversion
  def builds
  `GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`, and the
  consumers expose centered a.e. measurability, centered bounds, integrability,
  full finite-pair-trace `partialTraj` law, and succ-indexed conditional
  mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `Filter.Eventually.of_forall`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `RewardKernel.CenteredRewardKernelLaw`, and
  `History.finiteRewardHistoryOfTrace`.
- Intended proof route: instantiate the pointwise reward range bound at
  `reward omega (i + 1)`, lift it to an a.e. statement with
  `Filter.Eventually.of_forall`, construct the raw-bound/measurable-mean-range
  source by copying the remaining fields, then reuse the existing
  raw-bound/measurable-mean-range consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, measurable mean
  surface, deterministic pointwise raw reward range bounds, and deterministic
  pointwise mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled raw-range/measurable-mean-range source
  contract leaf for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`,
  `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the generated random next-pair law, mean measurability, deterministic
  raw reward or mean range bounds, ambient trajectory-to-`condExpKernel`
  identification, sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega =>
        Measure.map
          (fun y => (action y (i + 1), reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ...
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le i)))
```

- Exact Lean-facing statement: under the raw-reward-range/measurable-mean-range
  generated random-pair source, the conditional kernel pushforward of the next
  action/reward pair `(action y (i + 1), reward y (i + 1))` is trim-a.e. equal
  to `RewardKernel.actionRewardHistoryStepKernelFamily` evaluated at
  `History.finitePairHistoryOfTrace (action omega) (reward omega) i`, with
  pair-history context/state maps obtained by
  `History.pairHistoryRewardProjection`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`, and
  `History.measurable_pairHistoryRewardProjection`.
- Intended proof route: lower the source through
  `generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource`,
  then reuse the raw-bound/measurable-mean-range canonical pair-law theorem.
  The proof is a direct source-layer projection; no new measure manipulation is
  introduced.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, centered reward-kernel law, measurable mean
  surface, deterministic pointwise raw reward range bounds, and deterministic
  pointwise mean range bounds.  The theorem still uses trim-a.e. conditioning
  over `History.historyFiltrationSucc`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration is
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a construction of the generated random next-pair
  law and does not identify ambient `partialTraj`/history with
  `condExpKernel`.  If future proof search needs those facts, create separate
  leaves rather than weakening this consumer's statement.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    ...
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource` weakens
  to `GeneratedActionActualRewardMapSource` with the same action/reward trace,
  reward kernel, generated policy, context/state maps, default action, and
  timewise measurability witnesses.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`, and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource`.
- Intended proof route: feed `source.hstate` and `source.map_source` into
  `generatedActionActualRewardMapSource_of_randomPairMapSource`.  The raw
  reward range, mean range, mean measurability, centered-kernel law, and
  integrability-facing fields are deliberately unused because the target
  actual-reward-map interface only needs state measurability and the packaged
  random-pair map source.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable action/reward traces, generated random
  next-pair source contract, and source-packaged state measurability.  The
  deterministic raw reward and mean range bounds remain available for stronger
  consumers but are not required by this projection.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a new reward-law construction.  It does not
  derive the random next-pair law, deterministic raw reward or mean range
  bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`
is compiled locally:

```lean
structure ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real) where
  hcontext : forall n : Nat, Measurable (context n)
  mean_measurable :
    Measurable (fun pair : Prod Context Action => mean pair.1 pair.2)
  kernel_law :
    RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy
  definitional_map_source :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
      mu rewardKernel policy context state defaultAction reward hreward
  raw_reward_range_bound :
    forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real))
  mean_range_bound :
    forall i : Nat, forall context : Context, forall action : Action,
      Set.Icc (meanLo i) (meanHi i)
        (((mean context action : Rat) : Real))

def ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
```

- Exact Lean-facing statement: the definitional raw-range/measurable-mean-range
  source packages the practical generated-policy bounded reward interface
  without a separate `action : Omega -> ActionTrace Action` parameter or
  `haction` proof.  The action trace is fixed to
  `generatedActionFromRewardHistory policy state defaultAction reward`, and
  `GeneratedActionRandomPairDefinitionalMapSource` supplies the derived
  timewise action measurability plus the remaining random next-pair law
  contract.  The conversion def builds
  `GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`, and the
  consumers expose ambient integrability, full finite-pair-trace `partialTraj`
  law, and succ-indexed conditional mean-zero.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`, and
  `RewardKernel.CenteredRewardKernelLaw`.
- Intended proof route: derive `haction` with
  `generatedActionFromRewardHistory_measurable`, convert the definitional map
  source with `generatedActionRandomPairMapSource_of_definitionalMapSource`,
  copy context measurability, centered kernel law, mean measurability, and
  deterministic range bounds into the existing explicit-action raw-range
  source, then reuse the explicit-action raw-range integrability,
  `partialTraj`, and conditional mean-zero consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractors via the definitional map source, measurable context
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic pointwise raw reward range bounds, deterministic pointwise mean
  range bounds, and the definitional random next-pair law source.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-CONTRACT`;
  declarations are
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled definitional raw-range/measurable-mean-range
  source contract leaf for `COND-EXPECT-REWARD`, `ADAPTED-ACTION`,
  `MEAS-POLICY`, `MEAS-HISTORY`, `KERNEL-POLICY-BIND`, `KERNEL-REWARD`,
  `INT-REWARD-BOUNDED`, and `MEAS-REWARD`.
- Failure policy: this remains a contract/consumer wrapper.  It does not
  derive the definitional random next-pair law, mean measurability,
  deterministic raw reward or mean range bounds, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`
is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega =>
        Measure.map
          (fun y =>
            (generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (condExpKernel mu
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable
                hreward source.definitional_map_source.hstate)) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          ...
          i
          (History.finitePairHistoryOfTrace
            (generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc
            (generatedActionFromRewardHistory policy state defaultAction reward)
            reward
            (generatedActionFromRewardHistory_measurable
              hreward source.definitional_map_source.hstate)).le i)))
```

- Exact Lean-facing statement: for the practical definitional
  raw-range/measurable-mean-range generated random-pair source, the
  conditional kernel pushforward of the generated successor action and raw
  successor reward is trim-a.e. equal to
  `RewardKernel.actionRewardHistoryStepKernelFamily`, evaluated at the finite
  pair history built from `generatedActionFromRewardHistory` and `reward`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`, and
  `History.measurable_pairHistoryRewardProjection`.
- Intended proof route: derive the generated action measurability witness via
  `generatedActionFromRewardHistory_measurable`, lower the definitional source
  through
  `generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  then reuse the explicit raw-range/measurable-mean-range history-step pair-law
  theorem.  No new measure-theoretic argument is introduced.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, measurable reward-history
  state extractors through the definitional map source, measurable context
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic pointwise raw reward range bounds, deterministic pointwise mean
  range bounds, and the definitional random next-pair law source.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-HISTORYSTEP-PAIR-LAW`;
  declaration is
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled canonical pair-law consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a construction of the definitional random
  next-pair law and does not identify ambient `partialTraj`/history with
  `condExpKernel`.  If those facts are needed, create separate local leaves;
  do not weaken this theorem's statement.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens directly to the explicit `GeneratedActionRandomPairMapSource` whose
  action trace is
  `generatedActionFromRewardHistory policy state defaultAction reward`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  and
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource`.
- Intended proof route: project `source.definitional_map_source` through the
  existing definitional-to-explicit random-pair map source conversion.  This
  avoids constructing the full explicit raw-range source when a consumer only
  needs the lower random-pair map-law interface.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace, and the source-packaged definitional random next-pair map law.
  The centered-law, raw reward range, and mean range fields remain available
  for stronger consumers but are not required by this projection.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-RANDOM-PAIR-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a new random-pair law construction.  It does not
  derive the definitional random next-pair law, deterministic raw reward or
  mean range bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu

theorem ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu)
```

- Exact Lean-facing statement: the practical definitional
  raw-range/measurable-mean-range source directly yields a.e. measurability of
  the generated centered successor reward and the centered interval bound
  `[rewardLo i - meanHi i, rewardHi i - meanLo i]`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource`.
- Intended proof route: lower the definitional source to the explicit raw-range
  source using `generatedActionFromRewardHistory` and the packaged
  definitional map source, then reuse the compiled raw-range regularity
  consumers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace, source-packaged definitional random next-pair map law,
  measurable mean surface, centered kernel law, and deterministic raw reward
  and mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-CENTERED-REGULARITY`;
  declarations are
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  and
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled regularity leaf for `COND-EXPECT-REWARD`,
  `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this does not derive the definitional random next-pair law,
  deterministic raw reward or mean range bounds, ambient
  trajectory-to-`condExpKernel` identification, sub-Gaussianity, or final
  adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
      mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
      (fun i => rewardLo i - meanHi i)
      (fun i => rewardHi i - meanLo i)
```

- Exact Lean-facing statement: the practical definitional
  raw-range/measurable-mean-range source directly yields the bounded centered
  generated random-pair source over `generatedActionFromRewardHistory`, with
  lower and upper centered bounds
  `fun i => rewardLo i - meanHi i` and `fun i => rewardHi i - meanLo i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource`,
  `ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Intended proof route: fill the bounded-centered source fields directly.
  The context, centered kernel law, and definitional state measurability come
  from the source; the map-source field uses the existing definitional
  raw-range to explicit generated random-pair map projection; the centered
  a.e. measurability and interval-bound fields reuse the just-compiled
  definitional regularity wrappers.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace, source-packaged definitional random next-pair map law,
  measurable mean surface, centered kernel law, and deterministic raw reward
  and mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-BOUNDED-CENTERED-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a new random-pair law construction and does not
  prove sub-Gaussianity or a final adaptive ETC/UCB theorem.  It still assumes
  the definitional random next-pair law, mean measurability, deterministic raw
  reward and mean range bounds, and ambient trajectory-to-`condExpKernel`
  identification.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
      mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
```

- Exact Lean-facing statement: the practical definitional
  raw-range/measurable-mean-range source directly yields the
  integrability-based centered generated random-pair source over
  `generatedActionFromRewardHistory`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource`,
  `ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource`.
- Intended proof route: first build the bounded-centered source with lower and
  upper centered bounds `rewardLo i - meanHi i` and `rewardHi i - meanLo i`,
  then reuse the existing bounded-centered-to-centered conversion, which
  derives per-step integrability via `MeasureTheory.Integrable.of_mem_Icc`.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace, source-packaged definitional random next-pair map law,
  measurable mean surface, centered kernel law, and deterministic raw reward
  and mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-CENTERED-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this does not construct the definitional random next-pair
  law, ambient trajectory-to-`condExpKernel` identification, sub-Gaussian
  witnesses, or a final adaptive ETC/UCB theorem.  It only exposes the
  existing centered-source interface from the practical source contract.

`LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward
```

- Exact Lean-facing statement: the practical definitional
  raw-range/measurable-mean-range source directly yields
  `GeneratedActionRandomPairDefinitionalCenteredSource`, keeping the action
  trace implicit through `generatedActionFromRewardHistory`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource`,
  and
  `ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Intended proof route: project `hcontext`, `kernel_law`, and the packaged
  `definitional_map_source` directly from the practical source, then fill the
  definitional centered source's `centered_integrable` field with the existing
  bounded-derived integrability theorem.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, packaged definitional random
  next-pair map law, measurable mean surface, centered kernel law, and
  deterministic raw reward and mean range bounds.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-GENERATED-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-CENTERED-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this does not construct the definitional random next-pair
  law, ambient trajectory-to-`condExpKernel` identification, sub-Gaussian
  witnesses, or a final adaptive ETC/UCB theorem.  It only packages the
  already-derived regularity into the newer definitional centered-source
  interface.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens to `GeneratedActionDefinitionalActualRewardMapSource` with the same
  reward kernel, generated policy, context/state maps, default action, reward
  trace, and reward-trace measurability witness.  The action trace remains
  definitionally `generatedActionFromRewardHistory`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource`,
  and
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`.
- Intended proof route: project `source.definitional_map_source` into
  `generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource`.
  The deterministic raw reward range, mean range, context measurability, mean
  measurability, centered-kernel law, and integrability-facing fields are
  deliberately unused because the target definitional actual-reward-map
  interface only needs the packaged definitional random-pair source.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace through the definitional map source, and the source-packaged
  definitional random next-pair law.  The deterministic raw reward and mean
  range bounds remain available for stronger consumers but are not required by
  this projection.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-DEFINITIONAL-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a new reward-law construction.  It does not
  derive the definitional random next-pair law, deterministic raw reward or
  mean range bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
```

- Exact Lean-facing statement: a
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`
  weakens to the explicit `GeneratedActionActualRewardMapSource` whose action
  trace is `generatedActionFromRewardHistory policy state defaultAction reward`.
  The reward kernel, generated policy, context/state maps, default action,
  reward trace, reward-trace measurability witness, and generated-action
  measurability witness are inherited from the source package.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  `ConditionalExpectationReward.GeneratedActionActualRewardMapSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`,
  and
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource`.
- Intended proof route: first project the definitional raw-range source into
  `GeneratedActionDefinitionalActualRewardMapSource`, then reuse the existing
  definitional-to-explicit actual reward-map source conversion.  No new
  measure-map algebra is introduced in this wrapper.
- Regularity contracts: standard Borel sample space, finite measure,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable reward trace, generated reward-history
  action trace through the definitional map source, and the source-packaged
  definitional random next-pair law.  The deterministic raw reward and mean
  range bounds remain available for stronger consumers but are not required by
  this projection.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-RANDOM-PAIR-DEFINITIONAL-RAW-RANGE-MEASURABLE-MEAN-RANGE-BOUNDED-SOURCE-TO-ACTUAL-REWARD-MAP-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a new reward-law construction.  It does not
  derive the definitional random next-pair law, deterministic raw reward or
  mean range bounds, ambient trajectory-to-`condExpKernel` identification,
  sub-Gaussianity, or final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the first theorem proves ordinary conditional
  mean-zero for the succ-indexed centered reward using the concrete finite
  reward history `History.finiteRewardHistoryOfTrace (reward omega) i`, assuming
  next-reward measurability, prefix-coordinate measurability at `F i`,
  integrability, and the reward-coordinate pushforward identity from
  `condExpKernel mu (F i)` to `RewardKernel.historyStepKernelFamily`.  The
  second theorem specializes this to the generated shifted history filtration
  `History.historyFiltrationSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, consuming
  `centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`,
  `finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable`,
  `centeredReward_succ_frozenPast_ae_of_history_frozen`, and
  `History.measurable_reward_mem_historyFiltration_of_lt`.
- Intended proof route: build `history := History.finiteRewardHistoryOfTrace
  (reward omega) i`; use the finite-history measurability hookup to prove the
  history is frozen under the conditional kernel; use the frozen-history
  centered-target bridge to construct `h_kernel_X_eq`; feed that and the
  explicit `h_kernel_map_eq` into the existing map-law consumer.  The
  `historyFiltrationSucc` specialization supplies prefix-coordinate
  measurability from `History.measurable_reward_mem_historyFiltration_of_lt`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable context/state/action spaces, centered reward kernel law,
  next-reward measurability, centered-variable integrability, prefix reward
  coordinate measurability or generated history filtration hypotheses, and the
  explicit reward-coordinate pushforward equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP`; local inputs
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER` and
  `LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD` and
  `FILTRATION-HISTORY`.  It removes the separate frozen-past side condition
  from the map-law consumer under coordinate/generated-history measurability.
  The broad row remains `missing-leaf`.
- Failure policy: do not treat this as the reward-law identification.  The
  theorem still assumes the reward-coordinate pushforward equality from
  `condExpKernel` to `RewardKernel.historyStepKernelFamily`, so future work
  must prove that equality from the finite-prefix trajectory law.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER` is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega => 0)
```

- Exact Lean-facing statement: the theorem proves ordinary conditional
  mean-zero for the succ-indexed centered reward from a stronger next-step
  law assumption: under `condExpKernel mu (F i) omega`, the `(action, reward)`
  pair at time `i + 1` pushes forward to the local
  `RewardKernel.actionRewardHistoryStepKernelFamily` selected by
  `pairHistory omega`.  Pointwise compatibility hypotheses identify the
  pair-history context/state with the reward-history context/state used by the
  centered reward target.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, consuming
  `centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable`,
  Mathlib `Measure.map_map`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`.
- Intended proof route: map both sides of the assumed pair-law equality by
  `Prod.snd`; use `Measure.map_map` to rewrite the left side to the next
  reward-coordinate pushforward under `condExpKernel`; use
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map` to rewrite the
  right side to the reward-only selected law; then use the context/state
  compatibility hypotheses and feed the resulting reward-coordinate map law
  into the compiled map-law/frozen-past consumer.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable context/state/action spaces, next action and reward coordinate
  measurability, reward-prefix coordinate measurability at `F i`, centered
  integrability, centered reward kernel law, pair-history context/state
  measurability, and the explicit condExpKernel pair-law pushforward equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER`; local inputs
  `LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP`,
  `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER`, and
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD` and
  `KERNEL-POLICY-BIND`.  It moves the remaining map-law obligation from a
  reward-coordinate equality to an action/reward pair-law equality.
- Failure policy: do not treat this as a `partialTraj`/`condExpKernel`
  identification theorem.  It still assumes the pair-law pushforward equality;
  future work must prove that equality from the finite-prefix trajectory law
  and the chosen history filtration.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the theorem specializes the action/reward
  pair-map conditional mean-zero consumer to
  `History.historyFiltrationSucc action reward haction hreward`.  It proves
  ordinary conditional mean-zero for the succ-indexed centered reward while
  assuming the same action/reward pair-law pushforward identity, now stated at
  the generated history filtration level.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, consuming
  `centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable`;
  `History.historyFiltrationSucc`,
  `History.historyFiltrationSucc_apply`, and
  `History.measurable_reward_mem_historyFiltration_of_lt`.
- Intended proof route: instantiate the coordinate-measurable pair-map
  consumer with `F := History.historyFiltrationSucc action reward haction
  hreward`; supply next-coordinate measurability by `haction (i + 1)` and
  `hreward (i + 1)`; discharge each reward-prefix coordinate at `F i` with
  `History.measurable_reward_mem_historyFiltration_of_lt` plus
  `Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable context/state/action spaces, singleton-measurable action space,
  timewise measurable action and reward traces, context/state measurability,
  pair-history context/state measurability, centered reward kernel law,
  context/state compatibility between pair histories and reward histories,
  centered integrability, and the explicit generated-history `condExpKernel`
  action/reward pair-law pushforward equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP`; local
  inputs `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER`,
  `LOCAL-LEAF-HISTORY-FILTRATION`, and
  `LOCAL-LEAF-HISTORY-ADAPTED-COORDINATES`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `FILTRATION-HISTORY`, and `KERNEL-POLICY-BIND`.  It removes the explicit
  `F`, next-coordinate measurability, and reward-prefix measurability
  parameters from the pair-map consumer under generated history filtration.
- Failure policy: do not treat this as a trajectory-law theorem.  It still
  assumes the generated-history `condExpKernel` action/reward pair-law
  pushforward equality; future work must construct that equality from the
  finite-prefix `partialTraj` trajectory law and policy/history semantics.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP` is
compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hpairContext :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            context n (fun j : Finset.Iic n => (history j).2)))
    (hpairState :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            state n (fun j : Finset.Iic n => (history j).2)))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (fun j : Finset.Iic n => (history j).2))
            (fun n history =>
              state n (fun j : Finset.Iic n => (history j).2))
            hpairContext hpairState i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the theorem proves the same generated-history
  ordinary conditional mean-zero result, but fixes the pair-history argument
  in the remaining pushforward law to the concrete finite trace prefix
  `fun j => (action omega j.1, reward omega j.1)`.  The pair context/state
  are reward-projection wrappers around the original reward-history
  context/state.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`, consuming
  `centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc`;
  `History.finiteRewardHistoryOfTrace`;
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: instantiate the generated-history pair-law consumer
  with pair context/state wrappers
  `fun n history => context n (fun j => (history j).2)` and
  `fun n history => state n (fun j => (history j).2)`; instantiate
  `pairHistory omega` as the concrete trace-pair prefix
  `fun j => (action omega j.1, reward omega j.1)`; close the two
  compatibility hypotheses by definitional equality.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable context/state/action spaces, singleton-measurable action space,
  timewise measurable action and reward traces, original context/state
  measurability, reward-projection pair-context/state measurability, centered
  reward kernel law, centered integrability, and the explicit generated-history
  `condExpKernel` action/reward pair-law pushforward equality for the concrete
  trace-pair history.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP`;
  local inputs
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP` and
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `FILTRATION-HISTORY`, and `KERNEL-POLICY-BIND`.  It removes the external
  `pairHistory`, `h_pair_context_eq`, and `h_pair_state_eq` parameters under
  the concrete trace-pair representation.
- Failure policy: do not treat this as the pair-law identification.  It still
  assumes the generated-history `condExpKernel` pushforward equality into
  `RewardKernel.actionRewardHistoryStepKernelFamily`; future work must prove
  that equality from the finite-prefix `partialTraj` trajectory law and the
  policy/history construction.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP` is compiled
locally:

```lean
def History.pairHistoryRewardProjection
    {Action : Type v} {Reward : Type w} {t : Nat}
    (history : (i : Finset.Iic t) -> Prod Action Reward) :
    History.FiniteRewardHistory Reward t

theorem History.measurable_pairHistoryRewardProjection
    {Action : Type v} {Reward : Type w}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (t : Nat) :
    Measurable
      (fun history : (i : Finset.Iic t) -> Prod Action Reward =>
        History.pairHistoryRewardProjection history)

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the finite pair-history reward projection is a
  measurable map into finite reward histories, and the projected
  generated-history pair-law consumer now derives pair-context and pair-state
  measurability from the original reward-history `context`/`state`
  measurability.  The remaining hypothesis is the concrete
  generated-history `condExpKernel` pushforward law for the next
  `(Action, Reward)` pair.
- Local APIs/imports: `BanditRLProof.HistoryFiltration`,
  `BanditRLProof.ConditionalExpectationReward`,
  `History.pairHistoryRewardProjection`,
  `History.measurable_pairHistoryRewardProjection`, and
  `centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected`.
- Intended proof route: prove pair-history reward projection measurability by
  `measurable_pi_lambda` over `Finset.Iic` and coordinate maps
  `measurable_snd.comp (measurable_pi_apply i)`; instantiate the previous
  projected consumer with
  `(hcontext n).comp (History.measurable_pairHistoryRewardProjection n)` and
  the analogous `hstate` proof.
- Regularity contracts: measurable action/reward pair histories, measurable
  context/state/action spaces, singleton-measurable action space, timewise
  measurable action and reward traces, finite measure `mu`, centered
  integrability, centered reward kernel law, and the explicit concrete
  generated-history pair-law pushforward equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP`; local
  inputs `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY` and
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP`;
  Mathlib route `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `MEAS-HISTORY`, and `KERNEL-POLICY-BIND`.  It removes the separate projected
  pairContext/pairState measurability hypotheses from the concrete trace-pair
  route.
- Failure policy: do not treat this as a `condExpKernel` trajectory-law
  theorem.  It still assumes the concrete generated-history pair-law
  pushforward equality into `RewardKernel.actionRewardHistoryStepKernelFamily`.

`LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP` is compiled
locally:

```lean
abbrev History.FinitePairHistory
    (Action : Type v) (Reward : Type w) (t : Nat) :=
  (i : Finset.Iic t) -> Prod Action Reward

def History.finitePairHistoryOfTrace
    {Action : Type v} {Reward : Type w}
    (action : ActionTrace Action)
    (reward : RewardTrace Reward)
    (t : Nat) :
    History.FinitePairHistory Action Reward t :=
  fun i => (action i.1, reward i.1)

@[simp] theorem History.finitePairHistoryOfTrace_apply
    {Action : Type v} {Reward : Type w}
    (action : ActionTrace Action)
    (reward : RewardTrace Reward)
    (t : Nat) (i : Finset.Iic t) :
    History.finitePairHistoryOfTrace action reward t i =
      (action i.1, reward i.1)

@[simp] theorem History.pairHistoryRewardProjection_finitePairHistoryOfTrace
    {Action : Type v} {Reward : Type w}
    (action : ActionTrace Action)
    (reward : RewardTrace Reward)
    (t : Nat) :
    History.pairHistoryRewardProjection
        (History.finitePairHistoryOfTrace action reward t) =
      History.finiteRewardHistoryOfTrace reward t

theorem History.measurable_finitePairHistoryOfTrace
    {Omega : Type u} {Action : Type v} {Reward : Type w}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) t)

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the pair-coordinate finite trace prefix
  `History.finitePairHistoryOfTrace` is named and measurable, its reward
  projection is definitionally the finite reward history, and the generated
  conditional mean-zero consumer now states the remaining pair-law equality
  using that named prefix.
- Local APIs/imports: `BanditRLProof.HistoryFiltration`,
  `BanditRLProof.ConditionalExpectationReward`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`,
  `History.measurable_finitePairHistoryOfTrace`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel` as the matching
  pair-coordinate trajectory surface.
- Intended proof route: define the pair-coordinate prefix by
  `fun i => (action i.1, reward i.1)`, prove measurability by
  `measurable_pi_lambda` plus coordinatewise product measurability, then
  invoke the projection-measurability conditional expectation wrapper with
  `simpa [History.finitePairHistoryOfTrace]`.
- Regularity contracts: measurable action/reward spaces, timewise measurable
  action and reward traces, original reward-history context/state
  measurability, finite measure `mu`, centered integrability, centered reward
  kernel law, singleton-measurable action space, and the explicit
  generated-history `condExpKernel` pair-law equality stated with
  `History.finitePairHistoryOfTrace`.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP`; local
  inputs `LOCAL-LEAF-FINITE-HISTORY-PRODUCT-MEASURABILITY`,
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP`, and
  `LOCAL-LEAF-POLICY-REWARD-ACTION-REWARD-PARTIAL-TRAJECTORY`; Mathlib route
  `MLIB-CONDITIONAL-EXPECTATION`.
- Status: project-local compiled supporting leaf for `COND-EXPECT-REWARD`,
  `MEAS-HISTORY`, and `KERNEL-POLICY-BIND`.  It aligns the remaining
  `condExpKernel` pair-law hypothesis with the named finite pair-history
  object used by the pair-coordinate trajectory-kernel surface.
- Failure policy: do not treat this as the pair-law identification.  It still
  assumes the generated-history `condExpKernel` pushforward equality; future
  work must prove that equality from `partialTraj`.

`COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER` is compiled locally:

```lean
theorem ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace

theorem ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Exact Lean-facing statement: the first theorem projects an explicit
  generated-history `condExpKernel` law for the extended finite pair trace
  `History.finitePairHistoryOfTrace (action y) (reward y) (i + 1)` into a
  next `(Action, Reward)` pair pushforward identity against
  `RewardKernel.actionRewardHistoryStepKernelFamily`.  The second theorem adds
  the centered reward-kernel law and integrability hypotheses: under that same
  explicit generated-history
  `condExpKernel` law for the extended finite pair trace
  `History.finitePairHistoryOfTrace (action y) (reward y) (i + 1)` into
  `RewardKernel.actionRewardPartialTrajectoryKernel ... i (i + 1) ...`, the
  succ-indexed centered reward has ordinary conditional expectation zero
  against `History.historyFiltrationSucc ... i`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `BanditRLProof.RewardKernel`,
  `History.finitePairHistoryOfTrace`,
  `History.measurable_finitePairHistoryOfTrace`,
  `History.measurable_pairHistoryRewardProjection`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply`.
- Intended proof route: map the assumed extended finite-trace law along the
  next coordinate `i + 1`; use Mathlib `Measure.map_map` plus
  `measurable_pi_apply` and `History.measurable_finitePairHistoryOfTrace` to
  identify that pushforward with the conditional next `(Action, Reward)` pair;
  rewrite the trajectory-kernel side with
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply` to
  obtain the reusable pair-map law; the centered theorem then invokes
  `ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
- Regularity contracts: finite measure `mu`, standard Borel sample space,
  measurable context/state/action/reward spaces, singleton-measurable action
  space, timewise measurable action and reward traces, reward-history
  context/state measurability, centered integrability of the succ-indexed
  reward, centered reward-kernel law, and the explicit trim-a.e.
  generated-history `condExpKernel`/partialTraj extended finite pair-trace law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER`; local
  inputs `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-NEXT-MAP` and
  `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP`; Mathlib
  route `MLIB-CONDITIONAL-EXPECTATION` and `Measure.map_map`; no LML theorem
  is used as a proof dependency.
- Status: project-local compiled consumer for `COND-EXPECT-REWARD`,
  `KERNEL-POLICY-BIND`, and `MEAS-HISTORY`.
- Failure policy: do not mark `COND-EXPECT-REWARD` complete from this theorem.
  It consumes the exact generated-history `condExpKernel`/partialTraj law but
  does not prove that law, arbitrary adaptive policy predictability, a
  conditional sub-Gaussian witness, or any final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP` is
compiled locally:

```lean
theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (condExpKernel mu
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            ... i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))

theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_partialtraj_map_eq : ...)
    :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: the first theorem consumes an explicit
  full finite-pair trace `condExpKernel`/`partialTraj` law plus a trim-a.e.
  equality between the actual successor action and the policy-selected action,
  and concludes the actual-action reward-coordinate conditional map law.  The
  second theorem replaces the explicit action equality by
  `Policy.generatedActionTraceSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`,
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`, and
  Mathlib `Measure.map_map`.
- Intended proof route: reuse
  `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`
  to project the full finite-pair trace law to the next-pair law; map both
  sides through `Prod.snd`; rewrite the action/reward step-kernel side with
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`; then rewrite
  the policy-selected action to the actual successor action.  The generated
  wrapper derives that action equality pointwise from
  `Policy.generatedActionTraceSucc`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, singleton-measurable action space,
  timewise measurable action/reward traces, reward-history context/state
  measurability, the full finite-pair trace `condExpKernel`/`partialTraj` law,
  and either explicit successor action equality or generated shifted policy
  trace equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-REWARD-MAP`;
  declarations are
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`
  and
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
- Status: project-local compiled reward-map adapter leaf for
  `COND-EXPECT-REWARD`, `KERNEL-POLICY-BIND`, `MEAS-HISTORY`, and
  `KERNEL-REWARD`.
- Failure policy: do not treat this as the ambient trajectory-law
  identification.  It still assumes the full finite-pair trace
  `condExpKernel`/`partialTraj` law and does not prove integrability,
  sub-Gaussian witnesses, arbitrary adaptive policy predictability, or any
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (condExpKernel mu
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            ... i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))

theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_extend_map_eq : ...)
    :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: the first theorem consumes an extension-map
  `condExpKernel`/`partialTraj` law for the deterministic frozen old pair
  prefix extended by the random next pair, plus a trim-a.e. successor action
  equality, and concludes the actual-action reward-coordinate conditional map
  law.  The second theorem derives that successor action equality from
  `Policy.generatedActionTraceSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `History.extendPairHistorySucc`, `History.finitePairHistoryOfTrace`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  and
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
- Intended proof route: lift the extension-map law back to the full
  finite-pair trace law with the successor-decomposition adapter, then reuse
  the finite-pair-trace reward-map adapter.  The generated wrapper supplies
  the action equality by unfolding `Policy.generatedActionTraceSucc`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, singleton-measurable and countable
  action space, timewise measurable action/reward traces, reward-history
  context/state measurability, the extension-map
  `condExpKernel`/`partialTraj` law, and either explicit successor action
  equality or generated shifted policy trace equality.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-REWARD-MAP`;
  declarations are
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`
  and
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
- Status: project-local compiled reward-map adapter leaf for
  `COND-EXPECT-REWARD`, `KERNEL-POLICY-BIND`, `MEAS-HISTORY`,
  `FILTRATION-HISTORY`, and `KERNEL-REWARD`.
- Failure policy: do not treat this as the ambient trajectory-law
  identification.  It still assumes the extension-map
  `condExpKernel`/`partialTraj` law and does not prove integrability,
  sub-Gaussian witnesses, arbitrary adaptive policy predictability, or any
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP` is compiled
locally:

```lean
theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq
    ...
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Measure.map
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (condExpKernel mu (F i) omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu (F i) omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          (action omega (i + 1)))
      (ae (mu.trim (F.le i)))

theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_policy_eq : ...)
    (h_kernel_pair_map_eq : ... RewardKernel.actionRewardHistoryStepKernelFamily
      ... (History.finitePairHistoryOfTrace (action omega) (reward omega) i)) :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))

theorem ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    ...
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_pair_map_eq : ...)
    :
    Filter.Eventually
      (fun omega : Omega =>
        Measure.map
          (fun y : Omega => reward y (i + 1))
          (condExpKernel mu
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i)))
```

- Exact Lean-facing statement: the generic theorem consumes an explicit
  `condExpKernel` pushforward law for the random next pair
  `(action y (i + 1), reward y (i + 1))` into
  `RewardKernel.actionRewardHistoryStepKernelFamily`, plus a trim-a.e.
  successor equality between the actual action and the policy-selected action,
  and concludes the actual-action reward-coordinate conditional map law.  The
  finite-pair-history specialization fixes `F` to
  `History.historyFiltrationSucc` and fixes `pairHistory` to
  `History.finitePairHistoryOfTrace`; the generated wrapper derives the
  successor action equality from `Policy.generatedActionTraceSucc`.
- Local APIs/imports: `BanditRLProof.ConditionalExpectationReward`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`,
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection_finitePairHistoryOfTrace`, and
  `Policy.generatedActionTraceSucc`.
- Intended proof route: map the next-pair law through `Prod.snd`; identify the
  right-hand side by
  `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`; rewrite the
  policy-selected action to the actual next action with the supplied
  successor equality.  The finite-pair-history wrapper only unfolds projected
  `pairContext`, `pairState`, and `pairHistory`; the generated wrapper unfolds
  `Policy.generatedActionTraceSucc`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, timewise measurable action/reward
  traces, pair-context/pair-state measurability, the explicit next-pair
  `condExpKernel` law, and either trim-a.e. successor action equality or a
  generated shifted policy trace.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-HISTORYSTEP-REWARD-MAP`;
  declarations are
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`,
  and
  `ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
- Status: project-local compiled reward-coordinate adapter leaf for
  `COND-EXPECT-REWARD`, `KERNEL-POLICY-BIND`, `MEAS-HISTORY`, and
  `KERNEL-REWARD`.
- Failure policy: do not treat this as a proof of the next-pair law itself.
  It still assumes the `condExpKernel` next-pair pushforward identity and does
  not prove the ambient trajectory identification, integrability,
  sub-Gaussian witnesses, arbitrary adaptive policy predictability, or any
  final adaptive ETC/UCB theorem.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward y)
                  (reward y) (i + 1))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward)
                  reward
                  (generatedActionFromRewardHistory_measurable
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a full finite-pair generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and global model-side variance ceiling build the packaged practical
  definitional raw-range/measurable-mean-range uniform-variance source.  The
  return type is
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource
  mu rewardKernel policy context state mean varianceProxy defaultAction reward
  hreward rewardLo rewardHi meanLo meanHi varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: first reuse the existing full finite-pair
  `partialTraj` constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the uniform source field `variance_le` directly with
  `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the full finite-pair generated-history
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof and not a final
  adaptive theorem.  It still assumes the full generated finite-pair
  `partialTraj`/`condExpKernel` identity and a model-side variance ceiling; it
  does not derive that ceiling from raw/mean ranges, construct the random-pair
  law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward y)
                  (reward y) (i + 1))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      varianceCeiling mu
```

- Exact Lean-facing statement: a full finite-pair generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and a global context/action variance ceiling directly yield the
  succ-indexed `HasCondSubgaussianMGF` witness with proxy
  `varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: first build the packaged uniform-variance source from
  the full finite-pair `partialTraj` law and raw/mean range regularity.  Then
  consume that source with the existing packaged-source conditional MGF
  theorem.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the full generated finite-pair
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-UNIFORM-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`.
- Status: project-local compiled conditional-MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof, not a
  variance-ceiling derivation, and not a final adaptive theorem.  It still
  assumes the full generated finite-pair `partialTraj`/`condExpKernel`
  identity plus a global model-side variance ceiling.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward y)
                  (reward y) (i + 1))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a full finite-pair generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and time-indexed selected-history variance ceiling build the packaged
  practical definitional raw-range/measurable-mean-range history-variance
  source.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: first reuse the existing full finite-pair
  `partialTraj` constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the history-variance source field `variance_history_le` directly
  with `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  time-indexed selected-history variance ceiling, and the full generated
  finite-pair `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof and not a final
  adaptive theorem.  It still assumes the full generated finite-pair
  `partialTraj`/`condExpKernel` identity and a model-side selected-history
  variance ceiling; it does not derive that ceiling from raw/mean ranges,
  construct the random-pair law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward y)
                  (reward y) (i + 1))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state defaultAction
                    reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      (varianceCeiling i) mu
```

- Exact Lean-facing statement: a full finite-pair generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and a time-indexed selected-history variance ceiling directly yield the
  succ-indexed `HasCondSubgaussianMGF` witness with proxy
  `varianceCeiling i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: first build the packaged history-variance source from
  the full finite-pair `partialTraj` law and raw/mean range regularity.  Then
  consume that source with the existing packaged-source conditional MGF
  theorem.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  selected-history variance ceiling, and the full generated finite-pair
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-HISTORY-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
- Status: project-local compiled conditional-MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof, not a
  variance-ceiling derivation, and not a final adaptive theorem.  It still
  assumes the full generated finite-pair `partialTraj`/`condExpKernel`
  identity plus the selected-history variance ceiling.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (generatedActionFromRewardHistory policy state
                      defaultAction reward omega)
                    (reward omega) i)
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a frozen-prefix extension-map generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and global model-side variance ceiling build the packaged practical
  definitional raw-range/measurable-mean-range uniform-variance source.  The
  return type is the same uniform source package as the full finite-pair
  constructor, but the law hypothesis maps only the old finite pair prefix
  extended by the conditional next pair.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.extendPairHistorySucc`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: first reuse the existing frozen-prefix extension-map
  constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the uniform source field `variance_le` directly with
  `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the frozen-prefix extension-map
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof and not a final
  adaptive theorem.  It still assumes the frozen-prefix extension-map
  `partialTraj`/`condExpKernel` identity and a model-side variance ceiling; it
  does not derive that ceiling from raw/mean ranges, construct the random-pair
  law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (generatedActionFromRewardHistory policy state
                      defaultAction reward omega)
                    (reward omega) i)
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      varianceCeiling mu
```

- Exact Lean-facing statement: a frozen-prefix extension-map generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and a global context/action variance ceiling directly yield the
  succ-indexed `HasCondSubgaussianMGF` witness with proxy
  `varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.extendPairHistorySucc`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: first build the packaged uniform-variance source from
  the frozen-prefix extension-map `partialTraj` law and raw/mean range
  regularity.  Then consume that source with the existing packaged-source
  conditional MGF theorem.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the frozen-prefix extension-map
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-UNIFORM-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`.
- Status: project-local compiled conditional-MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof, not a
  variance-ceiling derivation, and not a final adaptive theorem.  It still
  assumes the frozen-prefix extension-map `partialTraj`/`condExpKernel`
  identity plus a global model-side variance ceiling.

`LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_reward_map_eq_actual_action :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map (fun y : Omega => reward y (i + 1))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (generatedActionFromRewardHistory policy state defaultAction
                reward omega (i + 1)))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      varianceCeiling mu
```

- Exact Lean-facing statement: an actual-action reward-coordinate
  selected-measure law, raw reward range, selected mean range, centered kernel
  law, and a global context/action variance ceiling directly yield the
  succ-indexed `HasCondSubgaussianMGF` witness with proxy `varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`,
  `History.historyFiltrationSucc`,
  `History.finiteRewardHistoryOfTrace`,
  `History.finitePairHistoryOfTrace`,
  `History.extendPairHistorySucc`,
  `RewardKernel.selectedMeasure`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: derive the frozen-prefix extension-map `partialTraj`
  law from the generated-action actual reward-coordinate law using the existing
  reward-map-to-extension-map adapter.  Then call the compiled frozen-prefix
  extension-map uniform-variance conditional MGF consumer.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the actual-action reward-coordinate
  `condExpKernel` selected-measure law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-ACTUAL-REWARD-MAP-UNIFORM-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`.
- Status: project-local compiled conditional-MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a reward-coordinate law constructor, not an
  ambient trajectory-to-`condExpKernel` theorem, not a variance-ceiling
  derivation, and not a final adaptive theorem.  It assumes the actual-action
  selected-measure law and a global model-side variance ceiling.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (generatedActionFromRewardHistory policy state
                      defaultAction reward omega)
                    (reward omega) i)
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a frozen-prefix extension-map generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and time-indexed selected-history variance ceiling build the packaged
  practical definitional raw-range/measurable-mean-range history-variance
  source.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.extendPairHistorySucc`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardPartialTrajectoryKernel`.
- Intended proof route: first reuse the existing frozen-prefix extension-map
  constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the history-variance source field `variance_history_le` directly
  with `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  time-indexed selected-history variance ceiling, and the frozen-prefix
  extension-map `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof and not a final
  adaptive theorem.  It still assumes the frozen-prefix extension-map
  `partialTraj`/`condExpKernel` identity and a model-side selected-history
  variance ceiling; it does not derive that ceiling from raw/mean ranges,
  construct the random-pair law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (generatedActionFromRewardHistory policy state
                      defaultAction reward omega)
                    (reward omega) i)
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              ... i (i + 1)
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      (varianceCeiling i) mu
```

- Exact Lean-facing statement: a frozen-prefix extension-map generated-history
  `partialTraj` law, raw reward range, selected mean range, centered kernel
  law, and a time-indexed selected-history variance ceiling directly yield the
  succ-indexed `HasCondSubgaussianMGF` witness with proxy
  `varianceCeiling i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.extendPairHistorySucc`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardPartialTrajectoryKernel`, and
  `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: first build the packaged history-variance source from
  the frozen-prefix extension-map `partialTraj` law and raw/mean range
  regularity.  Then consume that source with the existing packaged-source
  conditional MGF theorem.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  selected-history variance ceiling, and the frozen-prefix extension-map
  `partialTraj`/`condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-HISTORY-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
- Status: project-local compiled conditional-MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not the ambient trajectory-law proof, not a
  variance-ceiling derivation, and not a final adaptive theorem.  It still
  assumes the frozen-prefix extension-map `partialTraj`/`condExpKernel`
  identity plus the selected-history variance ceiling.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                (generatedActionFromRewardHistory policy state defaultAction
                  reward y (i + 1),
                  reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              ... i
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a canonical generated-history history-step
  next-pair law, raw reward range, selected mean range, centered kernel law,
  and global model-side variance ceiling build the packaged practical
  definitional raw-range/measurable-mean-range uniform-variance source.  The
  return type is the same uniform source package as the full finite-pair and
  extension-map constructors, but the law hypothesis is stated directly against
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: first reuse the existing canonical history-step
  constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the uniform source field `variance_le` directly with
  `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the canonical history-step next-pair
  `condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a proof of the canonical history-step next-pair
  law and not a final adaptive theorem.  It still assumes the history-step
  pair-map `condExpKernel` identity and a model-side variance ceiling; it does
  not derive that ceiling from raw/mean ranges, construct the random-pair law,
  or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded
    ...
    (varianceCeiling : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall context : Context, forall action : Action,
        varianceProxy context action <= varianceCeiling)
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                (generatedActionFromRewardHistory policy state defaultAction
                  reward y (i + 1),
                  reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              ... i
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      varianceCeiling mu
```

- Exact Lean-facing statement: a canonical generated-history history-step
  next-pair law, raw reward range, selected mean range, centered kernel law,
  and global varianceProxy ceiling directly imply the succ-indexed
  `HasCondSubgaussianMGF` witness for the centered successor reward with proxy
  `varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finiteRewardHistoryOfTrace`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`, and
  Mathlib's `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: package the canonical history-step next-pair law into
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`
  via
  `generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  then invoke the already compiled source-level uniform-variance conditional
  MGF consumer.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range, global
  context/action variance ceiling, and the canonical history-step next-pair
  `condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-UNIFORM-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeUniformVarianceBounded`.
- Status: project-local compiled conditional MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a proof of the canonical history-step next-pair
  law and not a final adaptive theorem.  It still assumes the history-step
  pair-map `condExpKernel` identity and a model-side global variance ceiling;
  it does not derive that ceiling from raw/mean ranges, construct the
  random-pair law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                (generatedActionFromRewardHistory policy state defaultAction
                  reward y (i + 1),
                  reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              ... i
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling
```

- Exact Lean-facing statement: a canonical generated-history history-step
  next-pair law, raw reward range, selected mean range, centered kernel law,
  and time-indexed selected-history variance ceiling build the packaged
  practical definitional raw-range/measurable-mean-range history-variance
  source.  The return type is the same history-variance source package
  consumed by the selected-history conditional MGF route, but the law
  hypothesis is stated directly against
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`, and
  `RewardKernel.actionRewardHistoryStepKernelFamily`.
- Intended proof route: first reuse the existing canonical history-step
  constructor for
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource`.
  Then fill the history-variance source field `variance_history_le` directly
  with `hvariance`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  time-indexed selected-history variance ceiling, and the canonical
  history-step next-pair `condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`.
- Status: project-local compiled source constructor for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a proof of the canonical history-step next-pair
  law and not a final adaptive theorem.  It still assumes the history-step
  pair-map `condExpKernel` identity and a model-side selected-history
  variance ceiling; it does not derive that ceiling from raw/mean ranges,
  construct the random-pair law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-COND-MGF`
is compiled locally:

```lean
theorem ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
    ...
    (varianceCeiling : Nat -> NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i)
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            Measure.map
              (fun y : Omega =>
                (generatedActionFromRewardHistory policy state defaultAction
                  reward y (i + 1),
                  reward y (i + 1)))
              (condExpKernel mu
                ((History.historyFiltrationSucc
                  (generatedActionFromRewardHistory policy state
                    defaultAction reward)
                  reward
                  (generatedActionFromRewardHistory_measurable hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              ... i
              (History.finitePairHistoryOfTrace
                (generatedActionFromRewardHistory policy state defaultAction
                  reward omega)
                (reward omega) i))
          (ae (mu.trim
            ((History.historyFiltrationSucc
              (generatedActionFromRewardHistory policy state defaultAction
                reward)
              reward
              (generatedActionFromRewardHistory_measurable hreward hstate)
              hreward).le i))))
    (i : Nat) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (generatedActionFromRewardHistory policy state defaultAction reward)
        reward
        (generatedActionFromRewardHistory_measurable hreward hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      (varianceCeiling i) mu
```

- Exact Lean-facing statement: a canonical generated-history history-step
  next-pair law, raw reward range, selected mean range, centered kernel law,
  and time-indexed selected-history variance ceiling directly imply the
  succ-indexed `HasCondSubgaussianMGF` witness for the centered successor
  reward with proxy `varianceCeiling i`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory`,
  `ConditionalExpectationReward.generatedActionFromRewardHistory_measurable`,
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`,
  `History.historyFiltrationSucc`,
  `History.finiteRewardHistoryOfTrace`,
  `History.finitePairHistoryOfTrace`,
  `History.pairHistoryRewardProjection`,
  `RewardKernel.actionRewardHistoryStepKernelFamily`, and
  Mathlib's `ProbabilityTheory.HasCondSubgaussianMGF`.
- Intended proof route: package the canonical history-step next-pair law into
  `GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`
  via
  `generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq`,
  then invoke the already compiled source-level selected-history conditional
  MGF consumer.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, measurable singleton and countable
  action space, timewise measurable rewards, measurable context and state
  extractors, measurable mean surface, centered reward-kernel law,
  deterministic raw reward range, deterministic selected mean range,
  time-indexed selected-history variance ceiling, and the canonical
  history-step next-pair `condExpKernel` law.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-HISTORY-VARIANCE-COND-MGF`;
  declaration is
  `ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded`.
- Status: project-local compiled conditional MGF consumer for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this is not a proof of the canonical history-step next-pair
  law and not a final adaptive theorem.  It still assumes the history-step
  pair-map `condExpKernel` identity and a model-side selected-history
  variance ceiling; it does not derive that ceiling from raw/mean ranges,
  construct the random-pair law, or prove UCB/ETC/RL regret.

`LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE`
is compiled locally:

```lean
def ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_uniformVarianceBoundedSource
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (varianceCeiling : NNReal)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi varianceCeiling) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi
      (fun _ : Nat => varianceCeiling)
```

- Exact Lean-facing statement: a practical definitional raw-range source with
  a packaged global context/action variance ceiling yields the weaker
  time-indexed selected-history variance source, using the constant schedule
  `fun _ : Nat => varianceCeiling`.
- Local APIs/imports: `BanditRLProof.ConditionalRewardLawSource`,
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeUniformVarianceBoundedSource`,
  and
  `ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource`.
- Intended proof route: reuse `source.base_source`; for
  `variance_history_le i history`, instantiate `source.variance_le` at
  `context i history` and `(policy i).action (state i history)`.
- Regularity contracts: finite measure, standard Borel sample space,
  measurable context/state/action spaces, countable action space, timewise
  measurable reward trace, the practical definitional raw-range source fields,
  and the global deterministic variance ceiling.
- Retrieval evidence: local card
  `LOCAL-LEAF-COND-EXPECT-REWARD-UNIFORM-VARIANCE-SOURCE-TO-HISTORY-VARIANCE-SOURCE`;
  declaration is
  `ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeHistoryVarianceBoundedSource_of_uniformVarianceBoundedSource`.
- Status: project-local compiled source-conversion leaf for
  `COND-EXPECT-REWARD`, `ADAPTED-ACTION`, `MEAS-POLICY`, `MEAS-HISTORY`,
  `KERNEL-POLICY-BIND`, `KERNEL-REWARD`, `INT-REWARD-BOUNDED`, and
  `MEAS-REWARD`.
- Failure policy: this only converts a stronger variance-source package into a
  weaker one. It does not construct the definitional random next-pair law,
  prove the ambient trajectory-to-`condExpKernel` identification, derive a
  variance ceiling from raw/mean range bounds, or prove any final adaptive
  ETC/UCB theorem.

Current boundary after this leaf:

- `KERNEL-REWARD` is now compiled as the reward-kernel contract surface above.
- `POLICY-REWARD-ONE-STEP-KERNEL-COMPOSITION` is now compiled as the
  one-step policy/reward Markov-kernel composition surface above.
- `POLICY-REWARD-IIC-HISTORY-PARTIAL-TRAJECTORY` is now compiled as the
  finite-prefix reward-history `partialTraj` surface above.
- `KERNEL-POLICY-BIND` is now compiled as the finite-prefix action/reward pair
  trajectory-kernel surface above.  It also has selected-reward marginal
  wrappers for one-step and history-step action/reward kernels, plus one-step
  `partialTraj` next-coordinate marginal wrappers for reward-history and
  action/reward pair trajectories.  The remaining work is
  `partialTraj`/history-to-`condExpKernel` action/reward pair-law
  identification, posterior-kernel integration, infinite trajectory laws, and
  final adaptive theorem integration.
- `LOCAL-LEAF-KERNEL-CENTERED-REWARD-LAW-TRANSFER` is now compiled locally in
  `BanditRLProof.RewardKernel` for the `COND-EXPECT-REWARD` route:
  `RewardKernel.CenteredRewardKernelLaw` packages pointwise selected-reward
  centered integrability, zero integral, and `HasSubgaussianMGF` witnesses, and
  the `RewardKernel.composePolicy_centeredReward_*` plus
  `RewardKernel.historyStepKernelFamily_centeredReward_*` wrappers transfer
  those facts through policy-composed and finite reward-history step kernels.
  This is not a `condExpKernel` identity for the finite-prefix trajectory law.
- `LOCAL-LEAF-KERNEL-REWARD-MAP-LAW-TRANSFER` is now compiled locally in
  `BanditRLProof.RewardKernel`: one-step and history-step action/reward
  kernels push forward through `Prod.snd` to the selected reward measure.  This
  matches the map-law consumer shape but still does not construct the
  `condExpKernel` trajectory-law identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-CONDEXPKERNEL-ZERO` is now compiled locally in
  `BanditRLProof.ConditionalExpectationReward` as the consumer bridge from a
  zero `condExpKernel` centered-reward integral to ordinary conditional
  mean-zero.  It still assumes the conditional-kernel zero-integral fact.
- `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-CONSUMER` is now
  compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  consumer from explicit history-step law/integral equality plus
  `RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero` to
  ordinary conditional mean-zero.  It still assumes the trajectory-law
  `condExpKernel` identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-HISTORYSTEP-CONDEXPKERNEL-MAP-CONSUMER` is
  now compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  reward-coordinate pushforward-map consumer plus frozen-past condition.  It
  still assumes, rather than proves, the trajectory-law `condExpKernel`
  identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CENTERED` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the deterministic
  bridge from an assumed frozen finite-history property to the centered-target
  a.e. equality consumed by the map-law route.  It does not prove the
  frozen-history condition itself.
- `LOCAL-LEAF-COND-EXPECT-REWARD-FROZEN-HISTORY-CONDEXPKERNEL` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the
  conditional-kernel frozen-past route for conditioning-measurable events,
  countable variables, and finite reward histories.  It is now fed by the
  concrete finite-history measurability hookup, but still does not prove the
  reward-law `condExpKernel` identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-FINITE-HISTORY-MEAS-HOOKUP` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the coordinate
  measurability and generated `History.historyFiltrationSucc` hookup for
  freezing finite reward histories under `condExpKernel`.  The remaining
  `COND-EXPECT-REWARD` work is now routed through the action/reward pair-law
  identification below, broader adaptive-policy integration, and final theorem
  assembly.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-FROZEN-HOOKUP` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the
  `[Countable Action]` finite action/reward pair-history frozen-past hookup.
  The generated `History.historyFiltrationSucc` specialization freezes
  `History.finitePairHistoryOfTrace` prefixes under `condExpKernel`; the actual
  `partialTraj`/history-to-`condExpKernel` pair-law identification remains
  open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-HISTORY-SUCC-EXTEND-HOOKUP` is now
  compiled locally across `BanditRLProof.HistoryFiltration` and
  `BanditRLProof.ConditionalExpectationReward`.  It names the measurable
  successor extension of pair histories and shows that, under generated
  `condExpKernel`, the random `i+1` pair trace is a.e. a frozen old prefix
  extended by the random next pair.  The joint law identification remains open.
- `LOCAL-LEAF-POLICY-REWARD-PARTIALTRAJ-SUCC-EXTEND-MAP` is now compiled
  locally in `BanditRLProof.RewardKernel` as the Mathlib-backed one-step
  full-extension `partialTraj` wrapper.  It proves the trajectory-kernel side
  is `Measure.map (History.extendPairHistorySucc history)` of the configured
  next-pair kernel, but it still does not identify the generated
  `condExpKernel` law.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-CONSUMER` is now
  compiled locally in `BanditRLProof.ConditionalExpectationReward`.
  `Measure.map_congr` upgrades that generated successor decomposition into a
  pushforward equality, a named adapter lifts an extension-map-to-`partialTraj`
  law back to the full finite-pair-trace law, and the centered-reward consumer
  can now assume the narrower extension-map law.  The actual
  `partialTraj`/`condExpKernel` joint law identification remains open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-EXTEND-MAP-FROM-PAIRMAP` is now
  compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  law-builder from an explicit next-pair `condExpKernel` pushforward identity
  to the extension-map `partialTraj` identity.  It transports the law through
  `History.extendPairHistorySucc` and the RewardKernel full-extension wrapper;
  the next-pair conditional law itself remains open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-SPLIT-LAW-BUILDER` is now compiled
  locally across `BanditRLProof.RewardKernel` and
  `BanditRLProof.ConditionalExpectationReward`.  It decomposes the remaining
  next-pair conditional law into an action a.e. equality against the
  policy-selected action plus a reward-coordinate selected-measure law.
- `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-POLICY-HOOKUP` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the action side of
  that split: countable `F i`-measurable next actions plus trim-a.e.
  policy-generation equality supply the conditional action a.e. equality.
- `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-HISTORY-HOOKUP` is
  now compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  generated-history action-side hookup: visible finite pair histories and
  measurable `pairState` reduce the action side to pointwise policy-generation
  equality.
- `LOCAL-LEAF-COND-EXPECT-REWARD-ACTION-FREEZE-GENERATED-TRACE-SOURCE` is now
  compiled locally across `BanditRLProof.PolicyMeasurability` and
  `BanditRLProof.ConditionalExpectationReward` as the shifted generated-trace
  source for that pointwise policy-generation equality.
- `LOCAL-LEAF-COND-EXPECT-REWARD-NEXTPAIR-GENERATED-ACTION-ACTUAL-REWARD-HOOKUP`
  is now compiled locally in `BanditRLProof.ConditionalExpectationReward` as
  the generated-action plus actual/random-pair reward-law hookup.  An
  actual-action pair-product law marginalizes to the actual-action
  reward-coordinate map law, while a fully random next-pair law first freezes
  the action coordinate via `Measure.map_congr`; the resulting law is rewritten
  to the policy-selected action and combined with the split-law builder, then
  pushed through the extension-map `partialTraj` route; reward-coordinate,
  actual-action pair-product, and fully random pair law shapes now each expose
  reusable full finite-pair-trace law adapters before the centered mean-zero
  consumers.  The pair/reward source and ambient
  trajectory-to-`condExpKernel` identification remain open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-MAP-CONSUMER-FROZEN-HOOKUP` is now compiled
  locally in `BanditRLProof.ConditionalExpectationReward` as the map-law
  conditional mean-zero consumer with its frozen-past side condition discharged
  by coordinate measurability or generated `History.historyFiltrationSucc`.
  The remaining map-law input is now supplied by the pair-map consumer when an
  action/reward pair-law pushforward identity is available.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-CONSUMER` is now compiled locally in
  `BanditRLProof.ConditionalExpectationReward` as the action/reward pair-law
  consumer: a `condExpKernel` pushforward identity into
  `RewardKernel.actionRewardHistoryStepKernelFamily` marginalizes through
  `Prod.snd` into the reward-coordinate map-law route.  It still assumes the
  actual `partialTraj`/`condExpKernel` pair-law identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYFILTRATION-HOOKUP` is now
  compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  generated `History.historyFiltrationSucc` specialization of the pair-map
  consumer.  Local timewise measurability and history-filtration coordinate
  APIs now supply next-coordinate and reward-prefix measurability; the actual
  `partialTraj`/`condExpKernel` pair-law identification remains open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-HISTORYTRACE-PROJECTION-HOOKUP` is
  now compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  concrete finite trace-pair and reward-projection context/state
  specialization of the generated-history pair-map consumer.  The remaining
  `COND-EXPECT-REWARD` hard step is the actual generated-history
  `condExpKernel` pair-law pushforward identity.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-PROJECTION-MEAS-HOOKUP` is now
  compiled locally across `BanditRLProof.HistoryFiltration` and
  `BanditRLProof.ConditionalExpectationReward` as the measurable
  pair-history reward-projection hookup.  Projected pairContext/pairState
  measurability now follows from reward-history context/state measurability;
  the actual `partialTraj`/`condExpKernel` pair-law identification remains
  open.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PAIR-MAP-FINITEPAIRTRACE-HOOKUP` is now
  compiled locally across `BanditRLProof.HistoryFiltration` and
  `BanditRLProof.ConditionalExpectationReward` as the named
  `History.finitePairHistoryOfTrace` specialization of the generated-history
  pair-map consumer.  The remaining hard step is still the actual
  `partialTraj`/history-to-`condExpKernel` action/reward pair-law
  identification.
- `LOCAL-LEAF-COND-EXPECT-REWARD-PARTIALTRAJ-FINITEPAIRTRACE-CONSUMER` is now
  compiled locally in `BanditRLProof.ConditionalExpectationReward` as the
  partialTraj finite-pair-trace consumer.  An explicit generated-history
  `condExpKernel` law for the extended pair trace now projects through
  `RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply` into
  a reusable next-pair map-law adapter before feeding the centered-reward
  consumer; the actual `partialTraj`/history-to-`condExpKernel` action/reward
  pair-law identification remains open.
- `ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally
  below.  It is a conditional witness package/consumer, not a derivation of
  those fields from a concrete reward law.

`ETC-CENTERED-DIFF-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally:

```lean
structure ETC.CenteredDiffCondSubGaussianWitnesses
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)

theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w :
      ETC.CenteredDiffCondSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, importing
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail` and
  `BanditRLProof.ConcentrationSubGaussian`.
- Intended proof route: for each non-best arm, use
  `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`
  to reduce the empirical-mean event to the centered-diff finite-sum event;
  apply
  `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted` with the
  package's per-arm filtration, `StronglyAdapted`, zeroth
  `HasSubgaussianMGF`, and later `HasCondSubgaussianMGF`; finish by
  `MeasureTheory.measure_mono` and the package's tail domination field.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[StandardBorelSpace Omega]`, finite zero-or-probability measure `mu`,
  finite-arm ETC `spec`, `model`, `commitArm`, reward trace, tail budget,
  `0 < spec.explorationPulls`, per-arm filtrations, strong adaptedness,
  zeroth unconditional MGF witnesses, later conditional MGF witnesses up to
  `spec.explorationPulls * K - 1`, and tail domination.  No concrete reward
  kernel, conditional expectation identity, full policy predictability, or
  final adaptive ETC theorem is proved.
- Retrieval evidence: Mathlib/compiled declarations
  `ProbabilityTheory.HasCondSubgaussianMGF`,
  `MeasureTheory.StronglyAdapted`,
  `Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted`,
  `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`,
  `ETC.CenteredDiffCondSubGaussianWitnesses`, and
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`.
- Status: project-local compiled conditional centered-diff witness contract.
- Failure policy: if the adaptive route still fails, split the next leaf into
  one source of `HasCondSubgaussianMGF`, one source of conditional mean-zero,
  or a full policy-predictability theorem.  Do not jump to final adaptive ETC
  regret while these witness fields are still assumptions.

`ETC-CENTERED-DIFF-STRONGLY-ADAPTED-HISTORY` is compiled locally:

```lean
def History.historyFiltrationSucc
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Filtration Nat mOmega

theorem ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat) :
    @Measurable Omega Real
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      inferInstance
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)

theorem ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) :
    MeasureTheory.StronglyAdapted
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
```

- Local APIs/imports:
  `BanditRLProof.HistoryFiltration` and
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, importing
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail` and
  `BanditRLProof.ConcentrationSubGaussian`.
- Intended proof route: shift the generated history filtration by one step so
  time `t` contains reward observations with index `< t + 1`; use
  `History.measurable_reward_mem_historyFiltration_of_lt` with
  `Nat.lt_succ_self t`; compose the measurable reward coordinate with the
  deterministic Rat-to-Real centered pairwise reward-difference transform; turn
  the per-time measurable theorem into `StronglyAdapted`.
- Regularity contracts: `[MeasurableSpace Omega]`, fixed ETC `spec`,
  `model`, `commitArm`, reward trace `reward : Omega -> RewardTrace Rat`, and
  timewise reward measurability.  The fixed action trace is constant via
  `ETC.actionWithCommit`, so action measurability is discharged by
  `measurable_const`.
- Retrieval evidence: local declarations
  `History.historyFiltrationSucc`, `History.historyFiltrationSucc_apply`,
  `History.measurable_reward_mem_historyFiltration_of_lt`,
  `ETC.centeredPairwiseRewardDiff`,
  `ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc`, and
  `ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc`;
  Mathlib declaration `MeasureTheory.StronglyAdapted`.
- Status: project-local compiled adaptedness-field derivation for the ETC
  conditional centered-diff route.
- Failure policy: this leaf supplies only the `StronglyAdapted` field under the
  fixed-commit shifted-history filtration.  If the conditional route still
  fails, split `HasCondSubgaussianMGF` and conditional mean-zero derivations
  from the concrete reward law; do not treat this as a conditional MGF proof or
  as full adaptive-policy predictability.

`ETC-CENTERED-DIFF-COND-MGF-ZERO-MISS` is compiled locally:

```lean
theorem ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu

theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu

theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, importing
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`,
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`,
  `BanditRLProof.ConcentrationSubGaussian`, and
  `BanditRLProof.HistoryFiltration`.
- Intended proof route: unfold `ETC.centeredPairwiseRewardDiff`; use
  `h_ne_a` and `h_ne_best` to simplify both `if` branches to zero; discharge
  the unconditional theorem by `ProbabilityTheory.HasSubgaussianMGF.fun_zero`;
  discharge the conditional theorem by
  `ProbabilityTheory.HasCondSubgaussianMGF.fun_zero`; specialize it to
  `History.historyFiltrationSucc` with its `Filtration.le` field.
- Regularity contracts: unconditional theorem needs `[MeasurableSpace Omega]`
  and `[IsZeroOrProbabilityMeasure mu]`; conditional theorems need
  `[MeasurableSpace Omega]`, `[StandardBorelSpace Omega]`, finite `mu`, a
  sub-sigma-algebra witness `hm : m ≤ mOmega` or the shifted history
  filtration, fixed `spec`, `model`, `commitArm`, reward trace, arm/time, and
  the two action-miss inequalities.
- Retrieval evidence: local declarations
  `ETC.centeredPairwiseRewardDiff`,
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss`,
  `History.historyFiltrationSucc`; Mathlib declarations
  `ProbabilityTheory.HasSubgaussianMGF.fun_zero` and
  `ProbabilityTheory.HasCondSubgaussianMGF.fun_zero`.
- Status: project-local compiled zero-summand unconditional/conditional MGF
  source.
- Failure policy: this leaf only handles times where `actionWithCommit` pulls
  neither the comparison arm nor `model.bestArm`.  It does not prove
  sampled reward-law conditional MGF, conditional mean-zero, full policy
  predictability, or a final adaptive ETC theorem; the sampled-arm transfer and
  independence-based MGF leaves below handle only deterministic rewriting and
  independence-to-conditional-MGF bridging from supplied unconditional witnesses.

`ETC-CENTERED-DIFF-COND-MGF-SAMPLED-TRANSFER` is compiled locally:

```lean
theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action : ETC.actionWithCommit spec commitArm t = a)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        m hm
        (fun omega : Omega =>
          (((reward omega t - model.mean a : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu

theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action :
      ETC.actionWithCommit spec commitArm t = model.bestArm)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        m hm
        (fun omega : Omega =>
          (((model.mean model.bestArm - reward omega t : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu
```

History-specialized wrappers also compile:

```lean
theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm
theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`, importing
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`,
  `BanditRLProof.ConcentrationSubGaussian`, and
  `BanditRLProof.HistoryFiltration`.
- Intended proof route: unfold `ETC.centeredPairwiseRewardDiff`; in the
  `actionWithCommit t = a` branch, use non-bestness of `a` to remove the
  best-arm branch and reuse the supplied conditional MGF for
  `reward t - mean a`; in the `actionWithCommit t = bestArm` branch, remove
  the comparison-arm branch and reuse the supplied conditional MGF for
  `mean bestArm - reward t`; specialize both to `History.historyFiltrationSucc`
  by passing its `Filtration.le` proof.
- Regularity contracts: `[MeasurableSpace Omega]`, `[StandardBorelSpace Omega]`,
  finite `mu`, a sub-sigma-algebra witness `hm : m ≤ mOmega` or shifted history
  filtration, fixed `spec`, `model`, `commitArm`, reward trace, non-best
  comparison arm `a`, time `t`, parameter `c`, an action equality, and the
  sampled centered-reward conditional MGF witness.
- Retrieval evidence: local declarations
  `ETC.centeredPairwiseRewardDiff`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm`,
  and
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm`.
- Status: project-local compiled sampled-arm conditional MGF transfer.
- Failure policy: this leaf does not prove the sampled centered-reward
  conditional MGF witness or conditional mean-zero from the reward law.  The
  reward-level source contract below packages those witnesses but still does
  not derive them from a concrete kernel.  Do not jump to final adaptive ETC
  theorem.

`ETC-CENTERED-REWARD-COND-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally:

```lean
theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m <= mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat)
    (hne : a = model.bestArm -> False)
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasCondSubgaussianMGF
          m hm
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy
        spec model commitArm cReward a t)
      mu

theorem ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat)
    (hne : a = model.bestArm -> False)
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (History.historyFiltrationSucc
            (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
            reward
            (fun _t : Nat => measurable_const)
            hreward t)
          ((History.historyFiltrationSucc
            (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
            reward
            (fun _t : Nat => measurable_const)
            hreward).le t)
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy
        spec model commitArm cReward a t)
      mu

structure ETC.CenteredRewardCondSubGaussianWitnesses

noncomputable def
  ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`,
  `ETC.centeredPairwiseRewardDiffVarianceProxy`,
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm`,
  `History.historyFiltrationSucc`, and
  `ProbabilityTheory.Kernel.HasSubgaussianMGF.neg`.
- Intended proof route: case-split on
  `ETC.actionWithCommit spec commitArm t`; reuse the sampled comparison-arm
  transfer when it equals `a`, use Mathlib kernel-level negation plus the
  best-arm transfer when it equals `model.bestArm`, and use the zero-summand
  conditional MGF source otherwise.  The structure packages reward-level
  sampled MGF witnesses, zeroth unconditional witness, timewise reward
  measurability, and tail domination; the constructor fills
  `ETC.CenteredDiffCondSubGaussianWitnesses`.
- Regularity contracts: `[MeasurableSpace Omega]`, `[StandardBorelSpace Omega]`,
  finite zero-or-probability `mu`, fixed `spec`, `model`, `commitArm`, reward
  trace, `cReward : Fin K -> Nat -> NNReal`, timewise reward measurability,
  zeroth sampled centered-reward `HasSubgaussianMGF`, later sampled
  centered-reward `HasCondSubgaussianMGF` against `History.historyFiltrationSucc`
  at the preceding index, and tail domination for
  `ETC.centeredPairwiseRewardDiffVarianceProxy`.
- Retrieval evidence: local declarations
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward`,
  `ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward`,
  `ETC.CenteredRewardCondSubGaussianWitnesses`, and
  `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`.
- Status: project-local compiled reward-level conditional witness contract.
- Failure policy: this leaf still assumes the sampled centered-reward
  conditional MGF witnesses.  The independence-based MGF bridge below derives
  those witnesses from unconditional centered-reward sub-Gaussianity plus
  fixed-action history independence, and the zero-integral/raw-integrability
  sides have compiled source leaves.  Fixed-action bounded/source assembly of
  the full reward-level conditional package is handled by
  `ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE`; kernel-law assembly and
  full policy predictability remain open.  Do not start final adaptive ETC
  theorem work in the same batch.

`ETC-CENTERED-REWARD-COND-MGF-INDEP-SOURCE` is compiled locally:

```lean
theorem ETC.hasCondSubgaussianMGF_of_indep_comap
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real) (c : NNReal)
    (hmeasX : @Measurable Omega Real mOmega inferInstance X)
    (h_subG : ProbabilityTheory.HasSubgaussianMGF X c mu)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap X inferInstance) mcond mu) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu

theorem ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) (c : NNReal)
    (h_subG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward (fun _t : Nat => measurable_const) hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward (fun _t : Nat => measurable_const) hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      c mu
```

- Local APIs/imports: `ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat`,
  `ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel`,
  `MeasureTheory.condExp_indep_eq`,
  `MeasureTheory.StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable`,
  `History.historyFiltrationSucc`, and
  `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`.
- Intended proof route: unfold the conditional MGF target to Mathlib's kernel
  form, use `Kernel.HasSubgaussianMGF.of_rat`, prove rational conditional MGF
  bounds by identifying the conditional-kernel integral with conditional
  expectation, rewrite that conditional expectation to the global integral by
  independence, and close by the unconditional `h_subG.mgf_le`.
- Regularity contracts: `[StandardBorelSpace Omega]`, finite measure `mu`,
  measurable real variable `X`, unconditional `HasSubgaussianMGF X c mu`, and
  independence from the conditioning sigma-algebra; the ETC specialization also
  needs timewise reward measurability and reward-coordinate `iIndepFun`.
- Retrieval evidence: local declarations `ETC.hasCondSubgaussianMGF_of_indep_comap`,
  `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`,
  `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`,
  and Mathlib cards `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-INDEPENDENCE`.
- Status: project-local compiled independence-based conditional MGF source.
- Failure policy: this leaf is a bridge from unconditional centered-reward
  sub-Gaussianity to conditional MGF; bounded-source construction is handled by
  `ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE`, while kernel-law assembly
  remains open.

`ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE` is compiled locally:

```lean
theorem ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy lo hi b (i + 1)) mu
```

It also exposes:

```lean
noncomputable def ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (htail : forall a : Fin K, (a = model.bestArm -> False) ->
      ENNReal.ofReal
        (Real.exp
          (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
            (2 *
              (((Finset.range (spec.explorationPulls * K)).sum
                (fun t =>
                  ETC.centeredPairwiseRewardDiffVarianceProxy
                    spec model commitArm
                    (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                  NNReal) : Real)))) <= tail a) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward tail

theorem ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian
    ... :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail

theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian
    ... :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSource` imports
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`; it uses
  `ETC.BoundedRewardTraceSource`,
  `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`,
  `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`,
  `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`,
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses`,
  and `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`.
- Intended proof route:
  use `BoundedRewardTraceSource` to get the action-matched unconditional
  centered-reward sub-Gaussian witness; rewrite by
  `actionWithCommit spec commitArm (i + 1) = b`; feed the result plus
  `source.indep` into the independence-based conditional MGF bridge; assemble
  `CenteredRewardCondSubGaussianWitnesses`; convert it to the centered-diff
  witness package and then to the pairwise tail contract and argmax probability
  consumer.
- Regularity contracts:
  `[MeasurableSpace Omega]`, `[StandardBorelSpace Omega]`, probability measure
  `mu`, fixed `spec/model/commitArm`, reward trace, bounds `lo hi`,
  `ETC.BoundedRewardTraceSource`, explicit timewise reward measurability,
  positive exploration horizon `0 < spec.explorationPulls * K`,
  `0 < spec.explorationPulls` for the conditional tail consumer, `0 < K` for
  the argmax wrapper, and explicit tail domination.
- Retrieval evidence:
  local declarations
  `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource`,
  `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource`,
  `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian`,
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian`,
  `ETC.BoundedRewardTraceSource`,
  `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`,
  `ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward`,
  and Mathlib cards `MLIB-PROBABILITY-SUBGAUSSIAN`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-INDEPENDENCE`,
  `MLIB-MEASURE-INTEGRAL`.
- Status: project-local compiled bounded/source conditional witness and
  consumer leaf.
- Failure policy:
  this is fixed to deterministic `ETC.actionWithCommit`.  Do not cite it as
  arbitrary policy predictability, do not claim a kernel-law construction of
  `BoundedRewardTraceSource`, and do not treat the explicit `htail` domination
  as an automatically simplified Hoeffding bound.

`ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-BOUNDED-SOURCE` is compiled locally:

```lean
noncomputable def ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))

theorem ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail
    ... :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))

theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian
    ... :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`; reuses
  `ETC.centeredDiffSubGaussianTail`,
  `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource`,
  `ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses`,
  and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`.
- Intended proof route:
  choose the exact canonical centered-diff exponential tail
  `ETC.centeredDiffSubGaussianTail spec model (...)` as the `tail` argument
  and discharge the old `htail` hypothesis by definitional simplification.
- Regularity contracts:
  same fixed `actionWithCommit` bounded-source contracts as
  `ETC-CENTERED-REWARD-COND-WITNESS-BOUNDED-SOURCE`, except no explicit
  `htail` argument remains.
- Retrieval evidence:
  local declarations
  `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail`,
  `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail`,
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`,
  and `ETC.centeredDiffSubGaussianTail`.
- Status: project-local compiled canonical-tail bounded-source conditional
  route.
- Failure policy:
  this is still fixed to deterministic `ETC.actionWithCommit`; it does not
  prove full policy predictability, kernel-law construction, or final adaptive
  ETC regret.

`ETC-CENTERED-REWARD-COND-CANONICAL-TAIL-INFINITEPI-SOURCE` is compiled locally:

```lean
noncomputable def ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun r : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((r : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun r : Rat => (((r : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      (MeasureTheory.Measure.infinitePi coordLaw)
      spec model commitArm
      (fun omega : RewardTrace Rat => omega)
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))

theorem ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail
    ... :
    ETC.PairwiseEmpMeanTailContract
      (MeasureTheory.Measure.infinitePi coordLaw)
      spec model commitArm
      (fun omega : RewardTrace Rat => omega)
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))

theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian
    ... :
    MeasureTheory.Measure.infinitePi coordLaw
      {omega : RewardTrace Rat |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm omega a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`; reuses
  `ETC.boundedRewardTraceSource_infinitePi_actionWithCommit`,
  `ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail`,
  `ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail`,
  and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian`.
- Intended proof route:
  instantiate `BoundedRewardTraceSource` with
  `MeasureTheory.Measure.infinitePi coordLaw`, reward trace identity, and the
  coordinate a.s. bound/mean contracts; pass `fun t => measurable_pi_apply t`
  as reward measurability; derive `0 < spec.explorationPulls * K` from
  `0 < spec.explorationPulls` and `0 < K` in the probability wrapper.
- Regularity contracts:
  `coordLaw : Nat -> Measure Rat`, probability coordinate laws, fixed
  `spec`, `model`, `commitArm`, `lo hi`, action-matched coordinate a.s.
  bounds, action-matched coordinate mean identities, positive exploration
  horizon for witness construction, and `0 < K` for the argmax wrapper.
- Retrieval evidence:
  local declarations
  `ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail`,
  `ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail`,
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian`,
  `ETC.boundedRewardTraceSource_infinitePi_actionWithCommit`,
  `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`, and Mathlib
  `Measure.infinitePi` / `ProbabilityTheory.iIndepFun_infinitePi`.
- Status: project-local compiled infinitePi specialization of the conditional
  canonical-tail bounded-source route.
- Failure policy:
  fixed product-coordinate `actionWithCommit` only.  Do not cite this as a
  kernel-law construction, random/adaptive commit-arm result, arbitrary policy
  predictability, Bochner expected-regret theorem, or final adaptive ETC proof.

`ETC-CENTERED-REWARD-COND-MEAN-ZERO-INDEP-SOURCE` is compiled locally:

```lean
theorem ETC.centeredReward_condExp_eq_zero_of_indep
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (b : Fin K) (t : Nat)
    (hmeas : @Measurable Omega Real mOmega inferInstance
      (fun omega : Omega =>
        (((reward omega t - model.mean b : Rat) : Real))))
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          inferInstance)
        mcond mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp mcond mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))

theorem ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (t : Nat)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          inferInstance)
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))

theorem ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega (i + 1) - model.mean b : Rat) : Real)))
          inferInstance)
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))

theorem ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`,
  explicit import `Mathlib.Probability.ConditionalExpectation`,
  `MeasureTheory.condExp_indep_eq`, `ProbabilityTheory.Indep`,
  `History.historyFiltrationSucc`, `MeasurableSpace.comap`, and
  `Filter.EventuallyEq`.
- Intended proof route: introduce
  `X omega = ((reward omega t - model.mean b : Rat) : Real)` and
  `mX = MeasurableSpace.comap X inferInstance`; apply
  `MeasureTheory.condExp_indep_eq` with `mX` and the conditioning
  sigma-algebra, then rewrite the resulting constant conditional expectation
  using the zero integral hypothesis.  The history specialization supplies
  centered-reward measurability from timewise reward measurability and targets
  `History.historyFiltrationSucc`.  The succ-indexed specialization targets
  the Mathlib conditional-tail shape where the summand at `i + 1` is
  conditioned on filtration level `i`.  The `iIndepFun` specialization consumes
  the full fixed-action history independence leaf below.
- Regularity contracts: finite measure, ambient measurable space, centered
  reward measurability, independence of the centered reward coordinate
  sigma-algebra from the conditioning sigma-algebra, and exact zero integral of
  the centered reward.  The history specialization also needs timewise reward
  measurability.
- Retrieval evidence: local declarations
  `ETC.centeredReward_condExp_eq_zero_of_indep`,
  `ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep`, and
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep`,
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`;
  Mathlib declaration `MeasureTheory.condExp_indep_eq`.
- Status: project-local compiled conditional mean-zero source.
- Failure policy: this leaf proves conditional expectation, including the
  fixed-action iIndepFun route when a zero-integral side condition is supplied.
  It does not produce `HasCondSubgaussianMGF`.  The bounded-to-integrable and
  zero-integral sides can be supplied by the leaves below under bounded
  exact-mean reward assumptions; concrete reward-law conditional MGF remains
  open.

`ETC-CENTERED-REWARD-COND-MEAN-ZERO-BOUNDED-SOURCE` is compiled locally:

```lean
theorem ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSource` imports
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian` and
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`; the proof uses
  `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean` and
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`.
- Intended proof route:
  use `BoundedRewardTraceSource` at time `i + 1` to get the action-matched
  zero-integral identity, rewrite the pulled arm by
  `hact : actionWithCommit spec commitArm (i + 1) = b`, and feed the resulting
  zero integral plus `source.indep` into the fixed-action `iIndepFun`
  conditional mean-zero wrapper.
- Regularity contracts:
  ambient measurable space, probability measure, fixed `spec/model/commitArm`,
  reward trace, bounds `lo hi`, `ETC.BoundedRewardTraceSource`, explicit
  timewise reward measurability, action equality `hact`, and exploration-prefix
  proof `ht : i + 1 < spec.explorationPulls * K`.  No
  `StandardBorelSpace` assumption is needed for this mean-zero wrapper.
- Retrieval evidence:
  local declaration
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`;
  dependency declarations
  `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean` and
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward`;
  cards `MLIB-CONDITIONAL-EXPECTATION`,
  `MLIB-PROBABILITY-INDEPENDENCE`, and `MLIB-MEASURE-INTEGRAL`.
- Status: project-local compiled bounded-source conditional mean-zero wrapper.
- Failure policy:
  this is fixed to deterministic `ETC.actionWithCommit` and to the
  succ-indexed `History.historyFiltrationSucc` shape.  Do not cite it as an
  arbitrary adaptive-policy conditional expectation theorem, a condExpKernel
  trajectory-law identification, or a conditional MGF/sub-Gaussian result.

`MART-DIFF-REWARD` now has compiled global and finite-prefix witness surfaces,
a Mathlib partial-sum martingale wrapper, and a fixed ETC bounded-source
finite-prefix instance:

```lean
structure MartingaleDiff.SuccMartingaleDifference
    (mu : MeasureTheory.Measure Omega)
    (F : MeasureTheory.Filtration Nat mOmega)
    (Y : Nat -> Omega -> Real) : Prop where
  stronglyAdapted : MeasureTheory.StronglyAdapted F Y
  integrable : forall t, MeasureTheory.Integrable (Y t) mu
  condExp_succ_eq_zero :
    forall i,
      Filter.EventuallyEq (MeasureTheory.ae mu)
        (MeasureTheory.condExp (F i) mu (Y (i + 1)))
        (fun _omega => (0 : Real))

structure MartingaleDiff.SuccMartingaleDifferencePrefix
    (mu : MeasureTheory.Measure Omega)
    (F : MeasureTheory.Filtration Nat mOmega)
    (Y : Nat -> Omega -> Real)
    (n : Nat) : Prop where
  stronglyAdapted : MeasureTheory.StronglyAdapted F Y
  integrable : forall t, t < n -> MeasureTheory.Integrable (Y t) mu
  condExp_succ_eq_zero :
    forall i, i + 1 < n ->
      Filter.EventuallyEq (MeasureTheory.ae mu)
        (MeasureTheory.condExp (F i) mu (Y (i + 1)))
        (fun _omega => (0 : Real))

noncomputable def MartingaleDiff.partialSumsSucc
    (Y : Nat -> Omega -> Real) :
    Nat -> Omega -> Real

def MartingaleDiff.centeredRewardProcess
    (reward baseline : Nat -> Omega -> Real) :
    Nat -> Omega -> Real

theorem MartingaleDiff.succMartingaleDifference_centeredRewardProcess_of_condExp
    (mu : MeasureTheory.Measure Omega)
    (reward baseline : Nat -> Omega -> Real)
    (hadapted :
      MeasureTheory.StronglyAdapted F
        (MartingaleDiff.centeredRewardProcess reward baseline))
    (hintegrable :
      forall t,
        MeasureTheory.Integrable
          (MartingaleDiff.centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i,
        Filter.EventuallyEq (MeasureTheory.ae mu)
          (MeasureTheory.condExp (F i) mu
            (MartingaleDiff.centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    MartingaleDiff.SuccMartingaleDifference mu F
      (MartingaleDiff.centeredRewardProcess reward baseline)

theorem MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp
    (mu : MeasureTheory.Measure Omega)
    (reward baseline : Nat -> Omega -> Real)
    (n : Nat)
    (hadapted :
      MeasureTheory.StronglyAdapted F
        (MartingaleDiff.centeredRewardProcess reward baseline))
    (hintegrable :
      forall t, t < n ->
        MeasureTheory.Integrable
          (MartingaleDiff.centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i, i + 1 < n ->
        Filter.EventuallyEq (MeasureTheory.ae mu)
          (MeasureTheory.condExp (F i) mu
            (MartingaleDiff.centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    MartingaleDiff.SuccMartingaleDifferencePrefix mu F
      (MartingaleDiff.centeredRewardProcess reward baseline) n

theorem MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (h : MartingaleDiff.SuccMartingaleDifference mu F Y) :
    MeasureTheory.Martingale
      (MartingaleDiff.partialSumsSucc Y) F mu

theorem MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (reward baseline : Nat -> Omega -> Real)
    (hadapted :
      MeasureTheory.StronglyAdapted F
        (MartingaleDiff.centeredRewardProcess reward baseline))
    (hintegrable :
      forall t,
        MeasureTheory.Integrable
          (MartingaleDiff.centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i,
        Filter.EventuallyEq (MeasureTheory.ae mu)
          (MeasureTheory.condExp (F i) mu
            (MartingaleDiff.centeredRewardProcess reward baseline (i + 1)))
          (fun _omega => (0 : Real))) :
    MeasureTheory.Martingale
      (MartingaleDiff.partialSumsSucc
        (MartingaleDiff.centeredRewardProcess reward baseline)) F mu

theorem ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    MartingaleDiff.SuccMartingaleDifferencePrefix
      mu
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real)))
      n
```

Supporting declarations:

```lean
theorem ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc
theorem ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc
theorem ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource
```

- Local APIs/imports:
  `BanditRLProof.MartingaleDifference` imports
  `Mathlib.Probability.Martingale.Basic`; it uses
  `MeasureTheory.martingale_of_condExp_sub_eq_zero_nat` to turn the global
  succ-indexed witness into a Mathlib `Martingale` for
  `partialSumsSucc Y`.  The ETC instance is in
  `BanditRLProof.Algorithms.ETCBoundedRewardSource` and uses
  `History.historyFiltrationSucc`,
  `ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource`,
  and
  `ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource`.
- Intended proof route:
  define global and finite-prefix succ-indexed martingale-difference witnesses;
  define `centeredRewardProcess reward baseline = reward - baseline`; build
  global/prefix witnesses for centered rewards directly from adaptedness,
  integrability, and succ-indexed conditional mean-zero contracts; define
  `partialSumsSucc Y n = sum_{i < n} Y (i + 1)` so the Mathlib increment
  `S (i + 1) - S i` is `Y (i + 1)`; apply
  `MeasureTheory.martingale_of_condExp_sub_eq_zero_nat` to obtain the abstract
  partial-sum martingale.  For fixed ETC bounded rewards,
  prove centered reward measurability from the shifted generated history
  filtration's reward coordinate; turn raw bounded-source integrability into
  centered-reward integrability by subtracting the constant arm mean; reuse the
  bounded-source succ-indexed conditional mean-zero wrapper for the
  `condExp_succ_eq_zero` field.
- Regularity contracts:
  ambient measurable space, probability measure, fixed `spec/model/commitArm`,
  reward trace, `ETC.BoundedRewardTraceSource`, timewise reward measurability,
  and prefix bound `n <= spec.explorationPulls * K`.  No random commit arm,
  arbitrary policy predictability, or kernel law is introduced.
- Retrieval evidence:
  local declarations
  `MartingaleDiff.SuccMartingaleDifference`,
  `MartingaleDiff.SuccMartingaleDifferencePrefix`,
  `MartingaleDiff.centeredRewardProcess`,
  `MartingaleDiff.succMartingaleDifference_centeredRewardProcess_of_condExp`,
  `MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp`,
  `MartingaleDiff.partialSumsSucc`,
  `MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference`,
  `MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp`,
  `MartingaleDiff.SuccMartingaleDifferencePrefix.condExp_succ_ae_eq_zero`,
  `ETC.measurable_centeredReward_actionWithCommit_historyFiltrationSucc`,
  `ETC.stronglyAdapted_centeredReward_actionWithCommit_historyFiltrationSucc`,
  `ETC.centeredReward_actionWithCommit_integrable_of_boundedRewardTraceSource`,
  and
  `ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource`;
  Mathlib card `MLIB-MARTINGALE-STOCHASTIC`.
- Status: project-local compiled centered-reward martingale-difference leaf:
  global and finite-prefix witness surfaces, centered reward process builders,
  abstract Mathlib partial-sum `Martingale` wrappers, and fixed-action
  bounded-source centered-reward finite-prefix instance.
- Failure policy:
  do not treat the abstract partial-sum wrapper as a stopping-time theorem, a
  condExpKernel reward-law identification, a concrete adaptive-policy reward
  source, or the final adaptive ETC theorem.  Repair only the martingale
  witness/builder shapes, centered-process definition, or Mathlib martingale
  import in this batch.

`STOPPING-TIME-BUDGET` is compiled locally:

```lean
noncomputable def Budget.budgetExhaustionTime
    {Omega : Type u}
    (spent : Nat -> Omega -> Nat) (budget : Nat) :
    Omega -> WithTop Nat

theorem Budget.isStoppingTime_budgetExhaustionTime_of_adapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {F : MeasureTheory.Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat} (budget : Nat)
    (hspent : MeasureTheory.Adapted F spent) :
    MeasureTheory.IsStoppingTime F
      (Budget.budgetExhaustionTime spent budget)

theorem Budget.measurableSet_budgetExhaustionTime_le_of_adapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {F : MeasureTheory.Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat} (budget n : Nat)
    (hspent : MeasureTheory.Adapted F spent) :
    MeasurableSet[F n]
      {omega | Budget.budgetExhaustionTime spent budget omega <= n}
```

- Local APIs/imports: `BanditRLProof.BudgetStoppingTime`, importing
  `Mathlib.Probability.Process.HittingTime`.
- Intended proof route: define budget exhaustion as Mathlib
  `MeasureTheory.hittingAfter spent (Set.Ici budget) 0`; apply
  `MeasureTheory.Adapted.isStoppingTime_hittingAfter` with
  `measurableSet_Ici`; expose the horizon event by
  `IsStoppingTime.measurableSet_le`.
- Regularity contracts: ambient measurable space, filtration
  `F : Filtration Nat mOmega`, accumulated resource process
  `spent : Nat -> Omega -> Nat`, budget `budget : Nat`, and adaptedness
  `Adapted F spent`.  The current wrapper is `Nat`-valued and starts at time
  `0`.
- Retrieval evidence: Mathlib module
  `Mathlib.Probability.Process.HittingTime`, declarations
  `MeasureTheory.hittingAfter` and
  `MeasureTheory.Adapted.isStoppingTime_hittingAfter`; local declarations
  `Budget.budgetExhaustionTime`,
  `Budget.isStoppingTime_budgetExhaustionTime_of_adapted`, and
  `Budget.measurableSet_budgetExhaustionTime_le_of_adapted`.
- Status: project-local compiled Mathlib import-wrapper leaf.
- Failure policy: do not cite this as a Bandits-with-Knapsacks model, a
  resource feasibility theorem, optional-stopping theorem, Lagrangian
  comparison, or resource-constrained regret theorem.  Split those downstream
  uses into separate leaves after a concrete resource trace/model exists.

`IID-REWARD-FAMILY` is compiled locally:

```lean
theorem IndependenceFoundation.iIndepFun_infinitePi_coord
    (coordLaw : forall i, MeasureTheory.Measure (Omega i))
    [forall i, MeasureTheory.IsProbabilityMeasure (coordLaw i)]
    (X : forall i, Omega i -> Target i)
    (hX : forall i, Measurable (X i)) :
    ProbabilityTheory.iIndepFun
      (fun i omega => X i (omega i))
      (MeasureTheory.Measure.infinitePi coordLaw)

theorem IndependenceFoundation.iIndepFun_rewardTrace_infinitePi
    (coordLaw : Nat -> MeasureTheory.Measure Reward)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)] :
    ProbabilityTheory.iIndepFun
      (fun t (omega : RewardTrace Reward) => omega t)
      (MeasureTheory.Measure.infinitePi coordLaw)
```

- Local APIs/imports: `BanditRLProof.IndependenceFoundation`, importing
  `Mathlib.Probability.Independence.InfinitePi`.
- Intended proof route: apply Mathlib
  `ProbabilityTheory.iIndepFun_infinitePi` to measurable coordinate
  transforms; specialize with `X := fun _ r => r` and `measurable_id` for
  reward traces.
- Regularity contracts: dependent coordinate spaces with measurable spaces,
  probability coordinate laws, and measurable coordinate transforms.  The
  reward-trace specialization uses `RewardTrace Reward := Nat -> Reward`.
  This does not model arm-indexed rewards, conditional independence,
  filtration/history, kernels, posterior laws, or final regret theorems.
- Retrieval evidence: local declarations
  `IndependenceFoundation.iIndepFun_infinitePi_coord` and
  `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`; Mathlib
  declaration `ProbabilityTheory.iIndepFun_infinitePi`.
- Status: project-local compiled Mathlib import-wrapper leaf.
- Failure policy: if a downstream theorem needs arm/time product rewards or
  conditional independence, create a separate source leaf with an explicit
  product index or conditioning sigma-algebra.  Do not overload this wrapper
  into a filtration, kernel-law, conditional-expectation, or final regret
  theorem.

`ETC-CENTERED-REWARD-PAST-IINDEP-SOURCE` is compiled locally:

```lean
theorem ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (iSup fun j : Nat =>
        iSup fun _h : j <= i =>
          MeasurableSpace.comap
            (fun omega : Omega => reward omega j) inferInstance)
      mu

theorem ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (model : FiniteBanditModel K)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : RewardTrace Rat =>
          (((omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (iSup fun j : Nat =>
        iSup fun _h : j <= i =>
          MeasurableSpace.comap
            (fun omega : RewardTrace Rat => omega j) inferInstance)
      (MeasureTheory.Measure.infinitePi coordLaw)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`,
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`,
  `ProbabilityTheory.iIndepFun.iIndep`,
  `ProbabilityTheory.indep_iSup_of_disjoint`,
  `ProbabilityTheory.indep_of_indep_of_le_left`,
  `MeasurableSpace.comap`, `iSup`, and
  `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`.
- Intended proof route: turn reward-coordinate `iIndepFun` into independence
  of the coordinate sigma-algebras, use Mathlib's disjoint-`iSup`
  independence theorem to separate singleton future coordinate `{i + 1}` from
  the past set `{j | j <= i}`, then shrink the left sigma-algebra through the
  measurable map `r ↦ ((r - model.mean b : Rat) : Real)`.  The infinitePi
  theorem instantiates the reward-coordinate independence by
  `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`.
- Regularity contracts: ambient measurable space, timewise reward-coordinate
  measurability, reward-coordinate independence, model arm `b`, and time `i`.
  The infinitePi specialization requires probability coordinate laws.
- Retrieval evidence: local declarations
  `ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward` and
  `ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi`; local
  declaration `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`;
  Mathlib declarations `ProbabilityTheory.indep_iSup_of_disjoint` and
  `ProbabilityTheory.iIndepFun_infinitePi`.
- Status: project-local compiled product-law/history subleaf.
- Failure policy: this leaf proves independence only from the reward-only past
  coordinate sigma-algebra.  The next leaf adds deterministic fixed-action
  generators and proves full `History.historyFiltrationSucc` independence.  It
  does not derive conditional MGF witnesses or finish the adaptive ETC theorem.

`ETC-CENTERED-REWARD-HISTORY-IINDEP-SOURCE` is compiled locally:

```lean
theorem ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat) :
    (History.historyFiltrationSucc
      (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
      reward
      (fun _t : Nat => measurable_const)
      hreward i : MeasurableSpace Omega) <=
    (iSup fun j : Nat =>
      iSup fun _h : j <= i =>
        MeasurableSpace.comap
          (fun omega : Omega => reward omega j) inferInstance)

theorem ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      mu

theorem ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : RewardTrace Rat =>
          (((omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (History.historyFiltrationSucc
        (fun _omega : RewardTrace Rat => ETC.actionWithCommit spec commitArm)
        (fun omega : RewardTrace Rat => omega)
        (fun _t : Nat => measurable_const)
        (fun t : Nat => measurable_pi_apply t)
        i)
      (MeasureTheory.Measure.infinitePi coordLaw)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses`,
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`,
  `History.historyFiltrationSucc`, `History.historyFiltration_apply`,
  `MeasurableSpace.generateFrom_le`, `ProbabilityTheory.indep_of_indep_of_le_right`,
  and `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi`.
- Intended proof route: unfold the shifted history filtration, show fixed
  `actionWithCommit` singleton preimages are deterministic `univ` or `empty`,
  send reward generators with index `< i + 1` into the reward-only past
  `iSup`, then shrink the right sigma-algebra of the reward-only independence
  theorem.
- Regularity contracts: ambient measurable space, fixed `spec` and `commitArm`,
  timewise reward measurability, reward-coordinate independence, model arm `b`,
  and time `i`.  The infinitePi specialization requires probability coordinate
  laws.
- Retrieval evidence: local declarations
  `ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup`,
  `ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward`,
  and `ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi`; Mathlib
  declaration `ProbabilityTheory.indep_of_indep_of_le_right`.
- Status: project-local compiled full-history fixed-action independence leaf.
- Failure policy: this leaf is fixed-action only.  It does not prove arbitrary
  policy predictability, conditional MGF witnesses, or the final adaptive ETC
  theorem.

`INT-REWARD-BOUNDED` /
`ETC-CENTERED-REWARD-BOUNDED-INTEGRABLE-SOURCE` is compiled locally:

```lean
theorem ETC.centeredReward_integrable_of_mem_Icc
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu)) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu

theorem ETC.centeredReward_integrable_of_boundedRewardTraceSource
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`,
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`,
  `MeasureTheory.Integrable.of_mem_Icc`, `AEMeasurable`,
  `Filter.Eventually`, and `ETC.BoundedRewardTraceSource.meas/bound`.
- Intended proof route: apply `MeasureTheory.Integrable.of_mem_Icc` to the
  Real-cast reward coordinate using a.e. measurability and the a.s. interval
  bound.  The source-contract wrapper instantiates the arm as
  `ETC.actionWithCommit spec commitArm t` and uses `source.meas t ht` plus
  `source.bound t ht`.
- Regularity contracts: finite measure, reward-coordinate a.e. measurability,
  and an a.s. interval bound.  The source wrapper requires a probability
  measure, a `BoundedRewardTraceSource`, and an exploration-horizon proof.
- Retrieval evidence: local declarations
  `ETC.centeredReward_integrable_of_mem_Icc` and
  `ETC.centeredReward_integrable_of_boundedRewardTraceSource`; Mathlib
  declaration `MeasureTheory.Integrable.of_mem_Icc`.
- Status: project-local compiled bounded-to-integrable source.
- Failure policy: this leaf proves only raw reward integrability from bounded
  Real-valued rewards.  It does not construct a reward kernel and does not
  produce conditional MGF witnesses.

`ETC-CENTERED-REWARD-ZERO-INTEGRAL-SOURCE` is compiled locally:

```lean
theorem ETC.centeredReward_integral_eq_zero_of_integral_eq_mean
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (hint : MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hmean :
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0

theorem ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu
      (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0

theorem ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) =
      0
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`,
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`, `MeasureTheory.integral`,
  `MeasureTheory.integral_sub`, `MeasureTheory.integrable_const`, and
  `ETC.BoundedRewardTraceSource.meas/bound/mean`.
- Intended proof route: rewrite the Rat-centered reward as the Real subtraction
  `reward - mean`, use `integral_sub` with raw reward integrability and
  constant integrability, simplify the constant integral under
  `[IsProbabilityMeasure mu]`, and rewrite the raw integral with `hmean`.
  The bounded-Icc wrapper obtains raw integrability from
  `ETC.centeredReward_integrable_of_mem_Icc`; the source-contract wrapper
  obtains it from `ETC.centeredReward_integrable_of_boundedRewardTraceSource`
  and uses `source.mean t ht`.
- Regularity contracts: probability measure, raw reward integrability at the
  coordinate or bounded reward facts sufficient to derive it, exact raw reward
  mean identity, and for the source wrapper an action-matched
  `BoundedRewardTraceSource` plus an exploration-horizon proof `ht`.
- Retrieval evidence: local declarations
  `ETC.centeredReward_integral_eq_zero_of_integral_eq_mean`,
  `ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean`, and
  `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`;
  Mathlib declarations `MeasureTheory.integral_sub` and
  `MeasureTheory.integrable_const`.
- Status: project-local compiled zero-integral source.
- Failure policy: this leaf only discharges the zero-integral side condition
  after raw integrability or bounded reward facts plus exact mean are
  available.  It does not construct a reward kernel and does not derive
  conditional MGF witnesses.

Current boundary after this leaf:

- `ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is compiled locally below; the
  conditional route now has a witness package/consumer and a compiled
  fixed-commit shifted-history `StronglyAdapted` field, a zero-summand MGF
  source, sampled-arm conditional MGF transfer, and reward-level conditional
  witness contract, plus an independence-based centered-reward conditional
  mean-zero wrapper, its bounded-source action-matched mean-zero wrapper,
  fixed-prefix martingale-difference witness surface, reward-only and full
  fixed-action history independence bridges, a bounded-to-integrable source,
  and a zero-integral source from bounded exact-mean rewards.  It still needs
  concrete reward-law/kernel conditional MGF witnesses before final adaptive
  ETC theorem work.

`ETC-PAIRWISE-TAIL-PRODUCER-SUBGAUSS` is compiled locally:

```lean
theorem ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Fin K -> Idx -> Omega -> Real)
    (c : Fin K -> Idx -> NNReal)
    (eps : Fin K -> Real)
    -- plus non-best-arm independence, sub-Gaussian, event-subset, and tail
    -- domination hypotheses
    :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCPairwiseSubGaussianTail`, consuming
  `ETC.PairwiseEmpMeanTailContract` and
  `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun`.
- Intended proof route: for each non-best arm, use `mu.mono` on the supplied
  event subset, apply the ENNReal sub-Gaussian finite-sum tail wrapper, then
  apply the supplied tail-domination inequality.
- Regularity contracts: `[MeasurableSpace Omega]`, finite measure `mu`,
  `spec`, `model`, `commitArm`, `reward`, `tail`, common finite index set
  `idx`, abstract real-valued summands `X`, sub-Gaussian parameters `c`,
  thresholds `eps`, non-best-arm `iIndepFun` and `HasSubgaussianMGF`
  witnesses, event subset hypotheses, and tail RHS domination hypotheses.  No
  proof of the event subset, reward-law instantiation, filtration, conditional
  expectation, or final theorem facts.
- Retrieval evidence: local declaration is
  `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`; it consumes
  `Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun` and the compiled
  `ETC.PairwiseEmpMeanTailContract` surface.
- Status: project-local compiled sub-Gaussian pairwise-tail producer surface.
- Failure policy: if downstream ETC specialization fails, split only the
  concrete reward-difference bridge, Rat-to-Real reward-difference shape, `sumRewards` to
  exploration `Finset.sum`, or independence transport leaves; do not pivot to
  conditional sub-Gaussian, filtration/history, bounded Hoeffding, or final ETC
  theorem in the same batch.

Current boundary after this leaf:

- `ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` is compiled locally below.

`ETC-EMPMEAN-EVENT-SUBSET-SUMREWARDS-TAIL-EVENT` is compiled locally:

```lean
theorem ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    {Idx : Type v}
    (idx : Finset Idx)
    (X : Idx -> Omega -> Real)
    (eps : Real)
    (himp :
      forall omega : Omega,
        sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            model.bestArm (spec.explorationPulls * K) <=
          sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            a (spec.explorationPulls * K) ->
        eps <= idx.sum (fun i => X i omega)) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega | eps <= idx.sum (fun i => X i omega)}
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCEmpiricalMean`, importing
  `Mathlib.Algebra.Order.Field.Rat`, `Mathlib.Data.Real.Basic`, and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Intended proof route: introduce `omega`, apply the supplied pointwise
  implication `himp`, and obtain its fixed-horizon `sumRewards` comparison
  premise from
  `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos`.
- Regularity contracts: `{Omega : Type u}`, `{K : Nat}`,
  `spec : ETC.Spec K`, `model : FiniteBanditModel K`,
  `commitArm : Fin K`, stochastic `reward : Omega -> RewardTrace Rat`,
  arm `a`, `0 < spec.explorationPulls`, finite index set `idx`, abstract
  real summands `X`, threshold `eps`, and a pointwise implication from the
  fixed-horizon `sumRewards` comparison to the abstract tail event.  No
  centered reward-difference construction, measure, independence,
  sub-Gaussianity, filtration, conditional expectation, or final ETC theorem.
- Retrieval evidence: local declarations are
  `ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos` and
  `ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp`;
  the latter has been checked by `lake build Tests` and appears in
  `python3 tools/bandit.py list-lean-decls "empMeanAtExploration_ge_best_event_subset" --statement`.
- Status: project-local compiled event-shape bridge.
- Failure policy: if downstream specialization fails, split only the concrete
  centered reward-difference summand definition, the `sumRewards`-to-`Finset`
  algebra, or Rat-to-Real casting bridge; do not pivot to conditional
  sub-Gaussian, filtration/history, bounded Hoeffding, or final ETC theorem in
  the same batch.

Current boundary after this leaf:

- `ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` and
  `ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` are compiled locally below.

`ETC-SUMREWARDS-PAIRWISE-DIFF-FINSET` is compiled locally:

```lean
noncomputable def ETC.centeredPairwiseRewardDiff
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (omega : Omega) : Real

noncomputable def ETC.centeredPairwiseGapThreshold
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (a : Fin K) : Real

theorem ETC.sumRewards_le_imp_centered_pairwise_sum_ge
    (hcount_a : pullCount action a n = m)
    (hcount_b : pullCount action b n = m)
    (hraw : sumRewards action reward b n <=
      sumRewards action reward a n) :
    (m : Rat) * (muB - muA) <=
      (Finset.range n).sum (fun t : Nat =>
        (if action t = a then reward t - muA else 0) +
        (if action t = b then muB - reward t else 0))

theorem ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Set.Subset
      {omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega |
        ETC.centeredPairwiseGapThreshold spec model a <=
          (Finset.range (spec.explorationPulls * K)).sum (fun t =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)}
```

- Local APIs/imports: `BanditRLProof.Algorithms.ETCSumRewardsDiff`, consuming
  `BanditRLProof.Algorithms.ETCEmpiricalMean`,
  `BanditRLProof.MathlibWrappers`, Rat order/cast imports, and `Ring`.
- Intended proof route: rewrite selected centered sums to `sumRewards` minus
  `pullCount * mean`, use the equal exploration-horizon pull counts for arm
  `a` and `model.bestArm`, then cast the Rat finite sum to Real.
- Regularity contracts: deterministic fixed-commit ETC exploration horizon,
  `0 < spec.explorationPulls`, `reward : Omega -> RewardTrace Rat`, and
  equal exploration counts from `ETC.actionWithCommit`; no measure,
  independence, sub-Gaussianity, filtration, or final ETC theorem.
- Retrieval evidence: local declarations are `ETC.centeredPairwiseRewardDiff`,
  `ETC.centeredPairwiseGapThreshold`,
  `ETC.sumRewards_le_imp_centered_pairwise_sum_ge`, and
  `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`.
- Status: project-local compiled deterministic centered-diff bridge.
- Failure policy: if downstream probability work fails, split only
  independence witness transport, sub-Gaussian witness transport, or tail RHS
  shaping; do not rewrite this deterministic bridge or pivot to final ETC.

`ETC-PAIRWISE-TAIL-PRODUCER-CENTERED-DIFF` is compiled locally:

```lean
theorem ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t => c a t) : NNReal) : Real)))) <= tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCPairwiseCenteredSubGaussianTail`, consuming
  `ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds`,
  `ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event`,
  and `FiniteBanditModel.mean_le_bestArm_mean`.
- Intended proof route: instantiate the abstract sub-Gaussian producer with
  `idx := Finset.range (spec.explorationPulls * K)`,
  `X := ETC.centeredPairwiseRewardDiff`, and
  `eps := ETC.centeredPairwiseGapThreshold`; prove `0 <= eps` from
  `model.mean a <= model.mean model.bestArm`.
- Regularity contracts: finite measure `mu`, explicit non-best-arm
  `iIndepFun` and `HasSubgaussianMGF` witnesses for the concrete summands,
  and explicit tail RHS domination; no reward-law witness proof, filtration,
  conditional expectation, or final ETC theorem.
- Retrieval evidence: local declaration is
  `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`.
- Status: project-local compiled centered-diff sub-Gaussian producer
  specialization.
- Failure policy: the next leaf should be
  `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS`,
  `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS`, or a minimal conditional reward-law
  witness for the compiled conditional sub-Gaussian wrapper.  Do not
  start full Hoeffding, martingale, UCB, Thompson/EXP3/Tsallis/OFUL/RL, or
  final ETC work in the same batch.

Current boundary after this leaf:

- `ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally below.

`ETC-CENTERED-DIFF-SUBGAUSSIAN-WITNESS-CONTRACT` is compiled locally:

```lean
structure ETC.CenteredDiffSubGaussianWitnesses
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal) where
  c : Fin K -> Nat -> NNReal
  indep : ...
  subG : ...
  tail_bound : ...

theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
    (w :
      ETC.CenteredDiffSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCenteredDiffSubGaussianWitnesses`, consuming
  `ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds`.
- Intended proof route: package the concrete reward-law fields already needed
  by the centered-diff producer, then call the compiled producer theorem.
- Regularity contracts: `[MeasurableSpace Omega]`, finite measure `mu` for
  the consumer theorem, `spec`, `model`, `commitArm`, `reward`, `tail`, witness
  field `c`, non-best-arm independence, per-index `HasSubgaussianMGF` facts on
  `Finset.range (spec.explorationPulls * K)`, and tail RHS domination.
- Retrieval evidence: local declarations are
  `ETC.CenteredDiffSubGaussianWitnesses` and
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`.
- Status: project-local compiled witness contract surface.
- Failure policy: the next leaf should construct this witness package from an
  explicit reward-law assumption, or split a minimal conditional reward-law
  witness for the compiled history filtration and conditional sub-Gaussian
  wrapper.  Do not pivot to final ETC, UCB, Thompson/EXP3/Tsallis/OFUL/RL, or
  broad kernel work in the same batch.

Current boundary after this leaf:

- `ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` is compiled locally below.

`ETC-CENTERED-DIFF-SUBGAUSSIAN-CANONICAL-TAIL` is compiled locally:

```lean
noncomputable def ETC.centeredDiffSubGaussianTail
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (c : Fin K -> Nat -> NNReal)
    (a : Fin K) : ENNReal

noncomputable def ETC.centeredDiffSubGaussianWitnesses_of_indep_subG
    (h_indep : ...)
    (h_subG : ...) :
    ETC.CenteredDiffSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c)

theorem ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep : ...)
    (h_subG : ...) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCenteredDiffCanonicalTail`, consuming
  `ETC.CenteredDiffSubGaussianWitnesses` and
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses`.
- Intended proof route: choose the exact exponential tail budget from the
  independent sub-Gaussian route, build the witness package with the supplied
  independence and `HasSubgaussianMGF` fields, and discharge tail domination by
  definitional equality.
- Regularity contracts: `[MeasurableSpace Omega]`, finite measure `mu` for the
  contract theorem, `spec`, `model`, `commitArm`, `reward`,
  `c : Fin K -> Nat -> NNReal`, `0 < spec.explorationPulls`, non-best-arm
  independence, and per-exploration-index `HasSubgaussianMGF` witnesses.
- Retrieval evidence: local declarations are
  `ETC.centeredDiffSubGaussianTail`,
  `ETC.centeredDiffSubGaussianWitnesses_of_indep_subG`, and
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`.
- Status: project-local compiled canonical tail helper.
- Failure policy: the next leaf should prove or import the independence and
  `HasSubgaussianMGF` witness fields for `ETC.centeredPairwiseRewardDiff`, or
  assemble the bounded/source conditional MGF and mean-zero witness fields for
  the compiled reward-level conditional source contract.  Full policy
  predictability is a separate stronger route.  Do not pivot to final ETC or
  another deterministic `sumRewards` bridge.

Current boundary after this leaf:

- `ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` is compiled locally below.

`ETC-WRONG-COMMIT-CANONICAL-SUBGAUSSIAN-BOUND` is compiled locally:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep : ...)
    (h_subG : ...) :
    mu {omega | (ETC.argmaxCommitOracle hK).choose
      (fun a => ETC.empMeanAtExploration spec commitArm (reward omega) a) =
      model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model c)
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCWrongCommitCanonicalTail`, consuming
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG` and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract`.
- Intended proof route: instantiate the compiled pairwise-tail contract with
  the canonical centered-diff tail, then feed that contract to the compiled
  concrete argmax-oracle filtered-sum probability consumer.
- Regularity contracts: `[MeasurableSpace Omega]`, finite measure `mu`,
  `hK : 0 < K`, `spec`, `model`, fixed `commitArm`, stochastic `reward`,
  variance proxies `c`, `0 < spec.explorationPulls`, non-best-arm
  independence, and per-exploration-index `HasSubgaussianMGF` witnesses for
  `ETC.centeredPairwiseRewardDiff`.
- Retrieval evidence: local declarations are
  `ETC.centeredDiffSubGaussianTail`,
  `ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG`, and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`.
- Status: project-local compiled canonical wrong-commit probability bound.
- Failure policy: the next leaf should prove or import the reward-law witness
  fields for `ETC.centeredPairwiseRewardDiff`, or split a minimal conditional
  reward-law witness for the compiled conditional sub-Gaussian wrapper.  Do not
  treat this as a full ETC expected-regret theorem.

Current boundary after this leaf:

- `ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` is compiled locally below.

`ETC-CENTERED-DIFF-INDEPENDENCE-WITNESS` is compiled locally:

```lean
theorem ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu) :
    forall a : Fin K, (a = model.bestArm -> False) ->
      ProbabilityTheory.iIndepFun
        (fun t omega =>
          ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega)
        mu
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardIndependence`, consuming
  `ETC.centeredPairwiseRewardDiff` and Mathlib
  `ProbabilityTheory.iIndepFun.comp`.
- Intended proof route: define the time-indexed deterministic transform
  `Rat -> Real` matching the centered pairwise reward-difference summand, then
  apply `iIndepFun.comp` to trace-level reward-coordinate independence.
- Regularity contracts: `[MeasurableSpace Omega]`, `mu`, `spec`, `model`,
  fixed `commitArm`, stochastic `reward`, and
  `iIndepFun (fun t omega => reward omega t) mu`; no finite-measure,
  sub-Gaussian, kernel, filtration, or conditional-expectation assumptions.
- Retrieval evidence: local declarations are
  `ETC.centeredPairwiseRewardDiff` and
  `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`; Mathlib
  declaration is `ProbabilityTheory.iIndepFun.comp`.
- Status: project-local compiled deterministic independence transfer.
- Failure policy: this does not prove trace-level reward independence from a
  stochastic environment.  The next leaf should supply a concrete source for
  that trace-level independence or prove/import `HasSubgaussianMGF` witnesses
  for `ETC.centeredPairwiseRewardDiff`.  Do not start final ETC expected-regret
  assembly from this leaf alone.

Current boundary after this leaf:

- `ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` and
  `ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` are compiled locally below.

`ETC-CENTERED-DIFF-SUBGAUSSIAN-REWARD-WITNESS` is compiled locally:

```lean
noncomputable def ETC.centeredPairwiseRewardDiffVarianceProxy

theorem ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega => (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega =>
        ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward a t)
      mu
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`, consuming
  `ETC.centeredPairwiseRewardDiff` and Mathlib
  `ProbabilityTheory.HasSubgaussianMGF.neg` / `fun_zero` / `congr`.
- Intended proof route: split on whether the ETC action at time `t` is arm
  `a`, the best arm, or neither; use the supplied centered reward sub-Gaussian
  witness in the first case, `HasSubgaussianMGF.neg` in the best-arm case, and
  `HasSubgaussianMGF.fun_zero` in the zero case.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[IsZeroOrProbabilityMeasure mu]`, `spec`, `model`, `commitArm`, `reward`,
  `cReward`, non-best arm `a`, time `t`, and a per-pulled-arm centered reward
  sub-Gaussian witness.
- Retrieval evidence: local declarations are
  `ETC.centeredPairwiseRewardDiffVarianceProxy` and
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`.
- Status: project-local compiled deterministic sub-Gaussian transfer.
- Failure policy: this does not prove centered reward sub-Gaussianity from a
  distribution, boundedness, kernel, or filtration.  The bounded-reward source
  leaf below now supplies one Mathlib-backed route from a.e. interval bounds
  plus exact mean identities; remaining work is to source those facts and
  trace-level reward-coordinate independence from an environment, or assemble
  bounded/source conditional MGF and mean-zero witness fields for the compiled
  reward-level conditional source contract.  Full policy predictability remains
  a separate stronger leaf.

`ETC-WRONG-COMMIT-REWARD-LAW-SUBGAUSSIAN-BOUND` is compiled locally:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_subG :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega => (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    mu {omega | (ETC.argmaxCommitOracle hK).choose
      (fun a => ETC.empMeanAtExploration spec commitArm (reward omega) a) =
      model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCCenteredDiffRewardSubGaussian`, consuming
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`,
  `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`, and
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`.
- Intended proof route: instantiate the canonical wrong-commit bound with the
  action-case variance proxy, discharge the centered-diff independence field
  via reward-coordinate `iIndepFun`, and discharge the centered-diff
  sub-Gaussian field via per-time centered reward witnesses.
- Regularity contracts: `[MeasurableSpace Omega]`, finite/probability-like
  measure classes, `hK : 0 < K`, `spec`, `model`, `commitArm`, `reward`,
  `cReward`, `0 < spec.explorationPulls`, trace-level reward-coordinate
  independence, and per-arm/time centered reward sub-Gaussian witnesses for
  `t < spec.explorationPulls * K`.
- Retrieval evidence: local declarations are
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`,
  `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`, and
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`.
- Status: project-local compiled reward-coordinate-law wrong-commit bound.
- Failure policy: this is still a wrong-commit probability theorem, not final
  ETC expected regret.  It does not construct the stochastic reward trace law;
  the bounded-reward source leaf below now removes the centered reward
  sub-Gaussianity assumption when a.e. bounds and exact mean identities are
  available.  The remaining next leaf should prove/import trace-level
  reward-coordinate independence, a.s. boundedness, and exact mean identities
  from an explicit model, boundedness assumption, or kernel/filtration route.

Current boundary after this leaf:

- `ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` and
  `ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` are compiled locally
  below.  The latter is the strong all-arm wrapper; the practical
  action-matched fixed-commit wrappers and source contract are also compiled
  below.

`ETC-CENTERED-REWARD-BOUNDED-SUBGAUSSIAN-SOURCE` is compiled locally:

```lean
noncomputable def ETC.centeredRewardBoundVarianceProxy

theorem ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean
    (hmeas : AEMeasurable
      (fun omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega =>
        Set.Icc (lo a t) (hi a t)
          (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu
      (fun omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega => (((reward omega t - model.mean a : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy lo hi a t) mu
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`, consuming
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`
  from `BanditRLProof.ConcentrationSubGaussian`.
- Intended proof route: instantiate the generic bounded-centered Hoeffding MGF
  wrapper on the raw reward coordinate cast to `Real`, then rewrite the proxy
  and centered variable into the ETC arm/time shape.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[IsProbabilityMeasure mu]`, a.e. measurability, a.s. interval bounds
  `Set.Icc (lo a t) (hi a t)`, and exact mean identity for the reward
  coordinate.
- Retrieval evidence: local declarations are
  `ETC.centeredRewardBoundVarianceProxy` and
  `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`;
  generic local declarations are `Concentration.intervalVarianceProxy` and
  `Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq`;
  Mathlib declaration is `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
- Status: project-local compiled bounded reward sub-Gaussian source.
- Failure policy: this does not prove the reward is bounded or has the right
  mean from a kernel or environment model.  Those source facts remain explicit.

`ETC-WRONG-COMMIT-BOUNDED-REWARD-SUBGAUSSIAN-BOUND` is compiled locally:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas : ...)
    (h_reward_bound : ...)
    (h_reward_mean : ...) :
    mu {omega | (ETC.argmaxCommitOracle hK).choose
      (fun a => ETC.empMeanAtExploration spec commitArm (reward omega) a) =
      model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`, consuming
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`
  and
  `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`.
- Intended proof route: use bounded rewards plus exact mean identities to
  produce per-time centered reward `HasSubgaussianMGF`, then feed those
  witnesses and trace-level reward-coordinate independence into the compiled
  reward-coordinate-law wrong-commit theorem.
- Regularity contracts: probability measure `mu`, `hK`, `spec`, `model`,
  `commitArm`, `reward`, interval functions `lo hi`, positive exploration
  count, trace-level reward-coordinate independence, a.e. measurability, a.s.
  interval bounds, and exact mean identities over the exploration horizon.
- Retrieval evidence: local declarations are
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered`,
  `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean`, and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG`.
- Status: project-local compiled bounded-reward wrong-commit probability
  bound.  This is a strong all-arm theorem: it assumes the same observed
  `reward omega t` has the right centered witness for every arm `b`.
- Failure policy: this is still not final ETC expected regret and still does
  not construct the reward trace law.  For a realistic fixed-commit ETC trace,
  use the action-matched wrapper below, where bounds and mean identities are
  keyed to `ETC.actionWithCommit spec commitArm t`.

`ETC-WRONG-COMMIT-ACTION-MATCHED-REWARD-SUBGAUSSIAN-BOUND` is compiled locally:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_subG :
      forall t, t < spec.explorationPulls * K ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega =>
            (((reward omega t -
              model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real)))
          (cReward (ETC.actionWithCommit spec commitArm t) t) mu) :
    mu {omega | (ETC.argmaxCommitOracle hK).choose
      (fun a => ETC.empMeanAtExploration spec commitArm (reward omega) a) =
      model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`, consuming
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail`,
  `ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward`, and
  `ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_centeredReward`.
- Intended proof route: feed the canonical wrong-commit theorem with
  centered-diff independence from trace-level reward independence; when the
  pulled arm at time `t` is `b`, rewrite the action-matched centered reward
  witness along `ETC.actionWithCommit spec commitArm t = b`.
- Regularity contracts: finite/probability-like measure classes, fixed
  `spec`, `model`, `commitArm`, trace-level reward-coordinate independence,
  exploration positivity, and per-time centered reward sub-Gaussian witness
  for the arm actually pulled at each exploration time.
- Retrieval evidence: local declaration is
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_centeredReward_subG`.
- Status: project-local compiled action-matched reward sub-Gaussian
  wrong-commit probability bound.
- Failure policy: this still assumes the action-matched centered reward
  sub-Gaussian witness.  It does not prove boundedness, exact means,
  independence, product laws, filtration, or final ETC expected regret.

`ETC-WRONG-COMMIT-ACTION-MATCHED-BOUNDED-REWARD-BOUND` is compiled locally:

```lean
theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas : forall t, t < spec.explorationPulls * K ->
      AEMeasurable (fun omega => (((reward omega t : Rat) : Real))) mu)
    (h_reward_bound : forall t, t < spec.explorationPulls * K ->
      Filter.Eventually
        (fun omega =>
          Set.Icc
            (lo (ETC.actionWithCommit spec commitArm t) t)
            (hi (ETC.actionWithCommit spec commitArm t) t)
            (((reward omega t : Rat) : Real)))
        (MeasureTheory.ae mu))
    (h_reward_mean : forall t, t < spec.explorationPulls * K ->
      MeasureTheory.integral mu
        (fun omega => (((reward omega t : Rat) : Real))) =
      (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    mu {omega | (ETC.argmaxCommitOracle hK).choose
      (fun a => ETC.empMeanAtExploration spec commitArm (reward omega) a) =
      model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSubGaussian`, consuming
  `ETC.centeredReward_hasSubgaussianMGF_of_mem_Icc_integral_eq_mean` and the
  action-matched reward sub-Gaussian wrong-commit wrapper.
- Intended proof route: for each exploration time, apply Mathlib's bounded
  reward source lemma to the actually pulled arm
  `ETC.actionWithCommit spec commitArm t`, then feed the resulting
  action-matched centered reward witness into the action-matched
  wrong-commit theorem.
- Regularity contracts: probability measure `mu`, `hK`, `spec`, `model`,
  `commitArm`, `reward`, interval functions `lo hi`, positive exploration
  count, trace-level reward-coordinate independence, timewise a.e.
  measurability, action-matched a.s. interval bounds, and action-matched exact
  mean identities over the exploration horizon.
- Retrieval evidence: local declaration is
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered`.
- Status: project-local compiled practical fixed-commit bounded-reward
  wrong-commit probability bound.
- Failure policy: this does not construct the stochastic reward trace law.
  The next source leaf should prove/import these action-matched facts from a
  product-coordinate law or another explicit environment model.

`ETC-BOUNDED-REWARD-TRACE-SOURCE-CONTRACT` is compiled locally:

```lean
structure ETC.BoundedRewardTraceSource

theorem ETC.centeredReward_integrable_of_boundedRewardTraceSource

theorem ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean

theorem ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource

theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardSource`, consuming the
  action-matched bounded-reward wrong-commit wrapper.
- Intended proof route: package trace-level reward-coordinate independence,
  timewise a.e. measurability, action-matched a.s. interval bounds, and
  action-matched exact mean identities into one reusable source structure;
  provide thin consumers for raw reward integrability, centered reward
  zero-integral, centered reward sub-Gaussianity, and the final fixed-commit
  wrong-commit probability bound.
- Regularity contracts: `[MeasurableSpace Omega]`,
  `[IsProbabilityMeasure mu]`, `spec`, `model`, `commitArm`, `reward`, `lo`,
  `hi`, and source fields only over `t < spec.explorationPulls * K`.
- Retrieval evidence: local declarations are `ETC.BoundedRewardTraceSource`,
  `ETC.centeredReward_integrable_of_boundedRewardTraceSource`,
  `ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean`,
  `ETC.centeredReward_hasSubgaussianMGF_of_boundedRewardTraceSource`, and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource`.
- Status: project-local compiled action-matched source-contract surface.
- Failure policy: this is still a contract, not a concrete source.  The next
  leaf should prove/import the contract fields from a concrete stochastic
  source or split a conditional reward-law witness leaf.  Full policy
  predictability remains separate.

`ETC-BOUNDED-REWARD-INFINITEPI-SOURCE` and
`ETC-WRONG-COMMIT-INFINITEPI-BOUNDED-REWARD-SOURCE` are compiled locally:

```lean
theorem ETC.boundedRewardTraceSource_infinitePi_actionWithCommit
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (h_coord_bound : forall t, t < spec.explorationPulls * K ->
      Filter.Eventually
        (fun r : Rat =>
          Set.Icc
            (lo (ETC.actionWithCommit spec commitArm t) t)
            (hi (ETC.actionWithCommit spec commitArm t) t)
            (((r : Rat) : Real)))
        (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean : forall t, t < spec.explorationPulls * K ->
      MeasureTheory.integral (coordLaw t)
        (fun r : Rat => (((r : Rat) : Real))) =
      (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    ETC.BoundedRewardTraceSource
      (MeasureTheory.Measure.infinitePi coordLaw)
      spec model commitArm
      (fun omega : RewardTrace Rat => omega) lo hi

theorem ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean
    ... :
    MeasureTheory.Measure.infinitePi coordLaw
      {omega : RewardTrace Rat |
        (ETC.argmaxCommitOracle hK).choose
          (fun a => ETC.empMeanAtExploration spec commitArm omega a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`, consuming
  `BanditRLProof.IndependenceFoundation`,
  `Mathlib.Data.Rat.Encodable`, and the action-matched source contract.
- Intended proof route: instantiate `ETC.BoundedRewardTraceSource` with
  `mu := Measure.infinitePi coordLaw` and reward trace identity.  Use
  `IndependenceFoundation.iIndepFun_rewardTrace_infinitePi` for coordinate
  independence,
  `Measure.infinitePi_map_eval` plus `MeasureTheory.ae_of_ae_map` for
  coordinate a.s. bounds, and `MeasureTheory.integral_map` plus
  `Measure.infinitePi_map_eval` for exact coordinate mean identities.  Then
  consume the source contract through the compiled wrong-commit wrapper.
- Regularity contracts: probability coordinate laws `coordLaw`, fixed `spec`,
  `model`, `commitArm`, interval functions `lo hi`, exploration positivity for
  the direct probability theorem, action-matched coordinate a.s. bounds, and
  action-matched coordinate mean identities.
- Retrieval evidence: local declarations are
  `ETC.boundedRewardTraceSource_infinitePi_actionWithCommit` and
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`.
- Status: project-local compiled fixed-commit product-coordinate reward source
  and wrong-commit probability bound.
- Failure policy: this is not final ETC expected regret.  It has no adaptive
  filtration, no random selected commit-arm trace, and no expected-regret
  assembly.

`ETC-WRONG-COMMIT-REGRET-ASSEMBLY-POINTWISE` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
    {Omega : Type u} {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat) (badGapBound : Rat)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (omega : Omega) :
    pseudoRegret model (ETC.actionWithCommit spec (commit omega))
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) *
        (if commit omega = model.bestArm then 0 else badGapBound))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`, consuming
  `BanditRLProof.Algorithms.ETCRegretLemmas` and
  `Mathlib.Data.Nat.Cast.Order.Basic`.
- Intended proof route: split on `commit omega = model.bestArm`.  In the best
  branch, consume
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm`.
  In the wrong branch, consume
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap`
  and use `mul_le_mul_of_nonneg_left` with `Nat.cast_nonneg` to replace
  `model.gap (commit omega)` by `badGapBound`.
- Regularity contracts: an arbitrary index type `Omega`, fixed `spec` and
  `model`, selector `commit : Omega -> Fin K`, suffix length `r`, and an
  explicit upper bound on all non-best model gaps.  No measure or
  measurability is assumed.
- Retrieval evidence: local declaration is
  `ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap`.
- Status: project-local compiled pointwise deterministic regret assembly.
- Failure policy: do not treat this as expected regret.  The next leaf should
  integrate the wrong-commit-shaped suffix penalty in `ENNReal` and connect it
  to a probability bound for `{omega | commit omega = model.bestArm -> False}`.

`ETC-WRONG-COMMIT-LINTEGRAL-REGRET-ASSEMBLY` is compiled locally:

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commit : Omega -> Fin K) (r : Nat)
    (badGapBound : Rat) (pWrong : ENNReal)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (hmeas_wrong :
      MeasurableSet {omega : Omega | commit omega = model.bestArm -> False})
    (hprob_wrong :
      mu {omega : Omega | commit omega = model.bestArm -> False} <= pWrong) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec (commit omega))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) * pWrong
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`, consuming
  `Mathlib.MeasureTheory.Integral.Lebesgue.Add`,
  `Mathlib.MeasureTheory.Measure.Typeclasses.Probability`,
  `Mathlib.Data.ENNReal.Real`, and
  `BanditRLProof.Algorithms.ETCWrongCommitRegretAssembly`.
- Intended proof route: use the pointwise bridge to get an
  `ENNReal.ofReal` bound by a constant exploration budget plus a wrong-event
  indicator carrying the suffix budget.  Then apply `lintegral_mono`,
  `lintegral_add_left`, `lintegral_const`,
  `lintegral_indicator_const`, `IsProbabilityMeasure.measure_univ`, and the
  abstract `hprob_wrong`.
- Regularity contracts: probability measure `mu`, wrong-event measurability,
  a non-best gap upper bound `badGapBound`, and an abstract wrong-commit
  probability upper bound `pWrong`.  This is still not a Bochner/Rat-valued
  expected-regret theorem.
- Retrieval evidence: local declaration is
  `ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`.
- Status: project-local compiled `ENNReal.ofReal` lower-integral regret
  assembly with an abstract wrong-probability supplier.
- Failure policy: do not fold in reward-law concentration or final ETC theorem
  work here.  The next leaf should instantiate `commit`, `hmeas_wrong`, and
  `hprob_wrong` from the concrete argmax oracle/infinitePi probability route.

`ETC-WRONG-COMMIT-INFINITEPI-LINTEGRAL-REGRET-ASSEMBLY` is compiled locally:

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (badGapBound : Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`, consuming
  `BanditRLProof.Algorithms.ETCExpectedRegretAssembly`,
  `BanditRLProof.Algorithms.ETCBoundedRewardInfinitePiSource`, and
  `BanditRLProof.Algorithms.ETCEmpiricalMeanMeasurability`.
- Intended proof route: define the commit selector as the finite argmax oracle
  applied to `ETC.empMeanAtExploration spec baseCommitArm omega`; prove
  wrong-event measurability from the coordinate empirical-mean measurability
  wrapper; obtain the concrete wrong-commit probability bound from the
  compiled infinitePi bounded-reward theorem; feed both facts into the
  abstract lower-integral assembly.
- Regularity contracts: probability coordinate laws, fixed `spec`, `model`,
  `baseCommitArm`, suffix length `r`, explicit `badGapBound`, positive
  exploration count, non-best gap upper bound, action-matched coordinate a.s.
  bounds, and coordinate mean identities over the exploration horizon.
- Retrieval evidence: local declarations are
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`,
  `ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob`,
  `ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean`,
  `ETC.measurable_empMeanAtExploration_coordinates`, and
  `ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean`.
- Status: project-local compiled concrete argmax/infinitePi
  `ENNReal.ofReal` lower-integral regret assembly.
- Failure policy: this is still not Bochner/Rat-valued expected regret.  It is
  fixed-product and fixed-exploration-source only, with no adaptive filtration,
  conditional expectation route, random environment kernel, final ETC theorem,
  or theorem-card promotion beyond the compiled statement.

`ETC-WRONG-COMMIT-INFINITEPI-SUMGAP-LINTEGRAL-REGRET-ASSEMBLY` is compiled
locally:

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) *
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`, consuming
  the concrete argmax/infinitePi lower-integral theorem and
  `Mathlib.Algebra.Order.BigOperators.Group.Finset`.
- Intended proof route: instantiate the previous concrete theorem with
  `badGapBound := (Finset.univ : Finset (Fin K)).sum (fun a => model.gap a)`.
  Discharge the non-best gap upper-bound contract using
  `Finset.single_le_sum`, `Finset.mem_univ`, and
  `FiniteBanditModel.gap_nonneg`.
- Regularity contracts: same coordinate laws, fixed `spec`, `model`,
  `baseCommitArm`, suffix `r`, interval functions, positive exploration
  count, coordinate bounds, and coordinate mean identities as the concrete
  infinitePi theorem.  There is no explicit `badGapBound` parameter.
- Retrieval evidence: local declarations are
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean`,
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`,
  `FiniteBanditModel.gap_nonneg`, and Mathlib `Finset.single_le_sum`.
- Status: project-local compiled conservative sum-gap suffix adapter.
- Failure policy: this deliberately trades sharpness for a simpler contract.
  It does not optimize constants, introduce Bochner expectation, or make the
  theorem adaptive.

`ETC-WRONG-COMMIT-INFINITEPI-MAXGAP-LINTEGRAL-REGRET-ASSEMBLY` is compiled
locally:

```lean
theorem ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * model.maxGap : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi)))
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`, consuming
  the concrete argmax/infinitePi lower-integral theorem and
  `FiniteBanditModel.gap_le_maxGap`.
- Intended proof route: instantiate the concrete theorem with
  `badGapBound := model.maxGap`; discharge the non-best gap upper-bound
  contract with `FiniteBanditModel.gap_le_maxGap`.
- Regularity contracts: same coordinate laws, fixed `spec`, `model`,
  `baseCommitArm`, suffix `r`, interval functions, positive exploration count,
  coordinate bounds, and coordinate mean identities as the concrete infinitePi
  theorem.  There is no explicit `badGapBound` parameter.
- Retrieval evidence: local declarations are
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean`,
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean`,
  and `FiniteBanditModel.gap_le_maxGap`.
- Status: project-local compiled sharper max-gap suffix adapter.
- Failure policy: this improves the suffix constant but remains an
  `ENNReal.ofReal` lower-integral surrogate.  It does not introduce Bochner
  expectation, adaptive filtration, conditional expectation, or a final ETC
  theorem.

`ETC-FIXED-PRODUCT-MAXGAP-LINTEGRAL-REGRET-WRAPPER` is compiled locally:

```lean
noncomputable def ETC.fixedProductArgmaxCommit
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (omega : RewardTrace Rat) : Fin K

noncomputable def ETC.fixedProductArgmaxAction
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (omega : RewardTrace Rat) : ActionTrace (Fin K)

noncomputable def ETC.fixedProductMaxGapLintegralRegretBound
    {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real) : ENNReal

theorem ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductMaxGapLintegralRegretBound spec model baseCommitArm r lo hi
```

- Local APIs/imports:
  `BanditRLProof.Algorithms.ETCInfinitePiExpectedRegretAssembly`,
  `ETC.fixedProductArgmaxCommit`, `ETC.fixedProductArgmaxAction`,
  `ETC.fixedProductMaxGapLintegralRegretBound`, and the compiled max-gap
  infinitePi lower-integral theorem.
- Intended proof route: define the selected commit arm and induced action trace
  as naming wrappers around `ETC.argmaxCommitOracle`, `ETC.empMeanAtExploration`,
  and `ETC.actionWithCommit`; define the RHS max-gap budget; then prove the
  theorem by unfolding these names and reusing
  `ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean`.
- Regularity contracts: same product-coordinate law, fixed `spec`, `model`,
  `baseCommitArm`, suffix `r`, interval functions, positive exploration count,
  coordinate bounds, and coordinate mean identities as the max-gap infinitePi
  theorem.  It introduces no new probabilistic assumptions.
- Retrieval evidence: local declarations are
  `ETC.fixedProductArgmaxCommit`, `ETC.fixedProductArgmaxAction`,
  `ETC.fixedProductMaxGapLintegralRegretBound`, and
  `ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean`.
- Status: project-local compiled fixed product-coordinate wrapper.
- Failure policy: this is polish over the fixed product-coordinate
  `ENNReal.ofReal` route.  Do not treat it as Bochner/Rat-valued expected regret,
  adaptive ETC, filtration, or conditional concentration.

Current boundary after this leaf:

- The next step is a deliberately small derivation of conditional witness
  fields from a concrete reward law before adaptive ETC theorem work.  The
  fixed-commit shifted-history `StronglyAdapted` field is now compiled; full
  policy predictability remains a separate stronger leaf if the route leaves
  the compiled discrete canary.

`FTRL-ONE-STEP` is compiled locally:

```lean
noncomputable def FTRL.linearLoss
    {Action : Type u}
    (arms : Finset Action) (p loss : Action -> Real) : Real

def FTRL.finiteSimplex
    {Action : Type u}
    (arms : Finset Action) (p : Action -> Real) : Prop

noncomputable def FTRL.regularizedObjective
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p : Action -> Real) : Real

def FTRL.IsRegularizedMinimizer
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p : Action -> Real) : Prop

theorem FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer feasible arms eta
      regularizer loss p)
    (hq : feasible q) :
    FTRL.linearLoss arms p loss - FTRL.linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta

theorem FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms) arms eta
      regularizer loss p)
    (hq : FTRL.finiteSimplex arms q) :
    FTRL.linearLoss arms p loss - FTRL.linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta
```

- Local APIs/imports: `BanditRLProof.FTRLOneStep`,
  `Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
  `Mathlib.Data.Real.Basic`, `Mathlib.Tactic.Linarith`, and
  `Mathlib.Tactic.Ring`.
- Intended proof route: define finite-action linear loss, a finite-simplex
  predicate, and the objective `eta * linearLoss + regularizer`; consume an
  explicit feasible-set minimizer certificate; rearrange the objective
  inequality with ordered-field algebra and divide by positive `eta`.
- Regularity contracts: explicit finite action set, Real loss vector,
  arbitrary Real-valued regularizer, feasible predicate or finite simplex,
  comparator feasibility, an explicit minimizer certificate, and `0 < eta`.
- Retrieval evidence: local declarations are `FTRL.linearLoss`,
  `FTRL.finiteSimplex`, `FTRL.regularizedObjective`,
  `FTRL.IsRegularizedMinimizer`,
  `FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer`, and
  `FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer`.
- Status: project-local compiled deterministic FTRL one-step wrapper.
- Failure policy: this does not prove convexity, existence or construction of
  a minimizer, Tsallis regularizer facts, stability/penalty decomposition,
  OMD equivalence, learning-rate optimization, or regret.

Current boundary after this leaf:

- The next FTRL/Tsallis step should either instantiate a concrete
  regularizer-side algebra leaf or prove a small simplex/weight API.  Do not
  jump directly to Tsallis-INF or EXP3 regret.

`TSALLIS-REGULARIZER` is compiled locally:

```lean
noncomputable def Tsallis.powerSum
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real

noncomputable def Tsallis.entropy
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real

noncomputable def Tsallis.negEntropyRegularizer
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real) : Real

theorem Tsallis.one_sub_exponent_ne_zero
    {alpha : Real} (halpha : alpha ≠ 1) :
    1 - alpha ≠ 0

theorem Tsallis.powerSum_nonneg_of_finiteSimplex
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) :
    0 <= Tsallis.powerSum arms alpha p

theorem Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex
    {Action : Type u}
    (arms : Finset Action) (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) (halpha : alpha ≠ 1) :
    0 <= Tsallis.powerSum arms alpha p ∧
      1 - alpha ≠ 0 ∧
      Tsallis.negEntropyRegularizer arms alpha p =
        - ((Tsallis.powerSum arms alpha p - 1) / (1 - alpha))
```

- Local APIs/imports: `BanditRLProof.TsallisRegularizer`,
  `BanditRLProof.FTRLOneStep`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`,
  and `Mathlib.Tactic.Linarith`.
- Intended proof route: define the finite power sum with `Real.rpow`, define
  Tsallis entropy and its negative-entropy regularizer, discharge the
  denominator from `alpha ≠ 1`, and prove nonnegative power sum from
  `FTRL.finiteSimplex` plus `Real.rpow_nonneg`.
- Regularity contracts: explicit finite action set, Real exponent `alpha`,
  finite-simplex probability vector, and `alpha ≠ 1`.  The probability
  nonnegativity is consumed only on arms in the finite set.
- Retrieval evidence: local declarations are `Tsallis.powerSum`,
  `Tsallis.entropy`, `Tsallis.negEntropyRegularizer`,
  `Tsallis.one_sub_exponent_ne_zero`,
  `Tsallis.powerSum_nonneg_of_finiteSimplex`, and
  `Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex`.
- Status: project-local compiled finite-simplex Tsallis regularizer
  well-definedness wrapper.
- Failure policy: this does not prove convexity, differentiability or
  subgradient facts, rpow stability/penalty, self-bounding, learning-rate
  optimization, FTRL minimizer existence, or Tsallis-INF regret.

Current boundary after this leaf:

- The next Tsallis/FTRL step should be a small rpow algebra, convexity, or
  stability/penalty leaf that consumes this regularizer surface.  Do not jump
  directly to a full Tsallis-INF theorem.

`EXP3-POTENTIAL` is compiled locally:

```lean
noncomputable def Exp3Potential.potential
    {Action : Type u} (arms : Finset Action) (w : Action -> Real) : Real

noncomputable def Exp3Potential.updatedWeight
    {Action : Type u}
    (eta : Real) (w loss : Action -> Real) (a : Action) : Real

noncomputable def Exp3Potential.updatedPotential
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) : Real

theorem Exp3Potential.updatedPotential_eq_sum
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) :
    Exp3Potential.updatedPotential arms eta w loss =
      arms.sum (fun a => w a * Real.exp (-eta * loss a))

theorem Exp3Potential.updatedPotential_nonneg_of_nonneg
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real)
    (hw : forall a, a ∈ arms -> 0 <= w a) :
    0 <= Exp3Potential.updatedPotential arms eta w loss

theorem Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) :
    Exp3Potential.updatedPotential arms eta w loss -
        Exp3Potential.potential arms w =
      arms.sum (fun a => w a * (Real.exp (-eta * loss a) - 1))

theorem Exp3Potential.potentialProcess_telescope_sum_range
    {Action : Type u}
    (arms : Finset Action) (w : Nat -> Action -> Real) (T : Nat) :
    (Finset.range T).sum
        (fun t => Exp3Potential.potentialProcess arms w (t + 1) -
          Exp3Potential.potentialProcess arms w t) =
      Exp3Potential.potentialProcess arms w T -
        Exp3Potential.potentialProcess arms w 0
```

- Local APIs/imports: `BanditRLProof.Exp3Potential`,
  `Mathlib.Analysis.SpecialFunctions.Exp`, `Mathlib.Finset.sum`, and
  `Mathlib.Tactic.Ring`.
- Intended proof route: define the finite potential as a `Finset.sum`, define
  the multiplicative exponential update, prove nonnegativity with
  `Real.exp_pos`, prove the one-step increment by `Finset.sum_sub_distrib`,
  and prove the finite-horizon telescope by induction over `Finset.range`.
- Regularity contracts: finite action set as an explicit `Finset Action`,
  Real weights/losses, and pointwise nonnegative current weights on the arms
  for nonnegative updated potential.  The exact algebra itself does not need a
  positive learning rate; future log/regret leaves may add that assumption.
- Retrieval evidence: local declarations are
  `Exp3Potential.potential`, `Exp3Potential.updatedWeight`,
  `Exp3Potential.updatedPotential`,
  `Exp3Potential.updatedPotential_eq_sum`,
  `Exp3Potential.updatedWeight_nonneg_of_nonneg`,
  `Exp3Potential.updatedPotential_nonneg_of_nonneg`,
  `Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one`,
  `Exp3Potential.sum_range_forward_difference`,
  `Exp3Potential.potentialProcess`, and
  `Exp3Potential.potentialProcess_telescope_sum_range`.
- Status: project-local compiled deterministic EXP3 potential wrapper.
- Failure policy: do not treat this as an importance-weighted estimator,
  EXP/log inequality import, learning-rate optimization, FTRL/OMD theorem, or
  EXP3 regret proof.  Those remain separate leaves.

Current boundary after this leaf:

- The next EXP3/adversarial step should be either an importance-weighted
  estimator API or a small exp/log inequality import wrapper.  Do not jump
  directly to EXP3 regret.

`ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND` is compiled locally:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) (commitArm : Fin K) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

- Local APIs/imports: `BanditRLProof.RegretCountBounds` and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Intended proof route: instantiate
  `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` with
  `action := ETC.actionWithCommit spec commitArm`, horizon
  `spec.explorationPulls * K`, and uniform count bound
  `B := spec.explorationPulls`; discharge the count bound with
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.
- Regularity contracts: only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, and `commitArm : Fin K`; no post-horizon
  behavior, empirical means, commit argmax, probability, concentration, or
  final theorem facts.
- Retrieval evidence: compiled `REGRET-UNIFORM-NAT-COUNT-BOUND` and compiled
  fixed-commit ETC exploration-horizon count.
- Status: project-local compiled ETC deterministic regret scaffold.
- Failure policy: do not prove post-exploration corollaries, empirical commit
  correctness, or probability facts in the same batch.

## Required Closeout

Before handing work back:

```bash
python3 tools/bandit.py check
python3 tools/bandit.py list-lean-decls QUERY --statement
python3 tools/bandit.py unfinished
```

Do not mark a leaf `compiled-local` until the Lean gate has actually passed.
