# Extended Pro Prompt: Baseline Review And PULLCOUNT-FINSET Direction

You are reviewing the current progress of ABRL, a Lean 4 repository for
bandit/RL proof engineering.

Current gate:

```bash
python3 tools/bandit.py check
```

passes with:

```text
lake build
lake build Tests
check passed
```

Recently compiled local leaves:

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

theorem sumRewards_eq_list_range_filter_foldl
    (hzero : forall x : Reward, x + 0 = x) :
    sumRewards action reward a t =
      ((List.range t).filter (fun s : Nat => decide (action s = a))).foldl
        (fun acc s => acc + reward s)
        0

theorem pseudoRegret_eq_list_range_foldl
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (List.range t).foldl
        (fun acc s => acc + model.gap (action s))
        0

theorem ETC.exploreArm_add_K (spec : ETC.Spec K) (t : Nat) :
    ETC.exploreArm spec (t + K) = ETC.exploreArm spec t
```

The next target set from the project owner is:

1. Mathlib-backed `Finset.range` wrappers:
   - `PULLCOUNT-FINSET`
   - `SUMREWARDS-FINSET`
   - `PSEUDOREGRET-FINSET`
2. probability / measure / filtration / conditional expectation layer;
3. sub-Gaussian, Hoeffding, martingale tail inequalities;
4. complete UCB, ETC, Thompson sampling, EXP3, Tsallis-INF, OFUL, RL/MDP theorems.

Please review:

1. Is the current deterministic baseline a reasonable completed batch before
   adding Mathlib?
2. Should the next immediate leaf be `PULLCOUNT-FINSET`, or should another
   small local consumer leaf happen first?
3. If `PULLCOUNT-FINSET` is next, give the exact Lean-facing statement, minimal
   imports, and proof route for Lean 4.29.1.
4. Can the proof route reuse `pullCount_eq_list_filter_length`, or should it
   prove directly by `Finset.range_succ`?
5. What failure policy should be used if Mathlib import setup is too large?
6. After `PULLCOUNT-FINSET`, what is the next batch size before asking you
   again?

Keep the answer focused on execution order and exact next Lean leaf design.
