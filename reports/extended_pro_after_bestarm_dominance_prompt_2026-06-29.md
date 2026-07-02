# Extended Pro Review Prompt: After Best-Arm Dominance Leaf

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Current new batch:

- Added `BanditRLProof/FiniteBanditModelInvariants.lean`.
- New compiled theorem:

```lean
theorem FiniteBanditModel.mean_le_bestArm_mean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm
```

- Local proof route: a private fold invariant over `List.finRange K` for the
  local `FiniteBanditModel.bestArm` selector.
- Imports: `Mathlib.Algebra.Order.Field.Rat`, `Mathlib.Data.Fintype.Basic`,
  and `BanditRLProof.Core`.
- Added root import, a `Tests/Basic.lean` smoke example, a local leaf card
  `LOCAL-LEAF-FINITE-BANDIT-MODEL-INVARIANTS`, and leaf id
  `FINITE-BANDIT-BESTARM-DOMINATES`.
- Updated README, completion gap audit, project overview, collaborator guide,
  theory tree, Mathlib foundation leaf map, and refreshed retrieval indexes.
- `python3 tools/bandit.py check` passes:
  - `lake build`
  - `lake build Tests`
  - placeholder scan
- Local declaration scan is now 111 declarations.

Important boundary:

- This only proves best-arm dominance.
- It does not yet prove `FiniteBanditModel.gap_nonneg`.
- It does not claim Rat-valued expectation, Bochner expectation, filtration,
  concentration, UCB/ETC regret, Thompson sampling, EXP3, Tsallis-INF, OFUL, or
  RL/MDP final theorem work.

Proposed next leaf:

```lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a
```

Expected route:

1. unfold `gap`;
2. use `FiniteBanditModel.mean_le_bestArm_mean model a`;
3. discharge `0 <= model.bestMean - model.mean a` with ordered-ring/linear
   arithmetic over `Rat`, likely via `sub_nonneg.mpr`.

Questions:

1. Is `FiniteBanditModel.gap_nonneg` the right next single leaf?
2. Is the statement above the exact Lean-facing statement you recommend?
3. Should the theorem live in `BanditRLProof.FiniteBanditModelInvariants`, or
   should it remain near `LeafLemmas`/`Core`?
4. Are there any hidden regularity contracts or import risks?
5. After `gap_nonneg`, should the next step be an automatic adapter removing
   the explicit gap-nonnegativity hypothesis from the existing lower-integral
   pseudo-regret bound, or should we pause again before touching expectation
   statements?
