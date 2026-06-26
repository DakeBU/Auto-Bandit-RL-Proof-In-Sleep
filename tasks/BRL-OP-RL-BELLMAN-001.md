# Define a finite-horizon RL Bellman and regret interface

Task id: `BRL-OP-RL-BELLMAN-001`
Kind: `openProblemProposal`
Status: `planned`
Harness: `hierarchical`

## Goal

Create a small Lean-facing interface for finite-horizon reinforcement learning:
finite states, finite actions, transition kernel surface, reward model, value
function, Bellman recursion, occupancy, and regret.

## Source

- Literature source: standard finite-horizon MDP/RL notation.
- Local surface: `BanditRLProof/OpenProblems.lean`
- Textbook/source card: `TXT-SLIVKINS-2019-2024`
- Scenario card: `SCN-RL-MDP`
- Mathlib cards: `MLIB-PROBABILITY-KERNEL`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION`

## Lean Target

```lean
-- future module:
-- BanditRLProof/RL/FiniteHorizon.lean
```

## Proof Obligations

- [ ] Decide dependency-light or Mathlib probability layer.
- [ ] Define finite MDP data.
- [ ] Define policy and trajectory surface.
- [ ] Define value and Bellman recursion.
- [ ] Define regret relative to an optimal policy.

## Mathlib-Ready Leaf Contract

Finite-set, kernel, expectation, measurability, and Bellman recursion support
lemmas should be split into leaf-sized statements.  General probability or
dynamic-programming infrastructure should be marked as Mathlib candidates; the
finite-horizon RL interface itself stays project-local until the dependency
layer is selected.

## Build Gate

```bash
python3 tools/bandit.py check
```
