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

## Build Gate

```bash
python3 tools/bandit.py check
```
