# Attribution

This project cites external work by public upstream source link.  Local
checkouts or local paper archives may be used during development, but public
documentation should cite the upstream paper or repository rather than local
filesystem locations.

## Primary Lean Bandit Reference

- [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML),
  Apache-2.0 License.  ABRL uses LML as the primary theorem-card source for
  finite stochastic bandits, regret decompositions, Explore-Then-Commit, UCB,
  Thompson sampling, and Bayesian regret.  Initial ABRL code does not vendor or
  import LML source.

## Automation References

- [Auto-Lean-in-Sleep: Block Encoding for Quantum Computing](https://github.com/DakeBU/Quantum-Computing-Block-Encoding),
  MIT License.  ABRL adapts the first ABEIS harness profile: one
  upper/middle/lower/reviewer hierarchy, conversion windows, proof obligations,
  run decks, and Lean-first acceptance.
- [Auto-claude-code-research-in-sleep](https://github.com/wanshuiyin/Auto-claude-code-research-in-sleep),
  MIT License.  Similar pattern studied for plain-file research workflow,
  local skills, task packets, reviews, and run logs.
- [LeanMarathon](https://github.com/YuanheZ/LeanMarathon).  Similar pattern
  studied for target review, proof-blueprint snapshots, dynamic proof leaves,
  worker/refiner roles, and deterministic gates.

## Lean And Learning-Theory References

- [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory).
  ABRL uses it as a proof-engineering reference for concentration,
  empirical-process, and ML-theory formalization at scale.
- [Mathlib](https://github.com/leanprover-community/mathlib4).  ABRL expects
  future probability, measure-theory, asymptotic, and concentration work to
  connect to Mathlib or to libraries built on Mathlib.

## Attribution Boundary

ABRL currently contains original code and theorem-card summaries.  A theorem
card is not copied source code and is not a local proof certificate.  If a
future task imports, ports, or vendors external Lean code, that task must:

1. name the upstream file and declaration;
2. record the license;
3. update `NOTICE.md`;
4. make the local Lean gate pass;
5. update the conversion window and proof-export text.
