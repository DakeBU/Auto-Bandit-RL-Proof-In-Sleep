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
- [Learning Beyond Gradients](https://github.com/Trinkle23897/learning-beyond-gradients).
  Similar pattern studied for persistent trial memory, layered feedback,
  append-only experiment traces, and iterative system improvement.  ABRL adapts
  this as trial JSONL, summary CSV, failed-route memory, and reviewer-guided
  proof-system maintenance.
- [EoH](https://github.com/FeiLiu36/EoH), MIT License.  Similar pattern
  studied for evolutionary search over structured candidate solutions.  ABRL
  adapts the idea only for future theorem-route and proof-DAG candidate
  populations under a fixed Lean-checkable target.
- [LeanMarathon](https://github.com/YuanheZ/LeanMarathon).  Similar pattern
  studied for target review, proof-blueprint snapshots, dynamic proof leaves,
  worker/refiner roles, and deterministic gates.

ABRL's public diagrams adapt the same broad visual pattern of harness,
dependency, and module-layout graphs while replacing the content with
bandit/RL-specific Mathlib-ready proof leaves and memory contracts.

## Lean And Learning-Theory References

- [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory).
  ABRL uses it as a proof-engineering reference for concentration,
  empirical-process, and ML-theory formalization at scale.
- [Mathlib](https://github.com/leanprover-community/mathlib4).  ABRL expects
  future probability, measure-theory, asymptotic, and concentration work to
  connect to Mathlib or to libraries built on Mathlib.
- [The Mathlib Community](https://mathlib-initiative.org/).  ABRL treats
  general proof-DAG leaf lemmas as future Mathlib contribution candidates
  whenever possible.

## Bandit Textbook And Survey References

- [Bubeck and Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic
  Multi-armed Bandit Problems](https://arxiv.org/abs/1204.5721).  ABRL uses it
  as a classic source card for stochastic/adversarial regret routes and lower
  bound structure.
- [Lattimore and Szepesvári, Bandit Algorithms](https://tor-lattimore.com/downloads/book/book.pdf).
  ABRL uses it as the main textbook spine for finite stochastic, adversarial,
  contextual, linear, lower-bound, and concentration branches.
- [Slivkins, Introduction to Multi-Armed Bandits](https://arxiv.org/abs/1904.07272).
  ABRL uses it as a broad scenario source for IID, Bayesian, contextual,
  Lipschitz, adversarial, knapsack, and agent-oriented bandit routes.

## Attribution Boundary

ABRL currently contains original code and theorem-card summaries.  A theorem
card is not copied source code and is not a local proof certificate.  If a
future task imports, ports, or vendors external Lean code, that task must:

1. name the upstream file and declaration;
2. record the license;
3. update `NOTICE.md`;
4. make the local Lean gate pass;
5. update the conversion window and proof-export text.
