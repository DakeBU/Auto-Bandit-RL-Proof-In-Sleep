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

## Literate Formalization Website

The organization of ABRL's Blueprint-style literate formalization website is
inspired by [Sho Sonoda's Lean-Ridgelet
project](https://github.com/shosonoda/lean-ridgelet) and its
[Blueprint website](https://shosonoda.github.io/lean-ridgelet/), especially
the idea of an implementation map that connects informal mathematics to Lean
declarations.  Lean-Ridgelet is distributed under the Apache License 2.0.

ABRL uses an independently implemented static generator and original content.
It does not copy Lean-Ridgelet source, templates, stylesheets, or
configuration.  Sho Sonoda has not been represented as an ABRL contributor,
maintainer, or endorser.

The community-facing sidebar, Book Map, contributor page, installation page,
and visible contribution route are also inspired by
[StatsMLlib](https://statsmllib.github.io/) and its
[public repository](https://github.com/Lean-MoDS/StatsMLlib), distributed under
Apache License 2.0. BanditRLlib independently implements its generator,
templates, styles, prose, JavaScript, diagrams, schema, and governance; no
StatsMLlib source file is copied. This attribution does not imply participation,
endorsement, review, or maintenance by StatsMLlib, Lean-MoDS, or their
contributors.

BanditRLlib's progressive graph explorer is also informed by Samplinglib's
public [Underlying Lean Graph of
Libraries](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html)
in [Auto-Sampling-Theory-In-Sleep](https://github.com/DakeBU/Auto-Sampling-Theory-In-Sleep).
BanditRLwiki's assumption-setting, theorem-case, and frontier organization is
also informed by the public
[SampleWiki](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki.html)
and [Sampling Frontier](https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki/frontier.html).
The audited Samplinglib default branch did not expose a repository license file
on 2026-08-22. BanditRLlib therefore treats these pages as design inspiration
only and independently implements the graph model, theorem data, generated
HTML, CSS, JavaScript, progressive branch limits, filters, status semantics,
and accessibility behavior. No Samplinglib source file, graph or theorem data,
template, stylesheet, or prose is copied. This reference does not imply shared
verification status, shared maintainers, endorsement, review, or
responsibility for BanditRLlib.

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

## Bandit Paper Card References

- [Auer, Cesa-Bianchi, and Fischer, Finite-time Analysis of the Multiarmed
  Bandit Problem](https://doi.org/10.1023/A:1013689704352).
- [Auer, Cesa-Bianchi, Freund, and Schapire, The Nonstochastic Multiarmed
  Bandit Problem](https://doi.org/10.1137/S0097539701398375).
- [Zimmert and Seldin, Tsallis-INF](https://arxiv.org/abs/1807.07623).
- [Masoudian and Seldin, Improved Analysis of the Tsallis-INF
  Algorithm](https://arxiv.org/abs/2103.12487).
- [Kato and Ito, LC-Tsallis-INF](https://arxiv.org/abs/2403.03219).
- [Tsuchiya and Ito, adaptive learning rate FTRL for
  best-of-both-worlds](https://arxiv.org/abs/2405.20028).
- [Garivier and Cappé, The KL-UCB Algorithm for Bounded Stochastic Bandits and
  Beyond](https://arxiv.org/abs/1102.2490).
- [Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit
  Problem](https://arxiv.org/abs/1111.1797).
- [Abbasi-Yadkori, Pál, and Szepesvári, Online Least Squares Estimation with
  Self-Normalized Processes](https://arxiv.org/abs/1102.2670).
- [Li, Chu, Langford, and Schapire, A Contextual-Bandit Approach to
  Personalized News Article Recommendation](https://doi.org/10.1145/1772690.1772758).
- [Azar, Osband, and Munos, Minimax Regret Bounds for Reinforcement
  Learning](https://arxiv.org/abs/1703.05449).
- [Badanidiyuru, Kleinberg, and Slivkins, Bandits with
  Knapsacks](https://arxiv.org/abs/1305.2545).
- [Sui, Zoghi, Hofmann, and Yue, Advancements in Dueling
  Bandits](https://doi.org/10.24963/ijcai.2018/776).
- [Khezeli and Bitar, Safe Linear Stochastic
  Bandits](https://doi.org/10.1609/aaai.v34i06.6581).
- [Tossou and Dimitrakakis, Algorithms for Differentially Private
  Multi-Armed Bandits](https://doi.org/10.1609/aaai.v30i1.10212).
- [Joseph, Kearns, Morgenstern, Neel, and Roth, Meritocratic Fairness for
  Infinite and Contextual Bandits](https://doi.org/10.1145/3278721.3278764).
- [Shi and Shen, Federated Multi-Armed
  Bandits](https://doi.org/10.1609/aaai.v35i11.17156).
- [Federated Neural Bandits](https://arxiv.org/abs/2205.14309).

## Attribution Boundary

ABRL currently contains original code and theorem-card summaries.  A theorem
card is not copied source code and is not a local proof certificate.  If a
future task imports, ports, or vendors external Lean code, that task must:

1. name the upstream file and declaration;
2. record the license;
3. update `NOTICE.md`;
4. make the local Lean gate pass;
5. update the conversion window and proof-export text.
