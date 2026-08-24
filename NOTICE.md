# Notice

This repository contains original ABRL harness code, the BanditRLlib Lean
library, and its literate website. It studies and attributes upstream systems
and proof libraries, but the repository does not vendor LML, LeanMarathon, ARIS, ABEIS, or
lean-stat-learning-theory source code.

## Referenced Projects

- Auto-Lean-in-Sleep: Block Encoding for Quantum Computing (ABEIS),
  https://github.com/DakeBU/Quantum-Computing-Block-Encoding, MIT License.
- Auto-claude-code-research-in-sleep (ARIS),
  https://github.com/wanshuiyin/Auto-claude-code-research-in-sleep, MIT License.
- Learning Beyond Gradients,
  https://github.com/Trinkle23897/learning-beyond-gradients.
- EoH, https://github.com/FeiLiu36/EoH, MIT License.
- LeanMachineLearning/LML,
  https://github.com/LeanMachineLearning/LML, Apache-2.0 License.
- LeanMarathon, https://github.com/YuanheZ/LeanMarathon.
- lean-stat-learning-theory,
  https://github.com/YuanheZ/lean-stat-learning-theory.
- Mathlib, https://github.com/leanprover-community/mathlib4.
- Lean-Ridgelet by Sho Sonoda,
  https://github.com/shosonoda/lean-ridgelet, Apache-2.0 License.  ABRL's
  literate formalization website is conceptually inspired by Lean-Ridgelet's
  Blueprint organization and implementation map.  No Lean-Ridgelet source,
  template, stylesheet, or configuration file is copied into this repository,
  and this reference does not imply participation, endorsement, or maintenance
  by Sho Sonoda.
- StatsMLlib by the Lean Models, Decisions, and Statistics community,
  https://github.com/Lean-MoDS/StatsMLlib, Apache-2.0 License, with its public
  site at https://statsmllib.github.io/.  ABRL's learning/browsing/contribution
  organization is conceptually inspired by StatsMLlib's book map, selected
  theorem presentation, and visible contribution path.  No StatsMLlib source,
  template, stylesheet, prose, or configuration file is copied, and this
  reference does not imply participation, endorsement, review, or maintenance
  by StatsMLlib, Lean-MoDS, its organizers, or its contributors.
- Auto-Sampling-Theory-In-Sleep / Samplinglib,
  https://github.com/DakeBU/Auto-Sampling-Theory-In-Sleep, with its public
  Underlying Lean Graph at
  https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/lean-foundations.html,
  SampleWiki at
  https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki.html,
  and Sampling Frontier at
  https://dakebu.github.io/Auto-Sampling-Theory-In-Sleep/example-cases/samplewiki/frontier.html.
  BanditRLlib's progressive Lean Graph and setting-to-case-to-frontier
  organization are conceptually informed by those public pages. The audited
  default branch did not expose a license file on 2026-08-22, so BanditRLlib
  treats them as design inspiration only and independently implements its
  model, theorem data, generated HTML, CSS, JavaScript, filtering, status
  semantics, and accessibility behavior. No Samplinglib source, graph or
  theorem data, template, stylesheet, or prose is copied, and no shared
  verification status, endorsement, review, or maintenance is implied.
- Bubeck and Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic
  Multi-armed Bandit Problems, https://arxiv.org/abs/1204.5721.
- Lattimore and Szepesvári, Bandit Algorithms,
  https://tor-lattimore.com/downloads/book/book.pdf.
- Slivkins, Introduction to Multi-Armed Bandits,
  https://arxiv.org/abs/1904.07272.
- Auer, Cesa-Bianchi, and Fischer, Finite-time Analysis of the Multiarmed
  Bandit Problem, https://doi.org/10.1023/A:1013689704352.
- Auer, Cesa-Bianchi, Freund, and Schapire, The Nonstochastic Multiarmed
  Bandit Problem, https://doi.org/10.1137/S0097539701398375.
- Zimmert and Seldin, Tsallis-INF,
  https://arxiv.org/abs/1807.07623.
- Masoudian and Seldin, improved Tsallis-INF analysis,
  https://arxiv.org/abs/2103.12487.
- Kato and Ito, LC-Tsallis-INF,
  https://arxiv.org/abs/2403.03219.
- Tsuchiya and Ito, adaptive learning rate FTRL for best-of-both-worlds,
  https://arxiv.org/abs/2405.20028.
- Garivier and Cappé, KL-UCB, https://arxiv.org/abs/1102.2490.
- Agrawal and Goyal, Thompson sampling analysis,
  https://arxiv.org/abs/1111.1797.
- Abbasi-Yadkori, Pál, and Szepesvári, self-normalized least-squares
  processes for bandits, https://arxiv.org/abs/1102.2670.
- Li, Chu, Langford, and Schapire, contextual-bandit news recommendation,
  https://doi.org/10.1145/1772690.1772758.
- Azar, Osband, and Munos, minimax regret for reinforcement learning,
  https://arxiv.org/abs/1703.05449.
- Badanidiyuru, Kleinberg, and Slivkins, Bandits with Knapsacks,
  https://arxiv.org/abs/1305.2545.
- Sui, Zoghi, Hofmann, and Yue, Advancements in Dueling Bandits,
  https://doi.org/10.24963/ijcai.2018/776.
- Khezeli and Bitar, Safe Linear Stochastic Bandits,
  https://doi.org/10.1609/aaai.v34i06.6581.
- Tossou and Dimitrakakis, differentially private multi-armed bandits,
  https://doi.org/10.1609/aaai.v30i1.10212.
- Joseph, Kearns, Morgenstern, Neel, and Roth, meritocratic fairness for
  contextual bandits, https://doi.org/10.1145/3278721.3278764.
- Shi and Shen, Federated Multi-Armed Bandits,
  https://doi.org/10.1609/aaai.v35i11.17156.
- Federated Neural Bandits, https://arxiv.org/abs/2205.14309.

When ABRL later imports, ports, or vendors any external source file, the
corresponding license and source-level notice must be updated before merging
that change.
