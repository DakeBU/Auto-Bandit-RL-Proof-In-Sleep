# Bandit Paper And Survey Cards

ABRL uses paper cards when a scenario needs a sharper source than the broad
textbook spine.  These cards are retrieval routes, not certified local Lean
results.  A card becomes certified only after the required declarations compile
inside this repository.

Refresh/search the compact index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-papers
python3 tools/bandit.py search-memory KL-UCB
python3 tools/bandit.py search-memory federated
```

## Classical Algorithm Cards

| Card | Source | Scenarios | First Lean leaf families |
| --- | --- | --- | --- |
| `PPR-AUER-CBF-2002-UCB1` | [Auer, Cesa-Bianchi, and Fischer, 2002](https://doi.org/10.1023/A:1013689704352) | finite stochastic | pull-count threshold, good-event split, tail summability |
| `PPR-AUER-CFS-2002-EXP3` | [Auer, Cesa-Bianchi, Freund, and Schapire, 2002](https://doi.org/10.1137/S0097539701398375) | adversarial finite | importance-weighted loss, exponential potential, learning-rate optimization |
| `PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF` | [Zimmert and Seldin, 2018](https://arxiv.org/abs/1807.07623) | best-of-both-worlds, stochastic/adversarial | Tsallis regularizer, FTRL optimality, self-bounding regret |
| `PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF` | [Masoudian and Seldin, 2021](https://arxiv.org/abs/2103.12487) | constrained adversarial, corrupted stochastic | stability/penalty split, gap-dependent conversion, power-weight algebra |
| `PPR-KATO-ITO-2024-LC-TSALLIS-INF` | [Kato and Ito, 2024](https://arxiv.org/abs/2403.03219) | linear contextual best-of-both-worlds | linear loss estimates, Tsallis regularization, contextual confidence bridge |
| `PPR-KUROKI-RUMI-TSUCHIYA-VITALE-CESABIANCHI-2023-BOBW-LCB` | [Kuroki, Rumi, Tsuchiya, Vitale, and Cesa-Bianchi, 2023](https://arxiv.org/abs/2312.15433) | linear contextual best-of-both-worlds | context distribution contract, linear loss estimator, FTRL stability |
| `PPR-ADAPTIVE-LR-FTRL-2024` | [Tsuchiya and Ito, 2024](https://arxiv.org/abs/2405.20028) | adaptive FTRL, best-of-both-worlds | adaptive learning rate, stability/penalty split, self-bounding conversion |
| `PPR-GARIVIER-CAPPE-2011-KLUCB` | [Garivier and Cappé, 2011](https://arxiv.org/abs/1102.2490) | finite stochastic | Bernoulli KL, confidence inversion, bounded reward event |
| `PPR-AGRAWAL-GOYAL-2011-TS` | [Agrawal and Goyal, 2011](https://arxiv.org/abs/1111.1797) | stochastic, Bayesian posterior | posterior action identity, probability matching, Bayesian regret |
| `PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED` | [Abbasi-Yadkori, Pál, and Szepesvári, 2011](https://arxiv.org/abs/1102.2670) | linear/GLM | Gram matrix monotonicity, self-normalized martingale, elliptical potential |
| `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB` | [Li, Chu, Langford, and Schapire, 2010](https://doi.org/10.1145/1772690.1772758) | contextual, linear, recommender | context-history interface, feature-vector reward, argmax policy |
| `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` | [Azar, Osband, and Munos, 2017](https://arxiv.org/abs/1703.05449) | finite-horizon RL/MDP | finite kernels, Bellman recursion, episode regret telescope |
| `PPR-GERCHINOVITZ-LATTIMORE-2016-REFINED-LOWER-BOUNDS` | [Gerchinovitz and Lattimore, NeurIPS 2016](https://proceedings.neurips.cc/paper/2016/hash/2f37d10131f2a483a8dd005b3d14b0d9-Abstract.html) | adversarial finite, high-probability lower bounds | clipped-normal hard reward matrix, same-policy history information, clipping concentration, deterministic-witness extraction |

## Frontier Scenario Cards

| Card | Source | Scenarios | First Lean leaf families |
| --- | --- | --- | --- |
| `PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK` | [Badanidiyuru, Kleinberg, and Slivkins, 2013](https://arxiv.org/abs/1305.2545) | resource-constrained, knapsack | resource traces, budget stopping time, primal-dual comparison |
| `PPR-IJCAI-2018-DUELING-SURVEY` | [Sui, Zoghi, Hofmann, and Yue, 2018](https://doi.org/10.24963/ijcai.2018/776) | dueling/preference | pairwise preference matrix, winner notions, comparison regret |
| `PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC` | [Khezeli and Bitar, 2020](https://doi.org/10.1609/aaai.v34i06.6581) | safe/constrained | baseline feasibility, safe-set monotonicity, constraint regret |
| `PPR-AAAI-2016-DP-MAB` | [Tossou and Dimitrakakis, 2016](https://doi.org/10.1609/aaai.v30i1.10212) | private bandits | privacy noise, composition, private confidence radius |
| `PPR-FAT-2018-MERITOCRATIC-FAIRNESS` | [Joseph, Kearns, Morgenstern, Neel, and Roth, 2018](https://doi.org/10.1145/3278721.3278764) | fair/contextual | fairness invariant, dominance relation, policy constraint |
| `PPR-AAAI-2021-FEDERATED-MAB` | [Shi and Shen, 2021](https://doi.org/10.1609/aaai.v35i11.17156) | federated/distributed | client-indexed traces, aggregation invariant, communication count |
| `PPR-FEDERATED-NEURAL-BANDITS-2022` | [Federated Neural Bandits, 2022](https://arxiv.org/abs/2205.14309) | federated, neural/recommender | client embedding contract, nonlinear confidence surrogate, federated update trace |
| `PPR-EMNLP-2024-LLM-PRIOR-BANDITS` | [Jump Starting Bandits with LLM-Generated Prior Knowledge, 2024](https://arxiv.org/abs/2406.19317) | LLM priors, contextual | prior-quality contract, logged-data positivity, warm-start comparison |
| `PPR-BOUNEFFOUF-FERAUD-2025-MAB-LLM` | [Bouneffouf and Feraud, 2025](https://arxiv.org/abs/2505.13355) | LLM/recommender/model-selection bandits | model-selection action space, prompt-policy context contract, feedback bridge |

## Source-Locked External Theory-Audit Cards

These cards are immutable source evidence after publication, not local proof
certificates.  The delayed lock and its initial feasibility slice were first
published together; the succinct and stochastic-gradient-bandit locks preceded
their case-specific Lean slices.  Selection, source hashes, timing, and
exclusion rules are recorded in
[`prospective-audit-2025-freeze.json`](prospective-audit-2025-freeze.json).

| Card | Source | Audit role | First exact leaves |
| --- | --- | --- | --- |
| `PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW` | [Schlisselberg, Lancewicki, Auer, and Mansour, NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/02f0ac0a323dc17d964d4bbf8a62e01b-Abstract-Conference.html) | flagship feasibility audit for one delayed SAPO algorithm across stochastic and adversarial losses | feedback-availability partition, outstanding-count surface, source-shaped elimination good-event projection, Corollary-D.8 union assembly, optimal-arm-survival core, D.10/D.12 width-direction diagnostic, processed-prefix and trace-summary factor-20 route, ordered no-switch transition and temporal trace, nonnegative-domain D.11 core, Algorithm-5 line-10 eliminated-arm initializer, causal one-round action law, same-algorithm multi-regime contract |
| `PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS` | [Zeng and Honorio, NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/26407588dfb08e48c459c074ab6adb7d-Abstract-Conference.html) | partial source audit aligned with the compiled Part IV information layer; terminal source contract blocked | 54 named declarations compile the atom/support contract, source-shaped `Q`/`R`, Definitions 3.1--3.3, Lemmas 3.1--3.4 through a finite-Bessel route, and a global-`R` boundedness diagnostic. The audit found that real-valued global `R` is not sound for an unbounded non-spanning system and that the printed Theorem 3.8 omits horizon conditions used by its proof; the original Lemmas 3.5--3.6 and Theorem 3.8 therefore remain source-contract blocked rather than being silently repaired. |
| `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB` | [Baudry et al., NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/a4e683f0ce6b91e7fbdae9d32642d88f-Abstract-Conference.html) | partial paper audit with one exact compiled external endpoint and bounded follow-on infrastructure | The counted ledger retains 352 audit-slice declarations through the eight-declaration selected-reward aggregation/readout layer. A separate ten-declaration native-law module now defines the native stationary process, proves equality of every inclusive finite visible prefix, and compiles `latentArmStreamVisibleTrajectoryMeasure_eq_native`, which promotes those identities to equality of the complete visible/native probability measures by projective-limit uniqueness. The terminal `twoArmFixedIIDDirac_theoremOne` is the source Theorem 1 for fixed two-arm IID laws, a Dirac environment prior, source `T = tailHorizon + 1`, and the exact constants and assumptions. Theorem 2 nevertheless remains blocked at stopped or pull-ordered selected IID, the stopped-prefix future/no-return law, conditional no-return, the ballot phase, and asymptotic assembly; the separate Appendix-E gate does not prove Theorem 4. Theorems 2--4 and the full paper remain open. |

## Use Rule

Every paper card used in a task must be paired with:

- a scenario card;
- a textbook root when one exists;
- Mathlib retrieval cards for general mathematical leaves;
- local Lean declarations found with `list-lean-decls`, when available;
- a proof-obligation row for each missing leaf.

If a source route stalls, record the mathematical failure signal before
changing the statement or proof strategy.
