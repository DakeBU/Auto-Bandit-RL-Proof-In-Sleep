# Director

First terminal: Chapter 1 Theorem 1.3, regret at most 4 + 4 log T for the actual past-average predictor, first choice 1/2. Necessary DAG: Lemma 1.2 -> FTL stability decomposition; empirical mean minimization + interval feasibility -> movement bound; movement + harmonic bound -> Theorem 1.3. The stochastic squared-loss motivation and no-regret semantics remain separate mandatory foundations.

Selected ready leaf: Lemma 1.2. Existing TsallisFTRLRegret is finite-action linear regularized optimization; its specific interface does not directly state arbitrary losses on arbitrary feasible sets. Prove the source's elementary induction without importing this specialization. No future-access algorithm will be presented as causal: the leader sequence in this lemma is explicitly an auxiliary hindsight comparator.
