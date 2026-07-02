# Cited Results: LML Bandit Library

| Result id | Source | Statement used | ABRL status | Used by | Reviewer note |
| --- | --- | --- | --- | --- | --- |
| `LML-BANDIT-REGRET-GAP` | LeanMachineLearning/LML `Bandits.regret_eq_sum_gap` | regret equals sum of selected action gaps | theorem-card | UCB, ETC, TS tasks | not local proof yet |
| `LML-BANDIT-REGRET-PULLCOUNT` | LeanMachineLearning/LML `Bandits.regret_eq_sum_pullCount_mul_gap` | regret equals sum over arms of pull count times gap | theorem-card; local deterministic analogue compiled as `pseudoRegret_eq_finset_sum_gap_mul_pullCount` | UCB, ETC tasks | external LML theorem still not imported/ported |
| `LML-UCB-REGRET` | LeanMachineLearning/LML `Bandits.UCB.regret_le` | finite sub-Gaussian UCB regret bound | theorem-card | `BRL-UCB-PORT-001` | dependency route undecided |
| `LML-ETC-REGRET` | LeanMachineLearning/LML `Bandits.ETC.regret_le` | finite sub-Gaussian ETC regret bound | theorem-card | `BRL-ETC-PORT-001` | dependency route undecided |
| `LML-TS-BAYES-REGRET` | LeanMachineLearning/LML `Bandits.integral_regret_le` | Thompson sampling Bayesian regret bound | theorem-card | `BRL-TS-BAYES-001` | dependency route undecided |
