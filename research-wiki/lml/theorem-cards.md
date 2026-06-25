# LML Theorem Cards

Source: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)

Seed commit: `19dc3ab132c2a7539f5944503d1114eac4c5bb74` (2026-06-24).

Status rule: every entry below is a theorem card until ABRL imports or ports
the declaration and passes the local Lean gate.

| Card id | LML declaration | Module | ABRL use | Status |
| --- | --- | --- | --- | --- |
| `LML-BANDIT-REGRET-GAP` | `Bandits.regret_eq_sum_gap` | `LeanMachineLearning.Online.Bandit.Regret` | regret as sum of gaps | theorem-card |
| `LML-BANDIT-REGRET-PULLCOUNT` | `Bandits.regret_eq_sum_pullCount_mul_gap` | `LeanMachineLearning.Online.Bandit.Regret` | pull-count regret decomposition | theorem-card |
| `LML-ETC-REGRET` | `Bandits.ETC.regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.ETC` | Explore-Then-Commit expected regret | theorem-card |
| `LML-UCB-REGRET` | `Bandits.UCB.regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.UCB` | UCB logarithmic regret route | theorem-card |
| `LML-TS-POSTERIOR-ACTION` | `Bandits.TS.hasCondDistrib_action` | `LeanMachineLearning.Online.Bandit.Algorithms.TS` | posterior best-action identity | theorem-card |
| `LML-TS-BAYES-REGRET` | `Bandits.integral_regret_le` | `LeanMachineLearning.Online.Bandit.Algorithms.Regret.BayesRegretTS` | Bayesian regret upper bound | theorem-card |

## Migration Notes

- LML currently uses a newer Lean toolchain than ABRL's dependency-light core.
- Do not add LML as a dependency without a task-level decision and build test.
- For small local ports, copy the theorem statement manually, attribute LML,
  and reprove or adapt the proof under ABRL's gate.
- For direct import, update `lakefile`, `lean-toolchain`, `NOTICE.md`, and the
  conversion window in the same change.
