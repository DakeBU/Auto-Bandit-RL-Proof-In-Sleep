# LML Integration

[LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML) is the
primary upstream Lean reference for ABRL.

The initial theorem-card seed was checked against upstream commit
`19dc3ab132c2a7539f5944503d1114eac4c5bb74` from 2026-06-24.

## Initial Mode

ABRL starts in theorem-card mode:

- LML declarations are recorded in `BanditRLProof/Literature.lean`;
- human-readable cards live in `research-wiki/lml/theorem-cards.md`;
- compact JSON cards live in `research-wiki/retrieval-index/lml_bandit_cards.json`;
- no LML source file is vendored or imported.

This keeps the initial Lean package fast and independent while preserving a
clear migration path.

## Main Theorem Cards

| LML declaration | Use in ABRL |
| --- | --- |
| `Bandits.regret_eq_sum_gap` | generic regret decomposition |
| `Bandits.regret_eq_sum_pullCount_mul_gap` | pull-count regret decomposition |
| `Bandits.ETC.regret_le` | Explore-Then-Commit regret route |
| `Bandits.UCB.regret_le` | UCB regret route |
| `Bandits.TS.hasCondDistrib_action` | Thompson posterior action identity |
| `Bandits.integral_regret_le` | Thompson sampling Bayesian regret bound |

## Migration Options

For each task, upper/middle should choose one of three routes:

1. `card-only`: use LML for planning and citation, no local theorem claim.
2. `port`: reimplement a small theorem locally, keeping attribution.
3. `dependency`: align toolchains and import LML or a downstream package.

The route must be written into the conversion window before lower agents spend
proof effort.

## License Note

LML is Apache-2.0.  If ABRL ports source-level code, update `NOTICE.md` and
the relevant file header before merging.
