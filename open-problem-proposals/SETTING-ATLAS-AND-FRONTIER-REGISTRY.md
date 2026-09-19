# SETTING-ATLAS-AND-FRONTIER-REGISTRY — canonical taxonomy and open-problem history

Problem id: `SETTING-ATLAS-AND-FRONTIER-REGISTRY`

Priority: **P0 for registry infrastructure; P0/P1/P2 per setting/problem record**

Status: first canonical JSON registries and public views added on the feature branch. Promotion into the legacy generated `banditrlwiki.json` topic cards remains a generator/data migration task, not a reason to duplicate or silently fork the old case data.

## Problem

The existing BanditRLwiki Setting Atlas has a useful coarse family layer and ten source-audit-pending topic cards, but an alphabetic list of every label mixes incompatible object types:

- mathematical settings (`heavy-tailed`, `causal`, `combinatorial`),
- objectives (`BAI`, regret minimization),
- algorithm families (`Thompson sampling`, `GP-UCB`),
- cross-cutting properties (`parameter-free`, `variance-aware`),
- application bridges (`LLM`),
- ambiguous shorthand (`OMDP`, `SLB`, `Transform`).

This prevents reliable coverage auditing and makes theorem comparisons unsafe.

## Canonical axes

The new `website/public-repo/data/setting-atlas.json` separates:

1. Foundations & objectives.
2. Feedback, noise & robustness.
3. Structured action/reward models.
4. Time, availability & resources.
5. Multi-agent / distributed learning.
6. Algorithm families.
7. RL & application bridges.
8. Source-disambiguation quarantine.

Every entry has `kind`, `axis`, `priority`, `site_status`, aliases and a short contract description.

## Normalizations from the collaborator list

- `Bolling Bandits` → likely **Ballooning Bandits (BL-MAB)**; retain the misspelling as an alias.
- `Tompson Sampling` → **Thompson sampling**, method rather than setting.
- `BAI and RM` → two objective nodes: **best-arm identification** and **regret minimization**.
- `Gaussian Process UCB` → GP-UCB method under the broader **kernel/RKHS bandit** setting.
- `Multinomial Bandits` → use **MNL/assortment bandits** only when the source means multinomial-logit choice; a generic multinomial reward law is not a separate top-level setting.
- `OMDP`, `SLB`, `Transform` → quarantine until a source fixes the expansion/definition. `SLB` may mean stochastic linear bandits, but this must not be guessed into the canonical graph.

## Important settings missing from the original list

At minimum the atlas must also expose explicit routes for:

- adversarial bandits;
- linear bandits;
- kernel/RKHS bandits;
- partial monitoring;
- bandits with knapsacks / budgeted bandits;
- sleeping/availability bandits;
- rotting/rising/restless bandits;
- batched/limited-adaptivity bandits;
- risk-sensitive/CVaR/survival bandits;
- multi-objective/Pareto bandits;
- private/JDP bandits;
- sparse/high-dimensional bandits;
- offline RL, POMDP, online/adversarial MDP and linear/kernel MDP routes.

## Frontier registry semantics

`website/public-repo/data/frontier-problems.json` stores **problem history**, not only currently open problems. A record may be:

- resolved with external formalization;
- resolved by peer-reviewed work;
- resolved by a current preprint;
- negatively resolved by a current preprint;
- partially resolved / under current audit;
- source-open under current audit;
- audit-needed.

Each record separates:

1. mathematical status;
2. publication/review status;
3. Lean status;
4. graph contribution.

## Social posts, talks and informal open problems

An informal item may enter the intake queue if it has an author-controlled or otherwise stable URL, author, date and a faithful short statement. It must carry an evidence grade. It cannot be promoted to a theorem-comparison case until the mathematical contract is frozen from a primary paper, manuscript, talk notes or author-maintained source.

Never turn “someone said this is open on social media” into an unconditional literature claim.

## First P0/P1 audit queue

### P0

- Gap-entropy / almost instance-wise optimal BAI — resolved in 2026; external Lean formalization available.
- Fixed-budget BAI instance complexity — Qin 2022; 2026 negative-resolution preprint must be audited theorem-by-theorem.
- Heavy-tailed bandits with unknown parameters — COLT 2025; 2026 parameter-free resolution preprint.
- Tight online RKHS confidence intervals — COLT 2021.
- Noise-free kernel bandit regret — COLT 2022.
- Order-optimal kernel RL — COLT 2024.
- Distributional regret conjecture from Lattimore–Szepesvari Chapter 17 — resolved by Lee–Oh COLT 2026; lower side already has local formalization evidence.

### P1

- Contextual first-order regret — historical resolved case.
- Contextual model selection — progress/impossibility map rather than a binary open/closed label.
- JDP linear contextual bandits — 2024 source gap plus current progress.
- Parameter-free dynamic linear bandits — 2026 reported resolution of a long-standing problem.
- RL horizon-dependence lower bounds — closure audit needed.

### P2 / later book routes

- POMDP memoryless planning.
- Risk-of-ruin/survival bandits.
- Limited-expert-advice historical resolution.

## Acceptance gate for promotion into legacy generated pages

1. `setting-atlas.json` is the canonical registry; do not manually duplicate dozens of topic definitions in multiple files.
2. Extend the site generator so `Bandit Book → Extended Chapters` and `BanditRLwiki → Setting Atlas` both read the canonical registry or a generated projection of it.
3. Preserve old topic URLs/aliases during migration.
4. Add schema validation for unique IDs, recognized kinds/axes/priorities, and valid source URLs where required.
5. Add a frontier audit date and evidence grade to every informal/current-open record.
6. Keep mathematical-open, formalization-open and source-audit-pending statuses distinct in UI and filters.
