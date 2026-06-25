---
name: bandit-concentration
description: Maintain proof obligations for Hoeffding, sub-Gaussian, martingale, and confidence-bound steps in bandit regret proofs.
argument-hint: "[task id or theorem]"
---

# Bandit Concentration

Use this skill for UCB, ETC, Thompson sampling, high-probability regret, or any
proof that invokes a tail bound.

## Required Ledger

Every concentration step must record:

- random variable or process;
- filtration or independence assumption;
- mean or conditional mean;
- variance proxy or bounded range;
- exact tail event;
- theorem source or local Lean declaration;
- whether the bound is one-sided, two-sided, uniform-in-time, or union-bounded.

## Common Routes

| Route | Typical use | Required blocker if missing |
| --- | --- | --- |
| sub-Gaussian MGF | UCB/ETC reward sums | MGF centered at arm mean |
| Hoeffding bounded rewards | simple finite-arm examples | bounded interval and independence |
| martingale concentration | adaptive rewards or RL | filtration and conditional MGF |
| peeling/union bound | anytime confidence | event family and summability |
| posterior confidence | Thompson sampling | posterior/action distribution identity |

## Reviewer Rule

Do not let a lower agent hide a concentration theorem inside prose.  If the
tail bound is not locally proved or imported, it must be a cited result or a
proof obligation.
