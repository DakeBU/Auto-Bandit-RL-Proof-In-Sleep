# Mathlib Candidate Leaves

This directory records proof-DAG leaves that are general enough to prepare for
future Mathlib contribution.  A candidate is not accepted as local certified
memory until it compiles in this repository or is imported from an upstream
library.

## Candidate Record

Use one section per candidate:

```text
## CANDIDATE-ID

- Proposed name:
- Mathematical area:
- Intended Mathlib namespace:
- Exact statement:
- Required imports:
- Local APIs:
- Intended proof route:
- Regularity contracts:
- Current ABRL task:
- Status: proposed | in-progress | locally-compiled | upstreamed | rejected
- Failure signal:
```

## Seed Areas For Bandit/RL Proofs

| Area | Typical leaf | Why it should be reusable |
| --- | --- | --- |
| Finite sums | pull-count decompositions, indicator sums, finite support rewrites | common across bandit, online learning, and probability proofs |
| Order and algebra | gap nonnegativity, monotone confidence radii, denominator positivity | not bandit-specific when stated cleanly |
| Regularity | integrability, measurability, continuity, nonemptiness, boundedness | hidden assumptions should become theorem contracts |
| Concentration infrastructure | union bounds, tail-event monotonicity, sub-Gaussian closure | useful beyond a single regret proof |
| Asymptotics | logarithmic and square-root regret simplifications | should not be buried inside algorithm proofs |

## Review Rule

Before adding tactic work, the candidate must name local APIs and an intended
proof route.  If repeated attempts fail, record whether the likely issue is a
false statement, missing assumption, wrong abstraction, unavailable API, or
counterexample.  Do not repeatedly rewrite the proof route without that audit.
