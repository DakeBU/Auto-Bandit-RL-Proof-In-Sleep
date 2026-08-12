# Book Map Chapters 7--8 canonical completion

Task id: `BOOKMAP-CHAPTERS-7-8-CANONICAL-COMPLETION`

Kind: `lean`

Status: `accepted`

Harness: `hierarchical`

## Goal

Promote two independent Book Map gates only after the external typed canary and
the full repository gate verify their exact canonical scopes:

- `CH7-EXP3-CANONICAL-COMPLETION`;
- `CH8-TSALLIS-FTRL-CANONICAL-COMPLETION`.

One gate never implies the other.  The joint task is accepted only when both
are accepted.

## Source placement

- Chapter 7: `TXT-BUBECK-CESABIANCHI-2012`,
  `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CFS-2002-EXP3`,
  `SCN-ADVERSARIAL-FINITE`, and inspiration-only
  `WEAPON-EXP3-POTENTIAL`.
- Chapter 8: `PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF`,
  `PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF`,
  `PPR-ADAPTIVE-LR-FTRL-2024`, `SCN-ADVERSARIAL-FINITE`,
  `SCN-BOBW-ADAPTIVE`, and inspiration-only
  `WEAPON-TSALLIS-INF-FTRL`.
- Mathlib cards are retrieval evidence.  No theorem card or proof weapon is a
  local proof term.

## Chapter 7 completion definition

The scoped canonical model has a finite nonempty decidable action set, a
probability prior on a Standard Borel environment, predictable adversarial
loss vectors in `[0,1]`, positive exploration, and the canonical generated
recursive importance-weighted EXP3 trajectory.  Completion requires the
traceable local chain:

1. exponential-potential one-step algebra;
2. deterministic Hedge regret decomposition;
3. importance-weighted estimator legality and positive support;
4. conditional first moments;
5. conditional second-moment or mixed-square control;
6. measurable recursive trajectory generation;
7. predictable-to-observed loss transport;
8. exploration-bias control;
9. horizon-tuned expected regret;
10. fixed-window best-supported-arm realized high-probability regret;
11. one fixed process and comparator with an all-positive-prefix realized
    regret event;
12. a separately labelled sparse/variance-sensitive endpoint.

The tuned expected theorem keeps `K >= 2`, `T > 0`,
`4*K*log K <= T`, comparator membership, and its horizon-dependent tuned
`eta`, `gamma`, and generated law.  The fixed-window best-arm theorem may be
instantiated at every positive horizon, but changing the horizon changes its
parameters and trajectory law.  Its name `allHorizon` does not mean a single
horizon-free policy with one simultaneous anytime event.

The same-process terminal
`Exp3.measure_sampledRealizedRegretGeometricAllTimeFailureSet_le` instead fixes
the prior, arms, loss, `eta`, `gamma`, and one supported comparator across all
positive prefixes.  It composes the predictable-regret and pure
realized-deviation failure sets through the exact pathwise decomposition and a
geometric countable outer-measure union.  It is not a horizon-varying tuned
sublinear confidence sequence.

## Chapter 8 completion definition

The scoped canonical model has a finite nonempty decidable action set, a
probability prior over a Standard Borel predictable `[0,1]` loss environment,
the half-Tsallis (`alpha = 1/2`) regularized finite-simplex minimizer, a
positive nonincreasing learning-rate schedule, importance-weighted feedback,
and the canonical generated recursive trajectory.  Completion requires:

1. finite-simplex and half-Tsallis regularizer interfaces;
2. existence, interiority, uniqueness, and measurable canonical minimizers;
3. one-step importance-weighted stability;
4. time-varying potential/penalty decomposition;
5. measurable scheduled history selector and recursive trajectory kernel;
6. actual conditional action law on the generated history;
7. observed importance-weighted score and FTRL probability alignment;
8. initial and successor expected stability;
9. all-times/all-rate stability summation;
10. expected predictable-environment regret on that trajectory;
11. suboptimal-probability and fixed-gap self-bounding transport;
12. the square-root schedule and logarithmic reciprocal-gap optimization;
13. a concrete finite-arm IID `[0,1]` bounded rational reward-law producer;
14. exact model-mean/gap transport and the generated logarithmic regret
    terminal
    `Tsallis.integral_sampledScheduledHalfTsallisFiniteArmIIDRewardLawRegret_le_log`.

The final theorem retains a positive finite model, probability arm laws,
a.e. `[0,1]` support, exact arm means, positive non-best gaps, a finite
horizon, and a nonnegative explicit additive corruption allowance.  The
canonical uncorrupted specialization sets that allowance to zero.

## Acceptance checklist

- [x] Required local declarations exist on the current Lean 4.29.1 toolchain.
- [x] `Tests/BookMapChaptersSevenAndEightCanary.lean` contains six route groups.
- [x] Chapter 7 expected, fixed-window, same-process, and sparse terminals have
  full-conclusion typed applications.
- [x] Chapter 8 generated law/alignment/stability/regret surfaces are checked.
- [x] Chapter 8 final IID reward-law theorem has a concrete nondegenerate
  `Fin 2` application with exact means `3/4` and `1/4` and a positive gap.
- [x] Focused canary build passes; audited axioms are baseline only.
- [x] Chapter, result, highlight, diagram, README, and overview surfaces agree.
- [x] Lifecycle/retrieval/frontier/manifest surfaces agree.
- [x] Full `python3 tools/bandit.py check` and website gates pass.

GitHub PR, Actions, merge, and Pages are post-commit delivery checks.  They are
recorded in the live handoff rather than self-certified by the commit being
delivered.

## Nonclaims and extensions

Chapter 7 completion does not claim a single horizon-free tuned EXP3 policy,
a tuned sublinear confidence sequence, optional stopping, Ville/Doob or
mixture boundaries, ideal EXP3.P, contextual/delayed EXP3, or one universal
theorem subsuming every hypothesis regime.  The sparse theorem retains its
supplied sparsity-failure probability.

Chapter 8 completion does not claim paper-sharp or minimax-optimal Tsallis-INF
constants, a complete best-of-both-worlds theorem, high-probability or realized
regret, contextual/linear Tsallis-INF, an observed-reward change detector, or
that the corruption, drifting-law, dynamic-comparator, and oracle-restart
extensions are prerequisites for the canonical chapter.  The compiled
`Fin 2` refined-averaged-stability obstruction remains visible and is not
silently bypassed.

## Failure policy

If either child gate fails, keep that chapter partial and record the exact
declaration, current compiler goal, regularity contract, retrieval evidence,
and next smallest bridge.  Do not weaken either terminal, substitute an
independent trajectory, add a hypothesis equivalent to the conclusion, or
promote a theorem card/proof weapon as a local proof.
