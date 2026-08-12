# Proof Obligations: Generated finite-arm empirical-mean telescoping all-time confidence

Task id: `CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-TELESCOPING-ALL-TIME`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`TXT-BUBECK-CESABIANCHI-2012`, `PPR-AUER-CBF-2002-UCB1`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `SCHEDULE` | `delta/((n+1)(n+2))` is positive and its ENNReal shares sum exactly to `ofReal delta` | Real reciprocal telescope | `ConcentrationConfidenceSchedule`, `HasSum`, `ENNReal.hasSum_coe` | Mathlib order/specific-limits cards; compiled OFUL precedent | finite reciprocal telescope, `HasSum`, NNReal/ENNReal coercion | `0<=delta`; strict positivity separately | project-local | lower | `Concentration.tsum_ofReal_telescopingConfidenceShare` | focused Lean | compiled |
| `FINITE-UNION` | finite arms and countable times retain total budget `delta` | `SCHEDULE`; generic finite uniform/countable union | `ConcentrationFintypeGeometricAllTime` generic parent APIs | `MLIB-MEASURE-INTEGRAL` | instantiate generic scheduled union and rewrite exact tsum | measurable ambient; finite nonempty arms; no event measurability | project-local | lower | `Concentration.measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare` | focused Lean | compiled |
| `GENERATED-ROOT` | canonical finite-arm empirical means satisfy the telescoping all-time radius simultaneously | `FINITE-UNION`; accepted fixed-horizon random-count tail | `ConditionalRewardPartialTrajectoryMaskedLaw` | local compiled declarations; textbook/paper/scenario placement | instantiate at `n+1` and `share/card` on one exact `trajMeasure` | probability initial law; finite nonempty Standard Borel arms; measurable context/state/mean; centered kernel law; variance ceiling; stationary means; positive proxy/delta | project-local | lower | `ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure` | focused/root/Tests/full gate | compiled |
| `ROOT` | imports, typed canary, fence, review, memory/frontier/docs/site/full gate | all above | repository harness | all above | no scope inflation | no fixed-policy UCB claim | project-local | reviewer | same terminal | `python3 tools/bandit.py check` | accepted (`mem-bf2d4d618cb0e53d`) |

## Failure Classification

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- missing regularity contract;
- likely false statement or counterexample;
- invalid route;
- stale dynamic leaf;
- connected blocker.

## Reviewer Notes

- Keep failed attempts in `proof-attempts/CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-TELESCOPING-ALL-TIME/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.
