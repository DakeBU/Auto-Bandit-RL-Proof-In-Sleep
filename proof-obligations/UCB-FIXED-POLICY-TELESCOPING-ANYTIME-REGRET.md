# Proof Obligations: Fixed-policy telescoping anytime UCB regret

Task id: `UCB-FIXED-POLICY-TELESCOPING-ANYTIME-REGRET`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`; `TXT-BUBECK-CESABIANCHI-2012`; `PPR-AUER-CBF-2002-UCB1`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-FIXED-POLICY-SCHEDULED-RADIUS` | exact scheduled radius/score definitions, nonnegative and measurable | telescoping schedule; current random-count radius | `ConditionalRewardLawSource`; `ConcentrationConfidenceSchedule`; finite-history countability | `MLIB-REAL-LOG-SQRT`; `MLIB-ORDER-ALGEBRA` | substitute the share `delta_t/K`; finite/countable measurability; explicit radius expansion | `0<K`; `0<delta`; positive count only for inversion | project-local | middle | `UCB.selectedPolicySuccessorTelescopingRadiusAt_nonneg`; `...LogBudget_mono` | focused Lean | compiled |
| `UCB-FIXED-POLICY-SCHEDULED-POLICY` | one policy/state/generated action/measure with no terminal horizon | scheduled radius | current `selectedPolicySuccessorHistory*`; `scoreArgmax`; initialization | local Lean declarations | structural recursion on reward histories; strict finite argmax | `Fin K` nonempty; Rat histories countable | project-local | middle | `UCB.selectedPolicySuccessorTelescopingHistoryPolicy`; `...ActionRewardTrajMeasure` | focused Lean | compiled |
| `UCB-FIXED-POLICY-GENERATED-ALIGNMENT` | reconstructed pair history, score, empirical count/mean, and selected action equal the generated trace quantities | scheduled policy | completed-history preservation lemmas; `generatedActionFromRewardHistory` | `MLIB-FINSET-SUMS` | structural induction plus completed-prefix identities | exact reward-reconstructed trace; sampled pair action is explicitly transported a.e. | project-local | lower | `UCB.selectedPolicySuccessorTelescopingPairHistory_eq_finitePairHistoryOfTrace`; `...HistoryIndex_finitePairHistoryOfTrace` | typed application | compiled |
| `UCB-FIXED-POLICY-ALL-TIME-CONFIDENCE` | same-policy all-time deviation event has measure at most `ofReal delta` on one canonical `trajMeasure` | alignment; accepted telescoping producer | `ConditionalRewardPartialTrajectoryTelescopingAllTime` | `MLIB-PROBABILITY-SUBGAUSSIAN`; `MLIB-MEASURE-INTEGRAL` | exact-let producer plus sampled/generated action a.e. transport | centered reward kernel law; selected variance ceiling; stationary means; positive sigma2/delta | project-local | lower | `UCB.measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure` | exact-let canary and axioms | compiled |
| `UCB-FIXED-POLICY-GOOD-EVENT-COUNT` | for every finite `T` and positive-gap arm, the same good event implies the terminal scheduled pull-count bound | confidence; alignment; score max; terminal radius envelope | UCB confidence-score algebra; prior-count witness; initialization exclusion | `WEAPON-UCB-OPTIMISM` inspiration; `MLIB-REAL-LOG-SQRT` | selected arm plus optimism gives gap <= twice radius; terminal log envelope inverts radius | `T` is a consumer index only; `K<=t`; positive best/chosen counts and gap | project-local | lower | `UCB.selectedPolicySuccessorTelescoping_allHorizonPullCount_of_not_badEvent` | focused Lean | compiled |
| `UCB-FIXED-POLICY-REGRET` | finite-time expectation keeps explicit failure contribution after the all-horizon arm-count theorem | all-horizon arm count | pseudo-regret finite-sum identity; `lintegral_natCast_le_threshold_add_bound_mul_of_measure_gt` | `MLIB-FINSET-SUMS`; `MLIB-MEASURE-INTEGRAL` | sum positive-gap expected counts at each requested horizon | probability measure; action measurability; deterministic count cap | project-local | middle | `UCB.lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure` | root/tests/check | compiled |
| `UCB-FIXED-POLICY-TELESCOPING-ANYTIME-REGRET-ROOT` | exact-let terminal bundle exposing fixed policy, same trajectory, all-time confidence, all-horizon count and expected boundary | all nodes above | terminal module and dedicated canary | all cards above | conclusion-typed application on the canonical let-chain | no horizon in policy/measure definition; no average consistency claim from fixed delta | project-local | upper | terminal declaration above; fence `537a4279...7c08` | full `python3 tools/bandit.py check` | compiled |

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

- Keep failed attempts in `proof-attempts/UCB-FIXED-POLICY-TELESCOPING-ANYTIME-REGRET/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.
