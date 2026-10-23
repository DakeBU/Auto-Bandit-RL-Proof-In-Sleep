# Batch25 implementation, dependency and reuse audit, stage 3

Reviewer: `/root/batch25_source_reviewer`. This is an explicitly **nonblind** stage, begun only after stage 2 was hash-sealed. Verdict: **accepted for the bounded original four production proofs and sixteen canary declarations against the inspected current shared dependencies**, retaining the stage-2 explicit source deltas. No blocking mathematical issue or proof-ingredient assumption smuggling was found. No production file or Git reference was changed by this reviewer.

## Evidence actually reviewed

Original production and canary captures under `batch25-intake-v1` were read completely. The reviewer read the current canonical implementations of OnlineGuessingRandomizedIID, OnlineGuessingIIDBenchmark, OnlineLearningHistory, OnlineLearningIID, OnlineLearningInformation, OnlineLearningStochastic, OnlineLearningFTL, OnlineLearningMean, OnlineLearningFoundations and OnlineLearningAsymptotic. This was a fresh review of current code, not reliance on their prior acceptance labels. The reuse decision and all twelve stored search outputs were read, and every search-output hash matched its receipt.

The root actor ran the private probe. This reviewer did not run that compiler command independently, but inspected its exact assembled source, successful receipt, complete log and all twenty exported dependency rows. The v2 receipt records exit 0 for `lake env lean .../batch25-actual-proof-probe-v2/Probe.lean`. Its accepted comparison main is `b4205fcf445d387f8226c0d763aac70afb189f98`; the recorded workspace head is `9e3d8d61e3c02bec1bb899d95677c4674f10cc30`, sharing tree `69a575ed37f3946be65eadeac8ccd6f94213259c` with current main. The reviewer independently observed that main tree and a clean canonical status.

Both original captures are byte-identical to the probe's stored source copies. The complete non-import original text of each file, including all statements and proof bodies, occurs unchanged in the assembled Probe.lean after line-ending normalization. The probe adds imports, neutral literal propositions and definition/type checks. It removes the canary's import of the not-yet-installed production module because those original production declarations are elaborated earlier in the same private file. The receipt's source bindings, probe, neutral propositions, log and dependency hashes were verified.

The v1 assembly failure is not successful compilation evidence. The parent reported that a duplicate universe command in the private wrapper was repaired in v2. This review's compiler conclusions rely only on the terminal v2 receipt/log. The v2 warnings concern unused hypothesis names inside neutral proposition definitions, which bind the hypotheses to reconstruct the complete theorem types. They are not errors in the original proofs and do not erase those premises from the checked types.

## Four production proofs against the sealed obligations

| Anchor | Reviewed implementation and obligation discharge |
|---|---|
| S001 | Constructs an eventual implication for zero denominator by restricting to T>0, invokes the signed `isLittleO_iff_tendsto'` API, and uses `normalized_excess` only on positive horizons. It never requires total(0)=0. This discharges D1/GAP-NORMALIZATION without replacing the arbitrary signed target with a one-sided bound. |
| S002 | Calls the existing randomized-history finite excess producer for the exact seed/policy/observations and uses its second component for all-T nonnegativity. It separately obtains the expected-fixed minimum identity. S001 gives the first asymptotic iff after that identity is substituted. The second iff follows from eventual equality at T>0 obtained from the finite risk identity, divided by T. This is a real finite-to-asymptotic composition; neither iff nor the risk identity is a public premise. |
| S003 | Forms a common conull event from the countable a.s. support assumptions. It derives L2 bounds for observations and the concrete mean prediction, then integrability of learner and constant-comparator finite sums. On each bounded path, `theorem_1_3` plus `empiricalMean_minimizes` bounds regret against m=E[Y0]. It integrates that inequality using proved integrability, identifies fixed-m loss as T variance, and uses the attained expected-fixed minimum. No observation independence is used, and the learner never receives m. The chosen route is the fixed-mean OR branch from stage 1; no E/min interchange occurs. |
| S004 | Derives the lower normalized bound from the existing IID causal mean-prediction excess theorem and the upper bound from S003 at eventually positive T. It derives 1/T and log(T)/T limits from the Mathlib real limit theorem and natural-to-real cofinality, assembles the logarithmic envelope, uses two-sided squeeze, and applies S001 with c=0 for little-o. It asserts both intended conclusions for the actual same process. |

## Current dependency audit

The finite stochastic producers supply the key premises internally:

- `expected_fixed_prefix_decomposition` derives L2 from a.s. bounds, exchanges only a finite sum with an integrable expectation, and transports each marginal's mean/variance through IdentDistrib. No independence is used.
- `expected_fixed_prefix_minimum` proves the population mean belongs to [0,1], exhibits its expected loss in the image, and proves it is least. `expectedFixedMinimum_eq_variance` uses `IsLeast.csInf_eq`. Thus the sInf is characterized by actual attainment, including T=0 without a uniqueness claim.
- `randomized_history_policy_expectedFixed_excess` builds a.s. prediction feasibility from legal-history feasibility and the conull observation support. It constructs measurable prediction in the seed/past information sigma algebra, then calls the information-level producer.
- `private_seed_past_independent` derives independence of the whole finite-past block and current observation from mutual independence, projects seed independence from the full process to that block, and invokes `independent_private_seed_pair`. That lemma proves the regrouped joint-law factorization. It does not confuse pairwise independence with independence of seed-plus-past from the present.
- The predictable information producer derives ambient measurability, L2 and current-observation independence, then applies `iid_cumulative_prediction_decomposition`. Its hP/hInd consumer premises are therefore supplied by proved producer edges, not smuggled into S002.
- `meanPredict_expectedFixed_excess` separately derives actual meanPredict measurability, a.s. boundedness and current-observation independence, using the zero-round constant and the strict-past sum at positive rounds. It avoids the older pointwise-bound convenience APIs. The risk identity reduces to `independent_prediction_square`, whose covariance-zero step explicitly uses the produced current independence and L2 facts.
- `expected_square_decomposition` and `independent_prediction_square` prove the actual variance/square identities using finite moments and covariance, not opaque assumed source claims.

For the deterministic source route, `empiricalMean_decomposition` proves the exact finite complete-square identity and `empiricalMean_minimizes` derives the global minimizer inequality. `lemma_1_2` uses induction, local prefix restriction, feasibility and minimization, corresponding to the source's cancellation/IH/prefix comparison. Its empty-horizon extension is harmless.

The current `theorem_1_3` uses `lemma_1_2`, `meanPredict_stability` and Mathlib's `harmonic_le_one_add_log`. Its implementation route is not a literal copy of every printed algebraic line: stability uses the running-average recurrence and the coefficient `(2/(t+1)-1/(t+1)^2)` times a squared bounded residual, and the initial term is relaxed directly to 4. The separately named `meanPredict_initial_stability` and `meanPredict_regret_refined` retain the source's sharper 1/4 first term, but they are not called by S003's actual theorem_1_3 dependency. The harmonic integral is reused as a Mathlib inequality, rather than reconstructed from the drawing inside this proof. These are valid implementation-route differences, not reasons to rewrite the independently sealed source topology or falsely claim every printed node is a direct Lean dependency.

## Actual compiled dependency and axiom checks

Every one of the twenty exported owned declarations has a value. No value-constant row contains a sorry/admit marker or a NeutralPacket proof dependency. The actual project-level production edges are:

- S001 -> normalized_excess.
- S002 -> randomized_history_policy_expectedFixed_excess, expectedFixedMinimum_eq_variance, S001, normalized_excess, plus the literal regret/minimum definitions.
- S003 -> theorem_1_3, empiricalMean_minimizes, meanPredict_mem, meanPredict_measurable, expected_fixed_prefix_decomposition, expectedFixedMinimum_eq_variance, plus literal mean/prediction/benchmark definitions.
- S004 -> meanPredict_expectedFixed_excess, S003, S001, plus literal predictor/regret definitions.

These are proof-value references, not inferred import edges. The JSON also retains standard elaboration/type constants, so it should not be presented as a graph of only conceptual mathematical dependencies.

The log prints all twenty axiom sets as subsets of exactly `Classical.choice`, `propext`, and `Quot.sound`. Four fresh neutral proposition assignments compiled, checking the exact four universal theorem types against the source-blind packet, and four full literal-definition equality checks compiled by rfl. No theorem-body identity or a mere name comparison was substituted for these checks.

## Canary audit and all sixteen declarations

1. `actual_meanPredict_success`: instantiates S004 in the existing IID observation model.
2. `actual_meanPredict_upper`: instantiates S003 at positive horizon.
3. `actual_meanPredict_two_round_positive`: checks actual two-round expected excess is 1/4.
4. `actual_positive_variance`: checks the model variance is 1/4.
5. `persistentPolicy`: literal seedBit policy, ignoring time and history.
6. `persistentPolicy_measurable`: proves measurability by seedBit and first projection.
7. `persistentPolicy_legal`: proves [0,1] output for every seed, even without using the bounded-history premise.
8. `persistentPrediction`: literal composition of this policy with seed and strict history.
9. `persistent_excess`: uses the finite randomized excess producer and `(seedBit(s)-1/2)^2=1/4` to obtain R(T)=T/4, including T=0.
10. `persistent_normalized_limit`: derives normalized limit 1/4 only by eventual positive division.
11. `persistent_not_sublinear`: contradicts uniqueness of limits if little-o were supplied.
12. `persistent_policy_not_successful`: uses S002's iff to refute the centered-average zero limit for this legal policy. This exercises characterization rather than universal success.
13. `zero_horizon_difference`: explicitly distinguishes centered normalized loss=-1/4 from normalized regret=0 at T=0.
14. `nonzero_initial_total_sublinear`: exercises S001 on total(T)=5+3T, where total(0) is nonzero, using an eventual identity.
15. `correlated_meanPredict_upper`: applies S003 to the constant-in-time observation process without an IID premise.
16. `correlated_meanPredict_negative_two`: proves its two-round expected-fixed regret is -1/4, preventing an unjustified nonnegative extension to S003.

The twenty compiled rows are four production theorems plus fourteen canary theorems and two canary definitions. Canary wrapper instantiations and diagnostic identities are validation, not sixteen additional source theorems or new shared-library advances. Their referenced imported test models are reused, and this review did not re-review the entirety of those imported test modules or run a full fresh root build.

## Reuse, binders and purification scope

The `adapt_existing` decision is supported by current declarations and actual compiled references. S001 is a useful normalization adapter with two genuine production consumers, S002 and S004, rather than a duplicate of the positive finite identity. S002 adds asymptotic equivalences to an existing finite excess theorem. S003 lifts the source pathwise bound to the expected-fixed benchmark. S004 closes the actual learner's stochastic zero limit. `meanPredict_noRegret` proves a distinct one-sided comparator-wise condition and cannot replace S004's ordinary zero limit.

No new foundational library, toolchain or external dependency is required. No shared primitive should receive novelty credit merely for these compositions. The logarithmic-envelope calculation resembles the local calculation in OnlineLearningAsymptotic, but the reviewed patch adds no duplicate public declaration for that arithmetic. Extracting a future shared envelope lemma is an optional purification step, not grounds to rewrite these sealed source signatures or a current blocker.

The stage-2 full binder ledger remains valid. All high-risk mathematical ingredients are internal proof dependencies: causal independence, L2/integrability, benchmark attainment, nonnegativity, pathwise regret upper bound, envelope convergence and final squeeze. There is no added convergence, risk decomposition, confidence event or fixed-mean-oracle learner hypothesis. The randomized sufficient-model assumptions remain explicitly derived-model premises rather than printed source binders.

## Bounded result

Stages 1–3 together support the bounded source-aware scientific acceptance of these original four proofs and diagnostics with explicit application deltas. The private exact-original elaboration is root-run evidence, independently inspected here. It is not a fresh imported-module compilation, combined root/Tests/full harness gate, rendered-reader check, contribution-contract acceptance, merge, live publication, entire-PR closure, chapter completion or authorization to retire refs. Those states remain separate.


---
Public location projection of private evidence batch25-source-review-v1/stage3-implementation-review.md. Original SHA256: `4d4872be0e03e4d71ddfe4134938b8a6a70537d1fd2744ff8a426d5d2b7711b8`. Physical paths alone are logicalized; original stage wording and limits remain unchanged. Later bounded status is recorded in review-binding.json.
