# Actual CUCB concentration producer

2026-09-18. Partial progress under the complete triggered-CUCB contract `81a1998`. Both source regret endpoints and topic acceptance remain incomplete; accepted topics are still 0/10.

## Mathematical connection now implemented

`CUCBHistory.oracleInput_visible` proves that matching past observation masks and matching observed outcomes suffice for equal oracle inputs. Masked latent values and aggregate reward coordinates cannot affect the policy. This strengthens the previous causality theorem, which compared whole feedback records.

`Algorithms/CUCBRoundMGF` derives uniform integrability from bounded outcomes and the marginal mean range. It integrates the primitive observation-factor inequality over `roundKernel` using the actual oracle/action/environment composition-product. The action whose feedback is sampled is the action drawn by that oracle; it is not an independent replacement action.

`Algorithms/CUCBConditionalMGF` proves exponential integrability at every real multiple of the compensated increment. It then uses the constructed trajectory's initial law and conditional successor law to produce `cucb_initial_MGF` and `cucb_successor_condMGF`. These inhabit the shared fixed-tilt concentration interface without assuming an external conditional-MGF or confidence estimate. The only probabilistic input beyond the constructed Markov kernels is the primitive `ObservationCompatible` equality of measures and probability law of bounded outcomes.

`Algorithms/CUCBConcentration` uses the shared compensated-MGF accumulation theorem to derive upper and lower tails on that same infinite trajectory, including its genuine first round. For actual observed count T and centered observed sum Z, it proves

    P[Z >= x and T <= b] <= exp(-2 x^2/b),
    P[-Z >= x and T <= b] <= exp(-2 x^2/b),

for x>=0 and b>0. `sum_pathCount` and `sum_pathNoise` identify these variables with the learner's actual masked statistics; the final declarations `observed_sum_upper_tail` and `observed_sum_lower_tail` expose those statistics directly.

`Algorithms/CUCBConfidence.path_deviation_confidence` peels over counts 1 through n. For each direction separately and L>=0, the probability of positive count T and directional centered deviation at least sqrt(T L/2) is at most n exp(-L). No conditioning on the random count is used. This is the required adaptive statistical producer, but conversion to the exact simultaneous CUCB nice-event bound still remains.

`Tests/CUCBConcentrationCanary` checks that arbitrary hidden outcomes and reward values do not alter the oracle input, and audits the new probability chain's axioms. It is not the nondegenerate noisy final-performance canary required by the contract.

## Remaining source work

- Convert centered-sum confidence to the exact empirical-mean radius with L=3 log(t), union over arms and both tails, and handle zero observations and radius clipping explicitly.
- Assemble the finite feasible-action, trigger-probability, score/smoothness and approximation-oracle model. The existing generic trajectory does not itself impose all source model properties.
- Construct the normalized analysis-counter recursion, prove its predictability, and derive charged-trigger lower tails from the actual environment law.
- Prove actual/mean reward expectation identity, the source impossible-case lemma and sufficient-sampling count bound.
- Complete both exact regret endpoints, the noisy combinatorial final canary, independent semantic review, shared mappings and all-ten-topic ICLR evidence.

The shared fixed-MGF and finite-union tools are real proof dependencies reused here. No empirical efficiency effect, controlled experiment, independent reviewer verdict, merge or deployment follows from these local mathematical results.
