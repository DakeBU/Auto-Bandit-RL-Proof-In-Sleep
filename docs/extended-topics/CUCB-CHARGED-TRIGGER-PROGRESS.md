# Actual CUCB charging and triggered-count concentration

2026-09-18. Partial progress under frozen full triggered-CUCB contract `81a1998`. Both exact source regret endpoints remain open; accepted topics remain 0/10.

## Actual analysis recursion

`Algorithms/CUCBCharge` defines `ChargeData` as fixed inputs to the analysis rule, explicitly separate from the full source instance. For bad actions it chooses the normalized threshold minimizer over possible-trigger arms, using integer historical counters, fixed inverse action gap and arm triggering lower bounds. Good actions produce no charge. The recursion starts at zero and increments exactly the selected arm once.

Proved: selection membership, threshold sufficiency for every possible-trigger arm with both exact coefficient branches, counters bounded by time and monotone one step, causality, total counter sum equals bad-round count, equality with the sum of actual charge indicators, measurability on the countable action/integer-counter domain, and invariance under arbitrary current feedback changes. `chargedObservations` counts successful observations on charged rounds and is bounded by both the corresponding counter and the learner's actual observation count. A pathwise deterministic-trigger implication is available, but its almost-sure premise still needs discharge from the actual environment.

`ChargeData` is not a complete source model: it does not assert that supplied gaps are actual score gaps or that lower bounds are source minima. The complete finite feasible-action/reward/smoothness/oracle model must construct this data and prove those connections. No topic completion follows from the structure.

## Primitive probability to actual adaptive tail

`Algorithms/CUCBTriggerMGF` derives, under an action's actual feedback measure,

    E exp(-lambda I_observed + (1-exp(-lambda)) p) <= 1

for lambda>=0 and p<=the actual observation probability. The proof integrates the two possible mask outcomes and uses 1+x<=exp(x). The observation probability premise is a primitive environment property, not an adaptive confidence or tail assumption. It imposes no independence between different arms.

`Algorithms/CUCBChargedMGF` uses the actual normalized charge at the current action, then integrates over the actual oracle/action/environment joint round kernel. Uncharged arms have factor one. It proves uniform integrability and the mixed round-factor bound.

`Algorithms/CUCBChargedConditional` extends a prefix only to compute past integer counters, proves the extension agrees with actual counters, and uses the constructed CUCB conditional trajectory law. Both the genuine first-round bound and successor conditional bounds are produced, with no current-feedback leakage.

`Algorithms/CUCBChargedConcentration` proves exponential integrability at every scalar and adaptation, supplies the shared fixed-tilt MGF accumulation interface, and identifies accumulated indicators with actual counters and charged observations. It derives, for k>=0 and p>=0,

    P[N_i(n)>=k and T_i(n)<=k p_i/2] <= exp(-k p_i/8).

Here N is the recursive normalized analysis counter, while T is the learner's actual masked observation count. The proof first bounds charged successes, then uses their pathwise domination by T. It chooses lambda=log(2), and proves the numerical exponent via mathlib's certified log(2)<0.6931471808 bound. It does not condition on the existence of a stopping time, or assume an MGF/tail for the selected subsequence.

The subsequent CUCB-SOURCE-MODEL-PROGRESS.md records completed full primitive model specification, actual minimum-trigger/gap identification, deterministic-trigger AE bridge and impossible-case proof. The remaining list below records the boundary of this earlier increment.

## Validation and remaining obligations

`Tests/CUCBChargeCanary` checks the actual optional charge selects the under-sampled arm in the mixed p=1/p=1/2 example, no counters increment when all actions are good, and exactly n total increments occur in n bad rounds. It audits dependency assumptions of the entire new chain. This remains an analysis regression, not the contract's noisy full-performance canary.

Remaining: construct the finite source model and identify p_i as its minimum triggering probability; derive the p_i=1 almost-sure deterministic relation; turn the charged tail into the exact sufficient-sampling probability with no extra action-cardinality factor; source reward expectation identity; optimism/smoothness impossible case; refined integral Theorem 1; both polynomial Theorem 2 branches; noisy final canary; independent source/repair acceptance; shared mappings and all-ten ICLR evidence. No controlled evaluation has run, and no merge/deployment is implied.
