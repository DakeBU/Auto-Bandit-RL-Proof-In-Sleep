# CUCB Theorem 1: compiled repaired endpoint

2026-09-18. The frozen CUCB contract and all-ten-topic objective are unchanged. Theorem 1 is now compiled from the actual source-model trajectory, using the already disclosed normalized analysis-counter repair. This is not independent acceptance of the repair or completion of the combinatorial topic; both mandatory Theorem 2 branches have since compiled (see CUCB-THEOREM-TWO-PROGRESS.md), while the concrete noisy final-performance canaries remain open.

## Source and exact endpoint

The frozen primary source is Chen et al., JMLR 17(50), 2016, Algorithm 1 and Theorem 1 / Equation (2), [PDF](https://jmlr.org/papers/volume17/14-298/14-298.pdf). The local frozen PDF was rehashed as `6a29fc188cd1490c53864eb4f839e572551c171388fc27ba256a7e61424e856c`; the extracted Theorem 1 formula was compared again. The inverse-range clarification and normalized charge repair remain disclosed in CUCB-CONTRACT.md. The learner is unchanged.

`SourceModel.theorem_one_refined_regret` proves, for every integer H>=1:

    approximationRegret H <= sum_i armRefinedTerm H i
      + (1+(2+I{globalMinTrigger<1})*pi^2/6)*m*Delta_max.

Here approximationRegret is exactly H*alpha*beta*trueOpt minus the expected actual cumulative reward. Each armRefinedTerm is zero when its finite family of positive-gap actions that can trigger that arm is empty. Otherwise it is

    minBadGap_i * gapThreshold H p_i minBadGap_i
      + integral_minBadGap_i^maxBadGap_i gapThreshold H p_i x dx.

The gapThreshold is the frozen exact piecewise threshold through the proved scalar inverse. The p_i and global minimum are computed from the actual environment observation probabilities. Delta_max is the actual maximum positive action gap, zero when there are no bad actions. There is no extra action-cardinality factor and no reward support bound.

## Actual counting and integral construction

`Algorithms/CUCBUnderCount` proves monotonic actual integer counters, strict increase between distinct charge times and injection of actual charge times into their prior counters. A floor/range cardinality argument yields at most B+1 charges whose prior counter is <=B. The actual underChargeTimes and underChargeGapTail are finite subsets of the real action history. Threshold antitonicity turns their tail count at any positive source-domain x into <=ell_H(x,p_i)+1. The bad-action families and min/max gap bounds are derived, including an empty-family no-charge theorem.

`FiniteGapLayerCake` is a reusable finite-gap lemma. It proves interval integrability of the step functions and their finite count, the exact identity sum gaps = a*card + integral_a^b count{gap>=x}dx, and the envelope sum gaps <=a*ell(a)+integral_a^b ell(x)dx+b. It uses the exact interval indicator integral, so equal endpoints and the boundary points require no informal measure-zero shortcut.

`Algorithms/CUCBUnderCountIntegral` instantiates this envelope with the actual charge counter producer. It identifies the actual underSampledGap sum exactly with the sum of per-arm charged gap weights, handles empty bad-action families, and bounds the total by sum_i armRefinedTerm +m*Delta_max. No visit/count inequality is assumed.

`Algorithms/CUCBRefinedRegret` integrates the actual pathwise bound using the previously produced weight integrability, then combines it with the actual signed oracle-failure cancellation and the exact cumulative sufficient-sampling tail. This closes the full refined Theorem 1 endpoint. It also proves approximationRegret<=0 whenever every action gap is nonpositive, including H=0.

## Remaining acceptance

Theorem 2 now has the exact polynomial envelope, constants, exponents and both compiled deterministic/probabilistic branches; see CUCB-THEOREM-TWO-PROGRESS.md. The frozen obligations also require genuinely noisy multiple non-singleton feasible-action canaries, distinct rewards, nontrivial triggering and approximation-oracle cases; independent source/repair semantic review; shared mappings; and all-topic ICLR evidence under the frozen protocol. Dependency audits and joint gates do not replace these. No merge, deployment, manuscript update or controlled evaluation is implied.
