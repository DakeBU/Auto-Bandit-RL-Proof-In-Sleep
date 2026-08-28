# Proof obligations: prospective SGB phase-transition follow-on

Task id: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

| Obligation | Evidence target | Status | Boundary |
| --- | --- | --- | --- |
| `SGB-C1-TRIVIAL-REGRET` | pathwise and integral `Delta*T` upper bound | compiled | `twoArmSampledPseudoRegret_le_gap_mul_horizon`; actual sampled actions |
| `SGB-C1-MARGIN` | `2*eta*C_eta <= Delta` implies Theorem-1 margin and `1/eta` constant | compiled | `sourceTheoremOne_margin_of_two_mul_eta_sourceC_le`; `sourceTheoremOne_constant_le_inv_eta` |
| `SGB-C1-GAP-FREE` | exact piecewise Corollary-1 finite bound | compiled | `twoArmFixedIIDDirac_corollaryOne_piecewise`; fixed IID, `T >= 2`, horizon-indexed eta |
| `SGB-C1-RATE` | explicit absolute-constant `sqrt(T*log T)` bound | compiled | `twoArmFixedIIDDirac_corollaryOne`; direct Theorem-1 companion |
| `SGB-T2-NTH-PULL` | stopping-time and chronological-to-pull-index bridge | compiled | `WithTop Nat` missing-pull value; finite exact count/action specification; measurable stopped reward and post-pull probability; no IID claim |
| `SGB-T2-LATENT-PRODUCT` | finite product law for fixed-arm latent coordinates and finite nth-pull readout | compiled | `armStreamMeasure_map_fixedArmFinitePrefix_eq_pi`; latent-coupling lift; `twoArmNthOptimalPullReward_eq_latentCoordinate_ae`; no totalized or occurrence-conditioned stopped-reward IID claim |
| `SGB-T2-PREFIX-MIXTURE` | finite deferred-decisions factorization of the latent stream box and generated visible prefix | compiled | exact finite stream-box product law, stream-prefix kernel-law locality, Markov visible-prefix kernel, and joint stream-box/visible-prefix mixture; no visible-marginal/native-prefix identification |
| `SGB-T2-ACTION-READOUT` | next-action factorization and pathwise selected-coordinate support in the latent coupling | compiled | `latentArmStreamTrajectoryMeasure_map_visiblePrefix_nextAction_eq_compProd`; `latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae`; neither theorem is selected-reward freshness |
| `SGB-T2-BRANCH-LOCALITY` | branchwise factor-through-complement producer for the selected latent coordinate | compiled | two generic safe-fiber measure bridges plus the count-cap base/successor induction prove `latentArmStreamVisiblePrefixNextActionBranchLocality`; `latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod` gives the unconditional exact branchwise product law |
| `SGB-T2-NATIVE-TRAJECTORY` | forgetting the latent stream recovers the native fixed-IID SGB trajectory law | blocked | first remaining core technical blockers are aggregation into selected-reward freshness, visible-marginal/native-prefix identification, and trajectory uniqueness; branch locality itself is compiled |
| `SGB-T2-SELECTED-IID` | target-faithful transfer of the source pull-ordered reward blocks to the native phase event | partial | latent product/readout, finite-prefix mixture, action/readout, count-capped branch locality, and the exact branchwise coordinate product law compile; aggregate selected-reward freshness, native trajectory equality, and phase-event transport do not |
| `SGB-T2-FUTURE-CYLINDER` | conditional probability of no later optimal-arm pull after the random nth-pull prefix | blocked | one-step action kernels at fixed histories do not by themselves supply a stopped-prefix future law |
| `SGB-T2-STARVATION` | Appendix-C Step-1 event-to-regret lower bound | partial | measurable fixed-cutoff event and generated-law `Delta*(T-n)*P(event)` consumer compile; it is not yet composed with the separately compiled nth-pull bridge, and conditional probability `>= 1/2` remains unproved |
| `SGB-T2-PHASE-PROBABILITY` | `S0/S1` probability via Rademacher/binomial/ballot route | blocked | exact finite constants and path event |
| `SGB-T2-POLYLOG-OMEGA` | frozen K=2 Theorem-2 terminal | blocked | depends on all preceding producers |
| `SGB-PHASE-CANARY` | exact imports, checks, and representative axiom prints | compiled | companion, deterministic-consumer, nth-pull, latent-reward, finite-prefix-mixture, safe-fiber measure bridge, count-cap induction, branch-locality producer, and unconditional branch-product canaries use baseline axioms only |

## Source and scenario

- Source card:
  `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- Proof branch: two-arm fixed-IID generated-process phase transition.
- Mathlib routes: probability kernels and conditional laws, stopping times,
  infinite products, binomial PMFs, finite sums, logarithm/exponential/square
  root order algebra, and Stirling bounds.

## Failure policy

No row may be promoted from a plan, theorem card, scalar proxy, or supplied
IID selected-reward assumption.  If the adaptive nth-pull producer or ballot
route does not compile, record the exact boundary and retain Theorem 2 as
blocked.  Corollary 1 has a separate evidence row and cannot substitute for
the core target.
