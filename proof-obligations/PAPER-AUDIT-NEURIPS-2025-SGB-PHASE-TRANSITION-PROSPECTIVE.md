# Proof obligations: prospective SGB phase-transition follow-on

Task id: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

| Obligation | Evidence target | Status | Boundary |
| --- | --- | --- | --- |
| `SGB-C1-TRIVIAL-REGRET` | pathwise and integral `Delta*T` upper bound | compiled | `twoArmSampledPseudoRegret_le_gap_mul_horizon`; actual sampled actions |
| `SGB-C1-MARGIN` | `2*eta*C_eta <= Delta` implies Theorem-1 margin and `1/eta` constant | compiled | `sourceTheoremOne_margin_of_two_mul_eta_sourceC_le`; `sourceTheoremOne_constant_le_inv_eta` |
| `SGB-C1-GAP-FREE` | exact piecewise Corollary-1 finite bound | compiled | `twoArmFixedIIDDirac_corollaryOne_piecewise`; fixed IID, `T >= 2`, horizon-indexed eta |
| `SGB-C1-RATE` | explicit absolute-constant `sqrt(T*log T)` bound | compiled | `twoArmFixedIIDDirac_corollaryOne`; direct Theorem-1 companion |
| `SGB-T2-NTH-PULL` | stopping-time and chronological-to-pull-index bridge | not started | no totalized missing pull |
| `SGB-T2-SELECTED-IID` | finite joint law of rewards at adaptive arm-0 pull times | blocked | first core technical blocker |
| `SGB-T2-STARVATION` | Appendix-C Step-1 event-to-regret lower bound | partial | measurable fixed-cutoff event and generated-law `Delta*(T-n)*P(event)` consumer compile; nth-pull identification and conditional probability `>= 1/2` do not |
| `SGB-T2-PHASE-PROBABILITY` | `S0/S1` probability via Rademacher/binomial/ballot route | blocked | exact finite constants and path event |
| `SGB-T2-POLYLOG-OMEGA` | frozen K=2 Theorem-2 terminal | blocked | depends on all preceding producers |
| `SGB-PHASE-CANARY` | exact imports, checks, and representative axiom prints | compiled | both companion and deterministic-consumer canaries use baseline axioms only |

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
