# Recent heavy-tail source audit: Park et al., AISTATS 2026

Source: *Boltzmann Exploration for Heavy-Tailed Bandits*, Park, Cho and Lee,
PMLR300 (2026). Frozen PDF SHA256:
`c192f3345a20227243a822e8fc60d2fd0b8f71d44d5f5f3cc7e35f267d33d102`.

Independent reading covered the model, Algorithm1, main statements and the full
relevant proof chain in Appendices B-G (PDF pp13-35), including the IPW theorem.
Consequential formulas were checked in rendered pages. Experiments, code,
AppendixH, external cited proofs and later corrections were not audited.
A full reading is not a successful validation of every printed result.

Assumption1 is a raw absolute moment bound on the reward distribution D_i.
The bias proof truncates actual rewards and uses that raw moment; a bound on
centered noise alone, with arbitrary mean shifts, does not supply the stated
contract. The algorithm also knows T,p,nu, uses a common truncation threshold
and randomized Boltzmann selection. It is a distinct source line, not a direct
replacement for the BCL sample-ordinal estimator or unknown-parameter adaptation.

The independent report flags these unresolved proof steps:

- AppendixD Eq133 changes the truncation threshold of all earlier observations
  when s changes. Fixed-s independence does not by itself make this triangular
  array's exponential process a supermartingale for a maximal inequality.
- AppendixG.1 Eq285 substitutes inverse marginal success probability for an
  expectation of inverse history-conditional success probability. Jensen's
  inequality runs in the other direction; rare histories with small propensity
  need separate control.
- AppendixC Eq108-109 loses a T power: dividing
  T^(1-1/p)*(T*nu/(K*d)^p)^(1/p) by T leaves nu^(1/p)/(K*d), without T decay.
  Finite Monte Carlo propensity estimates may also be zero; eventwise lower
  bounds cannot silently be used in unconditional expectations.
- Gap-log signs, parameter-dependent constant absorption and stated horizon
  conditions require adjudication. Exact softmax positivity alone is not a
  uniform history-independent lower bound on propensity.

These are bounded proof-audit findings, not a blanket refutation of the intended
regret rates, an author-issued erratum, or Lean-certified impossibility results.
They prevent importing the printed theorem unqualified. The complete report
retains exact assumptions, equation anchors and additional limitations.

Private report: `E:/ABRL/maintenance/extended-topics-20260919-claude/review-20260919/park26-full-audit.md`.
Report SHA256: `e7ebf39d272c30615aa7c3373f51214ee3088eb8af8adc2c0c0082e4e3045eb7`.
