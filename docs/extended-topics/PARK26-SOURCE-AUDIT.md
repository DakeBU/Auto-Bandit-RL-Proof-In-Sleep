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

The initial independent report flagged the following proof steps. Their final bounded adjudication and separately reviewed IPW repair are recorded below:

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


## Final bounded adjudication (2026-09-20)

The [regret proof adjudication](PARK26-REGRET-ADJUDICATION.md) supplies an exact
counterexample to the asserted Eq133 prefix supermartingale: under the source
cutoffs, iid rewards in {-1,0}, K=2,T=8,nu=1/2, the conditional increment at
3-to-4 exceeds one on an event of probability1/8. Eq285's general probability
inference also fails by an explicit positive-propensity example. This second
example is not asserted to be an actual H-BE trajectory. The ordinary-log gap
bound requires a finite-time regime or changed expression. The main regret
rate is neither disproved nor repaired by these findings.

The [IPW derivation](PARK26-IPW-REPAIR.md) separates the positive-probability
zero denominator, support/target mismatch and lost T exponent. AppendixC Eq66
uses a target that need not equal the advertised uniform-policy value without
full actionwise support. The repaired theorem explicitly assumes that support,
a known floor d and independent conditional replays, and uses max(d/2,phat).
It proves a complete unconditional L1 risk bound through a self-contained
scalar martingale p-moment argument. Its optional conditional-risk statement
names the joint event and the horizon-dependent Monte Carlo requirement.

Independent mathematical and source reviews accept these bounded conclusions
with explicit deltas. Receipt: `runs/extended-topics-20260919/park-adjudication-audit.json`.
The source-selection decision is to retain H-BE as distinct recent prior art
and decline unqualified import of the printed full regret results. Its rejected
proof chain and unread external dependencies are not dependencies of the BCL
representative endpoint or the new IPW repair. This closes the named Park
source-disposition issue; it does not validate the entire paper, create a Lean
result, or complete the heavy-tail topic.
