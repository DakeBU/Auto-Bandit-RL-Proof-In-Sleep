# Conversion Window: One causal behavioral kernel process and exact IID expected-fixed excess

Task id: `ONLINE-KERNEL-CAUSAL-20261008`

Source card:
Scenario card:

## Natural-Language Statement

Write the theorem, proof fragment, or paper equation in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task packet | no |
| sub-Gaussian rewards | obligation | cited result | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | theorem-card route plus local wrappers | pivot only after reviewer records a mathematical reason |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | this file | TBD | TBD | project-local | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing lemma:
- [ ] Missing regularity contract:
- [ ] Mathlib candidate to upstream:
- [ ] Missing cited-result entry:


## Draft5 derived kernel targets, contextv2

Source v10 printed1/PDF13: predict a unit number before revealing the next target; squared loss under a fixed unknown IID unit law cannot beat cumulative variance. Printed3/PDF15 states why a strategy can use the past while the future is unavailable. The source does not itself state a five-part stochastic-kernel representation theorem. This package makes a specified standard-Borel behavioral randomized policy model precise and connects its actual generated process to the source IID benchmark.

Given ONE infinite family kappa_t of Markov kernels from (generated unit action history of lengtht, real observation history of lengtht) to I=[0,1], choose ONE jointly measurable sampler family f_t before any observation law or horizon. Draw one infinite tape U from product uniform volume; under rho x nu the tape is independent of the entire observation stream. The actual finite recursion starts from the empty action history and appends f_t((generated actions strictly beforet,Y_<t),U_t). No prediction kernel may be supplied with arbitrary future observations, a known mean or a horizon-specific strategy. Prove all earlier entries coincide with the SAME infinite generated process and prove nonanticipation under equality of tape coordinates<=t and observations<t.

For EVERY probability observation-stream law nu (not necessarily IID/unit), derive the actual joint law of generated history and next action as history marginal compProd kappa_t, using fresh-draw independence produced from the infinite-product law and strict recursion. Then derive condDistrib equality AE on that actual history marginal. This is not assumed input; single-step mathlib sampling alone is insufficient. Bundled ProbabilityMeasure only expresses total mass1. Real observation history is deliberately unrestricted in realization. Unit outputs are typed, globally feasible.

For the SAME family and process, under measurable coordinate IID/same-law targets AE in[0,1], prove every naturalT including0 expectedFixedRegret equals sum of expected squared prediction deviations from EY0 and is nonnegative. Population mean is analysis-only. Benchmark is minimum expected FIXED unit-comparator loss outside expectation. No pathwise/min-expectation exchange/rate/convergence/high-probability or adaptive-adversary guarantee follows from this product-law IID endpoint. Law-relative condDistrib equality does not make off-support histories unique. Classical sampler selection is not an executable distribution-free numerical sampler. Other private-state/general-filtration/completion constructions need separate precise contracts and remain required until audited. Original16/null/fullchapter/wholeGoal boundaries unchanged.

Exact5 headersv1 unchanged; contextv2 computational annotation repair retained. Targets-v2.json and DAG define all obligations. K1/K2 dependency-ready; other terminals await real proofs. No new public theorem body. Contract review required before stabilization.
