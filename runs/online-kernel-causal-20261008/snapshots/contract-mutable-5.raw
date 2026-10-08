# One causal behavioral kernel process and exact IID expected-fixed excess

Task id: `ONLINE-KERNEL-CAUSAL-20261008`
Kind: `causal-kernel-realization`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or literature-port target.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Existing Lean declaration:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- target declaration names here
```

Target file: `BanditRLProof/OnlineGuessingKernelCausal.lean`

## Proof Obligations

- [ ] Natural-language statement is mapped to Lean symbols.
- [ ] Required model assumptions are explicit.
- [ ] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [ ] Reusable theorem cards are identified before proof search.
- [ ] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [ ] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [ ] `lake build && lake build Tests` passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | project-local |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task ONLINE-KERNEL-CAUSAL-20261008 --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```


## Draft5 derived kernel targets, contextv2

Source v10 printed1/PDF13: predict a unit number before revealing the next target; squared loss under a fixed unknown IID unit law cannot beat cumulative variance. Printed3/PDF15 states why a strategy can use the past while the future is unavailable. The source does not itself state a five-part stochastic-kernel representation theorem. This package makes a specified standard-Borel behavioral randomized policy model precise and connects its actual generated process to the source IID benchmark.

Given ONE infinite family kappa_t of Markov kernels from (generated unit action history of lengtht, real observation history of lengtht) to I=[0,1], choose ONE jointly measurable sampler family f_t before any observation law or horizon. Draw one infinite tape U from product uniform volume; under rho x nu the tape is independent of the entire observation stream. The actual finite recursion starts from the empty action history and appends f_t((generated actions strictly beforet,Y_<t),U_t). No prediction kernel may be supplied with arbitrary future observations, a known mean or a horizon-specific strategy. Prove all earlier entries coincide with the SAME infinite generated process and prove nonanticipation under equality of tape coordinates<=t and observations<t.

For EVERY probability observation-stream law nu (not necessarily IID/unit), derive the actual joint law of generated history and next action as history marginal compProd kappa_t, using fresh-draw independence produced from the infinite-product law and strict recursion. Then derive condDistrib equality AE on that actual history marginal. This is not assumed input; single-step mathlib sampling alone is insufficient. Bundled ProbabilityMeasure only expresses total mass1. Real observation history is deliberately unrestricted in realization. Unit outputs are typed, globally feasible.

For the SAME family and process, under measurable coordinate IID/same-law targets AE in[0,1], prove every naturalT including0 expectedFixedRegret equals sum of expected squared prediction deviations from EY0 and is nonnegative. Population mean is analysis-only. Benchmark is minimum expected FIXED unit-comparator loss outside expectation. No pathwise/min-expectation exchange/rate/convergence/high-probability or adaptive-adversary guarantee follows from this product-law IID endpoint. Law-relative condDistrib equality does not make off-support histories unique. Classical sampler selection is not an executable distribution-free numerical sampler. Other private-state/general-filtration/completion constructions need separate precise contracts and remain required until audited. Original16/null/fullchapter/wholeGoal boundaries unchanged.

Exact5 headersv1 unchanged; contextv2 computational annotation repair retained. Targets-v2.json and DAG define all obligations. K1/K2 dependency-ready; other terminals await real proofs. No new public theorem body. Contract review required before stabilization.
