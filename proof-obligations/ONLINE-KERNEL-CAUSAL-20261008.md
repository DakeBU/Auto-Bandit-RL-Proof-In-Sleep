# Proof Obligations: One causal behavioral kernel process and exact IID expected-fixed excess

Task id: `ONLINE-KERNEL-CAUSAL-20261008`

Source card:
Scenario card:

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ONLINE-KERNEL-CAUSAL-20261008-ROOT` | root theorem or definition | conversion window | TBD | TBD | TBD | TBD | project-local | upper | TBD | `lake build && lake build Tests` | planned |

## Failure Classification

Use exactly one:

- source translation gap;
- local Lean lemma gap;
- theorem-card dependency;
- external cited result;
- semantic interface gap;
- missing regularity contract;
- likely false statement or counterexample;
- invalid route;
- stale dynamic leaf;
- connected blocker.

## Reviewer Notes

- Keep failed attempts in `proof-attempts/ONLINE-KERNEL-CAUSAL-20261008/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.


## Draft5 derived kernel targets, contextv2

Source v10 printed1/PDF13: predict a unit number before revealing the next target; squared loss under a fixed unknown IID unit law cannot beat cumulative variance. Printed3/PDF15 states why a strategy can use the past while the future is unavailable. The source does not itself state a five-part stochastic-kernel representation theorem. This package makes a specified standard-Borel behavioral randomized policy model precise and connects its actual generated process to the source IID benchmark.

Given ONE infinite family kappa_t of Markov kernels from (generated unit action history of lengtht, real observation history of lengtht) to I=[0,1], choose ONE jointly measurable sampler family f_t before any observation law or horizon. Draw one infinite tape U from product uniform volume; under rho x nu the tape is independent of the entire observation stream. The actual finite recursion starts from the empty action history and appends f_t((generated actions strictly beforet,Y_<t),U_t). No prediction kernel may be supplied with arbitrary future observations, a known mean or a horizon-specific strategy. Prove all earlier entries coincide with the SAME infinite generated process and prove nonanticipation under equality of tape coordinates<=t and observations<t.

For EVERY probability observation-stream law nu (not necessarily IID/unit), derive the actual joint law of generated history and next action as history marginal compProd kappa_t, using fresh-draw independence produced from the infinite-product law and strict recursion. Then derive condDistrib equality AE on that actual history marginal. This is not assumed input; single-step mathlib sampling alone is insufficient. Bundled ProbabilityMeasure only expresses total mass1. Real observation history is deliberately unrestricted in realization. Unit outputs are typed, globally feasible.

For the SAME family and process, under measurable coordinate IID/same-law targets AE in[0,1], prove every naturalT including0 expectedFixedRegret equals sum of expected squared prediction deviations from EY0 and is nonnegative. Population mean is analysis-only. Benchmark is minimum expected FIXED unit-comparator loss outside expectation. No pathwise/min-expectation exchange/rate/convergence/high-probability or adaptive-adversary guarantee follows from this product-law IID endpoint. Law-relative condDistrib equality does not make off-support histories unique. Classical sampler selection is not an executable distribution-free numerical sampler. Other private-state/general-filtration/completion constructions need separate precise contracts and remain required until audited. Original16/null/fullchapter/wholeGoal boundaries unchanged.

Exact5 headersv1 unchanged; contextv2 computational annotation repair retained. Targets-v2.json and DAG define all obligations. K1/K2 dependency-ready; other terminals await real proofs. No new public theorem body. Contract review required before stabilization.


## Five derived behavioral-kernel obligations accepted; draft delivery pending

Task: `ONLINE-KERNEL-CAUSAL-20261008`

Five derived behavioral-kernel proofs only: one sampler before all laws/horizons, actual finite causal recursion and same-process prefix consistency, derived joint law, AE conditional law and every-horizon IID expected-fixed excess/nonnegativity. Original16 Chapter1 source objects/null unknown proof total; arbitrary-protocol/filtration/private-state reduction and action-dependent adaptive environments are not covered. Other required source/information constructions, remaining Chapter1/2, unenumerated Chapters3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged. Five focused public bodies and13canary proofs;57standard-only axiom records,52selected nodes3106coalesced TYPE_VALUEedges22requireddirectVALUEpairs. Combined root9102/Tests9264/fullharness472tests7skips; both contributor bases and ownshadow passed. Applicable clean local site preserves10942complete old records plus17module nodes:5terminals,8context definitions,4private helpers.12original pixels inspected by formalizer/distinctFINAL. CONTRACT104/retrieval16/BODY350/EOF22/registry-repair13/FINAL separately bound; all failure logs retained. Reused distinct automated actors; no absolute-blind/human/external/runtime attestation. Native/post-native/delivery separately recorded.
