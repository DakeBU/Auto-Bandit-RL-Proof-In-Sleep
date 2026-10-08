# Proof Obligations: Actual FTL best regret and fixed-comparator ordinary-limit criterion

Task id: `ONLINE-FTL-LIMIT-20261009`

Source card:
Scenario card:

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ONLINE-FTL-LIMIT-20261009-ROOT` | root theorem or definition | conversion window | TBD | TBD | TBD | TBD | project-local | upper | TBD | `lake build && lake build Tests` | planned |

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

- Keep failed attempts in `proof-attempts/ONLINE-FTL-LIMIT-20261009/`.
- Do not promote simulator checks, prose sketches, or theorem cards to certified memory.
- If an LML theorem is used, cite the upstream declaration and record whether it is imported, ported, or only a theorem card.
- Do not frequently change proof strategy; record the mathematical reason before pivoting.
- Mark general leaf lemmas as Mathlib candidates when they should become reusable upstream infrastructure.


## Own draft five derived FTL limit obligations

Orabona v10 printed2/PDF14 first defines signed regret against the minimum fixed comparator in[0,1], then defines comparator-wise regret. The no-regret sentence displays an ordinary limit <=0. Printed4/PDF16 Theorem1.3 gives actual strict-past mean predictions with initial1/2 and best-fixed regret <=4+4lnT; printed6/PDF18 concludes sublinear growth. Existing upper-epsilon NoRegret and literal finite-real-limit LimitNoRegret remain distinct, existing headers/bodies untouched. The previously accepted abstract signed-unbounded-affine obstruction is not a bounded-square-loss FTL counterexample.

Freeze five DERIVED hinge obligations: F1 actual meanPredict cumulative loss minus empirical-mean comparator loss is nonnegative for EVERY real observation stream and every naturalT including0, by prefix minimization and the actual strict-past prediction. F2 exact fixed-comparator decomposition for all realy,u andT including0: actual regret(u,T)=actual regret(empMean_T,T)-T*(u-empMean_T)^2. F3 for one infinite unit observation stream, the ACTUAL interval-minimum signed best regret divided byT tends to0, using F1 plus source4log upper; no regret lower/upper oracle is input. F4 for the SAME actual FTL and every real fixedu,a, ordinary normalized regret tends toa IFF (u-empMean_T)^2 tends to-a. F5 when the stream empirical mean tends tom, every real comparator limit is-(u-m)^2; restricting comparators to[0,1] produces literal LimitNoRegret. The extra empirical-mean convergence is an explicit sufficient condition; do not attribute it to the arbitrary-stream source theorem.

No probability/expectation/high-probability/minE exchange/pathwise-best-regret nonnegativity for arbitrary algorithms. F1 uses a produced hindsight empirical mean, not a caller minimizer/stability premise. F1/F2 unbounded-stream statements do not claim valid unit game outputs for unbounded observations. F3/F4/F5 retain all-time unit observations. T0 normalization uses Lean total division by0=0 and is irrelevant to atTop; finite F2 includesT0 by empty sums. No unconditional ordinary limit for every arbitrary bounded stream is claimed. A concrete bounded oscillating-mean same-FTL counterexample and exact all-comparator converse remain separate required source-semantics reconciliation work, not silently excluded or declared false here. This package does not complete C1 or the whole Goal; original source obligations and subsequent chapters remain.

Exact frozen headers/DAG: docs/contracts/online-ftl-limit-v1. Contract review pending,0 production bodies compiled;5 derived obligations open.


## Five derived actual FTL limit obligations accepted; draft delivery pending

Five derived same-process FTL hinges: all-real empty-horizon loss-gap/decomposition; unit-stream best average zero and signed fixed-limit equivalence; explicit empirical-mean convergence produces literal LimitNoRegret. Concrete bounded oscillating actual-FTL obstruction and exact all-comparator converse remain REQUIRED. Original16Chapter1 source objects/null unknown proof total, other C1/C2, unenumerated C3-16 and necessary appendices remain REQUIRED; whole Goal ACTIVE, main/live unchanged. Twelve actual alternating-binary canaries instantiate all five terminals; proved mean/count and fixed-zero limit -1/4. Five whole-type VALUE witnesses,29 standard-only axiom outputs,24 selected nodes2676 coalesced TYPE_VALUEedges16 required directVALUEpairs and17 native fences. Actual root9103/Tests9266/fullharness-v2 472tests7skips; both contributor bases and ownshadow passed. First fullharness-v1 untracked-Lean rejection1 retained and staging-only repair0. F1 fence/render/capture-prerequisite failures retained. Applicable clean local site preserves10959complete registry records plus exactly5production nodes; twelve original images inspected by formalizer/distinctFINAL. Distinct reused automated roles; no absolute-blind/human/external/runtime-model attestation. Native/post-native/draft delivery separately recorded.
