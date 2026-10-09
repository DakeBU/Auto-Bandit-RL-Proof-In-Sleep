# Conversion Window: Actual unbounded OSD failure

Task id: `ONLINE-CH2-UNBOUNDED-OSD-20261010`
Source: frozen Orabona v10 arXiv1912.13213,2026-06-21,SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17; Theorem5.4 printed52-53/PDF64-65, required Chapter2 printed14/PDF26 forward dependency.

## Natural-Language Statement

For every alpha in(0,1) and natural horizon T with T>=2/((1-alpha)phi(alpha)), actual unprojected OSD initialized0 with source eta_t=t^(-alpha) suffers regret at comparator0 at least phi(alpha)T^(2-alpha)/2 on some convex1-Lipschitz loss sequence. The witness is first ceil(T/2) losses -x and then floor(T/2) losses+x; in positive dimension use a unit vector. Retain the printed strict phi range(0,1-ln2) and limit at1 equal1-ln2>=0.3. No supplied desired regret bound, iterate identity, phi positivity, attainment assumption or lower-bound consumer replaces this production chain.

## Lean Mapping

| Source object | Actual shared/new Lean object | Index / role |
| --- | --- | --- |
| R^d, d>=1 | finite-dimensional real inner-product E; Nontrivial E for final existence | Scalar and unit-vector helpers separate |
| V=R^d | OnlineHuber.fullSpace, shared Domain/projection | Existing full-space projection identity reused |
| eta_t=t^-alpha | powerSteps alpha i=((i+1):R)^(-alpha) | Source round1 maps Lean0 |
| current subgradient | actual OnlineSubgradientDescent.currentSubgradient | Affine full singleton forces actual chosen vector |
| x_t | actual shared iterate at i=t-1 | Initial0/current action before loss |
| loss_t | switchLoss T v i, coerced to EReal in actual OSD | Losses real finite everywhere; source convex/Lipschitz facts proved |
| ceil(T/2),floor(T/2) | (T+1)/2,T/2 natural division | Exact odd/even count and split retained |
| Regret_T(0) | shared OnlineSubgradientDescent.regret fullSpace powerSteps coercedloss 0 0 T | Same actual recursion; no alternate algorithm |
| phi(alpha) | exact new phi formula | Denominators1-alpha/2-alpha; strict open alpha interval |

## Assumption Ledger

Full endpoint: finite-dimensional real E, Nontrivial E, 0<alpha<1, natural T satisfying exact real threshold. Convexity and LipschitzWith1 of witness losses produced, not assumed. CompleteSpace follows from finite dimension. Nontrivial removes the impossible zero-dimensional positive lower bound; pinned proof assumes d1 and embeds for d>=2. All losses finite globally; coercion/toReal needs no defaults. Step/iterate affine helpers need no eta positivity or alpha restriction. Power positivity holds for any real alpha because every played base i+1>0. Identity permits T0, though the source failure endpoint never does. No bounded domain, comparator distance oracle, random process, future-aware algorithm, computable/measurable selector or uniform guarantee over all algorithms is asserted.

## Local API and Proof Route

Actual declaration retrieval v1 failed on three namespace names; v2 actual0 verifies corrected global strictConcaveOn_log_Ioi/integral_rpow and Real.hasStrictDerivAt_const_rpow. Shared affine_subdifferential/fullSpace/project_fullSpace/currentSubgradient/step/iterate/regret are retrieved with actual complete scopes. No external library/toolchain upgrade. One lower route from singleton selection to actual step/unroll, signed finite sum identity, sum-integral bounds and exact threshold; then unit-vector lift and source existential witness. Phi range/limit required as parallel analytic dependencies, not assumptions.

## Proof DAG and Conversion

See dependency-DAG-draft-v1.json and eleven exact headers/scopes in headers-draft-v1.json, plus four complete prospective definitions. Type probe v1 failed only because the zero-binder phi_limit generated `fun =>`; version2 fixes the type-probe syntax and leaves every mathematical header/definition unchanged. It elaborates eleven Prop types, not eleven theorem proofs. Distinct neutral decoder and anti-anchored source review precede stabilization/lowering. Own task/session/trials/journal only; global SGB/frontier/registry remain unchanged.

## Gaps and Acceptance Boundary

All eleven draft terminals open; no theorem body lowered. Required source lower bound, phi range/limit, same-policy public canaries, proof VALUE dependencies, axiom/frozen/body review, root/Tests/full harness and source-qualified shared registry/reader/site/pixel/native/delivery gates remain required. A first helper does not close the lower bound. All8Chapter2forward containers remain required/open pending dedicated reconciliation. Chapter2partial/null, Chapters3-16unenumerated/null, persistent Goal ACTIVE. No Chapter5whole, main/merged/live/deployment/retirement claim.
