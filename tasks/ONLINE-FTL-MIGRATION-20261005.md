# Actual causal FTL source migration

Source Orabona arXiv1912.13213v10, frozen21June2026 SHAcef4edfa...a1b17. Example2.10 printed12/PDF24:V=[-1,1], losses ell_t(x)=z_t*x. z1=-1/2; later even source rounds+1, odd source rounds-1. First prediction arbitrary feasible x1; later FTL predictions+1 on even source rounds and-1 on odd source rounds. Regret against comparator0 exactly T-1-x1/2 >= T-3/2 for T>=1.

Audit retained actual prefix statistic recursively, not an assumed stability/regret bound. Lean0 is source round1. linearFTLPredict uses exactly t past coefficients, takes feasible x0 at0 and minimizes the past linear-loss sum by the sign of prefixCoefficient; tie rule at zero chooses-1 for positive indices. The failure stream has no later zero prefix, so later source predictions do not depend on that tie rule. AtT0 all losses/prefix sums are zero; the source endpoint still deliberately requiresT>=1. Historical minimization helper has no feasible-x0 premise because at0 both sums are0; algorithm feasibility and source endpoint separately require x0 in[-1,1]. Coefficients are arbitrary real in generic helpers; only the failure witness uses specified values. Comparator0 is the cited fixed feasible comparator, not an asserted best hindsight comparator. This is a deterministic failure of this FTL family, not an all-algorithms lower bound or stochastic theorem. Full future coefficient functions are mathematical input representations; actual recursion and strict-prefix identity establish causality.

Mathematical objects:scalar real actions/coefficient losses, finite horizon, closed interval. Quantifier order:fix arbitrary coefficient sequence/initial action, prove outputs for everyt; fix specified witness and every feasibleinitial, everyT>=1. Assumptions:membership only where needed; no probability/integrability/gradient/compactness oracle premise. Conclusion:exact loss/regret identity AND uniform linear lower bound. Constants/index:T-1-x0/2, worst feasiblex0<=1 givesT-3/2; Leanodd positiveindex is sourceeven. Information:output before current coefficient, past prefix only. Boundary:no convergence/no universal adversarial lower bound; original three definitions/seven theorem bodies retained, existing two nondegenerate public canaries reused. This is independent migration of one historical production path, not seven new proofs or wholeChapter2 acceptance. Existing prior same-model semantic judgment stays historical, never relabelled independent.

| Target | Dependencies | State |
|---|---|---|
|prefixCoefficient_eq_sum||retained compiled body; fresh independent review pending|
|linearFTLPredict_prefix|prefixCoefficient_eq_sum|retained compiled body; fresh independent review pending|
|linearFTLPredict_mem||retained compiled body; fresh independent review pending|
|linearFTLPredict_minimizes|prefixCoefficient_eq_sum|retained compiled body; fresh independent review pending|
|failure_prefixCoefficient||retained compiled body; fresh independent review pending|
|failure_prediction|failure_prefixCoefficient|retained compiled body; fresh independent review pending|
|example_2_10|failure_prediction|retained compiled body; fresh independent review pending|

Allowed edits after reviewed stabilization:source-qualified comments in OnlineFTLFailure only, task-local contracts/evidence and scoped shared Book/manifest integration. No old header/definition/body rewrite; any semantic target change needs a new version/review. Same Lean/Lake project/registry; no per-book project/globalSGB overwrite. Whole Goal remains active; Chapter2 and other20main migration paths remain mandatory after this single-file scope is accepted.
