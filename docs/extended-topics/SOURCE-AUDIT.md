# Research selection and source audit, 2026-09-17

This records source screening, not an exhaustive literature review or acceptance
of all the directory entries. Original topic owner remains
`website/content/banditrlwiki.json`; all ten topics were source-audit-pending at
the frozen base. Local source PDFs and text are retained privately under
`E:/ABRL/maintenance/extended-topics-20260917/sources` with hashes in the receipt.

## Primary case and an actual diagnostic

Bubeck, Cesa-Bianchi, Lugosi (2013), DOI 10.1109/TIT.2013.2277869,
[author-hosted published PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/01/BCL13.pdf),
and [preprint v1](https://arxiv.org/pdf/1209.1727v1).
The published pp. 7712--7713 were visually checked because PDF extraction drops
mathematical glyphs. Figure 1 uses delta=t^-2, while the second proof step prints
`2 sum_{s=1}^t 1/s^4 <= 2/t^3`. This inequality is false already for t=2;
replacing s by t still requires delta=t^-4, not t^-2. Moreover solving
`2*v^(1/(1+epsilon))*(c log(t^2)/s)^(epsilon/(1+epsilon)) <= Delta`
requires the factor `2^((1+epsilon)/epsilon)` absent from the printed threshold.
This is a diagnosis of the displayed proof, NOT a refutation of the rate or a
claim that no alternative argument establishes the published theorem.

Repair branch, explicitly an adaptation: use delta_t=t^-4 for t>=2. With a valid
one-sided estimator radius r(s,t)=v^(1/p)*(4c log t/s)^((p-1)/p), choose
L_i=ceil(4c*2^(p/(p-1))*v^(1/(p-1))*log(max(T,2))/Delta_i^(p/(p-1)))+1.
Then s>=L_i implies 2r(s,t)<Delta_i. The two fixed-prefix tail unions have
probability <=2(t-1)t^-4 <=2t^-3. Initialization and small counts contribute
L_i, and bad-event selections contribute at most sum_{t>=2}2t^-3 <=2.
Thus E R_T <= sum_{Delta_i>0} Delta_i*(L_i+2), once the estimator concentration
and causal sampling obligations are proved. This formula is a paper derivation,
not yet a Lean-certified endpoint; it deliberately does not preserve faulty
displayed constants. Bernstein's bounded-increment term also needs care because
centering a signed [-B,B] variable gives a 2B bound.

## Status clarification, 2026-09-19

The preceding generic one-sided repair derivation is retained as historical
analysis, not the current compiled contract. The actual conservative endpoint
`HeavyTail.robust_expected_regret` was compiled at
`280378670ca4647440f795aae1905149eff0063b` (see the regret validation receipt).
It uses radius 8a and two-sided confidence, with total selection-failure bound
4t/max(t,2)^4 and a proved finite tail sum at most 2; the corresponding threshold
contains 16 raised to p/(p-1). See `DERIVATION.md` for the actual formula.
The generic paragraph's factor 2 must not be substituted for this compiled
chain's factor 4. Source adjudication and independent semantic acceptance
remain distinct obligations. The triage table below records the original base;
current execution follows `ALL-TOPICS-PROGRAM.md` in strict topic order.

## Recent candidates: inspect assumptions before selecting endpoints

| Source | Distinct question and audited part | Decision |
|---|---|---|
| [Genalti et al., COLT 2024](https://proceedings.mlr.press/v247/genalti24a.html) | Raw (1+epsilon)-moments; unknown epsilon/u. Section 3 negative results rule out cost-free general adaptation; AdaR-UCB adds truncated non-positivity on an optimal arm. | Keep as boundary and later target. Do not label known-parameter work adaptive. Full theorem/proof audit still required before formalization. |
| [Park et al., AISTATS 2026](https://proceedings.mlr.press/v300/park26a.html) | H-BE randomized policy, horizon-dependent threshold, explicit propensities. Assumption 1 writes a raw p-moment of D_i despite nearby noise language; resolve what D_i denotes before using a centered-noise interpretation. | Defer. Existing SGB odds lemmas do not establish this distinct algorithm's regret theorem. |
| [Yu et al., UAI 2025](https://proceedings.mlr.press/v286/yu25b.html) | GLM, conditional finite variance, pseudo-Huber regression, corruption budget. | Follow-on variance-aware case, not a general infinite-variance theorem. Needs vector confidence producer. |
| [Tani et al., UAI 2026](https://proceedings.mlr.press/v337/tani26a.html) | Assumption 3.1 is conditional mean-zero noise and conditional (1+epsilon)-moment; Assumption 3.2 bounds features/parameter. Corruption occurs after reward/action and may depend on both. | Strong future transfer challenge for OFUL/OMD interfaces, but IID scalar clipping does not prove Theorem 4.5. |

All four PDFs were retrieved; this table is a targeted model/theorem screening.
They are not marked full-proof-audited. No recent-source endpoint is frozen from
its abstract. The classical primary case has the clearest source and strongest
direct relationship to existing arm-prefix/count infrastructure.

## Whole-directory triage

| Topic | Real connection at base | Scientific endpoint / missing producer | Priority |
|---|---|---|---|
| heavy-tailed | UCB prefix, argmax, count, Real regret | moment -> estimator -> actual robust policy -> expected regret | primary |
| corruption-tolerant | Tsallis corruption interfaces; transformed prefix | clipped-mean stability under L1 corruption; no generic robust regret claim | reserved narrow transfer |
| variance-aware | variance/Chebyshev, fixed-tilt MGF | variance-sensitive robust confidence, not sub-Gaussian relabeling | next after scalar producer |
| combinatorial | finite action, importance weighting | semi-bandit estimator and oracle contract | later; feedback must be fixed |
| thompson-bayesian | posterior and Bayes regret modules | specify likelihood/prior under heavy tails | later; posterior producer missing |
| multi-agent | finite arm bookkeeping | communication/collision observation law | defer; no shared model yet |
| lipschitz | finite discretizations at most | metric covering/zooming dimension with approximation regret | defer; infinite-action producer |
| causal | history kernels are not causal interventions | identification and intervention law | defer; source/model unresolved |
| constrained | stopping/budget bookkeeping | feasibility and comparator definition | defer; distinguish safety from resource budget |
| matrix | linear algebra/OFUL is only adjacent | low-rank observation/recovery and exploration guarantee | defer; model not selected |

These are mature research families with continuing work, not ten newly emerged
topics. Unselected topics retain pending source audits.
