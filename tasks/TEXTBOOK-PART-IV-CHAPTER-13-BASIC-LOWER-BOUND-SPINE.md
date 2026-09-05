# Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Close the source-faithful main-text contract for Chapter 13, *Lower Bounds:
Basic Ideas*.  The previously compiled slice exposes minimax/worst-case
expected-regret semantics, the least-explored alternative-arm averaging step,
and the conditional algebraic two-environment reduction behind equations
(13.2)--(13.3); the separately compiled Chapter 15 construction supplies the
caller-free Gaussian endpoint.  The expanded contract also accounts for the
minimax-optimality definition, the Gaussian two-point testing discussion and
Eq. (13.1), and the broader 1-subgaussian near-minimax consequence stated in
the main prose.

The maintained public names remain **BanditRLlib** and
*ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for
Bandit and Reinforcement Learning Theory*.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- DOI: <https://doi.org/10.1017/9781108571401>.
- Formal author version: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 13, CUP print pp. 155--159, author-online
  pp. 180--185, physical PDF pp. 189--194.  Theorem 13.1 is CUP p. 155 /
  author-online p. 180 / physical PDF p. 189; Section 13.1 starts at CUP
  p. 155 / author-online pp. 181--182 / physical PDF pp. 190--191.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.
- Proof inspiration only: `WEAPON-KL-CHANGE-OF-MEASURE`.

The source statement is restated rather than copied: for the class of
`k`-armed unit-variance Gaussian bandits whose mean vector belongs to
`[0,1]^k`, there is a universal positive constant `c` such that, when `k > 1`
and `n >= k`, the infimum over policies of the worst-case expected cumulative
pseudo-regret is at least `c * sqrt (k*n)`. Chapter 13 labels this as Theorem
13.1 and explicitly defers its proof to Chapter 15.

## Frozen Chapter 13 completion contract

The contract was re-audited against physical PDF pp. 189--194.  A `complete`
chapter claim requires every mathematical main-text item below to be mapped
and every precise result to have a source-faithful compiled endpoint.  A
weaker consequence may be useful evidence but cannot discharge the exact
source node.

| Source item | Completion role | Required evidence | Current status |
| --- | --- | --- | --- |
| worst-case and minimax regret; minimax-optimal policy | required main text | explicit classes and fixed-horizon regret functional; attainment predicate | compiled |
| Theorem 13.1 | required main theorem | unit-Gaussian `[0,1]^k` minimax lower bound for `k>1`, `n>=k` | compiled through Chapter 15 with `c=1/54` |
| Section 13.1 two-point Gaussian test and midpoint decision | required main text | derive the empirical mean law `N(mu,1/n)` from `n` independent `N(mu,1)` observations; exact midpoint error events | compiled for the canonical finite product law |
| Eq. (13.1) | required displayed result | both explicit Mills-ratio bounds with the printed constants | compiled by `gaussianSampleMeanZeroErrorProbability_source_bounds`; final integration gate pending |
| competition/similarity trade-off | required source mapping | narrative route to the precise two-environment nodes; no invented standalone proposition | mapped |
| Eqs. (13.2)--(13.3), least-explored arm, one-coordinate change, `Delta` tuning, information bridge | required main text | exact identities/inequalities and the Chapter 14--15 same-policy history-law route | compiled locally or through Chapter 15 |
| Algorithm 7 / Theorem 9.1 near-minimax claim for the broader 1-subgaussian class | required connected main-text claim | Gaussian-subclass lower transfer plus a compiled MOSS upper theorem on the stated broader class | compiled broad-class near-minimax endpoint; full integration and publication gates pending |
| Section 13.2 Notes | optional enrichment | itemized mapping if attempted; never used to hide a main-text gap | optional, unformalized |
| Section 13.3 Bibliographic Remarks / Eq. (13.4) | source support for Eq. (13.1) | Abramowitz--Stegun Mills-ratio source and exact integral leaf | both exact integral bounds compiled in `GaussianMillsRatio.lean` |
| Section 13.4 Exercises 13.1--13.2 | optional exercises | separate exercise contracts if attempted | optional, unformalized |

The currently compiled core uses these interfaces:

1. For arbitrary policy and environment types, define worst-case and minimax
   expected regret in `ENNReal` over explicit policy/environment classes.
   Empty classes keep the standard complete-lattice semantics; intended
   Gaussian use will require explicit nonemptiness at the consumer.
2. Index a `k = m + 1` arm problem by distinguished base arm `0` and
   alternative arms `Fin m` mapped through `Fin.succ`. From nonnegative
   expected pulls and the exact pull budget `sum_a E[T_a(n)] = n`, prove that
   some alternative arm has expected pulls at most `n / m`.
3. Define the exact Chapter 13 algebraic expressions

   ```text
   base lower-bound expression    = Delta * (n - E_nu[T_0(n)])
   changed lower-bound expression = Delta * E_nu'[T_0(n)].
   ```

   Prove the quantitative maximum lower bound
   `Delta * (n - error) / 2` only under the explicit comparison
   `E_nu[T_0(n)] - E_nu'[T_0(n)] <= error`, and retain the half-horizon
   statement as its zero-error corollary. The comparison is a named missing
   information-theoretic bridge, not a hidden assumption and not a caller-free
   lower-bound theorem.
4. Publish the declarations through the root library and a full-typed external
   canary. The canary must instantiate nonempty policy/environment classes and
   a nondegenerate three-arm expected-pull vector.
5. Compile the fixed-class minimax-optimality predicate, the canonical iid
   Gaussian product law and its empirical-mean pushforward, the midpoint
   decision error events, and a genuine Gaussian Chernoff upper bound without
   labeling it as the exact Eq. (13.1).

Target files: `BanditRLProof/LowerBounds/BasicIdeas.lean` and the downstream
consumer `BanditRLProof/LowerBounds/GaussianMinimax.lean`.

Expected public declarations:

```lean
LowerBounds.worstCaseExpectedRegret
LowerBounds.minimaxExpectedRegret
LowerBounds.IsMinimaxOptimal
LowerBounds.IsMinimaxOptimal.mem_policyClass
LowerBounds.IsMinimaxOptimal.eq_minimaxExpectedRegret
LowerBounds.expectedRegret_le_worstCaseExpectedRegret
LowerBounds.minimaxExpectedRegret_le_worstCaseExpectedRegret
LowerBounds.le_minimaxExpectedRegret
LowerBounds.exists_alternative_le_average
LowerBounds.alternativeExpectedPullBudget_le
LowerBounds.exists_leastExploredAlternative
LowerBounds.baseEnvironmentRegret
LowerBounds.changedEnvironmentRegretLowerBound
LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error
LowerBounds.max_base_changed_regretLowerBound_ge_half
LowerBounds.gaussianSampleMeanVariance
LowerBounds.gaussianSampleMeanVariance_pos
LowerBounds.gaussianSampleMeanLaw
LowerBounds.gaussianIIDObservationLaw
LowerBounds.gaussianCoordinateAverage
LowerBounds.gaussianIIDSumLaw
LowerBounds.gaussianIIDSampleMeanLaw
LowerBounds.twoPointGaussianThresholdDecision
LowerBounds.twoPointGaussianThresholdDecision_zero_error_event
LowerBounds.twoPointGaussianThresholdDecision_gap_error_event
LowerBounds.gaussianSampleMeanZeroErrorProbability
LowerBounds.gaussianSampleMeanGapErrorProbability
LowerBounds.hasSubgaussianMGF_id_gaussianReal_zero
LowerBounds.hasSubgaussianMGF_gap_sub_id_gaussianReal
LowerBounds.gaussianReal_zero_Ici_le_exp_neg_sq_div_two_variance
LowerBounds.gaussianReal_gap_Iio_half_le_exp_neg_sq_div_two_variance
LowerBounds.gaussianSampleMeanZeroErrorProbability_le_exp
LowerBounds.gaussianSampleMeanGapErrorProbability_le_exp
LowerBounds.gaussianSampleMeanThresholdRisk
LowerBounds.gaussianSampleMeanThresholdRisk_le_exp
LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt
```

## Proof obligations

- [x] The formal source and page placement are recorded.
- [x] Theorem 13.1 is fenced as source-stated and is compiled through the
  Chapter 15 specialization with explicit universal constant `1/54`.
- [x] The compiled Chapter 13 semantic signature is frozen before tactics.
- [x] Hidden regularity assumptions are explicit in the conversion window.
- [x] Minimax and worst-case definitions and order leaves compile.
- [x] Fixed-class minimax-optimality semantics compile.
- [x] The Section 13.1 midpoint decision and both deterministic error-event
  identities compile.
- [x] The empirical mean of `n>0` independent `N(mu,1)` observations is
  connected to the declared `N(mu,1/n)` observation law.
- [x] Centered/reflected Gaussian sub-Gaussian bridges and the source-shaped
  `exp(-n*Delta^2/8)` Chernoff upper bound compile for both hypotheses and
  their worst-case threshold risk.
- [x] The exact two-sided Mills-ratio Eq. (13.1) compiles with its printed
  constants.
- [x] Alternative-arm averaging leaves compile from the exact pull budget.
- [x] Conditional two-environment algebra leaves compile without a statistical
  nonclaim being promoted.
- [x] Re-run integration for the exact Mills-ratio extension: root import,
  typed canary, Tests, axiom scan, full harness, synchronized exports/indexes,
  documentation and website. The earlier Chernoff-only baseline passed;
  that historical gate does not certify this extension. The expanded
  Mills/MOSS tree now passes local e218fc8 full checks and PR #105's
  latest-head run 33952076777, with rendered export and local site QA
  recorded in `reviews/2026-09-05-ch13-moss-closeout-audit.md`.
- [x] Refresh the structured source/Lean/evidence review for the exact-bound
  extension. The earlier review's website-status-enum P3 was corrected;
  the exact-Mills audit and current source-coverage/consumer self-review
  are recorded, without claiming independent approval.
- [x] The earlier dependency-slice PR #9, remote Actions run `31942624241`, merge commit `44c3e153`,
  Pages deployment job `95156292456`, and the live desktop/mobile Chapter 13
  page pass.
- [ ] The current Chapter 15 downstream Theorem 13.1 consumer passes its own
  PR, authoritative-main Actions, Pages deployment, and live Chapter 13 check.
- [x] The main-prose broader-class near-minimax consequence has a compiled
  MOSS/Algorithm 7 upper theorem for the stated 1-subgaussian class.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| minimax surface | `iSup`, `iInf`, `ENNReal`, subtypes | complete-lattice introduction/elimination | explicit policy/environment subsets; nonemptiness only at semantic consumers | project-local |
| minimax-optimality | compiled minimax surface, equality | package admissibility and attainment without assuming an infimum is attained | fixed policy/environment classes and horizon-indexed regret functional | project-local |
| Gaussian test upper tail | Mathlib `gaussianReal`, exact Gaussian MGF, `HasSubgaussianMGF.measure_ge_le` | identify both midpoint error events and apply the one-sided Chernoff bound at variance `1/n` on each side | positive gap; positive sample size is compiled separately for the nondegenerate source interpretation | compiled project-local consequence |
| Gaussian empirical-mean law | `Measure.pi`, `charFun_map_sum_pi_eq_prod`, `charFun_gaussianReal`, `gaussianReal_map_div_const` | identify the exact sum law on the canonical finite iid product, then scale by `1/n` | `n>0`; coordinate law `N(mu,1)` | compiled project bridge |
| exact Eq. (13.1) | Gaussian density/set integral plus Eq. (13.4) Mills-ratio bounds | prove the printed lower and upper denominator constants, then rescale to variance `1/n` | `n>0`, `Delta>0`, measurable midpoint event | locally compiled Mathlib-candidate analytic leaf |
| finite average | `Fin.sum_univ_succ`, `Finset.exists_le_of_sum_le`, `Fintype.card_fin` | split arm zero, bound alternative sum, compare with constant average | `0 < m`, every expected pull nonnegative, exact total expected-pull identity | mathlib-composed project leaf |
| two-environment algebra | ordered-field arithmetic, `max`, `nlinarith` | combine base and changed lower expressions under a named upper bound on `E_nu[T_0]-E_nu'[T_0]` | `0 <= Delta`; the quantitative cross-law discrepancy is explicit and remains unproved here | project-local |
| history change of measure | compiled Chapter 15 Lemma 15.1 | Chapter 14 KL plus the Chapter 15 randomized-history construction | measurability, common randomized policy, countably generated rewards | compiled downstream dependency |
| Gaussian minimax terminal | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | Chapter 15 consumption of Chapter 14 information bridge and Chapter 13 algebra | unit variance, means in `[0,1]^k`, `k > 1`, `n >= k` | compiled source-order endpoint with explicit `c=1/54` |

## Retrieval cards

- Mathlib: `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`,
  `MLIB-ORDER-ALGEBRA`.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none required by the first compiled leaves.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims

- Theorem 13.1 is not proved inside the Chapter 13 module; the project-level
  source endpoint is the separately compiled Chapter 15 consumer.
- The Chernoff upper bound is not Eq. (13.1): it neither supplies the printed
  Mills-ratio denominator nor the required lower bound.
- No Gaussian measure, adaptive history likelihood ratio, KL chain rule,
  event-level binary KL inequality, Pinsker/Bretagnolle--Huber inequality, or
  absolute-continuity result is claimed locally in this chapter.
- An external theorem card or proof-weapon card is never a local Lean proof.
- The compiled conditional algebra theorem alone does not establish the
  cross-environment comparison; the Chapter 14--15 route supplies it on the
  same policy and history law.
- The chapter does not cover finite-arm minimax sharp constants,
  instance-dependent asymptotics, or high-probability lower bounds.
- A Gaussian-subclass lower bound alone does not prove the broader
  1-subgaussian Algorithm 7 near-minimax statement; its upper side remains a
  distinct MOSS/Chapter 9 dependency.

## Failure policy

### 2026-09-05 Broader-class near-minimax consumer

`LowerBounds/SubgaussianMinimax.lean` now compiles the main-prose consequence.
The class is all stationary unit-subgaussian arm laws with gaps in `[0,1]`,
not merely bounded means. `subgaussianMinimax_sandwich` proves lower constant
1/54 and MOSS worst-case upper constant 40 on the same history-law regret;
`moss_nearMinimax` proves the universal factor 2160. The source only asks
for a constant factor, not an optimal constant. The Gaussian subclass
embedding is regret preserving and the MOSS policy does not depend on means.
The horizon is t+1 for inclusive history t, with k>1 and k<=t+1.
This supersedes the historical open-MOSS note below. Whole-chapter status
remains partial pending current full checks, comprehensive export/site
synchronization, review, PR and authoritative deployment/live verification.

### 2026-09-05 MOSS peeling progress

`ConcentrationDyadicExponential.lean` and `Algorithms/MOSSPeeling.lean`
compile the geometric-series estimate and source Lemma 9.3 with its actual
empirical-mean/radius event and printed constant 15. Contracts remain explicit:
strongly measurable independent centered unit-subgaussian coordinates,
positive delta and gap. The telescoping intermediate bound 12 implies 15;
no probability-tail premise is assumed. This does not yet instantiate the
centered arm-stream model or prove Theorem 9.1. Next leaves are expected
optimism deficit, large-gap occupancy, and concrete history regret assembly.
Chapter status remains partial. Route: `research-wiki/mathlib-candidates/moss-dyadic-peeling.md`.

Full validation at preceding commit `511062a` passed root (8857 jobs),
Tests (8901 jobs), ProofGraphExport, and 400 Python tests (7 skipped,
176.716 seconds). This is not full validation of the subsequent peeling files.

Do not weaken Theorem 13.1, identify expectations from different environments,
drop the policy-consistency or absolute-continuity requirements of the future
bridge, or relabel deterministic scaffolding as the Gaussian minimax theorem.
For any broader replacement route, preserve the exact source target and record
the smallest missing definition, Mathlib API, regularity assumption, and
reusable leaf before changing route.
