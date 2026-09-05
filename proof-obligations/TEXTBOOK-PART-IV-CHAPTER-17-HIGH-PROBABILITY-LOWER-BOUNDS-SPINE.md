# Proof Obligations: Textbook Part IV Chapter 17 high-probability lower bounds

Task id: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-ADVERSARIAL-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `CH17-SOURCE-FENCE` | exact Theorem 17.1 / Corollaries 17.2--17.3 / Theorem 17.4 / Claims 17.5--17.7 / Eq. (17.8) | official source | evidence artifacts | textbook/paper cards | freeze regret notion, all quantifiers, event direction, constants, and pages | three editions distinct | source evidence | repository artifacts | source review | mapped |
| `CH17-TAIL-EVENT` | `{quantity>=threshold}` | sets/order | set comprehension | `MLIB-ORDER-ALGEBRA` | literal source event direction | no probability law hidden | project-local | `tailAtLeast` | focused Lean | compiled |
| `CH17-THM-17-1-THRESHOLD` | outer `1/4` times exact minimum | log/sqrt/min | real special functions | `MLIB-REAL-LOG-SQRT` | literal transcription with `alternativeArms=k-1` | terminal supplies positivity | project-local | `stochasticHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-COR-17-2-THRESHOLD` | exact Eq. (17.7) threshold | log/sqrt/min | real special functions | `MLIB-REAL-LOG-SQRT` | retain `1/2` inside sqrt and outer `1/4` | terminal supplies side condition | project-local | `stochasticMinimaxHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-THM-17-4-THRESHOLD` | `c sqrt(nk log(1/(2delta)))` | log/sqrt | real special functions | `MLIB-REAL-LOG-SQRT` | literal transcription | terminal supplies `c,C,n,k,delta` conditions | project-local | `adversarialHighProbabilityThreshold` | focused Lean | compiled |
| `CH17-FIRST-MOMENT` | average tail gives one point | probability measure | `exists_integral_le` | `MLIB-MEASURE-INTEGRAL` | first moment method | probability law and integrability | Mathlib-composed | `exists_tailMass_ge_of_integral_ge` | focused Lean | compiled |
| `CH17-CLAIM-17-5` | `E_Q[1-F_X(u)]>=delta` gives deterministic `x` | first-moment leaf | Bochner integral | textbook card | specialize tail mass to `1-F_x(u)` | integrability explicit | exact source claim | `exists_cdfTail_ge_of_integral_ge` | focused Lean | compiled |
| `CH17-EVENT-SUBTRACTION` | pull-small `2delta`, clipping-bad `delta` imply good `delta` | finite measure | `le_measureReal_diff` | `MLIB-MEASURE-INTEGRAL` | outer-measure difference plus linear arithmetic | no measurable-set premise needed | Mathlib-composed | `measureReal_diff_ge_delta` | focused Lean | compiled |
| `CH17-EQ-17-8-EXPRESSION` | exact RHS count expression | natural casts/order | real arithmetic | `MLIB-ORDER-ALGEBRA` | define source lower expression | construction semantics separate | project-local | `adversarialRegretLowerExpression` | focused Lean | compiled |
| `CH17-EQ-17-8-QUARTER` | count bounds leave `Delta n/4` | previous expression | ordered multiplication | `MLIB-ORDER-ALGEBRA` | subtract half and quarter, multiply by nonnegative gap | nonnegative gap | project-local | `adversarialRegretLowerExpression_ge_quarter` | focused Lean | compiled |
| `CH17-EQ-17-8-TRANSFER` | source comparison implies random-regret threshold | previous leaf | order transitivity | textbook card | compose with explicit construction premise | Eq. (17.8) remains premise | project-local conditional | `randomRegret_ge_quarter_of_clippingDecomposition` | focused Lean | compiled |
| `CH17-HISTORY` | original-law expected-pull/history information | compiled Ch15 Lemma 15.1 | compiled stochastic policy/history | Chapter 17 tail-event consumer | change one Gaussian arm and instantiate the history identity | same randomized policy; first-law pulls | project-local consumer | theorem 17.1 proof route | focused Lean | compiled |
| `CH17-THM-17-1` | exact stochastic tail lower bound | history, BH, least arm, tuning | Ch13--15 | source card | quantify the premise over the full gap-at-most-one class, restrict it to the unit-cube hard family, choose gap, one-arm change, sum two tail events | exact `n,k,B,delta` and full source class | source terminal | `gaussianRandomPseudoRegret_ge_theorem17_1` | focused Lean | compiled |
| `CH17-COR-17-2` | exact Eq. (17.7) | Theorem 17.1 | expectation/tail bound | source card | contradiction and choose source `B=sqrt(2 log(1/(4delta)))` | Eq. (17.6) exact | source terminal | `gaussianRandomPseudoRegret_ge_corollary17_2` | focused Lean | compiled |
| `CH17-COR-17-3` | no single all-confidence policy | Theorem 17.1 | `Integrable.integral_eq_integral_meas_le`, `integral_comp_mul_left_Ioi`, and `integral_exp_neg_rpow_inv_le_one` | `MLIB-MEASURE-INTEGRAL`, Gamma convexity, real-rpow asymptotics | rescale the strict tail, integrate to a uniform first moment, then calibrate two confidence levels and a sufficiently large natural horizon | real `p in (0,1)`, strict `<delta`, one policy and full `E^k` | compiled source terminal | `noUniformGaussianRandomPseudoRegretTail_corollary17_3` | focused Lean | compiled |
| `CH17-CLIPPED-NORMAL` | reward-matrix hard family and interaction law | Gaussian/clipping/kernels | `Measure.pi`, clipping map, history kernels | probability cards | preserve within-round dependence and across-time IID; all-round marginal identity | same randomized policy and full hard family | project-local | `adversarialNoiseHistoryJoint_history_marginal` | focused Lean | compiled; full local gate passed |
| `CH17-CLAIM-17-6` | corrected `P_Qi(T_i<=n/2)>=2delta` | hard family and history KL | Chapter 14--15 route | textbook/paper route | least arm plus entropy calculation and joint-law transport | exact `Delta`; same policy; user-approved non-strict correction | corrected terminal | `adversarialNoiseHistoryJoint_pull_le_half_claim17_6` | focused Lean | compiled; full local gate passed |
| `CH17-EQ-17-8` | construction-level pathwise regret comparison | clipped reward coordinates | finite sums/indicators and finite supremum | textbook/paper route | show chosen arm reward dominates except pull/clipping rounds | exact clipping map and shared centered noise | source terminal | `adversarialRandomRegret_ge_eq17_8` | focused Lean | compiled |
| `CH17-CLAIM-17-7` | literal boundary clipping count tail at most `delta` | Gaussian MGF and bounded Hoeffding | product independence and count envelope | `MLIB-PROBABILITY-SUBGAUSSIAN` | bound each boundary hit and sum/count | exact constants and horizon condition; full family including base | source terminal | `adversarialFullBoundaryCount_tail_claim17_7` | focused Lean | compiled; full local gate passed |
| `CH17-THM-17-4` | deterministic reward-matrix witness | Claims 17.5--17.7 and Eq. (17.8) | first moment, calibration, measurable CDF | source/paper route | good-event subtraction, calibrate `Delta`, extract witness | `c=1/160`, `C=64`, approved `0<delta<=1/32`; strict tail | corrected terminal | `adversarialRandomRegret_ge_theorem17_4` | focused Lean | compiled; full local gate passed |
| `CH17-CANARY` | root-import typed applications and axiom reports | compiled slice | `BanditRLProof` root | local declarations | instantiate nontrivial threshold and probability leaves | no placeholders | project-local | `Tests/TextbookPartIVChapter17Canary.lean` | Tests | verified on Linux PR/main |
| `CH17-SITE-REVIEW` | synchronized evidence/site and independent audit | all above | build/check/browser | repository | compare informal and Lean statements | no terminal promotion | repository | evidence artifacts | full/local | site, desktop/mobile, Linux, and review passed |
| `CH17-REMOTE` | PR, authoritative-main Actions, Pages, and live page | accepted local slice | GitHub workflow | repository | merge through PR and inspect deployed artifact | source terminals remain blocked; PR #17; merge `eb41d96`; main run `31976153611`; deploy `95238317293`; live desktop/mobile | repository | remote evidence | deployment | verified |

## Claim 17.7 update (2026-09-05)

The dated update/failure sections below preserve intermediate states. Their
then-open blockers are superseded by the current table and final report:
all Chapter 17 body interfaces pass the full local gate with the two approved
corrections. Prior remote/browser evidence is historical, not a new deployment.

`adversarialClippingCount_tail_claim17_7` has passed the focused module build.
Its route uses Gaussian MGF/Chernoff, product-coordinate marginals,
`iIndepFun_pi`, and bounded-variable Hoeffding: mean at most `1/8`, proxy
`1/4`, and exponent `-n/32`. No concentration hypothesis is assumed.
The literal textbook boundary count is connected through
`adversarialBoundaryClippingCountReal_le`: an interior-noise round has all
shifted rewards strictly between zero and one, by the existing shift bounds
and `clipUnitReward_eq_self`. The boundary-event wrapper
`adversarialBoundaryClippingCount_tail_claim17_7` passed the focused module
build on 2026-09-05 (3588 jobs).
This dated update supersedes the older Claim 17.7 blocked row above.
Theorem 17.4 still requires the policy-coupled shared-noise matrix law.

## Corrected Claim 17.6 update (2026-09-05)

`adversarialClippedHistory_pull_le_half_claim17_6` passed the focused build
(3588 jobs). Its non-strict event is the user-approved correction, not the
false literal source event. Exact tuning, arbitrary common randomized
policy, base-or-alternative witness, and `0<delta<1/8` are explicit.
The proof derives finite expected-pull information and the BH bound from
the raw observation law, then transports pull events to clipped histories.
This supersedes the older Claim 17.6 probability-bound blocker.
Remaining route: construct the shared-noise reward-matrix/policy joint law,
prove its clipped-history marginal and noise marginal, include the base
instance in the pathwise regret argument, combine with Claim 17.7, justify
the final confidence domain and constants, and extract a fixed matrix.
Theorem 17.4 remains partial; none of those bridges is an assumed terminal.

Full-family pathwise bridge route: retain `adversarialFullHardShift`, prove
its range `[0,2*gap]` and distinguished-arm separation (including arm zero),
then reuse `clipUnitReward_eq_self_of_ne_endpoints`, monotonicity of min/max,
finite sums, and `adversarialComparatorRegret_le_randomRegret` for literal
boundary-count Eq. (17.8). Bound that count by the existing noise envelope
and reuse the compiled Claim 17.7. No new probability assumptions/imports.

Conditional-matrix-law route: define a kernel from deterministic reward
tables to inclusive histories using `Kernel.const`, `Kernel.deterministic`,
`Kernel.compProd`, and the existing zero/successor history equivalences.
At each step use the original `algorithm.policy` on the observed prefix.
Prove the kernel is Markov by induction. This provides the measurable
conditional law needed for matrix averaging; marginal equivalence to the
Gaussian observation law remains a separate obligation, not a premise.

Noise integration preparation: prove table-prefix congruence of the history
kernel by its zero/successor recurrences and the exact step feedback law.
Embed the finite shared-noise matrix as a table with zero future rows; prove
the embedding measurable, then form the noise/history `Measure.compProd`.
Its noise marginal follows from the Markov property. The history marginal
must still be identified by independent-coordinate integration.

Coordinate split route: specialize Mathlib `measurePreserving_piFinSuccAbove`
to the centered Gaussian product. On the inverse split, prefix-congruence
and `Fin.insertNth_apply_below` remove dependence on a future coordinate.
This supplies the independent-coordinate factorization needed by the next
history-marginal induction; no conditional-independence assumption is added.

Initial marginal route: expand the table-history zero recurrence, integrate
its deterministic reward, exchange noise and initial action via Tonelli,
then use the exact full-family reward marginal and the canonical zero law.
APIs: `lintegral_map`, `Measure.lintegral_compProd`,
`Kernel.lintegral_deterministic`, `lintegral_lintegral_swap`,
`measurePreserving_eval`, `canonicalBanditHistoryMeasure_zero`.

Successor integration route: for a fixed prefix probability law, combine
history and policy action by `Measure.compProd`; Tonelli exchanges this pair
with a fresh Gaussian coordinate. Integrate the clipped reward map and
identify `Thompson.historyStepKernel` for the stationary clipped kernel.
The prefix law is fixed only within a split-coordinate fiber, justified
later by the already compiled future-coordinate invariance.

Joint good-event route: transfer the measurable noise-envelope clipping
event through the proved `fst` marginal; combine its upper bound `delta`
with the proved joint pull event lower bound `2*delta` via
`measureReal_diff_ge_delta`. Use `adversarialFullBoundaryCount_le` to retain
the literal boundary count in the resulting event. No independence between
the pull event and clipping event is assumed.

Count/regret bridge: reindex inclusive histories as `Fin (n+1)` action
paths. Prove equality of recursive pull counts and indicator sums by
`Fin.sum_univ_castSucc`, then convert finite ENNReal sums to Real. Compose
the full-family Eq. (17.8) with the joint good-event count inequalities.

Fixed-instance extraction route: retrieved `exists_tailMass_ge_of_integral_ge`
and the measure-integral card. For a measurable joint event, kernel section
mass is measurable (`Kernel.measurable_kernel_prodMk_left`), bounded by one,
and integrable (`Integrable.of_bound`). `integral_toReal` and
`Measure.compProd_apply` identify its mean with joint probability. Apply
the compiled first-moment method. The generic kernel-section helper is a
Mathlib candidate; the adversarial wrappers retain concrete event semantics.

Final calibration route (authorized erratum): use `0<delta<=1/32` so
`log(1/(2delta))/2<=log(1/(8delta))` and
`log(1/delta)<=2*log(1/(2delta))`. A horizon constant `64` and a strictly
smaller threshold coefficient (candidate `1/160`) leave slack for the
source strict-tail event. Prove every inequality before asserting the
corrected terminal; preserve the impossible-domain counterexample.

Source-interface audit: expose fixed-table random regret, its separate
Bochner expectation, and CDF `P(R<=u)`. Prove the strict tail equals `1-F(u)`
using finite-max measurability and `measureReal_compl`. The CDF wrapper
must consume the compiled corrected strict-tail terminal, not rename
an expectation or random pseudo-regret as adversarial random regret.

## Failure classification

2026-09-05 user confirmation authorizes the recorded erratum route:
non-strict Claim 17.6 and an explicitly justified confidence domain for
Theorem 17.4. Historical source obstructions below stay as evidence, not
as a requirement to ask again. Current route: include the base arm among
the hard-family witnesses, choose a least-pulled alternative, use the
compiled history KL, and apply BH with the source gap tuning.

### Source-level obstruction found 2026-09-05

Follow-up audit: Theorem 17.4's stated `delta in (0,1)` also needs a
domain repair. Set `delta=3/4`, `k=2`, `n=1`, and use a uniform initial
action. The horizon condition holds for every positive `C` because its
logarithm is negative. The real square root is undefined in usual real
notation; in Lean's total `Real.sqrt` it is zero. For any fixed rewards
`x,y`, at most one action has strictly positive regret, so the strict CDF
tail at zero has probability at most `1/2 < 3/4`. External Lean canary
`E:/Temp/Chapter17DeltaRangeCounterexample.lean` compiled the indicator
bound, horizon condition, and zero threshold on 2026-09-05.
This is a second instance of the same completion blocker: the literal
source targets cannot all be true. It does not authorize target repair.

The official author PDF, physical page 228 (zero-based 227), states Claim
17.6 with `T_i(n) < n/2`, not `<=`. For two arms and any positive even
horizon, the deterministic policy that pulls each arm exactly half the
time makes this event empty for both arms, under every reward law.
Thus its probability is zero and cannot be at least `2 delta` for positive
delta. This remains true for arbitrarily large even horizons and does not
depend on clipping. The exact literal requested Claim 17.6 is false.
Changing `<` to `<=` is a possible repair but changes the user-requested
statement; it is not silently substituted here. The source includes arm 1
(the base instance) among its witnesses, which also does not fix this tie.

The equal-variance Gaussian KL and hard-family history identity now compile:
`klDiv_gaussianReal_common_scale`, `klDiv_adversarialUnclippedKernel`, and
`klDiv_adversarialUnclipped_base_changed_history` (3588-job focused build).

Equal-variance Gaussian KL route (Mathlib candidate): push the existing
unit-variance pair with means `mu/sigma, nu/sigma` through
`(Homeomorph.mulLeft₀ sigma hne).toMeasurableEquiv`.
Use `gaussianReal_map_const_mul`, `klDiv_map_measurableEquiv`, and
`klDiv_gaussianReal_one`; normalize the resulting real square algebra.
The only added regularity is `sigma != 0` (the source assumes `sigma > 0`).

Integrated transport route: expand `Measure.compProd_apply` on a measurable
set, use `lintegral_map` for the clipped prefix and the compiled pointwise
`adversarialClipped_historyStepLaw`, then identify the preimage under
`Prod.map` of prefix clipping and pair clipping. This yields the joint
prefix/next-pair identity needed by the successor-history induction.

History transport proof uses `canonicalBanditHistoryMeasure_zero` and
`canonicalBanditHistoryMeasure_succ`, `Measure.map_map`, and the measurable
singleton/successor history encodings. Initial transport follows from
`adversarialClipped_initialPairLaw` and coordinatewise clipping of the
singleton encoding. Successor transport additionally needs compProd
pushforward compatibility for the lifted policy kernel.

Lifted-policy route for Claim 17.6: clip only the reward coordinate of each
finite history, and comap the original policy along this measurable map.
The initial action law is unchanged. Prove prefix compatibility and pull
count preservation by the existing recursive pull-count definition. This
allows the Gaussian comparison to use a policy that reads only clipped
observations; the pushforward history-law identity remains to be proved.

Claim 17.6 feedback-law route: map `gaussianReal 0 sigma^2` by
`x ↦ clipUnitReward (1/2 + x + shift arm)`; use
`Kernel.ofFunOfCountable` for the finite-arm Markov kernel and
`canonicalBanditHistoryMeasure` for the same `HistoryAlgorithm`.
This constructs the observation law only. Equality with the correlated
pre-sampled reward-matrix interaction and its KL bound remain separate
obligations; the marginal kernel alone does not certify those claims.

The literal Eq. (17.8) route uses `clipUnitReward`'s min/max definition:
if its output is neither endpoint, its input lies in `(0,1)` and clipping
is the identity. Apply this to both arms on each non-boundary round,
use the hard-shift gap, sum, and pass to the finite maximum comparator.
No distributional or policy assumptions are needed for this pathwise step.

Theorem 17.1 and Corollaries 17.2--17.3 now compile through Chapter 15's exact
same-policy history KL identity and the layer-cake/Gamma calibration. The adversarial path construction
and Eq. (17.8) compile, while Claim 17.6 still needs the policy-coupled
pushed-forward hard law and Claim 17.7 still needs its exact Gaussian
clipping-count concentration. No theorem target is weakened in response.

## Reviewer notes

Current opening-interface route (2026-09-05): fixed-table random regret is
measurable and takes values among the finitely many action-path regrets.
Bound its norm by the sum of these norms and use `Integrable.of_bound`.
This proves the separate Bochner expectation well-defined even for an
arbitrary fixed real table; the theorem witness remains bounded in `[0,1]`.
The CDF complement terminal and integrability lemma pass the final full
repository gate on a hash-matched short-path snapshot: root/Tests/exporter,
placeholder scan, and 400 Python tests with 7 expected skips.

- Compare random pseudo-regret, random regret, and expected regret exactly.
- Check Theorem 17.1's uniform premise, outer factor `1/4`, KL direction, and
  probability `>=delta`.
- Check Corollary 17.2's Eq. (17.6), the factor `1/2` inside the square root,
  and the same outer quarter.
- Check Corollary 17.3's single-policy quantifiers, real exponent, and strict
  `<delta` direction.
- Check Theorem 17.4's deterministic bounded reward matrix, CDF argument,
  `log(1/(2delta))`, and horizon condition.
- Check Claim 17.5's integrability and the explicitly approved non-strict
  Claim 17.6; Claim 17.7 retains the literal full-family boundary event.
- Check within-round arm dependence and across-time IID in the hard family.
- Do not promote the NeurIPS paper, theorem cards, open-problem proposals, or
  conditional algebra to compiled terminal evidence.
