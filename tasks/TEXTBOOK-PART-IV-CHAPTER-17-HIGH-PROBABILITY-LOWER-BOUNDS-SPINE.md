# Textbook Part IV Chapter 17 high-probability lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Formalize the source-faithful stochastic and adversarial high-probability
lower-bound routes in Lattimore--Szepesvari, *Bandit Algorithms* (2020),
Chapter 17. The exact source terminals are Theorem 17.1, Corollaries 17.2 and
17.3, Theorem 17.4, and Claims 17.5--17.7. The current compiled slice closes
Theorem 17.1, Corollaries 17.2--17.3, Claim 17.5, and construction-level Eq.
(17.8), including the correlated shared-noise clipped path, and Claim 17.7.
The user-approved non-strict Claim 17.6 and corrected Theorem 17.4 now have
focused-build terminals, including the shared-noise joint law, fixed-table
extraction, and CDF-complement interface. The latter uses `c=1/160`, `C=64`,
`0<delta<=1/32`, and strict random-regret tails. Full local root/Tests/exporter,
placeholder-scan, and Python regression gates pass on the hash-matched
short-path snapshot. This is local acceptance of the approved corrected
chapter, not a new merge or deployment.

## Frozen chapter-completion contract (2026-09-04)

Chapter completion is evaluated against every mathematical item in the
chapter body, not against the presence of a threshold definition or a
conditional consumer.  The following table is the source-faithful acceptance
contract for this task.  A row may move to `compiled` only when the named
local declaration exists, is root-imported, is exercised by the Chapter 17
canary, and passes the repository gates.

The table preserves the frozen body coverage. The two user-approved source
corrections are explicit below; false printed statements are not promoted
to proved claims. All rows have current local root/canary/full-gate evidence.

| Body item | Required local surface | Completion rule | Current status |
| --- | --- | --- | --- |
| opening definitions of adversarial random regret `Rhat_n` and expected regret `R_n` | `adversarialTableRandomRegret`, `adversarialTableExpectedRegret`, `integrable_adversarialTableRandomRegret` | pathwise random regret and its integrable deterministic expectation remain separate | compiled |
| Section 17.1 random pseudo-regret `Rbar_n` | `gaussianRandomPseudoRegret` on the canonical finite history | must be the gap-times-random-pull-count variable, not its expectation | compiled |
| Gaussian class `E^k` and Eq. (17.4) | unit-variance Gaussian arm laws, gap-at-most-one environment contract, and uniform expected-pseudo-regret premise for one policy | the unit-cube construction may witness the conclusion, but the premise must not be silently changed to an independent-arm or deterministic-policy model | compiled full source class; proof uses embedded unit-cube subfamily |
| Theorem 17.1 | `gaussianRandomPseudoRegret_ge_theorem17_1` | exact outer `1/4`, minimum, `log(1/(4 delta))`, `>= delta`, original-to-alternative history KL, and original-law expected pulls | compiled |
| Corollary 17.2 | `gaussianRandomPseudoRegret_ge_corollary17_2` | exact Eq. (17.6), factor `1/2` inside the square root in Eq. (17.7), and the same outer quarter | compiled |
| Corollary 17.3 | `noUniformGaussianRandomPseudoRegretTail_corollary17_3` | one policy for every horizon/confidence/environment, real `p in (0,1)`, and strict `< delta` | compiled |
| Section 17.2 policy/reward-matrix coupling and CDF `F_x` | `adversarialTableHistoryKernel`, `adversarialNoiseHistoryJoint_history_marginal`, `adversarialTable_strictTail_eq_one_sub_CDF` | same-policy fixed-table law; actual random regret and strict CDF complement | compiled |
| Claim 17.5 | `exists_cdfTail_ge_of_integral_ge` | average hard-law tail yields one deterministic matrix; integrability remains explicit | compiled |
| clipping map and hard laws `Q_i` | correlated-within-round / IID-across-time clipped-normal reward matrix with shared `eta_t` | exact full-family shifts, measurable reward table, and all-round same-policy joint-law marginal | compiled |
| Claim 17.6, approved correction | `adversarialNoiseHistoryJoint_pull_le_half_claim17_6` | exact gap and probability `>=2delta`, with corrected `T_i<=n/2` | compiled corrected terminal |
| construction-level Eq. (17.8) | pathwise declaration over the clipped reward matrix and policy actions | must prove the comparison itself; `randomRegret_ge_quarter_of_clippingDecomposition` is only a downstream conditional consumer | compiled |
| Claim 17.7 | `adversarialFullBoundaryCount_tail_claim17_7` | exact full-family clipping event, `sigma=1/10`, `Delta<1/8`, `n>=32 log(1/delta)`, and probability `<=delta` | compiled |
| Theorem 17.4, approved correction | `adversarialRandomRegret_ge_theorem17_4` | deterministic bounded matrix, strict CDF tail, `c=1/160`, `C=64`, `0<delta<=1/32`, and source-form horizon | compiled corrected terminal |

### Current acceptance evidence (2026-09-05)

All named endpoints below pass focused compilation and the full local gate:
8852 root jobs, 8894 Tests jobs, exporter, placeholder scan, and 400 Python
tests with 7 expected skips. See `reports/chapter17-corrected-terminal-validation-2026-09-05.md`.

- Opening random regret and expectation: `adversarialTableRandomRegret`,
  `adversarialTableExpectedRegret`, and `integrable_adversarialTableRandomRegret`.
- Same-policy matrix/history coupling: `adversarialTableHistoryKernel` and
  `adversarialNoiseHistoryJoint_history_marginal` (all rounds).
- CDF: `adversarialTableCDF`, `adversarialTable_strictTail_eq_one_sub_CDF`.
- Claim 17.6: `adversarialNoiseHistoryJoint_pull_le_half_claim17_6`, with
  user-approved `<= n/2`; the balanced two-arm counterexample refutes `< n/2`.
- Claim 17.7: `adversarialFullBoundaryCount_tail_claim17_7`, using the literal
  boundary event for the full hard family, including the base environment.
- Eq. (17.8): `adversarialFullRandomRegret_ge_boundary_eq17_8`.
- Corrected Theorem 17.4: `adversarialRandomRegret_ge_theorem17_4`, with
  deterministic bounded matrix, `1-F_x(u)`, `c=1/160`, `C=64`, and approved
  `0<delta<=1/32`. The printed `(0,1)` domain is not asserted.

Section 17.3 notes, Section 17.4 bibliographic remarks, and Exercise 17.1 are
optional explanatory/export material.  They cannot compensate for an open
body row above.  In particular, Exercise 17.1 is not a license to omit Claims
17.5--17.7 from the chapter-completion gate because those claims occur in the
body proof of Theorem 17.4.

## Source

- Authors: Tor Lattimore and Csaba Szepesvari.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- Book DOI: <https://doi.org/10.1017/9781108571401>.
- Chapter DOI: <https://doi.org/10.1017/9781108571401.022>.
- CUP chapter page:
  <https://www.cambridge.org/core/books/abs/bandit-algorithms/highprobability-lower-bounds/CDC23AC2BB673E4D5FDBD05D3BD3AB9E>.
- Official author PDF: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 17, CUP print pp. 185--190; author-online
  page labels 215--221; physical PDF pp. 224--230.
- Chapter opening: CUP p. 185; author-online p. 215; physical PDF p. 224.
- Section 17.1 Stochastic Bandits: CUP pp. 186--188; author-online pp.
  216--218; physical PDF pp. 225--227. Theorem 17.1 and Corollaries
  17.2--17.3.
- Section 17.2 Adversarial Bandits: CUP pp. 188--190; author-online pp.
  218--220; physical PDF pp. 227--229. Theorem 17.4 and Claims 17.5--17.7.
- Section 17.3 Notes: CUP p. 190; author-online p. 220; physical PDF p. 229.
- Section 17.4 Bibliographic Remarks: CUP p. 190; author-online p. 220;
  physical PDF p. 229.
- Section 17.5 Exercises: CUP p. 190; author-online p. 221; physical PDF
  p. 230.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` plus Chapter 17 cards below.
- Scenario cards: `SCN-STOCHASTIC-FINITE` and `SCN-ADVERSARIAL-FINITE`.
- Detailed adversarial route evidence only: Gerchinovitz--Lattimore,
  *Refined Lower Bounds for Adversarial Bandits*, NeurIPS 2016,
  <https://proceedings.neurips.cc/paper/2016/hash/2f37d10131f2a483a8dd005b3d14b0d9-Abstract.html>.

The CUP print pagination, author-online page labels, and physical PDF pages are
edition-specific fields. The author PDF explicitly warns that its pagination
does not match the print edition, so no constant page offset is inferred.

## Frozen source targets

The chapter opening defines adversarial random regret and expected regret as

```text
Rhat_n = max_{i in [k]} sum_{t=1}^n (x_ti - x_t,A_t),
R_n = E[Rhat_n].
```

Section 17.1 defines stochastic random pseudo-regret by

```text
Rbar_n = sum_{i=1}^k T_i(n) Delta_i.
```

Let `E^k` be the class of `k`-armed Gaussian bandits whose suboptimality gaps
are bounded by one. The source writes `mu in [0,1]^d` when introducing
`nu_mu`; the surrounding `k`-armed context indicates a dimensional typo.
The Lean target records a `k`-indexed mean vector and does not silently retain
an unrelated `d`.

Theorem 17.1: let `n>=1`, `k>=2`, `B>0`, and let one policy `pi` satisfy for
every `nu in E^k`

```text
R_n(pi,nu) <= B sqrt((k-1)n).                              (17.4)
```

For every `delta in (0,1)`, there exists `nu in E^k` such that

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    (1/4) min { n,
      (1/B) sqrt((k-1)n) log(1/(4 delta)) }) >= delta.
```

The factor `1/4` is outside the whole minimum. The proof chooses

```text
Delta = min { 1/2,
  (1/(2B)) sqrt((k-1)/n) log(1/(4 delta)) },
```

uses the least-pulled arm among arms `i>1`, changes that arm's mean by
`2 Delta`, and applies Bretagnolle--Huber and Lemma 15.1 in the original-law
to alternative-law KL direction.

Corollary 17.2: if `n>=1`, `k>=2`, `delta in (0,1)`, and

```text
n delta <= sqrt(n(k-1) log(1/(4 delta))),                 (17.6)
```

then for every policy there exists `nu in E^k` such that

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    (1/4) min { n,
      sqrt((n(k-1)/2) log(1/(4 delta))) }) >= delta.      (17.7)
```

Corollary 17.3: for `k>=2`, `p in (0,1)`, and `B>0`, there does not exist one
policy `pi` such that for all `n>=1`, all `delta in (0,1)`, and all
`nu in E^k`,

```text
P_nu^pi(
  Rbar_n(pi,nu) >=
    B sqrt((k-1)n) log(1/delta)^p) < delta.
```

The strict `< delta`, every-horizon/every-confidence quantifiers, and single
policy are essential.

Theorem 17.4: there exist sufficiently small/large universal constants
`c,C>0` such that for `k>=2`, `n>=1`, `delta in (0,1)`, and

```text
n >= C k log(1/(2 delta)),
```

there exists a deterministic reward sequence `x in [0,1]^(n x k)` whose
random-regret CDF `F_x` satisfies

```text
1 - F_x(c sqrt(n k log(1/(2 delta)))) >= delta.
```

Claim 17.5: for a probability law `Q` on bounded reward matrices, if

```text
E_Q[1 - F_X(u)] >= delta,
```

then some deterministic `x` satisfies `1-F_x(u)>=delta`. Lean makes the
suppressed integrability of `x |-> 1-F_x(u)` explicit.

Claim 17.6 uses a correlated-across-arms, IID-across-time clipped-normal hard
family. For `sigma>0` and

```text
Delta = sigma sqrt(((k-1)/(2n)) log(1/(8 delta))),
```

some arm `i` satisfies `P_Qi(T_i(n)<n/2)>=2 delta`.

Equation (17.8) is

```text
Rhat_n >= Delta (
  n - T_i(n)
    - sum_{t=1}^n I{exists j in [k] : X_tj in {0,1}}).   (17.8)
```

Claim 17.7: for `sigma=1/10`, `Delta<1/8`, and
`n>=32 log(1/delta)`, the probability that the clipping-count sum is at least
`n/4` is at most `delta`.

## Historical progress log on 2026-09-05

These entries preserve intermediate proof states and their then-current
blockers. They are superseded by the current acceptance table above and the
final validation report; statements below that a gate is pending are historical.

CORRECTED THEOREM 17.4 TERMINAL: focused build passed (3588 jobs) for
`exists_adversarialTable_randomRegret_gt_theorem17_4`. Constants are
`c=1/160`, `C=64`, confidence domain is `0<delta<=1/32`, and the horizon
condition is `64*k*log(1/(2delta))<=N`. The result is a deterministic
`[0,1]`-valued table and a strict random-regret tail probability at least
`delta`. Local inclusive indexing is `N=n+1`, `k=m+1`, `m>0`.
`adversarialHorizon_calibration` derives all earlier gap/clipping conditions;
`adversarialThreshold_calibration` supplies strict threshold slack. This is
the explicitly authorized corrected statement, not the false original
confidence domain. Full repository gates and artifact synchronization
remain pending; do not mark the chapter's completion contract satisfied yet.

DETERMINISTIC TABLE UPDATE: focused build passed (3588 jobs) for
`exists_adversarialTable_randomRegret_tail`. It returns an oblivious table
bounded in `[0,1]` at every time/arm, with the original policy's random
regret tail at least `delta` at threshold `gap*(n+1)/4`. The proof uses a
measurable joint regret event, bounded/integrable kernel section masses,
and the compiled first-moment extraction. It does not assume an instance
selection principle or measurable-event premise. Remaining mathematics:
calibrate source-form constants/horizon and the corrected confidence domain,
and lower the threshold strictly for the source CDF-complement event.
Repository-wide gates/status synchronization also remain incomplete.

JOINT RANDOM-REGRET UPDATE: focused build passed (3588 jobs) for
`adversarialNoiseHistoryJoint_good_event`, the exact history/action-count
conversion `adversarialHistoryActions_pullCountReal`, and
`adversarialNoiseHistoryJoint_randomRegret_tail`. The coupled hard matrix
now has random regret at least `gap*(n+1)/4` with probability at least
`delta`, under explicit `0<delta<1/8`, `gap<1/8`, and
`32*log(1/delta)<=n+1` conditions. The literal boundary count is preserved.
Remaining: derive these conditions and a strict smaller threshold from
the final horizon/confidence contract, prove the fixed-table tail is
measurable, and extract a deterministic bounded reward table. This is not
yet Theorem 17.4's calibrated strict-tail deterministic-matrix terminal.

ALL-ROUND HISTORY MARGINAL UPDATE: focused build passed for
`lintegral_adversarialNoiseHistoryKernel_succ`,
`lintegral_adversarialNoiseHistoryKernel_eq_clipped`, and
`adversarialNoiseHistoryJoint_history_marginal`. The matrix-policy joint
measure now has the exact canonical clipped history marginal at every
observed prefix (`n<N+1`). This supersedes all older history-marginal
blockers below. Remaining Theorem 17.4 obligations: joint good-event bound,
history/action-path count conversion, pathwise regret composition, justified
confidence-domain/constants calibration, and fixed-table extraction.

SUCCESSOR SLICE UPDATE: focused build passed (3588 jobs) for
`lintegral_adversarialFreshNoise_step` and
`lintegral_adversarialNoiseHistoryKernel_succ_slice`. The former integrates
fresh noise against a fixed prefix law and the original policy; the latter
uses proved future-coordinate invariance on each remaining-noise slice
to turn the next table-history observation into the canonical clipped
transition. Remaining: integrate over the rest coordinates, reconstruct
the previous noise mixture using the split integral, and induct from the
compiled initial marginal. The all-round marginal is not yet claimed.

INITIAL HISTORY MARGINAL UPDATE: focused build passed (3588 jobs) for
`adversarialNoiseHistoryJoint_history_marginal_zero`. This is the actual
initial history marginal equality, obtained by Tonelli and the full-family
reward marginal, not an assumed coupling. The successor conditional
integral formula `lintegral_adversarialTableHistoryKernel_succ` also compiles.
The all-round marginal still needs the successor noise-integration step;
the zero case alone does not close Theorem 17.4.

COORDINATE-INTEGRATION UPDATE: focused build passed for
`adversarialCenteredNoiseLaw_split`,
`adversarialNoiseHistoryKernel_split_future`, and
`lintegral_adversarialCenteredNoiseLaw_split`. These isolate one Gaussian
coordinate, prove the prefix law does not depend on a future coordinate,
and express the full noise integral as an iterated coordinate/rest integral.
Next exact target, for `n<horizon`: the `snd` marginal of
`adversarialNoiseHistoryJoint algorithm sigma gap i n` equals
`adversarialClippedHistoryLaw algorithm sigma (adversarialFullHardShift gap i) n`.
Use zero/successor recursion; in the successor step split coordinate `n+1`,
remove it from the prefix kernel, and integrate the deterministic feedback
to its Gaussian clipped arm law. This equality is still unproved.

JOINT-SPACE UPDATE: `adversarialTableHistoryKernel_prefix_congr` proves
nonanticipation with respect to table rows. `adversarialFullRewardTable`
embeds finite shared-noise matrices measurably; `adversarialNoiseHistoryJoint`
is a probability measure using the original policy conditional on that
table. `adversarialNoiseHistoryJoint_noise_marginal` identifies its noise
marginal exactly. These passed the focused build and external axiom audit
(only `propext`, `Classical.choice`, `Quot.sound`). The history marginal is
still open; a noise marginal alone does not justify importing Claim 17.6.

FULL-FAMILY AND CONDITIONAL-LAW UPDATE: focused build passed (3588 jobs)
for `adversarialFullRandomRegret_ge_boundary_eq17_8` and
`adversarialFullBoundaryCount_tail_claim17_7`, including the base-arm witness.
`adversarialTableHistoryKernel` is now a measurable Markov kernel from fixed
oblivious reward tables to observed histories. Its zero and successor
recurrences compile, and `adversarialTableStepKernel_apply` proves that
fixing a table uses the original policy and that table's deterministic
feedback. Remaining: integrate this kernel against shared Gaussian noise,
prove the observation-law marginal (not just each arm's reward marginal),
and carry out the final strict-tail and deterministic-matrix extraction.
Theorem 17.4 is not yet a compiled terminal.

CORRECTED CLAIM 17.6: `adversarialClippedHistory_pull_le_half_claim17_6`
passed the focused module build (3588 jobs). It quantifies every common
randomized history algorithm, `m+1` arms with `m>0`, `n+1` observations,
nonzero `sigma`, and `0<delta<1/8`, retaining the exact source gap tuning.
The witness includes the base instance, and the event is explicitly
`T_i <= (n+1)/2`. The proof combines expected-pull conservation, a least
alternative, the exact lifted-history KL, BH at scale `4*delta`, and the
proved clipped-history pushforward. No KL or testing bound is assumed.
This supersedes older statements that its history probability bound is open.
It does not establish the shared-noise full-matrix joint law or Theorem 17.4.
External audit `E:/Temp/Chapter17Claim177Audit.lean` passed, reporting only
`propext`, `Classical.choice`, and `Quot.sound` for the corrected claim,
gap calibration, and history KL. `git diff --check` passed. The attempted
`python tools/bandit.py check` failed in an unrelated RL module while creating
`FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretFinitePrefixCumulativeAverageRate.olean`
(258-character absolute output path). The root-import canary therefore still
cannot run because `BanditRLProof.olean` is unavailable. No full-repository
gate success is claimed; the failure is an output-file creation error, not
a Chapter 17 proof error. Its exact filesystem cause is not yet established.

USER-APPROVED ERRATUM ROUTE (2026-09-05): the user confirmed proceeding
with explicitly recorded source corrections. Claim 17.6 will use the
non-strict event `T_i(n) <= n/2`; the confidence domain will be stated
explicitly so the positive-gap logarithm is valid. Theorem 17.4's valid
confidence domain must be justified by the completed proof. The original
counterexamples remain recorded. Earlier notes requiring authorization
are historical and have now been satisfied; they are not current blockers.

FOLLOW-UP SOURCE AUDIT: Theorem 17.4's confidence range `(0,1)` includes
`delta=3/4`. At `n=1,k=2`, uniform random play has strict positive-regret
probability at most `1/2` for every deterministic reward vector. Its
displayed logarithm is negative, making the horizon condition automatic
and Lean's real-sqrt threshold zero. Thus this literal target also needs
a confidence-range correction. The arithmetic counterexample compiled.
No repaired target has been substituted without user direction.

SOURCE OBSTRUCTION: literal Claim 17.6 uses `T_i(n) < n/2` and is false
for a deterministic balanced two-arm policy at an even horizon. Each count
equals `n/2` on every path, so every candidate event is empty. The official
author PDF was rechecked on 2026-09-05 at physical page 228. A Lean external
canary proved the two-round count identity, empty event under every measure,
and contradiction with `2 delta > 0`. The whole objective cannot be marked
complete under the exact literal statement. A non-strict repair would
require an explicit change of target.

The equal-variance Gaussian KL and exact base-to-changed history information
identity compile as `klDiv_gaussianReal_common_scale` and
`klDiv_adversarialUnclipped_base_changed_history` (3588 jobs).

Full finite-horizon transport now compiles as
`adversarialClippedHistoryLaw_eq_map`; the integrated step is
`adversarialClipped_prefixStepLaw`. Pull-small probabilities transfer exactly
via `adversarialClippedHistoryLaw_pullSmall`, and
`adversarialUnclippedKernel_apply` identifies the Gaussian mean and variance.
Focused build passed (3588 jobs). Next: equal-variance Gaussian KL via a
scaling measurable equivalence and the existing unit-variance KL theorem,
then the history identity, least-arm argument, and source gap tuning.
The pre-sampled matrix/policy joint law and deterministic witness remain open.

`adversarialClippedHistoryLaw_zero` and
`adversarialClipped_historyStepLaw` now compile (3588-job focused build).
They establish initial history transport and pointwise next-pair transport.
To finish transport at arbitrary horizons, integrate the latter over the
prefix law and commute clipping with the successor history encoding.
This is still a dependency of Claim 17.6, not its probability lower bound.

The lifted policy `adversarialClipHistoryAlgorithm`, its exact action-law
evaluation, and preservation of both ENNReal and real pull counts compile.
`adversarialClippedKernel_eq_map` and `adversarialClipped_initialPairLaw`
also compile (focused module build, 3588 jobs). The remaining history
transport is the successor step for the canonical history law; the initial
pair identity alone does not close Claim 17.6.

The clipped feedback kernel and its same-policy canonical observation law
now compile as `adversarialClippedKernel` and `adversarialClippedHistoryLaw`.
`adversarialCenteredNoiseLaw_reward_marginal` proves the exact single-coordinate
pushforward from the original shared-noise matrix. Focused build passed
(3588 jobs). Full interaction-law equivalence and the Claim 17.6 history KL
bound remain open; marginal equality does not replace either obligation.

Claim 17.7 now compiles for both the absolute-noise envelope count and the
literal textbook boundary count. The new declarations are
`adversarialClippingCount_tail_claim17_7`,
`adversarialBoundaryClippingCountReal_le`, and
`adversarialBoundaryClippingCount_tail_claim17_7`.
The focused module build passed (3588 jobs). This supersedes the older
blocked Claim 17.7 entries below. Claim 17.6 and Theorem 17.4 remain open.
The stronger literal boundary-count Eq. (17.8) is now compiled as
`adversarialRandomRegret_ge_boundary_eq17_8` (focused build, 3588 jobs).
It applies to every realized noise and action path. The older
`adversarialRandomRegret_ge_eq17_8` uses the envelope count.

## Historical baseline Lean target and status fence

Target file: `BanditRLProof/LowerBounds/HighProbability.lean`.

Compiled public declarations:

```lean
LowerBounds.gaussianRandomPseudoRegret
LowerBounds.gaussianExpectedPseudoRegretReal
LowerBounds.GapOneGaussianBanditEnvironment
LowerBounds.gapOneGaussianExpectedPseudoRegretReal
LowerBounds.gapOneGaussianRandomPseudoRegret
LowerBounds.gaussianRandomPseudoRegret_ge_theorem17_1
LowerBounds.gaussianRandomPseudoRegret_ge_corollary17_2
LowerBounds.noUniformGaussianRandomPseudoRegretTail_corollary17_3
LowerBounds.integral_exp_neg_rpow_inv_le_one
LowerBounds.integral_le_scale_of_all_rpow_log_tail
LowerBounds.tailAtLeast
LowerBounds.stochasticHighProbabilityThreshold
LowerBounds.stochasticMinimaxHighProbabilityThreshold
LowerBounds.adversarialHighProbabilityThreshold
LowerBounds.exists_tailMass_ge_of_integral_ge
LowerBounds.exists_cdfTail_ge_of_integral_ge
LowerBounds.measureReal_diff_ge_delta
LowerBounds.adversarialRegretLowerExpression
LowerBounds.adversarialRegretLowerExpression_ge_quarter
LowerBounds.randomRegret_ge_quarter_of_clippingDecomposition
LowerBounds.clipUnitReward
LowerBounds.adversarialHardShift
LowerBounds.adversarialClippedGaussianReward
LowerBounds.adversarialCenteredNoiseLaw
LowerBounds.adversarialClaim17_6Gap
LowerBounds.adversarialRandomRegret
LowerBounds.adversarialRandomRegret_ge_eq17_8
```

`exists_cdfTail_ge_of_integral_ge` is the exact first-moment content of Claim
17.5, with the textbook-suppressed integrability assumption made explicit.
The threshold declarations and remaining theorems are dependency leaves.

Reserved source terminals, with no declaration claimed:

```lean
LowerBounds.adversarialRandomRegret_ge_theorem17_4
LowerBounds.clippedGaussian_pullCount_lt_half_claim17_6
LowerBounds.clippingCount_ge_quarter_le_claim17_7
```

The chapter stays `partial`. Theorem 17.1, Corollaries 17.2--17.3, Claim 17.5, the
centered shared-noise form of the clipped hard family, and construction-level
Eq. (17.8) compile. Theorem 17.4 and Claims 17.6--17.7 remain blocked.

## Exact regularity contract

- Stochastic random pseudo-regret and adversarial random regret are distinct
  random variables and must not be interchanged.
- `E^k` contains `k`-armed Gaussian bandits with gaps bounded by one. The
  source construction uses unit-variance Gaussian laws and mean vectors in
  the unit cube.
- Expected regret in Eq. (17.4) is deterministic; `Rbar_n` is random through
  pull counts. Every probability is under the history law induced by the same
  possibly randomized nonanticipating policy.
- Theorem 17.1 uses `n>=1`, `k>=2`, `B>0`, and `delta in (0,1)`. Its uniform
  expected-regret premise quantifies over every environment in `E^k`.
- KL direction is original history law to changed-environment history law;
  expected pull counts are under the original law.
- Corollary 17.2 retains its horizon-confidence side condition, the factor
  `1/2` inside the square root, and the outer factor `1/4`.
- Corollary 17.3 uses one policy for all horizons, confidence levels, and
  environments. Its exponent is a real `p in (0,1)` on `log(1/delta)` and the
  upper-tail probability is strictly less than `delta`.
- Theorem 17.4 is adversarial, concerns random regret, and produces a
  deterministic reward matrix in `[0,1]^(n x k)`. The universal constants and
  horizon condition remain explicit.
- Claim 17.5 needs a probability law on reward matrices, the Borel sigma
  algebra, and integrability of `x |-> 1-F_x(u)`. The compiled generic theorem
  does not assert that a future bandit CDF construction supplies integrability.
- Claim 17.6's reward coordinates are correlated across arms at a fixed time,
  but each arm is IID across time. The policy interaction law must preserve
  the source conditional policy kernel.
- Claim 17.7 needs the exact clipping map, Gaussian tails, a union/count
  argument, `sigma=1/10`, `Delta<1/8`, and `n>=32 log(1/delta)`.
- Equation (17.8) is proved pathwise for the clipped shared-noise construction
  and the actual max-over-fixed-arms adversarial random regret. The older
  quarter-horizon theorem remains a reusable downstream algebra lemma.

## Historical semantic and analytic blockers (discharged or explicitly corrected)

Theorem 17.1 reuses the compiled same-policy adaptive-history divergence
decomposition of Lemma 15.1 and preserves the original-law expected pull
count. Corollary 17.2 closes by its expectation contradiction. Corollary 17.3
now compiles by integrating the strict all-confidence tail, applying the Gamma
bound, and calibrating two confidence levels plus a sufficiently large horizon
against Theorem 17.1.

Theorem 17.4 is described only at a high level in the textbook and delegates
details to Gerchinovitz--Lattimore (2016). A source-faithful proof needs the
clipped-normal reward-matrix law, the associated policy-history law, the
relative-entropy calculation of Claim 17.6, the clipping concentration of
Claim 17.7, and the pathwise reward comparison in Eq. (17.8). The external
paper is route evidence, not a local theorem.

These are two explicit open-problem proposals. They are not reasons to
replace randomized policies by deterministic maps, assume armwise
independence in the adversarial hard family, reverse KL, change random
pseudo-regret into expected regret, or weaken a probability/constant.

## Historical proof obligations (superseded by current acceptance evidence)

- [x] Official edition, book/chapter DOI, stable author PDF, section titles,
  and three-way pagination are recorded.
- [x] Theorem 17.1, Corollaries 17.2--17.3, Theorem 17.4, Claims 17.5--17.7,
  and Eq. (17.8) are frozen with exact quantifiers, event directions,
  constants, and threshold placement.
- [x] Existing Chapters 14--16 and Mathlib first-moment/outer-measure APIs are
  audited.
- [x] Exact tail-event and stochastic/adversarial threshold interfaces compile.
- [x] Claim 17.5's first-moment content compiles with integrability explicit.
- [x] The probability subtraction combining Claims 17.6--17.7 compiles.
- [x] The quarter-horizon algebra following Eq. (17.8) compiles.
- [x] Lemma 15.1's source-faithful stochastic-history information identity
  and the Chapter 17 tail-event consumer compile.
- [x] Theorem 17.1 and Corollary 17.2 compile.
- [x] Corollary 17.3 compiles.
- [x] The clipped shared-noise path construction, its IID Gaussian noise law,
  exact Claim 17.6 gap tuning, and construction-level Eq. (17.8) compile.
- [ ] Claims 17.6--17.7 and Theorem 17.4 compile.
- [ ] Current-run root import, full Lean/Tests/harness gate, expanded typed
  canary, axiom reports, placeholder scan, exports, retrieval indexes, site
  build/check, browser QA, and read-only review are all recorded below.
- [ ] Current PR CI, Pages deployment, and live checks pass. These remain
  post-push gates and must not be inferred from the historical baseline.

## Historical local verification evidence (2026-09-04)

- `lake build BanditRLProof.LowerBounds.HighProbability`: passed with 3588
  jobs after the final stochastic and adversarial edits.
- A focused external canary checks the six new public surfaces and prints
  axioms for nine representative Chapter 17 declarations; every report is
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- The lean-verified site build passed with 604 modules, 8259 declarations,
  zero placeholders, and 447 foundations. `check_site.py` passed with 658
  pages, 113 highlights, 18 Mermaid blocks, 9026 Lean source links, and valid
  internal links, README links, MathJax fallbacks, and Pages workflow.
- Chrome desktop QA at 1280x900 renders the updated status, source map, and
  navigation. A real 390x844 device-emulation pass reports equal document
  client/scroll widths (`390/390`), seven rendered MathJax containers, zero
  broken images, and compiled Theorem 17.1 / Eq. (17.8) correspondence rows.
  The Codex in-app browser container separately timed out while attaching;
  that environment issue is not represented as a site failure or pass.
- Native `lake build`, `lake build Tests.TextbookPartIVChapter17Canary`, and
  `python tools/bandit.py check` all reach the same pre-existing unrelated RL
  module and then fail to create its 155-character basename `.olean` at a
  258-character destination path. The focused Chapter 17 module has no failure;
  authoritative Linux PR CI is the required full root/Tests/harness gate.
- The current read-only review records no unresolved P0--P2 in the compiled
  slice and preserves the then-current four terminal blockers in
  `reviews/2026-09-04-textbook-part-iv-chapter-17-high-probability-lower-bounds-closure.md`.
- The proof-graph exporter compiles, and the complete Python harness suite
  passes 400 tests with seven expected skips.

## Historical baseline local verification evidence (2026-08-16/17)

- `lake build BanditRLProof.LowerBounds.HighProbability`: passed, 2654 jobs.
- The public `BanditRLProof` root and expanded Chapter 17 canary compile through
  the worktree's `X:` short-path mapping. Axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `python3 tools/bandit.py check` reaches the full root build but Windows fails
  to create an existing unrelated long-named RL object file because of
  MAX_PATH. No Chapter 17 target fails; authoritative Linux CI passed below.
- `python3 website/scripts/build_site.py --lean-verified`: passed with 563
  modules, 7415 declarations, and zero placeholders.
- `python3 website/scripts/check_site.py`: passed with 591 pages, 14 Mermaid
  blocks, and 16037 Lean source links.
- Desktop browser QA at 1280x720 found `PARTIAL`, all seven MathJax displays,
  the complete Part IV navigation, no document-level horizontal overflow,
  and local scrolling on long formula/table/code containers.
- Independent read-only review initially found two P3 evidence/canary gaps;
  both were corrected, and re-review found no unresolved P0--P3. See
  `reviews/2026-08-17-textbook-part-iv-chapter-17-high-probability-lower-bounds-spine.md`.

## Historical baseline remote verification evidence (2026-08-17)

- PR #17 passed `Lean and documentation / build` in run `31975031469`, job
  `95233089033` (23m13s), and was merged without a direct push to `main`.
- Merge commit: `eb41d9607cc5a46aa208572e3a6f05f291c82798`.
- Authoritative-main run `31976153611` passed: build job `95235875154`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 22m24s; deployment job `95238317293` passed in 12s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-17-high-probability/>.
  Desktop 1280x720 and native mobile 390x844 inspections confirmed the
  `2026-08-16T22:44:25+00:00` build, overall `PARTIAL` chapter status, CUP
  print pp. 185--190 and physical-PDF pp. 224--230, all seven MathJax
  displays, the compiled Claim 17.5/threshold/event-subtraction/Eq. (17.8)
  algebra slice, the then-blocked Theorem 17.1 / Corollaries 17.2--17.3 /
  Theorem 17.4 terminals, and zero broken images. Browser metrics found no
  document-level horizontal overflow at 390x844 (`375/375` client/scroll
  width); the mobile TOC/sidebar and long MathJax displays retain intentional
  local horizontal scrolling.

This remote acceptance is retained only as evidence for the earlier scoped
dependency slice. It is not evidence for the declarations added on 2026-09-04.
The current chapter remains `partial` for the exact blockers listed above.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| exact threshold surfaces | `Real.sqrt`, `Real.log`, `min`, natural casts | transcribe all constants and grouping before later tuning algebra | positivity remains terminal-side; `alternativeArms=k-1` at consumer | compiled project-local definitions |
| Claim 17.5 | `MeasureTheory.exists_integral_le` | first-moment method on `x |-> 1-F_x(u)` | probability measure and integrability | compiled exact source claim |
| good-event subtraction | `le_measureReal_diff`, real linear arithmetic | subtract the clipping-bad event from the pull-small event | finite measure; outer-measure sets need not be measurable | compiled project-local |
| Eq. (17.8) construction and quarter algebra | clipped monotonicity, finite sums, ordered-field multiplication | prove the distinguished-arm comparison pathwise, then use `T_i<=n/2` and clipping count `<=n/4` | nonnegative gap; shared noise across arms | compiled project-local |
| stochastic terminal | Chapter 14 BH plus Chapter 15 history KL | least-pulled arm, one-coordinate Gaussian change, exact tuning | same stochastic policy and original-law pulls | compiled Theorem 17.1 and Corollary 17.2 |
| Corollary 17.3 tail integration | `Integrable.integral_eq_integral_meas_le`, `integral_comp_mul_left_Ioi`, `integral_exp_neg_rpow_inv_le_one` | rescale the all-confidence tail, derive the uniform first moment, calibrate two confidence levels and a large horizon, then contradict Theorem 17.1 | integrable nonnegative random pseudo-regret; real `p in (0,1)` | compiled exact source terminal |
| clipped-normal law | `Measure.pi`, Gaussian map/clipping | construct the correlated-across-arm reward matrix from one IID centered path; still connect it to policy interaction | Borel measurability; IID across time only | path law compiled; interaction law open |
| Claim 17.6 | relative entropy and history law | least-pulled arm plus changed law and source entropy calculation | exact `Delta`, same policy, finite KL | connected blocker |
| Claim 17.7 | Gaussian tail/concentration and finite unions | bound each clipping indicator and its count | `sigma=1/10`, `Delta<1/8`, exact horizon condition | open concentration leaf |
| Theorem 17.4 | Claims 17.5--17.7 and Eq. (17.8) | combine good event, calibrate `Delta`, then first moment | deterministic witness matrix and CDF law | blocked source terminal |

## Retrieval cards

- Mathlib: `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`,
  `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-INDEPENDENCE`, and `MLIB-PROBABILITY-SUBGAUSSIAN`.
- Local compiled dependencies: Chapter 14 `bretagnolleHuber`; Chapter 15
  `klDiv_gaussianReal_one`; Chapter 13 `exists_leastExploredAlternative`.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-LS-2020-THM-17-1-STOCHASTIC-TAIL`,
  `TXT-LS-2020-COR-17-2-STOCHASTIC-MINIMAX-TAIL`,
  `TXT-LS-2020-COR-17-3-UNIFORM-TAIL-IMPOSSIBILITY`,
  `TXT-LS-2020-THM-17-4-ADVERSARIAL-TAIL`, and
  `TXT-LS-2020-CLAIMS-17-5-17-7`.
- Scenario: `SCN-STOCHASTIC-FINITE`, `SCN-ADVERSARIAL-FINITE`.
- Paper route evidence only: `PPR-GERCHINOVITZ-LATTIMORE-2016-REFINED-LOWER-BOUNDS`.
- LML: none promoted.
- Proof weapon route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- A threshold definition is not a tail lower-bound theorem.
- The compiled Claim 17.5 adapter does not construct the reward-matrix law,
  the policy interaction law, or its CDF.
- Probability subtraction and Eq. (17.8) do not prove Claims 17.6--17.7.
- The stochastic random pseudo-regret is not adversarial random regret and is
  not deterministic expected regret.
- Theorem cards, open-problem proposals, and the NeurIPS paper remain route
  evidence only.
- If the terminals remain blocked, preserve their exact contracts and publish
  only Claim 17.5 plus reusable compiled leaves and explicit blockers.
