# Textbook Part IV Chapter 16 instance-dependent lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Formalize the source-faithful instance-dependent lower-bound route in
Lattimore--Szepesvári, *Bandit Algorithms* (2020), Chapter 16. The exact
terminals are Definition 16.1, Theorem 16.2, Lemma 16.3, and Theorem 16.4.
The compiled spine freezes the consistency quantifiers, the extended-real
`d_inf` interface, the exact unit-Gaussian Table 16.1 formula, and the
subpolynomial log-growth step. It also compiles the same-policy one-arm
history-KL specialization, the finite arm-law mean-to-gap producer, exact
Lemma 16.3, and exact finite-time Gaussian Theorem 16.4. Theorem 16.2 also compiles, including every extended-real information branch
and finite-count Fatou aggregation.

2026-09-05 verified progress: the near-infimum law selector, complete infinite
infimum characterization, finite-mean single-arm replacement, product-class
closure, and `exists_confusingEnvironment_lt` now compile and pass the
Chapter 16 canary with only the standard axiom set. The exact per-arm and regret terminals now also compile and pass the canary.
The final gate and delivery audit remains in progress.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- Book DOI: <https://doi.org/10.1017/9781108571401>.
- Chapter DOI: <https://doi.org/10.1017/9781108571401.021>.
- CUP chapter page:
  <https://www.cambridge.org/core/books/abs/bandit-algorithms/instancedependent-lower-bounds/C6CDB8FD64DF85192F18CC0811667470>.
- Official author PDF: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 16, CUP print pp. 177--184; author-online
  page labels 206--214; physical PDF pp. 215--223.
- §16.1 Asymptotic Bounds: CUP pp. 177--179; author-online pp. 207--208;
  physical PDF pp. 216--217. Definition 16.1 and Theorem 16.2.
- §16.2 Finite-Time Bounds: CUP p. 180; author-online pp. 209--210;
  physical PDF pp. 218--219. Lemma 16.3 and Theorem 16.4.
- §16.3 Notes: CUP p. 181; author-online p. 210; physical PDF p. 219.
- §16.4 Bibliographic Remarks: CUP p. 181; author-online p. 211;
  physical PDF p. 220.
- §16.5 Exercises: CUP pp. 181--184; author-online pp. 211--214;
  physical PDF pp. 220--223.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` plus Chapter 16 cards below.
- Scenario card: `SCN-STOCHASTIC-FINITE`.

The CUP print pagination, author-online page labels, and physical PDF pages are
edition-specific fields. The author PDF explicitly warns that its pagination
does not match the print edition, so no constant page offset is inferred.

## Frozen source targets

Definition 16.1 calls a policy `pi` consistent over an environment class `E`
when, for every `nu in E` and every real `p>0`,

```text
lim_{n -> infinity} R_n(pi,nu) / n^p = 0.                 (16.1)
```

Let `E=M_1 x ... x M_k` be an unstructured class whose component laws have
finite means. For a law `P in M` with mean below `muStar`, define

```text
d_inf(P,muStar,M) = inf { D(P,P') : P' in M, mean(P') > muStar }.
```

Theorem 16.2 says that every policy consistent over `E` satisfies, for every
`nu=(P_i)` in `E`,

```text
liminf_{n -> infinity} R_n(pi,nu)/log(n)
  >= c*(nu,E)
   = sum_{i: Delta_i>0} Delta_i / d_inf(P_i,muStar,M_i).  (16.2)
```

The KL direction is always original law `P_i` to confusing alternative
`P_i'`. The proof changes only suboptimal arm `i` to a law whose mean is
strictly above the original optimal mean and uses
`A={T_i(n)>n/2}`. Expected pulls are under the original environment.

Lemma 16.3 considers environments differing only at arm `i`, where `i` is
suboptimal in `nu` and uniquely optimal in `nu'`. With
`lambda=mu_i(nu')-mu_i(nu)`, it gives the finite-time pull-count bound

```text
E_nu[T_i(n)] >=
  (log(min{lambda-Delta_i(nu),Delta_i(nu)}/4)
    + log(n) - log(R_n(nu)+R_n(nu')))
  / D(P_i,P_i').                                         (16.4)
```

Theorem 16.4 specializes to unit-variance Gaussian bandits. For a nonempty set
`N` of horizons, `C>0`, `p in (0,1)`, and a policy satisfying
`R_n(pi,nu')<=C n^p` for every `n in N` and every coordinatewise local
alternative `nu' in E(nu)`, it states that for `epsilon in (0,1]` and `n in N`,

```text
R_n(pi,nu) >= 2/(1+epsilon)^2
  * sum_{i:Delta_i>0}
      (((1-p)log(n)+log(epsilon*Delta_i/(8C)))/Delta_i)^+. (16.5)
```

## Lean target and status fence

Target file: `BanditRLProof/LowerBounds/InstanceDependent.lean`.

Compiled public declarations:

```lean
LowerBounds.IsConsistentRegret
LowerBounds.IsConsistentPolicyOver
LowerBounds.IsConsistentRegret.add
LowerBounds.IsConsistentRegret.eventually_add_le_rpow
LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le
LowerBounds.divergenceInfimum
LowerBounds.divergenceInfimum_le
LowerBounds.parametricDivergenceInfimum
LowerBounds.parametricDivergenceInfimum_le
LowerBounds.unitGaussianDivergenceInfimum
LowerBounds.unitGaussianDivergenceInfimum_le_perturbed
LowerBounds.unitGaussianDivergenceInfimum_ge
LowerBounds.unitGaussianDivergenceInfimum_eq
LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_mul_of_only_arm_changed
LowerBounds.oneArmMajorityPullEvent
LowerBounds.measurableSet_oneArmMajorityPullEvent
LowerBounds.bretagnolleHuberScale_expectedPulls_mul_armKL_le_majorityErrors
LowerBounds.bretagnolleHuberScale_mul_eq_exp
LowerBounds.exp_testing_bound_of_majority_regret_bounds
LowerBounds.expectedPullCount_ge_log_regret_of_exp_testing_bound
LowerBounds.finiteHistoryGapPseudoRegret
LowerBounds.canonicalGapExpectedPseudoRegret
LowerBounds.measurable_finiteHistoryGapPseudoRegret
LowerBounds.finiteHistoryGapPseudoRegret_ne_top
LowerBounds.finiteHistoryGapPseudoRegret_toReal
LowerBounds.sum_canonicalRealizedExpectedPullCountThrough_general
LowerBounds.canonicalRealizedExpectedPullCountThrough_ne_top
LowerBounds.canonicalGapExpectedPseudoRegret_eq_sum_expectedPulls
LowerBounds.canonicalGapExpectedPseudoRegret_ne_top
LowerBounds.canonicalGapExpectedPseudoRegretReal
LowerBounds.oneArmMajority_forces_gapPseudoRegret
LowerBounds.oneArmMajority_compl_forces_gapPseudoRegret
LowerBounds.oneArmMajority_probability_charge_le_expectedPseudoRegret
LowerBounds.oneArmMajority_compl_probability_charge_le_expectedPseudoRegret
LowerBounds.expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed
LowerBounds.FiniteMeanBanditEnvironment
LowerBounds.FiniteMeanBanditEnvironment.gap
LowerBounds.FiniteMeanBanditEnvironment.mean_eq_of_armLaw_eq
LowerBounds.oneArmMeanChange_produces_gap_contract
LowerBounds.oneArmMeanIncrease_sub_gap_eq_changedMargin
LowerBounds.UnitVarianceGaussianBanditEnvironment
LowerBounds.chapter16GaussianChangedEnvironment
LowerBounds.chapter16GaussianChangedEnvironment_armKL
LowerBounds.canonicalGapExpectedPseudoRegretReal_eq_sum_expectedPulls
LowerBounds.expectedPullCount_ge_log_regret_changeOfMeasure
LowerBounds.gaussianExpectedPullCount_ge_finiteTimeInstanceDependent
LowerBounds.gaussianExpectedRegret_ge_finiteTimeInstanceDependent
```

Compiled asymptotic source terminals:

```lean
LowerBounds.consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf
LowerBounds.consistentPolicy_liminf_expectedRegret_div_log_ge
```

All four main-text items are compiled, including both Theorem 16.2
declarations above. Current full repository and delivery gates remain separate.

## Exact regularity contract

- The class in Theorem 16.2 is unstructured: a Cartesian product of per-arm
  distribution classes. Structured-bandit information constraints are not
  silently included.
- Component laws are probability measures with finite real means.
- Consistency quantifiers are `forall nu in E, forall p>0`; `p` is real, not
  a fixed exponent or a natural number.
- Regret is expected pseudo-regret and is nonnegative. The generic compiled
  consistency predicate does not hide nonnegativity as a field.
- `d_inf` is extended-real. Empty confusing-alternative sets yield `infinity`;
  zero and infinite information costs require explicit branches before real
  division or reciprocal manipulation.
- Confusing alternatives have mean strictly greater than `muStar`, not merely
  greater than or equal to it.
- KL direction is original `P_i` to alternative `P_i'`; expectations in the
  pull constraint are under the original environment.
- The history laws use the same possibly randomized nonanticipating policy.
- Theorem 16.2 uses a `liminf`; the proof's log-growth step must not be
  replaced by convergence without proving it.
- Lemma 16.3's logarithm arguments are positive because the original gap and
  the alternative optimality margin are positive. A real-valued division
  branch also needs finite positive arm KL.
- Theorem 16.4 uses unit-variance Gaussian arms, a nonempty horizon set,
  `C>0`, `p in (0,1)`, `epsilon in (0,1]`, and the positive part in Eq. (16.5).

## Current compiled semantic route

The finite-mean product-environment layer now ties every arm mean to its
Bochner integral, proves unchanged arm laws have unchanged means, and produces
the exact original gap, changed optimality margin, and alternative-gap
comparison. This closes Lemma 16.3, including finite and infinite KL branches.
The unrestricted unit-variance Gaussian layer then performs the
`(1+epsilon) Delta_i` shift, proves local-class membership and exact arm KL,
normalizes the published logarithm, takes positive parts, and sums the per-arm
bounds to close Theorem 16.4.

Theorem 16.2 now constructs class-preserving alternatives, applies consistency
at exact n-pull horizons, and aggregates costs with `ENNReal.inv_sInf`.
Empty, zero, finite, and infinite information branches retain their meanings.
Finite-count Fatou assembles the regret sum in the required direction.

## Compiled event-to-regret implementation contract

The compiled production leaf is not an assumed scalar regret. It uses the
canonical finite-history law together with a nonnegative per-arm gap vector,
defines realized pseudo-regret as the finite sum of `gap * pullCount`, and
defines expected pseudo-regret by a lower integral under the same arm kernel
and randomized history policy. The two pathwise and integrated producers are:

- on `oneArmMajorityPullEvent`, the original environment pays at least
  `(lastRound + 1) * gap(changedArm) / 2` pathwise;
- on its complement, an alternative for which every non-changed arm has gap
  at least `changedMargin` pays at least
  `(lastRound + 1) * changedMargin / 2` pathwise.

`sum_finiteHistoryPullCountReal`,
`ofReal_mul_probReal_le_lintegral_of_event`, and the canonical realized
expected-pull interface are the local APIs. The proofs expose gap
nonnegativity, positive original gap, positive changed margin, the same history
event, and the exact inclusive horizon. The combined theorem
`expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed` discharges the
finite-positive-KL scalar route with the exact factor `1/4`; the compiled
finite-mean source bridge upgrades it to Lemma 16.3, and the Gaussian consumer
upgrades that terminal to Theorem 16.4.

## Proof obligations

- [x] Official edition, book/chapter DOI, stable author PDF, section titles,
  and three-way pagination are recorded.
- [x] Definition 16.1, Theorem 16.2, Lemma 16.3, and Theorem 16.4 are frozen
  with exact quantifiers, KL direction, event orientation, constants, and
  positive-part placement.
- [x] Existing Chapter 14--15 and Mathlib asymptotic/infimum APIs are audited.
- [x] Exact generic consistency and `d_inf` interfaces compile.
- [x] Sum closure, eventual every-power domination, and eventual log-ratio
  dependency leaves compile.
- [x] Candidate `d_inf` bounds and the unit-Gaussian perturbed-alternative KL
  cost compile.
- [x] Exact Gaussian `d_inf` equality compiles for the source's strictly
  suboptimal unit-variance Gaussian branch.
- [x] Lemma 15.1's source-faithful same-policy history KL identity compiles;
  the Chapter 16 one-arm KL specialization, measurable majority event,
  Bretagnolle--Huber information inequality, and scalar log assembly compile.
- [x] Canonical gap-times-pull-count expected pseudo-regret, both exact
  majority-event charges, and the finite-positive-KL factor-`1/4` conditional
  logarithmic consumer compile.
- [x] Finite arm-law integral means and certified optima are identified with
  the compiled original/changed gap vectors.
- [ ] Theorem 16.2's per-arm and regret `liminf` terminals compile.
- [x] Lemma 16.3 and Theorem 16.4 compile with their exact source constants,
  local-class quantifiers, horizon set, and positive-part placement.
- [x] The focused Chapter 16 canary compiles the new gap-event/regret slice and
  representative axiom reports use only the baseline logical axioms.
- [x] The current fifteen-declaration extension passes refreshed root imports,
  Tests, scans, full harness, exports, indexes, site, browser, and the scoped
  independent review recorded in
  `reviews/2026-08-22-textbook-part-iv-chapter-16-event-regret-extension.md`.
- [x] The preceding twenty-declaration Gaussian-equality and one-arm
  event-information extension passed PR #38, authoritative-main Actions,
  Pages deployment, and live desktop/mobile checks.
- [x] The current fifteen-declaration gap-event/regret extension passed PR #40,
  authoritative-main Actions run `32554151109`, Pages deployment, and live
  checks at merge `08c1470`.

## Historical remote verification evidence

The earlier fifteen-declaration extension was remotely verified with its
then-blocked source terminals. This history is not evidence for the new PR.

- PR #40 passed `Lean and documentation / build` in run `32553086838` and the
  result-free lifecycle probe in run `32553086905`; it was merged through the
  PR without a direct push to `main`.
- Merge commit: `08c147088c9ae77f3487b6a01fb46637798b2742`.
- Authoritative-main run `32554151109` passed: build job `96985590260`
  completed Lean, Tests, the lean-verified site, site checks, and Pages artifact
  upload; deployment job `96987991435` passed.
- The live manifest is clean, public, and Lean-verified at the same commit:
  580 modules, 7,754 scanner declarations, zero placeholders, and 74
  milestones (63 compiled, 6 partial, 4 blocked, 1 planned).
- The live Chapter 16 page shows the fifteen compiled gap-event/regret
  declarations, retains Lemma 16.3 and Theorems 16.2/16.4 as blocked, and links
  `expectedPullCount_ge_log_gapPseudoRegret_of_only_arm_changed` to the
  merge-pinned source at `BanditRLProof/LowerBounds/InstanceDependent.lean#L721`.

### Verified twenty-declaration predecessor

- PR #38 passed `Lean and documentation / build` in run `32545603658`, job
  `96963381949` (25m12s), and the result-free lifecycle probe in run
  `32545603656`, job `96963381807` (19s). It was merged through the PR without
  a direct push to `main`.
- Merge commit: `359fb6a2b8a85854cb9228f3f459568e62ae47b1`.
- Authoritative-main run `32546802426` passed: build job `96966584799`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 24m42s; deployment job `96969660988` passed in 9s.
- The live manifest is clean, public, and Lean-verified at the same commit:
  580 modules, 7,739 scanner declarations, zero placeholders, and 73
  milestones (62 compiled, 6 partial, 4 blocked, 1 planned).
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-16-instance-dependent/>.
  Desktop and 390x844 checks found no document-level horizontal overflow; the
  704px Lean correspondence table scrolls only inside its labelled 341px
  region. The page shows twenty compiled dependency declarations and retains
  Lemma 16.3 and Theorems 16.2/16.4 as blocked. The compiled
  `unitGaussianDivergenceInfimum_eq` card links to the merge-pinned source at
  `BanditRLProof/LowerBounds/InstanceDependent.lean#L202`.

### Historical verification for the older slice

- PR #15 passed `Lean and documentation / build` in run `31966790756`, job
  `95213073705` (20m40s), and was merged without a direct push to `main`.
- Merge commit: `7b3dd86559384f392691b9b4c3ccf85d4b0b1670`.
- Authoritative-main run `31967845116` passed: build job `95215621768`
  completed Lean, Tests, the lean-verified site, site checks, and Pages
  artifact upload in 22m58s; deployment job `95218324472` passed in 9s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-16-instance-dependent/>.
  Desktop 1280x720 and mobile 390x844 inspections confirmed the
  `2026-08-16T19:54:25+00:00` build, overall `PARTIAL` chapter status, CUP
  print pp. 177--184 and physical-PDF pp. 215--223, the compiled consistency
  and `d_inf` dependency slice, the blocked Theorem 16.2 / Lemma 16.3 /
  Theorem 16.4 terminals, and zero broken images. Chrome runtime metrics found
  no document-level horizontal overflow at 390x844 (`390/390` client/scroll
  width); only the intended local TOC and MathJax containers scroll.

That earlier remote acceptance applies only to the older consistency,
asymptotic-helper, and candidate-`d_inf` slice. PR #38 and authoritative-main
run `32546802426` verify the then-current 20-declaration extension. The chapter
remains `partial`, and all three source terminals retain their blocked status.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| consistency closure and power domination | `Tendsto.add`, `eventually_lt_const`, `Real.rpow_pos_of_pos` | add normalized limits, then clear an eventually positive denominator | positive real exponent; natural horizon eventually nonzero | compiled project-local |
| log-growth adapter | `Real.log_le_log`, `Real.log_rpow`, positive division | convert eventual power domination into an eventual log-ratio inequality | positive regret sum; horizon greater than one | compiled project-local |
| distribution-class `d_inf` | complete-lattice `sInf`, Chapter 14 extended-real KL | retain empty, zero, finite, and infinite branches | measurable reward space; explicit mean functional and class membership | compiled project-local interface |
| parameterized `d_inf` candidate | `sInf_le`, Gaussian arm KL | insert a strictly better alternative and preserve KL direction | strict mean improvement | compiled project-local |
| Gaussian exact `d_inf` | preceding candidate plus lower bound and limit/infimum approximation | squeeze positive perturbations to the strict boundary | original mean below target; extended-real conversion | compiled project-local |
| history information constraint | compiled Chapter 15 history law and Chapter 14 BH | specialize Lemma 15.1 to one changed arm and the exact majority event | same stochastic policy; first-law expectation | compiled project-local |
| event-to-regret producers | canonical finite-history law and gap-times-pull-count pseudo-regret | bound the original and changed majority-event errors by exact charges and apply the factor-`1/4` logarithmic consumer | nonnegative gap vectors, positive original gap and changed margin, source horizon convention | compiled project-local conditional interface |
| source mean-to-gap bridge | finite arm-law integral means and certified optima | identify the canonical gap vectors with the source environments' actual mean gaps | finite means; original/changed optimal-arm certificates | compiled project-local |
| asymptotic terminal | finite-time information inequality plus consistency log leaf | divide by log horizon and take liminf | positive gap/information; zero/infinite branches | compiled source terminal |
| finite-time Gaussian terminal | Lemma 16.3, Gaussian KL, regret decomposition | choose mean shift `Delta_i(1+epsilon)`, sum positive parts | exact local class and horizon quantifiers | compiled source terminal |

## Retrieval cards

- Mathlib: `MLIB-ASYMPTOTICS`, `MLIB-REAL-LOG-SQRT`,
  `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-ORDER-ALGEBRA`, measure KL and complete
  lattice `sInf` APIs.
- Local compiled dependencies: Chapter 14 `bretagnolleHuber`; Chapter 15
  `relativeEntropy`, `klDiv_gaussianReal_one`,
  `banditHistoryRelativeEntropy_eq_expectedPulls_sum`, and the current
  Gaussian law.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-LS-2020-DEF-16-1-CONSISTENCY`, `TXT-LS-2020-THM-16-2-ASYMPTOTIC`,
  `TXT-LS-2020-LEMMA-16-3-FINITE-TIME`, and
  `TXT-LS-2020-THM-16-4-GAUSSIAN-FINITE-TIME`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none promoted.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- A generic `Tendsto` or `sInf` leaf is not a bandit lower-bound terminal.
- The exact Gaussian `d_inf` row is a parametric distribution-level theorem,
  not Theorem 16.2's full bandit `liminf` conclusion.
- Lemma 16.3 and Theorem 16.4 do not by themselves supply Theorem 16.2's
  near-infimum alternatives or extended-real `liminf` branches.
- Theorem cards and source prose remain route evidence only.
- If the terminals remain blocked, preserve their exact contracts and publish
  only compiled reusable leaves plus the blockers. Do not restrict the policy
  to a deterministic map, reverse KL, weaken strict alternative optimality, or
  delete the consistency quantifiers.
