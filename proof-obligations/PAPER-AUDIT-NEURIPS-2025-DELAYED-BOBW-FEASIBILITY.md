# Proof obligations: NeurIPS 2025 delayed-feedback BoBW feasibility

| Leaf | Target | Dependencies searched | Route | Status |
| --- | --- | --- | --- | --- |
| `DELAYED-BOBW-FEEDBACK-AVAILABILITY-PARTITION` | exact strict-availability partition and cardinality | `MLIB-FINSET-SUMS`; local range/filter wrappers | complementary filters inside `Finset.range t` | compiled |
| `DELAYED-BOBW-MISSING-COUNT-SURFACE` | action-time outstanding count, finite maximum, and pointwise bounds | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`; `Finset.sup` | finite prefix supremum; keep end-of-round `sigma` bridge separate | compiled |
| `DELAYED-BOBW-SIGMA-INDEX-BRIDGE` | paper one-based/end-of-round missing count equals the reindexed zero-based action-time outstanding count | `Finset.range`, filtered-cardinality wrappers, natural-order arithmetic | map paper round `s + 1` to zero-based `s`; prove `t < (s+1)+d` iff `not (s+d<t)` | compiled |
| `DELAYED-BOBW-SAME-ALGORITHM-REGIME-CONTRACT` | one algorithm/initialization/tuning/information/comparator identity feeding both regime endpoints | local generated-policy contracts; source Theorems 4.1 and 5.1 | generic shared-field structure and instantiated endpoint predicates | compiled interface; Delayed SAPO and endpoints open |
| `DELAYED-BOBW-CAUSAL-ACTION-TIME-VIEW` | expose past actions and only losses satisfying the source strict-availability predicate | local history interfaces; source Section 2 and Algorithm 5 | option-valued pre-action view plus observation-equivalence theorem for every typed decision rule | compiled interface; randomized Delayed SAPO kernel open |
| `DELAYED-BOBW-NEWLY-OBSERVED-PROCESSING` | set-level content of Algorithm 5's `B(t) \ S` loop | `Finset.sdiff`, disjointness, monotone finite prefixes; source Algorithm 5 lines 2--4 | prove availability monotonicity and exact update after processing all new arrivals | compiled set invariant; sequence order and BSC updates open |
| `DELAYED-BOBW-ACTIVE-EQUAL-ALLOCATION` | Algorithm 5 line 15 residual mass divided equally among active arms | finite real sums, active/inactive partition, field normalization | define the full probability vector and prove coordinate nonnegativity plus total mass one | compiled allocation leaf; EAP bounds supplying inactive hypotheses open |
| `DELAYED-BOBW-OPTIMAL-ARM-SURVIVAL` | Algorithm 5 lines 7--8 and the deterministic core of Lemma D.9: an optimal arm satisfying an explicit confidence certificate is not eliminated | real absolute-value interval, strict line-7 test, finite-set difference; source Lemma D.9 | package the exact elimination snapshot, derive the empirical upper inequality, and prove post-elimination nonemptiness | compiled deterministic implication; recursive full Lemma D.9 open |
| `DELAYED-BOBW-GOOD-EVENT-D9-PROJECTION` | derive `muStar <= ucbStar` from both source upper-confidence surfaces and bound optimal-arm elimination by the complement of the elimination good event | finite infimum, `min`, event inclusion, measure monotonicity; source Definition D.1 and Lemma D.9 | package the elimination slice, construct the survival certificate, and expose a failure-budget consumer | compiled projection/consumer; full event and D.2--D.7 component producers open |
| `DELAYED-BOBW-D8-D9-ASSEMBLY` | combine the six D.2--D.7 failure components into Corollary D.8's `9/T` budget and transport it through D.9 survival | finite outer-measure union, source-exact three `2/T` and three `1/T` shares, complement inclusion | name the six failure events, prove the exact source budget sum, and compose an explicit full-event projection with optimal-arm survival | compiled union/composition; six concentration proofs and semantic projection remain open |
| `DELAYED-BOBW-D10-D12-GAP-ORDERING-AUDIT` | audit the width/gap chain used by Appendix Lemma D.10 and expose both the displayed four-edge route and a conditional same-snapshot factor-20 skeleton for Lemma D.12 / main-text Lemma 4.2 | `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`; source empirical-width definition, Algorithm 5 line-7 snapshot, and physical PDF pp. 26--27 | prove width antitonicity and a literal `T=4` reverse-direction witness; derive the eliminated-arm lower gap; prove the exact small-count width lower bound; consume a large/small-count branch certificate and an explicit same-prefix factor-ten edge; retain the conditional four-edge consumer for comparison | compiled diagnostic and conditional consumers; a downstream D.1 processed-prefix producer and trace-summary adapter supply algebraic inputs conditionally, while the generated state and unconditional D.10/D.12 remain open |
| `DELAYED-BOBW-D1-ACTIVE-COUNT-TO-WIDTH-PRODUCER` | derive the same-prefix D.10 width inputs and repaired D.12 factor-20 conclusion from Algorithm 5 line-15 source-time allocations plus the exact D.1 count clause | `delayedSAPOProbability_of_active`; source width; finite sums; real log/sqrt; recursive empirical UCB definition | record an ordered source-time allocation/action ledger; derive equal active-arm pull mass; prove `n_j >= n_i/4 - 6 log T`; split at `192 log T`; produce factor three, factor ten, current-UCB, and the existing same-snapshot consumer inputs | compiled deterministic producer and conditional gap theorem; a trace-summary adapter now constructs the ledger certificate, but Algorithm-5 generation and D.4 probability remain open, so D.10/D.12/Lemma 4.2 are not complete |
| `DELAYED-BOBW-PROCESSED-TRACE-SUMMARY-ADAPTER` | construct the processed-prefix certificate from a source-shaped trace summary without assuming chronological processing order or width/gap conclusions | distinct source indices; strict `s + d_s < t` availability; separate intra-round and source-round active sets; `DelayedSAPOProcessedPrefixCountCertificate`; source D.4 count clause | read chosen actions and line-15 allocations at stored source indices; consume explicit current-to-source containment; record source-trace antitonicity separately; define source width and recursive empirical UCB; consume only the two D.4 count inequalities | compiled deterministic adapter and conditional factor-20 consumer; Algorithm-5 transition-and-invariant-to-summary producer, D.4 `2/T` probability, and generated trajectory remain open |
| `DELAYED-BOBW-ORDERED-NO-SWITCH-PROCESS-ONE` | compile one source-faithful no-switch iteration of physical PDF page 22, Algorithm 5 lines 3--4 and 7--8, with the line-7 summary formed after appending the newly observed source and the line-8 successor formed by active-set removal | `newlyObservedBefore`; `observedBefore`; `DelayedSAPOEliminationSnapshot.remainingActive`; `DelayedSAPOProcessedTraceSummary`; `List.Nodup.injective_get`; `List.nodup_concat`; `Finset.sdiff_subset` | keep the paper sequence as a duplicate-free `List Nat`; accept an arbitrary member of `B(t) \ S`; append it without sorting; derive strict availability, source-index injectivity, and current-to-source containment from a round-start invariant and an antitone source-round active trace; then preserve the invariant through exact line-8 removal | compiled 15-declaration structural leaf and focused nonchronological canary; BSC/EAP, numeric state generation, round finalization, trajectory measurability, D.4 probability, and every paper endpoint remain open |
| `DELAYED-BOBW-ORDERED-NO-SWITCH-TRACE-ORDERING` | derive the temporal premise for the repaired factor-20 gap consumer from an exact finite no-switch structural trace rather than accepting that a later-eliminated arm remained active at an earlier snapshot | `DelayedSAPONoSwitchProcessOne.afterLine8`; `newlyObservedBefore`; `observedBefore`; `DelayedSAPOProcessedTraceSummary.gap_le_twenty_mul_gap_at_earlier_elimination_snapshot_of_traceSummary`; `Relation.ReflTransGen`; `Finset.sdiff_eq_empty_iff_subset` | add an explicit round-close certificate, a round-advance state, and the reflexive-transitive closure of processing/advance steps; prove current-active monotonicity along the trace; transport later elimination membership back to the earlier line-8 remaining set; invoke the existing D.4-conditional trace-summary consumer | compiled 12-declaration deterministic trace and conditional factor-20 consumer; no numeric BSC/EAP producer, generated law, D.4 probability, switch path, unconditional source lemma, or regret endpoint |
| `DELAYED-BOBW-D11-NONNEGATIVE-GAP-HALF-SET` | recover the deterministic counting fact used by Appendix Lemma D.11 on the nonnegative stochastic-loss-gap domain | finite sums/cardinality; nonnegative gaps; optimal-arm minimality; source Appendix Lemma D.11 | state nonnegativity explicitly, split empty/zero-average cases, sum the strict-above-threshold subset, and specialize to stochastic loss gaps | compiled six-declaration domain core and signed premise-boundary canary; no source correction is claimed; Lemma D.13 and the stochastic endpoint remain open |
| `DELAYED-BOBW-ALGORITHM5-LINE10-ELIMINATED-ARM-INITIALIZATION` | construct the literal Algorithm 5 line-10 state for exactly the arms selected by line 7 | `DelayedSAPONoSwitchProcessOne.toPreEliminationSummary`; source empirical width; `DelayedSAPOEliminationSnapshot.eliminated`; real positivity/division | freeze `S`, empirical mean, `p_i^1`, `8 width_i(S)`, and `N_i^1`; update only eliminated bank entries; preserve surviving/active entries; expose `1 < T` for positive width/target | compiled 31-declaration initialization producer and concrete two-arm canary; EAP transitions, confidence-set evolution, BSC, generated law, D.4, and endpoints remain open |
| `DELAYED-BOBW-CAUSAL-ACTION-MEASURE` | line-15 vector induces a probability measure and a causal measure-valued decision rule | local `Exp3.FiniteActionDistribution`, `finiteActionMeasure`; causal observation equivalence | package explicit EAP premises, reuse the finite-action law, and transport equality through `ActionTimeView` | compiled one-round action law; measurable history kernel and recursive generated trajectory open |

## Current compiled leaf contract

- Compiled target pair:
  `DELAYED-BOBW-D11-NONNEGATIVE-GAP-HALF-SET` and
  `DELAYED-BOBW-ALGORITHM5-LINE10-ELIMINATED-ARM-INITIALIZATION`.
- Local APIs/imports: finite sums and filtered-cardinality algebra for D.11;
  `OrderedProcessingTransition.lean`, the exact line-7 eliminated set, and the
  source width for line 10.
- Intended D.11 route: require the nonnegative gap property used by Markov's
  inequality, prove that a strict-above-twice-average set has cardinality at
  most half, then instantiate gaps as `mean i - mean optimal`.
- Intended line-10 route: read the post-append processed count and width from
  the exact no-switch step; construct the printed real-valued initializer;
  update only arms in the line-7 eliminated set; preserve surviving arms and
  prove positivity without hiding the `T = 1` totalized-division edge case.
- Hidden regularity: D.11 needs nonnegative values, which the source stochastic
  gaps obtain from optimal-arm minimality.  Strict positivity of the line-10
  surrogate gap and phase target needs `1 < T`; an upper bound on `p_i^1`
  separately needs `n_i(S) <= T`.
- Failure policy: do not compile the unrestricted signed D.11 statement,
  silently round `N_i^1`, initialize arms outside the current eliminated set,
  or treat the bank initializer as an EAP/BSC transition or generated process.
- Next boundaries, not attempted here: formalize the EAP phase transition and
  confidence-set evolution, reconcile the exact D.13 witness/index statement,
  construct the measurable randomized trajectory, and prove D.4's simultaneous
  `2/T` event on that law.

## Paper-level blockers

- EAP phase transitions and recursive probability-bank evolution beyond the
  compiled line-10 initializer;
- measurable randomized Delayed SAPO kernel instantiated on the compiled
  causal view and its generated trajectory law;
- exact source detection/switch state machine;
- source-faithful ordering of simultaneous arrivals and recursive confidence
  updates after each processed item (the new state permits, but does not choose,
  a nonchronological order);
- stochastic good-event and delayed concentration chain;
- external adversarial `ALG` theorem contract;
- Delayed SAPO instantiation of the compiled generic shared-identity interface,
  followed by a coupled wrapper for Theorems 4.1 and 5.1.

Until those close, the external audit remains partial and no paper theorem is
classified as compiled or audited.

## Concentration ledger for the next stochastic leaf

- Random process: armwise empirical losses over processed delayed feedback,
  together with the importance-weighted estimator used by BSC.
- Filtration: the pre-action history generated from `ActionTimeView`; sampled
  actions and newly returned feedback must be adapted to successive histories.
- Mean: armwise stochastic mean `mu_i`; delays remain oblivious-adversarial.
- Variance/range: losses lie in `[0,1]`; the importance-weighted branch also
  needs the source lower bound on the action probability.
- Exact event: extend the compiled elimination slice to the full Definition-D.1
  simultaneous count, phase, empirical/error, and delay fields.  The existing
  slice derives `muStar <= ucbStar`; it is no longer an independent certificate.
- Source: physical-PDF Appendix D, Definition D.1 and Lemmas D.2--D.3; the
  deterministic consumer is Lemma D.9.
- Mode: arm-uniform and processed-prefix-uniform, hence union bounded; it is
  not yet a locally proved anytime confidence theorem.
- Hidden regularity: measurability, adaptedness, armwise iid stochastic losses,
  positive sampling probability, boundedness, and integrability remain open.
- Mathlib status: martingale and conditional-MGF infrastructure exists locally,
  but no imported theorem currently discharges this exact delayed adaptive
  prefix event.

## Lemma D.10/D.12 source-direction audit

- Source surface: `width_i(S) = min(1, sqrt(2 log(T) / n_i(S)))`, the
  displayed prefix condition `n <= |S-tilde_i|`, and the D.12 chain on physical
  PDF pp. 26--27.
- Local APIs/imports: `Real.sqrt_le_sqrt`, ordered real division,
  `min_le_min_left`, `linarith`, and `norm_num`.
- Compiled diagnostic: the width is antitone as its positive count grows.  A
  normalized count-one/count-four witness and a literal source-domain `T=4`
  theorem both show that the printed reverse prefix-to-later inequality is not
  a generic consequence of count growth.
- Compiled conditional repair skeleton: at the snapshot where `iEarlier` is
  eliminated, derive `8 w_earlier < gap_earlier` from the actual strict line-7
  test and good-event projection.  For `iLater`, the large branch consumes the
  current-UCB surface and `w_optimal <= 3 w_later`; the small branch consumes
  an exact source-width equality and `count <= 96 * scale`, using the compiled
  implication `1 <= 10 w_later`.  Either branch gives
  `gap_later <= 16 w_later`; the explicit same-prefix comparison
  `w_later <= 10 w_earlier` then gives `gap_later <= 20 gap_earlier` without
  transporting a width to the later elimination snapshot.
- Comparison route: the explicit four-edge contract remains compiled to show
  exactly what the printed D.12 chain would require if its D.10 endpoint were
  supplied.
- Hidden regularity: nonnegative width scale, positive counts for division,
  ordered processed-prefix indices, and the D.10 endpoint inequalities.  The
  prefix index is not wall-clock action time.
- Compiled producer: `ProcessedPrefixCounts.lean` derives the source
  large/small-count branch, current-UCB edge, optimal-to-later factor-three
  edge, and later-to-earlier factor-ten edge from an explicit source-time
  allocation/action ledger and the exact D.1 count/width/recursive-UCB
  projection.  It then invokes the existing same-snapshot consumer.
- Compiled trace-summary adapter: `RecursiveProcessedState.lean` constructs the
  source-indexed ledger from distinct strictly available entries, derives
  active persistence without conflating intra-round and action-round state,
  and defines the width and recursive-UCB surfaces.  It consumes only the two
  D.4 count inequalities.
- Remaining producers: generate that summary and instantiate the structural
  trace on the measurable randomized Algorithm-5 trajectory; prove D.4's
  simultaneous `2/T` probability statement; cover the switch path and package
  the resulting unconditional source elimination theorem.
- Boundary: the same-snapshot algebraic skeleton is a conditional consumer,
  not a complete repair.  Lemma D.10, Lemma D.12, Lemma 4.2, and Theorem 4.1
  remain unverified until the source branch producers are instantiated.  Author
  clarification remains useful for the intended printed proof.

## Lemma D.11/D.13 counting audit

- Printed D.11 surface: a finite set of reals with average `mu` has at most half
  its elements strictly above `2 * mu`.
- Promoted domain: nonnegative stochastic loss gaps, obtained because the
  chosen optimal arm minimizes the mean loss.  The unrestricted real-valued
  formulation is not promoted, and the signed canary only guards this premise
  boundary; no source correction is claimed.
- Compiled leaf: `StochasticGapHalfSet.lean` proves the finite nonnegative
  theorem, empty/zero-average boundaries, and the source gap specialization.
- D.13 boundary: the printed existence step quantifies an arm `j` outside the
  selected half-set but writes the concluding bound with `Delta_i`.  The exact
  witness/index bridge and the source's half-active-set convention are not
  repaired or promoted here; D.13 remains open pending a source-faithful
  statement or clarification.
