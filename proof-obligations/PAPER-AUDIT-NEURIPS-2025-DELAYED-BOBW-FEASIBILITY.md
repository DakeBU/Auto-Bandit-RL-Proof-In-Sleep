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
| `DELAYED-BOBW-D8-D9-ASSEMBLY` | combine the six D.2--D.7 failure components into Corollary D.8's `9/T` budget and transport it through D.9 survival | finite outer-measure union, explicit `1/T^2` and `1/T` arithmetic, complement inclusion | name the six failure events, prove the union budget, and compose an explicit full-event projection with optimal-arm survival | compiled union/composition; six concentration proofs and semantic projection remain open |
| `DELAYED-BOBW-D10-D12-GAP-ORDERING-AUDIT` | audit the width/gap chain used by Appendix Lemma D.10 and expose both the displayed four-edge route and a conditional same-snapshot factor-20 skeleton for Lemma D.12 / main-text Lemma 4.2 | `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`; source empirical-width definition, Algorithm 5 line-7 snapshot, and physical PDF pp. 26--27 | prove width antitonicity and a literal `T=4` reverse-direction witness; derive the eliminated-arm lower gap; prove the exact small-count width lower bound; consume a large/small-count branch certificate and an explicit same-prefix factor-ten edge; retain the conditional four-edge consumer for comparison | compiled diagnostic and conditional consumers; recursive branch/count/width producers and unconditional D.10/D.12 remain open |
| `DELAYED-BOBW-CAUSAL-ACTION-MEASURE` | line-15 vector induces a probability measure and a causal measure-valued decision rule | local `Exp3.FiniteActionDistribution`, `finiteActionMeasure`; causal observation equivalence | package explicit EAP premises, reuse the finite-action law, and transport equality through `ActionTimeView` | compiled one-round action law; measurable history kernel and recursive generated trajectory open |

## Active leaf contract

- Local APIs/imports: `Mathlib.Data.Finset.Card`, `Finset.range`,
  `Finset.filter`, complement/disjoint/cardinality lemmas.
- Intended proof route: define the source predicate once; use its Boolean
  complement inside the finite prefix; prove disjointness, union, then card
  addition.
- Hidden regularity: none beyond `delay : Nat -> Nat` and `t : Nat`.
- Mathlib candidacy: the generic filter partition already belongs in Mathlib;
  these declarations are thin project-local wrappers that preserve paper
  indexing.
- Failure policy: do not change strict `< t` to `<= t`, extend beyond
  `Finset.range t`, or smuggle future delay knowledge into the algorithm.  If
  an off-by-one mismatch appears, update the conversion window before tactics.

## Paper-level blockers

- delayed SAPO state and probability-bank data structures;
- randomized Delayed SAPO kernel instantiated on the compiled causal view;
- exact source detection/switch state machine;
- source-faithful ordering of simultaneous arrivals and recursive confidence
  updates after each processed item;
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
- Remaining producers: the recursive source large/small-count branch
  certificate, the actual source-width/count equality in the small branch, the
  current-UCB and factor-three edges in the large branch, the later-to-earlier
  same-prefix factor-ten comparison, the ordered processed trace, and their
  probability/recursive trajectory instantiation.
- Boundary: the same-snapshot algebraic skeleton is a conditional consumer,
  not a complete repair.  Lemma D.10, Lemma D.12, Lemma 4.2, and Theorem 4.1
  remain unverified until the source branch producers are instantiated.  Author
  clarification remains useful for the intended printed proof.
