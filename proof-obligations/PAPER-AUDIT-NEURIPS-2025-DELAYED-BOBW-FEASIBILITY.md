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
| `DELAYED-BOBW-GOOD-EVENT-D9-PROJECTION` | derive `muStar <= ucbStar` from both source upper-confidence surfaces and bound optimal-arm elimination by the complement of the elimination good event | finite infimum, `min`, event inclusion, measure monotonicity; source Definition D.1 and Lemma D.9 | package the elimination slice, construct the survival certificate, and expose a failure-budget consumer | compiled projection/consumer; full event and D.2--D.8 probability producer open |
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
