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
