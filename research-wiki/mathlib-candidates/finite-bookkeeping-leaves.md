# Finite Bookkeeping Leaf Candidates

Status: local compiled bridge leaves.
Local module: `BanditRLProof.LeafLemmas`.

These leaves are intentionally dependency-light.  They are not proposed as-is
for Mathlib when they mention ABRL definitions, but they identify the generic
finite-sum, finite-index, and order facts that future Mathlib-backed tasks
should search, import, or upstream.

## Compiled Local Bridge Lemmas

| Local declaration | Role | Mathlib retrieval cards | Future action |
| --- | --- | --- | --- |
| `pullCount_one` | one-step pull count expansion | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | bridge to indicator-sum count theorem |
| `pullCount_succ_of_eq` | selected arm increments count | `MLIB-FINSET-SUMS` | keep local; generic indicator lemma may upstream |
| `pullCount_succ_of_ne` | nonselected arm count is stable | `MLIB-FINSET-SUMS` | keep local; generic filter-count lemma may upstream |
| `pullCount_le_succ` | pull count monotonicity | `MLIB-ORDER-ALGEBRA` | bridge to monotone finite count facts |
| `pullCount_succ_le_succ` | one-step count growth bound | `MLIB-ORDER-ALGEBRA` | bridge to count Lipschitz-in-time facts |
| `pullCount_mono` | monotonicity over arbitrary time order | `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS` | bridge to monotone filtered-cardinality facts |
| `pullCount_le_time` | count is bounded by elapsed time | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to cardinality/subset bound |
| `pullCount_add_le` | count over a future segment grows by at most segment length | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to filtered-cardinality interval bound |
| `pullCount_le_add` | count is monotone from a prefix into a longer prefix | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to filtered-cardinality monotonicity |
| `pullCount_eq_zero_of_forall_ne` | no matching action gives zero count | `MLIB-FINSET-SUMS` | bridge to empty filtered set/cardinality zero |
| `pullCount_eq_time_of_forall_eq` | all actions match gives count equal to time | `MLIB-FINSET-SUMS` | bridge to full filtered range/cardinality |
| `pullCount_pos_of_eq_before` | one observed match implies positive count | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to nonempty filtered range/cardinality positive |
| `pullCount_const_self` | constant action trace has count equal to time for its arm | `MLIB-FINSET-SUMS` | bridge to full filtered range/cardinality |
| `pullCount_const_of_ne` | constant action trace gives zero count for other arms | `MLIB-FINSET-SUMS` | bridge to empty filtered range/cardinality |
| `pullCount_add_eq_of_forall_ne_between` | a segment without the arm leaves its count unchanged | `MLIB-FINSET-SUMS` | bridge to filtered interval with empty match set |
| `pullCount_add_eq_add_of_forall_eq_between` | a segment entirely using the arm increases count by segment length | `MLIB-FINSET-SUMS` | bridge to filtered interval with full match set |
| `sumRewards_succ_of_eq` | selected reward is added | `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL` | bridge to finite-sum reward decomposition |
| `sumRewards_succ_of_ne` | nonselected reward sum is stable | `MLIB-FINSET-SUMS` | bridge to filtered sum update lemmas |
| `sumRewards_eq_zero_of_forall_ne` | no selected arm gives zero reward sum | `MLIB-FINSET-SUMS` | bridge to empty filtered-sum theorem |
| `sumRewards_const_of_ne` | constant other arm gives zero reward sum | `MLIB-FINSET-SUMS` | bridge to filtered-sum theorem over constant trace |
| `FiniteBanditModel.gap_of_ne_bestArm` | explicit nonbest gap surface | `MLIB-ORDER-ALGEBRA` | later add nonnegativity after best-arm optimality route |
| `pseudoRegret_one` | first-step pseudo-regret expansion | `MLIB-FINSET-SUMS` | bridge to finite-sum regret definition |
| `pseudoRegret_succ_of_bestArm` | best-arm pull adds no pseudo-regret | `MLIB-ORDER-ALGEBRA` | useful in ETC/UCB local wrappers |
| `pseudoRegret_succ_of_gap_zero` | zero-gap pull adds no pseudo-regret | `MLIB-ORDER-ALGEBRA` | useful in ties and multiple optimal arms |
| `pseudoRegret_eq_zero_of_forall_bestArm` | all best-arm actions have zero pseudo-regret | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to zero finite-sum regret route |
| `pseudoRegret_eq_zero_of_forall_gap_zero` | all zero-gap actions have zero pseudo-regret | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to tie-aware regret route |
| `pseudoRegret_const_bestArm` | constant best-arm policy has zero pseudo-regret | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | useful baseline sanity theorem |
| `pseudoRegret_const_of_gap_zero` | constant zero-gap policy has zero pseudo-regret | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | tie-aware baseline sanity theorem |
| `pseudoRegret_add_eq_of_forall_bestArm_between` | a best-arm segment leaves pseudo-regret unchanged | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | bridge to ETC commit and baseline segments |
| `pseudoRegret_add_eq_of_forall_gap_zero_between` | a zero-gap segment leaves pseudo-regret unchanged | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | tie-aware segment bridge |

## Next Upstream Candidates

- finite filtered-count update;
- finite indicator-sum update;
- monotonicity and one-step growth of filtered counts;
- interval filtered-count bounds and empty/full interval updates;
- bridge between recursive counts and `Finset.range` sums;
- filtered reward-sum update under additive zero law.

Each candidate must be restated without ABRL-specific names before it is marked
as a genuine Mathlib upstream proposal.
