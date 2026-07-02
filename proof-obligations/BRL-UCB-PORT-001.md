# Proof Obligations: BRL-UCB-PORT-001

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | LML theorem cards, ABRL core | `LML-UCB-REGRET`, `TXT-LATTIMORE-SZEPESVARI-2020` | keep route fixed until reviewer records pivot reason | theorem-card status, toolchain alignment | project-local decision | upper | no Lean declaration | memory | planned |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas`, `PullCountDecomposition`, `RegretDecomposition` | pull counts, segment counts, reward sums, gap surface, deterministic pull-count partition, deterministic regret-by-pull-count identity | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `LOCAL-LEAF-MATHLIB-FINSET-WRAPPERS`, `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | compiled dependency-light bookkeeping plus Mathlib Finset wrappers, finite-action count partition, and arm reindexing | finite arms, horizon, rational mean model | project-local compiled leaves | reviewer | `pullCount_le_time`, `pullCount_add_le`, `finset_sum_pullCount_eq_time`, `sumRewards_add_eq_of_forall_ne_between`, `pseudoRegret_add_eq_of_forall_gap_zero_between`, `pseudoRegret_eq_finset_sum_gap_mul_pullCount` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | replace placeholder score with UCB width when dependency layer is selected | route decision | UCB score surface, logarithm/confidence API | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` | define width, prove selected arm maximizes index | positive counts, positive horizon, order/algebra facts | mathlib-candidate for generic order/algebra leaves | lower Lean | `UCB.score_eq_empiricalMean` | build | blocked |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards, `MeasureFoundation`, `MeasurableSums`, `MeasurableLocalQuantities`, `MeasurableRegret`, `MeasurablePullCount`, `MeasurablePullCountCast`, `ExpectationFoundation`, `ExpectationSums`, `ExpectationPullCount`, `ExpectationWeightedPullCount` | LML/Mathlib concentration route plus measurable action-event/indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities | `LOCAL-LEAF-MEASURE-FOUNDATION`, `LOCAL-LEAF-MEASURABLE-SUMS`, `LOCAL-LEAF-MEASURABLE-LOCAL-QUANTITIES`, `LOCAL-LEAF-MEASURABLE-REGRET`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT`, `LOCAL-LEAF-MEASURABLE-PULLCOUNT-CAST`, `LOCAL-LEAF-EXPECTATION-FOUNDATION`, `LOCAL-LEAF-EXPECTATION-SUMS`, `LOCAL-LEAF-EXPECTATION-PULLCOUNT`, `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION` | one-sided and union-bounded tail event control after event, pull-indicator, selected-reward indicator, finite-sum, `sumRewards`, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count identities are explicit | measurability, lower-integral event measures, lower-integral finite sums, lower-integral pull counts, lower-integral weighted pull counts, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported, with local measurable-event, indicator, finite-sum, local reward-sum, pseudo-regret, pull-count, scalar-cast pull-count, lower-integral indicator, lower-integral finite-sum, lower-integral pull-count, and weighted pull-count leaves compiled | lower retrieval | `measurableSet_actionTrace_eval_eq`, `measurable_actionTrace_eval_eq_indicator_const`, `measurable_actionTrace_eval_eq_indicator_reward`, `measurable_finset_sum_indicator_reward`, `measurable_sumRewards`, `measurable_pseudoRegret`, `measurable_pullCount`, `measurable_natCast_pullCount`, `lintegral_actionTrace_eval_eq_indicator_one`, `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`, `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`, `lintegral_finset_sum_gap_mul_natCast_pullCount_eq` plus TBD tail declarations | memory/build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above | compiled deterministic regret decomposition, pull-count partition/bounds, concentration cards | `LOCAL-LEAF-PULLCOUNT-DECOMPOSITION`, `LOCAL-LEAF-REGRET-DECOMPOSITION`, `LML-UCB-REGRET`, `MLIB-ASYMPTOTICS` | good-event pull-count bound plus bad-event summation | all upstream contracts above | project-local final theorem | lower Lean | TBD | build | blocked |

Compiled bridge update: `EXP-PULLCOUNT-LE-TIME` is now available through
`LOCAL-LEAF-EXPECTATION-PULLCOUNT-BOUNDS` and declaration
`lintegral_natCast_pullCount_le_time`.  Use it as an `ENNReal` probability
pull-count budget bound for UCB expected-count scaffolding; it does not close
`EXP-REGRET-PULLCOUNT`, concentration, or the final UCB theorem.

Compiled weighted bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME` is now
available through `LOCAL-LEAF-EXPECTATION-WEIGHTED-PULLCOUNT-BOUNDS` and
declaration
`lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it
as the `ENNReal` weighted probability budget bound before choosing a
`Fin K`/`Finset.univ`, scalar-conversion, or Bochner expected-regret route.

Compiled finite-arm bridge update: `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` is now
available through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-BOUNDS` and declaration
`lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.  Use it as
the finite-arm `Finset.univ` budget bound before the separate scalar conversion
for `FiniteBanditModel.gap : Fin K -> Rat`.

Compiled model-gap bridge update: `EXP-MODEL-GAP-OFREAL-BOUND` is now available
through `LOCAL-LEAF-EXPECTATION-FINITE-BANDIT-MODEL-BOUNDS` and declaration
`lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`.
Use it as an `ENNReal.ofReal` surrogate bound for `FiniteBanditModel.gap`; it
does not prove Rat-valued expected regret or gap faithfulness.

Compiled scalar bridge update: `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` is now
available through `LOCAL-LEAF-SCALAR-ENNREAL` and declaration
`ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg`.  Use it for exact scalar
conversion under explicit nonnegativity before any UCB Rat-valued expected
regret claim.

Compiled pointwise pseudo-regret bridge update:
`OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` is now available through
`LOCAL-LEAF-SCALAR-PSEUDOREGRET` and declaration
`ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`.
Use it as a scalar/model faithfulness bridge under explicit model-gap
nonnegativity; it does not prove expected regret, model-gap nonnegativity,
concentration, or the final UCB theorem.

Compiled lower-integral pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-OFREAL-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`.
Use it as an `ENNReal.ofReal` lower-integral bound under explicit model-gap
nonnegativity; it does not prove Rat-valued expected regret, Bochner expected
regret, model-gap nonnegativity, concentration, or the final UCB theorem.

Compiled Rat-contract pseudo-regret bridge update:
`EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` is now available through
`LOCAL-LEAF-EXPECTATION-PSEUDOREGRET-RAT-BOUNDS` and declaration
`lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`.
Use it when UCB scaffolding has a Rat-level gap nonnegativity contract; it does
not prove that contract from `FiniteBanditModel.bestArm`.

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.
