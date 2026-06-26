# Proof Obligations: BRL-UCB-PORT-001

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | LML theorem cards, ABRL core | `LML-UCB-REGRET`, `TXT-LATTIMORE-SZEPESVARI-2020` | keep route fixed until reviewer records pivot reason | theorem-card status, toolchain alignment | project-local decision | upper | no Lean declaration | memory | planned |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas` | pull counts, segment counts, reward sums, gap surface | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `LML-BANDIT-REGRET-PULLCOUNT` | compiled dependency-light bookkeeping | finite arms, horizon, rational mean model | project-local wrappers with generic arithmetic candidates | reviewer | `pullCount_le_time`, `pullCount_add_le`, `sumRewards_add_eq_of_forall_ne_between`, `pseudoRegret_add_eq_of_forall_gap_zero_between` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | replace placeholder score with UCB width when dependency layer is selected | route decision | UCB score surface, logarithm/confidence API | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` | define width, prove selected arm maximizes index | positive counts, positive horizon, order/algebra facts | mathlib-candidate for generic order/algebra leaves | lower Lean | `UCB.score_eq_empiricalMean` | build | blocked |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards | LML/Mathlib concentration route | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION` | one-sided and union-bounded tail event control | measurability, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported | lower retrieval | TBD | memory/build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above | regret decomposition, pull-count bound, concentration cards | `LML-UCB-REGRET`, `MLIB-ASYMPTOTICS` | good-event pull-count bound plus bad-event summation | all upstream contracts above | project-local final theorem | lower Lean | TBD | build | blocked |

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.
