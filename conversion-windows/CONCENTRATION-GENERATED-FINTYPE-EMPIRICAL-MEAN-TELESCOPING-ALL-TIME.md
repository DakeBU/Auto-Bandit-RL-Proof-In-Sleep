# Conversion Window: Generated finite-arm empirical-mean telescoping all-time confidence

Task id: `CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-TELESCOPING-ALL-TIME`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`TXT-BUBECK-CESABIANCHI-2012`, `PPR-AUER-CBF-2002-UCB1`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

For every time index `n`, allocate confidence budget
`delta_n = delta / ((n+1)*(n+2))`. These positive shares sum exactly to
`delta`. Divide each time share equally across a nonempty finite arm type and
instantiate the existing canonical fixed-arm, fixed-horizon random-count
empirical-mean tail at horizon `n+1`. The union over all times and arms then
has outer measure at most `ENNReal.ofReal delta` on the identical generated
`Kernel.trajMeasure`.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `delta_n` | time-`n` confidence share | `Concentration.telescopingConfidenceShare delta n` | deterministic Real schedule | mapped |
| `A_t` | generated selected action | first coordinate of canonical pair trajectory | action process | mapped |
| `Y_t` | generated reward | second coordinate of canonical pair trajectory | reward process | mapped |
| `N_a(n+1)` | successor pull count | `successorArmPullCount action arm (n+1)` | random Nat count | mapped |
| `bad(n,a)` | absolute empirical-mean crossing at peeling radius | set comprehension in the terminal module | event; outer measure used | mapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite nonempty action set | `[Fintype Action] [Nonempty Action]` | local union adapter | no |
| measurable/standard-Borel action with measurable singletons | typeclasses | canonical trajectory/fixed-horizon producer | no |
| probability initial pair law | `[IsProbabilityMeasure mu0]` | canonical trajectory | no |
| conditional centered sub-Gaussian reward kernel | `CenteredRewardKernelLaw` plus selected variance ceiling | compiled fixed-horizon tail | no |
| stationary per-arm conditional mean | `harmMean` | compiled fixed-horizon tail | no |
| positive proxy and budget | `hsigma2`, `hdelta` | radius/share positivity | no |
| event measurability / independence / optional stopping | absent | outer-measure union route | no |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| schedule | `HasSum`, `ENNReal.hasSum_coe`, reciprocal finite sums | `MLIB-ORDER-ALGEBRA`; OFUL local precedent | telescope to one and multiply by delta | do not change schedule after tactic friction |
| union | existing `measure_iUnion_iUnion_fintype_le_tsum_of_uniform` | `MLIB-MEASURE-INTEGRAL` | specialize to telescoping shares and exact tsum | do not add measurability |
| generated root | accepted fixed-horizon generated tail | source cards above; no LML proof term | instantiate `(n+1, arm, delta_n/card)` and close with union | audit only indexing/share/same-measure |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `SCHEDULE` | exact positive telescoping confidence schedule | deterministic real/ENNReal sum APIs | lower | `Concentration.tsum_ofReal_telescopingConfidenceShare` | reciprocal telescope | Mathlib cards above; OFUL local precedent | `0<=delta`; positivity separately | project-local | focused Lean | compiled |
| `FINITE-UNION` | all times/all arms outer-measure adapter | `SCHEDULE`, existing finite-index scheduled union | lower | `Concentration.measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare` | specialize and rewrite tsum | Mathlib measure/order cards | finite nonempty arms | project-local | focused Lean | compiled |
| `GENERATED-ROOT` | canonical all-time empirical-mean event | `FINITE-UNION`, accepted fixed-horizon producer | lower | `...simultaneous_fintype_telescopingAllTime...trajMeasure` | exact same-measure instantiation | textbook/paper/scenario placement | full ledger above | project-local | focused/root/Tests/full gate | accepted |

## Gaps

- [x] Add the generic telescoping schedule and exact ENNReal sum.
- [x] Add the finite-index telescoping all-time union wrapper.
- [x] Add the canonical generated empirical-mean terminal and external canary.
- [x] Record statement fence, retrieval evidence, reviewer result, typed
  memory, frontier, docs/website status, and full gate.
- Verified memory: `mem-bf2d4d618cb0e53d`; full statement hash:
  `0084164a0ef29bd352de50fa771eba63c024bd45a664aafe842c116f58f24855`.
- No LML or external cited theorem is used as a proof term.
