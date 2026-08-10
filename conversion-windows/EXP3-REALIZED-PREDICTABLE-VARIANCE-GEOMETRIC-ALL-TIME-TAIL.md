# Conversion Window: Generated EXP3 predictable-variance geometric all-time tail

Task id: `EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

## Natural-Language Statement

Fix one generated EXP3 process. Give prefix `n+1` the positive confidence
share `delta / 2 / 2^n` and a positive predictable-variance budget `V_n`.
The mass of trajectories for which at least one positive prefix has both
realized-minus-predictable loss above the corresponding optimized quadratic
radius and cumulative predictable variance at most `V_n` is at most
`ENNReal.ofReal delta`.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `delta_n` | geometric confidence share | `Concentration.geometricConfidenceShare delta n` | compiled |
| `r_n` | quadratic radius at `V_n, delta_n` | `Exp3.sampledRealizedPredictableVarianceGeometricRadius` | compiled |
| `D_n` | sum of realized selected-loss deviations over `range (n+1)` | existing `sampledTrajectoryRealizedDeviationAt` finite sum | compiled parent |
| `W_n` | sum of selected-loss predictable variances over `range (n+1)` | existing `sampledTrajectoryPredictableRealizedVarianceAt` finite sum | compiled parent |
| `E` | `union_n {r_n <= D_n and W_n <= V_n}` | `sampledPredictableRealizedDeviationAllTimeFailureSet` | compiled |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| Standard Borel nonempty Env/Action; measurable action singletons; decidable Action | explicit typeclasses | generated EXP3 fixed-tilt parent | no |
| probability prior and nonempty finite arms | explicit | generated trajectory law | no |
| fixed `eta`, positive `gamma <= 1`, one `PredictableLossVector` | explicit | fixed-tilt parent | no |
| positive `varianceBudget n` and positive outer `delta` | explicit | quadratic optimizer and geometric schedule | no |
| event measurability | deliberately absent | countable outer-measure union | no |
| independence/stationarity | deliberately absent | conditional-MGF parent already owns process contracts | no |
| deterministic proof that `W_n <= V_n` | deliberately absent | theorem controls the joint event only | downstream |

## Local API And Proof Route

| Node | Existing APIs/imports | Route | Pivot rule |
| --- | --- | --- | --- |
| N0 schedule | `hasSum_geometric_two'`; `HasSum.toNNReal`; `ENNReal.hasSum_coe` | prove positivity and exact ENNReal tsum | retain exact total `delta` |
| N1 event/radius | existing sampled quadratic radius and finite-prefix processes | name radius/event and prove membership iff | preserve prefix `n+1` |
| N2 pointwise tail | generated fixed-tilt predictable-variance theorem | specialize every `n` at the scheduled radius | keep eta/gamma/loss fixed across n |
| root | compiled countable scheduled quadratic theorem | choose constant scale/cap one, use N2 and exact N0 budget | no finite truncation or changed process |

## Proof DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| N0 | positive share and exact ENNReal sum | Mathlib geometric series | lower | `geometricConfidenceShare_pos`; `tsum_ofReal_geometricConfidenceShare` | positive/nonnegative delta | focused/Tests | compiled |
| N1 | named radius and all-time failure semantics | existing sampled radius/process | lower | radius, failure set, membership iff | none beyond definitions | focused/Tests | compiled |
| N2 | per-prefix quadratic fixed-tail family | fixed-tilt generated EXP3 parent | middle | internal specialization | generated process contracts; positive budget | focused | compiled |
| root | one-process all-time tail | N0-N2; countable scheduled parent | upper | `measure_sampledPredictableRealizedDeviationAllTimeFailureSet_le` | full ledger above | full harness | accepted |

Retrieval also records
`LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE` as the owner of N0
and `LOCAL-LEAF-OFUL-ALL-TIME-TELESCOPING-SCALAR-RIDGE-CONFIDENCE` as an
independent local precedent for exact Real-to-NNReal-to-ENNReal confidence
budget transport.

## Remaining Boundaries

- The theorem does not prove the predictable-variance budget events hold.
- It is simultaneous fixed-process confidence, not an algorithm whose
  `eta/gamma` is retuned separately at every horizon.
- Full realized regret still needs a pathwise potential/comparator assembly
  and a usable variance-budget producer.
- No Ville/Doob, mixture, optional-stopping, self-normalized, general Freedman,
  or ideal EXP3.P conclusion is implied.

The accepted statement is fenced by
`be643bca7d9a7f9ddf16cb98c5fcab0d74ee624eaeed4cfe4a4af530b84073b2`.
Focused/root/Tests builds, three external semantic canaries, baseline axiom
audit, and independent read-only review all pass. Verified memory is
`mem-1d262929553ef1ca`; frontier shadow has zero mismatches.
