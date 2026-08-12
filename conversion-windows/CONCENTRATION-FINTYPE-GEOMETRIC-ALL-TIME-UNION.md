# Conversion Window: Finite-index geometric all-time confidence union

Task id: `CONCENTRATION-FINTYPE-GEOMETRIC-ALL-TIME-UNION`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-CONTEXTUAL-FINITE`

## Natural-Language Statement

Let `bad n i` be a bad event for time `n` and an index `i` in a nonempty
finite type. If every event at time `n` has outer measure at most
`deltaAt n / card`, then the union over all times and indices has outer measure
at most the ENNReal sum of `deltaAt`. With the compiled geometric schedule and
`delta >= 0`, this total is exactly `ENNReal.ofReal delta`.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `I` | finite index family | `[Fintype Idx] [Nonempty Idx]` | explicit |
| `E_{n,i}` | bad event at time/index | `bad n i : Set Omega` | explicit |
| `delta_n / card(I)` | per-index share | displayed `ENNReal.ofReal` premise | explicit |
| `union_n union_i E_{n,i}` | all-time simultaneous failure | nested `Set.iUnion` | compiled |
| `sum_n delta_n` | scheduled outer budget | `sum' n, ENNReal.ofReal (deltaAt n)` | compiled |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| measurable ambient space | typeclass | Mathlib measure API | no |
| finite, nonempty index type | typeclasses | equal-share normalization | no |
| one pointwise outer-measure tail per time/index | higher-order premise | downstream producer | no |
| `delta >= 0` for exact geometric total | explicit premise | compiled schedule theorem | no |
| event measurability | deliberately absent | outer-measure union APIs | no |
| probability measure, independence, filtration | deliberately absent | composition-only leaf | no |

## Local API And Proof Route

| Node | Existing APIs/imports | Intended route | Pivot rule |
| --- | --- | --- | --- |
| N0 finite share | finite-union equal-share wrapper | use `Finset.univ` and its nonemptiness | do not replace `Fintype` by a caller `Finset` |
| N1 countable union | `measure_iUnion_le`; `ENNReal.tsum_le_tsum` | compare every time term with N0 | do not add measurable events |
| root | exact geometric schedule theorem | rewrite the N1 `tsum` | do not change to a finite horizon |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Regularity | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| N0 | per-time finite union `<= ofReal deltaAt n` | finite equal-share parent | internal specialization | finite nonempty index | focused | compiled |
| N1 | nested countable/finite union `<= tsum` | N0 and countable subadditivity | `measure_iUnion_iUnion_fintype_le_tsum_of_uniform` | measurable ambient space | focused/Tests | compiled |
| root | nested union `<= ofReal delta` | N1 and exact geometric total | `measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare` | `0 <= delta` | full harness | accepted |

## Gaps

- [x] Existing local search found the two separate parent adapters but no
  generic theorem composing finite indices with all countable times.
- [x] Mathlib/local APIs suffice; no new upstream theorem is required.
- [x] Lean source and root import compile at the focused-module boundary.
- [x] Root/Tests/canary, statement-fence, baseline-axiom, website, and
  independent-review gates pass; all four P2 harness findings are repaired.
- [x] Verified memory `mem-99363842cb89e027`, accepted frontier, zero-mismatch
  shadow, and full harness gate pass.
