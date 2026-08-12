# Proof Obligations: Finite-index geometric all-time confidence union

Task id: `CONCENTRATION-FINTYPE-GEOMETRIC-ALL-TIME-UNION`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario cards: `SCN-STOCHASTIC-FINITE`, `SCN-CONTEXTUAL-FINITE`

| Node | Target | Local APIs/imports | Retrieval | Proof route | Regularity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `FINITE-AT-TIME` | `mu (union_i bad n i) <= ofReal (deltaAt n)` | finite equal-share outer-union wrapper; `Finset.univ_nonempty` | finite-union local card; Mathlib measure/Finset cards | instantiate at time `n` | measurable ambient; finite nonempty index | compiled |
| `COUNTABLE-TSUM` | `mu (union_n union_i bad n i) <= sum' n ofReal (deltaAt n)` | `measure_iUnion_le`; `ENNReal.tsum_le_tsum` | countable-scheduled local precedent | outer subadditivity then termwise finite bound | no event measurability or probability normalization | compiled |
| `GEOMETRIC-ROOT` | nested union `<= ofReal delta` | exact geometric-confidence `tsum` | geometric-schedule local card | rewrite the exact total | `0 <= delta` | accepted |

## Reviewer Checklist

- The quantifier order is countable time outside finite index.
- The same nonempty finite type is used at every time.
- The pointwise share is exactly `deltaAt n / Fintype.card Idx`.
- The theorem is an outer-measure statement and does not require event
  measurability or a probability measure.
- The root uses the existing geometric schedule exactly, not an inequality or
  an undocumented confidence reallocation.
- No theorem card or proof weapon is treated as local proof evidence.

## Failure Classification

Record exactly one first failure: card normalization, nested union elaboration,
countable outer-measure comparison, geometric total rewriting, public-import
canary, or false statement. Do not add stochastic-process assumptions or
claim a downstream algorithm theorem.
