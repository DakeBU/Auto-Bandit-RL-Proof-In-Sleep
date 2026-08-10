# Proof Obligations: Generated EXP3 predictable-variance geometric all-time tail

Task id: `EXP3-REALIZED-PREDICTABLE-VARIANCE-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `GEOMETRIC-SHARE` | positive `delta/2/2^n`; ENNReal tsum exactly `ofReal delta` | Mathlib geometric series | `hasSum_geometric_two'`; `HasSum.toNNReal`; `ENNReal.hasSum_coe` | `LOCAL-LEAF-CONCENTRATION-GEOMETRIC-CONFIDENCE-SCHEDULE`; specific-limits and ENNReal APIs; OFUL exact-budget precedent | real HasSum -> NNReal -> ENNReal | `0<delta` for positivity; `0<=delta` for sum | compiled |
| `NAMED-EVENT` | radius and countable failure set with exact membership semantics | sampled radius/process definitions | finite sums; `Set.mem_iUnion` | local EXP3 predictable-variance route | definitions plus simp | no measure assumptions | compiled |
| `POINTWISE-TAIL` | fixed-tilt family for every prefix `n+1` | generated fixed-tilt theorem | `sampledPredictableRealizedDeviation_sum_tail_predictableVariance_fixedTilt` | local fixed-MGF route | specialize threshold and budget at n | fixed process; positive gamma/cap and budget | compiled |
| `ALL-TIME-ROOT` | named failure mass at most `ofReal delta` | all three nodes; countable scheduled quadratic theorem | `ConcentrationQuadraticScheduled` | local countable leaf; Mathlib measure/tsum APIs | instantiate constant scale/cap and exact geometric budget | full generated EXP3 ledger | accepted |

## Failure Classification

Record exactly one first blocker: geometric ENNReal transport, named-event
normalization, pointwise fixed-tilt specialization, countable theorem
elaboration, false statement, or connected downstream variance-budget gap.
Do not weaken to finitely many horizons, horizon-dependent process parameters,
or an abstract caller-supplied confidence schedule.

## Reviewer Checklist

- All prefixes are `n+1`; the empty prefix is excluded.
- `eta`, `gamma`, `loss`, `prior`, and `arms` define one common process.
- The share schedule sums exactly to the outer budget.
- The theorem controls a joint deviation/variance event and does not establish
  the variance budget itself.
- Literature cards and weapons are not treated as local proof evidence.

## Verification

Focused/root/Tests builds and direct canaries for the exact geometric `tsum`,
the full membership equivalence, and the terminal theorem pass. SafeVerify
records statement hash
`be643bca7d9a7f9ddf16cb98c5fcab0d74ee624eaeed4cfe4a4af530b84073b2`;
the seven public declarations expose only baseline axioms. Independent review
found no Lean/math defect after the retrieval-ownership and canary fixes.
Verified memory is `mem-1d262929553ef1ca`; frontier shadow has zero mismatches.
