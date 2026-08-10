# Proof Obligations: Generated EXP3 realized-deviation geometric all-time tail

Task id: `EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

| Node | Target | Local APIs/imports | Retrieval | Proof route | Regularity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `FINITE-VARIANCE-ONE` | centered second moment of a finite `[0,1]` loss law is at most one | `FiniteActionDistribution`; finite sums; order algebra | local exact variance; `MLIB-FINSET-SUMS`; `MLIB-ORDER-ALGEBRA` | mean in `[0,1]`; centered square `<=1`; weighted sum | finite law and supported unit losses only | compiled |
| `GENERATED-LINEAR-BUDGET` | each generated variance is `<=1`; prefix sum is `<=horizon` | generated distribution source and predictable loss Icc APIs | local generated variance declarations | instantiate finite bound and sum | measurable Env; measurable-singleton Action; decidable nonempty arms; `0<=gamma<=1` | compiled |
| `PURE-EVENT` | named geometric all-time pure-deviation event with exact membership | prior geometric schedule/radius | accepted all-time joint leaf | definitions and `Set.mem_iUnion` | no measure assumptions | compiled |
| `EVENT-EQUALITY` | joint event at budget `n+1` equals pure event | generated linear budget and both membership theorems | local event APIs | extensionality; add/remove universally true variance conjunct | generated budget contracts | compiled |
| `PURE-TAIL-ROOT` | pure failure event mass `<=ofReal delta` | event equality and prior terminal | accepted joint all-time leaf | specialize budget, rewrite set, retain same measure | full generated process ledger and `delta>0` | accepted |

## Reviewer Checklist

- The process parameters are outside the countable index.
- Every event uses `Finset.range (n+1)`.
- The variance conjunct is removed only after a pointwise deterministic proof.
- The radius still uses the exact geometric share.
- The result is not reported as full regret, Ville/Doob, Freedman, or EXP3.P.

## Failure Classification

Record exactly one first blocker: finite-law nonlinear inequality, generated
source specialization, finite-sum cast normalization, event extensionality,
terminal rewrite, false statement, or downstream regret assembly. Do not
weaken the target by restoring an abstract variance budget or finite horizon.
