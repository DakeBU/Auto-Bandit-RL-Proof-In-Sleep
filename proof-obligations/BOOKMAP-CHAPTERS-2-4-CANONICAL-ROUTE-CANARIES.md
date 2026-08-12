# Proof Obligations: Book Map Chapters 2--4 canonical route completion

Task id: `BOOKMAP-CHAPTERS-2-4-CANONICAL-ROUTE-CANARIES`

| Node | Target | Local APIs/imports | Retrieval | Regularity | Status |
| --- | --- | --- | --- | --- | --- |
| `RAT-ARGMAX-FIRST` | canonical Rat oracle equals first-occurrence list argmax | `Mathlib.Data.List.MinMax`, `List.argmax`, `List.finRange` | local Real analogue plus Mathlib list API | `0 < K` | compiled |
| `RAT-ARGMAX-LEAST-TIE` | any arm tying the maximum has no smaller list/encoding position | `List.index_of_argmax`, `List.idxOf_finRange` | local Real least-tie precedent; no LML proof term | Rat scores, finite nonempty arms | compiled |
| `CH2-SURFACE` | required generated law/conditional MGF/finite-time and finite/countable adapters are importable | conditional-reward and concentration modules | exact local declarations | explicit theorem contracts | compiled canary |
| `CH3-SURFACE` | generated law, exploration, least tie, wrong-commit union, expected regret | `ETCGeneratedHistoryPolicy`, `ETCFiniteArmRewardLaw` | exact local declarations | same canonical kernel/trajectory lets | compiled canary |
| `CH4-SURFACE` | finite-time confidence, large-gap, count, expected regret, horizon-indexed average consistency | pair-trajectory and finite-arm asymptotic modules | exact local declarations | same constructor family for each `(T,delta)` | compiled canary |
| `ROOT` | public root, Tests, docs/site/review/lifecycle/full gate | repository harness | all above | no scope inflation | accepted |

## Reviewer Checklist

- The new tie theorem refers to the Rat oracle used by
  `explorationArgmaxHistoryPolicy`, not only the separate Real selector.
- Equality on scores does not update the strict fold, so the least occurrence
  is preserved.
- The Chapter 3 named wrong-commit theorem and matching bounded expected
  endpoint expose identical `armLaw`, `rewardKernel`, `stepKernel`, and
  `trajMeasure` lets.
- The UCB canary starts from the actual finite-time producer used by the
  policy chain; the all-time theorem is shown only as a separate Chapter 2
  extension.
- Horizon-indexed expected-average consistency is not described as one fixed
  anytime policy or fixed measure.
- No theorem card, proof weapon, or adjacent `#check` is promoted beyond the
  exact declarations it names.

## Failure Classification

Record one first failure: fold/argmax orientation, finRange index mismatch,
false tie claim, stale import/object, same-source mismatch, chapter-scope
overstatement, reviewer rejection, or full-gate failure.
