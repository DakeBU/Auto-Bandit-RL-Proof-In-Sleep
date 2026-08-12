# Conversion Window: Book Map Chapters 2--4 canonical route completion

Task id: `BOOKMAP-CHAPTERS-2-4-CANONICAL-ROUTE-CANARIES`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CBF-2002-UCB1`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

For any nonempty finite Rat score vector, the canonical ETC commit oracle is
the first maximizing arm in `List.finRange K`. Consequently, if any arm ties
the selected maximal score, the selected arm has no larger encoding. This
fixes the tie semantics of the exact oracle used by the measurable generated
ETC policy.

The chapter canary separately checks that the declared Probability adapters,
canonical generated ETC route, and horizon-indexed ordinary-UCB route are
publicly importable. It does not assert that the geometric all-time event is
consumed by a fixed anytime UCB policy.

## Lean Mapping

| Symbol | Meaning | Lean surface | Status |
| --- | --- | --- | --- |
| ordered arms | canonical finite enumeration | `List.finRange K` | compiled |
| strict-update argmax | Rat commit oracle | `ETC.argmaxCommitOracle hK` | compiled parent |
| first maximum | Mathlib list argmax | `List.argmax scores (List.finRange K)` | compiled equality |
| least tie | selected encoding is minimal among maximizers | `ETC.argmaxCommitOracle_encode_le_of_score_le` | compiled |
| ETC law | measurable generated reward-history trajectory | `explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure` | compiled |
| UCB family | policy/measure constructor parameterized by `(T, delta)` | `selectedPolicySuccessorHistoryPolicy` and pair `trajMeasure` | compiled |

## Assumption Ledger

| Assumption | Lean status | Purpose |
| --- | --- | --- |
| `0 < K` | explicit | supplies a nonempty initial arm |
| `scores : Fin K -> Rat` | typed | exact canonical ETC score type |
| tying/maximal score inequality | explicit | identifies an alternative maximum |
| probability/measurability/concentration | absent from tie leaf | deterministic selection semantics only |
| UCB horizon and confidence schedule | explicit in existing terminals | horizon-indexed ordinary-UCB scope |

## Proof DAG

| Node | Interface | Dependencies | Gate | Status |
| --- | --- | --- | --- | --- |
| N0 | fold equals first list argmax | `List.argmax`, strict-update fold | focused Lean | compiled |
| N1 | selected maximum precedes any tying arm | N0, `List.index_of_argmax` | focused Lean | compiled |
| N2 | three chapter surfaces under one test import | existing local theorem chains | dedicated canary | compiled |
| root | scoped chapter promotion evidence | N1, N2, docs/site/review/full check | repository gate | gate-pending |

## Scope Boundary

- Pinned LML declarations remain theorem-card-only.
- The ordinary-UCB completion surface is one horizon-indexed canonical family,
  not one fixed all-time probability source.
- The geometric all-time empirical-mean event remains a compiled extension,
  not a UCB score/count/regret/consistency theorem.
- KL-UCB, self-normalized confidence, UCB-VI, and RL confidence are outside
  this Book Map leaf.
