# Book Map Chapters 2--4 canonical route completion canaries

Task id: `BOOKMAP-CHAPTERS-2-4-CANONICAL-ROUTE-CANARIES`
Kind: `lean`
Status: `accepted`
Harness: `hierarchical`

## Goal

Close the only mathematical gap found by the chapter audit--the public
least-encoded tie certificate for the Rat commit oracle used by the canonical
generated ETC policy--and compile one external canary that names the exact
Probability, ETC, and ordinary-UCB route surfaces used by the scoped Book Map
completion definitions.

The UCB surface is the existing horizon-indexed `(T, delta)` canonical family.
The separately compiled geometric all-time confidence producer is not claimed
as an anytime one-policy UCB consumer.

## Source

- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Paper card: `PPR-AUER-CBF-2002-UCB1`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.
- Local ETC source: `ETC.argmaxCommitOracle`,
  `ETC.explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure`,
  and the bounded/sub-Gaussian endpoints in `ETCFiniteArmRewardLaw.lean`.
- Local UCB source: the fixed-horizon pair-trajectory chain and its
  finite-arm horizon-indexed asymptotic specialization.
- Pinned LML cards and proof weapons are route evidence only, never proof
  terms.

## Lean Target

```lean
ETC.argmaxCommitOracle_argmax_finRange
ETC.argmaxCommitOracle_encode_le_of_score_le
```

Target file: `BanditRLProof/Algorithms/ETCArgmaxOracle.lean`.
External canary: `Tests/BookMapChaptersTwoToFourCanary.lean`.

## Proof Obligations

- [x] Identify the exact Rat oracle used by the generated ETC policy.
- [x] Prove equality with Mathlib's first-occurrence `List.argmax`.
- [x] Derive least-encoded selection among all arms tying the maximum.
- [x] Keep the leaf deterministic: no probability or concentration premise.
- [x] Compile the named ETC wrong-commit union and expected-regret endpoints
  on the same canonical `historyStepKernelFamily`/`trajMeasure` surface.
- [x] Compile the actual finite-horizon UCB confidence, large-gap, pull-count,
  expected-regret, and horizon-indexed expected-average terminal surfaces.
- [x] Keep the geometric all-time producer visibly separate from the ordinary
  UCB chain.
- [x] Complete statement fence, retrieval/lifecycle records, independent
  review, website/docs/paper synchronization, and the full repository gate.

Acceptance evidence: verified memory `mem-dfedda06bab23849`, accepted reviewer
trial at index 326, active frontier `frontier-1a4ddfd06eb81f17`, statement
fence `8a571fbd...ffee6`, zero shadow mismatches across 327 trials, and a passing
`python3 tools/bandit.py check`.

## Local APIs, Route, And Contracts

| Node | APIs/imports | Proof route | Regularity contracts | Status |
| --- | --- | --- | --- | --- |
| Rat list argmax | `Mathlib.Data.List.MinMax`, `List.argmax`, `List.finRange` | identify the strict-update fold with first-occurrence argmax | `0 < K` | compiled |
| least tie | `List.index_of_argmax`, `List.idxOf_finRange` | compare list positions of the selected maximum and any tying arm | finite `Fin K`; Rat linear order | compiled |
| Chapter 3 surface | generated policy/law, named wrong-commit union, bounded and sub-Gaussian regret terminals | `#check`, typed tie application, axiom reports | theorem signatures remain authoritative | compiled canary |
| Chapter 4 surface | finite-time confidence through horizon-indexed consistency | exact local declarations plus typed terminal application | finite arms, probability laws, sub-Gaussian MGF, explicit horizon schedule | compiled canary |

## Failure Policy

If the tie theorem fails, classify the first issue as `List.argmax` fold
orientation, finRange order/index rewriting, or a false least-encoded claim.
Do not change the oracle, weaken maximality, assume unique maxima, or replace
the Rat generated source by the separate Real route. If the UCB chapter audit
fails, keep it partial; do not relabel the geometric all-time producer as an
anytime UCB regret theorem.
