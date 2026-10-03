# Proof Obligations: Theorem2.26
Task id: `ONLINE-SUBGRADIENT-MAX`

| Node | Target | Dependencies | Owner | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| active-support | actual active support belongs to max support | finite maximum order | lower | focused + axioms | compiled-public; acceptance pending |
| hull-forward | ordinary hull contained in full max support | active-support, actual support convexity | lower | focused + canary | compiled-public; acceptance pending |
| regularity | continuity implies interior, compact supports | exact source assumptions, existing boundedness/existence | lower | focused | compiled-public; acceptance pending |
| hull-reverse | every max support in ordinary active hull | actual compactness and separation/decomposition | lower | focused + semantic review | compiled-public; acceptance pending |
| ROOT | theorem_2_26 exact equality | forward, reverse | upper | public names + canary + axioms + root/Tests/full harness + semantic/site | compiled-public; acceptance pending |

## Failure classification
First type probe found guessed EReal.add_le_add_left, continuousAt_iff, EReal.continuousAt_toReal unavailable; retained logs. This is local API mismatch, not mathematical failure. Card path initially nonexistent, corrected actual paths and retained miss. Empty theorem slots are parser metadata, not compiled proof. No failed attempt can authorize source weakening.
