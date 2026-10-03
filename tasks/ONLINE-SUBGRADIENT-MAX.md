# Orabona Theorem2.26 finite maximum rule
Task id: `ONLINE-SUBGRADIENT-MAX`
Kind: `theorem`
Status: `candidate`
Harness: `hierarchical`

## Goal and source
Pinned v10 Theorem2.26 printed18/PDF30. Exact mandatory terminal: global subdifferential of actual finite maximum equals ordinary convex hull of the active subgradient union. Source contract: docs/contracts/online-subgradient-max-v1; run: runs/online-subgradient-max-20261003. SourceProper, IsConvexExtended, all-query-domain and each ContinuousAt retained. Nonempty finite family makes source maximum defined. No probability or algorithm claim.

## Lean Target
`BanditRL.OnlineConvex.theorem_2_26`; dependency `active_subgradient_support_max`.
Target file: `BanditRLProof/OnlineSubgradientMax.lean`
Frozen native headers/hashes in contract. Full exact equality compiles publicly with all source assumptions, five nondegenerate canaries and distinct actual-body review accepted. Root9077/Tests9208 pass; full harness/axioms/graph/site/final-reader/binding gates pending.

## Mathlib-Ready Leaf Contract
| Leaf | Local APIs | Route | Regularity | Status |
| --- | --- | --- | --- | --- |
| active support | Finset.le_sup', SourceSubdifferential | active equality and global support order | finite nonempty family only | project-local |
| forward hull | convexHull_min, convex halfspaces | prove convex support set | query finite and no bottom as needed | mathlib-candidate |
| reverse | local bounded/existence/limit supports | actual separation/decomposition | exact source continuity and finite dimension | project-local; full exact source terminal compiled, acceptance pending |

## Retrieval and trial logging
Actual memory/declaration/card/API receipts indexed in run. Failed guessed card path retained, corrected actual research-wiki/mathlib and lml theorem-cards searched. No whole-library absence claim. Native trial-log on attempts; retain snapshots and failures. No chapter or book completion.
