# Orabona closed/proper definitions and indicator equivalences

Task id: `ONLINE-BOOK-CH2-CLOSED-PROPER`
Kind: `theorem`
Status: `accepted-local`
Harness: `hierarchical`

## Exact source and target
Orabona arXiv1912.13213v10, printed16/PDF28, Definitions2.16/2.18 and Examples2.17/2.19, including the unnumbered lower-semicontinuity equivalence. Pinned PDF SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Public file BanditRLProof/OnlineClosedProper.lean; exact two definitions and three targets are bound in docs/contracts/online-closed-proper-public-v1, parent online-closed-proper-v1. Finite real cuts, both infinite values, finite-value witness, and empty sets are retained. Source Euclidean scope generalizes to arbitrary topological space. No probability, filtration, or regret claim.

## Dependency-ready leaves and reuse
1. Closedness iff lower semicontinuity: use open complements, EReal.exists_between_coe_real, and the union of real superlevels for the bottom threshold. Mathlib-candidate bridge from source real cuts to the existing full-threshold API.
2. Closed indicator iff closed set: reuse shared extendedIndicator, calculate its real sublevels. Project source adapter.
3. Proper indicator iff nonempty set: reuse the same zero/top indicator; finite witness is exactly membership. Project source adapter.

The DAG has existing EReal/topology and extendedIndicator parents -> three independent leaf equivalences -> source prerequisite mapping for later subgradient analysis. No proof of those later subgradient results is inferred.

## Evidence and remaining gates
Focused9070jobs includes public root/canary. Combined root/Tests9194jobs and full harness464tests/7existing skips passed. Standard-only axioms; independent source-blind decoder and distinct source reviewer accepted with explicit arbitrary-topology delta. Source/read inventory in runs/online-closed-proper-20261003. Site build02/check02 passed after preserving schema-failure01. Full-root graph export and contribution manifest/PR delivery remain pending at this checkpoint. Active global frontier remains unchanged.

Final local gates passed; exact evidence: runs/online-closed-proper-20261003/acceptance-decision.md. Scoped PR delivery remains pending.
