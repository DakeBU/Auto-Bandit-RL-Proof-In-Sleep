# Basic source subgradient packet

Task id: `ONLINE-BOOK-CH2-SUBGRADIENT-BASIC`
Kind: `theorem`
Status: `candidate`
Harness: `hierarchical`

Source: Orabona arXiv1912.13213v10, Definition2.20, proper support-domain inclusion and Theorem2.21, printed16-17/PDF28-29; pinned PDF SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17.

Exact targets/context: online-subgradient-basic-v1 and path-only online-subgradient-basic-public-v1. SourceSubdifferential is a global supporting-vector set over EReal values. Proper-point effective-domain membership and real-valued convexity-on-V are separate finite dependency-ready leaves. Reuse shared SourceProper/effectiveDomain, EReal coercion arithmetic and inner-product bilinearity. No probability/filtration/regret claim. Normed inner-product generalization and dropping unnecessary convexity from finite-domain consequence are explicit source deltas.

DAG: existing properness/domain/EReal APIs -> support definition -> two independent theorem leaves -> source prerequisite mapping. Later interior existence, singleton/differentiability equivalence and sum/max rules remain mandatory; current interior producer is scratch only. No declaration count implies chapter progress.

Actual evidence: public-focused01 and canary02 pass9071jobs, including root and nondegenerate quadratic/outside-interval canaries. Fullgate01 failed an untracked-source fixture; candidate commit repaired tracking, fullgate02 passes465tests/7existing skips and combined root/Tests. Six compiled proof-value graph checks pass. Distinct automated semantic actors accepted explicit deltas. Site/contributor/delivery remain separate pending gates at this checkpoint.
