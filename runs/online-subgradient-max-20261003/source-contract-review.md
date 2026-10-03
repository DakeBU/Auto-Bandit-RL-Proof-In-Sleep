# Theorem 2.26 source contract review

Verdict: **accepted-with-explicit-delta for contract stabilization only**. No mathematical header repair required. Explicit nonempty finite indexing makes the source maximum well-defined; coordinate-free finite-dimensional Euclidean representation and EReal with properness encode the source range. Foundation inclusion is a stronger auxiliary statement, not the full theorem. No body, compilation, public acceptance, external-human review or chapter/book completion is certified.

Actor: `/root/source_reviewer`, distinct automated anti-anchored source reviewer; requested GPT-6 Astra / medium; 2026-10-03.

## Source and read scope

I read tmp/subgradient-max-source-pages.txt and freshly extracted Theorem 2.26 from original PDF physical30/printed18. Independently measured PDF SHA256 is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, matching the pin. The source states a finite family of proper convex functions into (-infinity,+infinity], a query in every domain, continuity of every component at that query, and exact ordinary convex-hull equality over active subdifferentials.

I read all seven v1 contract files (context, two headers, contract, manifest, two native fences), the complete neutral packet/reconstruction and blind receipt. I independently checked that the blind receipt's raw packet and report hashes match current bytes. Supplied shared definitions agree with those inspected in the preceding sequential source reviews; this pass does not claim a new transitive library/body audit. No proof bodies or compilation outputs were inspected because this task is contract stabilization.

## Seven semantic slots

| Slot | Mismatch search and result |
| --- | --- |
| 1. Objects/spaces | Actual finite nonempty maximum is Finset.univ.sup', not an assumed upper envelope. EReal functions are proper at the source terminal, excluding bottom globally. Explicit finite-dimensional real inner-product structure represents source Euclidean space. |
| 2. Quantifiers/order | Every family and query satisfying all component assumptions; every candidate support vector. Active membership requires exact equality f_i(x)=max_j f_j(x) and an actual global component support at the same x. All tied active indices contribute, with no unique maximizer premise. |
| 3. Assumptions | Every component proper and convex; x in every effective domain; every component ContinuousAt at x. No extra closedness, global finiteness/continuity, bounded domain, differentiability or supplied decomposition. Continuity is ambient into EReal, not merely within a thin domain and not restricted to active functions. |
| 4. Conclusion | Exact equality with ordinary convexHull over real scalars of the active support union. No closure, closed hull, sum, intersection, selected gradient or forward-only substitute. Foundation leaf proves only active-union inclusion and cannot discharge the full theorem. |
| 5. Constants/normalization | Unweighted actual maximum, exact activity, ordinary convex combinations. No approximation threshold, rate, external modulus or hidden scaling. |
| 6. Probability/information | Deterministic convex analysis, no randomness, filtration, online information, algorithm or regret assertion. |
| 7. Boundaries | Empty index set excluded explicitly; singleton/duplicates/ties/zero-dimensional space allowed. Query finiteness follows component properness plus all-domain membership. Infinities away from x remain allowed; no all-x claim without query hypotheses. |

## Continuity, activity and hull audit

At the terminal, SourceProper excludes negative infinity while effectiveDomain excludes positive infinity at x, so all component values and their finite maximum are finite there. Ambient ContinuousAt into the standard EReal topology at a finite value expresses extended-real continuity as in the source. A bounded open interval around that finite value yields local finiteness; it does not require global real-valuedness. Replacing this with relative-domain continuity would change the theorem and is not permitted. No closed-epigraph assumption has been smuggled into IsConvexExtended, which remains real-height epigraph convexity.

SourceFiniteMax takes the actual maximum of a finite nonempty family. SourceActiveSubgradientUnion is exactly the union over indices with f_i(x)=F(x), each contributing its whole global subdifferential. Inactive supports do not enter. Nonempty indexing is an explicit source well-definedness convention: the printed maximum has no empty-family value prescribed. It is not an added analytic restriction on a meaningful source empty-maximum case. Any future empty-index extension would require its own definition and review.

The foundation leaf intentionally omits properness, convexity, continuity and finite-dimensionality. Its statement is a valid stronger order-level dependency: an active support has base value F(x), and its component value at every y is bounded above by F(y). Its unusual improper EReal cases belong to that auxiliary scope and are not source-terminal guarantees. Neither an active index's existence nor the foundation inclusion supplies actual support nonemptiness or the reverse convex-hull decomposition.

The required hull is ordinary convexHull, not its closure. A later proof using separation must actually establish any needed compactness/closedness from the stated assumptions, rather than replacing the output by a closed hull or assuming the decomposition. The proposed DAG is only a plan; its APIs and producers are not certified by this header review. The singleton case reduces to convexity of the component subdifferential under the hypotheses; ties retain the full union before taking the hull.

## Decoder, native fences and mandatory gaps

The independent blind reconstruction correctly recovers ambient continuity of every component, all-domain membership, full global supports, actual active maximum and ordinary hull. Its raw receipt matches its packet and report. Native JSON statement fields match both actual headers and manifest native fingerprints. Their empty source_assumptions arrays do not erase the explicit assumptions in the terminal.

Stabilize these exact endpoints with the explicit deltas above. Required remaining work includes actual maximum-support inclusion, convex-hull forward inclusion, and the full reverse inclusion under precisely the frozen assumptions, together with meaningful tied/inactive/singleton/infinite-away-from-query cases and subsequent technical/semantic/binding stages. No proof has been accepted here. A proposed source/header change must use a new reviewed version rather than silent weakening. Later hinge/affine/Lipschitz/OSD/linearization, older-stack migration and whole-book obligations remain separate and required.

## Raw SHA256 reviewed inputs

Independently computed current raw bytes, without line-ending normalization or JSON reserialization. Paths relative to E:/ABRL/worktrees/research-online-book. The companion JSON additionally binds this report; neither output self-hashes recursively.

| File | Raw SHA256 |
| --- | --- |
| `docs/contracts/online-subgradient-max-v1/active_subgradient_support_max-header.txt` | `ba07be0895372ac2a50be362b59c536aea72e47c46e5bf82239c2a1ee45356d2` |
| `docs/contracts/online-subgradient-max-v1/active_subgradient_support_max.json` | `c97f87a806574e03545034ca67fb41902eedcec5db7940f1fd264a524b99294d` |
| `docs/contracts/online-subgradient-max-v1/context.txt` | `af96fc425ad16cf6e789215142d51a91bfcd1caf3a852194643cedf91cf0b1e5` |
| `docs/contracts/online-subgradient-max-v1/contract-manifest.json` | `18ba092cb28814a29676f5b6c8e5259d19180ca1def38b307233f46495c4a819` |
| `docs/contracts/online-subgradient-max-v1/contract.md` | `2343cf57397e4781882dba842b23324a76f30f4b0af8c0dd5d431e9db2e15edc` |
| `docs/contracts/online-subgradient-max-v1/theorem_2_26-header.txt` | `dadc1a0d783951bc11b13e6713dfef348fece79dda05572005768d87d5e29414` |
| `docs/contracts/online-subgradient-max-v1/theorem_2_26.json` | `d1c35dfa3cec7f54bb84009c3ad40e0a1f99b1c982eacee6d45dbf047ffcccfe` |
| `runs/online-subgradient-max-20261003/blind-packet.txt` | `b179d387065324c9f258417a5eb25ea81aa4125ca8aeeab47325a07104f831b9` |
| `runs/online-subgradient-max-20261003/blind-reconstruction.md` | `c0deb3178f446f33a199c8c431081d785036e0f6347fffe3ae046c7e70a4f012` |
| `runs/online-subgradient-max-20261003/blind-receipt.json` | `bfd3a1c19653e92c604445a55dd20bcfd4c78b954c98fc278c405921a4759e73` |
| `tmp/subgradient-max-source-pages.txt` | `86172f77076921066a225d2afee2274f16c99891ee962858acce66e8adb627f3` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
