# Theorem 2.26 actual body review

Verdict: **accepted-with-explicit-delta for the inspected complete candidate body and five named canaries**. No mathematical repair requested. Deltas remain explicit nonempty indexing for a defined finite maximum and coordinate-free finite-dimensional Euclidean/EReal presentation. This is a distinct automated body review, not external-human review or final public/reader/root/harness/site/binding acceptance. The public focused gate was in progress when assigned and is not certified completed here.

Actor: `/root/source_reviewer`, requested GPT-6 Astra / medium; 2026-10-03. Prior contract receipt remains immutable and does not substitute for inspection of the actual construction.

## Read scope and binding

I read all code in OnlineSubgradientMax.lean and OnlineSubgradientMaxCanary.lean, successful max-full-leaf-01/max-canary-06 log result tails, their complete snapshots through programmatic comparison, and the scoped actual subgradients_locally_bounded and subgradient_limit_of_continuousAt interfaces/body excerpts. The v1 contracts, prior source-contract report/receipt, and full blind reconstruction were inspected earlier in this continuous review; the terminal header was reread. Tool comparison removing comments, scratch #print lines and whitespace found the public module equal to its compiled scratch snapshot; the canary namespace suffix likewise matched its snapshot. These comparisons supplement full reading of the actual public files, not replace it. Hashes below bind snapshots/logs separately, not an independently rerun compilation.

The original source was freshly extracted in the contract pass from physical30/printed18; I rehashed the pinned PDF again here, matching cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. The source requires ordinary convex-hull equality for proper convex finite-family functions, common-domain query and ambient continuity of every component there. No source or library transitive closure audit is implied by containing-file hashes.

## Seven semantic slots

| Slot | Actual implementation finding |
| --- | --- |
| 1. Objects/spaces | Actual Finset.sup' over nonempty finite indexing; exact equality defines activity; full global component supports. Finite-dimensional inner-product space remains explicit in terminal. |
| 2. Quantifiers | All functions proper/convex, all finite at query and all continuous there. Each candidate max support and each separating direction is arbitrary. Nearby argmax/support witnesses are constructed, not passed into the terminal. |
| 3. Assumptions | Frozen hypotheses unchanged. No component closedness, bounded domain, global real-valuedness, assumed compactness/decomposition, unique active index or differentiability introduced. |
| 4. Conclusion | Both directions of exact ordinary convexHull equality. Actual compactness proves the hull closed for separation; no replacement by closedConvexHull. |
| 5. Constants/normalization | Nearby points x+(1/(n+1))*d have positive step tending to0. Local norm bounds are derived and summed; no bound/modulus is a terminal input. No approximate activity or weighted maximum. |
| 6. Probability/information | Deterministic classical choices and filter/subsequence limits; no stochastic selection, algorithm or causal claim. |
| 7. Boundaries | Finite ties, singleton, zero-dimensional space and top values away from query retained. Empty indexing excluded explicitly. Early nearby indices can be outside the domain but are discarded by eventual membership, not assumed feasible. |

## Forward inclusion and ordinary-hull producer

The foundation consumes a real active component support, rewrites its base value using exact activity, and bounds its value at every test point by the actual maximum. It does not assume convexity or a maximum oracle. Finite maximum attainment is proved from Finset.sup'; properness and common-domain membership produce finite maximum value and no-bottom globally. The support-equivalence helper handles top-valued test points explicitly and translates finite ones to real inequalities. Convexity of the global support set then follows by convex combination of actual inequalities, giving convexHull forward inclusion.

The same real-inequality description represents each support set as an intersection of closed halfspaces, proving its closedness without assuming the function closed. Ambient continuity and finite query imply domain interior. Existing local support boundedness then bounds the support set in a compact finite-dimensional closed ball, producing its compactness. The ordinary hull of the finite union of active supports is genuinely proved compact: convexJoin is a continuous image of [0,1] times two compact sets; induction on the finite family uses convexHull_union, each component support's convexity, and explicit empty-set branches. Inactive components are replaced by empty sets solely in this active-union representation. This proves the exact hull compact, not a larger closed hull.

## Actual reverse construction and limit audit

For arbitrary direction d and aggregate support g, ys(n)=x+(1/(n+1))*d converges to x. Every component has x in domain interior, so finite-index eventual conjunction gives eventual simultaneous interior membership of ys. Local support bounds are obtained separately for each function and combined with finite summation. Actual finiteMax_attained chooses idx(n) for every n. At domain-interior points, subgradient_exists_of_domain_interior supplies an actual component support qs(n); outside that eventually valid regime a dummy0 is used with a conditional proof. The proof explicitly derives eventual support membership before using bounds or comparison, so dummy early values create no hidden assumption.

The sum of nonnegative component bounds uniformly bounds qs eventually. Finite-dimensional compactness gives a convergent subsequence. Finiteness of the index type supplies one index i occurring frequently on that subsequence. The restricted filter atTop intersect principal{n:idx(phi(n))=i} is explicitly proved NeBot. Both point and support convergence are transferred to this filter, and eventual component support membership is rewritten to the fixed i. Thus the limit theorem is not applied along a potentially empty or changing-component filter.

continuousAt_finite_toReal correctly obtains real-part continuity by restricting EReal.toReal away from both infinities at the finite query. The inspected subgradient_limit_of_continuousAt interface requires a nontrivial filter and actual eventual global supports; the body supplies them. Its conclusion is a genuine global support k of component i at x, including top-valued test points. Activity is proved separately: every component value is bounded by f_i at nearby fixed-index maximizers, and ambient EReal continuity of every component passes these inequalities to the limit; combined with the actual maximum bound this gives f_i(x)=F(x).

The displacement comparison adds the actual max-support inequality from x to y and the selected component-support inequality back from y to x, using f_i(x)<=F(x), yielding inner(g,y-x)<=inner(q,y-x). Positive step cancellation gives the direction comparison. Passing it to the same nontrivial limit yields inner(g,d)<=inner(k,d) for an actual active support k.

Finally, if g lay outside the ordinary compact convex hull, geometric separation gives a continuous linear functional strictly larger at g than on the hull. Riesz converts it to a direction with the checked inner-product orientation. The constructed active k lies in the hull and dominates g in that direction, contradicting strict separation. No decomposition or dual attainment is assumed; the full reverse membership is produced. The exact terminal header matches the frozen proper/convex/all-domain/all-continuity statement.

## Canaries and observed compilation

The Bool affine family y and -y proves an actual tie active union {-1,1}. The terminal yields its hull and then the exact interval[-1,1]. The mixture/rejection canary admits1/2 in the aggregate support while proving it absent from the active union, and excludes2. At query2 it excludes the inactive -1 slope and gives exactly{1}. The singleton Unit family is the indicator of[-1,1]: ambient continuity at0 is proved through local equality to0, the full terminal gives{0} there, and the maximum equals top at2. This explicitly tests finite-query continuity without imposing global finite-valuedness. These are five named endpoint canaries, with genuine supporting prerequisites, not an exhaustive test of every possible hypothesis failure.

max-full-leaf-01 reports theorem_2_26 and the direction witness with only propext, Classical.choice and Quot.sound. max-canary-06 reports all five named canaries with the same standard axioms; displayed warnings are unused context/simp issues. Snapshot comparisons link these mathematical texts to the current candidate. I did not run compilation, audit every failed historical attempt, or certify the public-focused job's completion.

## Remaining gates

No proof or source-header repair requested. Root/Tests and full harness gates, actual public focused completion, final reader/source-inventory/status audit, graph/registry/contribution/site evidence and immutable byte binding remain separate. The accepted contract/foundation alone would not have discharged this theorem; this receipt now specifically audits the complete reverse body. Later hinge/affine/Lipschitz/OSD/linearization, older-stack migration and whole-book completion remain outside scope.

## Raw SHA256 inputs

Current raw filesystem bytes; no normalization or reserialization. Paths relative to E:/ABRL/worktrees/research-online-book. Companion receipt additionally binds this report.

| File | Raw SHA256 |
| --- | --- |
| `BanditRLProof/OnlineSubgradientMax.lean` | `c1224494d910035fb482971885a5a4c617da9b3d9a618cb71ec91e5b15dd018c` |
| `Tests/OnlineSubgradientMaxCanary.lean` | `39eb5e0937ebdb7d60776f8a8bfe3feeafb76d0e1232aeaabbb92bc2f45f1421` |
| `BanditRLProof/OnlineSubgradientDifferentiability.lean` | `49ca6eb223e522fbb0fc4b40cb5c0d13977666f220001a92ecb11b1e79eb603a` |
| `runs/online-subgradient-max-20261003/attempts/max-full-leaf-01.lean` | `ab6e8e455d9604624c3df2068fa2c390c350da7b9906637f290a08d25fce262c` |
| `runs/online-subgradient-max-20261003/attempts/max-full-leaf-01.log` | `8c58a9c616bcf19d0153c3b12b2ee8ee61ff6948775925d7bd83120ce818184b` |
| `runs/online-subgradient-max-20261003/attempts/max-canary-06.lean` | `6a38ecdbb3078a9dd5ec0f24015cb4b3dc8f0d72d82f3612b05958960a2c6583` |
| `runs/online-subgradient-max-20261003/attempts/max-canary-06.log` | `d71b5351a2d5bac83f620c2520d76e3f33256594b992e8cac04687d3091f0413` |
| `runs/online-subgradient-max-20261003/source-contract-review.md` | `5722b5f995b00fa1a8d9c843979238f4aa5c776828c2d85153ce93883c414495` |
| `runs/online-subgradient-max-20261003/source-contract-receipt.json` | `ae5bc3b55a114bde6450660d702fb9a05802c4a2ec7e9709c07763d0a1bec382` |
| `runs/online-subgradient-max-20261003/blind-packet.txt` | `b179d387065324c9f258417a5eb25ea81aa4125ca8aeeab47325a07104f831b9` |
| `runs/online-subgradient-max-20261003/blind-reconstruction.md` | `c0deb3178f446f33a199c8c431081d785036e0f6347fffe3ae046c7e70a4f012` |
| `runs/online-subgradient-max-20261003/blind-receipt.json` | `bfd3a1c19653e92c604445a55dd20bcfd4c78b954c98fc278c405921a4759e73` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `docs/contracts/online-subgradient-max-v1/active_subgradient_support_max-header.txt` | `ba07be0895372ac2a50be362b59c536aea72e47c46e5bf82239c2a1ee45356d2` |
| `docs/contracts/online-subgradient-max-v1/active_subgradient_support_max.json` | `c97f87a806574e03545034ca67fb41902eedcec5db7940f1fd264a524b99294d` |
| `docs/contracts/online-subgradient-max-v1/context.txt` | `af96fc425ad16cf6e789215142d51a91bfcd1caf3a852194643cedf91cf0b1e5` |
| `docs/contracts/online-subgradient-max-v1/contract-manifest.json` | `18ba092cb28814a29676f5b6c8e5259d19180ca1def38b307233f46495c4a819` |
| `docs/contracts/online-subgradient-max-v1/contract.md` | `2343cf57397e4781882dba842b23324a76f30f4b0af8c0dd5d431e9db2e15edc` |
| `docs/contracts/online-subgradient-max-v1/theorem_2_26-header.txt` | `dadc1a0d783951bc11b13e6713dfef348fece79dda05572005768d87d5e29414` |
| `docs/contracts/online-subgradient-max-v1/theorem_2_26.json` | `d1c35dfa3cec7f54bb84009c3ad40e0a1f99b1c982eacee6d45dbf047ffcccfe` |
